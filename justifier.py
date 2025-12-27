from collections import defaultdict
from typing import Sequence, Tuple, List

from clingo import ast
from clingo.ast import ProgramBuilder
from clingo.control import Control
from clingo.propagator import PropagateControl, PropagateInit, Propagator
from clingo.backend import Backend
from clingo.ast import parse_string, AST, ASTType
from clingo.symbol import Function

class Transformer:
    """
    Transformer for the guess and check solver.
    """
    _builder: ProgramBuilder
    _state: str
    _check: List[AST]
    _glue: List[AST]

    def __init__(
        self,
        builder: ProgramBuilder,
        check: List[AST],
        glue: List[str]
    ):
        self._builder = builder
        self._state = "guess"
        self._check = check
        self._glue = glue

    def add(self, stm: AST):
        """
        Add the given statement to the guess or check programs.
        """
        if stm.ast_type == ASTType.Program:
            if stm.name == "shared" and not stm.parameters:
                self._state = "shared"
            elif stm.name == "glue" and not stm.parameters:
                self._state = "glue"
            elif stm.name == "check" and not stm.parameters:
                self._state = "check"
            elif (stm.name in ["base", "guess"]) and not stm.parameters:
                self._state = "guess"
            else:
                raise RuntimeError("unexpected program part")

        else:
            if self._state == "shared":
                self._builder.add(stm)
                self._check.append(stm)
                self._glue.append(stm)
            elif self._state == "guess":
                self._builder.add(stm)
            elif self._state == "check":
                self._check.append(stm)
            elif self._state == "glue":
                self._glue.append(stm)


class Checker:
    """
    Class wrapping a solver to perform the second level check.
    """
    _ctl: Control
    _map: List[Tuple[int, int, int]]

    def __init__(self):
        self._ctl = Control(["--heuristic=Domain"])
        self._map = []

    def backend(self) -> Backend:
        """
        Return the backend of the underlying solver.
        """
        return self._ctl.backend()

    def add(self, guess_lit: int, check_lit: int, indicator_lit: int):
        """
        Map the given solver literal to the corresponding program literal in
        the checker.
        """
        self._map.append((guess_lit, check_lit, indicator_lit))

    def ground(self, check: Sequence[ast.AST]):
        """
        Ground the check program.
        """
        with ProgramBuilder(self._ctl) as bld:
            for stm in check:
                bld.add(stm)

        self._ctl.ground([("base", [])])

    def check(self, control: PropagateControl) -> bool:
        """
        Return true if the check program is unsatisfiable w.r.t. to the atoms
        of the guess program.

        The truth values of the atoms of the guess program are stored in the
        assignment of the given control object.
        """

        assignment = control.assignment

        assumptions = []
        for guess_lit, check_lit, _ in self._map:
            guess_truth = assignment.value(guess_lit)
            assumptions.append(check_lit if guess_truth else -check_lit)

        with self._ctl.solve(assumptions, yield_=True) as handle:
            result = handle.get()
            model = handle.model()
            mask = []
            if model:
                for guess_lit, check_lit, indicator_lit in self._map:
                    if model.is_true(indicator_lit):
                        mask.append(guess_lit)
            if result.unsatisfiable is not None:
                return result.unsatisfiable, mask

        raise RuntimeError("search interrupted")


class CheckPropagator(Propagator):
    """
    Simple propagator verifying that a check program holds on total
    assignments.
    """
    _check: List[AST]
    _glue: List[str]
    _checkers: List[Checker]
    _gluelits: List[int]

    def __init__(self, check: List[AST], glue: List[AST]):
        self._check = check
        self._glue = glue
        self._checkers = []
        self._gluelits = []
        self.num_conflicts = []

    def init(self, init: PropagateInit):
        """
        Initialize the solvers for the check programs.
        """
        # we need a checker for each thread (to be able to solve in parallel)
        for _ in range(init.number_of_threads):
            checker = Checker()
            self._checkers.append(checker)

            self.num_conflicts.append(0)

            with checker.backend() as backend:
                for atom in init.symbolic_atoms:

                    # ignore atoms that are not glue
                    if str(atom.symbol) not in self._glue:
                        continue

                    guess_lit = init.solver_literal(atom.literal)
                    guess_truth = init.assignment.value(guess_lit)

                    # ignore false atoms
                    if guess_truth is False:
                        continue

                    check_lit = backend.add_atom(atom.symbol)

                    indicator_symbol = Function("relevant", [atom.symbol], True)
                    indicator_lit = backend.add_atom(indicator_symbol)

                    if guess_lit not in self._gluelits:
                        self._gluelits.append(guess_lit)

                    # fix true atoms
                    if guess_truth is True:
                        backend.add_rule([check_lit], [])

                    # add a choice rule for unknow atoms and add them to the
                    # mapping table of the checker
                    else:
                        backend.add_rule([check_lit], [], True)
                        backend.add_rule([indicator_lit], [], True)
                        checker.add(guess_lit, check_lit, indicator_lit)

            checker.ground(self._check)


    def check(self, control: PropagateControl):
        """
        Check total assignments.
        """
        assignment = control.assignment
        checker = self._checkers[control.thread_id]

        unsatisfiable, mask = checker.check(control)
        if not unsatisfiable:

            conflict = []

            for lit in self._gluelits:
                if lit in mask:
                    conflict.append(-lit if assignment.is_true(lit) else lit)

            # print('.', end='')
            control.add_clause(conflict)
            self.num_conflicts[control.thread_id] += 1


def program_parts_based_on_axioms(part_dict, axioms):
    program = ""
    for axiom, part in part_dict.items():
        if axiom in axioms:
            program += part
    return program

def program_base(
    num_voters,
    num_profiles,
    num_candidates,
    axioms,
    num_axiom_instances=None,
):
    program = f"""
        #program shared.

        #const num_candidates={num_candidates}.
        candidate(1..num_candidates).
        position(1..num_candidates).

        #const num_voters={num_voters}.
        voter(1..num_voters).

        #const num_profiles={num_profiles}.
        profile_num(1..num_profiles).
    """
    if num_axiom_instances:
        program += f"""
            #const num_axiom_instances={num_axiom_instances}.
        """
    program += """
        % Auxiliary
        swap(C1,C2,C1,C2) :-
            candidate(C1), candidate(C2), C1 < C2.
        swap(C1,C2,C2,C1) :-
            candidate(C1), candidate(C2), C1 < C2.
        swap(C1,C2,C3,C3) :-
            candidate(C1), candidate(C2), C1 < C2,
            candidate(C3), C3 != C1, C3 != C2.
        """
    program += program_parts_based_on_axioms({
        "pareto":
        """
        use_axiom(pareto).
        axiom(pareto(C)) :- candidate(C),
            use_axiom(pareto).
        pos_axiom_instance(single(Prof),pareto(C)) :-
            use_axiom(pareto),
            profile_num(Prof), axiom(pareto(C)).
        """,
        "faithfulness":
        """
        use_axiom(faithfulness).
        axiom(faithfulness) :-
            use_axiom(faithfulness).
        pos_axiom_instance(single(Prof),faithfulness) :-
            use_axiom(faithfulness),
            profile_num(Prof), axiom(faithfulness).
        """,
        "unanimity":
        """
        use_axiom(unanimity).
        axiom(unanimity) :-
            use_axiom(unanimity).
        pos_axiom_instance(single(Prof),unanimity) :-
            use_axiom(unanimity),
            profile_num(Prof), axiom(unanimity).
        """,
        "cancellation":
        """
        use_axiom(cancellation).
        axiom(cancellation) :-
            use_axiom(cancellation).
        pos_axiom_instance(single(Prof),cancellation) :-
            use_axiom(cancellation),
            profile_num(Prof), axiom(cancellation).
        """,
        "reinforcement":
        """
        use_axiom(reinforcement).
        axiom(reinforcement) :-
            use_axiom(reinforcement).
        reinforcement_triple(Prof1,Prof2,Prof3) :-
            use_axiom(reinforcement),
            profile_num(Prof1), profile_num(Prof2), Prof1 <= Prof2,
            profile_num(Prof3),
            Prof1 < Prof3, Prof2 < Prof3. % only allowed due to symmetry breaking
        reinforcement_triple(Prof1,Prof2,1) :-
            use_axiom(reinforcement),
            profile_num(Prof1), profile_num(Prof2), Prof1 <= Prof2.
        pos_axiom_instance(triple(Prof1,Prof2,Prof3),reinforcement) :-
            use_axiom(reinforcement),
            reinforcement_triple(Prof1,Prof2,Prof3),
            axiom(reinforcement).
        """,
        "condorcet":
        """
        use_axiom(condorcet).
        axiom(condorcet(C)) :- candidate(C),
            use_axiom(condorcet).
        pos_axiom_instance(single(Prof),condorcet(C)) :-
            use_axiom(condorcet),
            profile_num(Prof), axiom(condorcet(C)).
        """,
        "neutrality":
        """
        use_axiom(neutrality2).
        axiom(neutrality2(C1,C2)) :- candidate(C1), candidate(C2), C1 < C2,
            use_axiom(neutrality2).
        pos_axiom_instance(double(Prof1,Prof2),neutrality2(C1,C2)) :-
            use_axiom(neutrality2),
            profile_num(Prof1), profile_num(Prof2), Prof1 <= Prof2,
            axiom(neutrality2(C1,C2)).
        """,
        "positive_responsiveness":
        """
        use_axiom(pos_responsiveness).
        pos_response_pair(C,P) :-
            use_axiom(pos_responsiveness),
            candidate(C), position(P), P < num_candidates.
        axiom(pos_responsiveness(V1,V2,C,P)) :-
            use_axiom(pos_responsiveness),
            voter(V1), voter(V2), pos_response_pair(C,P).
        pos_axiom_instance(double(Prof1,Prof2),pos_responsiveness(V1,V2,C,P)) :-
            use_axiom(pos_responsiveness),
            profile_num(Prof1), profile_num(Prof2),
            axiom(pos_responsiveness(V1,V2,C,P)).
        """
    }, axioms)
    return program


def program_target(
    target_profile,
    target_outcomes,
):
    program = "#program shared.\n"
    for vote_num, vote in enumerate(target_profile, 1):
        for position, candidate in enumerate(vote, 1):
            program += f"target_profile({vote_num},{candidate},{position}).\n"
    for outcome in target_outcomes:
        program += f"target_outcome({outcome}).\n"
    program += """
        target_voter(V) :- target_profile(V,_,_).
    """
    return program


def program_guess(
    axioms,
    target_profile,
    target_outcomes,
    candidates,
    num_axiom_instances=None,
):
    program = """
        #program guess.

        %%% Guess profiles
        { active_voter(Prof,V) } :- profile_num(Prof), voter(V).
        :- active_voter(Prof,V), not active_voter(Prof,V-1),
            voter(V), voter(V-1).
        active_profile(Prof) :- profile_num(Prof), active_voter(Prof,1).
        :- active_profile(Prof), profile_num(Prof-1),
            not active_profile(Prof-1).

        same_size_profiles(Prof1,Prof2) :-
            profile_num(Prof1), profile_num(Prof2), Prof1 < Prof2,
            active_voter(Prof1,V), not active_voter(Prof1,V+1),
            active_voter(Prof2,V), not active_voter(Prof2,V+1).
        same_size_profiles(Prof1,Prof2) :-
            same_size_profiles(Prof2,Prof1).
        same_size_as_target_profile(Prof) :-
            profile_num(Prof), Prof > 1,
            same_size_profiles(1,Prof).

        1 { profile(Prof,V,Cand,Pos) : position(Pos) } 1 :-
            profile_num(Prof), voter(V), active_voter(Prof,V), candidate(Cand).
        1 { profile(Prof,V,Cand,Pos) : candidate(Cand) } 1 :-
            profile_num(Prof), voter(V), active_voter(Prof,V), position(Pos).
    """
    if num_axiom_instances:
        program += """
            %%% Guess the right amount of axiom instances to use
            num_axiom_instances { use_axiom_instance(Profiles,Axiom) :
                axiom_applicable(Profiles,Axiom) } num_axiom_instances.
        """
    else:
        program += """
            %%% Use all applicable axiom instances
            use_axiom_instance(Profiles,Axiom) :-
                axiom_applicable(Profiles,Axiom).
        """

    program += """
        %%% Symmetry breaking: lexicographical ordering within each profile
        lex_eq_until(Prof,V1,V2,0) :-
            profile_num(Prof), voter(V1), voter(V2), V1 < V2.
        lex_eq_until(Prof,V1,V2,Pos) :-
            profile_num(Prof), voter(V1), voter(V2), V1 < V2,
            position(Pos), lex_eq_until(Prof,V1,V2,Pos-1),
            profile(Prof,V1,C,Pos), profile(Prof,V2,C,Pos).
        lex_dom(Prof,V1,V2) :- profile_num(Prof), voter(V1), voter(V2), V1 < V2,
            profile(Prof,V1,C1,Pos), profile(Prof,V2,C2,Pos), C2 < C1,
            lex_eq_until(Prof,V1,V2,Pos-1).
        :- profile_num(Prof), lex_dom(Prof,V1,V2),
            voter(V1), voter(V2), V1 < V2,
            active_voter(Prof,V1), active_voter(Prof,V2).

        %%% Symmetry breaking, no two profiles may be the same
        :- profile_num(Prof), profile_num(Prof+1),
            active_voter(Prof,V), active_voter(Prof+1,V),
            not active_voter(Prof,V+1), not active_voter(Prof+1,V+1),
            votes_identical(Prof,W,Prof+1,W) : active_voter(Prof,W).

        %%% Make sure that the target profile appears with index 1
        :- not profile(1,V,Cand,Pos), target_profile(V,Cand,Pos).
        target_active_voter(V) :- target_profile(V,_,_).
        :- active_voter(1,V), not target_active_voter(V).

        %%% Shared for applicability of various axioms
        num_active_voters(Prof,Num) :-
            profile_num(Prof), Num = #count { V : active_voter(Prof,V) }.
        num_active_voters(Prof,Num) :-
            active_voter(Prof,Num), not active_voter(Prof,Num+1). % Redundant
        votes_identical(Prof1,V1,Prof2,V2) :-
            profile_num(Prof1), profile_num(Prof2),
            active_voter(Prof1,V1), active_voter(Prof2,V2),
            profile(Prof1,V1,C,P) : profile(Prof2,V2,C,P).
        num_votes_identical(Prof1,V1,Prof2,N) :-
            profile_num(Prof1), profile_num(Prof2), voter(V1),
            N = #count { V2 : voter(V2), votes_identical(Prof1,V1,Prof2,V2) }.
    """
    program += program_parts_based_on_axioms({
        "pareto":
        """
        %%% Applicability of PARETO
        dominates_in_voter(Prof,V,C1,C2) :-
            use_axiom(pareto),
            profile_num(Prof), active_voter(Prof,V),
            candidate(C1), candidate(C2), C1 != C2,
            profile(Prof,V,C1,P1), profile(Prof,V,C2,P2), P1 < P2.
        dominates_in_profile(Prof,C1,C2) :-
            use_axiom(pareto),
            profile_num(Prof),
            candidate(C1), candidate(C2), C1 != C2,
            dominates_in_voter(Prof,V,C1,C2) : active_voter(Prof,V).
        axiom_applicable(single(Prof),pareto(C2)) :-
            use_axiom(pareto),
            pos_axiom_instance(single(Prof),pareto(C2)),
            active_profile(Prof),
            dominates_in_profile(Prof,C1,C2), candidate(C1), C1 != C2.

        % TODO: some redundant constraints?
        % IDEA: make it pareto(C1,C2), to indicate which is the *dominating*
        % candidate; this might make it more efficient to add
        % redundant constraints

        is_used(pareto) :- use_axiom_instance(Pr,pareto(C)).
        """,
        "faithfulness":
        """
        %%% Applicability of FAITHFULNESS
        axiom_applicable(single(Prof),faithfulness) :-
            use_axiom(faithfulness),
            pos_axiom_instance(single(Prof),faithfulness),
            active_profile(Prof),
            active_voter(Prof,1), not active_voter(Prof,2).

        :- axiom_applicable(single(Prof),faithfulness),
            active_voter(Prof,V), V > 1.

        % TODO: some redundant constraints?

        is_used(faithfulness) :- use_axiom_instance(Pr,faithfulness).
        """,
        "unanimity":
        """
        %%% Applicability of UNANIMITY
        axiom_applicable(single(Prof),unanimity) :-
            use_axiom(unanimity),
            pos_axiom_instance(single(Prof),unanimity),
            active_profile(Prof), candidate(C),
            profile(Prof,V,C,1) : active_voter(Prof,V).

        :- axiom_applicable(single(Prof),unanimity),
            profile(Prof,V1,C1,1),
            profile(Prof,V2,C2,1), V1 < V2, C1 != C2.

        % TODO: some redundant constraints?

        is_used(unanimity) :- use_axiom_instance(Pr,unanimity).
        """,
        "cancellation":
        """
        %%% Applicability of CANCELLATION
        num_active_voters_even(Prof) :-
            use_axiom(cancellation),
            num_active_voters(Prof,Num), Num \\ 2 == 0.
        cancellation_flipped_pair(Prof,V1,V2) :-
            use_axiom(cancellation),
            num_active_voters_even(Prof), num_active_voters(Prof,Num),
            active_voter(Prof,V1), active_voter(Prof,V2), V1 < V2,
            V1 <= Num/2, V2 == Num-V1+1.
        cancellation_identical_pair(Prof,V1,V2) :-
            use_axiom(cancellation),
            num_active_voters_even(Prof), num_active_voters(Prof,Num),
            active_voter(Prof,V1), active_voter(Prof,V2), V1 < V2,
            V1 <= Num/2, V2 <= Num/2.
        cancellation_identical_pair(Prof,V1,V2) :-
            use_axiom(cancellation),
            num_active_voters_even(Prof), num_active_voters(Prof,Num),
            active_voter(Prof,V1), active_voter(Prof,V2), V1 < V2,
            V1 > Num/2, V2 > Num/2.
        votes_identical(Prof,V1,V2) :-
            votes_identical(Prof,V1,Prof,V2), V1 < V2.
        votes_flipped(Prof,V1,V2) :-
            use_axiom(cancellation),
            profile_num(Prof), active_voter(Prof,V1),
            active_voter(Prof,V2), V1 < V2,
            profile(Prof,V2,C,num_candidates-P+1) : profile(Prof,V1,C,P).
        axiom_applicable(single(Prof),cancellation) :-
            use_axiom(cancellation),
            pos_axiom_instance(single(Prof),cancellation),
            active_profile(Prof),
            num_active_voters_even(Prof),
            votes_identical(Prof,V1,V2) :
                cancellation_identical_pair(Prof,V1,V2);
            votes_flipped(Prof,V1,V2) : cancellation_flipped_pair(Prof,V1,V2).

        :- axiom_applicable(single(Prof),cancellation),
            active_voter(Prof,V), not active_voter(Prof,V+1),
            V \\ 2 == 1.
        %:- axiom_applicable(single(Prof),cancellation),
        %    active_voter(Prof,V1),
        %    active_voter(Prof,V2), V1 < V2,
        %    active_voter(Prof,V3), V2 < V3,
        %    profile(Prof,V1,C,P1), profile(Prof,V2,C,P2),
        %    profile(Prof,V3,C,P3), P1 != P2, P1 != P3, P2 != P3.

        % TODO: some redundant constraints?

        is_used(cancellation) :- use_axiom_instance(Pr,cancellation).
        """,
        "reinforcement":
        """
        %%% Applicability of REINFORCEMENT
        reinforcement_count_check(triple(Prof1,Prof2,Prof3),V) :-
            use_axiom(reinforcement),
            pos_axiom_instance(triple(Prof1,Prof2,Prof3),reinforcement),
            active_voter(Prof3,V),
            num_votes_identical(Prof3,V,Prof1,N1),
            num_votes_identical(Prof3,V,Prof2,N2),
            num_votes_identical(Prof3,V,Prof3,N3),
            N3 = N1 + N2.
        axiom_applicable(triple(Prof1,Prof2,Prof3),reinforcement) :-
            use_axiom(reinforcement),
            pos_axiom_instance(triple(Prof1,Prof2,Prof3),reinforcement),
            active_profile(Prof1), active_profile(Prof2),
            active_profile(Prof3),
            num_active_voters(Prof1,N1), num_active_voters(Prof2,N2),
            num_active_voters(Prof3,N3), N3 = N1 + N2,
            reinforcement_count_check(triple(Prof1,Prof2,Prof3),V) :
                active_voter(Prof3,V).

        % TODO: some more redundant constraints?
        :- axiom_applicable(triple(Prof1,Prof2,Prof3),reinforcement),
            active_voter(Prof1,V1), active_voter(Prof2,V2),
            V1 + V2 > num_voters.

        is_used(reinforcement) :- use_axiom_instance(Pr,reinforcement).
        """,
        "condorcet":
        """
        %%% Applicability of CONDORCET
        beats(Prof,V,C1,C2) :-
            use_axiom(condorcet),
            profile_num(Prof), active_voter(Prof,V),
            candidate(C1), candidate(C2), C1 != C2,
            profile(Prof,V,C1,P1), profile(Prof,V,C2,P2), P1 < P2.
        majority_beats(Prof,C1,C2) :-
            use_axiom(condorcet),
            profile_num(Prof), candidate(C1), candidate(C2), C1 != C2,
            N1 = #count { V : beats(Prof,V,C1,C2) },
            N2 = #count { V : beats(Prof,V,C2,C1) },
            N1 > N2.
        axiom_applicable(single(Prof),condorcet(C1)) :-
            use_axiom(condorcet),
            pos_axiom_instance(single(Prof),condorcet(C1)),
            active_profile(Prof),
            majority_beats(Prof,C1,C2) : candidate(C2), C1 != C2.

        is_used(condorcet) :- use_axiom_instance(Pr,condorcet(C)).
        """,
        "neutrality":
        """
        %%% Applicability of NEUTRALITY/2
        votes_identical_under_swap(Prof1,V1,Prof2,V2,C1,C2) :-
            use_axiom(neutrality2),
            profile_num(Prof1), profile_num(Prof2),
            active_voter(Prof1,V1), active_voter(Prof2,V2),
            candidate(C1), candidate(C2), C1 < C2,
            profile(Prof1,V1,CS2,P) : profile(Prof2,V2,CS1,P), swap(C1,C2,CS1,CS2).
        num_votes_identical_under_swap(Prof1,V1,Prof2,C1,C2,N) :-
            use_axiom(neutrality2),
            profile_num(Prof1), profile_num(Prof2), voter(V1),
            candidate(C1), candidate(C2), C1 < C2,
            N = #count { V2 : voter(V2),
                votes_identical_under_swap(Prof1,V1,Prof2,V2,C1,C2) }.
        neutrality2_count_check(double(Prof1,Prof2),C1,C2,V) :-
            use_axiom(neutrality2),
            pos_axiom_instance(double(Prof1,Prof2),neutrality2(C1,C2)),
            active_voter(Prof1,V),
            num_votes_identical(Prof1,V,Prof1,N),
            num_votes_identical_under_swap(Prof1,V,Prof2,C1,C2,N).
        axiom_applicable(double(Prof1,Prof2),neutrality2(C1,C2)) :-
            use_axiom(neutrality2),
            pos_axiom_instance(double(Prof1,Prof2),neutrality2(C1,C2)),
            active_profile(Prof1), active_profile(Prof2),
            num_active_voters(Prof1,N), num_active_voters(Prof2,N),
            neutrality2_count_check(double(Prof1,Prof2),C1,C2,V) :
                active_voter(Prof1,V).

        :- use_axiom_instance(double(Prof1,Prof2),neutrality2(C1,C2)),
            active_voter(Prof1,W), not active_voter(Prof2,W).
        :- use_axiom_instance(double(Prof1,Prof2),neutrality2(C1,C2)),
            active_voter(Prof2,W), not active_voter(Prof1,W).

        % TODO: some redundant constraints?

        is_used(neutrality2) :- use_axiom_instance(Pr,neutrality2(C1,C2)).
        """,
        "positive_responsiveness":
        """
        %%% Applicability of POSITIVE RESPONSIVENESS
        votes_identical_after_upwards_move(Prof1,V1,Prof2,V2,C,P) :-
            use_axiom(pos_responsiveness),
            profile_num(Prof1), profile_num(Prof2),
            active_voter(Prof1,V1), active_voter(Prof2,V2),
            pos_response_pair(C,P),
            profile(Prof1,V1,C,P1), profile(Prof2,V2,C,P1-P),
            profile(Prof2,V2,C2,P2) :
                profile(Prof1,V1,C2,P2), P2 > P1;
            profile(Prof2,V2,C2,P2) :
                profile(Prof1,V1,C2,P2), P2 < P1-P;
            profile(Prof2,V2,C2,P2+1) :
                profile(Prof1,V1,C2,P2), P2 < P1, P2 >= P1-P.
        ith_voter_modulo_vote(Prof,V,I,I) :-
            profile_num(Prof), voter(V), active_voter(Prof,I), I < V.
        ith_voter_modulo_vote(Prof,V,I,I+1) :-
            profile_num(Prof), voter(V), active_voter(Prof,I+1), I >= V.
        %profiles_identical_modulo_two_votes_up_to(Prof1,V1,Prof2,V2,0) :-
        %    profile_num(Prof1), voter(V1), active_voter(Prof1,V1),
        %    profile_num(Prof2), voter(V2), active_voter(Prof2,V2).
        %profiles_identical_modulo_two_votes_up_to(Prof1,V1,Prof2,V2,N) :-
        %    profile_num(Prof1), voter(V1), active_voter(Prof1,V1),
        %    profile_num(Prof2), voter(V2), active_voter(Prof2,V2),
        %    profiles_identical_modulo_two_votes_up_to(Prof1,V1,Prof2,V2,N-1),
        %    ith_voter_modulo_vote(Prof1,V1,N,W1),
        %    ith_voter_modulo_vote(Prof2,V2,N,W2),
        %    votes_identical(Prof1,W1,Prof2,W2).
        %profiles_identical_modulo_two_votes(Prof1,V1,Prof2,V2) :-
        %    profile_num(Prof1), active_voter(Prof1,W),
        %    not active_voter(Prof1,W+1),
        %    profile_num(Prof2), active_voter(Prof2,W),
        %    not active_voter(Prof2,W+1),
        %    active_voter(Prof1,V1), active_voter(Prof2,V2),
        %    profiles_identical_modulo_two_votes_up_to(Prof1,V1,Prof2,V2,W-1).
        profiles_identical_modulo_two_votes(Prof1,V1,Prof2,V2) :-
            profile_num(Prof1), active_voter(Prof1,W),
            not active_voter(Prof1,W+1),
            profile_num(Prof2), active_voter(Prof2,W),
            not active_voter(Prof2,W+1),
            active_voter(Prof1,V1), active_voter(Prof2,V2),
            votes_identical(Prof1,W1,Prof2,W2) :
                ith_voter_modulo_vote(Prof1,V1,N,W1),
                ith_voter_modulo_vote(Prof2,V2,N,W2).
        axiom_applicable(double(Prof1,Prof2),pos_responsiveness(V1,V2,C,P)) :-
            use_axiom(pos_responsiveness),
            pos_axiom_instance(double(Prof1,Prof2),
                pos_responsiveness(V1,V2,C,P)),
            active_profile(Prof1), active_profile(Prof2),
            votes_identical_after_upwards_move(Prof1,V1,Prof2,V2,C,P),
            profiles_identical_modulo_two_votes(Prof1,V1,Prof2,V2).
        axiom_applicable(double(Prof1,Prof2),pos_responsiveness(V1,V2,C,P)) :-
            use_axiom(pos_responsiveness),
            pos_axiom_instance(double(Prof1,Prof2),
                pos_responsiveness(V1,V2,C,P)),
            active_profile(Prof1), active_profile(Prof2),
            votes_identical_after_upwards_move(Prof1,V1,Prof2,V2,C,P),
            profiles_identical_modulo_two_votes(Prof1,V1,Prof2,V2).

        :- axiom_applicable(double(Prof1,Prof2),pos_responsiveness(V1,V2,C,P)),
            active_voter(Prof1,W), not active_voter(Prof2,W).
        :- axiom_applicable(double(Prof1,Prof2),pos_responsiveness(V1,V2,C,P)),
            active_voter(Prof2,W), not active_voter(Prof1,W).
        :- axiom_applicable(double(Prof1,Prof2),pos_responsiveness(V1,V2,C,P)),
            not active_voter(Prof1,V1).
        :- axiom_applicable(double(Prof1,Prof2),pos_responsiveness(V1,V2,C,P)),
            not active_voter(Prof2,V2).

        :- axiom_applicable(double(Prof1,Prof2),pos_responsiveness(V1,V2,C1,P)),
            profile(Prof1,V1,C2,P1), profile(Prof2,V2,C2,P2),
            candidate(C2), C1 != C2,
            |P1-P2| > 1.
        :- axiom_applicable(double(Prof1,Prof2),pos_responsiveness(V1,V2,C,P)),
            profile(Prof1,V1,C,P), profile(Prof2,V2,C,P).

        % TODO: test efficiency of this.. :)
        :- axiom_applicable(double(Prof1,Prof2),pos_responsiveness(V1,V2,C,P)),
            ith_voter_modulo_vote(Prof1,V1,I,J1),
            ith_voter_modulo_vote(Prof2,V2,I,J2),
            profile(Prof1,J1,C',P'),
            not profile(Prof2,J2,C',P').
        :- axiom_applicable(double(Prof1,Prof2),pos_responsiveness(V1,V2,C,P)),
            ith_voter_modulo_vote(Prof1,V1,I,J1),
            ith_voter_modulo_vote(Prof2,V2,I,J2),
            profile(Prof2,J2,C',P'),
            not profile(Prof1,J1,C',P').

        is_used(pos_responsiveness) :-
            use_axiom_instance(Pr,pos_responsiveness(V1,V2,C,P)).
        """
        # """
        # %%% Applicability of POSITIVE RESPONSIVENESS
        # votes_identical_after_upwards_move(Prof1,V1,Prof2,V2,C,P) :-
        #     use_axiom(pos_responsiveness),
        #     profile_num(Prof1), profile_num(Prof2),
        #     active_voter(Prof1,V1), active_voter(Prof2,V2),
        #     pos_response_pair(C,P),
        #     profile(Prof1,V1,C,P1), profile(Prof2,V2,C,P1-P),
        #     profile(Prof2,V2,C2,P2) :
        #         profile(Prof1,V1,C2,P2), P2 > P1;
        #     profile(Prof2,V2,C2,P2) :
        #         profile(Prof1,V1,C2,P2), P2 < P1-P;
        #     profile(Prof2,V2,C2,P2+1) :
        #         profile(Prof1,V1,C2,P2), P2 < P1, P2 >= P1-P.
        # pos_response_check(Prof1,V1,Prof2,V2,C,P) :-
        #     use_axiom(pos_responsiveness),
        #     profile_num(Prof1), profile_num(Prof2),
        #     active_voter(Prof1,V1), active_voter(Prof2,V2),
        #     pos_response_pair(C,P),
        #     votes_identical_after_upwards_move(Prof1,V1,Prof2,V2,C,P),
        #     num_votes_identical(Prof2,V2,Prof2,N2),
        #     num_votes_identical(Prof2,V2,Prof1,N1),
        #     N2 = N1 + 1.
        # pos_response_check(Prof1,V1,Prof2,V2,C,P) :-
        #     use_axiom(pos_responsiveness),
        #     profile_num(Prof1), profile_num(Prof2),
        #     active_voter(Prof1,V1), active_voter(Prof2,V2),
        #     pos_response_pair(C,P),
        #     votes_identical(Prof1,V1,Prof2,V2),
        #     num_votes_identical(Prof2,V2,Prof2,N2),
        #     num_votes_identical(Prof2,V2,Prof1,N1),
        #     N2 = N1 - 1.
        # pos_response_check(Prof1,V1,Prof2,V2,C,P) :-
        #     use_axiom(pos_responsiveness),
        #     profile_num(Prof1), profile_num(Prof2),
        #     active_voter(Prof1,V1), active_voter(Prof2,V2),
        #     pos_response_pair(C,P),
        #     not votes_identical_after_upwards_move(Prof1,V1,Prof2,V2,C,P),
        #     not votes_identical(Prof1,V1,Prof2,V2),
        #     num_votes_identical(Prof2,V2,Prof2,N2),
        #     num_votes_identical(Prof2,V2,Prof1,N1),
        #     N2 = N1.
        # axiom_applicable(double(Prof1,Prof2),pos_responsiveness(V,C,P)) :-
        #     use_axiom(pos_responsiveness),
        #     pos_axiom_instance(double(Prof1,Prof2),pos_responsiveness(V,C,P)),
        #     active_profile(Prof1), active_profile(Prof2),
        #     num_active_voters(Prof1,N), num_active_voters(Prof2,N),
        #     pos_response_check(Prof1,V,Prof2,V2,C,P) : active_voter(Prof2,V2).
        #
        # is_used(pos_responsiveness) :-
        #     use_axiom_instance(Pr,pos_responsiveness(V,C,P)).
        # """
    }, axioms)

    if len(target_outcomes) != len(candidates):
        program += """
            %%% Rule out the 'everyone-wins' rule
            :- not rule_out(all_winners).
        """
        program += program_parts_based_on_axioms({
            "pareto":
            """
            rule_out(all_winners) :- is_used(pareto).
            """,
            "faithfulness":
            """
            rule_out(all_winners) :- is_used(faithfulness).
            """,
            "unanimity":
            """
            rule_out(all_winners) :- is_used(unanimity).
            """,
            "condorcet":
            """
            rule_out(all_winners) :- is_used(condorcet).
            """,
            "positive_responsiveness":
            """
            rule_out(all_winners) :- is_used(pos_responsiveness).
            """,
        }, axioms)

    program += """
        :- not rule_out(lex_firstlast_top).

        rule_out(lex_firstlast_top) :-
            candidate(C),
            target_profile(V,C,1) : target_voter(V).
    """
    program += program_parts_based_on_axioms({
        "cancellation":
        """
        rule_out(lex_firstlast_top) :- is_used(cancellation).
        """,
        "neutrality":
        """
        rule_out(lex_firstlast_top) :- is_used(neutrality2).
        """,
        "condorcet":
        """
        rule_out(lex_firstlast_top) :- is_used(condorcet).
        """,
    }, axioms)

    if not is_borda_winners(target_profile, target_outcomes):
        if "condorcet" in axioms:
            program += """
                :- not is_used(condorcet).
            """
        else:
            program += ":-.\n"

    if not is_plurality_winners(target_profile, target_outcomes):
        program += """
            :- not rule_out(plurality).
            :- not rule_out(plurality_on_size).
        """
        program += program_parts_based_on_axioms({
            "cancellation":
            """
            rule_out(plurality) :- is_used(cancellation).
            rule_out(plurality_on_size) :-
                use_axiom_instance(Pr,cancellation),
                Pr = single(Prof),
                same_size_as_target_profile(Prof).
            """,
            "reinforcement":
            """
            rule_out(plurality_on_size) :- is_used(reinforcement_on_size).
            is_used(reinforcement_on_size) :-
                use_axiom_instance(Pr,reinforcement),
                Pr = triple(Prof1,Prof2,Prof3),
                same_size_as_target_profile(Prof1).
            is_used(reinforcement_on_size) :-
                use_axiom_instance(Pr,reinforcement),
                Pr = triple(Prof1,Prof2,Prof3),
                same_size_as_target_profile(Prof2).
            is_used(reinforcement_on_size) :-
                use_axiom_instance(Pr,reinforcement),
                Pr = triple(Prof1,Prof2,Prof3),
                same_size_as_target_profile(Prof3).
            """,
            "condorcet":
            """
            rule_out(plurality) :- is_used(condorcet).
            rule_out(plurality_on_size) :- is_used(condorcet).
            """,
            "positive_responsiveness":
            """
            rule_out(plurality_on_size) :- is_used(pos_responsiveness_on_size).
            is_used(pos_responsiveness_on_size) :-
                use_axiom_instance(Pr,pos_responsiveness(V1,V2,C,P)),
                Pr = double(Prof1,Prof2),
                same_size_as_target_profile(Prof1).
            rule_out(plurality) :- is_used(pos_responsiveness).
            """,
        }, axioms)

    if not is_nondominated_outcomes(
        target_profile,
        target_outcomes,
        candidates,
    ):
        program += """
            :- not rule_out(nondominated_outcomes).
        """
        # program += program_parts_based_on_axioms({
        #     "reinforcement":
        #     """
        #     rule_out(nondominated_outcomes) :- is_used(reinforcement_on_size).
        #     is_used(reinforcement_on_size) :-
        #         use_axiom_instance(Pr,reinforcement),
        #         Pr = triple(Prof1,Prof2,Prof3),
        #         same_size_as_target_profile(Prof1).
        #     is_used(reinforcement_on_size) :-
        #         use_axiom_instance(Pr,reinforcement),
        #         Pr = triple(Prof1,Prof2,Prof3),
        #         same_size_as_target_profile(Prof2).
        #     is_used(reinforcement_on_size) :-
        #         use_axiom_instance(Pr,reinforcement),
        #         Pr = triple(Prof1,Prof2,Prof3),
        #         same_size_as_target_profile(Prof3).
        #     """,
        #     "condorcet":
        #     """
        #     rule_out(nondominated_outcomes) :- is_used(condorcet).
        #     """,
        #     "positive_responsiveness":
        #     """
        #     rule_out(nondominated_outcomes) :-
        #         is_used(pos_responsiveness_on_size).
        #     is_used(pos_responsiveness_on_size) :-
        #         use_axiom_instance(Pr,pos_responsiveness(V,C,P)),
        #         Pr = double(Prof1,Prof2),
        #         same_size_as_target_profile(Prof1).
        #     """,
        # }, axioms)
        program += program_parts_based_on_axioms({
            "reinforcement":
            """
            rule_out(nondominated_outcomes) :- is_used(reinforcement).
            """,
            "condorcet":
            """
            rule_out(nondominated_outcomes) :- is_used(condorcet).
            """,
            "positive_responsiveness":
            """
            rule_out(nondominated_outcomes) :- is_used(pos_responsiveness).
            """,
        }, axioms)

    program += """
        %%% CONSTANT RULE BUILT-IN COUNTEREXAMPLE (STANDALONE)
        unique_target_outcome(C) :-
            target_outcome(C),
            not target_outcome(C2) : candidate(C2), C2 != C.
        :- candidate(C), not unique_target_outcome(C),
            not rule_out(constant(C)).
    """
    program += program_parts_based_on_axioms({
        "pareto":
        """
        rule_out(constant(C)) :-
            candidate(C), not unique_target_outcome(C),
            use_axiom_instance(single(Prof),pareto(C)).
        """,
        "unanimity":
        """
        rule_out(constant(C)) :-
            candidate(C), not unique_target_outcome(C),
            use_axiom_instance(single(Prof),unanimity),
            profile(Prof,1,C2,1), candidate(C2), C2 != C.
        """,
        "faithfulness":
        """
        rule_out(constant(C)) :-
            candidate(C), not unique_target_outcome(C),
            use_axiom_instance(single(Prof),faithfulness),
            profile(Prof,1,C2,1), candidate(C2), C2 != C.
        """,
        "cancellation":
        """
        rule_out(constant(C)) :-
            candidate(C), not unique_target_outcome(C),
            use_axiom_instance(single(Prof),cancellation).
        """,
        "condorcet":
        """
        rule_out(constant(C)) :-
            candidate(C), not unique_target_outcome(C),
            use_axiom_instance(single(Prof),condorcet(C2)),
            candidate(C2), C2 != C.
        """,
        "neutrality":
        """
        rule_out(constant(C)) :-
            candidate(C), not unique_target_outcome(C),
            use_axiom_instance(double(Prof1,Prof2),neutrality(C,C2)).
        rule_out(constant(C)) :-
            candidate(C), not unique_target_outcome(C),
            use_axiom_instance(double(Prof1,Prof2),neutrality(C2,C)).
        """,
    }, axioms)

    program += """
        %%% Redundant constraint: only use subsequent profile numbers
        :- profile_num(Prof), profile_num(Prof+1),
            profile_used(Prof+1), not profile_used(Prof).

        %%% Symmetry breaking: only guess profiles that are actually used
        profile_used(Prof) :- use_axiom_instance(single(Prof),_).
        profile_used(Prof) :- use_axiom_instance(double(Prof,_),_).
        profile_used(Prof) :- use_axiom_instance(double(_,Prof),_).
        profile_used(Prof) :- use_axiom_instance(triple(Prof,_,_),_).
        profile_used(Prof) :- use_axiom_instance(triple(_,Prof,_),_).
        profile_used(Prof) :- use_axiom_instance(triple(_,_,Prof),_).
        :- active_profile(Prof), not profile_used(Prof).

        %%% Symmetry breaking: only use profiles that are
        %%% connected to the target
        profile_edge(Prof,Prof,Axiom) :-
            use_axiom_instance(single(Prof),Axiom).
        profile_edge(Prof1,Prof2,Axiom) :-
            use_axiom_instance(double(Prof1,Prof2),Axiom).
        profile_edge(Prof1,Prof2,Axiom) :-
            use_axiom_instance(triple(Prof1,Prof2,_),Axiom).
        profile_edge(Prof1,Prof2,Axiom) :-
            use_axiom_instance(triple(Prof1,_,Prof2),Axiom).
        profile_edge(Prof1,Prof2,Axiom) :-
            use_axiom_instance(triple(_,Prof1,Prof2),Axiom).
        profile_edge(Prof1,Prof2,Axiom) :-
            profile_edge(Prof2,Prof1,Axiom).
        profile_connected(1).
        profile_connected(Prof2) :-
            profile_connected(Prof1),
            profile_edge(Prof1,Prof2,_).
        :- profile_used(Prof), not profile_connected(Prof).

        %%% ENSURE NO LEAVES IN THE CONNECTIVITY GRAPH OF PROFILES
        :- profile_edge(Prof1,Prof2,pos_responsiveness(_,_,_,_)),
            Prof1 != Prof2,
            not profile_edge(Prof1',Prof2,_) :
                profile_num(Prof1'), Prof1 != Prof1'.
        :- profile_edge(Prof1,Prof2,neutrality(_,_)),
            Prof1 != Prof2,
            not profile_edge(Prof1',Prof2,_) :
                profile_num(Prof1'), Prof1 != Prof1'.
        :- profile_edge(Prof1,Prof2,reinforcement),
            Prof1 != Prof2,
            not profile_edge(Prof1',Prof2,_) :
                profile_num(Prof1'), Prof1 != Prof1'.

        %%% Symmetry breaking: only use profiles that are
        %%% connected to the target
        % profile_connected(1).
        % profile_connected(Prof1) :-
        %     profile_connected(Prof2),
        %     use_axiom_instance(double(Prof1,Prof2),_).
        % profile_connected(Prof1) :-
        %     profile_connected(Prof2),
        %     use_axiom_instance(double(Prof2,Prof1),_).
        % profile_connected(Prof1) :-
        %     profile_connected(Prof2),
        %     use_axiom_instance(triple(Prof1,Prof2,_),_).
        % profile_connected(Prof1) :-
        %     profile_connected(Prof2),
        %     use_axiom_instance(triple(Prof1,_,Prof2),_).
        % profile_connected(Prof1) :-
        %     profile_connected(Prof2),
        %     use_axiom_instance(triple(_,Prof1,Prof2),_).
        % profile_connected(Prof1) :-
        %     profile_connected(Prof2),
        %     use_axiom_instance(triple(Prof2,Prof1,_),_).
        % profile_connected(Prof1) :-
        %     profile_connected(Prof2),
        %     use_axiom_instance(triple(Prof2,_,Prof1),_).
        % profile_connected(Prof1) :-
        %     profile_connected(Prof2),
        %     use_axiom_instance(triple(_,Prof2,Prof1),_).
        % :- profile_used(Prof), not profile_connected(Prof).

        % %%% Redundant constraint: provide upper bound on
        % %%% number of profiles to use
        % %%% (SEEMS NOT TO GIVE A GOOD TRADEOFF)
        % max_num_profiles(S) :-
        %     S2 = #sum { 1,Prof1,Prof2,Axiom :
        %         use_axiom_instance(double(Prof1,Prof2),Axiom) },
        %     S3 = #sum { 2,Prof1,Prof2,Prof3,Axiom :
        %         use_axiom_instance(triple(Prof1,Prof2,Prof3),Axiom) },
        %     S = 1 + S2 + S3.
        % :- max_num_profiles(S), profile_used(S+1).

        %%% Symmetry breaking: ensure that profiles (except no 1)
        %%% are sorted by size
        :- profile_used(Prof1), profile_used(Prof2), Prof1 < Prof2,
            Prof1 != 1, Prof2 != 1,
            num_active_voters(Prof1,N1),
            num_active_voters(Prof2,N2),
            N2 < N1.

        %%% Symmetry breaking: ensure that same-size profiles (except no 1)
        %%% are lexicographically sorted
        interprof_vote_lex_eq_until(Prof1,Prof2,V,0) :-
            profile_num(Prof1), profile_num(Prof2), Prof1 < Prof2, voter(V).
        interprof_vote_lex_eq_until(Prof1,Prof2,V,Pos) :-
            profile_num(Prof1), profile_num(Prof2), Prof1 < Prof2, voter(V),
            position(Pos), interprof_vote_lex_eq_until(Prof1,Prof2,V,Pos-1),
            profile(Prof1,V,C,Pos), profile(Prof2,V,C,Pos).
        interprof_vote_lex_dom(Prof1,Prof2,V) :-
            profile_num(Prof1), profile_num(Prof2), Prof1 < Prof2, voter(V),
            profile(Prof1,V,C1,Pos), profile(Prof2,V,C2,Pos), C2 < C1,
            interprof_vote_lex_eq_until(Prof1,Prof2,V,Pos-1).
        interprof_lex_eq_until(Prof1,Prof2,0) :-
            profile_num(Prof1), profile_num(Prof2), Prof1 < Prof2.
        interprof_lex_eq_until(Prof1,Prof2,V) :-
            profile_num(Prof1), profile_num(Prof2), Prof1 < Prof2, voter(V),
            interprof_lex_eq_until(Prof1,Prof2,V-1),
            votes_identical(Prof1,V,Prof2,V).
        interprof_lex_dom(Prof1,Prof2) :-
            profile_num(Prof1), profile_num(Prof2), Prof1 < Prof2, voter(V),
            interprof_lex_eq_until(Prof1,Prof2,V-1),
            interprof_vote_lex_dom(Prof1,Prof2,V).
        :- profile_num(Prof1), profile_num(Prof2), Prof1 < Prof2,
            num_active_voters(Prof1,N), num_active_voters(Prof2,N),
            interprof_lex_dom(Prof2,Prof1).

        #show profile/4.
        #show use_axiom_instance/2.
    """
    # program += """
    #     %%% Rules used for early pruning of profile sequences
    #     %%% GENERAL
    #     target_outcome_differs(Rule) :-
    #         rule(Rule), derived_outcome(Rule,1,C),
    #         not target_outcome(C).
    #     target_outcome_differs(Rule) :-
    #         rule(Rule), not derived_outcome(Rule,1,C),
    #         target_outcome(C).
    #     :- rule(Rule), target_outcome_differs(Rule),
    #         rule_satisfies_axiom_instance(Rule,Profiles,Axiom) :
    #             use_axiom_instance(Profiles,Axiom).
    #
    #     %%% REVERSE PLURALITY
    #     rule(reverse_plurality).
    #     amount_last(Prof,C,Num) :-
    #         profile_num(Prof), active_profile(Prof), candidate(C),
    #         Num = #count { V : profile(Prof,V,C,num_candidates) }.
    #     derived_outcome(reverse_plurality,Prof,C) :-
    #         profile_num(Prof), active_profile(Prof), candidate(C),
    #         amount_last(Prof,C,Num),
    #         Num2 <= Num : amount_last(Prof,C2,Num2).
    #     rule_satisfies_axiom_instance(reverse_plurality,single(Prof),
    #     pareto(C)) :-
    #         pos_axiom_instance(single(Prof),pareto(C)),
    #         not derived_outcome(reverse_plurality,Prof,C).
    #     rule_satisfies_axiom_instance(reverse_plurality,
    #     triple(Prof1,Prof2,Prof3),reinforcement) :-
    #         pos_axiom_instance(triple(Prof1,Prof2,Prof3),reinforcement).
    #     rule_satisfies_axiom_instance(reverse_plurality,double(Prof1,Prof2),
    #         neutrality2(C1,C2)) :-
    #         pos_axiom_instance(double(Prof1,Prof2),neutrality2(C1,C2)).
    #     rule_satisfies_axiom_instance(reverse_plurality,double(Prof1,Prof2),
    #         pos_responsiveness(V,C,P)) :-
    #         pos_axiom_instance(double(Prof1,Prof2),pos_responsiveness(V,C,P)),
    #         not derived_outcome(reverse_plurality,Prof1,C).
    #
    #     %%% REVERSE BORDA
    #     rule(reverse_borda).
    #     reverse_borda_score(Prof,C,Num) :-
    #         profile_num(Prof), active_profile(Prof), candidate(C),
    #         Num = #sum { P-1,V : profile(Prof,V,C,P) }.
    #     reverse_borda_beats(Prof,C1,C2) :-
    #         profile_num(Prof), active_profile(Prof),
    #         candidate(C1), candidate(C2), C1 != C2,
    #         reverse_borda_score(Prof,C1,Score1), reverse_borda_score(Prof,C2,Score2),
    #         Score1 > Score2.
    #     reverse_borda_nonwinner(Prof,C1) :-
    #         profile_num(Prof), active_profile(Prof),
    #         candidate(C1), candidate(C2), C1 != C2,
    #         reverse_borda_beats(Prof,C2,C1).
    #     derived_outcome(reverse_borda,Prof,C) :-
    #         profile_num(Prof), active_profile(Prof),
    #         candidate(C),
    #         not reverse_borda_nonwinner(Prof,C).
    #     % derived_outcome(reverse_borda,Prof,C) :-
    #     %     profile_num(Prof), active_profile(Prof), candidate(C),
    #     %     reverse_borda_score(Prof,C,Score),
    #     %     Score2 <= Score : reverse_borda_score(Prof,C2,Score2).
    #     rule_satisfies_axiom_instance(reverse_borda,single(Prof),pareto(C)) :-
    #         pos_axiom_instance(single(Prof),pareto(C)),
    #         derived_outcome(reverse_borda,Prof,C).
    #     rule_satisfies_axiom_instance(reverse_borda,single(Prof),
    #     cancellation) :-
    #         pos_axiom_instance(single(Prof),cancellation).
    #     rule_satisfies_axiom_instance(reverse_borda,triple(Prof1,Prof2,Prof3),
    #         reinforcement) :-
    #         pos_axiom_instance(triple(Prof1,Prof2,Prof3),reinforcement).
    #     rule_satisfies_axiom_instance(reverse_borda,double(Prof1,Prof2),
    #         neutrality2(C1,C2)) :-
    #         pos_axiom_instance(double(Prof1,Prof2),neutrality2(C1,C2)).
    #     rule_satisfies_axiom_instance(reverse_borda,double(Prof1,Prof2),
    #         pos_responsiveness(V,C,P)) :-
    #         pos_axiom_instance(double(Prof1,Prof2),pos_responsiveness(V,C,P)),
    #         not derived_outcome(reverse_borda,Prof1,C).
    # """
    return program


def program_heuristics(axioms):
    program = """
        #heuristic profile(Prof,V,C,P). [-30,init]
        %#heuristic is_used(Rule). [100,init]

        #heuristic is_used(Rule). [20,false]
    """
    program += program_parts_based_on_axioms({
        # "positive_responsiveness":
        # """
        # #heuristic use_axiom_instance(Pr,pos_responsiveness(V1,V2,C,P)).
        #     [100,false]
        # """
    }, axioms)

    return program


def program_size_bounds(profile_size_bounds):
    program = ""
    for profile_num, bound in enumerate(profile_size_bounds, 2):
        if bound:
            program += f"""
                :- active_voter({profile_num},{bound+1}).
            """
    return program


def program_glue():
    program = """
        #program glue.

        % Profiles
        glue(profile(Prof,V,Cand,Pos)) :-
            profile_num(Prof), voter(V), candidate(Cand), position(Pos).

        % Axiom instances used
        glue(use_axiom_instance(Profiles,Axiom)) :-
            pos_axiom_instance(Profiles,Axiom).
    """
    return program


def program_check(
    axioms,
    num_axiom_instances,
):
    if num_axiom_instances:
        return program_check_not_all_instances(axioms)
    return program_check_all_instances(axioms)


def program_check_not_all_instances(
    axioms,
):

    program = """
        #program check.

        %%% Guess (irresolute) outcomes for all profiles
        1 { outcome(Prof,C) : candidate(C) } :- profile_num(Prof).

        %%% Make sure that the outcome for profile 1
        %%% differs from the target outcome
        target_outcome_differs :-
            outcome(1,C), not target_outcome(C), candidate(C).
        target_outcome_differs :-
            not outcome(1,C), target_outcome(C), candidate(C).
        :- not target_outcome_differs.

        %%% Heuristic: satisfy as many axioms as possible
        #heuristic falsified(pos_axiom_instance(Profiles,Axiom)) :
            use_axiom_instance(Profiles,Axiom). [20,false]
        #heuristic falsified(pos_axiom_instance(Profiles,Axiom)) :
            pos_axiom_instance(Profiles,Axiom). [10,false]

        %%% Make sure that the outcomes satisfy all used axiom instances
        :- use_axiom_instance(Profiles,Axiom),
            falsified(pos_axiom_instance(Profiles,Axiom)).
    """
    if "pareto" in axioms:
        program += """
            %%% PARETO
            falsified(pos_axiom_instance(single(Prof),pareto(C))) :-
                pos_axiom_instance(single(Prof),pareto(C)),
                outcome(Prof,C).
        """
    if "faithfulness" in axioms:
        program += """
            %%% FAITHFULNESS
            falsified(pos_axiom_instance(single(Prof),faithfulness)) :-
                pos_axiom_instance(single(Prof),faithfulness),
                profile(Prof,1,C,1), not outcome(Prof,C).
            falsified(pos_axiom_instance(single(Prof),faithfulness)) :-
                pos_axiom_instance(single(Prof),faithfulness),
                profile(Prof,1,C1,1),
                outcome(Prof,C2), candidate(C2), C1 != C2.
        """
    if "unanimity" in axioms:
        program += """
            %%% UNANIMITY
            falsified(pos_axiom_instance(single(Prof),unanimity)) :-
                pos_axiom_instance(single(Prof),unanimity),
                profile(Prof,1,C,1), not outcome(Prof,C).
            falsified(pos_axiom_instance(single(Prof),unanimity)) :-
                pos_axiom_instance(single(Prof),unanimity),
                profile(Prof,1,C1,1),
                outcome(Prof,C2), candidate(C2), C1 != C2.
        """
    if "cancellation" in axioms:
        program += """
            %%% CANCELLATION
            falsified(pos_axiom_instance(single(Prof),cancellation)) :-
                pos_axiom_instance(single(Prof),cancellation),
                not outcome(Prof,C), candidate(C).
        """
    if "reinforcement" in axioms:
        program += """
            %%% REINFORCEMENT
            outcomes_intersect(Prof1,Prof2) :-
                profile_num(Prof1), profile_num(Prof2), Prof1 <= Prof2,
                outcome(Prof1,C), outcome(Prof2,C), candidate(C).
            falsified(pos_axiom_instance(triple(Prof1,Prof2,Prof3),
            reinforcement)) :-
                pos_axiom_instance(triple(Prof1,Prof2,Prof3),reinforcement),
                outcomes_intersect(Prof1,Prof2),
                outcome(Prof3,C), not outcome(Prof1,C).
            falsified(pos_axiom_instance(triple(Prof1,Prof2,Prof3),
            reinforcement)) :-
                pos_axiom_instance(triple(Prof1,Prof2,Prof3),reinforcement),
                outcomes_intersect(Prof1,Prof2),
                outcome(Prof3,C), not outcome(Prof2,C).
            falsified(pos_axiom_instance(triple(Prof1,Prof2,Prof3),
            reinforcement)) :-
                pos_axiom_instance(triple(Prof1,Prof2,Prof3),reinforcement),
                outcomes_intersect(Prof1,Prof2),
                outcome(Prof1,C), outcome(Prof2,C), not outcome(Prof3,C).
        """
    if "condorcet" in axioms:
        program += """
            %%% CONDORCET
            falsified(pos_axiom_instance(single(Prof),condorcet(C))) :-
                pos_axiom_instance(single(Prof),condorcet(C)),
                not outcome(Prof,C).
            falsified(pos_axiom_instance(single(Prof),condorcet(C1))) :-
                pos_axiom_instance(single(Prof),condorcet(C1)),
                outcome(Prof,C2), candidate(C2), C1 != C2.
        """
    if "neutrality" in axioms:
        program += """
            %%% NEUTRALITY/2
            falsified(pos_axiom_instance(double(Prof1,Prof2),
            neutrality2(C1,C2))) :-
                pos_axiom_instance(double(Prof1,Prof2),neutrality2(C1,C2)),
                swap(C1,C2,CS1,CS2), candidate(CS1),
                outcome(Prof1,CS1), not outcome(Prof2,CS2).
            falsified(pos_axiom_instance(double(Prof1,Prof2),
            neutrality2(C1,C2))) :-
                pos_axiom_instance(double(Prof1,Prof2),neutrality2(C1,C2)),
                swap(C1,C2,CS1,CS2), candidate(CS1),
                outcome(Prof2,CS2), not outcome(Prof1,CS1).
        """
    if "positive_responsiveness" in axioms:
        program += """
            %%% POSITIVE RESPONSIVENESS
            falsified(pos_axiom_instance(double(Prof1,Prof2),
            pos_responsiveness(V1,V2,C,P))) :-
                pos_axiom_instance(double(Prof1,Prof2),
                    pos_responsiveness(V1,V2,C,P)),
                candidate(C),
                outcome(Prof1,C), not outcome(Prof2,C).
            falsified(pos_axiom_instance(double(Prof1,Prof2),
            pos_responsiveness(V1,V2,C1,P))) :-
                pos_axiom_instance(double(Prof1,Prof2),
                    pos_responsiveness(V1,V2,C1,P)),
                candidate(C1), candidate(C2), C1 != C2,
                outcome(Prof1,C1), outcome(Prof2,C2).
        """
    program += """
        % %%% REFINEMENT STRATEGY 1
        % relevant(profile(Prof,V,Cand,Pos)) :-
        %     profile_num(Prof), voter(V), candidate(Cand), position(Pos).
        % relevant(use_axiom_instance(Profiles,Axiom)) :-
        %     falsified(pos_axiom_instance(Profiles,Axiom)),
        %     pos_axiom_instance(Profiles,Axiom).

        %%% REFINEMENT STRATEGY 2
        % (SEEMS BEST PERFORMING, SOMEHOW :))
        relevant(profile(Prof,V,Cand,Pos)) :-
            profile_num(Prof), voter(V), candidate(Cand), position(Pos).
        relevant(use_axiom_instance(Profiles,Axiom)) :-
            not falsified(pos_axiom_instance(Profiles,Axiom)),
            pos_axiom_instance(Profiles,Axiom).

        % %%% REFINEMENT STRATEGY 3
        % relevant(profile(Prof,V,Cand,Pos)) :-
        %     profile_num(Prof), voter(V), candidate(Cand), position(Pos).
        % relevant(use_axiom_instance(Profiles,Axiom)) :-
        %     not use_axiom_instance(Profiles,Axiom),
        %     pos_axiom_instance(Profiles,Axiom).

        % %%% REFINEMENT STRATEGY 4
        % relevant(profile(Prof,V,Cand,Pos)) :-
        %     profile_num(Prof), voter(V), candidate(Cand), position(Pos).
        % relevant(use_axiom_instance(Profiles,Axiom)) :-
        %     use_axiom_instance(Profiles,Axiom).

        % %%% REFINEMENT STRATEGY 5
        % relevant(profile(Prof,V,Cand,Pos)) :-
        %     profile_num(Prof), voter(V), candidate(Cand), position(Pos).
        % relevant(use_axiom_instance(Profiles,Axiom)) :-
        %     pos_axiom_instance(Profiles,Axiom).

        % %%% REFINEMENT STRATEGY 6 (ONLY FOR FINDING PROFILES ONLY)
        % relevant(profile(Prof,V,Cand,Pos)) :-
        %     profile_num(Prof), voter(V), candidate(Cand), position(Pos).
    """
    return program


def program_check_all_instances(
    axioms,
):

    program = """
        #program check.

        %%% Guess (irresolute) outcomes for all profiles
        1 { outcome(Prof,C) : candidate(C) } :- profile_num(Prof).

        %%% Make sure that the outcome for profile 1 differs
        %%% from the target outcome
        target_outcome_differs :-
            outcome(1,C), not target_outcome(C), candidate(C).
        target_outcome_differs :-
            not outcome(1,C), target_outcome(C), candidate(C).
        :- not target_outcome_differs.
    """
    if "pareto" in axioms:
        program += """
            %%% PARETO
            :- use_axiom_instance(single(Prof),pareto(C)),
                outcome(Prof,C).
        """
    if "faithfulness" in axioms:
        program += """
            %%% FAITHFULNESS
            :- use_axiom_instance(single(Prof),faithfulness),
                profile(Prof,1,C,1), not outcome(Prof,C).
            :- use_axiom_instance(single(Prof),faithfulness),
                profile(Prof,1,C1,1),
                outcome(Prof,C2), candidate(C2), C1 != C2.
        """
    if "unanimity" in axioms:
        program += """
            %%% UNANIMITY
            :- use_axiom_instance(single(Prof),unanimity),
                profile(Prof,1,C,1), not outcome(Prof,C).
            :- use_axiom_instance(single(Prof),unanimity),
                profile(Prof,1,C1,1),
                outcome(Prof,C2), candidate(C2), C1 != C2.
        """
    if "cancellation" in axioms:
        program += """
            %%% CANCELLATION
            :- use_axiom_instance(single(Prof),cancellation),
                not outcome(Prof,C), candidate(C).
        """
    if "reinforcement" in axioms:
        program += """
            %%% REINFORCEMENT
            outcomes_intersect(Prof1,Prof2) :-
                profile_num(Prof1), profile_num(Prof2), Prof1 <= Prof2,
                outcome(Prof1,C), outcome(Prof2,C), candidate(C).
            :- use_axiom_instance(triple(Prof1,Prof2,Prof3),reinforcement),
                outcomes_intersect(Prof1,Prof2),
                outcome(Prof3,C), not outcome(Prof1,C).
            :- use_axiom_instance(triple(Prof1,Prof2,Prof3),reinforcement),
                outcomes_intersect(Prof1,Prof2),
                outcome(Prof3,C), not outcome(Prof2,C).
            :- use_axiom_instance(triple(Prof1,Prof2,Prof3),reinforcement),
                outcomes_intersect(Prof1,Prof2),
                outcome(Prof1,C), outcome(Prof2,C), not outcome(Prof3,C).
        """
    if "condorcet" in axioms:
        program += """
            %%% CONDORCET
            :- use_axiom_instance(single(Prof),condorcet(C)),
                not outcome(Prof,C).
            :- use_axiom_instance(single(Prof),condorcet(C1)),
                outcome(Prof,C2), candidate(C2), C1 != C2.
        """
    if "neutrality" in axioms:
        program += """
            %%% NEUTRALITY/2
            :- use_axiom_instance(double(Prof1,Prof2),neutrality2(C1,C2)),
                swap(C1,C2,CS1,CS2), candidate(CS1),
                outcome(Prof1,CS1), not outcome(Prof2,CS2).
            :- use_axiom_instance(double(Prof1,Prof2),neutrality2(C1,C2)),
                swap(C1,C2,CS1,CS2), candidate(CS1),
                outcome(Prof2,CS2), not outcome(Prof1,CS1).
        """
    if "positive_responsiveness" in axioms:
        program += """
            %%% POSITIVE RESPONSIVENESS
            :- use_axiom_instance(double(Prof1,Prof2),
            pos_responsiveness(V1,V2,C,P)),
                candidate(C),
                outcome(Prof1,C), not outcome(Prof2,C).
            :- use_axiom_instance(double(Prof1,Prof2),
            pos_responsiveness(V1,V2,C1,P)),
                candidate(C1), candidate(C2), C1 != C2,
                outcome(Prof1,C1), outcome(Prof2,C2).
        """
    program += """
        % %%% REFINEMENT STRATEGY 3
        % relevant(profile(Prof,V,Cand,Pos)) :-
        %     profile_num(Prof), voter(V), candidate(Cand), position(Pos).
        % relevant(use_axiom_instance(Profiles,Axiom)) :-
        %     not use_axiom_instance(Profiles,Axiom),
        %     pos_axiom_instance(Profiles,Axiom).

        % %%% REFINEMENT STRATEGY 4
        % relevant(profile(Prof,V,Cand,Pos)) :-
        %     profile_num(Prof), voter(V), candidate(Cand), position(Pos).
        % relevant(use_axiom_instance(Profiles,Axiom)) :-
        %     use_axiom_instance(Profiles,Axiom).

        % %%% REFINEMENT STRATEGY 5
        % relevant(profile(Prof,V,Cand,Pos)) :-
        %     profile_num(Prof), voter(V), candidate(Cand), position(Pos).
        % relevant(use_axiom_instance(Profiles,Axiom)) :-
        %     pos_axiom_instance(Profiles,Axiom).

        %%% REFINEMENT STRATEGY 6 (ONLY FOR FINDING PROFILES ONLY)
        relevant(profile(Prof,V,Cand,Pos)) :-
            profile_num(Prof), voter(V), candidate(Cand), position(Pos).
    """
    return program


def nondominated_outcomes(profile, candidates):
    outcomes = set()
    for candidate1 in candidates:
        dominated = False
        for candidate2 in candidates:
            if candidate1 != candidate2:
                dominates = True
                for vote in profile:
                    index2 = vote.index(candidate2)
                    index1 = vote.index(candidate1)
                    dominates_in_vote = index2 < index1
                    if not dominates_in_vote:
                        dominates = False
                if dominates:
                    dominated = True
        if not dominated:
            outcomes.add(candidate1)
    return outcomes


def is_nondominated_outcomes(profile, outcomes, candidates):
    winners = nondominated_outcomes(profile, candidates)
    return winners == set(outcomes)


def plurality_winners(profile):
    scores = defaultdict(int)
    for vote in profile:
        candidate = vote[0]
        scores[candidate] += 1
    max_score = 0
    for candidate, score in scores.items():
        if score > max_score:
            max_score = score
    winners = set()
    for candidate, score in scores.items():
        if score == max_score:
            winners.add(candidate)
    return winners


def is_plurality_winners(profile, outcomes):
    winners = plurality_winners(profile)
    return winners == set(outcomes)


def borda_winners(profile):
    scores = defaultdict(int)
    for vote in profile:
        top_score = len(vote)-1
        score = top_score
        for candidate in vote:
            scores[candidate] += score
            score -= 1
    max_score = 0
    for candidate, score in scores.items():
        if score > max_score:
            max_score = score
    winners = set()
    for candidate, score in scores.items():
        if score == max_score:
            winners.add(candidate)
    return winners


def is_borda_winners(profile, outcomes):
    winners = borda_winners(profile)
    return winners == set(outcomes)


def pretty_justification(
    profiles,
    instances,
):
    pretty_repr = ""
    for profile_num, profile in enumerate(profiles, 1):
        pretty_repr += f"Profile {profile_num}: {profile}\n"

    for instance in instances:
        pretty_repr += f"Axiom instance: {instance}\n"

    return pretty_repr


def model_to_justification(
    model,
    idx_to_candidate,
):

    profile_info = {}
    max_profile = 0
    max_position = 0
    max_votes = defaultdict(int)
    instances = set()

    for atom in model.symbols(shown=True):
        if atom.name == "profile":
            profile_num = atom.arguments[0].number
            if profile_num > max_profile:
                max_profile = profile_num
            vote = atom.arguments[1].number
            candidate = atom.arguments[2].number
            position = atom.arguments[3].number
            if position > max_position:
                max_position = position
            if vote > max_votes[profile_num]:
                max_votes[profile_num] = vote
            profile_info[(profile_num, vote, position)] = candidate
        if atom.name == "use_axiom_instance":
            if atom.arguments[1].name == "pareto":
                idx = atom.arguments[1].arguments[0].number
                candidate = idx_to_candidate[idx]
                profile_num = atom.arguments[0].arguments[0].number
                instance = ("pareto", candidate, profile_num)
            if atom.arguments[1].name == "condorcet":
                idx = atom.arguments[1].arguments[0].number
                candidate = idx_to_candidate[idx]
                profile_num = atom.arguments[0].arguments[0].number
                instance = ("condorcet", candidate, profile_num)
            if atom.arguments[1].name == "faithfulness":
                profile_num = atom.arguments[0].arguments[0].number
                instance = ("faithfulness", profile_num)
            if atom.arguments[1].name == "unanimity":
                profile_num = atom.arguments[0].arguments[0].number
                instance = ("unanimity", profile_num)
            if atom.arguments[1].name == "cancellation":
                profile_num = atom.arguments[0].arguments[0].number
                instance = ("cancellation", profile_num)
            if atom.arguments[1].name == "reinforcement":
                profile_num1 = atom.arguments[0].arguments[0].number
                profile_num2 = atom.arguments[0].arguments[1].number
                profile_num3 = atom.arguments[0].arguments[2].number
                instance = (
                    "reinforcement",
                    profile_num1,
                    profile_num2,
                    profile_num3,
                )
            if atom.arguments[1].name == "neutrality2":
                idx1 = atom.arguments[1].arguments[0].number
                candidate1 = idx_to_candidate[idx1]
                idx2 = atom.arguments[1].arguments[1].number
                candidate2 = idx_to_candidate[idx2]
                profile_num1 = atom.arguments[0].arguments[0].number
                profile_num2 = atom.arguments[0].arguments[1].number
                instance = (
                    "neutrality",
                    candidate1,
                    candidate2,
                    profile_num1,
                    profile_num2,
                )
            if atom.arguments[1].name == "pos_responsiveness":
                idx = atom.arguments[1].arguments[2].number
                candidate = idx_to_candidate[idx]
                profile_num1 = atom.arguments[0].arguments[0].number
                profile_num2 = atom.arguments[0].arguments[1].number
                instance = (
                    "positive_responsiveness",
                    candidate,
                    profile_num1,
                    profile_num2,
                )
            instances.add(instance)

    profiles = []
    for profile_num in range(1, max_profile+1):
        votes_list = []
        for vote in range(1, max_votes[profile_num]+1):
            vote_list = [
                idx_to_candidate[profile_info[(profile_num, vote, position)]]
                for position in range(1, max_position+1)
            ]
            votes_list.append(vote_list)
        profiles.append(votes_list)

    return profiles, instances


def find_justification(
    target_profile,
    target_outcomes,
    axioms,
    num_voters=3,
    num_profiles=3,
    num_axiom_instances=None,
    verbose=True,
    num_solutions=1,
    base_timeout=None,
    subseq_timeout=None,
    profile_size_bounds=None,
    additional_code=None,
):

    candidates = set()
    for vote in target_profile:
        for candidate in vote:
            candidates.add(candidate)
    candidates = list(candidates)
    candidates.sort()
    num_candidates = len(candidates)

    candidate_to_idx = {}
    idx_to_candidate = {}
    for idx, candidate in enumerate(candidates, 1):
        candidate_to_idx[candidate] = idx
        idx_to_candidate[idx] = candidate

    target_profile_idxs = [
        [candidate_to_idx[candidate] for candidate in vote]
        for vote in target_profile
    ]
    target_profile_idxs.sort()
    target_outcomes_idxs = [
        candidate_to_idx[outcome] for outcome in target_outcomes
    ]

    control = Control([
        "--heuristic=Domain",
    ])

    program = program_base(
        num_voters,
        num_profiles,
        num_candidates,
        axioms,
        num_axiom_instances,
    )
    program += program_target(
        target_profile_idxs,
        target_outcomes_idxs,
    )
    program += program_guess(
        axioms,
        target_profile,
        target_outcomes,
        candidates,
        num_axiom_instances=num_axiom_instances,
    )
    program += program_heuristics(axioms)
    if profile_size_bounds:
        program += program_size_bounds(profile_size_bounds)
    program += program_glue()
    program += program_check(
        axioms,
        num_axiom_instances,
    )
    if additional_code:
        program += f"""
            #program guess.
            {additional_code}
        """

    check: List[AST] = []
    glue: List[AST] = []
    with ProgramBuilder(control) as bld:
        trans = Transformer(bld, check, glue)
        parse_string(program, trans.add)

    glue_control = Control()
    with ProgramBuilder(glue_control) as glue_bld:
        for stm in glue:
            glue_bld.add(stm)
    glue_control.ground([("base", [])])
    glue_control.configuration.solve.models = 1
    glue = []
    def on_model(model):
        for atom in model.symbols(shown=True):
            if atom.name == "glue":
                glue.append(str(atom.arguments[0]))
    glue_control.solve(on_model=on_model)

    propagator = CheckPropagator(check, glue)
    control.register_propagator(propagator)

    if verbose:
        print(".. Grounding ..")
    control.ground([("base", [])])
    control.configuration.solve.models = num_solutions

    if verbose:
        print(".. Solving ..")

    if base_timeout:
        timeout = base_timeout
    else:
        timeout = -1
    with control.solve(yield_=True, async_=True) as handle:
        solution_num = 1
        while True:
            handle.resume()
            finished = handle.wait(timeout)
            if finished:
                model = handle.model()
                if model is None:
                    # result = handle.get()
                    if verbose:
                        print(".. Search completed ..")
                    break
                profiles, instances = model_to_justification(
                    model,
                    idx_to_candidate,
                )
            else:
                if verbose:
                    print(".. Timeout ..")
                break
            if subseq_timeout:
                timeout = subseq_timeout
            else:
                timeout = -1

            print(f"== Justification {solution_num} ==\n")
            print(f"{pretty_justification(profiles, instances)}")
            solution_num += 1

    if verbose:
        print(f".. Total time: {control.statistics['summary']['times']['total']:.2f} seconds ..")
        print(".. Total number of refinements:", end='')
        print(f" {sum(propagator.num_conflicts)} ..")

### TODO'S:
# - come up with iterative solving strategy/function
# - add comments
#
# - make list of examples
# - add arg-options for sym breaking and optional encodings
# - add arg-options for redundant constraints
# - add arg-options for refinement strategies
# - think of and test heuristics
# - (?) fix constant-rule built-in counterexample, depending on actual outcome
#
# - develop dedicated propagator for pos respons.
