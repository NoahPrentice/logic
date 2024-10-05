# This file is part of the materials accompanying the book
# "Mathematical Logic through Python" by Gonczarowski and Nisan,
# Cambridge University Press. Book site: www.LogicThruPython.org
# (c) Yannai A. Gonczarowski and Noam Nisan, 2017-2022
# File name: predicates/completeness.py

"""Building blocks for proving the Completeness Theorem for Predicate Logic."""

from typing import AbstractSet, Container, Set, Union

from logic_utils import fresh_constant_name_generator

from predicates.syntax import *
from predicates.semantics import *
from predicates.proofs import *
from predicates.prover import *
from predicates.deduction import *
from predicates.prenex import *
import itertools


def get_constants(formulas: AbstractSet[Formula]) -> Set[str]:
    """Finds all constant names in the given formulas.

    Parameters:
        formulas: formulas to find all constant names in.

    Returns:
        A set of all constant names used in one or more of the given formulas.
    """
    constants = set()
    for formula in formulas:
        constants.update(formula.constants())
    return constants


def is_closed(sentences: AbstractSet[Formula]) -> bool:
    """Checks whether the given set of prenex-normal-form sentences is closed.

    Parameters:
        sentences: set of prenex-normal-form sentences to check.

    Returns:
        ``True`` if the given set of sentences is primitively, universally, and
        existentially closed; ``False`` otherwise.
    """
    for sentence in sentences:
        assert (
            is_in_prenex_normal_form(sentence) and len(sentence.free_variables()) == 0
        )
    return (
        is_primitively_closed(sentences)
        and is_universally_closed(sentences)
        and is_existentially_closed(sentences)
    )


def is_primitively_closed(sentences: AbstractSet[Formula]) -> bool:
    """Checks whether the given set of prenex-normal-form sentences is
    primitively closed.

    Parameters:
        sentences: set of prenex-normal-form sentences to check.

    Returns:
        ``True`` if for every n-ary relation name from the given sentences, and
        for every n (not necessarily distinct) constant names from the given
        sentences, either the invocation of this relation name over these
        constant names (in order), or the negation of this invocation (or both),
        is one of the given sentences; ``False`` otherwise.
    """
    for sentence in sentences:
        assert (
            is_in_prenex_normal_form(sentence) and len(sentence.free_variables()) == 0
        )
    # Task 12.1a

    # We start by making a function that checks if a single relation is closed.

    def relation_is_closed(
        sentences: AbstractSet[Formula],
        universe: set[Term],
        relation_name: str,
        arity: int,
    ) -> bool:
        """Determines if a single relation is primatively closed in the set of
        sentences.

        Paramaters:
            sentences: set of prenex-normal-form sentences.
            universe: set of constants in the sentences, as terms.
            relation_name: the relation name to check.
            arity: the relation's arity.

        Returns:
            ``True`` if, for every possible combination of arguments which may be
            related, either the primative sentence stating that they are related or its
            negation is in ``sentences``.
        """

        # (1) Find all possible arguments for the relation (which is all possible tuples
        # of elements from our universe, Omega^n)
        Omega_n = list(itertools.product(universe, repeat=arity))

        # (2) For all possible arguments, check if the relation's primative or its
        # negation is in sentences.
        for arguments in Omega_n:
            primative = Formula(relation_name, arguments)
            negation = Formula("~", primative)
            if not (primative in sentences) and not (negation in sentences):
                return False
        return True

    # Then we check each relation of each sentence, skipping ones we already checked.
    universe = set(Term(constant_name) for constant_name in get_constants(sentences))
    checked_relations = set()

    for sentence in sentences:
        sentence_relations = set(sentence.relations()).difference(checked_relations)
        for relation_name, arity in sentence_relations:
            checked_relations.add((relation_name, arity))
            if not relation_is_closed(sentences, universe, relation_name, arity):
                return False
    return True


def is_universally_closed(sentences: AbstractSet[Formula]) -> bool:
    """Checks whether the given set of prenex-normal-form sentences is
    universally closed.

    Parameters:
        sentences: set of prenex-normal-form sentences to check.

    Returns:
        ``True`` if for every universally quantified sentence from the given set
        of sentences, and for every constant name from these sentences, the
        statement quantified by this sentence, with every free occurrence of the
        universal quantification variable name replaced with this constant name,
        is also in the given set; ``False`` otherwise.
    """
    for sentence in sentences:
        assert (
            is_in_prenex_normal_form(sentence) and len(sentence.free_variables()) == 0
        )
    # Task 12.1b

    def universal_is_closed(
        sentences: AbstractSet[Formula], universal: Formula, universe: set[Term]
    ) -> bool:
        """Checks whether a single universally quantified sentence is closed.

        Parameters:
            sentences: set of prenex-normal-form sentences.
            universal: formula whose root is a universal quantification.
            universe: set of constants.

        Returns:
            True if every universal instantiation of universal is in sentences; False
            otherwise.
        """

        statement = universal.statement
        variable = universal.variable
        for element in universe:
            if statement.substitute({variable: element}) not in sentences:
                return False
        return True

    universe = set(Term(constant_name) for constant_name in get_constants(sentences))
    for sentence in sentences:
        if sentence.root != "A":
            continue
        if not universal_is_closed(sentences, sentence, universe):
            return False
    return True


def is_existentially_closed(sentences: AbstractSet[Formula]) -> bool:
    """Checks whether the given set of prenex-normal-form sentences is
    existentially closed.

    Parameters:
        sentences: set of prenex-normal-form sentences to check.

    Returns:
        ``True`` if for every existentially quantified sentence from the given
        set of sentences there exists a constant name such that the statement
        quantified by this sentence, with every free occurrence of the
        existential quantification variable name replaced with this constant
        name, is also in the given set; ``False`` otherwise.
    """
    for sentence in sentences:
        assert (
            is_in_prenex_normal_form(sentence) and len(sentence.free_variables()) == 0
        )
    # Task 12.1c

    def existential_is_closed(
        sentences: AbstractSet[Formula], existential: Formula, universe: set[Term]
    ) -> bool:
        """Checks whether a single existentially quantified sentence is closed.

        Parameters:
            sentences: set of prenex-normal-form sentences.
            universal: formula whose root is an existential quantification.
            universe: set of constants.

        Returns:
            True if some instantiation of existential is in sentences; False otherwise.
        """
        statement = existential.statement
        variable = existential.variable
        for element in universe:
            if statement.substitute({variable: element}) in sentences:
                return True
        return False

    universe = set(Term(constant_name) for constant_name in get_constants(sentences))
    for sentence in sentences:
        if sentence.root != "E":
            continue
        if not existential_is_closed(sentences, sentence, universe):
            return False
    return True


def find_unsatisfied_quantifier_free_sentence(
    sentences: Container[Formula], model: Model[str], unsatisfied: Formula
) -> Formula:
    """
    Given a universally and existentially closed set of prenex-normal-form
    sentences, given a model whose universe is the set of all constant names
    from the given sentences, and given a sentence from the given set that the
    given model does not satisfy, finds a quantifier-free sentence from the
    given set that the given model does not satisfy.

    Parameters:
        sentences: universally and existentially closed set of
            prenex-normal-form sentences, which is only to be accessed using
            containment queries, i.e., using the ``in`` operator as in:

            >>> if sentence in sentences:
            ...     print('contained!')

        model: model for all element names from the given sentences, whose
            universe is `get_constants`\ ``(``\ `sentences`\ ``)``.
        unsatisfied: sentence (which possibly contains quantifiers) from the
            given sentences that is not satisfied by the given model.

    Returns:
        A quantifier-free sentence from the given set of sentences that is not
        satisfied by the given model.
    """
    # We assume that every formula in sentences is in prenex normal form and has
    # no free variable names, that sentences is universally and existentially
    # closed, and that the set of constant names that appear somewhere in
    # sentences is model.universe; but we cannot assert these since we cannot
    # iterate over sentences.
    for constant in model.universe:
        assert is_constant(constant)
    assert is_in_prenex_normal_form(unsatisfied)
    assert len(unsatisfied.free_variables()) == 0
    assert unsatisfied in sentences
    assert not model.evaluate_formula(unsatisfied)
    # Task 12.2

    # Base case
    if is_quantifier_free(unsatisfied):
        return unsatisfied

    # Recursive case
    # If the unsatisfied formula is not quantifier-free, then it is of the form
    # Qx[phi(x)] for some quantifier Q, some variable name x, and some parametrized
    # formula phi. We consider 2 cases:
    #   (1) Q = E (existential quantification). Then we
    #       (a) Find an existential witness phi(c) for the original formula, which must
    #           be unsatisfied as the original formula is.
    #       (b) Recursively find an unsatisfied quantifier-free sentence from phi(c).
    #   (2) Q = A (universal quantification). Then we
    #       (a) Find a constant c that makes phi(c) false (one must exist as the
    #           original formula is unsatisfied).
    #       (b) Recursively find an unsatisfied quantifier-free sentence from phi(c).

    Q = unsatisfied.root
    x = unsatisfied.variable
    phi = unsatisfied.statement

    # (1) Existential quantification
    if Q == "E":
        # (a) Find an existential witness
        for constant in model.universe:
            if phi.substitute({x: Term(constant)}) in sentences:
                c = Term(constant)
                break
        # (b) Recurse
        return find_unsatisfied_quantifier_free_sentence(
            sentences, model, phi.substitute({x: c})
        )

    # (2) Universal quantification

    # (a) Find a constant c that makes phi(c) false
    for constant in model.universe:
        if not model.evaluate_formula(phi.substitute({x: Term(constant)})):
            c = Term(constant)
            break
    # (b) Recurse
    return find_unsatisfied_quantifier_free_sentence(
        sentences, model, phi.substitute({x: c})
    )


def get_primitives(quantifier_free: Formula) -> Set[Formula]:
    """Finds all primitive subformulas of the given quantifier-free formula.

    Parameters:
        quantifier_free: quantifier-free formula that contains no function names
            and no equalities, whose subformulas are to be searched.

    Returns:
        The primitive subformulas (i.e., relation invocations) of which the
        given quantifier-free formula is composed using logical operators.

    Examples:
        The primitive subformulas of ``'(R(c1,d)|~(Q(c1)->~R(c2,a)))'`` are
        ``'R(c1,d)'``, ``'Q(c1)'``, and ``'R(c2,a)'``.
    """
    assert is_quantifier_free(quantifier_free)
    assert len(quantifier_free.functions()) == 0
    assert "=" not in str(quantifier_free)
    # Task 12.3a

    if is_relation(quantifier_free.root):
        return {quantifier_free}
    elif is_unary(quantifier_free.root):
        return get_primitives(quantifier_free.first)
    # Binary operator
    return get_primitives(quantifier_free.first).union(
        get_primitives(quantifier_free.second)
    )


def model_or_inconsistency(sentences: AbstractSet[Formula]) -> Union[Model[str], Proof]:
    """Either finds a model in which the given closed set of prenex-normal-form
    sentences holds, or proves a contradiction from these sentences.

    Parameters:
        sentences: closed set of prenex-normal-form sentences that contain no
            function names and no equalities, to either find a model of, or
            prove a contradiction from.

    Returns:
        A model in which all of the given sentences hold if such exists,
        otherwise a valid proof of  a contradiction from the given formulas via
        `~predicates.prover.Prover.AXIOMS`.
    """
    assert is_closed(sentences)
    for sentence in sentences:
        assert len(sentence.functions()) == 0
        assert "=" not in str(sentence)
    # Task 12.3b

    # We proceed in several steps:
    #   (1) Build the model from the set of sentences, by
    #       (a) getting the universe as the constant names in the sentences, and by
    #           interpreting constants as their own names, and
    #       (b) interpreting relations through the primatives that appear in sentences
    #   (2) If the model is a model of the sentences, return it. Otherwise, we
    #       (a) find a quantifier-free sentence that is unsatisfied by the model,
    #       (b) create a proof whose assumptions are our axioms and the sentences,
    #       (c) instantiate every sentence that is a primative or its negation, as well
    #           as the unsatisfied formula from (a), and
    #       (d) tautologically infer the contradiction (unsatisfied&~unsatisfied).

    # (1) Build the model from the set of sentences

    # (a) Get the universe and constant interpretations
    universe = get_constants(sentences)
    constant_interpretations = {c: c for c in universe}

    # (b) Get the relation interpretations through the primatives in sentences

    def interpret_relation(
        sentences: AbstractSet[Formula], relation_name: str, arity: int
    ) -> set[Tuple[str]]:
        """Gets the interpretation of a single relation from the primatives that appear
        in the given set of sentences.

        Parameters:
            sentences: set of closed sentences.
            relation_name: name of relation to interpret
            arity: arity of relation_name.

        Returns:
            A set of all argument-tuples which appear in a primative relation invocation
            of the given relation in the given set of sentences. The arguments in the
            tuples are strings.
        """
        relation_interpretation = set()
        for sentence in sentences:
            if sentence.root != relation:
                continue
            arguments = tuple([str(argument) for argument in sentence.arguments])
            relation_interpretation.add(arguments)
        return relation_interpretation

    relations = set()
    for sentence in sentences:
        relations.update(sentence.relations())

    relation_interpretations = dict()
    for relation, arity in relations:
        relation_interpretations[relation] = interpret_relation(
            sentences, relation, arity
        )

    model = Model(universe, constant_interpretations, relation_interpretations)

    # (2) If the model is a model of the sentences, we return it
    if model.is_model_of(sentences):
        return model

    # Otherwise, we (a) find a quantifier-free sentence that is unsatisfied

    for sentence in sentences:
        if not model.evaluate_formula(sentence):
            unsatisfied = sentence
            break
    unsatisfied = find_unsatisfied_quantifier_free_sentence(
        sentences, model, unsatisfied
    )

    # (b) Create a proof
    proof = Prover(set(sentences).union(Prover.AXIOMS))

    # (c) Instantiate all primatives or their negations, as well as ``unsatisfied``
    primatives_in_unsatisfied = get_primitives(unsatisfied)
    for primative in primatives_in_unsatisfied:
        if primative in sentences:
            proof.add_assumption(primative)
        if Formula("~", primative) in sentences:
            proof.add_assumption(Formula("~", primative))

    unsatisfied_line_number = proof.add_assumption(unsatisfied)

    # (d) Tautologically infer the contradiction (unsatisfied&~unsatisfied).
    contradiction = Formula("&", unsatisfied, Formula("~", unsatisfied))
    proof.add_tautological_implication(
        contradiction, {i for i in range(len(proof._lines))}
    )
    return proof.qed()


def combine_contradictions(
    proof_from_affirmation: Proof, proof_from_negation: Proof
) -> Proof:
    """Combines the given two proofs of contradictions, both from the same
    assumptions/axioms except that the latter has an extra assumption that is
    the negation of an extra assumption that the former has, into a single proof
    of a contradiction from only the common assumptions/axioms.

    Parameters:
        proof_from_affirmation: valid proof of a contradiction from one or more
            assumptions/axioms that are all sentences and that include
            `~predicates.prover.Prover.AXIOMS`.
        proof_from_negation: valid proof of a contradiction from the same
            assumptions/axioms of `proof_from_affirmation`, but with one
            simple assumption (i.e., without any templates) `assumption`
            replaced with its negation ``'~``\ `assumption`\ ``'``.

    Returns:
        A valid proof of a contradiction from only the assumptions/axioms common
        to the given proofs (i.e., without `assumption` or its negation).
    """
    assert proof_from_affirmation.is_valid()
    assert proof_from_negation.is_valid()
    common_assumptions = proof_from_affirmation.assumptions.intersection(
        proof_from_negation.assumptions
    )
    assert len(common_assumptions) == len(proof_from_affirmation.assumptions) - 1
    assert len(common_assumptions) == len(proof_from_negation.assumptions) - 1
    affirmed_assumption = list(proof_from_affirmation.assumptions - common_assumptions)[
        0
    ]
    negated_assumption = list(proof_from_negation.assumptions - common_assumptions)[0]
    assert len(affirmed_assumption.templates) == 0
    assert len(negated_assumption.templates) == 0
    assert negated_assumption.formula == Formula("~", affirmed_assumption.formula)
    assert proof_from_affirmation.assumptions.issuperset(Prover.AXIOMS)
    assert proof_from_negation.assumptions.issuperset(Prover.AXIOMS)
    for assumption in common_assumptions.union(
        {affirmed_assumption, negated_assumption}
    ):
        assert len(assumption.formula.free_variables()) == 0
    # Task 12.4

    # Let phi be the extra assumption in proof_from_affirmation. We use proof by way of
    # contradiction to deduce ~phi from proof_from_affirmation, and to deduce ~~phi from
    # proof_from_negation. The conjunction of these is a contradiction.
    phi = affirmed_assumption.formula
    not_phi = negated_assumption.formula
    not_not_phi = Formula("~", not_phi)

    proof = Prover(common_assumptions)
    not_affirmation_line_number = proof.add_proof(
        not_phi, prove_by_way_of_contradiction(proof_from_affirmation, phi)
    )
    not_negation_line_number = proof.add_proof(
        not_not_phi, prove_by_way_of_contradiction(proof_from_negation, not_phi)
    )

    proof.add_tautological_implication(
        Formula("&", not_phi, not_not_phi),
        {not_affirmation_line_number, not_negation_line_number},
    )
    return proof.qed()


def eliminate_universal_instantiation_assumption(
    proof: Proof, universal: Formula, constant: str
) -> Proof:
    """Converts the given proof of a contradiction, whose assumptions/axioms
    include `universal` and `instantiation`, where the latter is the universal
    instantiation of the former with the constant name `constant`, to a proof
    of a contradiction from the same assumptions without `instantiation`.

    Parameters:
        proof: valid proof of a contradiction from one or more
            assumptions/axioms that are all sentences and that include
            `~predicates.prover.Prover.AXIOMS`.
        universal: assumption of the given proof that is universally quantified.
        constant: constant name such that the formula `instantiation` obtained
            from the statement quantified by `universal` by replacing all free
            occurrences of the universal quantification variable name by the
            given constant name, is an assumption of the given proof.

    Returns:
        A valid proof of a contradiction from the assumptions/axioms of the
        given proof except `instantiation`.
    """
    assert proof.is_valid()
    assert Schema(universal) in proof.assumptions
    assert universal.root == "A"
    assert is_constant(constant)
    assert (
        Schema(universal.statement.substitute({universal.variable: Term(constant)}))
        in proof.assumptions
    )
    for assumption in proof.assumptions:
        assert len(assumption.formula.free_variables()) == 0
    # Task 12.5

    # We suppose universal = Ax[phi(x)], and constant = c. We use proof by contradiction
    # to prove ~phi(c) (as phi(c) is an assumption of ``proof``), and then we instantiate
    # universal to prove phi(c). The conjunction of these is a contradiction.
    phi = universal.statement
    x = universal.variable
    c = constant
    phi_c = phi.substitute({x: Term(c)})
    not_phi_c = Formula("~", phi_c)

    new_assumptions = set(proof.assumptions).difference({Schema(phi_c)})
    new_proof = Prover(new_assumptions)
    not_phi_c_line_number = new_proof.add_proof(
        not_phi_c, prove_by_way_of_contradiction(proof, phi_c)
    )
    universal_line_number = new_proof.add_assumption(universal)
    phi_c_line_number = new_proof.add_universal_instantiation(
        phi_c, universal_line_number, c
    )
    new_proof.add_tautological_implication(
        Formula("&", phi_c, not_phi_c), {not_phi_c_line_number, phi_c_line_number}
    )
    return new_proof.qed()


def universal_closure_step(sentences: AbstractSet[Formula]) -> Set[Formula]:
    """Augments the given sentences with all universal instantiations of each
    universally quantified sentence from these sentences, with respect to all
    constant names from these sentences.

    Parameters:
        sentences: prenex-normal-form sentences to augment with their universal
            instantiations.

    Returns:
        A set of all of the given sentences, and in addition any formula that
        can be obtained from the statement quantified by any universally
        quantified sentence from the given sentences by replacing all
        occurrences of the quantification variable name with some constant name
        from the given sentences.
    """
    for sentence in sentences:
        assert (
            is_in_prenex_normal_form(sentence) and len(sentence.free_variables()) == 0
        )
    # Task 12.6

    sentences = set(sentences)
    universe = set(Term(constant) for constant in get_constants(sentences))
    universals = [sentence for sentence in sentences if sentence.root == "A"]
    for universal in universals:
        for constant in universe:
            sentences.add(
                universal.statement.substitute({universal.variable: constant})
            )
    return sentences


def replace_constant(proof: Proof, constant: str, variable: str = "zz") -> Proof:
    """Replaces all occurrences of the given constant name in the given proof
    with the given variable name.

    Parameters:
        proof: valid proof in which to replace.
        constant: constant name that does not appear as a template constant name
            in any of the assumptions of the given proof.
        variable: variable name that does not appear anywhere in the given proof
            or in its assumptions.

    Returns:
        A valid proof where every occurrence of the given constant name in the
        given proof and in its assumptions is replaced with the given variable
        name.
    """
    assert proof.is_valid()
    assert is_constant(constant)
    assert is_variable(variable)
    for assumption in proof.assumptions:
        assert constant not in assumption.templates
        assert variable not in assumption.formula.variables()
    for line in proof.lines:
        assert variable not in line.formula.variables()
    # Task 12.7a


def eliminate_existential_witness_assumption(
    proof: Proof, existential: Formula, constant: str
) -> Proof:
    """Converts the given proof of a contradiction, whose assumptions/axioms
    include `existential` and `witness`, where the latter is the existential
    witness of the former with the witnessing constant name `constant`, to a
    proof of a contradiction from the same assumptions without `witness`.

    Parameters:
        proof: valid proof, which does not contain the variable name ``'zz'`` in
            its lines or assumptions, of a contradiction from one or more
            assumptions/axioms that are all sentences and that include
            `~predicates.prover.Prover.AXIOMS`.
        existential: assumption of the given proof that is existentially
            quantified.
        constant: constant name such that the formula `witness` obtained from
            from the statement quantified by `existential` by replacing all free
            occurrences of the existential quantification variable name by the
            given constant name, is an assumption of the given proof, and such
            that this constant name does not appear in any assumption of the
            given proof except `witness`.

    Returns:
        A valid proof of a contradiction from the assumptions/axioms of the
        given proof except `witness`.
    """
    assert proof.is_valid()
    assert Schema(existential) in proof.assumptions
    assert existential.root == "E"
    assert is_constant(constant)
    witness = existential.statement.substitute({existential.variable: Term(constant)})
    assert Schema(witness) in proof.assumptions
    for assumption in proof.assumptions:
        assert len(assumption.formula.free_variables()) == 0
        assert "zz" not in assumption.formula.variables()
    for assumption in proof.assumptions - {Schema(witness)}:
        assert constant not in assumption.formula.constants()
    for line in proof.lines:
        assert "zz" not in line.formula.variables()
    # Task 12.7b


def existential_closure_step(sentences: AbstractSet[Formula]) -> Set[Formula]:
    """Augments the given sentences with an existential witness that uses a new
    constant name, for each existentially quantified sentence from these
    sentences for which an existential witness is missing.

    Parameters:
        sentences: prenex-normal-form sentences to augment with any missing
            existential witnesses.

    Returns:
        A set of all of the given sentences, and in addition for every
        existentially quantified sentence from the given sentences, a formula
        obtained from the statement quantified by that sentence by replacing all
        occurrences of the quantification variable name with a new constant name
        obtained by calling
        `next`\ ``(``\ `~logic_utils.fresh_constant_name_generator`\ ``)``.
    """
    for sentence in sentences:
        assert (
            is_in_prenex_normal_form(sentence) and len(sentence.free_variables()) == 0
        )
    # Task 12.8
