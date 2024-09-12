# This file is part of the materials accompanying the book
# "Mathematical Logic through Python" by Gonczarowski and Nisan,
# Cambridge University Press. Book site: www.LogicThruPython.org
# (c) Yannai A. Gonczarowski and Noam Nisan, 2017-2022
# File name: propositions/tautology.py

"""The Tautology Theorem and its implications."""

from typing import List, Sequence, Union

from logic_utils import frozendict

from propositions.syntax import *
from propositions.semantics import *
from propositions.proofs import *
from propositions.axiomatic_systems import *
from propositions.deduction import *


def formulas_capturing_model(model: Model) -> List[Formula]:
    """Computes the formulas that capture the given model: ``'``\ `x`\ ``'``
    for each variable name `x` that is assigned the value ``True`` in the given
    model, and ``'~``\ `x`\ ``'`` for each variable name `x` that is assigned
    the value ``False``.

    Parameters:
        model: model to construct the formulas for.

    Returns:
        A list of the constructed formulas, ordered alphabetically by variable
        name.

    Examples:
        >>> formulas_capturing_model({'p2': False, 'p1': True, 'q': True})
        [p1, ~p2, q]
    """
    assert is_model(model)
    # Task 6.1a

    formula_list = []
    keys = list(model.keys())
    keys.sort()
    for key in keys:
        if model[key]:
            formula_list.append(Formula.parse(key))
        else:
            formula_list.append(Formula("~", Formula.parse(key)))
    return formula_list


def prove_in_model(formula: Formula, model: Model) -> Proof:
    """Either proves the given formula or proves its negation, from the formulas
    that capture the given model.

    Parameters:
        formula: formula that contains no constants or operators beyond ``'->'``
            and ``'~'``, whose affirmation or negation is to prove.
        model: model from whose formulas to prove.

    Returns:
        If `formula` evaluates to ``True`` in the given model, then a valid
        proof of `formula`; otherwise a valid proof of ``'~``\ `formula`\ ``'``.
        The returned proof is from the formulas that capture the given model, in
        the order returned by `formulas_capturing_model`\ ``(``\ `model`\ ``)``,
        via `~propositions.axiomatic_systems.AXIOMATIC_SYSTEM`.

    Examples:
        >>> proof = prove_in_model(Formula.parse('(p->q7)'),
        ...                        {'q7': False, 'p': False})
        >>> proof.is_valid()
        True
        >>> proof.statement.conclusion
        (p->q7)
        >>> proof.statement.assumptions
        (~p, ~q7)
        >>> proof.rules == AXIOMATIC_SYSTEM
        True

        >>> proof = prove_in_model(Formula.parse('(p->q7)'),
        ...                        {'q7': False, 'p': True})
        >>> proof.is_valid()
        True
        >>> proof.statement.conclusion
        ~(p->q7)
        >>> proof.statement.assumptions
        (p, ~q7)
        >>> proof.rules == AXIOMATIC_SYSTEM
        True
    """
    assert formula.operators().issubset({"->", "~"})
    assert is_model(model)
    # Task 6.1b

    # Code follows the approach outlined on p. 87. The formula, phi, we are asked to
    # prove will fall into one of three cases:
    #   (1) phi is a variable. This is the base case of the recursion. In this case, phi
    #       or ~phi will be an assumption of the proof depending on if phi evaluates to
    #       True or False in the model.
    #   (2) phi = (phi1->phi2) for some formulas phi1 and phi2. If phi evaluates to false
    #       in the model, then phi1 is True and phi2 is False, so we prove phi1 and ~phi2
    #       recursively and use NI. If phi evaluates to True, then there are two subcases
    #           (a) phi1 evaluates to False. Then we recursively prove ~phi1 and use I2.
    #           (b) phi2 evaluates to True. Then we recursively prove phi2 and use I1.
    #   (3) phi = ~psi for some formula psi. If psi is false, then we recursively prove
    #       ~psi = phi. If psi is true, then we recursively prove psi and use NN to prove
    #       ~phi = ~~psi.

    phi = formula

    # (1) phi is a variable (base case)
    if is_variable(phi.root):
        if evaluate(phi, model):
            statement = InferenceRule(formulas_capturing_model(model), phi)
            lines = [Proof.Line(phi)]
            return Proof(statement, AXIOMATIC_SYSTEM, lines)

        statement = InferenceRule(formulas_capturing_model(model), Formula("~", phi))
        lines = [Proof.Line(Formula("~", phi))]
        return Proof(statement, AXIOMATIC_SYSTEM, lines)

    # (2) phi = (phi1->phi2) (recursive case)
    elif phi.root == "->":
        phi1 = phi.first
        phi2 = phi.second
        if not evaluate(phi, model):
            phi1_proof = prove_in_model(phi1, model)
            phi2_proof = prove_in_model(phi2, model)
            return combine_proofs(phi1_proof, phi2_proof, Formula("~", phi), NI)

        # (a) phi1 is False
        if not evaluate(phi1, model):
            return prove_corollary(prove_in_model(phi1, model), phi, I2)
        # (b) phi2 is True
        return prove_corollary(prove_in_model(phi2, model), phi, I1)

    # (3) phi = ~psi (recursive case)
    psi = phi.first
    if evaluate(phi, model):
        return prove_in_model(psi, model)
    return prove_corollary(prove_in_model(psi, model), Formula("~", phi), NN)


def reduce_assumption(
    proof_from_affirmation: Proof, proof_from_negation: Proof
) -> Proof:
    """Combines the two given proofs, both of the same formula `conclusion` and
    from the same assumptions except that the last assumption of the latter is
    the negation of that of the former, into a single proof of `conclusion` from
    only the common assumptions.

    Parameters:
        proof_from_affirmation: valid proof of `conclusion` from one or more
            assumptions, the last of which is an assumption `assumption`.
        proof_from_negation: valid proof of `conclusion` from the same
            assumptions and inference rules of `proof_from_affirmation`, but
            with the last assumption being ``'~``\ `assumption`\ ``'`` instead
            of `assumption`.

    Returns:
        A valid proof of `conclusion` from only the assumptions common to the
        given proofs (i.e., without the last assumption of each), via the same
        inference rules of the given proofs and in addition
        `~propositions.axiomatic_systems.MP`,
        `~propositions.axiomatic_systems.I0`,
        `~propositions.axiomatic_systems.I1`,
        `~propositions.axiomatic_systems.D`, and
        `~propositions.axiomatic_systems.R`.

    Examples:
        If `proof_from_affirmation` is of ``['p', '~q', 'r'] ==> '(p&(r|~r))'``,
        then `proof_from_negation` must be of
        ``['p', '~q', '~r'] ==> '(p&(r|~r))'`` and the returned proof is of
        ``['p', '~q'] ==> '(p&(r|~r))'``.
    """
    assert proof_from_affirmation.is_valid()
    assert proof_from_negation.is_valid()
    assert (
        proof_from_affirmation.statement.conclusion
        == proof_from_negation.statement.conclusion
    )
    assert len(proof_from_affirmation.statement.assumptions) > 0
    assert len(proof_from_negation.statement.assumptions) > 0
    assert (
        proof_from_affirmation.statement.assumptions[:-1]
        == proof_from_negation.statement.assumptions[:-1]
    )
    assert (
        Formula("~", proof_from_affirmation.statement.assumptions[-1])
        == proof_from_negation.statement.assumptions[-1]
    )
    assert proof_from_affirmation.rules == proof_from_negation.rules
    # Task 6.2

    # We only have to use the deduction theorem on both proofs and then use R!
    affirmation_implies_conclusion = remove_assumption(proof_from_affirmation)
    negation_implies_conclusion = remove_assumption(proof_from_negation)
    return combine_proofs(
        affirmation_implies_conclusion,
        negation_implies_conclusion,
        proof_from_affirmation.statement.conclusion,
        R,
    )


def prove_tautology(tautology: Formula, model: Model = frozendict()) -> Proof:
    """Proves the given tautology from the formulas that capture the given
    model.

    Parameters:
        tautology: tautology that contains no constants or operators beyond
            ``'->'`` and ``'~'``, to prove.
        model: model over a (possibly empty) prefix (with respect to the
            alphabetical order) of the variable names of `tautology`, from whose
            formulas to prove.

    Returns:
        A valid proof of the given tautology from the formulas that capture the
        given model, in the order returned by
        `formulas_capturing_model`\ ``(``\ `model`\ ``)``, via
        `~propositions.axiomatic_systems.AXIOMATIC_SYSTEM`.

    Examples:
        >>> proof = prove_tautology(Formula.parse('(~(p->p)->q)'),
        ...                         {'p': True, 'q': False})
        >>> proof.is_valid()
        True
        >>> proof.statement.conclusion
        (~(p->p)->q)
        >>> proof.statement.assumptions
        (p, ~q)
        >>> proof.rules == AXIOMATIC_SYSTEM
        True

        >>> proof = prove_tautology(Formula.parse('(~(p->p)->q)'))
        >>> proof.is_valid()
        True
        >>> proof.statement.conclusion
        (~(p->p)->q)
        >>> proof.statement.assumptions
        ()
        >>> proof.rules == AXIOMATIC_SYSTEM
        True
    """
    assert is_tautology(tautology)
    assert tautology.operators().issubset({"->", "~"})
    assert is_model(model)
    assert sorted(tautology.variables())[: len(model)] == sorted(model.keys())
    # Task 6.3a

    # Base case: the model is over all the variable names in the tautology.
    # Then we use prove_in_model.
    if tautology.variables().issubset(model.keys()):
        return prove_in_model(tautology, model)
    # Recursive case: the model is missing a variable, say x.
    # Then we copy our model twice, adding x = True in one and x = False in the other.
    # We recursively prove the tautology in these two models and use reduce_assumption.
    x = sorted(tautology.variables())[len(model)]
    true_model = dict(model)
    false_model = dict(model)
    true_model[x] = True
    false_model[x] = False

    affirmation_proof = prove_tautology(tautology, true_model)
    negation_proof = prove_tautology(tautology, false_model)
    return reduce_assumption(affirmation_proof, negation_proof)


def proof_or_counterexample(formula: Formula) -> Union[Proof, Model]:
    """Either proves the given formula or finds a model in which it does not
    hold.

    Parameters:
        formula: formula that contains no constants or operators beyond ``'->'``
            and ``'~'``, to either prove or find a counterexample for.

    Returns:
        If the given formula is a tautology, then an assumptionless proof of the
        formula via `~propositions.axiomatic_systems.AXIOMATIC_SYSTEM`,
        otherwise a model in which the given formula does not hold.
    """
    assert formula.operators().issubset({"->", "~"})
    # Task 6.3b

    # We could check if formula is a tautology using is_tautology() from chapter 2, but
    # if is_taulology(model) returned False, we would have to loop through all of the
    # models again to find one that made formula False. So, duplicating the code from
    # is_tautology is more efficient.
    models = list(all_models(list(formula.variables())))
    for i in range(len(models)):
        if not evaluate(formula, models[i]):
            return models[i]
    return prove_tautology(formula)


def encode_as_formula(rule: InferenceRule) -> Formula:
    """Encodes the given inference rule as a formula consisting of a chain of
    implications.

    Parameters:
        rule: inference rule to encode.

    Returns:
        The formula encoding the given rule.

    Examples:
        >>> encode_as_formula(InferenceRule([Formula('p1'), Formula('p2'),
        ...                                  Formula('p3'), Formula('p4')],
        ...                                 Formula('q')))
        (p1->(p2->(p3->(p4->q))))

        >>> encode_as_formula(InferenceRule([], Formula('q')))
        q
    """
    # Task 6.4a

    current_formula = rule.conclusion
    for assumption in reversed(list(rule.assumptions)):
        current_formula = Formula("->", assumption, current_formula)
    return current_formula


def prove_sound_inference(rule: InferenceRule) -> Proof:
    """Proves the given sound inference rule.

    Parameters:
        rule: sound inference rule whose assumptions and conclusion contain no
            constants or operators beyond ``'->'`` and ``'~'``, to prove.

    Returns:
        A valid proof of the given sound inference rule via
        `~propositions.axiomatic_systems.AXIOMATIC_SYSTEM`.
    """
    assert is_sound_inference(rule)
    for formula in {rule.conclusion}.union(rule.assumptions):
        assert formula.operators().issubset({"->", "~"})
    # Task 6.4b

    tautology_proof = prove_tautology(encode_as_formula(rule))
    lines = list(tautology_proof.lines)
    # If the rule had no assumptions, we're done.
    if len(rule.assumptions) == 0:
        return Proof(rule, AXIOMATIC_SYSTEM, lines)
    # Otherwise, we deal with the assumptions, which we do through a loop. At each
    # step in the loop, the last line of the proof is (A_i -> [...]) where A_i is the
    # next assumption to be removed. So, we instantiate that assumption and then use
    # MP to remove it.
    for i in range(len(rule.assumptions)):
        lines.append(Proof.Line(rule.assumptions[i]))
        next_formula = lines[-2].formula.second
        lines.append(Proof.Line(next_formula, MP, [len(lines) - 1, len(lines) - 2]))
    return Proof(rule, AXIOMATIC_SYSTEM, lines)


def model_or_inconsistency(formulas: Sequence[Formula]) -> Union[Model, Proof]:
    """Either finds a model in which all the given formulas hold, or proves
    ``'~(p->p)'`` from these formulas.

    Parameters:
        formulas: formulas that use only the operators ``'->'`` and ``'~'``, to
            either find a model of, or prove ``'~(p->p)'`` from.

    Returns:
        A model in which all of the given formulas hold if such exists,
        otherwise a valid proof of ``'~(p->p)'`` from the given formulas via
        `~propositions.axiomatic_systems.AXIOMATIC_SYSTEM`.
    """
    for formula in formulas:
        assert formula.operators().issubset({"->", "~"})
    # Task 6.5

    # (1) Conjoin all of the formulas together
    formula_list = list(formulas)
    conjoined_formula = formula_list[0]
    for i in range(1, len(formula_list)):
        conjoined_formula = Formula("&", formula_list[i], conjoined_formula)

    # (2) Try to return a model that makes conjoined_formula True
    models = list(all_models(list(conjoined_formula.variables())))
    consistent_model = {}
    for model in models:
        if evaluate(conjoined_formula, model):
            consistent_model = model
            break
    if consistent_model != {}:
        return consistent_model

    # (3) If (2) fails, then prove ~(p->p) from the formulas.
    rule = InferenceRule(formulas, Formula.parse("~(p->p)"))
    return prove_sound_inference(rule)


def prove_in_model_full(formula: Formula, model: Model) -> Proof:
    """Either proves the given formula or proves its negation, from the formulas
    that capture the given model.

    Parameters:
        formula: formula that contains no operators beyond ``'->'``, ``'~'``,
            ``'&'``, and ``'|'`` (and may contain constants), whose affirmation
            or negation is to prove.
        model: model from whose formulas to prove.

    Returns:
        If `formula` evaluates to ``True`` in the given model, then a valid
        proof of `formula`; otherwise a valid proof of ``'~``\ `formula`\ ``'``.
        The returned proof is from the formulas that capture the given model, in
        the order returned by `formulas_capturing_model`\ ``(``\ `model`\ ``)``,
        via `~propositions.axiomatic_systems.AXIOMATIC_SYSTEM_FULL`.

    Examples:
        >>> proof = prove_in_model_full(Formula.parse('(p&q7)'),
        ...                             {'q7': True, 'p': True})
        >>> proof.is_valid()
        True
        >>> proof.statement.conclusion
        (p&q7)
        >>> proof.statement.assumptions
        (p, q7)
        >>> proof.rules == AXIOMATIC_SYSTEM_FULL
        True

        >>> proof = prove_in_model_full(Formula.parse('(p&q7)'),
        ...                             {'q7': False, 'p': True})
        >>> proof.is_valid()
        True
        >>> proof.statement.conclusion
        ~(p&q7)
        >>> proof.statement.assumptions
        (p, ~q7)
        >>> proof.rules == AXIOMATIC_SYSTEM_FULL
        True
    """
    assert formula.operators().issubset({"T", "F", "->", "~", "&", "|"})
    assert is_model(model)
    # Optional Task 6.6

    # --- Code from prove_in_model ---
    # The only change made was replacing calls to prove_in_model with prove_in_model_full
    # and changing AXIOMATIC_SYSTEM to AXIOMATIC_SYSTEM_FULL

    phi = formula

    # (1) phi is a variable
    if is_variable(phi.root):
        if evaluate(phi, model):
            statement = InferenceRule(formulas_capturing_model(model), phi)
            lines = [Proof.Line(phi)]
            return Proof(statement, AXIOMATIC_SYSTEM_FULL, lines)

        statement = InferenceRule(formulas_capturing_model(model), Formula("~", phi))
        lines = [Proof.Line(Formula("~", phi))]
        return Proof(statement, AXIOMATIC_SYSTEM_FULL, lines)

    # (2) phi = (phi1->phi2)
    elif phi.root == "->":
        phi1 = phi.first
        phi2 = phi.second
        if not evaluate(phi, model):
            phi1_proof = prove_in_model_full(phi1, model)
            phi2_proof = prove_in_model_full(phi2, model)
            return combine_proofs(phi1_proof, phi2_proof, Formula("~", phi), NI)

        # (a) phi1 is False
        if not evaluate(phi1, model):
            return prove_corollary(prove_in_model_full(phi1, model), phi, I2)
        # (b) phi2 is True
        return prove_corollary(prove_in_model_full(phi2, model), phi, I1)

    # (3) phi = ~psi
    elif phi.root == "~":
        psi = phi.first
        if evaluate(phi, model):
            return prove_in_model_full(psi, model)
        return prove_corollary(prove_in_model_full(psi, model), Formula("~", phi), NN)

    # --- New code ---
    # When extending task 6.1, we only need to consider 4 new cases:
    #   (1) phi = T. Then we prove phi from additional axiom T.
    #   (2) phi = F. Then we prove ~phi from additional axiom NF.
    #   (3) phi = (phi1&phi2). If phi is True, then phi1 and phi2 are True, so we prove
    #       them recursively and use additional axiom A. If phi is False, then there are
    #       two subcases:
    #           (a) phi1 is False. Then we recursively prove phi1 and use new axiom NA2.
    #           (b) phi2 is False. Then we recursively prove phi2 and use new axiom NA1.
    #   (4) phi = (phi1|phi2). If phi is False, then phi1 and phi2 are False, so we prove
    #       ~phi1 and ~phi2 recursively and use additional axiom NO. If phi is True, then
    #       there are two subcases:
    #           (a) phi1 is True. Then we recursively prove phi1 and use new axiom O2.
    #           (b) phi2 is True. Then we recursively prove phi2 and use new axiom O1.

    # (4) phi = T
    elif phi.root == "T":
        lines = [Proof.Line(phi, T, [])]
        statement = InferenceRule(formulas_capturing_model(model), phi)
        return Proof(statement, AXIOMATIC_SYSTEM_FULL, lines)

    # (5) phi = F
    elif phi.root == "F":
        lines = [Proof.Line(Formula("~", phi), NF, [])]
        statement = InferenceRule(formulas_capturing_model(model), Formula("~", phi))
        return Proof(statement, AXIOMATIC_SYSTEM_FULL, lines)

    # (6) phi = (phi1&phi2)
    elif phi.root == "&":
        phi1 = phi.first
        phi2 = phi.second
        if evaluate(phi, model):
            phi1_proof = prove_in_model_full(phi1, model)
            phi2_proof = prove_in_model_full(phi2, model)
            return combine_proofs(phi1_proof, phi2_proof, phi, A)

        # (a) phi1 is False
        if not evaluate(phi1, model):
            phi1_proof = prove_in_model_full(phi1, model)
            return prove_corollary(phi1_proof, Formula("~", phi), NA2)

        # (b) phi2 is False
        phi2_proof = prove_in_model_full(phi2, model)
        return prove_corollary(phi2_proof, Formula("~", phi), NA1)

    # (7) phi = (phi1|phi2)
    phi1 = phi.first
    phi2 = phi.second
    if not evaluate(phi, model):
        not_phi1_proof = prove_in_model_full(phi1, model)
        not_phi2_proof = prove_in_model_full(phi2, model)
        return combine_proofs(not_phi1_proof, not_phi2_proof, Formula("~", phi), NO)

    # (a) phi1 is True
    if evaluate(phi1, model):
        phi1_proof = prove_in_model_full(phi1, model)
        return prove_corollary(phi1_proof, phi, O2)

    # (b) phi2 is True
    phi2_proof = prove_in_model_full(phi2, model)
    return prove_corollary(phi2_proof, phi, O1)
