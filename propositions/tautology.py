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
    captureList = []
    keys = list(model.keys())
    keys.sort()
    for key in keys:
        if model[key]:
            captureList.append(Formula.parse(key))
        else:
            captureList.append(Formula('~', Formula.parse(key)))
    return captureList

def prove_in_model(formula: Formula, model:Model) -> Proof:
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
    assert formula.operators().issubset({'->', '~'})
    assert is_model(model)
    # Task 6.1b

    # Code follows the approach outlined on p. 87.

    # Case 1 (base case): formula = x or ~x.
    if is_variable(formula.root):
        if evaluate(formula, model):
            statement = InferenceRule(formulas_capturing_model(model), formula)
            lines = [Proof.Line(formula)]
            return Proof(statement, AXIOMATIC_SYSTEM, lines)
        else:
            statement = InferenceRule(formulas_capturing_model(model), Formula('~', formula))
            lines = [Proof.Line(Formula('~', formula))]
            return Proof(statement, AXIOMATIC_SYSTEM, lines)
    # Case 2: The main operator is ->.
    elif formula.root == '->':
        # In this case, we again check if our formula evaluates to true or false.
        if evaluate(formula, model):
            # If it evaluates to true, then we check if the antecedent is false
            # or if the consequent is true. One of these must hold.
            if not evaluate(formula.first, model):
                # If the antecedent is false, we prove its negation recursively
                # and use I2.
                return prove_corollary(prove_in_model(formula.first, model), formula, I2)
            else:
                # If the antecedent is true, the consequent is true. So we recursively
                # prove the consequent and use I1.
                return prove_corollary(prove_in_model(formula.second, model), formula, I1)
        else:
            # If our formula evaluates to false, then we recursively prove the antecedent
            # and the negation of the consequent.
            antecedentProof = prove_in_model(formula.first, model)
            consequentProof = prove_in_model(formula.second, model)
            return combine_proofs(antecedentProof, consequentProof, Formula('~', formula), NI)
    # Case 3: The main operator is ~.
    else:
        # If the formula is of the form ~P,
        # we check if it evaluates to true or false.
        if evaluate(formula, model):
            # If it evaluates to true, then P evaluates to false. So we
            # recursively prove ~P.
            return prove_in_model(formula.first, model)
        else:
            # If, however, the formula evaluates to false, then P evaluates
            # to true, so we prove P and then use double-negation.
            return prove_corollary(prove_in_model(formula.first, model), Formula('~', formula), NN)

def reduce_assumption(proof_from_affirmation: Proof,
                      proof_from_negation: Proof) -> Proof:
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
    assert proof_from_affirmation.statement.conclusion == \
           proof_from_negation.statement.conclusion
    assert len(proof_from_affirmation.statement.assumptions) > 0
    assert len(proof_from_negation.statement.assumptions) > 0
    assert proof_from_affirmation.statement.assumptions[:-1] == \
           proof_from_negation.statement.assumptions[:-1]
    assert Formula('~', proof_from_affirmation.statement.assumptions[-1]) == \
           proof_from_negation.statement.assumptions[-1]
    assert proof_from_affirmation.rules == proof_from_negation.rules
    # Task 6.2
    # Game plan: let A be the assumption set without the last assumption, and let p be the remaining
    # assumption in proof_from_affirmation (so ~p is the remaining assumption in proof_from_negation).
    # Then let c be the conclusion of the proof. Proof_from_affirmation proves c from A u {p}, so the
    # Deduction Theorem will give us a proof of (p->c) from A. Likewise, we get a proof of (~p->c)
    # from the same set A using proof_from negation. Then the rule R with q = p and p = c will let us
    # use combine_proofs to put them together.
    affirmation_implies_conclusion = remove_assumption(proof_from_affirmation)
    negation_implies_conclusion = remove_assumption(proof_from_negation)
    return combine_proofs(affirmation_implies_conclusion, # Proof from affirmation
                          negation_implies_conclusion, # Proof from negation
                          proof_from_affirmation.statement.conclusion, # The formula to prove
                          R)

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
    assert tautology.operators().issubset({'->', '~'})
    assert is_model(model)
    assert sorted(tautology.variables())[:len(model)] == sorted(model.keys())
    # Task 6.3a
    # Check if the model uses all of the tautology's variables
    modelUsesAllTautologyVariables = True
    for variable in tautology.variables():
        if variable not in model.keys():
            modelUsesAllTautologyVariables = False
            break
    if modelUsesAllTautologyVariables: # If it does, then we use prove_in_model.
        return prove_in_model(tautology, model)
    else: # Otherwise, we construct a proof with one additional variable.
        # Start by adding all of the model's current variables to two new models.
        affirmation_model = dict()
        negation_model = dict()
        for key in model.keys():
            affirmation_model[key] = model[key]
            negation_model[key] = model[key]

        # Then we add the next variable, True in one model but False in the other.
        tautologyVariables = sorted(tautology.variables())
        nextVariable = tautologyVariables[len(model)]
        affirmation_model[nextVariable] = True
        negation_model[nextVariable] = False

        # Prove the tautology from each of those.
        affirmation_proof = prove_tautology(tautology, affirmation_model)
        negation_proof = prove_tautology(tautology, negation_model)

        # Use reduce_assumption and you're done.
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
    assert formula.operators().issubset({'->', '~'})
    # Task 6.3b

    # Get all the models over the variables
    formulaVariables = list(formula.variables())
    models = list(all_models(formulaVariables))

    for i in range(len(models)):
        if not evaluate(formula, models[i]): # If the formula evaluates to False anywhere, return that model
            return models[i]
    return prove_tautology(formula) # If it gets through with no Falses, then it's a tautology, so we prove it.

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
    # We work backwards through the assumptions, making each one the antecedent of the next implication.
    current_formula = rule.conclusion
    for i in range(len(rule.assumptions)):
        current_formula = Formula('->', rule.assumptions[-i - 1], current_formula)
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
        assert formula.operators().issubset({'->', '~'})
    # Task 6.4b

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
        assert formula.operators().issubset({'->', '~'})
    # Task 6.5

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
    assert formula.operators().issubset({'T', 'F', '->', '~', '&', '|'})
    assert is_model(model)
    # Optional Task 6.6
