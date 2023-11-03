# This file is part of the materials accompanying the book
# "Mathematical Logic through Python" by Gonczarowski and Nisan,
# Cambridge University Press. Book site: www.LogicThruPython.org
# (c) Yannai A. Gonczarowski and Noam Nisan, 2017-2022
# File name: propositions/semantics.py

"""Semantic analysis of propositional-logic constructs."""

from typing import AbstractSet, Iterable, Iterator, Mapping, Sequence, Tuple

from propositions.syntax import *
from propositions.proofs import *

#: A model for propositional-logic formulas, a mapping from variable names to
#: truth values.
Model = Mapping[str, bool]

def is_model(model: Model) -> bool:
    """Checks if the given dictionary is a model over some set of variable
    names.

    Parameters:
        model: dictionary to check.

    Returns:
        ``True`` if the given dictionary is a model over some set of variable
        names, ``False`` otherwise.
    """
    for key in model:
        if not is_variable(key):
            return False
    return True

def variables(model: Model) -> AbstractSet[str]:
    """Finds all variable names over which the given model is defined.

    Parameters:
        model: model to check.

    Returns:
        A set of all variable names over which the given model is defined.
    """
    assert is_model(model)
    return model.keys()

def evaluate(formula: Formula, model: Model) -> bool:
    """Calculates the truth value of the given formula in the given model.

    Parameters:
        formula: formula to calculate the truth value of.
        model: model over (possibly a superset of) the variable names of the
            given formula, to calculate the truth value in.

    Returns:
        The truth value of the given formula in the given model.

    Examples:
        >>> evaluate(Formula.parse('~(p&q76)'), {'p': True, 'q76': False})
        True

        >>> evaluate(Formula.parse('~(p&q76)'), {'p': True, 'q76': True})
        False
    """
    assert is_model(model)
    assert formula.variables().issubset(variables(model))
    # Task 2.1, edited for Task 3.2
    if formula.root == 'T':
        return True
    elif formula.root == 'F':
        return False
    elif is_variable(formula.root):
        return model[formula.root]
    elif formula.root == '~':
        return (not evaluate(formula.first, model))
    elif formula.root == '&':
        return (evaluate(formula.first, model) and evaluate(formula.second, model))
    elif formula.root == '|':
        return (evaluate(formula.first, model) or evaluate(formula.second, model))
    elif formula.root == '->':
        return (not evaluate(formula.first, model) or evaluate(formula.second, model))
    elif formula.root == '+':
        return (evaluate(formula.first, model) != evaluate(formula.second, model))
    elif formula.root == '<->':
        return (evaluate(formula.first, model) == evaluate(formula.second, model))
    elif formula.root == '-&':
        return not (evaluate(formula.first, model) and evaluate(formula.second, model))
    elif formula.root == '-|':
        return not (evaluate(formula.first, model) or evaluate(formula.second, model))

def all_models(variables: Sequence[str]) -> Iterable[Model]:
    """Calculates all possible models over the given variable names.

    Parameters:
        variables: variable names over which to calculate the models.

    Returns:
        An iterable over all possible models over the given variable names. The
        order of the models is lexicographic according to the order of the given
        variable names, where False precedes True.

    Examples:
        >>> list(all_models(['p', 'q']))
        [{'p': False, 'q': False}, {'p': False, 'q': True}, {'p': True, 'q': False}, {'p': True, 'q': True}]

        >>> list(all_models(['q', 'p']))
        [{'q': False, 'p': False}, {'q': False, 'p': True}, {'q': True, 'p': False}, {'q': True, 'p': True}]
    """
    for v in variables:
        assert is_variable(v)
    # Task 2.2
    def combinations(n: int):
        if n == 1:
            falseList = [False]
            trueList = [True]
            return [falseList, trueList]
        elif n < 1:
            return []
        else:
            previous1 = combinations(n-1)
            previous2 = [False for i in range(2**(n-1))]
            for i in range(len(previous1)):
                previous2[i] = [True] + previous1[i]
                previous1[i] = [False] + previous1[i]
            return previous1 + previous2
    combinationList = combinations(len(variables))
    modelList = []
    for combo in combinationList:
        model = dict()
        for index in range(len(combo)):
            model[variables[index]] = combo[index]
        modelList.append(model)
    return modelList

def truth_values(formula: Formula, models: Iterable[Model]) -> Iterable[bool]:
    """Calculates the truth value of the given formula in each of the given
    models.

    Parameters:
        formula: formula to calculate the truth value of.
        models: iterable over models to calculate the truth value in.

    Returns:
        An iterable over the respective truth values of the given formula in
        each of the given models, in the order of the given models.

    Examples:
        >>> list(truth_values(Formula.parse('~(p&q76)'), all_models(['p', 'q76'])))
        [True, True, True, False]
    """
    # Task 2.3
    valueList = []
    for model in models:
        valueList.append(evaluate(formula, model))
    return valueList

def print_truth_table(formula: Formula) -> None:
    """Prints the truth table of the given formula, with variable-name columns
    sorted alphabetically.

    Parameters:
        formula: formula to print the truth table of.

    Examples:
        >>> print_truth_table(Formula.parse('~(p&q76)'))
        | p | q76 | ~(p&q76) |
        |---|-----|----------|
        | F | F   | T        |
        | F | T   | T        |
        | T | F   | T        |
        | T | T   | F        |
    """
    # Task 2.4
    vars = sorted(list(formula.variables()))
    formString = formula.__repr__()
    table = "|"
    for var in vars:
        table += " " + var + " |"
    table += " " + formString + " |\n|"
    for var in vars:
        table += '-'*(len(var) + 2) + '|'
    table += '-'*(len(formString) + 2) + '|\n|'
    models = all_models(vars)
    count = 0
    for model in models:
        if count != 0:
            table += "\n|"
        for var in vars:
            if evaluate(Formula.parse(var), model):
                table += " T" + " "*len(var) + "|"
            else:
                table += " F" + " "*len(var) + "|"
        if evaluate(formula, model):
            table += " T" + " "*len(formString) + "|"
        else:
            table += " F" + " "*len(formString) + "|"
        count += 1
    print(table)

def is_tautology(formula: Formula) -> bool:
    """Checks if the given formula is a tautology.

    Parameters:
        formula: formula to check.

    Returns:
        ``True`` if the given formula is a tautology, ``False`` otherwise.
    """
    # Task 2.5a
    vars = list(formula.variables())
    models = all_models(vars)
    if len(models) == 0:
        if evaluate(formula, {'z992928478': False}):
            return True
        else:
            return False
    value = True
    for model in models:
        if evaluate(formula, model) == False:
            value = False
            break
    return value

def is_contradiction(formula: Formula) -> bool:
    """Checks if the given formula is a contradiction.

    Parameters:
        formula: formula to check.

    Returns:
        ``True`` if the given formula is a contradiction, ``False`` otherwise.
    """
    # Task 2.5b
    vars = list(formula.variables())
    models = all_models(vars)
    if len(models) == 0:
        if evaluate(formula, {'z992928478': False}):
            return False
        else:
            return True
    value = True
    for model in models:
        if evaluate(formula, model):
            value = False
            break
    return value

def is_satisfiable(formula: Formula) -> bool:
    """Checks if the given formula is satisfiable.

    Parameters:
        formula: formula to check.

    Returns:
        ``True`` if the given formula is satisfiable, ``False`` otherwise.
    """
    # Task 2.5c
    vars = list(formula.variables())
    models = all_models(vars)
    if len(models) == 0:
        if evaluate(formula, {'z992928478': False}):
            return True
        else:
            return False
    value = False
    for model in models:
        if evaluate(formula, model):
            value = True
            break
    return value

def _synthesize_for_model(model: Model) -> Formula:
    """Synthesizes a propositional formula in the form of a single conjunctive
    clause that evaluates to ``True`` in the given model, and to ``False`` in
    any other model over the same variable names.

    Parameters:
        model: model over a nonempty set of variable names, in which the
            synthesized formula is to hold.

    Returns:
        The synthesized formula.
    """
    assert is_model(model)
    assert len(model.keys()) > 0
    # Task 2.6
    formulaList = []
    for var in model:
        if model[var]:
            formulaList.append(Formula(var))
        else:
            formulaList.append(Formula('~', Formula(var)))
    if len(formulaList) == 1:
        return formulaList[0]
    else:
        form = Formula('&', formulaList[0], formulaList[1])
        formulaList.pop(0)
        formulaList.pop(0)
        while len(formulaList) > 0:
            tempForm = form
            form = Formula('&', tempForm, formulaList[0])
            formulaList.pop()
        return form

def synthesize(variables: Sequence[str], values: Iterable[bool]) -> Formula:
    """Synthesizes a propositional formula in DNF over the given variable names,
    that has the specified truth table.

    Parameters:
        variables: nonempty set of variable names for the synthesized formula.
        values: iterable over truth values for the synthesized formula in every
            possible model over the given variable names, in the order returned
            by `all_models`\ ``(``\ `~synthesize.variables`\ ``)``.

    Returns:
        The synthesized formula.

    Examples:
        >>> formula = synthesize(['p', 'q'], [True, True, True, False])
        >>> for model in all_models(['p', 'q']):
        ...     evaluate(formula, model)
        True
        True
        True
        False
    """
    assert len(variables) > 0
    # Task 2.7
    models = all_models(variables)
    formList = []
    for valIndex in range(len(values)):
        if values[valIndex]:
            formList.append(_synthesize_for_model(models[valIndex]))
    if len(formList) == 0:
        return Formula('|', Formula('&', Formula(variables[0]), Formula('~', Formula(variables[0]))), Formula('&', Formula(variables[0]), Formula('~', Formula(variables[0]))))
    elif len(formList) == 1:
        return formList[0]
    else:
        form = Formula('|', formList[0], formList[1])
        formList.pop(0)
        formList.pop(0)
        while len(formList) != 0:
            tempForm = form
            form = Formula('|', tempForm, formList[0])
            formList.pop(0)
        return form
def _synthesize_for_all_except_model(model: Model) -> Formula:
    """Synthesizes a propositional formula in the form of a single disjunctive
    clause that evaluates to ``False`` in the given model, and to ``True`` in
    any other model over the same variable names.

    Parameters:
        model: model over a nonempty set of variable names, in which the
            synthesized formula is to not hold.

    Returns:
        The synthesized formula.
    """
    assert is_model(model)
    assert len(model.keys()) > 0
    # Optional Task 2.8

def synthesize_cnf(variables: Sequence[str], values: Iterable[bool]) -> Formula:
    """Synthesizes a propositional formula in CNF over the given variable names,
    that has the specified truth table.

    Parameters:
        variables: nonempty set of variable names for the synthesized formula.
        values: iterable over truth values for the synthesized formula in every
            possible model over the given variable names, in the order returned
            by `all_models`\ ``(``\ `~synthesize.variables`\ ``)``.

    Returns:
        The synthesized formula.

    Examples:
        >>> formula = synthesize_cnf(['p', 'q'], [True, True, True, False])
        >>> for model in all_models(['p', 'q']):
        ...     evaluate(formula, model)
        True
        True
        True
        False
    """
    assert len(variables) > 0
    # Optional Task 2.9

def evaluate_inference(rule: InferenceRule, model: Model) -> bool:
    """Checks if the given inference rule holds in the given model.

    Parameters:
        rule: inference rule to check.
        model: model to check in.

    Returns:
        ``True`` if the given inference rule holds in the given model, ``False``
        otherwise.

    Examples:
        >>> evaluate_inference(InferenceRule([Formula('p')], Formula('q')),
        ...                    {'p': True, 'q': False})
        False

        >>> evaluate_inference(InferenceRule([Formula('p')], Formula('q')),
        ...                    {'p': False, 'q': False})
        True
    """
    assert is_model(model)
    # Task 4.2

def is_sound_inference(rule: InferenceRule) -> bool:
    """Checks if the given inference rule is sound, i.e., whether its
    conclusion is a semantically correct implication of its assumptions.

    Parameters:
        rule: inference rule to check.

    Returns:
        ``True`` if the given inference rule is sound, ``False`` otherwise.
    """
    # Task 4.3

print(is_tautology(Formula('F')))