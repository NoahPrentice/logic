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
    if formula.root == "T":
        return True
    elif formula.root == "F":
        return False
    elif is_variable(formula.root):
        return model[formula.root]
    elif formula.root == "~":
        return not evaluate(formula.first, model)
    elif formula.root == "&":
        return evaluate(formula.first, model) and evaluate(formula.second, model)
    elif formula.root == "|":
        return evaluate(formula.first, model) or evaluate(formula.second, model)
    elif formula.root == "->":
        return not evaluate(formula.first, model) or evaluate(formula.second, model)
    elif formula.root == "+":
        return evaluate(formula.first, model) != evaluate(formula.second, model)
    elif formula.root == "<->":
        return evaluate(formula.first, model) == evaluate(formula.second, model)
    elif formula.root == "-&":
        return not (evaluate(formula.first, model) and evaluate(formula.second, model))
    elif formula.root == "-|":
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

    # The main work comes from finding all possible n-tuples (or lists of length n)
    # containing only True and False. This is done with the following helper function.
    def combinations(n: int) -> list:
        """Creates a list of all n-tuples containing only True and False.

        Parameters:
            n: length of tuples to generate.

        Returns:
            A list of all n-tuples containing only True and False, in
            lexicographic order, e.g., combinations(2) returns
            [[False, False], [False, True], [True, False], [True, True]].
        """
        # Base case
        if n == 1:
            falseList = [False]
            trueList = [True]
            return [falseList, trueList]
        elif n < 1:
            return []

        # Recursive case
        # We recursively find all (n-1)-tuples, and then add False or True to the start
        # of each tuple. Combining the results gives us what we wanted.
        previous1 = combinations(n - 1)
        previous2 = previous1.copy()
        for i in range(len(previous1)):
            previous1[i] = [False] + previous1[i]
            previous2[i] = [True] + previous2[i]
        return previous1 + previous2

    # With this above helper function, building the model is as simple is turning each
    # n-tuple it gave us into a dictionary.
    combination_list = combinations(len(variables))
    for combo in combination_list:
        model = dict()
        for index in range(len(combo)):
            model[variables[index]] = combo[index]
        yield model


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
    for model in models:
        yield evaluate(formula, model)


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

    # I build the truth table into a single string. We do this in two steps:
    #   (i) create the header of the table by adding all of the variables and the
    #       formula, separated by vertical bars, and then adding a horizontal line.
    #   (ii) add a new line for each possible model over the variables, with the
    #       truth values of the variables and formula underneath.

    # (i) Create the header of the table
    variables = sorted(list(formula.variables()))
    formula_string = str(formula)
    table = "|"
    for variable in variables:
        table += " " + variable + " |"
    table += " " + formula_string + " |\n|"
    for variable in variables:
        table += "-" * (len(variable) + 2) + "|"
    table += "-" * (len(formula_string) + 2) + "|\n|"

    # (ii) add a new line for each possible model over the variables
    models = all_models(variables)
    is_first_line = True
    for model in models:
        if not is_first_line:
            table += "\n|"
        for variable in variables:
            if evaluate(Formula.parse(variable), model):
                table += " T" + " " * len(variable) + "|"
            else:
                table += " F" + " " * len(variable) + "|"
        if evaluate(formula, model):
            table += " T" + " " * len(formula_string) + "|"
        else:
            table += " F" + " " * len(formula_string) + "|"
        is_first_line = False
    print(table)


def is_tautology(formula: Formula) -> bool:
    """Checks if the given formula is a tautology.

    Parameters:
        formula: formula to check.

    Returns:
        ``True`` if the given formula is a tautology, ``False`` otherwise.
    """
    # Task 2.5a

    variables = list(formula.variables())
    # If there are no variables, we just evaluate it with any model
    if len(variables) == 0:
        if evaluate(formula, {"x": False}):
            return True
        else:
            return False

    # Otherwise, we check each model, stopping if we get False.
    models = list(all_models(variables))
    value = True
    for model in models:
        if not evaluate(formula, model):
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

    # formula is a contradiction if and only if ~formula is a tautology.
    return is_tautology(Formula("~", formula))


def is_satisfiable(formula: Formula) -> bool:
    """Checks if the given formula is satisfiable.

    Parameters:
        formula: formula to check.

    Returns:
        ``True`` if the given formula is satisfiable, ``False`` otherwise.
    """
    # Task 2.5c

    # formula is satisfiable if and only if it is not a contradiction.
    return not is_contradiction(formula)


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

    # For each variable in the model, we add it or its negation to a list of formulas.
    formula_list = []
    for variable in model:
        if model[variable]:
            formula_list.append(Formula(variable))
        else:
            formula_list.append(Formula("~", Formula(variable)))

    # Once we have done this, we just need to conjoin all of the formulas together.
    if len(formula_list) == 1:
        return formula_list[0]
    formula = Formula("&", formula_list.pop(), formula_list.pop())
    while len(formula_list) > 0:
        temp_formula = formula
        formula = Formula("&", temp_formula, formula_list.pop())
    return formula


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

    # Since _synthesize_for_model gives us a formula that holds only in one model, and
    # since we want a formula that holds in only the models determined by "values", we:
    #   (i) go through each model whose value is True and use _synthesize_for_model to
    #       get a formula that is true in that model and that model only,
    #   (ii) build the disjunction of all of the formulas achieved in (i).

    # (i) Get a formula for each model whose value is True.
    models = list(all_models(variables))
    formula_list = []
    for i in range(len(values)):
        if values[i]:
            formula_list.append(_synthesize_for_model(models[i]))

    # (ii) Form the disjunction of all of the formulas achieved in (i).
    if len(formula_list) == 0:
        # If values is always False, we return a contradiction.
        return Formula("&", Formula(variables[0]), Formula("~", Formula(variables[0])))
    elif len(formula_list) == 1:
        return formula_list[0]

    formula = Formula("|", formula_list.pop(), formula_list.pop())
    while len(formula_list) != 0:
        temp_formula = formula
        formula = Formula("|", temp_formula, formula_list.pop())
    return formula


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

    # For each variable in the model, we add it or its negation to a list of formulas.
    formula_list = []
    for variable in model:
        if model[variable]:
            formula_list.append(Formula("~", Formula(variable)))
        else:
            formula_list.append(Formula(variable))
    
    # "or" all of the formulas together.
    if len(formula_list) == 1:
        return formula_list[0]
    formula = Formula("|", formula_list.pop(), formula_list.pop())
    while len(formula_list) > 0:
        temp_formula = formula
        formula = Formula("|", temp_formula, formula_list.pop())
    return formula


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

    # (i) Get a formula for each model whose value is False
    models = list(all_models(variables))
    formula_list = []
    for i in range(len(values)):
        if not values[i]:
            formula_list.append(_synthesize_for_all_except_model(models[i]))
    
    # (ii) Form the conjunction of all of the formulas achieved in (i)
    if len(formula_list) == 0:
        # If values is always True, we return a tautology.
        return Formula("|", Formula(variables[0]), Formula("~", Formula(variables[0])))
    elif len(formula_list) == 1:
        return formula_list[0]
    formula = Formula("&", formula_list.pop(), formula_list.pop())
    while len(formula_list) != 0:
        temp_formula = formula
        formula = Formula("&", temp_formula, formula_list.pop())
    return formula


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
    assumptionsHold = True
    for assumption in rule.assumptions:
        if evaluate(assumption, model) == False:
            assumptionsHold = False
            break
    return not assumptionsHold or evaluate(rule.conclusion, model)


def is_sound_inference(rule: InferenceRule) -> bool:
    """Checks if the given inference rule is sound, i.e., whether its
    conclusion is a semantically correct implication of its assumptions.

    Parameters:
        rule: inference rule to check.

    Returns:
        ``True`` if the given inference rule is sound, ``False`` otherwise.
    """
    # Task 4.3
    models = list(all_models(list(rule.variables())))
    for model in models:
        if not evaluate_inference(rule, model):
            return False
    return True
