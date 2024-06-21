# This file is part of the materials accompanying the book
# "Mathematical Logic through Python" by Gonczarowski and Nisan,
# Cambridge University Press. Book site: www.LogicThruPython.org
# (c) Yannai A. Gonczarowski and Noam Nisan, 2017-2022
# File name: predicates/functions.py

"""Syntactic conversion of predicate-logic formulas to not use functions and
equality."""

from typing import AbstractSet, List, Set

from logic_utils import fresh_variable_name_generator, is_z_and_number

from predicates.syntax import *
from predicates.semantics import *

def function_name_to_relation_name(function: str) -> str:
    """Converts the given function name to a canonically corresponding relation
    name.

    Parameters:
        function: function name to convert.

    Returns:
        A relation name that is the same as the given function name, except that
        its first letter is capitalized.
    """
    assert is_function(function)
    return function[0].upper() + function[1:]

def relation_name_to_function_name(relation: str) -> str:
    """Converts the given relation name to a canonically corresponding function
    name.

    Parameters:
        relation: relation name to convert.

    Returns:
        A function name `function` such that
        `function_name_to_relation_name`\ ``(``\ `function`\ ``)`` is the given
        relation name.
    """
    assert is_relation(relation)
    return relation[0].lower() + relation[1:]

def replace_functions_with_relations_in_model(model: Model[T]) -> Model[T]:
    """Converts the given model to a canonically corresponding model without any
    function interpretations, replacing each function interpretation with a
    canonically corresponding relation interpretation.

    Parameters:
        model: model to convert, such that there exist no canonically
            corresponding function name and relation name that both have
            interpretations in this model.

    Returns:
        A model obtained from the given model by replacing every function
        interpretation of a function name with a relation interpretation of the
        canonically corresponding relation name, such that the relation
        interpretation contains any tuple
        ``(``\ `x1`\ ``,``...\ ``,``\ `xn`\ ``)``  if and only if `x1` is the
        output of the function interpretation for the arguments
        ``(``\ `x2`\ ``,``...\ ``,``\ `xn`\ ``)``.
    """
    for function in model.function_interpretations:
        assert function_name_to_relation_name(function) not in \
               model.relation_interpretations
    # Task 8.1

    # Unpack everything in the model.
    universe = model.universe
    constant_interpretations = model.constant_interpretations
    relation_interpretations = dict(model.relation_interpretations)
    function_interpretations = model.function_interpretations

    # Go through each function, one at a time
    for function_name in function_interpretations:
        # Find its interpretation. The interpretation will be a Mapping (dict)
        # from Omega^(arity) to Omega. We turn this into a relation with arity
        # Omega^(arity + 1). We do this by taking each input for the function
        # (given as the keys of the dict) and putting its arguments into a tuple with 
        # the output (given as the value of the dict) in front.
        function_interpretation = function_interpretations[function_name] # Mapping from Omega^(arity) to Omega
        # Initialize a set for our relation and find its new name.
        relation_interpretation = set()
        relation_name = function_name_to_relation_name(function_name)
        # Now we go through each possible input for the function
        for input_arguments in function_interpretation.keys():
            # We put all of the input arguments into a list
            new_relation = [arg for arg in input_arguments]
            # And insert the output (value of the Mapping) in position 0.
            new_relation.insert(0, function_interpretation[input_arguments])
            # Then cast to a tuple and add it as a new relation interpretation.
            relation_interpretation.add(tuple(new_relation))
        relation_interpretations[relation_name] = relation_interpretation
    # Once we're done with each of the functions, we return a new Model.
    empty_mapping = dict()
    return Model(universe, constant_interpretations, relation_interpretations, empty_mapping)

def replace_relations_with_functions_in_model(model: Model[T],
                                              original_functions:
                                              AbstractSet[str]) -> \
        Union[Model[T], None]:
    """Converts the given model with no function interpretations to a
    canonically corresponding model with interpretations for the given function
    names, having each new function interpretation replace a canonically
    corresponding relation interpretation.

    Parameters:
        model: model to convert, that contains no function interpretations.
        original_functions: function names for the model to convert to,
            such that no relation name that canonically corresponds to any of
            these function names has an interpretation in the given model.

    Returns:
        A model `model` with the given function names such that
        `replace_functions_with_relations_in_model`\ ``(``\ `model`\ ``)``
        is the given model, or ``None`` if no such model exists.
    """
    assert len(model.function_interpretations) == 0
    for function in original_functions:
        assert is_function(function)
        assert function not in model.function_interpretations
        assert function_name_to_relation_name(function) in \
               model.relation_interpretations
    # Task 8.2

    # Unpack the model.
    universe = list(model.universe)
    constant_interpretations = model.constant_interpretations
    function_interpretations = dict()
    relation_interpretations = dict(model.relation_interpretations)
    relation_arities = model.relation_arities

    # We loop through every function which we are trying to construct.
    for function_name in original_functions:
        # Find its corresponding relation and the info about it.
        relation_name = function_name_to_relation_name(function_name)
        relation_interpretation = relation_interpretations[relation_name]
        relation_arity = relation_arities[relation_name]

        # We try to interpret the relation as a function from Omega^(arity-1) to Omega.
        # This is possible if and only if every element of Omega^(arity-1) appears exactly
        # once at the end of a tuple in the relation. This occurs if and only if:
        #   (a) There are as many tuples in the relation as there are elements of Omega^(arity-1),
        #   (b) No element of Omega^(arity-1) appears more than once at the end of a tuple.

        # Check condition (a)
        omega_size = len(universe)
        if len(list(relation_interpretation)) != omega_size**(relation_arity-1):
            return None
        
        # If condition (a) holds, then we can go ahead and look through the actual related tuples.
        function_interpretation = dict()
        for tuple_relation in relation_interpretation:
            relation = list(tuple_relation)
            args = tuple(relation[1:])

            # Check condition (b) for each element of Omega^(arity-1)
            if args in function_interpretation.keys():
                return None
            
            # If both hold, then we build the function.
            value = relation[0]
            function_interpretation[args] = value

        # Add the function to the interpretations and remove it as a relation interpretation
        function_interpretations[function_name] = function_interpretation
        relation_interpretations.pop(relation_name)
    return Model(universe, constant_interpretations, relation_interpretations, function_interpretations)
    
    


def _compile_term(term: Term) -> List[Formula]:
    """Syntactically compiles the given term into a list of single-function
    invocation steps.

    Parameters:
        term: term to compile, whose root is a function invocation, and which
            contains no variable names that are ``z`` followed by a number.

    Returns:
        A list of steps, each of which is a formula of the form
        ``'``\ `y`\ ``=``\ `f`\ ``(``\ `x1`\ ``,``...\ ``,``\ `xn`\ ``)'``,
        where `y` is a new variable name obtained by calling
        `next`\ ``(``\ `~logic_utils.fresh_variable_name_generator`\ ``)``, `f`
        is a function name, and each of the `x`\ `i` is either a constant name
        or a variable name. If `x`\ `i` is a new variable name, then it is also
        the left-hand side of a previous step, where all of the steps "leading
        up to" `x1` precede those "leading up" to `x2`, etc. If all the returned
        steps hold in any model, then the left-hand-side variable name of the
        last returned step evaluates in that model to the value of the given
        term.
    """
    assert is_function(term.root)
    for variable in term.variables():
        assert not is_z_and_number(variable)
    # Task 8.3

    steps = []
    # We'll use recursion to handle nested function calls. We start by finding
    # which arguments are themselves function calls.
    arguments = list(term.arguments)
    indices_of_arguments_which_are_functions = []
    for i in range(len(arguments)):
        if is_function(arguments[i].root):
            indices_of_arguments_which_are_functions.append(i)

    # If our function's arguments contain no functions, then
    # we can just return it as a step. This is our base case.
    if len(indices_of_arguments_which_are_functions) == 0:
        steps.append(Formula("=", [Term(next(fresh_variable_name_generator)), term]))
        return steps
    
    # Otherwise, we recurse to find the steps of each of the function arguments,
    # in order. We need to keep track of what variables we call each of the
    # arguments under the new naming, though.
    for i in indices_of_arguments_which_are_functions:
        arg_steps = _compile_term(arguments[i])
        steps.extend(arg_steps)
        # We give this argument a new variable name, which we find as it
        # is the left hand side of the equality in the last step.
        arguments[i] = arg_steps[-1].arguments[0]
    
    # Add our final step, which is an equality for our entire term, using the new
    # argument names.
    steps.append(Formula("=", [Term(next(fresh_variable_name_generator)), Term(term.root, arguments)]))
    return steps
    

def replace_functions_with_relations_in_formula(formula: Formula) -> Formula:
    """Syntactically converts the given formula to a formula that does not
    contain any function invocations, and is "one-way equivalent" in the sense
    that the former holds in a model if and only if the latter holds in the
    canonically corresponding model with no function interpretations.

    Parameters:
        formula: formula to convert, which contains no variable names that are
            ``z`` followed by a number, and such that there exist no canonically
            corresponding function name and relation name that are both invoked
            in this formula.

    Returns:
        A formula such that the given formula holds in any model `model` if and
        only if the returned formula holds in
        `replace_function_with_relations_in_model`\ ``(``\ `model`\ ``)``.
    """
    assert len({function_name_to_relation_name(function) for
                function,arity in formula.functions()}.intersection(
                    {relation for relation,arity in formula.relations()})) == 0
    for variable in formula.variables():
        assert not is_z_and_number(variable)
    # Task 8.4

def replace_functions_with_relations_in_formulas(formulas:
                                                 AbstractSet[Formula]) -> \
        Set[Formula]:
    """Syntactically converts the given set of formulas to a set of formulas
    that do not contain any function invocations, and is "two-way
    equivalent" in the sense that:

    1. The former holds in a model if and only if the latter holds in the
       canonically corresponding model with no function interpretations.
    2. The latter holds in a model if and only if that model has a
       canonically corresponding model with interpretations for the functions
       names of the former, and the former holds in that model.

    Parameters:
        formulas: formulas to convert, which contain no variable names that are
            ``z`` followed by a number, and such that there exist no canonically
            corresponding function name and relation name that are both invoked
            in these formulas.

    Returns:
        A set of formulas, one for each given formula as well as one additional
        formula for each relation name that replaces a function name from the
        given formulas, such that:

        1. The given formulas hold in a model `model` if and only if the
           returned formulas hold in
           `replace_functions_with_relations_in_model`\ ``(``\ `model`\ ``)``.
        2. The returned formulas hold in a model `model` if and only if
           `replace_relations_with_functions_in_model`\ ``(``\ `model`\ ``,``\ `original_functions`\ ``)``,
           where `original_functions` are all the function names in the given
           formulas, is a model and the given formulas hold in it.
    """
    assert len(set.union(*[{function_name_to_relation_name(function) for
                            function,arity in formula.functions()}
                           for formula in formulas]).intersection(
                               set.union(*[{relation for relation,arity in
                                            formula.relations()} for
                                           formula in formulas]))) == 0
    for formula in formulas:
        for variable in formula.variables():
            assert not is_z_and_number(variable)
    # Task 8.5
        
def replace_equality_with_SAME_in_formulas(formulas: AbstractSet[Formula]) -> \
        Set[Formula]:
    """Syntactically converts the given set of formulas to a canonically
    corresponding set of formulas that do not contain any equalities, consisting
    of the following formulas:

    1. A formula for each of the given formulas, where each equality is
       replaced with a matching invocation of the relation name ``'SAME'``.
    2. Formula(s) that ensure that in any model of the returned formulas, the
       interpretation of the relation name ``'SAME'`` is reflexive,
       symmetric, and transitive.
    3. For each relation name from the given formulas, formula(s) that ensure
       that in any model of the returned formulas, the interpretation of this
       relation name respects the interpretation of the relation name
       ``'SAME'``.

    Parameters:
        formulas: formulas to convert, that contain no function names and do not
            contain the relation name ``'SAME'``.

    Returns:
        The converted set of formulas.
    """
    for formula in formulas:
        assert len(formula.functions()) == 0
        assert 'SAME' not in \
               {relation for relation,arity in formula.relations()}
    # Task 8.6
        
def add_SAME_as_equality_in_model(model: Model[T]) -> Model[T]:
    """Adds an interpretation of the relation name ``'SAME'`` in the given
    model, that canonically corresponds to equality in the given model.

    Parameters:
        model: model that has no interpretation of the relation name
            ``'SAME'``, to add the interpretation to.

    Returns:
        A model obtained from the given model by adding an interpretation of the
        relation name ``'SAME'``, that contains precisely all pairs
        ``(``\ `x`\ ``,``\ `x`\ ``)`` for every element `x` of the universe of
        the given model.
    """
    assert 'SAME' not in model.relation_interpretations
    # Task 8.7
    
def make_equality_as_SAME_in_model(model: Model[T]) -> Model[T]:
    """Converts the given model to a model where equality coincides with the
    interpretation of ``'SAME'`` in the given model, in the sense that any set
    of formulas holds in the returned model if and only if its canonically
    corresponding set of formulas that do not contain equality holds in the
    given model.

    Parameters:
        model: model to convert, that contains no function interpretations, and
            contains an interpretation of the relation name ``'SAME'`` that is
            reflexive, symmetric, transitive, and respected by the
            interpretations of all other relation names.

    Returns:
        A model that is a model of any set `formulas` if and only if the given
        model is a model of
        `replace_equality_with_SAME`\ ``(``\ `formulas`\ ``)``. The universe of
        the returned model corresponds to the equivalence classes of the
        interpretation of ``'SAME'`` in the given model.
    """
    assert 'SAME' in model.relation_interpretations and \
           model.relation_arities['SAME'] == 2
    assert len(model.function_interpretations) == 0
    # Task 8.8
