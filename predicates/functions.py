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
    if is_equality(formula.root) or is_relation(formula.root):
        # First, compile all terms of the relation
        arguments = list(formula.arguments)
        new_arguments = list(formula.arguments)
        argument_steps = []
        for i in range(len(arguments)):
            if is_function(arguments[i].root):
                arg_steps = _compile_term(arguments[i])
                argument_steps.extend(arg_steps)
                new_arguments[i] = arg_steps[-1].arguments[0]
        # If no terms needed compiling, then our relation is good as it is.
        if len(argument_steps) == 0:
            return formula
        else:
            """ 
            Otherwise, we need to create a new formula that involves all of the compilation done for the
            needed terms. Because of the tree-like structure of the Formula class, it is easiest to do
            this "inside out" or "backwards": given an original formula of R(f(g(x)), h(2, y), 3), we have 
            argument_steps = [z1 = g(x), z2 = f(z1), z3 = h(2, y)]. Then our relation becomes R(z2, z3, 3).
            We take this relation as our initial subformula and loop *backwards* through each step in
            argument_steps, adding on its contribution: R(z2, z3, 3) -> H(z3, 2, y) & R(z2, z3, 3)
            -> Ez3[(H(z3, 2, y) & R(z2, z3, 3))] -> (F(z2, z1) & Ez3[(H(z3, 2, y) & R(z2, z3, 3))])
            -> Ez2[(F(z2, z1) & Ez3[(H(z3, 2, y) & R(z2, z3, 3))])] and so on. We do this by keeping track
            of each intermediate step as the "subformula," building on it in each iteration of the loop. 
            """
            subformula = Formula(formula.root, new_arguments) # Start with just the relation, e.g. R(z2, z3, 3).
            for step in reversed(argument_steps): # Loop through the steps backwards.
                # Each step is a Formula object like z5 = f(z4, 0), which has root "=" and arguments
                # [z5, f(z4, 0)]. We turn this into F(z5, z4, 0).
                relation_name = function_name_to_relation_name(step.arguments[1].root) # This yields F
                next_variable = step.arguments[0] # This yields z5
                relation_arguments = list(step.arguments[1].arguments) # List containing the arguments of f: [z4, 0]
                relation_arguments.insert(0, next_variable) # Insert z5 into beginning of list: [z5, z4, 0]
                relation = Formula(relation_name, relation_arguments) # Build the relation: F(z4, z4, 0)
                subformula = Formula('&', relation, subformula) # Add on the previous subformula
                subformula = Formula('E', next_variable.root, subformula) # Quantify over the next variable name.
            return subformula
    # If our formula is anythong other than a relation invocation (or equality), we just recurse.
    elif is_unary(formula.root):
        return Formula(formula.root, replace_functions_with_relations_in_formula(formula.first))
    elif is_binary(formula.root):
        return Formula(formula.root, replace_functions_with_relations_in_formula(formula.first), 
                       replace_functions_with_relations_in_formula(formula.second))
    elif is_quantifier(formula.root):
        return Formula(formula.root, formula.variable, replace_functions_with_relations_in_formula(formula.statement))

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

    return_set = set()
    for formula in formulas:
        # Add the function-free analog
        return_set.add(replace_functions_with_relations_in_formula(formula))
        functions_and_arities = [[function, arity] for function, arity in list(formula.functions())]
        # Now we loop through each function in the original formula.
        for i in range(len(functions_and_arities)):
            function_name = functions_and_arities[i][0]
            arity = functions_and_arities[i][1]
            relation_name = function_name_to_relation_name(function_name)

            #  --- Building the existence statement ---
            # We need arity + 1 variables, and their Term versions.
            variable_list = [next(fresh_variable_name_generator) for j in range(arity + 1)]
            term_list = [Term(var) for var in variable_list]

            # Start with, e.g., Ez[F(z,x)]
            existence_subformula = Formula('E', variable_list[0], Formula(relation_name, term_list))
            # Then universally quantify over all of the other variables, e.g., Ax[Ez[F(z, x)]]
            for j in range(arity): 
                existence_subformula = Formula('A', variable_list[j+1], existence_subformula)

            # --- Building the uniqueness statement ---
            # We need two sets of relation arguments, where the only difference is the first one
            # (the function's output).
            second_variable_list = variable_list
            second_variable_list.pop(0)
            second_variable_list.insert(0, next(fresh_variable_name_generator))
            second_term_list = [Term(var) for var in second_variable_list]

            # Start with, e.g., F(z1, x) & F(z2, x)
            uniqueness_subformula = Formula('&', Formula(relation_name, term_list), Formula(relation_name, second_term_list))
            # which becomes (F(z1, x) & F(z2, x) -> z1 = z2)
            uniqueness_subformula = Formula('->', uniqueness_subformula, Formula('=', [term_list[0], second_term_list[0]]))
            # then we universally quantify over all variables.
            uniqueness_subformula = Formula('A', second_variable_list[0], uniqueness_subformula)
            for j in range(arity + 1):
                uniqueness_subformula = Formula('A', variable_list[j], uniqueness_subformula)

            # Conjoin the existence and uniqueness statements, and add the conjunction to the set.
            return_set.add(Formula('&', existence_subformula, uniqueness_subformula))
    return return_set
        
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

    # First we see how to do it in a single formula.
    def replace_equality_with_SAME_in_formula(formula: Formula) -> Formula:
        if formula.root == '=':
            return Formula('SAME', formula.arguments)
        elif is_unary(formula.root):
            return Formula(formula.root, replace_equality_with_SAME_in_formula(formula.first))
        elif is_binary(formula.root):
            return Formula(formula.root, replace_equality_with_SAME_in_formula(formula.first), \
                           replace_equality_with_SAME_in_formula(formula.second))
        elif is_quantifier(formula.root):
            return Formula(formula.root, formula.variable, replace_equality_with_SAME_in_formula(formula.statement))
        else:
            return formula
    return_set = set()
    for formula in formulas:
        # Add each formula without equality.
        return_set.add(replace_equality_with_SAME_in_formula(formula))
        relations_and_arities = [[relation, arity] for relation, arity in formula.relations()]
        for i in range(len(relations_and_arities)): # Now we add a formula for each relation.
            relation_name = relations_and_arities[i][0]
            arity = relations_and_arities[i][1]
            # We need 2*arity variables. Trying to construct two lists of arity variables did not
            # work, for some reason. So I construct one list of 2*arity variables, and split it
            # in half.
            variable_list = [next(fresh_variable_name_generator) for i in range(2*arity)] 
            second_variable_list = variable_list[arity:]
            variable_list = variable_list[:arity]
            term_list = [Term(var) for var in variable_list]
            second_term_list = [Term(var) for var in second_variable_list]

            # Build, e.g., ((SAME(x1,x2) & SAME(y1, y2)) -> (R(x1, y1) -> R(x2, y2)))
            consequent = Formula('->', Formula(relation_name, term_list), Formula(relation_name, second_term_list))
            antecedent = Formula('SAME', [term_list[0], second_term_list[0]])
            for j in range(len(term_list) - 1):
                antecedent = Formula('&', antecedent, Formula('SAME', [term_list[j+1], second_term_list[j+1]]))
            subformula = Formula('->', antecedent, consequent)

            # Now we universally quantify over all of the variables.
            for j in range(len(variable_list)):
                subformula = Formula('A', variable_list[j], subformula)
                subformula = Formula('A', second_variable_list[j], subformula)
            return_set.add(subformula)
    # Add reflexivity, symmetry, and transitivity, and you're done!
    reflexivity = Formula.parse("Ax[x=x]")
    symmetry = Formula.parse("Ax[Ay[((x=y->y=x)&(y=x->x=y))]]")
    transitivity = Formula.parse("Ax[Ay[Az[((x=y&y=z)->x=z)]]]")
    return_set.add(replace_equality_with_SAME_in_formula(reflexivity))
    return_set.add(replace_equality_with_SAME_in_formula(symmetry))
    return_set.add(replace_equality_with_SAME_in_formula(transitivity))
    return return_set
        
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
    interpretation = []
    for x in model.universe:
        interpretation.append(tuple([x, x]))
    relation_interpretations = dict(model.relation_interpretations)
    relation_interpretations['SAME'] = interpretation
    return Model(model.universe, model.constant_interpretations, relation_interpretations, model.function_interpretations)
    
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
    universe = model.universe
    relation_interpretations = dict(model.relation_interpretations)
    constant_interpretations = dict(model.constant_interpretations)
    same_interpretation = [list(same_pair) for same_pair in relation_interpretations['SAME']]

    # --- Step 1: Updating the Universe ---
    # Construct the equivalence classes defined by 'SAME'
    equivalence_classes = []
    for x in universe:
        x_equivalence_class = []
        for same_pair in same_interpretation:
            if same_pair[0] == x:
                x_equivalence_class.append(same_pair[1])
        equivalence_classes.append(frozenset(x_equivalence_class))

    # Add only a single representative of each equivalence class to the new universe.
    new_universe = set()
    for equivalence_class in list(frozenset(equivalence_classes)):
        list_class = list(equivalence_class)
        new_universe.add(list_class[0])

    # TODO: change the equivalence class structure to a dictionary where each element
    # of the universe is a key and the value is its representative in the equivalence
    # class.

    # --- Step 2: Updating Constants ---
    def find_representative_of_element(element: T) -> T:
        # Takes in an element of the universe and finds its representative in the equivalence classes.
        for equivalence_class in list(frozenset(equivalence_classes)): # Look at each class
                        if element in equivalence_class: # Find the one that the element is in
                            for equivalence_class_element in equivalence_class: # Find the representative
                                if equivalence_class_element in new_universe:
                                    return equivalence_class_element # Return it.
    for constant_name in model.constant_interpretations.keys():
        constant_interpretations[constant_name] = find_representative_of_element(model.constant_interpretations[constant_name])
    
    # --- Step 3: Updating Relations ---
    def update_relation(relation_name: str) -> AbstractSet[Tuple[T]]:
        # Updates a relation so as to only involve elements of the new universe.
        # Consider the old universe {1, 2, 3} where SAME(1, 3) holds. Suppose we chose
        # to keep 1 in our universe but remove 3 (1 is in new_universe, but 3 is not). 
        # If we have a relation S defined by {(1, 3), (2, 3)}, we need to replace 3 in each
        # of the related tuples.
        new_interpretation = set()
        for related_tuple in relation_interpretations[relation_name]: # Look at, e.g., (1, 3)
            related_list = list(related_tuple) # Turn it into a list, e.g., [1, 3]
            for i in range(len(related_list)): # Go through each element.
                element = related_list[i]
                # If it isn't in the new_universe (as is the case for 3), we need to find
                # the representative chosen for the new_universe (in this case, 1), and replace.
                if element not in new_universe:
                    related_list[i] = find_representative_of_element(element)
            new_interpretation.add(tuple(related_list))
            # Once you do that for each related tuple, you're done.
        return new_interpretation
    for relation_name in model.relation_interpretations.keys():
        relation_interpretations[relation_name] = update_relation(relation_name)
    del relation_interpretations['SAME'] # Get rid of 'SAME'

    return Model(new_universe, constant_interpretations, relation_interpretations, model.function_interpretations)