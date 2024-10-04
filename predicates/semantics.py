# This file is part of the materials accompanying the book
# "Mathematical Logic through Python" by Gonczarowski and Nisan,
# Cambridge University Press. Book site: www.LogicThruPython.org
# (c) Yannai A. Gonczarowski and Noam Nisan, 2017-2022
# File name: predicates/semantics.py

"""Semantic analysis of predicate-logic expressions."""

from typing import AbstractSet, FrozenSet, Generic, Mapping, Tuple, TypeVar

from logic_utils import frozen, frozendict

from predicates.syntax import *

#: A generic type for a universe element in a model.
T = TypeVar("T")


@frozen
class Model(Generic[T]):
    """An immutable model for predicate-logic constructs.

    Attributes:
        universe (`~typing.FrozenSet`\\[`T`]): the set of elements to which
            terms can be evaluated and over which quantifications are defined.
        constant_interpretations (`~typing.Mapping`\\[`str`, `T`]): mapping from
            each constant name to the universe element to which it evaluates.
        relation_arities (`~typing.Mapping`\\[`str`, `int`]): mapping from
            each relation name to its arity, or to ``-1`` if the relation is the
            empty relation.
        relation_interpretations (`~typing.Mapping`\\[`str`, `~typing.AbstractSet`\\[`~typing.Tuple`\\[`T`, ...]]]):
            mapping from each n-ary relation name to argument n-tuples (of
            universe elements) for which the relation is true.
        function_arities (`~typing.Mapping`\\[`str`, `int`]): mapping from
            each function name to its arity.
        function_interpretations (`~typing.Mapping`\\[`str`, `~typing.Mapping`\\[`~typing.Tuple`\\[`T`, ...], `T`]]):
            mapping from each n-ary function name to the mapping from each
            argument n-tuple (of universe elements) to the universe element that
            the function outputs given these arguments.
    """

    universe: FrozenSet[T]
    constant_interpretations: Mapping[str, T]
    relation_arities: Mapping[str, int]
    relation_interpretations: Mapping[str, AbstractSet[Tuple[T, ...]]]
    function_arities: Mapping[str, int]
    function_interpretations: Mapping[str, Mapping[Tuple[T, ...], T]]

    def __init__(
        self,
        universe: AbstractSet[T],
        constant_interpretations: Mapping[str, T],
        relation_interpretations: Mapping[str, AbstractSet[Tuple[T, ...]]],
        function_interpretations: Mapping[
            str, Mapping[Tuple[T, ...], T]
        ] = frozendict(),
    ):
        """Initializes a `Model` from its universe and constant, relation, and
        function name interpretations.

        Parameters:
            universe: the set of elements to which terms are to be evaluated
                and over which quantifications are to be defined.
            constant_interpretations: mapping from each constant name to a
                universe element to which it is to be evaluated.
            relation_interpretations: mapping from each relation name that is to
                be the name of an n-ary relation, to the argument n-tuples (of
                universe elements) for which the relation is to be true.
            function_interpretations: mapping from each function name that is to
                be the name of an n-ary function, to a mapping from each
                argument n-tuple (of universe elements) to a universe element
                that the function is to output given these arguments.
        """
        for constant in constant_interpretations:
            assert is_constant(constant)
            assert constant_interpretations[constant] in universe
        relation_arities = {}
        for relation in relation_interpretations:
            assert is_relation(relation)
            relation_interpretation = relation_interpretations[relation]
            if len(relation_interpretation) == 0:
                arity = -1  # any
            else:
                some_arguments = next(iter(relation_interpretation))
                arity = len(some_arguments)
                for arguments in relation_interpretation:
                    assert len(arguments) == arity
                    for argument in arguments:
                        assert argument in universe
            relation_arities[relation] = arity
        function_arities = {}
        for function in function_interpretations:
            assert is_function(function)
            function_interpretation = function_interpretations[function]
            assert len(function_interpretation) > 0
            some_argument = next(iter(function_interpretation))
            arity = len(some_argument)
            assert arity > 0
            assert len(function_interpretation) == len(universe) ** arity
            for arguments in function_interpretation:
                assert len(arguments) == arity
                for argument in arguments:
                    assert argument in universe
                assert function_interpretation[arguments] in universe
            function_arities[function] = arity

        self.universe = frozenset(universe)
        self.constant_interpretations = frozendict(constant_interpretations)
        self.relation_arities = frozendict(relation_arities)
        self.relation_interpretations = frozendict(
            {
                relation: frozenset(relation_interpretations[relation])
                for relation in relation_interpretations
            }
        )
        self.function_arities = frozendict(function_arities)
        self.function_interpretations = frozendict(
            {
                function: frozendict(function_interpretations[function])
                for function in function_interpretations
            }
        )

    def __repr__(self) -> str:
        """Computes a string representation of the current model.

        Returns:
            A string representation of the current model.
        """
        return (
            "Universe="
            + str(self.universe)
            + "; Constant Interpretations="
            + str(self.constant_interpretations)
            + "; Relation Interpretations="
            + str(self.relation_interpretations)
            + (
                "; Function Interpretations=" + str(self.function_interpretations)
                if len(self.function_interpretations) > 0
                else ""
            )
        )

    def evaluate_term(
        self, term: Term, assignment: Mapping[str, T] = frozendict()
    ) -> T:
        """Calculates the value of the given term in the current model under the
        given assignment of values to variable names.

        Parameters:
            term: term to calculate the value of, for the constant and function
                names of which the current model has interpretations.
            assignment: mapping from each variable name in the given term to a
                universe element to which it is to be evaluated.

        Returns:
            The value (in the universe of the current model) of the given
            term in the current model under the given assignment of values to
            variable names.
        """
        assert term.constants().issubset(self.constant_interpretations.keys())
        assert term.variables().issubset(assignment.keys())
        for function, arity in term.functions():
            assert (
                function in self.function_interpretations
                and self.function_arities[function] == arity
            )
        # Task 7.7

        # Values of constants and variables are given by the model or assignment
        # respectively.
        if is_constant(term.root):
            return self.constant_interpretations[term.root]
        elif is_variable(term.root):
            return assignment[term.root]

        # Values of functions rely on the values of their arguments and the model's
        # interpretation.
        function_interpretation = self.function_interpretations[term.root]
        argument_values = []
        for arg in term.arguments:
            argument_values.append(self.evaluate_term(arg, assignment))
        return function_interpretation[tuple(argument_values)]

    def evaluate_formula(
        self, formula: Formula, assignment: Mapping[str, T] = frozendict()
    ) -> bool:
        """Calculates the truth value of the given formula in the current model
        under the given assignment of values to free occurrences of variable
        names.

        Parameters:
            formula: formula to calculate the truth value of, for the constant,
                function, and relation names of which the current model has
                interpretations.
            assignment: mapping from each variable name that has a free
                occurrence in the given formula to a universe element to which
                it is to be evaluated.

        Returns:
            The truth value of the given formula in the current model under the
            given assignment of values to free occurrences of variable names.
        """
        assert formula.constants().issubset(self.constant_interpretations.keys())
        assert formula.free_variables().issubset(assignment.keys())
        for function, arity in formula.functions():
            assert (
                function in self.function_interpretations
                and self.function_arities[function] == arity
            )
        for relation, arity in formula.relations():
            assert relation in self.relation_interpretations and self.relation_arities[
                relation
            ] in {-1, arity}
        # Task 7.8

        # Evaluating the formula is different depending on its root. There are two base
        # cases, with the rest being recursive:
        #   (1) Equality. Then we use evaluate_term on the arguments and check if they're
        #       equal.
        #   (2) Relation. Then we use evaluate_term on the arguments and check if the
        #       tuple formed by them is in the relation interpretation.
        #   (3) Unary/binary operator. Then we recursively evaluate the operands and
        #       combine them in the obvious way.
        #   (4) Quantifier. Then we recursively evaluate formula.statement for
        #       each possible assignment to the quantified variable. If the quantifier is
        #       "E", we return True if formula.statement is ever True (and False
        #       otherwise). If the quantifier is "A", we return True if formula.statement
        #       is always true (and False otherwise).

        # (1) Equality
        if is_equality(formula.root):
            return self.evaluate_term(
                formula.arguments[0], assignment
            ) == self.evaluate_term(formula.arguments[1], assignment)

        # (2) Relation
        elif is_relation(formula.root):
            relation_interpretation = self.relation_interpretations[formula.root]
            argument_values = []
            for arg in formula.arguments:
                argument_values.append(self.evaluate_term(arg, assignment))
            return tuple(argument_values) in relation_interpretation

        # (3) Operator
        elif formula.root == "~":
            return not self.evaluate_formula(formula.first, assignment)
        elif formula.root == "|":
            return self.evaluate_formula(
                formula.first, assignment
            ) or self.evaluate_formula(formula.second, assignment)
        elif formula.root == "&":
            return self.evaluate_formula(
                formula.first, assignment
            ) and self.evaluate_formula(formula.second, assignment)
        elif formula.root == "->":
            return (
                not self.evaluate_formula(formula.first, assignment)
            ) or self.evaluate_formula(formula.second, assignment)

        # (4) Quantifier
        elif formula.root == "A":
            for variable_interpretation in self.universe:
                new_assignment = dict(assignment)
                new_assignment[formula.variable] = variable_interpretation
                if not self.evaluate_formula(formula.statement, new_assignment):
                    return False
            return True
        elif formula.root == "E":
            for variable_interpretation in self.universe:
                new_assignment = dict(assignment)
                new_assignment[formula.variable] = variable_interpretation
                if self.evaluate_formula(formula.statement, new_assignment):
                    return True
            return False

    def is_model_of(self, formulas: AbstractSet[Formula]) -> bool:
        """Checks if the current model is a model of the given formulas.

        Parameters:
            formulas: formulas to check, for the constant, function, and
                relation names of which the current model has interpretations.

        Returns:
            ``True`` if each of the given formulas evaluates to true in the
            current model under any assignment of elements from the universe of
            the current model to the free occurrences of variable names in that
            formula, ``False`` otherwise.
        """
        for formula in formulas:
            assert formula.constants().issubset(self.constant_interpretations.keys())
            for function, arity in formula.functions():
                assert (
                    function in self.function_interpretations
                    and self.function_arities[function] == arity
                )
            for relation, arity in formula.relations():
                assert (
                    relation in self.relation_interpretations
                    and self.relation_arities[relation] in {-1, arity}
                )
        # Task 7.9

        # evaluate_formula does all of the work for evaluating the formulas so long as
        # we have an assignment to the free variables of the formulas. So, we
        #   (1) Find all of the free variables in the formulas. If there are none, we
        #       evaluate the formulas and return True if all of them are True (and False
        #       otherwise).
        #   (2) If we have n free variables, then we need to construct every n-tuple
        #       containing elements of our universe, Omega. I call an n-tuple a "combo,"
        #       and the set of all such n-tuples is Omega^n.
        #   (3) Match each free variable with an element of the n-tuples to get all
        #       possible assignments of the free variables to an element of the universe.
        #       Evaluate the formulas for each assignment, and return True if all
        #       formulas are true for all assignments (and False otherwise).

        # (1) Find all of the free variables in the formulas.
        free_variables = set()
        for formula in formulas:
            free_variables.update(formula.free_variables())
        free_variables = list(free_variables)

        if len(free_variables) == 0:
            for formula in formulas:
                if not self.evaluate_formula(formula):
                    return False
            return True

        # (2) Construct Omega^n, where n is the number of free variables.
        def combinations(n, Omega) -> list[list[str]]:
            """Constructs Omega^n, where Omega is the universe and n is any integer.

            Parameters:
                n: dimension to build to
                Omega: universe

            Returns:
                Omega^n, that is, a list of every n-tuple consisting of elements of
                Omega. Instead of using tuples, though, it uses lists.
            """
            # Base cases: n <= 1
            if n < 1:
                return []
            list_omega = [[element] for element in list(Omega)]
            if n == 1:
                return list_omega
            
            # Recursive case: n > 1.
            Omega_n = []
            Omega_n_minus_1 = combinations(n - 1, Omega)
            for combo in Omega_n_minus_1:
                for element in Omega:
                    temp_combo = combo.copy()
                    temp_combo.append(element)
                    Omega_n.append(temp_combo)
            return Omega_n

        Omega_n = combinations(len(free_variables), self.universe)

        # (3) Get every possible assignment of the free variables, and evaluate all
        # formulas for all assignments.
        for combo in Omega_n:
            assignment = dict()
            for i in range(len(free_variables)):
                variable = free_variables[i]
                interpretation = combo[i]
                assignment[variable] = interpretation
            for formula in formulas:
                if not self.evaluate_formula(formula, frozendict(assignment)):
                    return False
        return True
