# This file is part of the materials accompanying the book
# "Mathematical Logic through Python" by Gonczarowski and Nisan,
# Cambridge University Press. Book site: www.LogicThruPython.org
# (c) Yannai A. Gonczarowski and Noam Nisan, 2017-2022
# File name: predicates/syntax.py

"""Syntactic handling of predicate-logic expressions."""

from __future__ import annotations
from functools import lru_cache
from typing import AbstractSet, Mapping, Optional, Sequence, Set, Tuple, Union

from logic_utils import (
    fresh_variable_name_generator,
    frozen,
    memoized_parameterless_method,
)

from propositions.syntax import (
    Formula as PropositionalFormula,
    is_variable as is_propositional_variable,
)


class ForbiddenVariableError(Exception):
    """Raised by `Term.substitute` and `Formula.substitute` when a substituted
    term contains a variable name that is forbidden in that context.

    Attributes:
        variable_name (`str`): the variable name that was forbidden in the
            context in which a term containing it was to be substituted.
    """

    variable_name: str

    def __init__(self, variable_name: str):
        """Initializes a `ForbiddenVariableError` from the offending variable
        name.

        Parameters:
            variable_name: variable name that is forbidden in the context in
                which a term containing it is to be substituted.
        """
        assert is_variable(variable_name)
        self.variable_name = variable_name


@lru_cache(maxsize=100)  # Cache the return value of is_constant
def is_constant(string: str) -> bool:
    """Checks if the given string is a constant name.

    Parameters:
        string: string to check.

    Returns:
        ``True`` if the given string is a constant name, ``False`` otherwise.
    """
    return (
        (
            (string[0] >= "0" and string[0] <= "9")
            or (string[0] >= "a" and string[0] <= "e")
        )
        and string.isalnum()
    ) or string == "_"


@lru_cache(maxsize=100)  # Cache the return value of is_variable
def is_variable(string: str) -> bool:
    """Checks if the given string is a variable name.

    Parameters:
        string: string to check.

    Returns:
        ``True`` if the given string is a variable name, ``False`` otherwise.
    """
    return string[0] >= "u" and string[0] <= "z" and string.isalnum()


@lru_cache(maxsize=100)  # Cache the return value of is_function
def is_function(string: str) -> bool:
    """Checks if the given string is a function name.

    Parameters:
        string: string to check.

    Returns:
        ``True`` if the given string is a function name, ``False`` otherwise.
    """
    return string[0] >= "f" and string[0] <= "t" and string.isalnum()


@frozen
class Term:
    """An immutable predicate-logic term in tree representation, composed from
    variable names and constant names, and function names applied to them.

    Attributes:
        root (`str`): the constant name, variable name, or function name at the
            root of the term tree.
        arguments (`~typing.Optional`\\[`~typing.Tuple`\\[`Term`, ...]]): the
            arguments of the root, if the root is a function name.
    """

    root: str
    arguments: Optional[Tuple[Term, ...]]

    def __init__(self, root: str, arguments: Optional[Sequence[Term]] = None):
        """Initializes a `Term` from its root and root arguments.

        Parameters:
            root: the root for the formula tree.
            arguments: the arguments for the root, if the root is a function
                name.
        """
        if is_constant(root) or is_variable(root):
            assert arguments is None
            self.root = root
        else:
            assert is_function(root)
            assert arguments is not None and len(arguments) > 0
            self.root = root
            self.arguments = tuple(arguments)

    @memoized_parameterless_method
    def __repr__(self) -> str:
        """Computes the string representation of the current term.

        Returns:
            The standard string representation of the current term.
        """
        # Task 7.1

        # Base case
        if is_constant(self.root) or is_variable(self.root):
            return self.root

        # Recursive case: term is a function invocation.
        # In this case, we need to include the function name and all of its arguments.
        # We add each argument with a comma, and then replace the final comma with ")".
        string = self.root + "("
        for i in range(len(self.arguments)):
            string += str(self.arguments[i]) + ","
        return string[:-1] + ")"

    def __eq__(self, other: object) -> bool:
        """Compares the current term with the given one.

        Parameters:
            other: object to compare to.

        Returns:
            ``True`` if the given object is a `Term` object that equals the
            current term, ``False`` otherwise.
        """
        return isinstance(other, Term) and str(self) == str(other)

    def __ne__(self, other: object) -> bool:
        """Compares the current term with the given one.

        Parameters:
            other: object to compare to.

        Returns:
            ``True`` if the given object is not a `Term` object or does not
            equal the current term, ``False`` otherwise.
        """
        return not self == other

    def __hash__(self) -> int:
        return hash(str(self))

    @staticmethod
    def _parse_prefix(string: str) -> Tuple[Union[Term, Tuple[Term]], str]:
        """Parses a prefix of the given string into a term.

        Parameters:
            string: string to parse, which has a prefix that is a valid
                representation of a term.

        Returns:
            A pair of the parsed term and the unparsed suffix of the string. If
            the given string has as a prefix a constant name (e.g., ``'c12'``)
            or a variable name (e.g., ``'x12'``), then the parsed prefix will be
            that entire name (and not just a part of it, such as ``'x1'``).
        """
        # Task 7.3a

        # In addition to the obvious cases of our string beginning with a constant name,
        # variable name, or function name, we also use this method to parse whole tuples
        # of terms, e.g., "(x19, 0, f(y))." This is so we can avoid duplicating code for
        # parsing formulas. For this reason, note the changed return type.

        # Constants and variables are handled the same as in propositional logic, with a
        # loop to find the entire name instead of just a prefix (e.g., x19 instead of x).
        if is_constant(string[0]) or is_variable(string[0]):
            term = string[0]
            while (len(term) < len(string)) and (
                is_variable(string[: len(term) + 1])
                or is_constant(string[: len(term) + 1])
            ):
                term = string[: len(term) + 1]
            rest = string[len(term) :]
            return (Term(term), rest)

        # We handle function names in pretty much the same way, and then we recursively
        # parse the arguments.
        elif is_function(string[0]):
            root = string[0]
            while len(root) < len(string) and is_function(string[: len(root) + 1]):
                root = string[: len(root) + 1]
            rest = string[len(root) :]
            arguments, rest = Term._parse_prefix(rest)
            return (Term(root, arguments), rest)

        # If the string's prefix is not a constant, variable, or function name, it must
        # be a tuple of terms as called for function or relation invocations.
        arguments = []

        if string[1] == ")":  # Check for nullary invocations
            return (tuple(arguments), string[2:])

        # If not a nullary invocation, we recursively find each argument until we hit ")"
        while len(string) > 0 and string[0] != ")":
            argument, string = Term._parse_prefix(string[1:])
            arguments.append(argument)
        return (tuple(arguments), string[1:])

    @staticmethod
    def parse(string: str) -> Term:
        """Parses the given valid string representation into a term.

        Parameters:
            string: string to parse.

        Returns:
            A term whose standard string representation is the given string.
        """
        # Task 7.3b

        return Term._parse_prefix(string)[0]  # Parse prefix does all the work!

    def constants(self) -> Set[str]:
        """Finds all constant names in the current term.

        Returns:
            A set of all constant names used in the current term.
        """
        # Task 7.5a

        if is_constant(self.root):
            return {self.root}
        elif is_function(self.root):
            constants = set()
            for term in self.arguments:
                constants.update(term.constants())
            return constants
        return set()

    def variables(self) -> Set[str]:
        """Finds all variable names in the current term.

        Returns:
            A set of all variable names used in the current term.
        """
        # Task 7.5b

        if is_variable(self.root):
            return {self.root}
        elif is_function(self.root):
            variables = set()
            for term in self.arguments:
                variables.update(term.variables())
            return variables
        return set()

    def functions(self) -> Set[Tuple[str, int]]:
        """Finds all function names in the current term, along with their
        arities.

        Returns:
            A set of pairs of function name and arity (number of arguments) for
            all function names used in the current term.
        """
        # Task 7.5c

        if is_function(self.root):
            functions = {(self.root, len(self.arguments))}
            for term in self.arguments:
                functions.update(term.functions())
            return functions
        return set()

    def substitute(
        self,
        substitution_map: Mapping[str, Term],
        forbidden_variables: AbstractSet[str] = frozenset(),
    ) -> Term:
        """Substitutes in the current term, each constant name `construct` or
        variable name `construct` that is a key in `substitution_map` with the
        term `substitution_map`\ ``[``\ `construct`\ ``]``.

        Parameters:
            substitution_map: mapping defining the substitutions to be
                performed.
            forbidden_variables: variable names not allowed in substitution
                terms.

        Returns:
            The term resulting from performing all substitutions. Only
            constant name and variable name occurrences originating in the
            current term are substituted (i.e., those originating in one of the
            specified substitutions are not subjected to additional
            substitutions).

        Raises:
            ForbiddenVariableError: If a term that is used in the requested
                substitution contains a variable name from
                `forbidden_variables`.

        Examples:
            >>> Term.parse('f(x,c)').substitute(
            ...     {'c': Term.parse('plus(d,x)'), 'x': Term.parse('c')}, {'y'})
            f(c,plus(d,x))

            >>> Term.parse('f(x,c)').substitute(
            ...     {'c': Term.parse('plus(d,y)')}, {'y'})
            Traceback (most recent call last):
              ...
            predicates.syntax.ForbiddenVariableError: y
        """
        for construct in substitution_map:
            assert is_constant(construct) or is_variable(construct)
        for variable in forbidden_variables:
            assert is_variable(variable)
        # Task 9.1

        def forbidden_variables_in_term(term: Term, forbidden_vars: AbstractSet[str]):
            if is_function(term.root):
                for arg in term.arguments:
                    forbidden_variables_in_term(arg, forbidden_vars)
            else:
                if term.root in forbidden_vars:
                    raise ForbiddenVariableError(term.root)

        # if self.root in substitution_map:
        #     for construct in substitution_map:
        #         forbidden_variables_in_term(substitution_map[construct], forbidden_variables)
        if is_constant(self.root) or is_variable(self.root):
            if self.root not in substitution_map:
                return self
            else:
                forbidden_variables_in_term(
                    substitution_map[self.root], forbidden_variables
                )
                return substitution_map[self.root]
        else:  # Function invocation
            new_args = []
            for arg in self.arguments:
                new_args.append(arg.substitute(substitution_map, forbidden_variables))
            return Term(self.root, new_args)


@lru_cache(maxsize=100)  # Cache the return value of is_equality
def is_equality(string: str) -> bool:
    """Checks if the given string is the equality relation.

    Parameters:
        string: string to check.

    Returns:
        ``True`` if the given string is the equality relation, ``False``
        otherwise.
    """
    return string == "="


@lru_cache(maxsize=100)  # Cache the return value of is_relation
def is_relation(string: str) -> bool:
    """Checks if the given string is a relation name.

    Parameters:
        string: string to check.

    Returns:
        ``True`` if the given string is a relation name, ``False`` otherwise.
    """
    return string[0] >= "F" and string[0] <= "T" and string.isalnum()


@lru_cache(maxsize=100)  # Cache the return value of is_unary
def is_unary(string: str) -> bool:
    """Checks if the given string is a unary operator.

    Parameters:
        string: string to check.

    Returns:
        ``True`` if the given string is a unary operator, ``False`` otherwise.
    """
    return string == "~"


@lru_cache(maxsize=100)  # Cache the return value of is_binary
def is_binary(string: str) -> bool:
    """Checks if the given string is a binary operator.

    Parameters:
        string: string to check.

    Returns:
        ``True`` if the given string is a binary operator, ``False`` otherwise.
    """
    return string == "&" or string == "|" or string == "->"


@lru_cache(maxsize=100)  # Cache the return value of is_quantifier
def is_quantifier(string: str) -> bool:
    """Checks if the given string is a quantifier.

    Parameters:
        string: string to check.

    Returns:
        ``True`` if the given string is a quantifier, ``False`` otherwise.
    """
    return string == "A" or string == "E"


@frozen
class Formula:
    """An immutable predicate-logic formula in tree representation, composed
    from relation names applied to predicate-logic terms, and operators and
    quantifications applied to them.

    Attributes:
        root (`str`): the relation name, equality relation, operator, or
            quantifier at the root of the formula tree.
        arguments (`~typing.Optional`\\[`~typing.Tuple`\\[`Term`, ...]]): the
            arguments of the root, if the root is a relation name or the
            equality relation.
        first (`~typing.Optional`\\[`Formula`]): the first operand of the root,
            if the root is a unary or binary operator.
        second (`~typing.Optional`\\[`Formula`]): the second operand of the
            root, if the root is a binary operator.
        variable (`~typing.Optional`\\[`str`]): the variable name quantified by
            the root, if the root is a quantification.
        statement (`~typing.Optional`\\[`Formula`]): the statement quantified by
            the root, if the root is a quantification.
    """

    root: str
    arguments: Optional[Tuple[Term, ...]]
    first: Optional[Formula]
    second: Optional[Formula]
    variable: Optional[str]
    statement: Optional[Formula]

    def __init__(
        self,
        root: str,
        arguments_or_first_or_variable: Union[Sequence[Term], Formula, str],
        second_or_statement: Optional[Formula] = None,
    ):
        """Initializes a `Formula` from its root and root arguments, root
        operands, or root quantified variable name and statement.

        Parameters:
            root: the root for the formula tree.
            arguments_or_first_or_variable: the arguments for the root, if the
                root is a relation name or the equality relation; the first
                operand for the root, if the root is a unary or binary operator;
                the variable name to be quantified by the root, if the root is a
                quantification.
            second_or_statement: the second operand for the root, if the root is
                a binary operator; the statement to be quantified by the root,
                if the root is a quantification.
        """
        if is_equality(root) or is_relation(root):
            # Populate self.root and self.arguments
            assert isinstance(
                arguments_or_first_or_variable, Sequence
            ) and not isinstance(arguments_or_first_or_variable, str)
            if is_equality(root):
                assert len(arguments_or_first_or_variable) == 2
            assert second_or_statement is None
            self.root, self.arguments = root, tuple(arguments_or_first_or_variable)
        elif is_unary(root):
            # Populate self.first
            assert isinstance(arguments_or_first_or_variable, Formula)
            assert second_or_statement is None
            self.root, self.first = root, arguments_or_first_or_variable
        elif is_binary(root):
            # Populate self.first and self.second
            assert isinstance(arguments_or_first_or_variable, Formula)
            assert second_or_statement is not None
            self.root, self.first, self.second = (
                root,
                arguments_or_first_or_variable,
                second_or_statement,
            )
        else:
            assert is_quantifier(root)
            # Populate self.variable and self.statement
            assert isinstance(arguments_or_first_or_variable, str) and is_variable(
                arguments_or_first_or_variable
            )
            assert second_or_statement is not None
            self.root, self.variable, self.statement = (
                root,
                arguments_or_first_or_variable,
                second_or_statement,
            )

    @memoized_parameterless_method
    def __repr__(self) -> str:
        """Computes the string representation of the current formula.

        Returns:
            The standard string representation of the current formula.
        """
        # Task 7.2

        # Base cases
        if is_equality(self.root):
            left = str(self.arguments[0])
            right = str(self.arguments[1])
            return left + "=" + right
        elif is_relation(self.root):
            if self.arguments == tuple():
                return self.root + "()"
            string = self.root + "("
            for i in range(len(self.arguments)):
                string += str(self.arguments[i]) + ","
            return string[:-1] + ")"

        # Recursive cases
        elif is_unary(self.root):
            return "~" + str(self.first)
        elif is_binary(self.root):
            first = str(self.first)
            second = str(self.second)
            return "(" + first + self.root + second + ")"
        # Quantification
        return self.root + self.variable + "[" + str(self.statement) + "]"

    def __eq__(self, other: object) -> bool:
        """Compares the current formula with the given one.

        Parameters:
            other: object to compare to.

        Returns:
            ``True`` if the given object is a `Formula` object that equals the
            current formula, ``False`` otherwise.
        """
        return isinstance(other, Formula) and str(self) == str(other)

    def __ne__(self, other: object) -> bool:
        """Compares the current formula with the given one.

        Parameters:
            other: object to compare to.

        Returns:
            ``True`` if the given object is not a `Formula` object or does not
            equal the current formula, ``False`` otherwise.
        """
        return not self == other

    def __hash__(self) -> int:
        return hash(str(self))

    @staticmethod
    def _parse_prefix(string: str) -> Tuple[Formula, str]:
        """Parses a prefix of the given string into a formula.

        Parameters:
            string: string to parse, which has a prefix that is a valid
                representation of a formula.

        Returns:
            A pair of the parsed formula and the unparsed suffix of the string.
            If the given string has as a prefix a term followed by an equality
            followed by a constant name (e.g., ``'f(y)=c12'``) or by a variable
            name (e.g., ``'f(y)=x12'``), then the parsed prefix will include
            that entire name (and not just a part of it, such as ``'f(y)=x1'``).
        """
        # Task 7.4a

        # There are 5 different kinds of formula root:
        #   (1) Unary operator. Then we recursively parse the operand.
        #   (2) Binary operator. Then we recursively parse the first operand, find the
        #       operator, and recursively parse the second operand.
        #   (3) Quantifier. Then we use Term._parse_prefix to find the quantified
        #       variable and recursively parse the statement.
        #   (4) Relation name. Then we find the full relation name and get the arguments
        #       from Term._parse_prefix.
        #   (5) Equality. Then we use Term._parse_prefix to find both sides of the
        #       equality.

        # (1) Unary operator
        if is_unary(string[0]):
            subformula, rest = Formula._parse_prefix(string[1:])
            return (Formula(string[0], subformula), rest)

        # (2) Binary operator
        elif string[0] == "(":
            first, rest = Formula._parse_prefix(string[1:])

            if is_binary(rest[0]):
                operator = rest[0]
                rest = rest[1:]
            else:
                operator = rest[0:2]
                rest = rest[2:]

            second, rest = Formula._parse_prefix(rest)
            return (Formula(operator, first, second), rest[1:])

        # (3) Quantifier
        elif is_quantifier(string[0]):
            quantifier = string[0]
            variable, rest = Term._parse_prefix(string[1:])

            rest = rest[1:]  # Remove the "["
            subformula, rest = Formula._parse_prefix(rest)
            # Remove the "]" and return the rest
            return (Formula(quantifier, variable.root, subformula), rest[1:])

        # (4) Relation name
        elif is_relation(string[0]):
            root = string[0]
            for i in range(1, len(string)):
                if is_relation(string[: i + 1]):
                    root = string[: i + 1]
                    continue
                rest = string[len(root) :]
                break
            arguments, rest = Term._parse_prefix(rest)
            return (Formula(root, arguments), rest)

        # (5) Equality
        left, rest = Term._parse_prefix(string)
        right, rest = Term._parse_prefix(rest[1:])  # Remove the "="
        return (Formula("=", (left, right)), rest)

    @staticmethod
    def parse(string: str) -> Formula:
        """Parses the given valid string representation into a formula.

        Parameters:
            string: string to parse.

        Returns:
            A formula whose standard string representation is the given string.
        """
        # Task 7.4b
        return Formula._parse_prefix(string)[0]

    def constants(self) -> Set[str]:
        """Finds all constant names in the current formula.

        Returns:
            A set of all constant names used in the current formula.
        """
        # Task 7.6a

        # Base case
        if is_relation(self.root) or is_equality(self.root):
            constants = set()
            for term in self.arguments:
                constants.update(term.constants())
            return constants

        # Recursive cases
        elif is_unary(self.root):
            return self.first.constants()
        elif is_binary(self.root):
            return self.first.constants().union(self.second.constants())
        return self.statement.constants()  # Quantification

    def variables(self) -> Set[str]:
        """Finds all variable names in the current formula.

        Returns:
            A set of all variable names used in the current formula.
        """
        # Task 7.6b

        # Base case
        if is_relation(self.root) or is_equality(self.root):
            variables = set()
            for term in self.arguments:
                variables.update(term.variables())
            return variables

        # Recursive cases
        elif is_unary(self.root):
            return self.first.variables()
        elif is_binary(self.root):
            return self.first.variables().union(self.second.variables())
        return self.statement.variables().union({self.variable})

    def free_variables(self) -> Set[str]:
        """Finds all variable names that are free in the current formula.

        Returns:
            A set of every variable name that is used in the current formula not
            only within a scope of a quantification on that variable name.
        """
        # Task 7.6c

        # Base case
        if is_relation(self.root) or is_equality(self.root):
            variables = set()
            for term in self.arguments:
                variables.update(term.variables())
            return variables

        # Recursive cases
        elif is_unary(self.root):
            return self.first.free_variables()
        elif is_binary(self.root):
            return self.first.free_variables().union(self.second.free_variables())
        return self.statement.free_variables().difference({self.variable})

    def functions(self) -> Set[Tuple[str, int]]:
        """Finds all function names in the current formula, along with their
        arities.

        Returns:
            A set of pairs of function name and arity (number of arguments) for
            all function names used in the current formula.
        """
        # Task 7.6d

        # Base case
        if is_relation(self.root) or is_equality(self.root):
            functions = set()
            for term in self.arguments:
                functions.update(term.functions())
            return functions

        # Recursive cases
        if is_unary(self.root):
            return self.first.functions()
        elif is_binary(self.root):
            return self.first.functions().union(self.second.functions())
        return self.statement.functions()

    def relations(self) -> Set[Tuple[str, int]]:
        """Finds all relation names in the current formula, along with their
        arities.

        Returns:
            A set of pairs of relation name and arity (number of arguments) for
            all relation names used in the current formula.
        """
        # Task 7.6e

        # Base cases
        if is_relation(self.root):
            return {(self.root, len(self.arguments))}
        elif is_equality(self.root):
            return set()

        # Recursive cases
        if is_unary(self.root):
            return self.first.relations()
        elif is_binary(self.root):
            return self.first.relations().union(self.second.relations())
        return self.statement.relations()

    def substitute(
        self,
        substitution_map: Mapping[str, Term],
        forbidden_variables: AbstractSet[str] = frozenset(),
    ) -> Formula:
        """Substitutes in the current formula, each constant name `construct` or
        free occurrence of variable name `construct` that is a key in
        `substitution_map` with the term
        `substitution_map`\ ``[``\ `construct`\ ``]``.

        Parameters:
            substitution_map: mapping defining the substitutions to be
                performed.
            forbidden_variables: variable names not allowed in substitution
                terms.

        Returns:
            The formula resulting from performing all substitutions. Only
            constant name and variable name occurrences originating in the
            current formula are substituted (i.e., those originating in one of
            the specified substitutions are not subjected to additional
            substitutions).

        Raises:
            ForbiddenVariableError: If a term that is used in the requested
                substitution contains a variable name from `forbidden_variables`
                or a variable name occurrence that becomes bound when that term
                is substituted into the current formula.

        Examples:
            >>> Formula.parse('Ay[x=c]').substitute(
            ...     {'c': Term.parse('plus(d,x)'), 'x': Term.parse('c')}, {'z'})
            Ay[c=plus(d,x)]

            >>> Formula.parse('Ay[x=c]').substitute(
            ...     {'c': Term.parse('plus(d,z)')}, {'z'})
            Traceback (most recent call last):
              ...
            predicates.syntax.ForbiddenVariableError: z

            >>> Formula.parse('Ay[x=c]').substitute(
            ...     {'c': Term.parse('plus(d,y)')})
            Traceback (most recent call last):
              ...
            predicates.syntax.ForbiddenVariableError: y
        """
        for construct in substitution_map:
            assert is_constant(construct) or is_variable(construct)
        for variable in forbidden_variables:
            assert is_variable(variable)
        # Task 9.2
        if is_unary(self.root):
            return Formula(
                self.root, self.first.substitute(substitution_map, forbidden_variables)
            )
        elif is_binary(self.root):
            return Formula(
                self.root,
                self.first.substitute(substitution_map, forbidden_variables),
                self.second.substitute(substitution_map, forbidden_variables),
            )
        elif is_equality(self.root) or is_relation(self.root):
            new_args = [
                arg.substitute(substitution_map, forbidden_variables)
                for arg in self.arguments
            ]
            return Formula(self.root, new_args)
        else:  # Quantification, the only difficult case
            forbidden_variables = set(forbidden_variables)
            if self.variable in substitution_map.keys():
                # We want to make sure to skip over any substitutions of the quantified variable.
                # So we delete the substitution from a copy of the map.
                sub_map = substitution_map.copy()
                del sub_map[self.variable]
                return Formula(
                    self.root,
                    self.variable,
                    self.statement.substitute(sub_map, forbidden_variables),
                )
            else:
                # If no such substitution is requested, we just want to make sure to forbid any
                # substitutions that would introduce a new term with the bound variable in it.
                forbidden_variables.add(self.variable)
                return Formula(
                    self.root,
                    self.variable,
                    self.statement.substitute(substitution_map, forbidden_variables),
                )

    def propositional_skeleton(
        self,
    ) -> Tuple[PropositionalFormula, Mapping[str, Formula]]:
        """Computes a propositional skeleton of the current formula.

        Returns:
            A pair. The first element of the pair is a propositional formula
            obtained from the current formula by substituting every (outermost)
            subformula that has a relation name, equality, or quantifier at its
            root with a propositional variable name, consistently such that
            multiple identical such (outermost) subformulas are substituted with
            the same propositional variable name. The propositional variable
            names used for substitution are obtained, from left to right
            (considering their first occurrence), by calling
            `next`\ ``(``\ `~logic_utils.fresh_variable_name_generator`\ ``)``.
            The second element of the pair is a mapping from each propositional
            variable name to the subformula for which it was substituted.

        Examples:
            >>> formula = Formula.parse('((Ax[x=7]&x=7)|(~Q(y)->x=7))')
            >>> formula.propositional_skeleton()
            (((z1&z2)|(~z3->z2)), {'z1': Ax[x=7], 'z2': x=7, 'z3': Q(y)})
            >>> formula.propositional_skeleton()
            (((z4&z5)|(~z6->z5)), {'z4': Ax[x=7], 'z5': x=7, 'z6': Q(y)})
        """
        # Task 9.8

        """
        The biggest difficulty with the structure of this function is that---though we want to
        replace every quantification, equality, or relation invocation with a variable---we do not
        want to generate a new variable every time we encounter a new formula of this type. An
        example of this is building the skeleton of (R(x)|R(x)). This would have the skeleton
        (z1|z1), not (z1|z2). So, when implementing the recursion for building the skeleton, we
        need to keep track of which formulas already have variable assignments, and which don't.
        For this purpose, I define a new function which does all of the work but keeps track of
        the assignments along the way. This makes recursion much easier.
        """

        def build_skeleton(
            formula: Formula, mapping: Mapping[str, Formula]
        ) -> Tuple[PropositionalFormula, Mapping[str, Formula]]:
            """
            Computes a propositional skeleton of the current formula.

            Parameters:
                formula: A predicate logic formula.
                mapping: A mapping from variable names to predicate logic formulas.

            Returns:
                A pair, as returned by propositional_skeleton. The first element is the
                propositional skeleton of the given formula, where variable names from the
                given mapping are used if possible. The second element is a new mapping,
                which is built by adding any new variable names to the old mapping.
            """

            if (
                is_quantifier(formula.root)
                or is_equality(formula.root)
                or is_relation(formula.root)
            ):
                # Check if the formula already has a variable assignment. If it does, return that.
                for key in mapping.keys():
                    if mapping[key] == formula:
                        return tuple([PropositionalFormula.parse(key), mapping])

                # Otherwise, get a new one and update the mapping.
                variable = next(fresh_variable_name_generator)
                new_mapping = mapping.copy()
                new_mapping[variable] = formula
                return tuple([PropositionalFormula.parse(variable), new_mapping])

            elif is_unary(formula.root):
                # Build the skeleton for the operand, and add the operator.
                first_skeleton = list(build_skeleton(formula.first, mapping))
                first_propositional_formula = first_skeleton[0]
                first_mapping = first_skeleton[1]

                new_formula = PropositionalFormula(
                    formula.root, first_propositional_formula
                )
                return tuple([new_formula, first_mapping])
            else:
                # For binary operators, we build the skeleton for both the first and
                # second operands, but make sure to use the updated mapping when
                # building the second skeleton.
                first_skeleton = list(build_skeleton(formula.first, mapping))
                first_propositional_formula = first_skeleton[0]
                first_mapping = first_skeleton[1]

                second_skeleton = list(build_skeleton(formula.second, first_mapping))
                second_propositional_formula = second_skeleton[0]
                second_mapping = second_skeleton[1]

                new_formula = PropositionalFormula(
                    formula.root,
                    first_propositional_formula,
                    second_propositional_formula,
                )
                return tuple([new_formula, second_mapping])

        return build_skeleton(self, dict())

    @staticmethod
    def from_propositional_skeleton(
        skeleton: PropositionalFormula, substitution_map: Mapping[str, Formula]
    ) -> Formula:
        """Computes a predicate-logic formula from a propositional skeleton and
        a substitution map.

        Arguments:
            skeleton: propositional skeleton for the formula to compute,
                containing no constants or operators beyond ``'~'``, ``'->'``,
                ``'|'``, and ``'&'``.
            substitution_map: mapping from each propositional variable name of
                the given propositional skeleton to a predicate-logic formula.

        Returns:
            A predicate-logic formula obtained from the given propositional
            skeleton by substituting each propositional variable name with the
            formula mapped to it by the given map.

        Examples:
            >>> Formula.from_propositional_skeleton(
            ...     PropositionalFormula.parse('((z1&z2)|(~z3->z2))'),
            ...     {'z1': Formula.parse('Ax[x=7]'), 'z2': Formula.parse('x=7'),
            ...      'z3': Formula.parse('Q(y)')})
            ((Ax[x=7]&x=7)|(~Q(y)->x=7))

            >>> Formula.from_propositional_skeleton(
            ...     PropositionalFormula.parse('((z9&z2)|(~z3->z2))'),
            ...     {'z2': Formula.parse('x=7'), 'z3': Formula.parse('Q(y)'),
            ...      'z9': Formula.parse('Ax[x=7]')})
            ((Ax[x=7]&x=7)|(~Q(y)->x=7))
        """
        for operator in skeleton.operators():
            assert is_unary(operator) or is_binary(operator)
        for variable in skeleton.variables():
            assert variable in substitution_map
        # Task 9.10
        if is_propositional_variable(skeleton.root):
            return substitution_map[skeleton.root]
        elif is_unary(skeleton.root):
            return Formula(
                skeleton.root,
                Formula.from_propositional_skeleton(skeleton.first, substitution_map),
            )
        else:  # Binary operator
            return Formula(
                skeleton.root,
                Formula.from_propositional_skeleton(skeleton.first, substitution_map),
                Formula.from_propositional_skeleton(skeleton.second, substitution_map),
            )
