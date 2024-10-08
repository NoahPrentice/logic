# This file is part of the materials accompanying the book
# "Mathematical Logic through Python" by Gonczarowski and Nisan,
# Cambridge University Press. Book site: www.LogicThruPython.org
# (c) Yannai A. Gonczarowski and Noam Nisan, 2017-2022
# File name: propositions/syntax.py

"""Syntactic handling of propositional formulas."""

from __future__ import annotations
from functools import lru_cache
from typing import Mapping, Optional, Set, Tuple, Union

from logic_utils import frozen, memoized_parameterless_method


@lru_cache(maxsize=100)  # Cache the return value of is_variable
def is_variable(string: str) -> bool:
    """Checks if the given string is a variable name.

    Parameters:
        string: string to check.

    Returns:
        ``True`` if the given string is a variable name, ``False`` otherwise.
    """
    return (
        string[0] >= "p"
        and string[0] <= "z"
        and (len(string) == 1 or string[1:].isdecimal())
    )


@lru_cache(maxsize=100)  # Cache the return value of is_constant
def is_constant(string: str) -> bool:
    """Checks if the given string is a constant.

    Parameters:
        string: string to check.

    Returns:
        ``True`` if the given string is a constant, ``False`` otherwise.
    """
    return string == "T" or string == "F"


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
    # Edited for task 3.1
    return string in {"&", "|", "->", "+", "<->", "-&", "-|"}


@frozen
class Formula:
    """An immutable propositional formula in tree representation, composed from
    variable names, and operators applied to them.

    Attributes:
        root (`str`): the constant, variable name, or operator at the root of
            the formula tree.
        first (`~typing.Optional`\\[`Formula`]): the first operand of the root,
            if the root is a unary or binary operator.
        second (`~typing.Optional`\\[`Formula`]): the second operand of the
            root, if the root is a binary operator.
    """

    root: str
    first: Optional[Formula]
    second: Optional[Formula]

    def __init__(
        self,
        root: str,
        first: Optional[Formula] = None,
        second: Optional[Formula] = None,
    ):
        """Initializes a `Formula` from its root and root operands.

        Parameters:
            root: the root for the formula tree.
            first: the first operand for the root, if the root is a unary or
                binary operator.
            second: the second operand for the root, if the root is a binary
                operator.
        """
        if is_variable(root) or is_constant(root):
            assert first is None and second is None
            self.root = root
        elif is_unary(root):
            assert first is not None and second is None
            self.root, self.first = root, first
        else:
            assert is_binary(root)
            assert first is not None and second is not None
            self.root, self.first, self.second = root, first, second

    @memoized_parameterless_method
    def __repr__(self) -> str:
        """Computes the string representation of the current formula.

        Returns:
            The standard string representation of the current formula.
        """
        # Task 1.1

        # Base case
        if is_variable(self.root) or is_constant(self.root):
            return self.root

        # Recursive case: self is an operator.
        if is_unary(self.root):
            return self.root + str(self.first)
        else:  # Binary operator
            return "(" + str(self.first) + self.root + str(self.second) + ")"

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

    @memoized_parameterless_method
    def variables(self) -> Set[str]:
        """Finds all variable names in the current formula.

        Returns:
            A set of all variable names used in the current formula.
        """
        # Task 1.2

        variables = set()

        # Base case
        if is_variable(self.root):
            variables.add(self.root)

        # Recursive case
        elif is_unary(self.root):
            variables.update(self.first.variables())
        elif is_binary(self.root):
            variables.update(self.first.variables())
            variables.update(self.second.variables())
        return variables

    @memoized_parameterless_method
    def operators(self) -> Set[str]:
        """Finds all operators in the current formula.

        Returns:
            A set of all operators (including ``'T'`` and ``'F'``) used in the
            current formula.
        """
        # Task 1.3

        operators = set()

        # Base case
        if is_constant(self.root):
            operators.add(self.root)

        # Recursive case
        elif is_unary(self.root):
            operators.add("~")
            operators.update(self.first.operators())
        elif is_binary(self.root):
            operators.add(self.root)
            operators.update(self.first.operators())
            operators.update(self.second.operators())
        return operators

    def NEW_parse_constant_or_variable(string: str) -> Tuple[Union[str, None], str]:
        """Parses a constant or variable at the beginning of a string. For example,
        parse_constant_or_variable("x19&F") returns ("x19", "&F), while
        parse_constant_or_variable("(x19&F)) returns (None, "x19&f").

        Parameters:
            string: string to parse

        Returns:
            A pair. The first element of the pair is a string containing the constant or
            variable at the beginning of the given string, and the second element is the
            rest. If no prefix of the given string is a constant or variable, returns
            (None, string).
        """
        if not (is_variable(string[0]) or is_constant(string[0])):
            return (None, string)
        if len(string) == 1:
            return (string, "")
        # If the string is longer than 1 character, we need to make sure we
        # return the entire variable name instead of just the beginning. So we
        # make our string longer and longer until we no longer have a variable.
        variable = string[0]
        rest = string[1:]
        for i in range(1, len(string)):
            if is_variable(string[: i + 1]) or is_constant(string[: i + 1]):
                variable = string[: i + 1]
                rest = string[i + 1 :]
        return (variable, rest)

    def NEW_parse_binary_operator(string: str) -> Tuple[Union[str, None], str]:
        """Parses a binary operator at the beginning of a string. For example,
        parse_operator("<->&abc") returns ("<->", "&abc"), while
        parse_operator("--x") returns error = (None, "Unexpected symbol).

        Parameters:
            string: string to parse

        Returns:
            A pair of the operator at the beginning of the string and the rest.
            If no prefix of the given string is an operator, returns an error.
        """
        error = (None, "Unexpected symbol")

        if len(string) == 0:
            return error

        # 1-character operators
        if string[0] == "&" or string[0] == "|" or string[0] == "+":
            return (string[0], string[1:])

        # 2-character operators
        if len(string) == 1:
            return error
        if string[0] == "-" and (
            string[1] == ">" or string[1] == "&" or string[1] == "|"
        ):
            return (string[0:2], string[2:])

        # 3-character operator
        if len(string) == 2:
            return error
        if string[0:3] == "<->":
            return (string[0:3], string[3:])
        return error

    @staticmethod
    def _parse_prefix(string: str) -> Tuple[Union[Formula, None], str]:
        """Parses a prefix of the given string into a formula.

        Parameters:
            string: string to parse.

        Returns:
            A pair of the parsed formula and the unparsed suffix of the string.
            If the given string has as a prefix a variable name (e.g.,
            ``'x12'``) or a unary operator followed by a variable name, then the
            parsed prefix will include that entire variable name (and not just a
            part of it, such as ``'x1'``). If no prefix of the given string is a
            valid standard string representation of a formula then returned pair
            should be of ``None`` and an error message, where the error message
            is a string with some human-readable content.
        """
        # Task 1.4, edited for task 3.1

        error = (None, "Unexpected symbol")

        # Base case: string is empty, or starts with a constant or variable.
        if string == "":
            return error

        elif is_constant(string[0]) or is_variable(string[0]):
            # The logic of parsing constants and variables is outsourced to a new helper
            # function I made. It is located above _parse_prefix.
            variable, rest = Formula.NEW_parse_constant_or_variable(string)
            return (Formula(variable), rest)

        # Recursive case: string starts with a ~ or (
        elif string[0] == "~" and len(string) > 1:
            # In this case, we recursively parse the operand (what comes after "~").
            first_prefix, rest = Formula._parse_prefix(string[1:])
            if first_prefix is None:
                return error
            return (Formula("~", first_prefix), rest)

        elif string[0] == "(" and len(string) > 1:
            # In this case, we expect a binary operator. So we
            #   (1) recursively parse the first operand (left conjunct, disjunct, etc.),
            #   (2) find the operator used, and
            #   (3) recursively parse the second operand (right conjunct, etc.).
            # All this time, we have to be very careful with how long the string is, so
            # that we don't incur index-out-of-bound errors. This explains the frequent
            # checks on len(rest). Additionally, if any of our recursive calls yield
            # errors, we need to pass that along by returning "error".

            # (1) Recursively parse the first operand
            first_prefix, rest = Formula._parse_prefix(string[1:])
            if first_prefix is None or len(rest) == 0:
                return error

            # (2) Find the operator
            # The logic of parsing binary operators is outsourced to a new helper
            # function I made. It is located above _parse_prefix.
            operator, rest = Formula.NEW_parse_binary_operator(rest)
            if operator is None:
                return error

            # (3) recursively parse the second operand
            second_prefix = None
            second_prefix, rest = Formula._parse_prefix(rest)
            if second_prefix is None or len(rest) == 0:
                return error
            elif rest[0] == ")":
                return (Formula(operator, first_prefix, second_prefix), rest[1:])
        return error

    @staticmethod
    def is_formula(string: str) -> bool:
        """Checks if the given string is a valid representation of a formula.

        Parameters:
            string: string to check.

        Returns:
            ``True`` if the given string is a valid standard string
            representation of a formula, ``False`` otherwise.
        """
        # Task 1.5

        prefix = Formula._parse_prefix(string)
        return prefix[0] is not None and prefix[1] == ""

    @staticmethod
    def parse(string: str) -> Formula:
        """Parses the given valid string representation into a formula.

        Parameters:
            string: string to parse.

        Returns:
            A formula whose standard string representation is the given string.
        """
        assert Formula.is_formula(string)
        # Task 1.6

        return Formula._parse_prefix(string)[0]

    def polish(self) -> str:
        """Computes the polish notation representation of the current formula.

        Returns:
            The polish notation representation of the current formula.
        """
        # Optional Task 1.7

        if is_unary(self.root):
            return self.root + self.first.polish()
        elif is_binary(self.root):
            return self.root + self.first.polish() + self.second.polish()
        else:
            return self.root

    @staticmethod
    def parse_polish(string: str) -> Formula:
        """Parses the given polish notation representation into a formula.

        Parameters:
            string: string to parse.

        Returns:
            A formula whose polish notation representation is the given string.
        """
        # Optional Task 1.8

        assert len(string) > 0

        # We start by building a _parse_prefix equivalent for polish notation.
        def polish_prefix(string: str) -> Tuple[Union[Formula, None], str]:
            """Parses a prefix of the given string into a formula. Assumes the string is
            given in polish notation.

            Parameters:
                string: string to parse.

            Returns: A pair of the prefix of the formula and the rest.
            """

            # Note that, as in _parse_prefix above, I outsource parsing constants,
            # variables, and binary operators to new helper functions I made. These are
            # located above _parse_prefix.

            # Base case: string starts with a constant or variable
            variable, rest = Formula.NEW_parse_constant_or_variable(string)
            if variable is not None:
                return (Formula(variable), rest)

            # Recursive case: string starts with an operator
            elif is_unary(string[0]):
                operand, rest = polish_prefix(string[1:])
                return (Formula(string[0], operand), rest)

            # For binary operators, we try to parse the operator and then recurse to find
            # the operands. We check for errors at every step, just to be safe :-)
            operator, rest = Formula.NEW_parse_binary_operator(string)
            if operator is None:
                return (operator, rest)

            left, rest = polish_prefix(rest)
            if left is None:
                return (left, rest)

            right, rest = polish_prefix(rest)
            if right is None:
                return (right, rest)
            return (Formula(operator, left, right), rest)

        # Then parsing is as simple as calling this function.
        formula, suffix = polish_prefix(string)
        if suffix == "":
            return formula
        return (None, "Unexpected symbol.")

    def substitute_variables(self, substitution_map: Mapping[str, Formula]) -> Formula:
        """Substitutes in the current formula, each variable name `v` that is a
        key in `substitution_map` with the formula `substitution_map[v]`.

        Parameters:
            substitution_map: mapping defining the substitutions to be
                performed.

        Returns:
            The formula resulting from performing all substitutions. Only
            variable name occurrences originating in the current formula are
            substituted (i.e., variable name occurrences originating in one of
            the specified substitutions are not subjected to additional
            substitutions).

        Examples:
            >>> Formula.parse('((p->p)|r)').substitute_variables(
            ...     {'p': Formula.parse('(q&r)'), 'r': Formula.parse('p')})
            (((q&r)->(q&r))|p)
        """
        for variable in substitution_map:
            assert is_variable(variable)
        # Task 3.3

        # Base case
        if is_variable(self.root):
            if self.root in substitution_map:
                return substitution_map[self.root]

        # Recursive case
        elif is_unary(self.root):
            return Formula(self.root, self.first.substitute_variables(substitution_map))
        elif is_binary(self.root):
            return Formula(
                self.root,
                self.first.substitute_variables(substitution_map),
                self.second.substitute_variables(substitution_map),
            )
        return self

    def substitute_operators(self, substitution_map: Mapping[str, Formula]) -> Formula:
        """Substitutes in the current formula, each constant or operator `op`
        that is a key in `substitution_map` with the formula
        `substitution_map[op]` applied to its (zero or one or two) operands,
        where the first operand is used for every occurrence of ``'p'`` in the
        formula and the second for every occurrence of ``'q'``.

        Parameters:
            substitution_map: mapping defining the substitutions to be
                performed.

        Returns:
            The formula resulting from performing all substitutions. Only
            operator occurrences originating in the current formula are
            substituted (i.e., operator occurrences originating in one of the
            specified substitutions are not subjected to additional
            substitutions).

        Examples:
            >>> Formula.parse('((x&y)&~z)').substitute_operators(
            ...     {'&': Formula.parse('~(~p|~q)')})
            ~(~~(~x|~y)|~~z)
        """
        for operator in substitution_map:
            assert is_constant(operator) or is_unary(operator) or is_binary(operator)
            assert substitution_map[operator].variables().issubset({"p", "q"})
        # Task 3.4

        # Base case
        if is_constant(self.root) and self.root in substitution_map:
            return substitution_map[self.root]

        # Recursive case
        if is_unary(self.root):
            new_first = self.first.substitute_operators(substitution_map)
            if self.root in substitution_map:
                return substitution_map[self.root].substitute_variables(
                    {"p": new_first}
                )
            return Formula(self.root, new_first)
        elif is_binary(self.root):
            new_first = self.first.substitute_operators(substitution_map)
            new_second = self.second.substitute_operators(substitution_map)
            if self.root in substitution_map:
                return substitution_map[self.root].substitute_variables(
                    {"p": new_first, "q": new_second}
                )
            return Formula(self.root, new_first, new_second)
        return self
