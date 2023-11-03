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

@lru_cache(maxsize=100) # Cache the return value of is_variable
def is_variable(string: str) -> bool:
    """Checks if the given string is a variable name.

    Parameters:
        string: string to check.

    Returns:
        ``True`` if the given string is a variable name, ``False`` otherwise.
    """
    return string[0] >= 'p' and string[0] <= 'z' and \
           (len(string) == 1 or string[1:].isdecimal())

@lru_cache(maxsize=100) # Cache the return value of is_constant
def is_constant(string: str) -> bool:
    """Checks if the given string is a constant.

    Parameters:
        string: string to check.

    Returns:
        ``True`` if the given string is a constant, ``False`` otherwise.
    """
    return string == 'T' or string == 'F'

@lru_cache(maxsize=100) # Cache the return value of is_unary
def is_unary(string: str) -> bool:
    """Checks if the given string is a unary operator.

    Parameters:
        string: string to check.

    Returns:
        ``True`` if the given string is a unary operator, ``False`` otherwise.
    """
    return string == '~'

@lru_cache(maxsize=100) # Cache the return value of is_binary
def is_binary(string: str) -> bool:
    """Checks if the given string is a binary operator.

    Parameters:
        string: string to check.

    Returns:
        ``True`` if the given string is a binary operator, ``False`` otherwise.
    """
    # Edited for task 3.1
    return string in {'&', '|',  '->', '+', '<->', '-&', '-|'}

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

    def __init__(self, root: str, first: Optional[Formula] = None,
                 second: Optional[Formula] = None):
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
        if is_unary(self.root):
            return self.root + self.first.__repr__()
        elif is_binary(self.root):
            return '(' + self.first.__repr__() + self.root + self.second.__repr__() + ')'
        else:
            return self.root

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
        x: Set[str] = set()
        if is_unary(self.root):
            x.update(self.first.variables())
        elif is_binary(self.root):
            x.update(self.first.variables())
            x.update(self.second.variables())
        elif self.root != 'T' and self.root != 'F':
            x.add(self.root)
        return x

    @memoized_parameterless_method
    def operators(self) -> Set[str]:
        """Finds all operators in the current formula.

        Returns:
            A set of all operators (including ``'T'`` and ``'F'``) used in the
            current formula.
        """
        # Task 1.3
        x: Set[str] = set()
        if is_unary(self.root):
            x.add('~')
            x.update(self.first.operators())
        elif is_binary(self.root):
            x.add(self.root)
            x.update(self.first.operators())
            x.update(self.second.operators())
        elif self.root == 'T' or self.root == 'F':
            x.add(self.root)
        return x
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
        error: Tuple[Union[Formula, None], str] = [None, 'Unexpected symbol']
        if string == '': # To avoid index errors (looking for a first character when there is none), we have to
                         # treat the case where the string is empty seperately.
            return error
        
        elif string[0] == 'T' or string[0] == 'F': # Otherwise, we check if the prefix is a constant, in which case we're done.
            if len(string) > 1:
                return [Formula(string[0]), string[1:]]
            else:
                return [Formula(string[0]), '']
            
        elif is_variable(string[0]): # If our first character is a variable, we need to find the whole variable.
            if len(string) == 1: # If the whole string is a single-letter variable, we're done.
                return [Formula(string[0]), '']
            else:
                variable = Formula(string[0]) # Otherwise, we initialize our variable to the first character,
                rest = string[1:]             # and say the rest is everything else.
                for i in range(1, len(string)):     # Then we look to see if the first letter is the prefix of another variable.
                    if is_variable(string[:i + 1]):         # If it really is the prefix of another variable,
                        variable = Formula(string[:i + 1])  # we change our formula to reflect that,
                        rest = string[i + 1:]               # and we say the rest is everything past it.
                    else:                                   
                        return [variable, rest]             # Otherwise, we know only the first character is a variable.
                return [variable, rest]

        elif string[0] == '~' and len(string) > 1: # If the prefix is a ~, then we know we just parse everything to the right.
            firstPrefix, rest = Formula._parse_prefix(string[1:])
            return [Formula('~', firstPrefix), rest]
        
        elif string[0] == '(' and len(string) > 1: # I've changed this to recursion for Ch. 3 because fixing my old thing would be just as hard.
            firstPrefix, rest = Formula._parse_prefix(string[1:]) # Recursively find the first prefix (left-hand conjunct, disjunct, etc.)
            secondPrefix = None # I need to initialize a future variable to "None" to avoid reference-before-assignment errors.
            # Once I've found the first prefix, I want to figure out what the operator is that comes after it.
            # My biggest fear is an "index out of bound" error: if I look for an operator in an empty string, Python gets mad.
            if firstPrefix is None or len(rest) == 0:
                return error
            # If I find a 1-character operator and try to parse the rest (when there is no rest), Python gets mad. Hence length must be > 1.
            elif (rest[0] == '&' or rest[0] == '|' or rest[0] == '+') and len(rest) > 1: 
                operator = rest[0]
                secondPrefix, rest = Formula._parse_prefix(rest[1:])
            # If I try to find a longer operator when the string isn't that long, Python gets mad. So first I have to check the length.
            # If my length is at least 3, then I can have a longer operator and something after it (the right-hand conjunct, disjunct, etc.)
            elif len(rest) >= 3:
                if rest[0] == '-' and (rest[1] == '>' or rest[1] == '&' or rest[1] == '|'): # Checking for the two-character operators.
                    operator = rest[0] + rest[1]
                    secondPrefix, rest = Formula._parse_prefix(rest[2:])
                # If my operator isn't a 2-character one, I need to check for the final, 3-character one, '<->'.
                # Again I need to check the length of the string here.
                if (rest[0] == '<' and rest[1] == '-' and rest[2] == '>') and len(rest) >= 4:
                    operator = '<->'
                    secondPrefix, rest = Formula._parse_prefix(rest[3:])
            else: # If there's no operator to go with the parenthesis, we return an error.
                return error
            if secondPrefix is None or len(rest) == 0: # If we ran into an error finding the second prefix, we need to pass it along.
                return error
            elif rest[0] == ')': # Otherwise, we have a well-formed formula as a prefix, so long as it ends with a closing parenthesis.
                return [Formula(operator, firstPrefix, secondPrefix), rest[1:]]
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
        return (prefix[0] is not None and prefix[1] == '')
        
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

    @staticmethod
    def parse_polish(string: str) -> Formula:
        """Parses the given polish notation representation into a formula.

        Parameters:
            string: string to parse.

        Returns:
            A formula whose polish notation representation is the given string.
        """
        # Optional Task 1.8

    def substitute_variables(self, substitution_map: Mapping[str, Formula]) -> \
            Formula:
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
        if is_variable(self.root):
            if self.root in substitution_map:
                return substitution_map[self.root]
        elif is_unary(self.root):
            return Formula(self.root, self.first.substitute_variables(substitution_map))
        elif is_binary(self.root):
            return Formula(self.root, self.first.substitute_variables(substitution_map), self.second.substitute_variables(substitution_map))
        return self
        

    def substitute_operators(self, substitution_map: Mapping[str, Formula]) -> \
            Formula:
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
            assert is_constant(operator) or is_unary(operator) or \
                   is_binary(operator)
            assert substitution_map[operator].variables().issubset({'p', 'q'})
        # Task 3.4
        if is_constant(self.root): 
        # If our root is a constant, check if it is mapped to something.
            if self.root in substitution_map: # If it is, replace it.
                return substitution_map[self.root] 
        elif is_unary(self.root): 
        # If our root is unary, we check if it is mapped to something.
            if self.root in substitution_map: 
            # If it is, we need to replace both the root and the object that the root is operating on.
                return substitution_map[self.root].substitute_variables({'p': self.first.substitute_operators(substitution_map)}) 
                # Of course, if the root appears in the mapping, it is mapped to a formula in terms of 'p', so we need to replace 'p' with the object.
            else:
            # Otherwise, we just need to replace the object.
                return Formula(self.root, self.first.substitute_operators(substitution_map)) # 
        elif is_binary(self.root):
        # Similarly, for binary operators, we need to replace both objects (both conjuncts/disjuncts, etc.) and, possibly, the operator itself.
            if self.root in substitution_map:
            # If we need to replace the operator itself, we (1) replace the first and second objects, and then (2) replace the operator.
            # Again, we have to be careful because the mapping uses 'p' and 'q', so we need to replace those.
                return substitution_map[self.root].substitute_variables({'p': self.first.substitute_operators(substitution_map), 'q': self.second.substitute_operators(substitution_map)})
            else:
            # If we don't, we can just replace the two objects.
                return Formula(self.root, self.first.substitute_operators(substitution_map), self.second.substitute_operators(substitution_map))
        return self
