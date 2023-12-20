# This file is part of the materials accompanying the book
# "Mathematical Logic through Python" by Gonczarowski and Nisan,
# Cambridge University Press. Book site: www.LogicThruPython.org
# (c) Yannai A. Gonczarowski and Noam Nisan, 2017-2022
# File name: propositions/proofs.py

"""Proofs by deduction in Propositional Logic."""

from __future__ import annotations
from typing import AbstractSet, FrozenSet, List, Mapping, Optional, Sequence, \
                   Set, Tuple, Union

from logic_utils import frozen, memoized_parameterless_method

from propositions.syntax import *

#: A mapping from variable names to formulas.
SpecializationMap = Mapping[str, Formula]

@frozen
class InferenceRule:
    """An immutable inference rule in Propositional Logic, comprised of zero
    or more assumed propositional formulas, and a conclusion propositional
    formula.

    Attributes:
        assumptions (`~typing.Tuple`\\[`~propositions.syntax.Formula`, ...]):
            the assumptions of the rule.
        conclusion (`~propositions.syntax.Formula`): the conclusion of the rule.
    """
    assumptions: Tuple[Formula, ...]
    conclusion: Formula

    def __init__(self, assumptions: Sequence[Formula], conclusion: Formula):
        """Initializes an `InferenceRule` from its assumptions and conclusion.

        Parameters:
            assumptions: the assumptions for the rule.
            conclusion: the conclusion for the rule.
        """
        self.assumptions = tuple(assumptions)
        self.conclusion = conclusion

    @memoized_parameterless_method
    def __repr__(self) -> str:
        """Computes a string representation of the current inference rule.

        Returns:
            A string representation of the current inference rule.
        """
        return str([str(assumption) for assumption in self.assumptions]) + \
               ' ==> ' + "'" + str(self.conclusion) + "'"

    def __eq__(self, other: object) -> bool:
        """Compares the current inference rule with the given one.

        Parameters:
            other: object to compare to.

        Returns:
            ``True`` if the given object is an `InferenceRule` object that
            equals the current inference rule, ``False`` otherwise.
        """
        return isinstance(other, InferenceRule) and \
               self.assumptions == other.assumptions and \
               self.conclusion == other.conclusion

    def __ne__(self, other: object) -> bool:
        """Compares the current inference rule with the given one.

        Parameters:
            other: object to compare to.

        Returns:
            ``True`` if the given object is not an `InferenceRule` object or
            does not does not equal the current inference rule, ``False``
            otherwise.
        """
        return not self == other

    def __hash__(self) -> int:
        return hash(str(self))
        
    def variables(self) -> Set[str]:
        """Finds all variable names in the current inference rule.

        Returns:
            A set of all variable names used in the assumptions and in the
            conclusion of the current inference rule.
        """
        # Task 4.1
        variables = set()
        for assumption in self.assumptions:
            variables.update(assumption.variables())
        variables.update(self.conclusion.variables())
        return variables


    def specialize(self, specialization_map: SpecializationMap) -> \
            InferenceRule:
        """Specializes the current inference rule by simultaneously substituting
        each variable name `v` that is a key in `specialization_map` with the
        formula `specialization_map[v]`.

        Parameters:
            specialization_map: mapping defining the specialization to be
                performed.

        Returns:
            The resulting inference rule.
        """        
        for variable in specialization_map:
            assert is_variable(variable)
        # Task 4.4
        assumptions = []
        for assumption in self.assumptions:
            assumptions.append(assumption.substitute_variables(specialization_map))
        return InferenceRule(assumptions, self.conclusion.substitute_variables(specialization_map))

    @staticmethod
    def _merge_specialization_maps(
            specialization_map1: Union[SpecializationMap, None],
            specialization_map2: Union[SpecializationMap, None]) -> \
            Union[SpecializationMap, None]:
        """Merges the given specialization maps while checking their
        consistency.

        Parameters:
            specialization_map1: first mapping to merge, or ``None``.
            specialization_map2: second mapping to merge, or ``None``.

        Returns:
            A single mapping containing all (key, value) pairs that appear in
            either of the given maps, or ``None`` if one of the given maps is
            ``None`` or if some key appears in both given maps but with
            different values.
        """
        if specialization_map1 is not None:
            for variable in specialization_map1:
                assert is_variable(variable)
        if specialization_map2 is not None:
            for variable in specialization_map2:
                assert is_variable(variable)
        # Task 4.5a
        if specialization_map1 is None or specialization_map2 is None:
            return None
        merged_map = dict()
        for variable in specialization_map1:
            if variable in specialization_map2:
                if specialization_map1[variable] != specialization_map2[variable]:
                    return None
            else:
                merged_map.update({variable: specialization_map1[variable]})
        for variable in specialization_map2:
            merged_map.update({variable: specialization_map2[variable]})
        return merged_map
    @staticmethod
    def _formula_specialization_map(general: Formula, specialization: Formula) \
            -> Union[SpecializationMap, None]:
        """Computes the minimal specialization map by which the given formula
        specializes to the given specialization.

        Parameters:
            general: non-specialized formula for which to compute the map.
            specialization: specialization for which to compute the map.

        Returns:
            The computed specialization map, or ``None`` if `specialization` is
            in fact not a specialization of `general`.
        """
        # Task 4.5b
        if is_constant(general.root):
            if general.root == specialization.root:
                return dict()
            else:
                return None
        elif is_variable(general.root):
            return {general.root: specialization}
        elif general.root != specialization.root:
            return None
        elif is_unary(general.root):
            return InferenceRule._formula_specialization_map(general.first, specialization.first)
        else:
            return InferenceRule._merge_specialization_maps(InferenceRule._formula_specialization_map(general.first, specialization.first),
                                                            InferenceRule._formula_specialization_map(general.second, specialization.second))

    def specialization_map(self, specialization: InferenceRule) -> \
            Union[SpecializationMap, None]:
        """Computes the minimal specialization map by which the current
        inference rule specializes to the given specialization.

        Parameters:
            specialization: specialization for which to compute the map.

        Returns:
            The computed specialization map, or ``None`` if `specialization` is
            in fact not a specialization of the current rule.
        """
        # Task 4.5c
        mapList = []
        if len(self.assumptions) != len(specialization.assumptions): # To avoid index errors, I have to make sure both inference rules
                                                                     # have the same assumptions.
            return None
        for i in range(len(self.assumptions)):
            mapList.append(InferenceRule._formula_specialization_map(self.assumptions[i], specialization.assumptions[i]))
        mapList.append(InferenceRule._formula_specialization_map(self.conclusion, specialization.conclusion))
        if len(mapList) == 1: # To avoid index errors, I check if there's only 1 map (if there were 0 assumptions)
            return mapList[0]
        else:
            finalMap = InferenceRule._merge_specialization_maps(mapList.pop(0), mapList.pop(0))
            while len(mapList) != 0:
                finalMap = InferenceRule._merge_specialization_maps(finalMap, mapList.pop(0))
            return finalMap


    def is_specialization_of(self, general: InferenceRule) -> bool:
        """Checks if the current inference rule is a specialization of the given
        inference rule.

        Parameters:
            general: non-specialized inference rule to check.

        Returns:
            ``True`` if the current inference rule is a specialization of
            `general`, ``False`` otherwise.
        """
        return general.specialization_map(self) is not None

@frozen
class Proof:
    """An immutable deductive proof in Propositional Logic, comprised of a
    statement in the form of an inference rule, a set of inference rules that
    may be used in the proof, and a list of lines that prove the statement via
    these inference rules.

    Attributes:
        statement (`InferenceRule`): the statement proven by the proof.
        rules (`~typing.AbstractSet`\\[`InferenceRule`]): the allowed rules of
            the proof.
        lines (`~typing.Tuple`\\[`Line`]): the lines of the proof.
    """
    statement: InferenceRule
    rules: FrozenSet[InferenceRule]
    lines: Tuple[Proof.Line, ...]
    
    def __init__(self, statement: InferenceRule,
                 rules: AbstractSet[InferenceRule],
                 lines: Sequence[Proof.Line]):
        """Initializes a `Proof` from its statement, allowed inference rules,
        and lines.

        Parameters:
            statement: the statement to be proven by the proof.
            rules: the allowed rules for the proof.
            lines: the lines for the proof.
        """
        self.statement = statement
        self.rules = frozenset(rules)
        self.lines = tuple(lines)

    @frozen
    class Line:
        """An immutable line in a deductive proof, comprised of a formula that
        is justified either as an assumption of the proof, or as the conclusion
        of a specialization of an allowed inference rule of the proof, the
        assumptions of which are justified by previous lines in the proof.

        Attributes:
            formula (`~propositions.syntax.Formula`): the formula justified by
                the line.
            rule (`~typing.Optional`\\[`InferenceRule`]): the inference rule,
                out of those allowed in the proof, that has a specialization
                that concludes the formula; or ``None`` if the formula is
                justified as an assumption of the proof.
            assumptions (`~typing.Optional`\\[`~typing.Tuple`\\[`int`]): tuple
                of zero or more numbers of previous lines in the proof whose
                formulas are the respective assumptions of the specialization of
                the rule that concludes the formula, if the formula is not
                justified as an assumption of the proof.
        """
        formula: Formula
        rule: Optional[InferenceRule]
        assumptions: Optional[Tuple[int, ...]]

        def __init__(self, formula: Formula,
                     rule: Optional[InferenceRule] = None,
                     assumptions: Optional[Sequence[int]] = None):
            """Initializes a `~Proof.Line` from its formula, and optionally its
            rule and numbers of justifying previous lines.

            Parameters:
                formula: the formula to be justified by the line.
                rule: the inference rule, out of those allowed in the proof,
                    that has a specialization that concludes the formula; or
                    ``None`` if the formula is to be justified as an assumption
                    of the proof.
                assumptions: numbers of previous lines in the proof whose
                    formulas are the respective assumptions of the
                    specialization of the rule that concludes the formula, or
                    ``None`` if the formula is to be justified as an assumption
                    of the proof.
            """
            assert (rule is None and assumptions is None) or \
                   (rule is not None and assumptions is not None)
            self.formula = formula
            self.rule = rule
            if assumptions is not None:
                self.assumptions = tuple(assumptions)

        def __repr__(self) -> str:
            """Computes a string representation of the current line.

            Returns:
                A string representation of the current line.
            """
            if self.rule is None:
                return str(self.formula)
            else:
                r = str(self.formula) + '    (Inference Rule ' + str(self.rule)
                if len(self.assumptions) == 1:
                    r += ' on line ' + str(self.assumptions[0])
                elif len(self.assumptions) > 1:
                    r += ' on lines ' + ','.join(map(str, self.assumptions))
                r += ')'
                return r

        def is_assumption(self) -> bool:
            """Checks if the current proof line is justified as an assumption of
            the proof.

            Returns:
                ``True`` if the current proof line is justified as an assumption
                of the proof, ``False`` otherwise.
            """
            return self.rule is None
        
    def __repr__(self) -> str:
        """Computes a string representation of the current proof.

        Returns:
            A string representation of the current proof.
        """
        r = 'Proof of ' + str(self.statement) + ' via inference rules:\n'
        for rule in self.rules:
            r += '  ' + str(rule) + '\n'
        r += 'Lines:\n'
        for i in range(len(self.lines)):
            r += ('%3d) ' % i) + str(self.lines[i]) + '\n'
        r += "QED\n"
        return r

    def rule_for_line(self, line_number: int) -> Union[InferenceRule, None]:
        """Computes the inference rule whose conclusion is the formula justified
        by the specified line, and whose assumptions are the formulas justified
        by the lines specified as the assumptions of that line.

        Parameters:
            line_number: number of the line according to which to compute the
                inference rule.

        Returns:
            The computed inference rule, with assumptions ordered in the order
            of their numbers in the specified line, or ``None`` if the specified
            line is justified as an assumption.
        """
        assert line_number < len(self.lines)
        # Task 4.6a
        if self.lines[line_number].rule is None: # If the line is justified as an assumption, we return None.
            return None
        assumptions = [] # Otherwise, we find all the assumptions of the rule by looping through the lines mentioned.

        # Because self is a proof object, we need to point to its list of lines, specify which line we're talking about, and make sure we talk
        # about the assumptions of the given line number. This "assumptions" property is a list of indices for other line numbers, not the
        # line or its formula itself. Making sure to add neither the index, nor the line itself, but only the formula of the line, took me ages.
        
        for assumptionNumber in self.lines[line_number].assumptions: 
            assumptions.append(self.lines[assumptionNumber].formula)
            
        return InferenceRule(assumptions, self.lines[line_number].formula) # Then we just list the assumptions and the conclusion

    def is_line_valid(self, line_number: int) -> bool:
        """Checks if the specified line validly follows from its justifications.

        Parameters:
            line_number: number of the line to check.

        Returns:
            If the specified line is justified as an assumption, then ``True``
            if the formula justified by this line is an assumption of the
            current proof, ``False`` otherwise. Otherwise (i.e., if the
            specified line is justified as a conclusion of an inference rule),
            ``True`` if the rule specified for that line is one of the allowed
            inference rules in the current proof, and it has a specialization
            that satisfies all of the following:

            1. The conclusion of that specialization is the formula justified by
               that line.
            2. The assumptions of this specialization are the formulas justified
               by the lines that are specified as the assumptions of that line
               (in the order of their numbers in that line), all of which must
               be previous lines.
        """
        assert line_number < len(self.lines)
        # Task 4.6b
        line = self.lines[line_number]
        if line.rule is None: # If the line is not justified by any rule, we check if it's an assumption.
            return line.formula in self.statement.assumptions
        else:
            is_specialization = False # If the line is justified by a rule, we try to find a potential allowed rule that specializes to it.
            for allowedRule in self.rules:
                if line.rule == allowedRule:
                    generalRule = allowedRule # If we find one, we note which rule it is and tell python we've found a potential specialization.
                    is_specialization = True
                    break
            if not is_specialization: # If we didn't find a potential specialization, we know the line is not valid.
                return False
            else: # If we found a potential specialization, we first need to make sure it actually specializes to the rule used.
                specificRule = self.rule_for_line(line_number)
                specializationMap = generalRule.specialization_map(specificRule)
                if specializationMap is None: # If it doesn't specialize to the rule used, the line is not valid.
                    return False
                else: # Otherwise, we have a genuine specialization.
                    specialization = generalRule.specialize(specializationMap)
                    if specialization.conclusion != line.formula: # For condition 1, we just check if the conclusion of the specialization is as needed.
                        return False
                    else: # For condition 2, we check to make sure the assumptions are the same and in the correct order
                        for i in range(len(specialization.assumptions)):
                            if specialization.assumptions[i] != self.lines[line.assumptions[i]].formula:
                                return False
                        for i in line.assumptions: # We then add in a final check to make sure we're not using a rule on later line.
                            if i >= line_number:
                                return False
        return True
        
    def is_valid(self) -> bool:
        """Checks if the current proof is a valid proof of its claimed statement
        via its inference rules.

        Returns:
            ``True`` if the current proof is a valid proof of its claimed
            statement via its inference rules, ``False`` otherwise.
        """
        # Task 4.6c
        if len(self.lines) == 0:
            return False
        elif self.statement.conclusion != self.lines[-1].formula:
            return False
        for i in range(len(self.lines)):
            if not self.is_line_valid(i):
                return False
        return True

def prove_specialization(proof: Proof, specialization: InferenceRule) -> Proof:
    """Converts the given proof of an inference rule to a proof of the given
    specialization of that inference rule.

    Parameters:
        proof: valid proof to convert.
        specialization: specialization of the rule proven by the given proof.

    Returns:
        A valid proof of the given specialization via the same inference rules
        as the given proof.
    """
    assert proof.is_valid()
    assert specialization.is_specialization_of(proof.statement)
    # Task 5.1
    map = proof.statement.specialization_map(specialization)
    lines = []
    for line in proof.lines:
        if hasattr(line, 'assumptions'):
            lines.append(Proof.Line(line.formula.substitute_variables(map), line.rule, line.assumptions))
        else:
            lines.append(Proof.Line(line.formula.substitute_variables(map), line.rule))
    return Proof(specialization, proof.rules, lines)

def _inline_proof_once(main_proof: Proof, line_number: int,
                       lemma_proof: Proof) -> Proof:
    """Inlines the given proof of a "lemma" inference rule into the given proof
    that uses that "lemma" rule, eliminating the usage of (a specialization of)
    that "lemma" rule in the specified line in the latter proof.

    Parameters:
        main_proof: valid proof to inline into.
        line_number: number of the line in `main_proof` that should be replaced.
        lemma_proof: valid proof of the inference rule of the specified line (an
            allowed inference rule of `main_proof`).

    Returns:
        A valid proof obtained by replacing the specified line in `main_proof`
        with a full (specialized) list of lines proving the formula of the
        specified line from the lines specified as the assumptions of that line,
        and updating justification line numbers specified throughout the proof
        to maintain the validity of the proof. The set of allowed inference
        rules in the returned proof is the union of the rules allowed in the two
        given proofs, but the "lemma" rule that is used in the specified line in
        `main_proof` is no longer used in the corresponding lines in the
        returned proof (and thus, this "lemma" rule is used one less time in the
        returned proof than in `main_proof`).
    """
    assert main_proof.is_valid()
    assert line_number < len(main_proof.lines)
    assert main_proof.lines[line_number].rule == lemma_proof.statement
    assert lemma_proof.is_valid()
    # Task 5.2a

    # --- 1. Adding the Lemma's Lines ---

    line = main_proof.lines[line_number]
    # We start by figuring out the new lines needed to replace the Lemma line.
    # We'll need a proof specialization for this.
    specialized_proof = prove_specialization(lemma_proof, main_proof.rule_for_line(line_number))
    # Now when we put everything together we just need the line number indices to work out.
    # We can start by adding the lines not affected by the change.
    newLines = [main_proof.lines[i] for i in range(line_number)]

    # Now we add the new lines, but we want to keep track of how many lines went unaffected.
    numberOfUnaffectedLines = len(newLines)

    # Let's go ahead and jump into the main loop, adding lines from the Lemma's proof.
    for specializedProofLineNumber in range(len(specialized_proof.lines)):
        specializedProofLine = specialized_proof.lines[specializedProofLineNumber]
        # If a line in the Lemma proof had no rule, then it was an assumption of the Lemma.
        # This means one of our previous lines will be that assumption, so we want to
        # reference it instead of adding it with no rule at all. 
        if specializedProofLine.rule is not None:
            # Now we have a line that references other lines in the Lemma proof. So we need
            # to find where in the proof we stated the formula that we're looking for.
            newAssumptions = []
            # We go through our line's assumptions one at a time.
            for assumption in specializedProofLine.assumptions:
                # And look through each previous line
                for previousLineNumber in range(len(newLines)):
                    previousLine = newLines[previousLineNumber]
                    # to check if it has the right formula.
                    if previousLine.formula == specialized_proof.lines[assumption].formula:
                        # If it does, we can reference it and stop looking.
                        newAssumptions.append(previousLineNumber)
                        break
            # Once all of a line's assumptions have been changed, we can add it.
            newLines.append(Proof.Line(specializedProofLine.formula, specializedProofLine.rule, newAssumptions))
    
    # --- 2. Adding the Remaining Lines ---

    # Now we do the same thing, but with the old lines that came after the Lemma line.
    # We could take the same approach as in (1), where we loop through every previous line
    # to look for the right formula. For the sake of efficiency, however, we can utilize
    # the fact that a rule either was unaffected or was merely shifted in its line number
    # by the number of added lines. In fact, I tried to do this for the main loop in (1), but
    # ran into issues. 
    
    indexShift = len(newLines) - numberOfUnaffectedLines - 1

    for oldLineNumber in range(line_number + 1, len(main_proof.lines)):
        oldLine = main_proof.lines[oldLineNumber]
        if oldLine.rule is None:
            newLines.append(oldLine)
        else:
            newAssumptions = []
            for assumption in oldLine.assumptions:
                # We check if our assumption index was affected
                # (we get >= instead of > because of 0-index)
                if assumption >= numberOfUnaffectedLines: 
                    # If our assumption was affected, we shift it up.
                    newAssumptions.append(assumption + indexShift)
                else: 
                    # Otherwise, it stays the same.
                    newAssumptions.append(assumption)
            newLines.append(Proof.Line(oldLine.formula, oldLine.rule, newAssumptions))
    
    # Now, the lines are ready for our new proof.

    # --- 3. Finishing Up ---

    # We end by updating the rules of our new proof.
    # As explained in the textbook, we need the same rules as the main proof and Lemma proof.
    newRules = [rule for rule in main_proof.rules]
    # Then we can add the Lemma's rules
    for rule in lemma_proof.rules:
        newRules.append(rule)
    
    # And now the rules are ready for our new proof! We just have to put it all together.
    return Proof(main_proof.statement, newRules, newLines)

def inline_proof(main_proof: Proof, lemma_proof: Proof) -> Proof:
    """Inlines the given proof of a "lemma" inference rule into the given proof
    that uses that "lemma" rule, eliminating all usages of (any specializations
    of) that "lemma" rule in the latter proof.

    Parameters:
        main_proof: valid proof to inline into.
        lemma_proof: valid proof of one of the allowed inference rules of
            `main_proof`.

    Returns:
        A valid proof obtained from `main_proof` by inlining (an appropriate
        specialization of) `lemma_proof` in lieu of each line that specifies the
        "lemma" inference rule proved by `lemma_proof` as its justification. The
        set of allowed inference rules in the returned proof is the union of the
        rules allowed in the two given proofs but without the "lemma" rule
        proved by `lemma_proof`.
    """
    assert main_proof.is_valid()
    assert lemma_proof.is_valid()
    # Task 5.2b
    
    # First we figure out how many times we use the Lemma.
    lemma_use_count = 0
    for line_number in range(len(main_proof.lines)):
        if main_proof.lines[line_number].rule == lemma_proof.statement:
            lemma_use_count += 1
    # Then we start building our new proof. I do this one use of the Lemma at a time,
    # storing the progress in the return_proof variable.
    return_proof = main_proof

    # We'll go through the proof one use of the lemma at a time, replacing that line, and
    # then doing it again. A while loop works well in this context. 
    while lemma_use_count > 0:
        for line_number in range(len(return_proof.lines)):
            if return_proof.lines[line_number].rule == lemma_proof.statement:
                # If we find a line that uses the lemma, we replace it, updating our return_proof,
                # and then we start over. This is to avoid the potential problem of changing our object
                # while we're in the process of looping through it.
                return_proof = _inline_proof_once(return_proof, line_number, lemma_proof)
                break
        # Then we tell Python we've removed one use of the Lemma, and restart the while loop if need-be.
        lemma_use_count += -1
    # At the end, we just have to fix the rules being used.
    return_proof_rules = set(main_proof.rules).union(set(lemma_proof.rules))
    return_proof_rules.remove(lemma_proof.statement)
    return Proof(return_proof.statement, return_proof_rules, return_proof.lines)