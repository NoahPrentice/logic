# This file is part of the materials accompanying the book
# "Mathematical Logic through Python" by Gonczarowski and Nisan,
# Cambridge University Press. Book site: www.LogicThruPython.org
# (c) Yannai A. Gonczarowski and Noam Nisan, 2017-2022
# File name: predicates/prover.py

"""Axiomatic schemas of Predicate Logic, and useful proof creation maneuvers
using them."""

from typing import AbstractSet, Collection, FrozenSet, List, Mapping, \
                   Sequence, Tuple, Union

from logic_utils import fresh_variable_name_generator, is_z_and_number

from predicates.syntax import *
from predicates.proofs import *

class Prover:
    """A class for gradually creating a predicate-logic proof from given
    assumptions as well as from the six axioms (`AXIOMS`) Universal
    Instantiation (`UI`), Existential Introduction (`EI`), Universal
    Simplification (`US`), Existential Simplification (`ES`), Reflexivity
    (`RX`), and Meaning of Equality (`ME`).

    Attributes:
        _assumptions (`~typing.FrozenSet`\\[`~predicates.proofs.Schema`]): the
            assumptions/axioms of the proof being created, which include
            `AXIOMS`.
        _lines (`~typing.List`\\[`~predicates.proofs.Proof.Line`]): the lines so
            far of the proof being created.
        _print_as_proof_forms (`bool`): flag specifying whether the proof being
            created is being printed in real time as it forms.
    """
    _assumptions: FrozenSet[Schema]
    _lines: List[Proof.Line]
    _print_as_proof_forms: bool

    #: Axiom schema of universal instantiation
    UI = Schema(Formula.parse('(Ax[R(x)]->R(c))'), {'R', 'x', 'c'})
    #: Axiom schema of existential introduction
    EI = Schema(Formula.parse('(R(c)->Ex[R(x)])'), {'R', 'x', 'c'})
    #: Axiom schema of universal simplification
    US = Schema(Formula.parse('(Ax[(Q()->R(x))]->(Q()->Ax[R(x)]))'),
                {'Q', 'R', 'x'})
    #: Axiom schema of existential simplification
    ES = Schema(Formula.parse('((Ax[(R(x)->Q())]&Ex[R(x)])->Q())'),
                {'Q', 'R', 'x'})
    #: Axiom schema of reflexivity
    RX = Schema(Formula.parse('c=c'), {'c'})
    #: Axiom schema of meaning of equality
    ME = Schema(Formula.parse('(c=d->(R(c)->R(d)))'), {'R', 'c', 'd'})
    #: Axiomatic system for Predicate Logic, consisting of `UI`, `EI`, `US`,
    #: `ES`, `RX`, and `ME`.
    AXIOMS = frozenset({UI, EI, US, ES, RX, ME})

    def __init__(self, assumptions: Collection[Union[Schema, Formula, str]],
                 print_as_proof_forms: bool=False):
        """Initializes a `Prover` from its assumptions/additional axioms. The
        proof created by the prover initially has no lines.

        Parameters:
            assumptions: the assumptions/axioms beyond `AXIOMS` for the proof
                to be created, each specified as either a schema, a formula that
                constitutes the unique instance of the assumption, or the string
                representation of the unique instance of the assumption.
            print_as_proof_forms: flag specifying whether the proof to be
                created is to be printed in real time as it forms.
        """
        self._assumptions = \
            Prover.AXIOMS.union(
                {assumption if isinstance(assumption, Schema)
                 else Schema(assumption) if isinstance(assumption, Formula)
                 else Schema(Formula.parse(assumption))
                 for assumption in assumptions})
        self._lines = []
        self._print_as_proof_forms = print_as_proof_forms
        if self._print_as_proof_forms:
            print('Proving from assumptions/axioms:\n'
                  '  AXIOMS')
            for assumption in self._assumptions - Prover.AXIOMS:
                  print('  ' + str(assumption))
            print('Lines:')

    def qed(self) -> Proof:
        """Concludes the proof created by the current prover.

        Returns:
            A valid proof, from the assumptions of the current prover as well as
            `AXIOMS`', of the formula justified by the last line appended to the
            current prover.
        """
        conclusion = self._lines[-1].formula
        if self._print_as_proof_forms:
            print('Conclusion:', str(conclusion) + '. QED\n')
        return Proof(self._assumptions, conclusion, self._lines)

    def _add_line(self, line: Proof.Line) -> int:
        """Appends to the proof being created by the current prover the given
        validly justified line.

        Parameters:
            line: proof line that is validly justified when appended to the
                lines of the proof being created by the current prover.

        Returns:
            The line number of the appended line in the proof being created by
            the current prover.
        """
        line_number = len(self._lines)
        self._lines.append(line)
        assert line.is_valid(self._assumptions, self._lines, line_number)
        if self._print_as_proof_forms:
            print(('%3d) ' % line_number) + str(line.formula))
        return line_number

    def add_instantiated_assumption(self, instance: Union[Formula, str],
                                    assumption: Schema,
                                    instantiation_map: InstantiationMap) -> \
            int:
        """Appends to the proof being created by the current prover a line that
        validly justifies the given instance of the given assumptions/axioms of
        the current prover.

        Parameters:
            instance: instance to be appended, specified as either a formula or
                its string representation.
            assumption: assumption/axiom of the current prover that instantiates
                the given instance.
            instantiation_map: mapping instantiating the given instance from the
                given assumption/axiom. Each value of this map may also be given
                as a string representation (instead of a term or a formula).

        Returns:
            The line number of the newly appended line that justifies the given
            instance in the proof being created by the current prover.
        """
        if isinstance(instance, str):
            instance = Formula.parse(instance)
        instantiation_map = dict(instantiation_map)
        for key in instantiation_map:
            value = instantiation_map[key]
            if is_variable(key):
                assert is_variable(value)
            elif is_constant(key):
                if isinstance(value, str):
                    instantiation_map[key] = Term.parse(value)
                else:
                    assert isinstance(value, Term)
            else:
                assert is_relation(key)
                if isinstance(value, str):
                    instantiation_map[key] = Formula.parse(value)
                else:
                    assert isinstance(value, Formula)
        return self._add_line(Proof.AssumptionLine(instance, assumption,
                                                   instantiation_map))
        
    def add_assumption(self, unique_instance: Union[Formula, str]) -> int:
        """Appends to the proof being created by the current prover a line that
        validly justifies the unique instance of one of the assumptions/axioms
        of the current prover.

        Parameters:
            unique_instance: unique instance of one of the assumptions/axioms
                of the current prover, to be appended, specified as either a
                formula or its string representation.

        Returns:
            The line number of the newly appended line that justifies the given
            instance in the proof being created by the current prover.
        """
        if isinstance(unique_instance, str):
            unique_instance = Formula.parse(unique_instance)
        return self.add_instantiated_assumption(unique_instance,
                                                Schema(unique_instance), {})

    def add_tautology(self, tautology: Union[Formula, str]) -> int:
        """Appends to the proof being created by the current prover a line that
        validly justifies the given tautology.

        Parameters:
            tautology: tautology to be appended, specified as either a formula
                or its string representation.

        Returns:
            The line number of the newly appended line that justifies the given
            tautology in the proof being created by the current prover.
        """
        if isinstance(tautology, str):
            tautology = Formula.parse(tautology)
        return self._add_line(Proof.TautologyLine(tautology))

    def add_mp(self, consequent: Union[Formula, str],
               antecedent_line_number: int, conditional_line_number: int) -> \
            int:
        """Appends to the proof being created by the current prover a line that
        validly justifies the given consequent of an MP inference from the
        specified already existing lines of the proof.

        Parameters:
            consequent: consequent of MP inference to be appended, specified as
                either a formula or its string representation.
            antecedent_line_number: line number in the proof of the antecedent
                of the MP inference that derives the given formula.
            conditional_line_number: line number in the proof of the conditional
                of the MP inference that derives the given formula.

        Returns:
            The line number of the newly appended line that justifies the given
            formula in the proof being created by the current prover.
        """
        if isinstance(consequent, str):
            consequent = Formula.parse(consequent)
        return self._add_line(Proof.MPLine(consequent, antecedent_line_number,
                                           conditional_line_number))

    def add_ug(self, quantified: Union[Formula, str],
               nonquantified_line_number: int) -> int:
        """Appends to the proof being created by the current prover a line that
        validly justifies the given universally quantified formula, the
        statement quantified by which is the specified already existing line of
        the proof.

        Parameters:
            quantified: universally quantified formula to be appended, specified
                as either a formula or its string representation.
            nonquantified_line_number: line number in the proof of the statement
                quantified by the given formula.

        Returns:
            The line number of the newly appended line that justifies the given
            formula in the proof being created by the current prover.
        """
        if isinstance(quantified, str):
            quantified = Formula.parse(quantified)
        return self._add_line(Proof.UGLine(quantified,
                                           nonquantified_line_number))

    def add_proof(self, conclusion: Union[Formula, str], proof: Proof) -> int:
        """Appends to the proof being created by the current prover a validly
        justified inlined version of the given proof of the given conclusion,
        the last line of which validly justifies the given formula.

        Parameters:
            conclusion: conclusion of the sequence of lines to be appended,
                specified as either a formula or its string representation.
            proof: valid proof of the given formula from a subset of the
                assumptions/axioms of the current prover.

        Returns:
            The line number of the newly appended line that justifies the given
            formula in the proof being created by the current prover.
        """
        if isinstance(conclusion, str):
            conclusion = Formula.parse(conclusion)
        assert proof.conclusion == conclusion
        assert proof.assumptions.issubset(self._assumptions)
        line_shift = len(self._lines)
        for line in proof.lines:
            if type(line) in {Proof.AssumptionLine, Proof.TautologyLine}:
                self._add_line(line)
            elif isinstance(line, Proof.MPLine):
                self.add_mp(line.formula,
                            line.antecedent_line_number + line_shift,
                            line.conditional_line_number + line_shift)
            else:
                assert isinstance(line, Proof.UGLine)
                self.add_ug(line.formula,
                            line.nonquantified_line_number + line_shift)
        line_number = len(self._lines) - 1
        assert self._lines[line_number].formula == conclusion
        return line_number                

    def add_universal_instantiation(self, instantiation: Union[Formula, str],
                                    line_number: int, term: Union[Term, str]) \
            -> int:
        """Appends to the proof being created by the current prover a sequence
        of validly justified lines, the last of which validly justifies the
        given formula, which is the result of substituting a term for the
        outermost universally quantified variable name in the formula in the
        specified already existing line of the proof.

        Parameters:
            instantiation: conclusion of the sequence of lines to be appended,
                specified as either a formula or its string representation.
            line_number: line number in the proof of a universally quantified
                formula of the form ``'A``\ `x`\ ``[``\ `statement`\ ``]'``.
            term: term, specified as either a term or its string representation,
                that when substituted into the free occurrences of `x` in
                `statement` yields the given formula.

        Returns:
            The line number of the newly appended line that justifies the given
            formula in the proof being created by the current prover.

        Examples:
            If Line `line_number` contains the formula
            ``'Ay[Az[f(x,y)=g(z,y)]]'`` and `term` is ``'h(w)'``, then
            `instantiation` should be ``'Az[f(x,h(w))=g(z,h(w))]'``.
        """
        if isinstance(instantiation, str):
            instantiation = Formula.parse(instantiation)
        assert line_number < len(self._lines)
        quantified = self._lines[line_number].formula
        assert quantified.root == 'A'
        if isinstance(term, str):
            term = Term.parse(term)
        assert instantiation == \
               quantified.statement.substitute({quantified.variable: term})
        # Task 10.1
        
        # At self._lines[line_number] is a Line whose formula has the form Ax[phi(x)]. We need to
        # use the axiom UI to deduce the instantiated assumption (Ax[phi(x)]->phi(term)). Then we use
        # MP on these two lines to deduce phi(term).

        # First we instantiate UI
        universal_formula = self._lines[line_number].formula # Ax[phi(x)]
        template_universal_statement =\
            universal_formula.statement.substitute({universal_formula.variable: Term('_')}, {}) # phi(_)
        ui_formula = Formula('->', universal_formula, instantiation) # (Ax[phi(x)]->phi(term))
        instantiation_map =\
              {'c': term, 'x': universal_formula.variable, 'R': template_universal_statement} 
        ui_line_number = self.add_instantiated_assumption(ui_formula, Prover.UI, instantiation_map)

        # Then we use MP
        instantiation_line_number = self.add_mp(instantiation, line_number, ui_line_number)
        return instantiation_line_number


    def add_tautological_implication(self, implication: Union[Formula, str],
                                     line_numbers: AbstractSet[int]) -> int:
        """Appends to the proof being created by the current prover a sequence
        of validly justified lines, the last of which validly justifies the
        given formula, which is a tautological implication of the formulas in
        the specified already existing lines of the proof.

        Parameters:
            implication: conclusion of the sequence of lines to be appended,
                specified as either a formula or its string representation.
            line_numbers: line numbers in the proof of formulas of which
                `implication` is a tautological implication.

        Returns:
            The line number of the newly appended line that justifies the given
            formula in the proof being created by the current prover.
        """
        if isinstance(implication, str):
            implication = Formula.parse(implication)
        for line_number in line_numbers:
            assert line_number < len(self._lines)
        # Task 10.2

        # We'll first build the formula that captures the tautological implication 'A implies I'
        # where 'I' is the given formula "implication" and A is the set of formulas at the given
        # line numbers.
        line_numbers = list(line_numbers) 
        line_numbers.sort(reverse=True) # Put the line_numbers in descending order
        formula = implication
        for line_number in line_numbers:
            formula = Formula('->', self._lines[line_number].formula, formula)

        # This is then added as a tautology, and saved as the first conditional line number. Then
        # we use MP until we run out of formulas in A.
        conditional_line_number = self.add_tautology(formula)
        line_numbers.sort() # Put the line_numbers in ascending order
        for line_number in line_numbers:
            new_conditional_line_number = self.add_mp(formula.second, line_number, conditional_line_number)
            conditional_line_number = new_conditional_line_number
            formula = formula.second
        return len(self._lines) - 1

    def add_existential_derivation(self, consequent: Union[Formula, str],
                                   line_number1: int, line_number2: int) -> int:
        """Appends to the proof being created by the current prover a sequence
        of validly justified lines, the last of which validly justifies the
        given formula, which is the consequent of the formula in the second
        specified already existing line of the proof, whose antecedent is
        existentially quantified by the formula in the first specified already
        existing line of the proof.

        Parameters:
            consequent: conclusion of the sequence of lines to be appended,
                specified as either a formula or its string representation.
            line_number1: line number in the proof of an existentially
                quantified formula of the form
                ``'E``\ `x`\ ``[``\ `antecedent(x)`\ ``]'``, where `x`
                is a variable name that may have free occurrences in
                `antecedent(x)` but has no free occurrences in `consequent`.
            line_number2: line number in the proof of the formula
                ``'(``\ `antecedent(x)`\\ ``->``\ `consequent`\ ``)'``.

        Returns:
            The line number of the newly appended line that justifies the given
            formula in the proof being created by the current prover.
        """
        if isinstance(consequent, str):
            consequent = Formula.parse(consequent)
        assert line_number1 < len(self._lines)
        quantified = self._lines[line_number1].formula
        assert quantified.root == 'E'
        assert quantified.variable not in consequent.free_variables()
        assert line_number2 < len(self._lines)
        conditional = self._lines[line_number2].formula
        assert conditional == Formula('->', quantified.statement, consequent)
        # Task 10.3

        # First we use UG on (R(x)->Q()), the formula at line_number2
        variable = quantified.variable
        ug_formula = Formula('A', variable, conditional)
        ug_line_number = self.add_ug(ug_formula, line_number2)

        # Next we instantiate ES = ((Ax[R(x)->Q()]&Ex[R(x)])->Q())
        # and infer consequent from this as a tautological implication
        instantiation_map = {'x': variable, 
                             'R': quantified.statement.substitute({variable: Term('_')}), 
                             'Q': consequent}
        es_line_number = self.add_instantiated_assumption(Prover.ES.instantiate(instantiation_map), Prover.ES, instantiation_map)
        consequent_line_number = self.add_tautological_implication(consequent, {ug_line_number, line_number1, es_line_number})
        return consequent_line_number

    def add_flipped_equality(self, flipped: Union[Formula, str],
                             line_number: int) -> int:
        """Appends to the proof being created by the current prover a sequence
        of validly justified lines, the last of which validly justifies the
        given equality, which is the result of exchanging the two sides of the
        equality in the specified already existing line of the proof.

        Parameters:
            flipped: conclusion of the sequence of lines to be appended,
                specified as either a formula or its string representation.
            line_number: line number in the proof of an equality that is the
                same as the given equality, except that the two sides of the
                equality are exchanged.

        Returns:
            The line number of the newly appended line that justifies the given
            equality in the proof being created by the current prover.
        """
        if isinstance(flipped, str):
            flipped = Formula.parse(flipped)
        assert is_equality(flipped.root)
        assert line_number < len(self._lines)
        equality = self._lines[line_number].formula
        assert equality == Formula('=', [flipped.arguments[1],
                                         flipped.arguments[0]])
        # Task 10.6

        # Want to derive d=c given c=d. Start by adding c=c.
        d = flipped.arguments[0]
        c = flipped.arguments[1]
        rx_line_number = self.add_instantiated_assumption(
            Prover.RX.instantiate({'c':c}), Prover.RX, {'c':c})
        
        # Add (c=d->(c=c->d=c))
        me_instantiation_map = {'c':c, 'd':d, 'R':Formula('=', [Term('_'), c])}
        me_line_number = self.add_instantiated_assumption(
            Prover.ME.instantiate(me_instantiation_map), Prover.ME, me_instantiation_map) 
        # Use MP twice
        mp_line_number = self.add_mp(
            self._lines[me_line_number].formula.second, line_number, me_line_number) # (c=c->d=c)
        return self.add_mp(self._lines[mp_line_number].formula.second, rx_line_number, mp_line_number) # d=c

    def add_free_instantiation(self, instantiation: Union[Formula, str],
                               line_number: int,
                               substitution_map:
                               Mapping[str, Union[Term, str]]) -> int:
        """Appends to the proof being created by the current prover a sequence
        of validly justified lines, the last of which validly justifies the
        given formula, which is the result of substituting terms for free
        variable names in the formula in the specified already existing line of
        the proof.

        Parameters:
            instantiation: conclusion of the sequence of lines to be appended,
                specified as either a formula or its string representation.
            line_number: line number in the proof of a formula with free
                variable names, which contains no variable names that are ``z``
                followed by a number.
            substitution_map: mapping from free variable names of the formula
                with the given line number to terms that contain no variable
                names that are ``z`` followed by a number, to be substituted for
                them to obtain the given formula. Each value of this map may
                also be given as a string representation (instead of a term).
                Only variable name occurrences originating in the formula with
                the given line number are substituted (i.e., variable names
                originating in one of the specified substitutions are not
                subjected to additional substitutions).

        Returns:
            The line number of the newly appended line that justifies the given
            formula in the proof being created by the current prover.
            
        Examples:
            If Line `line_number` contains the formula
            ``'(z=5&Az[f(x,y)=g(z,y)])'`` and `substitution_map` is
            ``{'y': 'h(w)', 'z': 'y'}``, then `instantiation` should be
            ``'(y=5&Az[f(x,h(w))=g(z,h(w))])'``.
        """
        if isinstance(instantiation, str):
            instantiation = Formula.parse(instantiation)
        substitution_map = dict(substitution_map)
        for variable in substitution_map:
            assert is_variable(variable)
            term = substitution_map[variable]
            if isinstance(term, str):
                substitution_map[variable] = term = Term.parse(term)
            for variable in term.variables():
                assert not is_z_and_number(variable)
        assert line_number < len(self._lines)
        original = self._lines[line_number].formula
        for variable in original.variables():
            assert not is_z_and_number(variable)
        assert original.free_variables().issuperset(substitution_map.keys())
        assert instantiation == original.substitute(substitution_map)
        # Task 10.7
        # Formula original is similar to plus(x,y)=plus(y,x). We turn this first
        # into an intermediate formula with different variables than those that
        # need to be replaced.
        free_vars = list(original.free_variables().intersection(substitution_map))
        new_vars = {var: next(fresh_variable_name_generator) for var in free_vars}
        new_substitution_map = {new_vars[var]:substitution_map[var] for var in free_vars}

        last_line_number = line_number
        for var in free_vars:
            # Generalize, e.g., Ax[plus(x,y)=plus(y,x)]
            non_quantified = self._lines[last_line_number].formula
            quantified = Formula('A', var, non_quantified)
            last_line_number = self.add_ug(quantified, last_line_number)
            # Instantiate with new variable, e.g., plus(z1,y)=plus(y,z1)
            last_line_number = self.add_universal_instantiation(
                quantified.statement.substitute({var:Term(new_vars[var])}, {}), 
                last_line_number, 
                new_vars[var])
        
        # Now we have the intermediate formula, e.g., plus(z1,z2)=plus(z2,z1) which we substitute as desired.
        for var in new_substitution_map:
            # Generalize, e.g., Az1[plus(z1,z2)=plus(z2,z1)]
            non_quantified = self._lines[last_line_number].formula
            quantified = Formula('A', var, non_quantified)
            last_line_number = self.add_ug(quantified, last_line_number)
            # Instantiate as desired, e.g., plus(f(y),z2)=plus(z2,f(y))
            last_line_number = self.add_universal_instantiation(
                quantified.statement.substitute({var:new_substitution_map[var]}, {}), 
                last_line_number, 
                new_substitution_map[var])
        return last_line_number

    def add_substituted_equality(self, substituted: Union[Formula, str],
                                 line_number: int,
                                 parametrized_term: Union[Term, str]) -> \
            int:
        """Appends to the proof being created by the current prover a sequence
        of validly justified lines, the last of which validly justifies the
        given equality, whose two sides are the results of substituting the two
        respective sides of the equality in the specified already existing line
        of the proof into the given parametrized term.

        Parameters:
            substituted: conclusion of the sequence of lines to be appended,
                specified as either a formula or its string representation.
            line_number: line number in the proof of an equality.
            parametrized_term: term parametrized by the constant name ``'_'``,
                specified as either a term or its string representation, such
                that substituting each of the two sides of the equality with the
                given line number into this parametrized term respectively
                yields each of the two sides of the given equality.

        Returns:
            The line number of the newly appended line that justifies the given
            equality in the proof being created by the current prover.

        Examples:
            If Line `line_number` contains the formula ``'g(x)=h(y)'`` and
            `parametrized_term` is ``'_+7'``, then `substituted` should be
            ``'g(x)+7=h(y)+7'``.
        """
        if isinstance(substituted, str):
            substituted = Formula.parse(substituted)
        assert is_equality(substituted.root)
        assert line_number < len(self._lines)
        equality = self._lines[line_number].formula
        assert is_equality(equality.root)
        if isinstance(parametrized_term, str):
            parametrized_term = Term.parse(parametrized_term)
        assert substituted == \
               Formula('=', [parametrized_term.substitute(
                                 {'_': equality.arguments[0]}),
                             parametrized_term.substitute(
                                 {'_': equality.arguments[1]})])
        # Task 10.8
        # Equality is a formula of the form c=d. First we instantiate ME to get
        # (c=d->(phi(c)=phi(c)->phi(c)=phi(d)).
        c = equality.arguments[0]
        d = equality.arguments[1]
        phi_c = parametrized_term.substitute({'_':c}, {}) # phi(c)
        phi_d = parametrized_term.substitute({'_':d}, {}) # phi(d)
        me_R = Formula('=', [phi_c, parametrized_term]) # R(_) = phi(c)=phi(_)
        me_instantiation_map = {'c':c, 'd':d, 'R':me_R}
        me_line_number = self.add_instantiated_assumption(
            Prover.ME.instantiate(me_instantiation_map), Prover.ME, me_instantiation_map)

        # Now use MP twice, using an instantiation of RX (phi(c)=phi(c)).
        mp_line_number = self.add_mp(
            self._lines[me_line_number].formula.second, line_number, me_line_number)
        antecedent_line_number = self.add_instantiated_assumption(
            Prover.RX.instantiate({'c':phi_c}), Prover.RX, {'c':phi_c})
        return self.add_mp(
            self._lines[mp_line_number].formula.second, antecedent_line_number, mp_line_number)

    def _add_chaining_of_two_equalities(self, line_number1: int,
                                        line_number2: int) -> int:
        """Appends to the proof being created by the current prover a sequence
        of validly justified lines, the last of which validly justifies an
        equality that is the result of chaining together the two equalities in
        the specified already existing lines of the proof.

        Parameters:
            line_number1: line number in the proof of an equality of the form
                ``'``\ `first`\ ``=``\ `second`\ ``'``.
            line_number2: line number in the proof of an equality of the form
                ``'``\ `second`\ ``=``\ `third`\ ``'``.

        Returns:
            The line number of the newly appended line that justifies the
            equality ``'``\ `first`\ ``=``\ `third`\ ``'`` in the proof being
            created by the current prover.

        Examples:
            If Line `line_number1` contains the formula ``'a=b'`` and Line
            `line_number2` contains the formula ``'b=f(b)'``, then the last
            appended line will contain the formula ``'a=f(b)'``.
        """
        assert line_number1 < len(self._lines)
        equality1 = self._lines[line_number1].formula
        assert is_equality(equality1.root)
        assert line_number2 < len(self._lines)
        equality2 = self._lines[line_number2].formula
        assert is_equality(equality2.root)
        assert equality1.arguments[1] == equality2.arguments[0]
        # Task 10.9a

        # If equality1 is x=y and equality2 is y=z, then we first deduce y=x.
        x = equality1.arguments[0]
        y = equality1.arguments[1]
        z = equality2.arguments[1]
        flipped_line_number = self.add_flipped_equality(
            Formula('=', [y, x]), line_number1)
        
        # Then we instantiate ME to get (y=x->(y=z->x=z)) and use MP twice.
        me_instantiation_map = {'c':y, 'd':x, 'R':Formula('=', [Term('_'), z])}
        me_line_number = self.add_instantiated_assumption(
            Prover.ME.instantiate(me_instantiation_map), Prover.ME, me_instantiation_map)
        mp_line_number = self.add_mp(
            self._lines[me_line_number].formula.second, flipped_line_number, me_line_number)
        return self.add_mp(self._lines[mp_line_number].formula.second, line_number2, mp_line_number)
        


    def add_chained_equality(self, chained: Union[Formula, str],
                             line_numbers: Sequence[int]) -> int:
        """Appends to the proof being created by the current prover a sequence
        of validly justified lines, the last of which validly justifies the
        given equality, which is the result of chaining together the equalities
        in the specified already existing lines of the proof.

        Parameters:
            chained: conclusion of the sequence of lines to be appended,
                specified as either a formula or its string representation,
                of the form ``'``\ `first`\ ``=``\ `last`\ ``'``.
            line_numbers: line numbers in the proof of equalities of the form
                ``'``\ `first`\ ``=``\ `second`\ ``'``,
                ``'``\ `second`\ ``=``\ `third`\ ``'``, ...,
                ``'``\ `before_last`\ ``=``\ `last`\ ``'``, i.e., the left-hand
                side of the first equality is the left-hand side of the given
                equality, the right-hand of each equality (except for the last)
                is the left-hand side of the next equality, and the right-hand
                side of the last equality is the right-hand side of the given
                equality.

        Returns:
            The line number of the newly appended line that justifies the given
            equality in the proof being created by the current prover.

            Examples:
            If `line_numbers` is ``[7,3,9]``, Line 7 contains the formula
            ``'a=b'``, Line 3 contains the formula ``'b=f(b)'``, and Line 9
            contains the formula ``'f(b)=0'``, then `chained` should be
            ``'a=0'``.
        """
        if isinstance(chained, str):
            chained = Formula.parse(chained)
        assert is_equality(chained.root)
        assert len(line_numbers) >= 2
        current_term = chained.arguments[0]
        for line_number in line_numbers:
            assert line_number < len(self._lines)
            equality = self._lines[line_number].formula
            assert is_equality(equality.root)
            assert equality.arguments[0] == current_term
            current_term = equality.arguments[1]
        assert chained.arguments[1] == current_term
        # Task 10.9b
        # Because our chaining of the first two equalities has a different structure than
        # the rest of them, we use them first.
        recent_equality = self._add_chaining_of_two_equalities(line_numbers[0], line_numbers[1])
        # For the rest, we just loop through the equalities in order. We will have just deduced
        # (at recent_equality) something like x=y, and the next equality given in line_numbers
        # will have something like y=z. So we just use 10.9a and update recent_equality.
        for i in range(2, len(line_numbers)):
            next_equality = line_numbers[i]
            recent_equality = self._add_chaining_of_two_equalities(recent_equality, next_equality)
        return recent_equality

    def cancel_in_group(self, line_number) -> int:
        """
        Works only in proofs where the group axioms are assumed. Takes a line
        of the form plus(a,c)=a and adds a sequence of justified lines, the
        last of which has formula c=0.
        """
        prover = self
        equality = self._lines[line_number].formula
        a = equality.arguments[1]
        c = equality.arguments[0].arguments[1]
        map = {'a':a,'c':c}
        step2 = prover.add_assumption('plus(minus(x),x)=0')
        step3 = prover.add_assumption('plus(plus(x,y),z)=plus(x,plus(y,z))')
        step4 = prover.add_assumption('plus(0,x)=x')

        # We take the formula in step 1, add minus(a) to both sides (by substitution), and then cancel the a's.
        step5 = prover.add_substituted_equality(
            Formula.parse('plus(minus(a),plus(a,c))=plus(minus(a),a)').substitute(map, {}), 
            line_number, 
            Term.parse('plus(minus(a),_)').substitute(map, {}))
        step6 = prover.add_free_instantiation(Formula.parse('plus(minus(a),a)=0').substitute(map, {}), step2, {'x':a})
        step7 = prover._add_chaining_of_two_equalities(step5, step6) # plus(minus(a),plus(a,c))=0

        # At this point, we've cancelled the a on the right to get 0, but we have to do the left side.
        step8 = prover.add_free_instantiation(
            Formula.parse('plus(plus(minus(a),a),c)=plus(minus(a),plus(a,c))').substitute(map, {}),
            step3, 
            {'x':Term.parse('minus(a)').substitute(map, {}),'y':a,'z':c})
        step9 = prover._add_chaining_of_two_equalities(step8, step7) # plus(plus(minus(a),a),c)=0
        step10 = prover.add_substituted_equality(
            Formula.parse('plus(plus(minus(a),a),c)=plus(0,c)').substitute(map, {}), 
            step6, 
            Term.parse('plus(_,c)').substitute(map, {}))
        step11 = prover.add_flipped_equality(
            Formula.parse('plus(0,c)=plus(plus(minus(a),a),c)').substitute(map, {}), 
            step10)
        step12 = prover._add_chaining_of_two_equalities(step11, step9) # plus(0,c)=0
        step13 = prover.add_free_instantiation(
            Formula.parse('plus(0,c)=c').substitute(map, {}), 
            step4, 
            {'x':c})
        step14 = prover.add_flipped_equality(
            Formula.parse('c=plus(0,c)').substitute(map, {}), 
            step13)
        return prover._add_chaining_of_two_equalities(step14, step12) # c=0