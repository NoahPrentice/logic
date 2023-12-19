# This file is part of the materials accompanying the book
# "Mathematical Logic through Python" by Gonczarowski and Nisan,
# Cambridge University Press. Book site: www.LogicThruPython.org
# (c) Yannai A. Gonczarowski and Noam Nisan, 2017-2022
# File name: propositions/deduction.py

"""Useful proof manipulation maneuvers in Propositional Logic."""

from propositions.syntax import *
from propositions.proofs import *
from propositions.axiomatic_systems import *

def prove_corollary(antecedent_proof: Proof, consequent: Formula,
                    conditional: InferenceRule) -> Proof:
    """Converts the given proof of a formula `antecedent` to a proof of the
    given formula `consequent` by using the given assumptionless inference rule
    of which ``'(``\ `antecedent`\ ``->``\ `consequent`\ ``)'`` is a
    specialization.

    Parameters:
        antecedent_proof: valid proof of `antecedent`.
        consequent: formula to prove.
        conditional: assumptionless inference rule of which the assumptionless
            inference rule with conclusion
            ``'(``\ `antecedent`\ ``->``\ `consequent`\ ``)'`` is a
            specialization.

    Returns:
        A valid proof of `consequent` from the same assumptions as the given
        proof, via the same inference rules as the given proof and in addition
        `~propositions.axiomatic_systems.MP` and `conditional`.
    """
    assert antecedent_proof.is_valid()
    assert InferenceRule([],
                         Formula('->', antecedent_proof.statement.conclusion,
                                 consequent)).is_specialization_of(conditional)
    # Task 5.3a
    # Copy the proof of the antecedent.
    consequent_proof_lines = list(antecedent_proof.lines)
    # Then add the instantiated conditional we need. No assumptions required.
    consequent_proof_lines.append(Proof.Line(Formula('->', antecedent_proof.statement.conclusion,
                                 consequent), conditional, []))
    
    # # Then we add a line to our proof concluding our consequent using modus ponens. The two assumptions are
    # the antecedent and the instantiated conditional, the penultimate and ultimate lines.
    consequent_proof_lines.append(Proof.Line(consequent, MP, [len(consequent_proof_lines)-2, len(consequent_proof_lines)-1]))

    # Now we construct our returned proof:
    # (1) Our statement has the same assumptions as the antecedent proof, but it concludes the consequent.
    # (2) Our allowed rules are the antecedent proof's rules, plus modus ponens and the conditional.
    # (3) The lines of the proof are the ones constructed above.
    return Proof(InferenceRule(antecedent_proof.statement.assumptions, consequent),
                    set(antecedent_proof.rules).union({conditional, MP}),
                    consequent_proof_lines)

def combine_proofs(antecedent1_proof: Proof, antecedent2_proof: Proof,
                   consequent: Formula, double_conditional: InferenceRule) -> \
        Proof:
    """Combines the given proofs of two formulas `antecedent1` and `antecedent2`
    into a proof of the given formula `consequent` by using the given
    assumptionless inference rule of which
    ``'(``\ `antecedent1`\ ``->(``\ `antecedent2`\ ``->``\ `consequent`\ ``))'``
    is a specialization.

    Parameters:
        antecedent1_proof: valid proof of `antecedent1`.
        antecedent2_proof: valid proof of `antecedent2` from the same
            assumptions and inference rules as `antecedent1_proof`.
        consequent: formula to prove.
        double_conditional: assumptionless inference rule of which the
            assumptionless inference rule with conclusion
            ``'(``\ `antecedent1`\ ``->(``\ `antecedent2`\ ``->``\ `consequent`\ ``))'``
            is a specialization.

    Returns:
        A valid proof of `consequent` from the same assumptions as the given
        proofs, via the same inference rules as the given proofs and in addition
        `~propositions.axiomatic_systems.MP` and `double_conditional`.
    """
    assert antecedent1_proof.is_valid()
    assert antecedent2_proof.is_valid()
    assert antecedent1_proof.statement.assumptions == \
           antecedent2_proof.statement.assumptions
    assert antecedent1_proof.rules == antecedent2_proof.rules
    assert InferenceRule(
        [], Formula('->', antecedent1_proof.statement.conclusion,
        Formula('->', antecedent2_proof.statement.conclusion, consequent))
        ).is_specialization_of(double_conditional)
    # Task 5.3b
    # We'll start our proof of the consequent by proving the two antecedents.
    # To begin with, then, we can just copy over the lines from the first proof.
    consequent_proof_lines = list(antecedent1_proof.lines)
    # Then we add the lines from our second proof, but all of our index references will be off.
    # To solve this, we just shift all of the assumption numbers by the number of lines we already have.
    for antecedent2_line_number in range(len(antecedent2_proof.lines)):
        if antecedent2_proof.lines[antecedent2_line_number].rule is None:
            consequent_proof_lines.append(antecedent2_proof.lines[antecedent2_line_number])
        else:
            consequent_proof_lines.append(
                # The formula and rule stay the same.
                Proof.Line(antecedent2_proof.lines[antecedent2_line_number].formula, 
                antecedent2_proof.lines[antecedent2_line_number].rule, 
                # But the assumptions get shifted by the number of lines in the first proof.
                [x + len(antecedent1_proof.lines) for x in antecedent2_proof.lines[antecedent2_line_number].assumptions]))
    # Then we add the instantiated double conditional, no assumptions required.
    consequent_proof_lines.append(Proof.Line(
        Formula('->', antecedent1_proof.statement.conclusion, Formula('->', antecedent2_proof.statement.conclusion, consequent)),
        double_conditional, []))
    # Now we have everything we need to deduce the conditional. Just apply MP twice!

    # The following indices are used:
    # antecedent1_statement_index = len(antecedent1_proof.lines) - 1
    # antecedent2_statement_index = len(antecedent2_proof.lines) + len(antecedent1_proof.lines) - 1
    # double_conditional_index = len(antecedent2_proof.lines) + len(antecedent1_proof.lines)

    # First application of MP: deducing (a2 -> c), a2 = antecedent2, c = consequent
    consequent_proof_lines.append(Proof.Line(
        Formula('->', antecedent2_proof.statement.conclusion, consequent), MP, 
        [len(antecedent1_proof.lines) - 1, len(antecedent2_proof.lines) + len(antecedent1_proof.lines)]))
    # Second application of MP: deducing the consequent.
    consequent_proof_lines.append(Proof.Line(
        consequent, MP, 
        [len(antecedent2_proof.lines) + len(antecedent1_proof.lines) - 1, len(antecedent2_proof.lines) + len(antecedent1_proof.lines) + 1]))
    return Proof(InferenceRule(antecedent1_proof.statement.assumptions, consequent), antecedent1_proof.rules.union({MP, double_conditional}), consequent_proof_lines)

def remove_assumption(proof: Proof) -> Proof:
    """Converts the given proof of some `conclusion` formula, the last
    assumption of which is an assumption `assumption`, to a proof of
    ``'(``\ `assumption`\ ``->``\ `conclusion`\ ``)'`` from the same assumptions
    except `assumption`.

    Parameters:
        proof: valid proof to convert, with at least one assumption, via some
            set of inference rules all of which have no assumptions except
            perhaps `~propositions.axiomatic_systems.MP`.

    Returns:
        A valid proof of ``'(``\ `assumption`\ ``->``\ `conclusion`\ ``)'``
        from the same assumptions as the given proof except the last one, via
        the same inference rules as the given proof and in addition
        `~propositions.axiomatic_systems.MP`,
        `~propositions.axiomatic_systems.I0`,
        `~propositions.axiomatic_systems.I1`, and
        `~propositions.axiomatic_systems.D`.
    """        
    assert proof.is_valid()
    assert len(proof.statement.assumptions) > 0
    for rule in proof.rules:
        assert rule == MP or len(rule.assumptions) == 0
    # Task 5.4
    assumption = proof.statement.assumptions[-1]
    newLines = []
    for line_number in range(len(proof.lines)):
        line = proof.lines[line_number]
        # --- Case 1: The Line is in A ---
        if line.formula in proof.statement.assumptions and line.formula != assumption:
            # Add the assumption.
            newLines.append(Proof.Line(line.formula))
            # Instantiate I1.
            newLines.append(Proof.Line(Formula('->', line.formula, Formula('->', assumption, line.formula)), I1, []))
            # Use MP.
            newLines.append(Proof.Line(Formula('->', assumption, line.formula), MP, [len(newLines) - 2, len(newLines) - 1]))

        # --- Case 2: The Line is the Assumption ---
        elif line.formula == assumption:
            # Instantiate I0 using the assumption
            newLines.append(Proof.Line(Formula('->', assumption, assumption), I0, []))

        # --- Case 3: The Line is Deduced via MP ---
        elif line.rule == MP:
            # Let a be our assumption, xi the current line's formula, and xj and xk = (xj->xi) the formulae used as 
            # the assumptions of MP. (xj = line.assumptions[0], xk = line.assumptions[1]). We know we have previously
            # deduced (a -> xj) and (a -> xk). We instantiate D to get ((a->(xj->xi))->((a->xj)->(a->xi))). This is
            # the same as ((a->xk)->((a->xj)->(a->xi))). So we can use the fact that we've previously deduced
            # (a->xk) and (a->xj). First, though, we need to find (a->xk) and (a->xj).
            xi = line.formula
            xj = proof.lines[line.assumptions[0]].formula
            xk = proof.lines[line.assumptions[1]].formula
            xjIndex, xkIndex = -1, -1
            for previousLineNumber in range(len(newLines)):
                # Check if a previous line has formula (a->xj).
                if newLines[previousLineNumber].formula == Formula('->', assumption, xj):
                    xjIndex = previousLineNumber
                # Check for (a->xk).
                elif newLines[previousLineNumber].formula == Formula('->', assumption, xk):
                    xkIndex = previousLineNumber
            # Instantiate D (with p = a, q = xj, r = xi) getting ((a->xk)->((a->xj)->(a->xi))).
            newLines.append(Proof.Line(
                D.conclusion.substitute_variables({'p': assumption, 'q': xj, 'r': xi}),
                D, []))
            # First application of MP: deduce ((a->xj)->(a->xi)) from (a->xk) and instantiation of D.
            newLines.append(Proof.Line(
                D.conclusion.second.substitute_variables({'p': assumption, 'q': xj, 'r': xi}),
                MP, [xkIndex, len(newLines) - 1]))
            # Second application of MP: deduce (a->xi) from previous line and (a->xj).
            newLines.append(Proof.Line(
                Formula('->', assumption, xi), MP, [xjIndex, len(newLines) - 1]))
    
        # --- Case 4: The Line is Deduced via Some Other Rule ---
        else:
            # Then, as the book explains, the rule must have had no assumptions. So we can do essentially the same thing as Case 1.
            # Add the line as is.
            newLines.append(Proof.Line(line.formula, line.rule, []))
            # Instantiate I1.
            newLines.append(Proof.Line(Formula('->', line.formula, Formula('->', assumption, line.formula)), I1, []))
            # Use MP.
            newLines.append(Proof.Line(Formula('->', assumption, line.formula), MP, [len(newLines) - 2, len(newLines) - 1]))
    
    # Now the lines are complete, so we just have to put it together into a new Proof.
    return Proof(
        InferenceRule([proof.statement.assumptions[i] for i in range(len(proof.statement.assumptions) - 1)], 
                      Formula('->', assumption, proof.lines[-1].formula)), 
        proof.rules.union({MP, I0, I1, D}), newLines)

def prove_from_opposites(proof_of_affirmation: Proof,
                         proof_of_negation: Proof, conclusion: Formula) -> \
        Proof:
    """Combines the given proofs of a formula `affirmation` and its negation
    ``'~``\ `affirmation`\ ``'`` into a proof of the given formula.

    Parameters:
        proof_of_affirmation: valid proof of `affirmation`.
        proof_of_negation: valid proof of ``'~``\ `affirmation`\ ``'`` from the
            same assumptions and inference rules of `proof_of_affirmation`.
        conclusion: formula to prove.

    Returns:
        A valid proof of `conclusion` from the same assumptions as the given
        proofs, via the same inference rules as the given proofs and in addition
        `~propositions.axiomatic_systems.MP` and
        `~propositions.axiomatic_systems.I2`.
    """
    assert proof_of_affirmation.is_valid()
    assert proof_of_negation.is_valid()
    assert proof_of_affirmation.statement.assumptions == \
           proof_of_negation.statement.assumptions
    assert Formula('~', proof_of_affirmation.statement.conclusion) == \
           proof_of_negation.statement.conclusion
    assert proof_of_affirmation.rules == proof_of_negation.rules
    # Task 5.6
    # Explosion time!
    return combine_proofs(proof_of_negation, proof_of_affirmation, conclusion, I2)
    # What a nice, refreshing result!

def prove_by_way_of_contradiction(proof: Proof) -> Proof:
    """Converts the given proof of ``'~(p->p)'``, the last assumption of which
    is an assumption ``'~``\ `formula`\ ``'``, to a proof of `formula` from the
    same assumptions except ``'~``\ `formula`\ ``'``.

    Parameters:
        proof: valid proof of ``'~(p->p)'`` to convert, the last assumption of
            which is of the form ``'~``\ `formula`\ ``'``, via some set of
            inference rules all of which have no assumptions except perhaps
            `~propositions.axiomatic_systems.MP`.

    Returns:
        A valid proof of `formula` from the same assumptions as the given proof
        except the last one, via the same inference rules as the given proof and
        in addition `~propositions.axiomatic_systems.MP`,
        `~propositions.axiomatic_systems.I0`,
        `~propositions.axiomatic_systems.I1`,
        `~propositions.axiomatic_systems.D`, and
        `~propositions.axiomatic_systems.N`.
    """
    assert proof.is_valid()
    assert proof.statement.conclusion == Formula.parse('~(p->p)')
    assert len(proof.statement.assumptions) > 0
    assert proof.statement.assumptions[-1].root == '~'
    for rule in proof.rules:
        assert rule == MP or len(rule.assumptions) == 0
    # Task 5.7
    pp = Formula.parse('(p->p)')
    f = proof.statement.assumptions[-1].first
    # We have a proof with assumption ~f and conclusion ~(p->p). So we can use
    # the Deduction Theorem to turn it into a proof of (~f -> ~(p->p)). 
    Lines = list(remove_assumption(proof).lines)

    # Then, we instantiate N (q = f, p = (p->p)) to get ((~f->~(p->p))->((p->p)->f)).
    Lines.append(Proof.Line(N.conclusion.substitute_variables({'q' : f, 'p' : pp}), N, []))

    # We use MP once to get ((p->p)->f):
    Lines.append(Proof.Line(Formula('->', pp, f), MP, [len(Lines)-2, len(Lines)-1]))

    # Finally, the axiom I0 = (p->p) with MP deduces f.
    Lines.append(Proof.Line(pp, I0, []))
    Lines.append(Proof.Line(f, MP, [len(Lines)-1, len(Lines)-2]))

    # That finishes the lines, let's put it all together!
    return Proof(InferenceRule([proof.statement.assumptions[i] for i in range(len(proof.statement.assumptions)-1)], f), 
                 proof.rules.union({MP, I0, I1, D, N}), Lines)
    # What an incredibly cool result! I had no idea that you could formally prove like this that contradictions work.
    # Probably my favorite result from the book so far.