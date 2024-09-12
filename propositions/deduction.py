# This file is part of the materials accompanying the book
# "Mathematical Logic through Python" by Gonczarowski and Nisan,
# Cambridge University Press. Book site: www.LogicThruPython.org
# (c) Yannai A. Gonczarowski and Noam Nisan, 2017-2022
# File name: propositions/deduction.py

"""Useful proof manipulation maneuvers in Propositional Logic."""

from propositions.syntax import *
from propositions.proofs import *
from propositions.axiomatic_systems import *


def prove_corollary(
    antecedent_proof: Proof, consequent: Formula, conditional: InferenceRule
) -> Proof:
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
    assert InferenceRule(
        [], Formula("->", antecedent_proof.statement.conclusion, consequent)
    ).is_specialization_of(conditional)
    # Task 5.3a

    # We take a proof of phi and an inference rule which specializes to (phi->psi) and
    # build a proof of psi.
    phi = antecedent_proof.statement.conclusion
    psi = consequent
    psi_proof_lines = list(antecedent_proof.lines)

    # Add (phi->psi) and deduce psi.
    psi_proof_lines.append(Proof.Line(Formula("->", phi, psi), conditional, []))
    psi_proof_lines.append(
        Proof.Line(psi, MP, [len(psi_proof_lines) - 2, len(psi_proof_lines) - 1])
    )

    return Proof(
        InferenceRule(antecedent_proof.statement.assumptions, consequent),
        antecedent_proof.rules.union({conditional, MP}),
        psi_proof_lines,
    )


def combine_proofs(
    antecedent1_proof: Proof,
    antecedent2_proof: Proof,
    consequent: Formula,
    double_conditional: InferenceRule,
) -> Proof:
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
    assert (
        antecedent1_proof.statement.assumptions
        == antecedent2_proof.statement.assumptions
    )
    assert antecedent1_proof.rules == antecedent2_proof.rules
    assert InferenceRule(
        [],
        Formula(
            "->",
            antecedent1_proof.statement.conclusion,
            Formula("->", antecedent2_proof.statement.conclusion, consequent),
        ),
    ).is_specialization_of(double_conditional)
    # Task 5.3b

    # Recall that antecedent1_proof proves phi1 and antecedent2_proof proves phi2. Then
    # double_conditional specializes to (phi1->(phi2->psi)) where psi = consequent. So,
    # we take 3 steps:
    #   (1) Add the lines from antecedent1_proof and antecedent2_proof, shifting
    #       assumptions where needed.
    #   (2) Build the additional lines needed, (phi1->(phi2->psi)) deduced as an
    #       assumption, (phi2->psi) deduced from MP, and psi deduced from MP.
    #   (3) Add the new lines and return the proof.

    # (1) Adding the lines from antecedent1_proof and antecedent2_proof
    new_lines = list(antecedent1_proof.lines)

    for line in antecedent2_proof.lines:
        if line.rule is None:
            new_lines.append(line)
            continue
        new_assumptions = (
            assumption + len(antecedent1_proof.lines) for assumption in line.assumptions
        )
        new_lines.append(Proof.Line(line.formula, line.rule, new_assumptions))

    # (2) Build the additional lines needed: (phi1->(phi2->psi)) which I call "double
    # conditional line," (phi2->psi) which I call "conditional line," and psi.
    phi1 = antecedent1_proof.statement.conclusion
    phi1_line_number = len(antecedent1_proof.lines) - 1
    phi2 = antecedent2_proof.statement.conclusion
    phi2_line_number = len(new_lines) - 1
    psi = consequent

    double_conditional_line = Proof.Line(
        Formula("->", phi1, Formula("->", phi2, psi)),
        double_conditional,
        tuple(),
    )
    double_conditional_line_number = len(new_lines)

    conditional_line = Proof.Line(
        Formula("->", phi2, psi),
        MP,
        (phi1_line_number, double_conditional_line_number),
    )
    conditional_line_number = len(new_lines) + 1

    psi_line = Proof.Line(
        psi,
        MP,
        (phi2_line_number, conditional_line_number),
    )

    # (3) Add the new lines and return the proof.
    new_lines.extend([double_conditional_line, conditional_line, psi_line])

    return Proof(
        InferenceRule(antecedent1_proof.statement.assumptions, psi),
        antecedent1_proof.rules.union({MP, double_conditional}),
        tuple(new_lines),
    )


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

    phi = proof.statement.assumptions[-1]  # The assumption being removed
    new_lines = []
    new_formulas = []

    # As the book explains, we go through each line in the original proof with formula
    # xi, and we add a sequence of lines letting us deduce (phi->xi), which I call "new
    # formula." Each of these lines falls into one of three cases:
    #   (1) xi = phi. Then the new formula is a specialization of I0.
    #   (2) xi was deduced via MP with assumptions xj and xk = (xj->xi). Then we have
    #       previously deduced (phi->xj) and (phi->xk), which I call "new_xj" and
    #       "new_xk", respectively. We (a) find where we did this, (b) instantiate D, and
    #       (c) use MP twice to deduce the new formula.
    #   (3) xi is in A or was deduced via an assumptionless inference rule. Then we (a)
    #       deduce xi in the same manner and (b) get the new formula from I1 and MP.
    for line_number in range(len(proof.lines)):
        line = proof.lines[line_number]
        xi = line.formula
        new_formula = Formula("->", phi, xi)

        # (1) xi = phi
        if xi == phi:
            I0_formula = Formula("->", phi, phi)
            new_formulas.append(I0_formula)
            new_lines.append(Proof.Line(I0_formula, I0, []))

        # (2) xi was deduced via MP
        elif line.rule == MP:
            # (a) Find where we deduced new_xj and new_xk
            xj = proof.lines[line.assumptions[0]].formula
            new_xj = Formula("->", phi, xj)
            xk = proof.lines[line.assumptions[1]].formula
            new_xk = Formula("->", phi, xk)

            new_xj_line_number = new_formulas.index(new_xj)
            new_xk_line_number = new_formulas.index(new_xk)

            # (b) Instantiate D: ((phi->xk)->((phi->xj)->(phi->xi)))
            D_formula = D.conclusion.substitute_variables({"p": phi, "q": xj, "r": xi})
            new_formulas.append(D_formula)
            new_lines.append(Proof.Line(D_formula, D, []))

            # (c) Use MP twice
            new_formulas.append(D_formula.second)
            new_lines.append(
                Proof.Line(
                    D_formula.second, MP, [new_xk_line_number, len(new_lines) - 1]
                )
            )

            new_formulas.append(new_formula)
            new_lines.append(
                Proof.Line(new_formula, MP, [new_xj_line_number, len(new_lines) - 1])
            )

        # (3) xi is in A or was deduced via an assumptionless inference rule
        else:
            # (a) Deduce xi in the same manner
            new_formulas.append(xi)
            new_lines.append(line)

            # (b) Get the new formula from I1 and MP
            I1_formula = Formula("->", xi, Formula("->", phi, xi))
            new_formulas.append(I1_formula)
            new_lines.append(Proof.Line(I1_formula, I1, []))

            new_formulas.append(new_formula)
            new_lines.append(
                Proof.Line(new_formula, MP, [len(new_lines) - 2, len(new_lines) - 1])
            )

    # Once we're done, we build the new proof.
    new_assumptions = [
        proof.statement.assumptions[i]
        for i in range(len(proof.statement.assumptions) - 1)
    ]
    new_statement = InferenceRule(
        new_assumptions, Formula("->", phi, proof.statement.conclusion)
    )
    return Proof(new_statement, proof.rules.union({MP, I0, I1, D}), new_lines)


def prove_from_opposites(
    proof_of_affirmation: Proof, proof_of_negation: Proof, conclusion: Formula
) -> Proof:
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
    assert (
        proof_of_affirmation.statement.assumptions
        == proof_of_negation.statement.assumptions
    )
    assert (
        Formula("~", proof_of_affirmation.statement.conclusion)
        == proof_of_negation.statement.conclusion
    )
    assert proof_of_affirmation.rules == proof_of_negation.rules
    # Task 5.6

    return combine_proofs(proof_of_negation, proof_of_affirmation, conclusion, I2)


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
    assert proof.statement.conclusion == Formula.parse("~(p->p)")
    assert len(proof.statement.assumptions) > 0
    assert proof.statement.assumptions[-1].root == "~"
    for rule in proof.rules:
        assert rule == MP or len(rule.assumptions) == 0
    # Task 5.7

    # We are given a proof with assumptions Au{~phi} and conclusion ~(p->p). So, we
    #   (1) use the deduction theorem to obtain a proof of (~phi->~(p->p)) from A,
    #   (2) instantiate I0 to get (p->p), and
    #   (3) instantiate N to get ((~phi->~(p->p))->((p->p)->phi)) and use MP twice with
    #       our results from (1) and (2).

    p_implies_p = Formula.parse("(p->p)")
    phi = proof.statement.assumptions[-1].first
    A = list(proof.statement.assumptions)
    A.remove(proof.statement.assumptions[-1])

    # (1) Use the deduction theorem to prove (~phi->~(p->p))
    lines = list(remove_assumption(proof).lines)

    # (2) Instantiate I0 to get (p->p)
    lines.append(Proof.Line(p_implies_p, I0, []))

    # (3) Instantiate N to get ((~phi->~(p->p))->((p->p)->phi)) and use MP twice
    lines.append(
        Proof.Line(
            N.conclusion.substitute_variables({"q": phi, "p": p_implies_p}), N, []
        )
    )

    lines.append(
        Proof.Line(
            Formula("->", p_implies_p, phi), MP, [len(lines) - 3, len(lines) - 1]
        )
    )
    lines.append(Proof.Line(phi, MP, [len(lines) - 3, len(lines) - 1]))

    return Proof(InferenceRule(A, phi), proof.rules.union({MP, I0, I1, D, N}), lines)
