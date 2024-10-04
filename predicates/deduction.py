# This file is part of the materials accompanying the book
# "Mathematical Logic through Python" by Gonczarowski and Nisan,
# Cambridge University Press. Book site: www.LogicThruPython.org
# (c) Yannai A. Gonczarowski and Noam Nisan, 2017-2022
# File name: predicates/deduction.py

"""Useful proof manipulation maneuvers in Predicate Logic."""

from predicates.syntax import *
from predicates.proofs import *
from predicates.prover import *


def remove_assumption(
    proof: Proof, assumption: Formula, print_as_proof_forms: bool = False
) -> Proof:
    """Converts the given proof of some `conclusion` formula, an assumption of
    which is `assumption`, to a proof of
    ``'(``\ `assumption`\ ``->``\ `conclusion`\ ``)'`` from the same assumptions
    except `assumption`.

    Parameters:
        proof: valid proof to convert, from assumptions/axioms that include
            `~predicates.prover.Prover.AXIOMS`.
        assumption: formula that is a simple assumption (i.e., without any
            templates) of the given proof, such that no line of the given proof
            is a UG line over a variable name that is free in this assumption.
        print_as_proof_forms: flag specifying whether the proof of
            ``'(``\ `assumption`\ ``->``\ `conclusion`\ ``)'`` is to be printed
            in real time as it is being created.

    Returns:
        A valid proof of ``'(``\ `assumption`\ ``->``\ `conclusion`\ ``)'``
        from the same assumptions/axioms as the given proof except `assumption`.
    """
    assert proof.is_valid()
    assert Schema(assumption) in proof.assumptions
    assert proof.assumptions.issuperset(Prover.AXIOMS)
    for line in proof.lines:
        if isinstance(line, Proof.UGLine):
            assert line.formula.variable not in assumption.free_variables()
    # Task 11.1

    # We have an old proof of a conclusion c from assumptions Au{phi}. We turn
    # this into a proof of (phi->c) via assumptions A.
    lines = list(proof.lines)
    phi = assumption

    new_assumptions = set(proof.assumptions)  # A
    new_assumptions.remove(Schema(phi))
    new_proof = Prover(new_assumptions, print_as_proof_forms)

    for line_number in range(len(lines)):
        line = lines[line_number]
        # We consider each line of the original proof to have formula xi.
        # We want to turn this into a validly justified line with formula
        # new_form = (phi->xi).
        xi = line.formula
        new_form = Formula("->", phi, xi)

        # Each line falls into 1 of 4 cases:
        # 1. xi is phi or xi is a tautology. Then we deduce (phi->xi) as a tautology.
        # 2. xi is deduced via MP. Then in the new proof, we have previously deduced
        #    (phi->a) and (phi->(a->xi)) for some formula a. So we (i) find
        #    where these formulas were deduced, and (ii) deduce (phi->xi) as a
        #    tautological implication of these.
        # 3. xi is deduced via UG. Then xi = Ax[psi(x)] and the new proof has
        #    previously deduced (phi->psi(x)). So we (i) find where we deduced
        #    it, (ii) use UG to get Ax[(phi->psi(x))], (iii) instantiate US to get
        #    (Ax[(phi->psi(x))]->(phi->Ax[psi(x)])), and (iv) deduce (phi->xi) as a
        #    tautological implication of these.
        # 4. xi is an (instantiated) assumption in A. Then we (i) deduce xi as an
        #    (instantiated) assumption, and (ii) deduce (phi->xi) as a tautological
        #    implication of xi.

        # Case 1: xi is phi or xi is a tautology
        if (xi == phi) or (isinstance(line, Proof.TautologyLine)):
            # deduce (phi->xi) as a tautology.
            new_proof.add_tautology(new_form)
            continue

        # Case 2: xi is deduced via MP
        elif isinstance(line, Proof.MPLine):
            antecedent = lines[line.antecedent_line_number].formula  # a
            conditional = lines[line.conditional_line_number].formula  # (a->xi)

            # (i) find where (phi->a) and (phi->(a->xi)) were deduced
            new_antecedent = Formula("->", phi, antecedent)  # (phi->a)
            new_conditional = Formula("->", phi, conditional)  # (phi->(a->xi))

            for previous_line_number in range(len(new_proof._lines)):
                previous_line = new_proof._lines[previous_line_number]
                previous_formula = previous_line.formula
                if str(previous_formula) == str(new_antecedent):
                    new_antecedent_line_number = previous_line_number
                elif str(previous_formula) == str(new_conditional):
                    new_conditional_line_number = previous_line_number

            # (ii) deduce (phi->xi) as a tautological implication of these.
            new_proof.add_tautological_implication(
                new_form, {new_antecedent_line_number, new_conditional_line_number}
            )
            continue

        # Case 3: xi is deduced via UG
        elif isinstance(line, Proof.UGLine):
            psi = xi.statement  # psi(x)
            x = xi.variable

            # (i) find where we deduced (phi->psi(x))
            conditional = Formula("->", phi, psi)  # (phi->psi(x))
            for previous_line_number in range(len(new_proof._lines)):
                previous_line = new_proof._lines[previous_line_number]
                previous_formula = previous_line.formula
                if str(previous_formula) == str(conditional):
                    conditional_line_number = previous_line_number
                    break

            # (ii) use UG to get Ax[(phi->psi(x))]
            generalized_conditional_line_number = new_proof.add_ug(
                Formula("A", x, conditional), conditional_line_number
            )

            # (iii) instantiate US to get (Ax[(phi->psi(x))]->(phi->Ax[psi(x)]))
            parametrized_psi = psi.substitute({x: Term("_")}, {})
            us_instantiation_map = {"Q": phi, "R": parametrized_psi, "x": x}
            us_instantiation_line_number = new_proof.add_instantiated_assumption(
                Prover.US.instantiate(us_instantiation_map),
                Prover.US,
                us_instantiation_map,
            )

            # (iv) deduce (phi->xi) as a tautological implication of these.
            new_proof.add_tautological_implication(
                new_form,
                {generalized_conditional_line_number, us_instantiation_line_number},
            )
            continue
        # Case 4: xi is an (instantiated) assumption in A
        # (i) deduce xi as an (instantiated) assumption
        if Schema(xi) in new_assumptions:  # Non-instantiated assumption
            instantiated_assumption = new_proof.add_assumption(xi)
        else:  # Instantiated assumption
            instantiated_assumption = new_proof.add_instantiated_assumption(
                xi, line.assumption, line.instantiation_map
            )

        # (ii) deduce (phi->xi) as a tautological implication of xi.
        new_proof.add_tautological_implication(
            new_form, {instantiated_assumption}
        )

    return new_proof.qed()


def prove_by_way_of_contradiction(proof: Proof, assumption: Formula) -> Proof:
    """Converts the given proof of a contradiction, an assumption of which is
    `assumption`, to a proof of ``'~``\ `assumption`\ ``'`` from the same
    assumptions except `assumption`.

    Parameters:
        proof: valid proof of a contradiction (i.e., a formula whose negation is
            a tautology) to convert, from assumptions/axioms that include
            `~predicates.prover.Prover.AXIOMS`.
        assumption: formula that is a simple assumption (i.e., without any
            templates) of the given proof, such that no line of the given proof
            is a UG line over a variable name that is free in this assumption.

    Returns:
        A valid proof of ``'~``\ `assumption`\ ``'`` from the same
        assumptions/axioms as the given proof except `assumption`.
    """
    assert proof.is_valid()
    assert Schema(assumption) in proof.assumptions
    assert proof.assumptions.issuperset(Prover.AXIOMS)
    for line in proof.lines:
        if isinstance(line, Proof.UGLine):
            assert line.formula.variable not in assumption.free_variables()
    # Task 11.2

    # As in propositional logic, we use the deduction theorem to prove
    # (assumption->~tautology). ~assumption is a tautological implication of this.
    new_assumptions = set(proof.assumptions)
    new_assumptions.remove(Schema(assumption))
    new_proof = Prover(new_assumptions)

    assumption_implies_contradiction = new_proof.add_proof(  # (assumption->~tautology)
        Formula("->", assumption, proof.conclusion),
        remove_assumption(proof, assumption),
    )
    new_proof.add_tautological_implication(
        Formula("~", assumption), {assumption_implies_contradiction}
    )
    return new_proof.qed()
