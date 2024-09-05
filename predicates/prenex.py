# This file is part of the materials accompanying the book
# "Mathematical Logic through Python" by Gonczarowski and Nisan,
# Cambridge University Press. Book site: www.LogicThruPython.org
# (c) Yannai A. Gonczarowski and Noam Nisan, 2017-2022
# File name: predicates/prenex.py

"""Conversion of predicate-logic formulas into prenex normal form."""

from typing import Tuple

from logic_utils import fresh_variable_name_generator, is_z_and_number

from predicates.syntax import *
from predicates.proofs import *
from predicates.prover import *

#: Additional axioms of quantification for Predicate Logic.
ADDITIONAL_QUANTIFICATION_AXIOMS = (
    Schema(
        Formula.parse("((~Ax[R(x)]->Ex[~R(x)])&(Ex[~R(x)]->~Ax[R(x)]))"), {"x", "R"}
    ),
    Schema(
        Formula.parse("((~Ex[R(x)]->Ax[~R(x)])&(Ax[~R(x)]->~Ex[R(x)]))"), {"x", "R"}
    ),
    Schema(
        Formula.parse(
            "(((Ax[R(x)]&Q())->Ax[(R(x)&Q())])&" "(Ax[(R(x)&Q())]->(Ax[R(x)]&Q())))"
        ),
        {"x", "R", "Q"},
    ),
    Schema(
        Formula.parse(
            "(((Ex[R(x)]&Q())->Ex[(R(x)&Q())])&" "(Ex[(R(x)&Q())]->(Ex[R(x)]&Q())))"
        ),
        {"x", "R", "Q"},
    ),
    Schema(
        Formula.parse(
            "(((Q()&Ax[R(x)])->Ax[(Q()&R(x))])&" "(Ax[(Q()&R(x))]->(Q()&Ax[R(x)])))"
        ),
        {"x", "R", "Q"},
    ),
    Schema(
        Formula.parse(
            "(((Q()&Ex[R(x)])->Ex[(Q()&R(x))])&" "(Ex[(Q()&R(x))]->(Q()&Ex[R(x)])))"
        ),
        {"x", "R", "Q"},
    ),
    Schema(
        Formula.parse(
            "(((Ax[R(x)]|Q())->Ax[(R(x)|Q())])&" "(Ax[(R(x)|Q())]->(Ax[R(x)]|Q())))"
        ),
        {"x", "R", "Q"},
    ),
    Schema(
        Formula.parse(
            "(((Ex[R(x)]|Q())->Ex[(R(x)|Q())])&" "(Ex[(R(x)|Q())]->(Ex[R(x)]|Q())))"
        ),
        {"x", "R", "Q"},
    ),
    Schema(
        Formula.parse(
            "(((Q()|Ax[R(x)])->Ax[(Q()|R(x))])&" "(Ax[(Q()|R(x))]->(Q()|Ax[R(x)])))"
        ),
        {"x", "R", "Q"},
    ),
    Schema(
        Formula.parse(
            "(((Q()|Ex[R(x)])->Ex[(Q()|R(x))])&" "(Ex[(Q()|R(x))]->(Q()|Ex[R(x)])))"
        ),
        {"x", "R", "Q"},
    ),
    Schema(
        Formula.parse(
            "(((Ax[R(x)]->Q())->Ex[(R(x)->Q())])&" "(Ex[(R(x)->Q())]->(Ax[R(x)]->Q())))"
        ),
        {"x", "R", "Q"},
    ),
    Schema(
        Formula.parse(
            "(((Ex[R(x)]->Q())->Ax[(R(x)->Q())])&" "(Ax[(R(x)->Q())]->(Ex[R(x)]->Q())))"
        ),
        {"x", "R", "Q"},
    ),
    Schema(
        Formula.parse(
            "(((Q()->Ax[R(x)])->Ax[(Q()->R(x))])&" "(Ax[(Q()->R(x))]->(Q()->Ax[R(x)])))"
        ),
        {"x", "R", "Q"},
    ),
    Schema(
        Formula.parse(
            "(((Q()->Ex[R(x)])->Ex[(Q()->R(x))])&" "(Ex[(Q()->R(x))]->(Q()->Ex[R(x)])))"
        ),
        {"x", "R", "Q"},
    ),
    Schema(
        Formula.parse(
            "(((R(x)->Q(x))&(Q(x)->R(x)))->"
            "((Ax[R(x)]->Ay[Q(y)])&(Ay[Q(y)]->Ax[R(x)])))"
        ),
        {"x", "y", "R", "Q"},
    ),
    Schema(
        Formula.parse(
            "(((R(x)->Q(x))&(Q(x)->R(x)))->"
            "((Ex[R(x)]->Ey[Q(y)])&(Ey[Q(y)]->Ex[R(x)])))"
        ),
        {"x", "y", "R", "Q"},
    ),
)


def is_quantifier_free(formula: Formula) -> bool:
    """Checks if the given formula contains any quantifiers.

    Parameters:
        formula: formula to check.

    Returns:
        ``False`` if the given formula contains any quantifiers, ``True``
        otherwise.
    """
    # Task 11.3a

    # Relations and equalities are always quantifier free, so we only need to check
    # for quantifiers and recurse for unary/binary operations.
    if is_unary(formula.root):
        return is_quantifier_free(formula.first)
    elif is_binary(formula.root):
        return is_quantifier_free(formula.first) and is_quantifier_free(formula.second)
    else:
        return not is_quantifier(formula.root)


def is_in_prenex_normal_form(formula: Formula) -> bool:
    """Checks if the given formula is in prenex normal form.

    Parameters:
        formula: formula to check.

    Returns:
        ``True`` if the given formula in prenex normal form, ``False``
        otherwise.
    """
    # Task 11.3b

    # Non-quantified statements must be quantifier free
    if not is_quantifier(formula.root):
        return is_quantifier_free(formula)
    # The statement of quantifications must also be in prenex normal form, so recurse.
    return is_in_prenex_normal_form(formula.statement)


def equivalence_of(formula1: Formula, formula2: Formula) -> Formula:
    """States the equivalence of the two given formulas as a formula.

    Parameters:
        formula1: first of the formulas the equivalence of which is to be
            stated.
        formula2: second of the formulas the equivalence of which is to be
            stated.

    Returns:
        The formula ``'((``\ `formula1`\ ``->``\ `formula2`\ ``)&(``\ `formula2`\ ``->``\ `formula1`\ ``))'``.
    """
    return Formula(
        "&", Formula("->", formula1, formula2), Formula("->", formula2, formula1)
    )


def has_uniquely_named_variables(formula: Formula) -> bool:
    """Checks if the given formula has uniquely named variables.

    Parameters:
        formula: formula to check.

    Returns:
        ``False`` if in the given formula some variable name has both bound and
        free occurrences or is quantified by more than one quantifier, ``True``
        otherwise.

    Examples:
        >>> has_uniquely_named_variables(
        ...     Formula.parse('(x=0&(Ax[R(x)]|Ex[R(x)]))'))
        False
        >>> has_uniquely_named_variables(
        ...     Formula.parse('(x=0&(Ax[R(x)]|Ey[R(y)]))'))
        False
        >>> has_uniquely_named_variables(
        ...     Formula.parse('(y=0&(Ax[R(x)]|Ex[R(x)]))'))
        False
        >>> has_uniquely_named_variables(
        ...     Formula.parse('(x=0&(Ay[R(y)]|Ez[R(z)]))'))
        True
    """
    forbidden_variables = set(formula.free_variables())

    def has_uniquely_named_variables_helper(formula: Formula) -> bool:
        if is_unary(formula.root):
            return has_uniquely_named_variables_helper(formula.first)
        elif is_binary(formula.root):
            return has_uniquely_named_variables_helper(
                formula.first
            ) and has_uniquely_named_variables_helper(formula.second)
        elif is_quantifier(formula.root):
            if formula.variable in forbidden_variables:
                return False
            forbidden_variables.add(formula.variable)
            return has_uniquely_named_variables_helper(formula.statement)
        else:
            assert is_equality(formula.root) or is_relation(formula.root)
            return True

    return has_uniquely_named_variables_helper(formula)


def _uniquely_rename_quantified_variables(formula: Formula) -> Tuple[Formula, Proof]:
    """Converts the given formula to an equivalent formula with uniquely named
    variables, and proves the equivalence of these two formulas.

    Parameters:
        formula: formula to convert, which contains no variable names that are
            ``z`` followed by a number.

    Returns:
        A pair. The first element of the pair is a formula equivalent to the
        given formula, with the exact same structure but with the additional
        property of having uniquely named variables, obtained by consistently
        replacing each variable name that is bound in the given formula with a
        new variable name obtained by calling
        `next`\ ``(``\ `~logic_utils.fresh_variable_name_generator`\ ``)``. The
        second element of the pair is a proof of the equivalence of the given
        formula and the returned formula (i.e., a proof of
        `equivalence_of`\ ``(``\ `formula`\ ``,``\ `returned_formula`\ ``)``)
        via `~predicates.prover.Prover.AXIOMS` and
        `ADDITIONAL_QUANTIFICATION_AXIOMS`.

    Examples:
        >>> formula = Formula.parse('~(w=x|Aw[(Ex[(x=w&Aw[w=x])]->Ax[x=y])])')
        >>> returned_formula, proof = _uniquely_rename_quantified_variables(
        ...     formula)
        >>> returned_formula
        ~(w=x|Az58[(Ez17[(z17=z58&Az4[z4=z17])]->Az32[z32=y])])
        >>> proof.is_valid()
        True
        >>> proof.conclusion == equivalence_of(formula, returned_formula)
        True
        >>> proof.assumptions == Prover.AXIOMS.union(
        ...     ADDITIONAL_QUANTIFICATION_AXIOMS)
        True
    """
    for variable in formula.variables():
        assert not is_z_and_number(variable)
    # Task 11.5

    assumptions = set(Prover.AXIOMS).union(set(ADDITIONAL_QUANTIFICATION_AXIOMS))

    if is_quantifier_free(formula):
        # Since free variables won't appear in calls to fresh_variable_name_generator,
        # we can ignore them and only deal with bound variables.
        proof = Prover(assumptions)
        proof.add_tautology(equivalence_of(formula, formula))
        return (formula, proof.qed())

    elif is_quantifier(formula.root):
        # If the formula is a quantification, then it is of the form Qx[phi(x)] for
        # some quantifier Q, parametrized formula phi, and variable name x.
        Q = formula.root
        x = formula.variable
        phi = formula.statement

        # We start by getting a formula equivalent to phi(x) with unique quantified
        # variable names. I call this psi(x). We also get a proof of
        # equivalence_of(phi(x), psi(x)). We now replace 'x' in psi(x) with a new
        # variable, say y, and quantify it to get Qy[psi(y)], the needed formula.
        psi, phi_equivalent_to_psi_proof = _uniquely_rename_quantified_variables(
            formula.statement
        )
        y = next(fresh_variable_name_generator)
        psi_y = psi.substitute({x: Term(y)})
        Qy_psi_y = Formula(formula.root, y, psi_y)

        # Now we have the equivalent formula, but we need to prove the equivalence. We
        # (i) take the proof of equivalence_of(phi(x), psi(x)), (ii) use an instance of
        # quantification axiom 15 (for universal quantification) or 16 (for existential
        # quantification), and (iii) deduce equivalence_of(Qx[phi(x)], Qy[psi(y)])
        # as a tautological implication. This final equivalence is what we need.

        # (i) Take the proof of equivalence_of(phi(x), psi(x))
        proof = Prover(assumptions)
        phi_psi_equivalence_line_number = proof.add_proof(
            phi_equivalent_to_psi_proof.conclusion, phi_equivalent_to_psi_proof
        )

        # (ii) Instantiate the appropriate quantification axiom
        parametrized_phi = phi.substitute({x: Term("_")})
        parametrized_psi = psi.substitute({x: Term("_")})
        axiom_instantiation_map = {
            "x": x,
            "y": y,
            "R": parametrized_phi,
            "Q": parametrized_psi,
        }
        if Q == "A":
            axiom = ADDITIONAL_QUANTIFICATION_AXIOMS[14]
        else:
            axiom = ADDITIONAL_QUANTIFICATION_AXIOMS[15]
        axiom_line_number = proof.add_instantiated_assumption(
            axiom.instantiate(axiom_instantiation_map), axiom, axiom_instantiation_map
        )

        # (iii) Deduce the desired equivalence as a tautological implication.
        proof.add_tautological_implication(
            equivalence_of(formula, Qy_psi_y),
            {phi_psi_equivalence_line_number, axiom_line_number},
        )
        return (Qy_psi_y, proof.qed())

    elif is_unary(formula.root):
        # If the formula's root is a unary operator, then the formula looks like *phi
        # for some unary operator * and some formula phi. We recursively find an
        # equivalent formula, psi, for phi, so that *phi is equivalent to *psi.
        star = formula.root
        phi = formula.first

        psi, phi_equivalent_to_psi_proof = _uniquely_rename_quantified_variables(phi)
        star_psi = Formula(star, psi)

        # With our equivalent formula, we just need a proof of equivalence. As with
        # quantification, we just take the proof of equivalence_of(phi, psi) and deduce
        # equivalence_of(*phi, *psi) as a tautological implication.
        proof = Prover(assumptions)
        psi_phi_equivalence = proof.add_proof(
            equivalence_of(phi, psi), phi_equivalent_to_psi_proof
        )
        proof.add_tautological_implication(
            equivalence_of(formula, star_psi), {psi_phi_equivalence}
        )
        return (star_psi, proof.qed())

    elif is_binary(formula.root):
        # In this case, the formula is (phi1*phi2) for some binary operator * and some
        # formulas phi1 and phi2. As before, we find the equivalent of this formula
        # recursively, and then proof the equivalence as a tautological implication of
        # the equivalences for phi1 and phi2.
        star = formula.root
        phi1 = formula.first
        phi2 = formula.second

        psi1, phi1_equivalent_to_psi1_proof = _uniquely_rename_quantified_variables(
            phi1
        )  # psi1 is the equivalent of phi1
        psi2, phi2_equivalent_to_psi2_proof = _uniquely_rename_quantified_variables(
            phi2
        )  # psi2 is the equivalent of phi2
        psi1_star_psi2 = Formula(star, psi1, psi2)

        # Building the proof of equivalence_of((phi1*phi2), (psi1*psi2))
        proof = Prover(assumptions)
        phi1_psi1_equivalence = proof.add_proof(
            equivalence_of(phi1, psi1), phi1_equivalent_to_psi1_proof
        )
        phi2_psi2_equivalence = proof.add_proof(
            equivalence_of(phi2, psi2), phi2_equivalent_to_psi2_proof
        )
        proof.add_tautological_implication(
            equivalence_of(formula, psi1_star_psi2),
            {phi1_psi1_equivalence, phi2_psi2_equivalence},
        )
        return (psi1_star_psi2, proof.qed())


def _pull_out_quantifications_across_negation(
    formula: Formula,
) -> Tuple[Formula, Proof]:
    """Converts the given formula with uniquely named variables of the form
    ``'~``\ `Q1`\ `x1`\ ``[``\ `Q2`\ `x2`\ ``[``...\ `Qn`\ `xn`\ ``[``\ `inner_formula`\ ``]``...\ ``]]'``
    to an equivalent formula of the form
    ``'``\ `Q'1`\ `x1`\ ``[``\ `Q'2`\ `x2`\ ``[``...\ `Q'n`\ `xn`\ ``[~``\ `inner_formula`\ ``]``...\ ``]]'``,
    and proves the equivalence of these two formulas.

    Parameters:
        formula: formula to convert, whose root is a negation, i.e., which is of
            the form
            ``'~``\ `Q1`\ `x1`\ ``[``\ `Q2`\ `x2`\ ``[``...\ `Qn`\ `xn`\ ``[``\ `inner_formula`\ ``]``...\ ``]]'``
            where `n`>=0, each `Qi` is a quantifier, each `xi` is a variable
            name, and `inner_formula` does not start with a quantifier.

    Returns:
        A pair. The first element of the pair is a formula equivalent to the
        given formula, but of the form
        ``'``\ `Q'1`\ `x1`\ ``[``\ `Q'2`\ `x2`\ ``[``...\ `Q'n`\ `xn`\ ``[~``\ `inner_formula`\ ``]``...\ ``]]'``
        where each `Q'i` is a quantifier, and where the `xi` variable names and
        `inner_formula` are the same as in the given formula. The second element
        of the pair is a proof of the equivalence of the given formula and the
        returned formula (i.e., a proof of
        `equivalence_of`\ ``(``\ `formula`\ ``,``\ `returned_formula`\ ``)``)
        via `~predicates.prover.Prover.AXIOMS` and
        `ADDITIONAL_QUANTIFICATION_AXIOMS`.

    Examples:
        >>> formula = Formula.parse('~Ax[Ey[R(x,y)]]')
        >>> returned_formula, proof = _pull_out_quantifications_across_negation(
        ...     formula)
        >>> returned_formula
        Ex[Ay[~R(x,y)]]
        >>> proof.is_valid()
        True
        >>> proof.conclusion == equivalence_of(formula, returned_formula)
        True
        >>> proof.assumptions == Prover.AXIOMS.union(
        ...     ADDITIONAL_QUANTIFICATION_AXIOMS)
        True
    """
    assert is_unary(formula.root)
    # Task 11.6

    assumptions = set(Prover.AXIOMS).union(set(ADDITIONAL_QUANTIFICATION_AXIOMS))

    # Base case: n = 0
    if not is_quantifier(formula.first.root):
        # In this case, our formula stays the same, so the equivalence is a tautology.
        proof = Prover(assumptions)
        proof.add_tautology(equivalence_of(formula, formula))
        return (formula, proof.qed())

    # Recursive case: n > 0
    # Then the formula has the form ~Qx[phi(x)] for some quantifier Q, some parametrized
    # formula phi and some variable name x. We
    #   (i) recurse to find an equivalent formula, rho, for ~phi and a proof of
    #       equivalence_of(~phi(x), rho(x)),
    #   (ii) construct the new formula Q'x[rho(x)], where Q' = A if Q = E and vice versa,
    #   (iii) use new axiom 1 or 2 to prove equivalence_of(~Qx[phi(x)], Q'x[~phi(x)]),
    #   (iv) instantiate new axiom 15 or 16 and use the proof from (i) to prove
    #       equivalence_of(Q'x[~phi(x)], Q'x[rho(x)]), and
    #   (v) use a tautological implication on the equivalences from (iii) and (iv) to
    #       deduce equivalence_of(~Qx[phi(x)], Q'x[rho(x)]), as desired.
    Q = formula.first.root
    x = formula.first.variable
    phi = formula.first.statement
    not_phi = Formula("~", phi)
    proof = Prover(assumptions)

    # (i) Recurse to get rho and a proof of = equivalence_of(~phi(x), rho(x))
    rho, not_phi_equivalent_to_rho_proof = _pull_out_quantifications_across_negation(
        not_phi
    )
    not_phi_rho_equivalence_line_number = proof.add_proof(
        equivalence_of(not_phi, rho), not_phi_equivalent_to_rho_proof
    )

    # (ii) Construct the new formula Q'x[rho(x)]
    if Q == "A":
        Q_prime = "E"
        axiom_1_or_2 = ADDITIONAL_QUANTIFICATION_AXIOMS[0]
        axiom_15_or_16 = ADDITIONAL_QUANTIFICATION_AXIOMS[15]
    else:
        Q_prime = "A"
        axiom_1_or_2 = ADDITIONAL_QUANTIFICATION_AXIOMS[1]
        axiom_15_or_16 = ADDITIONAL_QUANTIFICATION_AXIOMS[14]
    Q_prime_x_rho = Formula(Q_prime, x, rho)

    # (iii) Instantiate axiom 1 or 2 to get equivalence_of(~Qx[phi(x)], Q'x[~phi(x)])
    # which I call "QN_equivalence" (as this rule is called quantifier negation).
    parametrized_phi = phi.substitute({x: Term("_")})
    axiom_1_or_2_instantiation_map = {"x": x, "R": parametrized_phi}
    QN_equivalence = axiom_1_or_2.instantiate(axiom_1_or_2_instantiation_map)
    QN_equivalence_line_number = proof.add_instantiated_assumption(
        QN_equivalence, axiom_1_or_2, axiom_1_or_2_instantiation_map
    )

    # (iv) Use the proof from (i) and axiom 15 or 16 to prove
    # equivalence_of(Q'x[~phi(x)], Q'x[rho(x)]), which I call "Q_prime_equivalence"
    parametrized_not_phi = Formula("~", parametrized_phi)
    parametrized_rho = rho.substitute({x: Term("_")})
    axiom_15_or_16_instantiation_map = {
        "x": x,
        "y": x,
        "R": parametrized_not_phi,
        "Q": parametrized_rho,
    }
    axiom_15_or_16_line_number = proof.add_instantiated_assumption(
        axiom_15_or_16.instantiate(axiom_15_or_16_instantiation_map),
        axiom_15_or_16,
        axiom_15_or_16_instantiation_map,
    )

    Q_prime_equivalence = axiom_15_or_16.instantiate(
        axiom_15_or_16_instantiation_map
    ).second
    Q_prime_equivalence_line_number = proof.add_tautological_implication(
        Q_prime_equivalence,
        {axiom_15_or_16_line_number, not_phi_rho_equivalence_line_number},
    )

    # (v) Deduce equivalence_of(~Qx[phi(x)], Q'x[rho(x)]) as a tautological implication
    # of QN_equivalence and Q_prime_equivalence. This is the equivalence we need.
    proof.add_tautological_implication(
        equivalence_of(formula, Q_prime_x_rho),
        {Q_prime_equivalence_line_number, QN_equivalence_line_number},
    )
    return (Q_prime_x_rho, proof.qed())


def _pull_out_quantifications_from_left_across_binary_operator(
    formula: Formula,
) -> Tuple[Formula, Proof]:
    """Converts the given formula with uniquely named variables of the form
    ``'(``\ `Q1`\ `x1`\ ``[``\ `Q2`\ `x2`\ ``[``...\ `Qn`\ `xn`\ ``[``\ `inner_first`\ ``]``...\ ``]]``\ `*`\ `second`\ ``)'``
    to an equivalent formula of the form
    ``'``\ `Q'1`\ `x1`\ ``[``\ `Q'2`\ `x2`\ ``[``...\ `Q'n`\ `xn`\ ``[(``\ `inner_first`\ `*`\ `second`\ ``)]``...\ ``]]'``
    and proves the equivalence of these two formulas.

    Parameters:
        formula: formula with uniquely named variables to convert, whose root
            is a binary operator, i.e., which is of the form
            ``'(``\ `Q1`\ `x1`\ ``[``\ `Q2`\ `x2`\ ``[``...\ `Qn`\ `xn`\ ``[``\ `inner_first`\ ``]``...\ ``]]``\ `*`\ `second`\ ``)'``
            where `*` is a binary operator, `n`>=0, each `Qi` is a quantifier,
            each `xi` is a variable name, and `inner_first` does not start with
            a quantifier.

    Returns:
        A pair. The first element of the pair is a formula equivalent to the
        given formula, but of the form
        ``'``\ `Q'1`\ `x1`\ ``[``\ `Q'2`\ `x2`\ ``[``...\ `Q'n`\ `xn`\ ``[(``\ `inner_first`\ `*`\ `second`\ ``)]``...\ ``]]'``
        where each `Q'i` is a quantifier, and where the operator `*`, the `xi`
        variable names, `inner_first`, and `second` are the same as in the given
        formula. The second element of the pair is a proof of the equivalence of
        the given formula and the returned formula (i.e., a proof of
        `equivalence_of`\ ``(``\ `formula`\ ``,``\ `returned_formula`\ ``)``)
        via `~predicates.prover.Prover.AXIOMS` and
        `ADDITIONAL_QUANTIFICATION_AXIOMS`.

    Examples:
        >>> formula = Formula.parse('(Ax[Ey[R(x,y)]]&Ez[P(1,z)])')
        >>> returned_formula, proof = _pull_out_quantifications_from_left_across_binary_operator(
        ...     formula)
        >>> returned_formula
        Ax[Ey[(R(x,y)&Ez[P(1,z)])]]
        >>> proof.is_valid()
        True
        >>> proof.conclusion == equivalence_of(formula, returned_formula)
        True
        >>> proof.assumptions == Prover.AXIOMS.union(
        ...     ADDITIONAL_QUANTIFICATION_AXIOMS)
        True
    """
    assert has_uniquely_named_variables(formula)
    assert is_binary(formula.root)
    # Task 11.7a

    assumptions = set(Prover.AXIOMS).union(set(ADDITIONAL_QUANTIFICATION_AXIOMS))

    # Base case: n = 0
    if not is_quantifier(formula.first.root):
        # In this case, our formula stays the same, so the equivalence is a tautology.
        proof = Prover(assumptions)
        proof.add_tautology(equivalence_of(formula, formula))
        return (formula, proof.qed())

    # Recursive case: n > 0
    # Then the formula has the form (Qx[phi(x)]*psi) for some quantifier Q, binary
    # operator *, parametrized formula phi, formula psi, and variable name x. We
    #   (i) recurse to find an equivalent formula, rho(x), for (phi(x)*psi) and a proof
    #       of the equivalence.
    #   (ii) construct the new formula Q'x[rho(x)]. Q' will be Q unless * is ->, in which
    #       case you swap the quantifier (so Q' is A if Q is E and vice versa).
    #   (iii) instantiate a new axiom to pull out Q across * and prove
    #       equivalence_of((Qx[phi(x)]*psi), Q'x[(phi(x)*psi)])
    #   (iv) instantiate new axiom 15 or 16 and the proof from (i) to prove
    #       equivalence_of(Q'x[(phi(x)*psi)], Q'x[rho(x)]), and
    #   (v) use a tautological implication on the equivalences from (iii) and (iv) to
    #       deduce equivalence_of((Qx[phi(x)]*psi), Q'x[rho(x)]), as desired.
    Q = formula.first.root
    star = formula.root
    phi = formula.first.statement
    psi = formula.second
    phi_star_psi = Formula(star, phi, psi)
    x = formula.first.variable
    proof = Prover(assumptions, True)

    # (i) Recurse to find an equivalent formula, rho(x), for (phi(x)*psi)
    rho, phi_star_psi_equivalent_to_rho_proof = (
        _pull_out_quantifications_from_left_across_binary_operator(phi_star_psi)
    )
    phi_star_psi_rho_equivalence_line_number = proof.add_proof(
        equivalence_of(phi_star_psi, rho), phi_star_psi_equivalent_to_rho_proof
    )

    # (ii) Construct the new formula Q'x[rho(x)]
    if star == "->":
        if Q == "A":
            Q_prime = "E"
        else:
            Q_prime = "A"
    else:
        Q_prime = Q
    Q_prime_x_rho = Formula(Q_prime, x, rho)

    # (iii) Use a new axiom to get equivalence_of((Qx[phi(x)]*psi), Q'x[(phi(x)*psi)]),
    # which I call "pull_out_equivalence."
    pull_out_axiom_dict = {
        "&A": ADDITIONAL_QUANTIFICATION_AXIOMS[2],
        "&E": ADDITIONAL_QUANTIFICATION_AXIOMS[3],
        "|A": ADDITIONAL_QUANTIFICATION_AXIOMS[6],
        "|E": ADDITIONAL_QUANTIFICATION_AXIOMS[7],
        "->A": ADDITIONAL_QUANTIFICATION_AXIOMS[10],
        "->E": ADDITIONAL_QUANTIFICATION_AXIOMS[11],
    }
    pull_out_axiom = pull_out_axiom_dict[star + Q]

    parametrized_phi = phi.substitute({x: Term("_")})
    pull_out_axiom_instantiation_map = {"x": x, "Q": psi, "R": parametrized_phi}
    pull_out_equivalence_line_number = proof.add_instantiated_assumption(
        pull_out_axiom.instantiate(pull_out_axiom_instantiation_map),
        pull_out_axiom,
        pull_out_axiom_instantiation_map,
    )

    # (iv) Use axiom 15 or 16 and the proof from (i) to prove "Q_prime_equivalence",
    # equivalence_of(Q'x[(phi(x)*psi)], Q'x[rho(x)]).
    if Q_prime == "A":
        axiom_15_or_16 = ADDITIONAL_QUANTIFICATION_AXIOMS[14]
    else:
        axiom_15_or_16 = ADDITIONAL_QUANTIFICATION_AXIOMS[15]
    parametrized_phi_star_psi = phi_star_psi.substitute({x: Term("_")})
    parametrized_rho = rho.substitute({x: Term("_")})
    axiom_15_or_16_instantiation_map = {
        "x": x,
        "y": x,
        "R": parametrized_phi_star_psi,
        "Q": parametrized_rho,
    }
    axiom_15_or_16_line_number = proof.add_instantiated_assumption(
        axiom_15_or_16.instantiate(axiom_15_or_16_instantiation_map),
        axiom_15_or_16,
        axiom_15_or_16_instantiation_map,
    )
    
    Q_prime_equivalence = axiom_15_or_16.instantiate(
        axiom_15_or_16_instantiation_map
    ).second
    Q_prime_equivalence_line_number = proof.add_tautological_implication(
        Q_prime_equivalence,
        {phi_star_psi_rho_equivalence_line_number, axiom_15_or_16_line_number},
    )

    # (v) Deduce equivalence_of((Qx[phi(x)]*psi), Q'x[rho(x)]) as a tautological
    # implication of the equivalences in (iii) and (iv).
    proof.add_tautological_implication(
        equivalence_of(formula, Q_prime_x_rho),
        {pull_out_equivalence_line_number, Q_prime_equivalence_line_number},
    )
    return (Q_prime_x_rho, proof.qed())


def _pull_out_quantifications_from_right_across_binary_operator(
    formula: Formula,
) -> Tuple[Formula, Proof]:
    """Converts the given formula with uniquely named variables of the form
    ``'(``\ `first`\ `*`\ `Q1`\ `x1`\ ``[``\ `Q2`\ `x2`\ ``[``...\ `Qn`\ `xn`\ ``[``\ `inner_second`\ ``]``...\ ``]])'``
    to an equivalent formula of the form
    ``'``\ `Q'1`\ `x1`\ ``[``\ `Q'2`\ `x2`\ ``[``...\ `Q'n`\ `xn`\ ``[(``\ `first`\ `*`\ `inner_second`\ ``)]``...\ ``]]'``
    and proves the equivalence of these two formulas.

    Parameters:
        formula: formula with uniquely named variables to convert, whose root
            is a binary operator, i.e., which is of the form
            ``'(``\ `first`\ `*`\ `Q1`\ `x1`\ ``[``\ `Q2`\ `x2`\ ``[``...\ `Qn`\ `xn`\ ``[``\ `inner_second`\ ``]``...\ ``]])'``
            where `*` is a binary operator, `n`>=0, each `Qi` is a quantifier,
            each `xi` is a variable name, and `inner_second` does not start with
            a quantifier.

    Returns:
        A pair. The first element of the pair is a formula equivalent to the
        given formula, but of the form
        ``'``\ `Q'1`\ `x1`\ ``[``\ `Q'2`\ `x2`\ ``[``...\ `Q'n`\ `xn`\ ``[(``\ `first`\ `*`\ `inner_second`\ ``)]``...\ ``]]'``
        where each `Q'i` is a quantifier, and where the operator `*`, the `xi`
        variable names, `first`, and `inner_second` are the same as in the given
        formula. The second element of the pair is a proof of the equivalence of
        the given formula and the returned formula (i.e., a proof of
        `equivalence_of`\ ``(``\ `formula`\ ``,``\ `returned_formula`\ ``)``)
        via `~predicates.prover.Prover.AXIOMS` and
        `ADDITIONAL_QUANTIFICATION_AXIOMS`.

    Examples:
        >>> formula = Formula.parse('(Ax[Ey[R(x,y)]]|Ez[P(1,z)])')
        >>> returned_formula, proof = _pull_out_quantifications_from_right_across_binary_operator(
        ...     formula)
        >>> returned_formula
        Ez[(Ax[Ey[R(x,y)]]|P(1,z))]
        >>> proof.is_valid()
        True
        >>> proof.conclusion == equivalence_of(formula, returned_formula)
        True
        >>> proof.assumptions == Prover.AXIOMS.union(
        ...     ADDITIONAL_QUANTIFICATION_AXIOMS)
        True
    """
    assert has_uniquely_named_variables(formula)
    assert is_binary(formula.root)
    # Task 11.7b


def _pull_out_quantifications_across_binary_operator(
    formula: Formula,
) -> Tuple[Formula, Proof]:
    """Converts the given formula with uniquely named variables of the form
    ``'(``\ `Q1`\ `x1`\ ``[``\ `Q2`\ `x2`\ ``[``...\ `Qn`\ `xn`\ ``[``\ `inner_first`\ ``]``...\ ``]]``\ `*`\ `P1`\ `y1`\ ``[``\ `P2`\ `y2`\ ``[``...\ `Pm`\ `ym`\ ``[``\ `inner_second`\ ``]``...\ ``]])'``
    to an equivalent formula of the form
    ``'``\ `Q'1`\ `x1`\ ``[``\ `Q'2`\ `x2`\ ``[``...\ `Q'n`\ `xn`\ ``[``\ `P'1`\ `y1`\ ``[``\ `P'2`\ `y2`\ ``[``...\ `P'm`\ `ym`\ ``[(``\ `inner_first`\ `*`\ `inner_second`\ ``)]``...\ ``]]]``...\ ``]]'``
    and proves the equivalence of these two formulas.

    Parameters:
        formula: formula with uniquely named variables to convert, whose root
            is a binary operator, i.e., which is of the form
            ``'(``\ `Q1`\ `x1`\ ``[``\ `Q2`\ `x2`\ ``[``...\ `Qn`\ `xn`\ ``[``\ `inner_first`\ ``]``...\ ``]]``\ `*`\ `P1`\ `y1`\ ``[``\ `P2`\ `y2`\ ``[``...\ `Pm`\ `ym`\ ``[``\ `inner_second`\ ``]``...\ ``]])'``
            where `*` is a binary operator, `n`>=0, `m`>=0, each `Qi` and `Pi`
            is a quantifier, each `xi` and `yi` is a variable name, and neither
            `inner_first` nor `inner_second` starts with a quantifier.

    Returns:
        A pair. The first element of the pair is a formula equivalent to the
        given formula, but of the form
        ``'``\ `Q'1`\ `x1`\ ``[``\ `Q'2`\ `x2`\ ``[``...\ `Q'n`\ `xn`\ ``[``\ `P'1`\ `y1`\ ``[``\ `P'2`\ `y2`\ ``[``...\ `P'm`\ `ym`\ ``[(``\ `inner_first`\ `*`\ `inner_second`\ ``)]``...\ ``]]]``...\ ``]]'``
        where each `Q'i` and `P'i` is a quantifier, and where the operator `*`,
        the `xi` and `yi` variable names, `inner_first`, and `inner_second` are
        the same as in the given formula. The second element of the pair is a
        proof of the equivalence of the given formula and the returned formula
        (i.e., a proof of
        `equivalence_of`\ ``(``\ `formula`\ ``,``\ `returned_formula`\ ``)``)
        via `~predicates.prover.Prover.AXIOMS` and
        `ADDITIONAL_QUANTIFICATION_AXIOMS`.

    Examples:
        >>> formula = Formula.parse('(Ax[Ey[R(x,y)]]->Ez[P(1,z)])')
        >>> returned_formula, proof = _pull_out_quantifications_across_binary_operator(
        ...     formula)
        >>> returned_formula
        Ex[Ay[Ez[(R(x,y)->P(1,z))]]]
        >>> proof.is_valid()
        True
        >>> proof.conclusion == equivalence_of(formula, returned_formula)
        True
        >>> proof.assumptions == Prover.AXIOMS.union(
        ...     ADDITIONAL_QUANTIFICATION_AXIOMS)
        True
    """
    assert has_uniquely_named_variables(formula)
    assert is_binary(formula.root)
    # Task 11.8


def _to_prenex_normal_form_from_uniquely_named_variables(
    formula: Formula,
) -> Tuple[Formula, Proof]:
    """Converts the given formula with uniquely named variables to an equivalent
    formula in prenex normal form, and proves the equivalence of these two
    formulas.

    Parameters:
        formula: formula with uniquely named variables to convert.

    Returns:
        A pair. The first element of the pair is a formula equivalent to the
        given formula, but in prenex normal form. The second element of the pair
        is a proof of the equivalence of the given formula and the returned
        formula (i.e., a proof of
        `equivalence_of`\ ``(``\ `formula`\ ``,``\ `returned_formula`\ ``)``)
        via `~predicates.prover.Prover.AXIOMS` and
        `ADDITIONAL_QUANTIFICATION_AXIOMS`.

    Examples:
        >>> formula = Formula.parse('(~(Ax[Ey[R(x,y)]]->Ez[P(1,z)])|S(w))')
        >>> returned_formula, proof = _to_prenex_normal_form_from_uniquely_named_variables(
        ...     formula)
        >>> returned_formula
        Ax[Ey[Az[(~(R(x,y)->P(1,z))|S(w))]]]
        >>> proof.is_valid()
        True
        >>> proof.conclusion == equivalence_of(formula, returned_formula)
        True
        >>> proof.assumptions == Prover.AXIOMS.union(
        ...     ADDITIONAL_QUANTIFICATION_AXIOMS)
        True
    """
    assert has_uniquely_named_variables(formula)
    # Task 11.9


def to_prenex_normal_form(formula: Formula) -> Tuple[Formula, Proof]:
    """Converts the given formula to an equivalent formula in prenex normal
    form, and proves the equivalence of these two formulas.

    Parameters:
        formula: formula to convert, which contains no variable names that are
            ``z`` followed by a number.

    Returns:
        A pair. The first element of the pair is a formula equivalent to the
        given formula, but in prenex normal form. The second element of the pair
        is a proof of the equivalence of the given formula and the returned
        formula (i.e., a proof of
        `equivalence_of`\ ``(``\ `formula`\ ``,``\ `returned_formula`\ ``)``)
        via `~predicates.prover.Prover.AXIOMS` and
        `ADDITIONAL_QUANTIFICATION_AXIOMS`.

    Examples:
        >>> formula = Formula.parse('~(w=x|Aw[(Ex[(x=w&Aw[w=x])]->Ax[x=y])])')
        >>> returned_formula, proof = to_prenex_normal_form(formula)
        >>> returned_formula
        Ez58[Ez17[Az4[Ez32[~(w=x|((z17=z58&z4=z17)->z32=y))]]]]
        >>> proof.is_valid()
        True
        >>> proof.conclusion == equivalence_of(formula, returned_formula)
        True
        >>> proof.assumptions == Prover.AXIOMS.union(
        ...     ADDITIONAL_QUANTIFICATION_AXIOMS)
        True
    """
    for variable in formula.variables():
        assert not is_z_and_number(variable)
    # Task 11.10
