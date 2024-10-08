# This file is part of the materials accompanying the book
# "Mathematical Logic through Python" by Gonczarowski and Nisan,
# Cambridge University Press. Book site: www.LogicThruPython.org
# (c) Yannai A. Gonczarowski and Noam Nisan, 2017-2022
# File name: predicates/some_proofs.py

"""Some proofs in Predicate Logic."""

from predicates.syntax import *
from predicates.proofs import *
from predicates.prover import *
from predicates.deduction import *
from predicates.prenex import equivalence_of


def prove_syllogism(print_as_proof_forms: bool = False) -> Proof:
    """Proves from the assumptions:

    1. All men are mortal (``'Ax[(Man(x)->Mortal(x))]'``), and
    2. Aristotle is a man (``'Man(aristotle)'``)

    the conclusion: Aristotle is mortal (``'Mortal(aristotle)'``).

    Parameters:
        print_as_proof_forms: flag specifying whether the proof is to be printed
            in real time as it is being created.

    Returns:
        A valid proof of the above inference via
        `~predicates.prover.Prover.AXIOMS`.
    """
    prover = Prover({"Ax[(Man(x)->Mortal(x))]", "Man(aristotle)"}, print_as_proof_forms)
    step1 = prover.add_assumption("Ax[(Man(x)->Mortal(x))]")
    step2 = prover.add_instantiated_assumption(
        "(Ax[(Man(x)->Mortal(x))]->(Man(aristotle)->Mortal(aristotle)))",
        Prover.UI,
        {"R": "(Man(_)->Mortal(_))", "c": "aristotle"},
    )
    step3 = prover.add_mp("(Man(aristotle)->Mortal(aristotle))", step1, step2)
    step4 = prover.add_assumption("Man(aristotle)")
    step5 = prover.add_mp("Mortal(aristotle)", step4, step3)
    return prover.qed()


def prove_syllogism_with_universal_instantiation(
    print_as_proof_forms: bool = False,
) -> Proof:
    """Using the method `~predicates.prover.Prover.add_universal_instantiation`,
    proves from the assumptions:

    1. All men are mortal (``'Ax[(Man(x)->Mortal(x))]'``), and
    2. Aristotle is a man (``'Man(aristotle)'``)

    the conclusion: Aristotle is mortal (``'Mortal(aristotle)'``).

    Parameters:
        print_as_proof_forms: flag specifying whether the proof is to be printed
            in real time as it is being created.

    Returns:
        A valid proof, created with the help of the method
        `~predicates.prover.Prover.add_universal_instantiation`, of the above
        inference via `~predicates.prover.Prover.AXIOMS`.
    """
    prover = Prover({"Ax[(Man(x)->Mortal(x))]", "Man(aristotle)"}, print_as_proof_forms)
    step1 = prover.add_assumption("Ax[(Man(x)->Mortal(x))]")
    step2 = prover.add_universal_instantiation(
        "(Man(aristotle)->Mortal(aristotle))", step1, "aristotle"
    )
    step3 = prover.add_assumption("Man(aristotle)")
    step4 = prover.add_mp("Mortal(aristotle)", step3, step2)
    return prover.qed()


def prove_syllogism_all_all(print_as_proof_forms: bool = False) -> Proof:
    """Proves from the assumptions:

    1. All Greeks are human (``'Ax[(Greek(x)->Human(x))]'``), and
    2. All humans are mortal (``'Ax[(Human(x)->Mortal(x))]'``)

    the conclusion: All Greeks are mortal (``'Ax[(Greek(x)->Mortal(x))]'``).

    Parameters:
        print_as_proof_forms: flag specifying whether the proof is to be printed
            in real time as it is being created.

    Returns:
        A valid proof of the above inference via
        `~predicates.prover.Prover.AXIOMS`.
    """
    prover = Prover(
        {"Ax[(Greek(x)->Human(x))]", "Ax[(Human(x)->Mortal(x))]"}, print_as_proof_forms
    )
    step1 = prover.add_assumption("Ax[(Greek(x)->Human(x))]")
    step2 = prover.add_universal_instantiation("(Greek(x)->Human(x))", step1, "x")
    step3 = prover.add_assumption("Ax[(Human(x)->Mortal(x))]")
    step4 = prover.add_universal_instantiation("(Human(x)->Mortal(x))", step3, "x")
    step5 = prover.add_tautology(
        "((Greek(x)->Human(x))->((Human(x)->Mortal(x))->(Greek(x)->Mortal(x))))"
    )
    step6 = prover.add_mp(
        "((Human(x)->Mortal(x))->(Greek(x)->Mortal(x)))", step2, step5
    )
    step7 = prover.add_mp("(Greek(x)->Mortal(x))", step4, step6)
    step8 = prover.add_ug("Ax[(Greek(x)->Mortal(x))]", step7)
    return prover.qed()


def prove_syllogism_all_all_with_tautological_implication(
    print_as_proof_forms: bool = False,
) -> Proof:
    """Using the method
    `~predicates.prover.Prover.add_tautological_implication`, proves from the
    assumptions:

    1. All Greeks are human (``'Ax[(Greek(x)->Human(x))]'``), and
    2. All humans are mortal (``'Ax[(Human(x)->Mortal(x))]'``)

    the conclusion: All Greeks are mortal (``'Ax[(Greek(x)->Mortal(x))]'``).

    Parameters:
        print_as_proof_forms: flag specifying whether the proof is to be printed
            in real time as it is being created.

    Returns:
        A valid proof, created with the help of the method
        `~predicates.prover.Prover.add_tautological_implication`, of the above
        inference via `~predicates.prover.Prover.AXIOMS`.
    """
    prover = Prover(
        {"Ax[(Greek(x)->Human(x))]", "Ax[(Human(x)->Mortal(x))]"}, print_as_proof_forms
    )
    step1 = prover.add_assumption("Ax[(Greek(x)->Human(x))]")
    step2 = prover.add_universal_instantiation("(Greek(x)->Human(x))", step1, "x")
    step3 = prover.add_assumption("Ax[(Human(x)->Mortal(x))]")
    step4 = prover.add_universal_instantiation("(Human(x)->Mortal(x))", step3, "x")
    step5 = prover.add_tautological_implication("(Greek(x)->Mortal(x))", {step2, step4})
    step6 = prover.add_ug("Ax[(Greek(x)->Mortal(x))]", step5)
    return prover.qed()


def prove_syllogism_all_exists(print_as_proof_forms: bool = False) -> Proof:
    """Proves from the assumptions:

    1. All men are mortal (``'Ax[(Man(x)->Mortal(x))]'``), and
    2. Some men exist (``'Ex[Man(x)]'``)

    the conclusion: Some mortals exist (``'Ex[Mortal(x)]'``).

    Parameters:
        print_as_proof_forms: flag specifying whether the proof is to be printed
            in real time as it is being created.

    Returns:
        A valid proof of the above inference via
        `~predicates.prover.Prover.AXIOMS`.
    """
    prover = Prover({"Ax[(Man(x)->Mortal(x))]", "Ex[Man(x)]"}, print_as_proof_forms)
    step1 = prover.add_assumption("Ax[(Man(x)->Mortal(x))]")
    step2 = prover.add_assumption("Ex[Man(x)]")
    step3 = prover.add_universal_instantiation("(Man(x)->Mortal(x))", step1, "x")
    step4 = prover.add_instantiated_assumption(
        "(Mortal(x)->Ex[Mortal(x)])", Prover.EI, {"R": "Mortal(_)", "c": "x"}
    )
    step5 = prover.add_tautological_implication(
        "(Man(x)->Ex[Mortal(x)])", {step3, step4}
    )
    step6 = prover.add_ug("Ax[(Man(x)->Ex[Mortal(x)])]", step5)
    step7 = prover.add_instantiated_assumption(
        "((Ax[(Man(x)->Ex[Mortal(x)])]&Ex[Man(x)])->Ex[Mortal(x)])",
        Prover.ES,
        {"R": "Man(_)", "Q": "Ex[Mortal(x)]"},
    )
    step8 = prover.add_tautological_implication("Ex[Mortal(x)]", {step2, step6, step7})
    return prover.qed()


def prove_syllogism_all_exists_with_existential_derivation(
    print_as_proof_forms: bool = False,
) -> Proof:
    """Using the method `~predicates.prover.Prover.add_existential_derivation`,
    proves from the assumptions:

    1. All men are mortal (``'Ax[(Man(x)->Mortal(x))]'``), and
    2. Some men exist (``'Ex[Man(x)]'``)

    the conclusion: Some mortals exist (``'Ex[Mortal(x)]'``).

    Parameters:
        print_as_proof_forms: flag specifying whether the proof is to be printed
            in real time as it is being created.

    Returns:
        A valid proof, created with the help of the method
        `~predicates.prover.Prover.add_existential_derivation`, of the above
        inference via `~predicates.prover.Prover.AXIOMS`.
    """
    prover = Prover({"Ax[(Man(x)->Mortal(x))]", "Ex[Man(x)]"}, print_as_proof_forms)
    step1 = prover.add_assumption("Ax[(Man(x)->Mortal(x))]")
    step2 = prover.add_assumption("Ex[Man(x)]")
    step3 = prover.add_universal_instantiation("(Man(x)->Mortal(x))", step1, "x")
    step4 = prover.add_instantiated_assumption(
        "(Mortal(x)->Ex[Mortal(x)])", Prover.EI, {"R": "Mortal(_)", "c": "x"}
    )
    step5 = prover.add_tautological_implication(
        "(Man(x)->Ex[Mortal(x)])", {step3, step4}
    )
    step6 = prover.add_existential_derivation("Ex[Mortal(x)]", step2, step5)
    return prover.qed()


def prove_lovers(print_as_proof_forms: bool = False) -> Proof:
    """Proves from the assumptions:

    1. Everybody loves somebody (``'Ax[Ey[Loves(x,y)]]'``), and
    2. Everybody loves a lover (``'Ax[Az[Ay[(Loves(x,y)->Loves(z,x))]]]'``)

    the conclusion: Everybody loves everybody (``'Ax[Az[Loves(z,x)]]'``).

    Parameters:
        print_as_proof_forms: flag specifying whether the proof is to be printed
            in real time as it is being constructed.

    Returns:
        A valid proof of the above inference via
        `~predicates.prover.Prover.AXIOMS`.
    """
    prover = Prover(
        {"Ax[Ey[Loves(x,y)]]", "Ax[Az[Ay[(Loves(x,y)->Loves(z,x))]]]"},
        print_as_proof_forms,
    )
    # Task 10.4
    step1 = prover.add_assumption("Ax[Ey[Loves(x,y)]]")
    step2 = prover.add_assumption("Ax[Az[Ay[(Loves(x,y)->Loves(z,x))]]]")

    step3 = prover.add_universal_instantiation("Ey[Loves(x,y)]", step1, "x")
    step4 = prover.add_universal_instantiation(
        "Az[Ay[(Loves(x,y)->Loves(z,x))]]", step2, "x"
    )
    step5 = prover.add_universal_instantiation(
        "Ay[(Loves(x,y)->Loves(z,x))]", step4, "z"
    )
    step6 = prover.add_universal_instantiation("(Loves(x,y)->Loves(z,x))", step5, "y")

    step7 = prover.add_existential_derivation("Loves(z,x)", step3, step6)
    step8 = prover.add_ug("Az[Loves(z,x)]", step7)
    step9 = prover.add_ug("Ax[Az[Loves(z,x)]]", step8)
    return prover.qed()


def prove_homework(print_as_proof_forms: bool = False) -> Proof:
    """Proves from the assumptions:

    1. No homework is fun (``'~Ex[(Homework(x)&Fun(x))]'``), and
    2. Some reading is homework (``'Ex[(Homework(x)&Reading(x))]'``)

    the conclusion: Some reading is not fun (``'Ex[(Reading(x)&~Fun(x))]'``).

    Parameters:
        print_as_proof_forms: flag specifying whether the proof is to be printed
            in real time as it is being constructed.

    Returns:
        A valid proof of the above inference via
        `~predicates.prover.Prover.AXIOMS`.
    """
    prover = Prover(
        {"~Ex[(Homework(x)&Fun(x))]", "Ex[(Homework(x)&Reading(x))]"},
        print_as_proof_forms,
    )
    # Task 10.5

    # First we prove ~(Homework(x)&Fun(x)) and ((Reading(x)&~Fun(x))->Ex[(Reading(x)&~Fun(x))]) using EI
    step1 = prover.add_assumption("~Ex[(Homework(x)&Fun(x))]")
    step2 = prover.add_assumption("Ex[(Homework(x)&Reading(x))]")
    ei_map = {"c": Term("x"), "x": "x", "R": Formula.parse("(Homework(_)&Fun(_))")}
    step3 = prover.add_instantiated_assumption(  # ((Homework(x)&Fun(x))->Ex[(Homework(x)&Fun(x))])
        Prover.EI.instantiate(ei_map), Prover.EI, ei_map
    )
    step4 = prover.add_tautological_implication("~(Homework(x)&Fun(x))", {step1, step3})
    ei_map = {"c": Term("x"), "x": "x", "R": Formula.parse("(Reading(_)&~Fun(_))")}
    step5 = prover.add_instantiated_assumption(  # ((Reading(x)&~Fun(x))->Ex[(Reading(x)&~Fun(x))])
        Prover.EI.instantiate(ei_map), Prover.EI, ei_map
    )

    # Now we add in a tautology, an implication of which is ((Homework(x)&Reading(x))->Ex[(Reading(x)&~Fun(x))])
    step6 = prover.add_tautology(
        "((Homework(x)&Reading(x))->(~(Homework(x)&Fun(x))->(Reading(x)&~Fun(x))))"
    )
    step7 = prover.add_tautological_implication(
        "((Homework(x)&Reading(x))->Ex[(Reading(x)&~Fun(x))])", {step4, step5, step6}
    )
    step8 = prover.add_existential_derivation("Ex[(Reading(x)&~Fun(x))]", step2, step7)
    return prover.qed()


#: The three group axioms
GROUP_AXIOMS = frozenset(
    {"plus(0,x)=x", "plus(minus(x),x)=0", "plus(plus(x,y),z)=plus(x,plus(y,z))"}
)


def prove_group_right_neutral(
    stop_before_flipped_equality: bool,
    stop_before_free_instantiation: bool,
    stop_before_substituted_equality: bool,
    stop_before_chained_equality: bool,
    print_as_proof_forms: bool = False,
) -> Proof:
    """Proves from the group axioms that x+0=x (``'plus(x,0)=x'``).

    Parameters:
        stop_before_flipped_equality: flag specifying to stop proving just
            before the first call to
            `~predicates.prover.Prover.add_flipped_equality` and to return the
            prefix of the proof created up to that point.
        stop_before_free_instantiation: flag specifying to stop proving just
            before the first call to
            `~predicates.prover.Prover.add_free_instantiation` and to return the
            prefix of the proof created up to that point.
        stop_before_substituted_equality: flag specifying stop proving just
            before the first call to
            `~predicates.prover.Prover.add_substituted_equality` and to return
            the prefix of the proof created up to that point.
        stop_before_chained_equality: flag specifying to stop proving just
            before the first call to
            `~predicates.prover.Prover.add_chained_equality` and to return the
            prefix of the proof created up to that point.
        print_as_proof_forms: flag specifying whether the proof is to be printed
            in real time as it is being created.

    Returns:
        A valid proof of the above inference via
        `~predicates.prover.Prover.AXIOMS`.
    """
    prover = Prover(GROUP_AXIOMS, print_as_proof_forms)
    zero = prover.add_assumption("plus(0,x)=x")
    negation = prover.add_assumption("plus(minus(x),x)=0")
    associativity = prover.add_assumption("plus(plus(x,y),z)=plus(x,plus(y,z))")
    if stop_before_flipped_equality:
        return prover.qed()
    flipped_zero = prover.add_flipped_equality("x=plus(0,x)", zero)
    flipped_negation = prover.add_flipped_equality("0=plus(minus(x),x)", negation)
    flipped_associativity = prover.add_flipped_equality(
        "plus(x,plus(y,z))=plus(plus(x,y),z)", associativity
    )
    if stop_before_free_instantiation:
        return prover.qed()
    step7 = prover.add_free_instantiation(
        "0=plus(minus(minus(x)),minus(x))", flipped_negation, {"x": "minus(x)"}
    )
    step8 = prover.add_flipped_equality("plus(minus(minus(x)),minus(x))=0", step7)
    step9 = prover.add_free_instantiation(
        "plus(plus(minus(minus(x)),minus(x)),x)="
        "plus(minus(minus(x)),plus(minus(x),x))",
        associativity,
        {"x": "minus(minus(x))", "y": "minus(x)", "z": "x"},
    )
    step10 = prover.add_free_instantiation("plus(0,0)=0", zero, {"x": "0"})
    step11 = prover.add_free_instantiation(
        "plus(x,0)=plus(0,plus(x,0))", flipped_zero, {"x": "plus(x,0)"}
    )
    step12 = prover.add_free_instantiation(
        "plus(0,plus(x,0))=plus(plus(0,x),0)",
        flipped_associativity,
        {"x": "0", "y": "x", "z": "0"},
    )
    if stop_before_substituted_equality:
        return prover.qed()
    step13 = prover.add_substituted_equality(
        "plus(plus(0,x),0)=plus(plus(plus(minus(minus(x)),minus(x)),x),0)",
        step7,
        "plus(plus(_,x),0)",
    )
    step14 = prover.add_substituted_equality(
        "plus(plus(plus(minus(minus(x)),minus(x)),x),0)="
        "plus(plus(minus(minus(x)),plus(minus(x),x)),0)",
        step9,
        "plus(_,0)",
    )
    step15 = prover.add_substituted_equality(
        "plus(plus(minus(minus(x)),plus(minus(x),x)),0)="
        "plus(plus(minus(minus(x)),0),0)",
        negation,
        "plus(plus(minus(minus(x)),_),0)",
    )
    step16 = prover.add_free_instantiation(
        "plus(plus(minus(minus(x)),0),0)=plus(minus(minus(x)),plus(0,0))",
        associativity,
        {"x": "minus(minus(x))", "y": "0", "z": "0"},
    )
    step17 = prover.add_substituted_equality(
        "plus(minus(minus(x)),plus(0,0))=plus(minus(minus(x)),0)",
        step10,
        "plus(minus(minus(x)),_)",
    )
    step18 = prover.add_substituted_equality(
        "plus(minus(minus(x)),0)=plus(minus(minus(x)),plus(minus(x),x))",
        flipped_negation,
        "plus(minus(minus(x)),_)",
    )
    step19 = prover.add_free_instantiation(
        "plus(minus(minus(x)),plus(minus(x),x))="
        "plus(plus(minus(minus(x)),minus(x)),x)",
        flipped_associativity,
        {"x": "minus(minus(x))", "y": "minus(x)", "z": "x"},
    )
    step20 = prover.add_substituted_equality(
        "plus(plus(minus(minus(x)),minus(x)),x)=plus(0,x)", step8, "plus(_,x)"
    )
    if stop_before_chained_equality:
        return prover.qed()
    step21 = prover.add_chained_equality(
        "plus(x,0)=x",
        [
            step11,
            step12,
            step13,
            step14,
            step15,
            step16,
            step17,
            step18,
            step19,
            step20,
            zero,
        ],
    )
    return prover.qed()


def prove_group_unique_zero(print_as_proof_forms: bool = False) -> Proof:
    """Proves from the group axioms and from the assumption a+c=a
    (``'plus(a,c)=a'``) that c=0 (``'c=0'``).

    Parameters:
        print_as_proof_forms: flag specifying whether the proof is to be printed
            in real time as it is being created.

    Returns:
        A valid proof of the above inference via
        `~predicates.prover.Prover.AXIOMS`.
    """
    prover = Prover(GROUP_AXIOMS.union({"plus(a,c)=a"}), print_as_proof_forms)
    # Task 10.10
    step1 = prover.add_assumption("plus(a,c)=a")
    prover.cancel_in_group(step1)
    return prover.qed()


#: The six field axioms
FIELD_AXIOMS = frozenset(
    GROUP_AXIOMS.union(
        {
            "plus(x,y)=plus(y,x)",
            "times(x,1)=x",
            "times(x,y)=times(y,x)",
            "times(times(x,y),z)=times(x,times(y,z))",
            "(~x=0->Ey[times(y,x)=1])",
            "times(x,plus(y,z))=plus(times(x,y),times(x,z))",
        }
    )
)


def prove_field_zero_multiplication(print_as_proof_forms: bool = False) -> Proof:
    """Proves from the field axioms that 0*x=0 (``'times(0,x)=0'``).

    Parameters:
        print_as_proof_forms: flag specifying whether the proof is to be printed
            in real time as it is being created.

    Returns:
        A valid proof of the above inference via
        `~predicates.prover.Prover.AXIOMS`.
    """
    prover = Prover(FIELD_AXIOMS, print_as_proof_forms)
    # Task 10.11
    step1 = prover.add_assumption("times(x,plus(y,z))=plus(times(x,y),times(x,z))")
    step2 = prover.add_assumption("times(x,y)=times(y,x)")
    step3 = prover.add_assumption("plus(0,x)=x")

    # First we prove times(x,0)=plus(times(x,0),times(x,0))
    step5 = prover.add_free_instantiation(
        "times(x,plus(0,0))=plus(times(x,0),times(x,0))",
        step1,
        {"x": "x", "y": "0", "z": "0"},
    )
    step6 = prover.add_free_instantiation("plus(0,0)=0", step3, {"x": "0"})
    step7 = prover.add_substituted_equality(
        "times(x,plus(0,0))=times(x,0)", step6, "times(x,_)"
    )
    step8 = prover.add_flipped_equality("times(x,0)=times(x,plus(0,0))", step7)
    step9 = prover._add_chaining_of_two_equalities(
        step8, step5
    )  # times(x,0)=plus(times(x,0),times(x,0))
    step10 = prover.add_flipped_equality(
        "plus(times(x,0),times(x,0))=times(x,0)", step9
    )
    step11 = prover.cancel_in_group(step10)  # times(x,0)=0
    step12 = prover.add_free_instantiation(
        "times(0,x)=times(x,0)", step2, {"x": "0", "y": "x"}
    )
    step13 = prover._add_chaining_of_two_equalities(step12, step11)  # times(0,x)=0
    return prover.qed()


#: Axiom schema of induction
INDUCTION_AXIOM = Schema(Formula.parse("((R(0)&Ax[(R(x)->R(s(x)))])->Ax[R(x)])"), {"R"})
#: The seven axioms of Peano arithmetic
PEANO_AXIOMS = frozenset(
    {
        "(s(x)=s(y)->x=y)",
        "~s(x)=0",
        "plus(x,0)=x",
        "plus(x,s(y))=s(plus(x,y))",
        "times(x,0)=0",
        "times(x,s(y))=plus(times(x,y),x)",
        INDUCTION_AXIOM,
    }
)


def prove_peano_left_neutral(print_as_proof_forms: bool = False) -> Proof:
    """Proves from the axioms of Peano arithmetic that 0+x=x
    (``'plus(0,x)=x'``).

    Parameters:
        print_as_proof_forms: flag specifying whether the proof is to be printed
            in real time as it is being created.

    Returns:
        A valid proof of the above inference via
        `~predicates.prover.Prover.AXIOMS`.
    """
    prover = Prover(PEANO_AXIOMS, print_as_proof_forms)
    # Task 10.12
    # Base case: 0+0=0
    step1 = prover.add_assumption("plus(x,0)=x")
    step2 = prover.add_free_instantiation("plus(0,0)=0", step1, {"x": "0"})

    # Induction step: (0+x=x->0+s(x)=s(x))
    # We start by proving (0+x=x->s(0+x)=s(x))
    c = Term.parse("plus(0,x)")
    d = Term("x")
    r = Formula.parse("s(plus(0,x))=s(_)")
    me_instantiation_map = {"c": c, "d": d, "R": r}
    step3 = prover.add_instantiated_assumption(  # (0+x=x->(s(0+x)=s(0+x)->s(0+x)=s(x)))
        Prover.ME.instantiate(me_instantiation_map), Prover.ME, me_instantiation_map
    )
    step4 = prover.add_instantiated_assumption(
        "s(plus(0,x))=s(plus(0,x))", Prover.RX, {"c": Term.parse("s(plus(0,x))")}
    )
    step5 = prover.add_tautological_implication(
        "(plus(0,x)=x->s(plus(0,x))=s(x))", {step3, step4}
    )  # (0+x=x->s(0+x)=s(x))
    # Now we use that s(0+x)=0+s(x) to get (0+x=x->0+s(x)=s(x)) as desired
    step6 = prover.add_assumption("plus(x,s(y))=s(plus(x,y))")
    step7 = prover.add_free_instantiation(
        "plus(0,s(x))=s(plus(0,x))", step6, {"x": "0", "y": "x"}
    )
    step8 = prover.add_flipped_equality("s(plus(0,x))=plus(0,s(x))", step7)
    c = Term.parse("s(plus(0,x))")
    d = Term.parse("plus(0,s(x))")
    r = Formula.parse("(plus(0,x)=x->_=s(x))")
    me_instantiation_map = {"c": c, "d": d, "R": r}
    step9 = prover.add_instantiated_assumption(
        Prover.ME.instantiate(me_instantiation_map), Prover.ME, me_instantiation_map
    )  # (s(0+x)=0+s(x)->((0+x=x->s(0+x)=s(x))->(0+x=x->0+s(x)=s(x))))
    step10 = prover.add_mp(
        prover._lines[step9].formula.second, step8, step9
    )  # ((0+x=x->s(0+x)=s(x))->(0+x=x->0+s(x)=s(x)))
    step11 = prover.add_mp(
        prover._lines[step10].formula.second, step5, step10
    )  # (0+x=x->0+s(x)=s(x))

    # Now that the induction step is completed, we need only use the axiom schema of induction.
    step12 = prover.add_ug(
        Formula("A", "x", prover._lines[step11].formula), step11
    )  # Ax[(0+x=x->0+s(x)=s(x))]
    conjunction = Formula(
        "&", prover._lines[step2].formula, prover._lines[step12].formula
    )
    step13 = prover.add_tautological_implication(
        conjunction, {step2, step12}
    )  # (0+0=0&Ax[(0+x=x->0+s(x)=s(x))])
    induction_instantation_map = {"R": Formula.parse("plus(0,_)=_")}
    step14 = prover.add_instantiated_assumption(
        INDUCTION_AXIOM.instantiate(induction_instantation_map),
        INDUCTION_AXIOM,
        induction_instantation_map,
    )  # ((0+0=0&Ax[(0+x=x->0+s(x)=s(x))])->Ax[0+x=x])
    step15 = prover.add_mp("Ax[plus(0,x)=x]", step13, step14)
    step16 = prover.add_universal_instantiation("plus(0,x)=x", step15, "x")
    return prover.qed()


#: Axiom schema of (unrestricted) comprehension
COMPREHENSION_AXIOM = Schema(
    Formula.parse("Ey[Ax[((In(x,y)->R(x))&(R(x)->In(x,y)))]]"), {"R"}
)


def prove_russell_paradox(print_as_proof_forms: bool = False) -> Proof:
    """Proves from the axioms schema of unrestricted comprehension the
    contradiction ``'(z=z&~z=z)'``.

    Parameters:
        print_as_proof_forms: flag specifying whether the proof is to be printed
            in real time as it is being created.

    Returns:
        A valid proof of the above inference via
        `~predicates.prover.Prover.AXIOMS`.
    """
    prover = Prover({COMPREHENSION_AXIOM}, print_as_proof_forms)
    # Task 10.13

    # Instantiate the comprehension axiom with R(x) = ~In(x,x).
    step1 = prover.add_instantiated_assumption(
        COMPREHENSION_AXIOM.instantiate({"R": Formula.parse("~In(_,_)")}),
        COMPREHENSION_AXIOM,
        {"R": Formula.parse("~In(_,_)")},
    )

    # Now use UI to get (Ax[((In(x,y)->~In(x,x))&(~In(x,x)->In(x,y)))]->((In(y,y)->~In(y,y))&(~In(y,y)->In(y,y))))
    generalized_comprehension_statement = prover._lines[
        step1
    ].formula.statement  # Ax[((In(x,y)->~In(x,x))&(~In(x,x)->In(x,y)))]
    ui_map = {
        "R": generalized_comprehension_statement.statement.substitute(
            {"x": Term("_")}, {}
        ),
        "x": "x",
        "c": Term("y"),
    }
    step2 = prover.add_instantiated_assumption(
        Prover.UI.instantiate(ui_map), Prover.UI, ui_map
    )

    # The consequent of the above formula is a contradiction, so it is a tautology that it implies our desired conclusion.
    step3 = prover.add_tautology(
        "(((In(y,y)->~In(y,y))&(~In(y,y)->In(y,y)))->(z=z&~z=z))"
    )
    step4 = prover.add_tautological_implication(
        Formula("->", generalized_comprehension_statement, Formula.parse("(z=z&~z=z)")),
        {step2, step3},
    )

    # Finish with an existential derivation:
    # Ey[Ax[((In(x,y)->~In(x,x))&(~In(x,x)->In(x,y)))]] and (Ax[((In(x,y)->~In(x,x))&(~In(x,x)->In(x,y)))]->(z=z&~z=z))
    # imply (z=z&~z=z).
    step5 = prover.add_existential_derivation(Formula.parse("(z=z&~z=z)"), step1, step4)
    return prover.qed()


def _prove_not_exists_not_implies_all(
    variable: str, formula: Formula, print_as_proof_forms: bool = False
) -> Proof:
    """Proves that
    ``'(~E``\ `variable`\ ``[~``\ `formula`\ ``]->A``\ `variable`\ ``[``\ `formula`\ ``])'``.

    Parameters:
        variable: variable name for the quantifications in the formula to be
            proven.
        formula: statement to be universally quantified, and whose negation is
            to be existentially quantified, in the formula to be proven.
        print_as_proof_forms: flag specifying whether the proof is to be printed
            in real time as it is being created.

    Returns:
        A valid proof of the above formula via
        `~predicates.prover.Prover.AXIOMS`.
    """
    assert is_variable(variable)
    # Optional Task 11.4a

    phi = formula
    x = variable

    # We use the deduction theorem by assuming "assumption" = ~Ex[~phi(x)] and proving
    # Ax[phi(x)]. Then we instantiate EI as (~phi(x)->Ex[~phi(x)]) and deduce phi(x)
    # as a tautological implication of this and assumption. Once we use UG, we're done!
    assumption = Formula("~", Formula("E", x, Formula("~", phi)))
    assumptions = set(Prover.AXIOMS)
    assumptions.add(assumption)
    proof = Prover(assumptions, print_as_proof_forms)
    assumption_line_number = proof.add_assumption(assumption)

    parametrized_phi = phi.substitute({x: Term("_")})
    EI_instantiation_map = {"R": Formula("~", parametrized_phi), "c": Term(x), "x": x}
    EI_line_number = proof.add_instantiated_assumption(
        Prover.EI.instantiate(EI_instantiation_map), Prover.EI, EI_instantiation_map
    )

    phi_line_number = proof.add_tautological_implication(
        phi, {assumption_line_number, EI_line_number}
    )
    proof.add_ug(Formula("A", x, phi), phi_line_number)
    return remove_assumption(proof.qed(), assumption, print_as_proof_forms)


def _prove_exists_not_implies_not_all(
    variable: str, formula: Formula, print_as_proof_forms: bool = False
) -> Proof:
    """Proves that
    ``'(E``\ `variable`\ ``[~``\ `formula`\ ``]->~A``\ `variable`\ ``[``\ `formula`\ ``])'``.

    Parameters:
        variable: variable name for the quantifications in the formula to be
            proven.
        formula: statement to be universally quantified, and whose negation is
            to be existentially quantified, in the formula to be proven.
        print_as_proof_forms: flag specifying whether the proof is to be printed
            in real time as it is being created.

    Returns:
        A valid proof of the above formula via
        `~predicates.prover.Prover.AXIOMS`.
    """
    assert is_variable(variable)
    # Optional Task 11.4b

    phi = formula
    x = variable

    # We use the deduction theorem by assuming Ex[~phi(x)] and proving ~Ax[phi(x)], which
    # I call "consequent". We then instantiate UI as (Ax[phi(x)]->phi(x)), which
    # tautologically implies (~phi(x)->~Ax[phi(x)]), which I call "conditional". We can
    # use this with the assumption in an existential derivation to finish.

    assumption = Formula("E", x, Formula("~", phi))
    assumptions = set(Prover.AXIOMS)
    assumptions.add(assumption)
    proof = Prover(assumptions, print_as_proof_forms)
    assumption_line_number = proof.add_assumption(assumption)

    parametrized_phi = phi.substitute({x: Term("_")})
    UI_instantiation_map = {"R": parametrized_phi, "x": x, "c": Term(x)}
    UI_line_number = proof.add_instantiated_assumption(
        Prover.UI.instantiate(UI_instantiation_map), Prover.UI, UI_instantiation_map
    )

    consequent = Formula("~", Formula("A", x, phi))
    conditional = Formula("->", Formula("~", phi), consequent)
    conditional_line_number = proof.add_tautological_implication(
        conditional, {UI_line_number}
    )

    proof.add_existential_derivation(
        consequent, assumption_line_number, conditional_line_number
    )
    return remove_assumption(proof.qed(), assumption, print_as_proof_forms)


def prove_not_all_iff_exists_not(
    variable: str, formula: Formula, print_as_proof_forms: bool = False
) -> Proof:
    """Proves that
    `equivalence_of`\ ``('(~A``\ `variable`\ ``[``\ `formula`\ ``]', 'E``\ `variable`\ ``[~``\ `formula`\ ``]')``.

    Parameters:
        variable: variable name for the quantifications in the formula to be
            proven.
        formula: statement to be universally quantified, and whose negation is
            to be existentially quantified, in the formula to be proven.
        print_as_proof_forms: flag specifying whether the proof is to be printed
            in real time as it is being created.

    Returns:
        A valid proof of the above formula via
        `~predicates.prover.Prover.AXIOMS`.
    """
    assert is_variable(variable)
    # Optional Task 11.4c

    # We add the two proofs done in parts (a) and (b), and deduce the equivalence with
    # a tautological implication.

    proof = Prover(Prover.AXIOMS, print_as_proof_forms)
    first_direction = _prove_not_exists_not_implies_all(variable, formula)
    second_direction = _prove_exists_not_implies_not_all(variable, formula)

    first_line_number = proof.add_proof(first_direction.conclusion, first_direction)
    second_line_number = proof.add_proof(second_direction.conclusion, second_direction)

    proof.add_tautological_implication(
        equivalence_of(
            Formula("~", Formula("A", variable, formula)),
            Formula("E", variable, Formula("~", formula)),
        ),
        {first_line_number, second_line_number},
    )
    return proof.qed()
