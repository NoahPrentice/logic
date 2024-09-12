# This file is part of the materials accompanying the book
# "Mathematical Logic through Python" by Gonczarowski and Nisan,
# Cambridge University Press. Book site: www.LogicThruPython.org
# (c) Yannai A. Gonczarowski and Noam Nisan, 2017-2022
# File name: propositions/soundness.py

"""Programmatic proof of the soundness of Propositional Logic."""

from typing import Tuple

from propositions.syntax import *
from propositions.semantics import *
from propositions.proofs import *


def rule_nonsoundness_from_specialization_nonsoundness(
    general: InferenceRule, specialization: InferenceRule, model: Model
) -> Model:
    """Demonstrates the non-soundness of the given general inference rule given
    an example of the non-soundness of the given specialization of this rule.

    Parameters:
        general: inference rule to the soundness of which to find a
            counterexample.
        specialization: non-sound specialization of `general`.
        model: model in which `specialization` does not hold.

    Returns:
        A model in which `general` does not hold.
    """
    assert specialization.is_specialization_of(general)
    assert not evaluate_inference(specialization, model)
    # Task 4.9

    # We simply need to find the specialization map and build the general model from the
    # specialization model.
    specialization_map = general.specialization_map(specialization)
    general_model = dict()
    for variable in general.variables():
        general_model[variable] = evaluate(specialization_map[variable], model)
    return general_model


def nonsound_rule_of_nonsound_proof(
    proof: Proof, model: Model
) -> Tuple[InferenceRule, Model]:
    """Finds a non-sound inference rule used by the given valid proof of a
    non-sound inference rule, and demonstrates the non-soundness of the former
    rule.

    Parameters:
        proof: valid proof of a non-sound inference rule.
        model: model in which the inference rule proved by the given proof does
            not hold.

    Returns:
        A pair of a non-sound inference rule used in the given proof and a model
        in which this rule does not hold.
    """
    assert proof.is_valid()
    assert not evaluate_inference(proof.statement, model)
    # Task 4.10

    # The first line that is false is our culprit. We find the model for the general
    # inference rule using our solution to task 4.9.
    for line_number in range(len(proof.lines)):
        line = proof.lines[line_number]
        if not evaluate(line.formula, model):
            general_model = rule_nonsoundness_from_specialization_nonsoundness(
                line.rule, proof.rule_for_line(line_number), model
            )
            return (line.rule, general_model)
