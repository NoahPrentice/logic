# This file is part of the materials accompanying the book
# "Mathematical Logic through Python" by Gonczarowski and Nisan,
# Cambridge University Press. Book site: www.LogicThruPython.org
# (c) Yannai A. Gonczarowski and Noam Nisan, 2017-2022
# File name: propositions/some_proofs.py

"""Some proofs in Propositional Logic."""

from propositions.syntax import *
from propositions.proofs import *
from propositions.axiomatic_systems import *
from propositions.deduction import *

# Some inference rules that only use conjunction.

#: Conjunction introduction inference rule
A_RULE = InferenceRule([Formula.parse("x"), Formula.parse("y")], Formula.parse("(x&y)"))
#: Conjunction elimination (right) inference rule
AE1_RULE = InferenceRule([Formula.parse("(x&y)")], Formula.parse("y"))
#: Conjunction elimination (left) inference rule
AE2_RULE = InferenceRule([Formula.parse("(x&y)")], Formula.parse("x"))


def prove_and_commutativity() -> Proof:
    """Proves ``'(q&p)'`` from ``'(p&q)'`` via `A_RULE`, `AE1_RULE`, and
    `AE2_RULE`.

    Returns:
        A valid proof of ``'(q&p)'`` from the single assumption ``'(p&q)'`` via
        the inference rules `A_RULE`, `AE1_RULE`, and `AE2_RULE`.
    """
    # Task 4.7

    statement = InferenceRule([Formula.parse("(p&q)")], Formula.parse("(q&p)"))
    rules = [A_RULE, AE1_RULE, AE2_RULE]
    lines = [
        Proof.Line(Formula.parse("(p&q)")),
        Proof.Line(Formula.parse("p"), AE2_RULE, [0]),
        Proof.Line(Formula.parse("q"), AE1_RULE, [0]),
        Proof.Line(Formula.parse("(q&p)"), A_RULE, [2, 1]),
    ]
    return Proof(statement, rules, lines)


def prove_I0() -> Proof:
    """Proves `~propositions.axiomatic_systems.I0` via
    `~propositions.axiomatic_systems.MP`, `~propositions.axiomatic_systems.I1`,
    and `~propositions.axiomatic_systems.D`.

    Returns:
        A valid proof of `~propositions.axiomatic_systems.I0` via the inference
        rules `~propositions.axiomatic_systems.MP`,
        `~propositions.axiomatic_systems.I1`, and
        `~propositions.axiomatic_systems.D`.
    """
    # Task 4.8

    statement = I0
    rules = [MP, I1, D]
    lines = [
        Proof.Line(Formula.parse("(p->(p->p))"), I1, []),
        Proof.Line(Formula.parse("(p->((p->p)->p))"), I1, []),
        Proof.Line(Formula.parse("((p->((p->p)->p))->((p->(p->p))->(p->p)))"), D, []),
        Proof.Line(Formula.parse("((p->(p->p))->(p->p))"), MP, [1, 2]),
        Proof.Line(Formula.parse("(p->p)"), MP, [0, 3]),
    ]
    return Proof(statement, rules, lines)


#: Hypothetical syllogism
HS = InferenceRule(
    [Formula.parse("(p->q)"), Formula.parse("(q->r)")], Formula.parse("(p->r)")
)


def prove_hypothetical_syllogism() -> Proof:
    """Proves `HS` via `~propositions.axiomatic_systems.MP`,
    `~propositions.axiomatic_systems.I0`, `~propositions.axiomatic_systems.I1`,
    and `~propositions.axiomatic_systems.D`.

    Returns:
        A valid proof of `HS` via the inference rules
        `~propositions.axiomatic_systems.MP`,
        `~propositions.axiomatic_systems.I0`,
        `~propositions.axiomatic_systems.I1`, and
        `~propositions.axiomatic_systems.D`.
    """
    # Task 5.5

    # By the Deduction Theorem, we can prove HS by instead taking our assumptions, adding p, and proving r.
    statement = InferenceRule(
        [Formula.parse("(p->q)"), Formula.parse("(q->r)"), Formula("p")], Formula("r")
    )
    rules = [MP, I0, I1, D]
    lines = [
        Proof.Line(Formula("p")),
        Proof.Line(Formula.parse("(p->q)")),
        Proof.Line(Formula("q"), MP, [0, 1]),
        Proof.Line(Formula.parse("(q->r)")),
        Proof.Line(Formula("r"), MP, [2, 3]),
    ]
    proof = Proof(statement, rules, lines)
    return remove_assumption(proof)


def prove_I2() -> Proof:
    """Proves `~propositions.axiomatic_systems.I2` via
    `~propositions.axiomatic_systems.MP`, `~propositions.axiomatic_systems.I0`,
    `~propositions.axiomatic_systems.I1`, `~propositions.axiomatic_systems.D`,
    and `~propositions.axiomatic_systems.N`.

    Returns:
        A valid proof of `~propositions.axiomatic_systems.I2` via the inference
        rules `~propositions.axiomatic_systems.MP`,
        `~propositions.axiomatic_systems.I0`,
        `~propositions.axiomatic_systems.I1`,
        `~propositions.axiomatic_systems.D`, and
        `~propositions.axiomatic_systems.N`.
    """
    # Optional Task 6.7a

    # We can make our life easier by using HS and then removing it by inlining its proof.
    rules = {MP, I0, I1, D, N, HS}
    lines = [
        Proof.Line(Formula.parse("(~p->(~q->~p))"), I1, ()),
        Proof.Line(Formula.parse("((~q->~p)->(p->q))"), N, ()),
        Proof.Line(Formula.parse("(~p->(p->q))"), HS, (0, 1)),
    ]
    return inline_proof(Proof(I2, rules, lines), prove_hypothetical_syllogism())


#: Double-negation elimination
_NNE = InferenceRule([], Formula.parse("(~~p->p)"))


def _prove_NNE() -> Proof:
    """Proves `_NNE` via `~propositions.axiomatic_systems.MP`,
    `~propositions.axiomatic_systems.I0`, `~propositions.axiomatic_systems.I1`,
    `~propositions.axiomatic_systems.D`, and
    `~propositions.axiomatic_systems.N`.

    Returns:
        A valid proof of `_NNE` via the inference rules
        `~propositions.axiomatic_systems.MP`,
        `~propositions.axiomatic_systems.I0`,
        `~propositions.axiomatic_systems.I1`,
        `~propositions.axiomatic_systems.D`, and
        `~propositions.axiomatic_systems.N`.
    """
    # Optional Task 6.7b

    # (1) build a proof of p with ~~p as an assumption, using HS.
    statement = InferenceRule((Formula.parse("~~p"),), Formula("p"))
    rules = {MP, I0, I1, D, N, HS}
    lines = [
        Proof.Line(Formula.parse("~~p")),
        Proof.Line(Formula.parse("(~~p->(~~~~p->~~p))"), I1, ()),
        Proof.Line(Formula.parse("((~~~~p->~~p)->(~p->~~~p))"), N, ()),
        Proof.Line(Formula.parse("(~~p->(~p->~~~p))"), HS, (1, 2)),
        Proof.Line(Formula.parse("((~p->~~~p)->(~~p->p))"), N, ()),
        Proof.Line(Formula.parse("(~~p->(~~p->p))"), HS, (3, 4)),
        Proof.Line(Formula.parse("(~~p->p)"), MP, (0, 5)),
        Proof.Line(Formula("p"), MP, (0, 6)),
    ]

    # (2) Remove HS as a rule using inline_proof
    proof = inline_proof(Proof(statement, rules, lines), prove_hypothetical_syllogism())

    # (3) Turn the proof of {~~p}|-p into a proof of |-(~~p->p) using the deduction
    # theorem.
    return remove_assumption(proof)


def prove_NN() -> Proof:
    """Proves `~propositions.axiomatic_systems.NN` via
    `~propositions.axiomatic_systems.MP`, `~propositions.axiomatic_systems.I0`,
    `~propositions.axiomatic_systems.I1`, `~propositions.axiomatic_systems.D`,
    and `~propositions.axiomatic_systems.N`.

    Returns:
        A valid proof of `~propositions.axiomatic_systems.NN` via the inference
        rules `~propositions.axiomatic_systems.MP`,
        `~propositions.axiomatic_systems.I0`,
        `~propositions.axiomatic_systems.I1`,
        `~propositions.axiomatic_systems.D`, and
        `~propositions.axiomatic_systems.N`.
    """
    # Optional Task 6.7c

    # We use _NNE and then remove it using inline_proof.
    rules = {MP, I0, I1, D, N, _NNE}
    lines = [
        Proof.Line(Formula.parse("(~~~p->~p)"), _NNE, ()),
        Proof.Line(Formula.parse("((~~~p->~p)->(p->~~p))"), N, ()),
        Proof.Line(Formula.parse("(p->~~p)"), MP, (0, 1)),
    ]
    return inline_proof(Proof(NN, rules, lines), _prove_NNE())


#: Contraposition
_CP = InferenceRule([], Formula.parse("((p->q)->(~q->~p))"))


def _prove_CP() -> Proof:
    """Proves `_CP` via `~propositions.axiomatic_systems.MP`,
    `~propositions.axiomatic_systems.I0`, `~propositions.axiomatic_systems.I1`,
    `~propositions.axiomatic_systems.D`, and
    `~propositions.axiomatic_systems.N`.

    Returns:
        A valid proof of `_CP` via the inference rules
        `~propositions.axiomatic_systems.MP`,
        `~propositions.axiomatic_systems.I0`,
        `~propositions.axiomatic_systems.I1`,
        `~propositions.axiomatic_systems.D`, and
        `~propositions.axiomatic_systems.N`.
    """
    # Optional Task 6.7d

    # (1) Build a proof of {(p->q), ~~p}|-~~q using _NNE and NN
    statement = InferenceRule(
        (Formula.parse("(p->q)"), Formula.parse("~~p")), Formula.parse("~~q")
    )
    rules = {MP, I0, I1, D, N, _NNE, NN}
    lines = [
        Proof.Line(Formula.parse("(p->q)")),
        Proof.Line(Formula.parse("~~p")),
        Proof.Line(Formula.parse("(~~p->p)"), _NNE, ()),
        Proof.Line(Formula("p"), MP, (1, 2)),
        Proof.Line(Formula("q"), MP, (3, 0)),
        Proof.Line(Formula.parse("(q->~~q)"), NN, ()),
        Proof.Line(Formula.parse("~~q"), MP, (4, 5)),
    ]
    proof = Proof(statement, rules, lines)

    # (2) Use the deduction theorem to get a proof of |-((p->q)->(~~p->q))
    proof = remove_assumption(remove_assumption(proof))

    # (3) Deduce ((p->q)->(~q->~p)) using HS
    proof_lines = list(proof.lines)
    line_number = len(proof.lines)
    new_lines = [
        Proof.Line(Formula.parse("((~~p->~~q)->(~q->~p))"), N, ()),
        Proof.Line(
            Formula.parse("((p->q)->(~q->~p))"), HS, (line_number - 1, line_number)
        ),
    ]
    rules.add(HS)
    proof_lines.extend(new_lines)
    proof = Proof(_CP, rules, proof_lines)

    # (4) Get rid of _NNE, NN, and HS.
    proof = inline_proof(proof, _prove_NNE())
    proof = inline_proof(proof, prove_NN())
    return inline_proof(proof, prove_hypothetical_syllogism())


def prove_NI() -> Proof:
    """Proves `~propositions.axiomatic_systems.NI` via
    `~propositions.axiomatic_systems.MP`, `~propositions.axiomatic_systems.I0`,
    `~propositions.axiomatic_systems.I1`, `~propositions.axiomatic_systems.D`,
    and `~propositions.axiomatic_systems.N`.

    Returns:
        A valid proof of `~propositions.axiomatic_systems.NI` via the inference
        rules `~propositions.axiomatic_systems.MP`,
        `~propositions.axiomatic_systems.I0`,
        `~propositions.axiomatic_systems.I1`,
        `~propositions.axiomatic_systems.D`, and
        `~propositions.axiomatic_systems.N`.
    """
    # Optional Task 6.7e

    # (1) Prove {p, (p->q)}|-q using _CP
    statement = InferenceRule((Formula("p"), Formula.parse("(p->q)")), Formula("q"))
    rules = {MP, I0, I1, D, N, _CP}
    lines = [
        Proof.Line(Formula("p")),
        Proof.Line(Formula.parse("(p->q)")),
        Proof.Line(Formula("q"), MP, (0, 1)),
    ]
    proof = Proof(statement, rules, lines)

    # (2) Use deduction theorem to get {p}|-((p->q)->q)
    proof = remove_assumption(proof)

    # (3) Use _CP to prove (~q->~(p->q)) as a corollary
    proof = prove_corollary(proof, Formula.parse("(~q->~(p->q))"), _CP)

    # (4) Use the deduction theorem to get |-(p->(~q->~(p->q))), and then get rid of_CP
    proof = remove_assumption(proof)
    return inline_proof(proof, _prove_CP())


#: Consequentia mirabilis
_CM = InferenceRule([Formula.parse("(~p->p)")], Formula.parse("p"))


def _prove_CM() -> Proof:
    """Proves `_CM` via `~propositions.axiomatic_systems.MP`,
    `~propositions.axiomatic_systems.I0`, `~propositions.axiomatic_systems.I1`,
    `~propositions.axiomatic_systems.D`, and
    `~propositions.axiomatic_systems.N`.

    Returns:
        A valid proof of `_CM` via the inference rules
        `~propositions.axiomatic_systems.MP`,
        `~propositions.axiomatic_systems.I0`,
        `~propositions.axiomatic_systems.I1`,
        `~propositions.axiomatic_systems.D`, and
        `~propositions.axiomatic_systems.N`.
    """
    # Optional Task 6.7f

    # We prove the rule using I2 and then remove it.
    statement = InferenceRule((Formula.parse("(~p->p)"),), Formula("p"))
    rules = {MP, I0, I1, D, N, I2}
    lines = [
        Proof.Line(Formula.parse("(~p->p)")),
        Proof.Line(
            Formula.parse("((~p->(p->~(~p->p)))->((~p->p)->(~p->~(~p->p))))"), D, ()
        ),
        Proof.Line(Formula.parse("(~p->(p->~(~p->p)))"), I2, ()),
        Proof.Line(Formula.parse("((~p->p)->(~p->~(~p->p)))"), MP, (2, 1)),
        Proof.Line(Formula.parse("(~p->~(~p->p))"), MP, (0, 3)),
        Proof.Line(Formula.parse("((~p->~(~p->p))->((~p->p)->p))"), N, ()),
        Proof.Line(Formula.parse("((~p->p)->p)"), MP, (4, 5)),
        Proof.Line(Formula("p"), MP, (0, 6)),
    ]
    return inline_proof(Proof(statement, rules, lines), prove_I2())


def prove_R() -> Proof:
    """Proves `~propositions.axiomatic_systems.R` via
    `~propositions.axiomatic_systems.MP`, `~propositions.axiomatic_systems.I0`,
    `~propositions.axiomatic_systems.I1`, `~propositions.axiomatic_systems.D`,
    and `~propositions.axiomatic_systems.N`.

    Returns:
        A valid proof of `~propositions.axiomatic_systems.R` via the inference
        rules `~propositions.axiomatic_systems.MP`,
        `~propositions.axiomatic_systems.I0`,
        `~propositions.axiomatic_systems.I1`,
        `~propositions.axiomatic_systems.D`, and
        `~propositions.axiomatic_systems.N`.
    """
    # Optional Task 6.7g

    # (1) Prove {(q->p), (~q->p)}|-p using _CP, HS, and _CM
    statement = InferenceRule(
        (Formula.parse("(q->p)"), Formula.parse("(~q->p)")), Formula("p")
    )
    rules = {MP, I0, I1, D, N, _CP, HS, _CM}
    lines = [
        Proof.Line(Formula.parse("(q->p)")),
        Proof.Line(Formula.parse("(~q->p)")),
        Proof.Line(Formula.parse("((q->p)->(~p->~q))"), _CP, ()),
        Proof.Line(Formula.parse("(~p->~q)"), MP, (0, 2)),
        Proof.Line(Formula.parse("(~p->p)"), HS, (3, 1)),
        Proof.Line(Formula("p"), _CM, [4]),
    ]
    proof = Proof(statement, rules, lines)

    # (2) Remove _CM and HS
    proof = inline_proof(proof, _prove_CM())
    proof = inline_proof(proof, prove_hypothetical_syllogism())

    # (3) Use the deduction theorem to get |-((q->p)->((~q->p)->p)) and remove _CP
    proof = remove_assumption(remove_assumption(proof))
    return inline_proof(proof, _prove_CP())


def prove_N() -> Proof:
    """Proves `~propositions.axiomatic_systems.N` via
    `~propositions.axiomatic_systems.MP`, `~propositions.axiomatic_systems.I0`,
    `~propositions.axiomatic_systems.I1`, `~propositions.axiomatic_systems.D`,
    and `~propositions.axiomatic_systems.N_ALTERNATIVE`.

    Returns:
        A valid proof of `~propositions.axiomatic_systems.N` via the inference
        rules `~propositions.axiomatic_systems.MP`,
        `~propositions.axiomatic_systems.I0`,
        `~propositions.axiomatic_systems.I1`,
        `~propositions.axiomatic_systems.D`, and
        `~propositions.axiomatic_systems.N_ALTERNATIVE`.
    """
    # Optional Task 6.8

    # (1) Prove {(~q->~p)}|-(p->q) using HS
    statement = InferenceRule((Formula.parse("(~q->~p)"),), Formula.parse("(p->q)"))
    rules = {MP, I0, I1, D, N_ALTERNATIVE, HS}
    lines = [
        Proof.Line(Formula.parse("(~q->~p)")),
        Proof.Line(Formula.parse("((~q->~p)->((~q->p)->q))"), N_ALTERNATIVE, ()),
        Proof.Line(Formula.parse("((~q->p)->q)"), MP, (0, 1)),
        Proof.Line(Formula.parse("(p->(~q->p))"), I1, ()),
        Proof.Line(Formula.parse("(p->q)"), HS, (3, 2)),
    ]
    proof = Proof(statement, rules, lines)

    # (2) Get rid of HS and use the deduction theorem to get |-((~q->~p)->(p->q))
    proof = inline_proof(proof, prove_hypothetical_syllogism())
    return remove_assumption(proof)


def prove_NA1() -> Proof:
    """Proves `~propositions.axiomatic_systems.NA1` via
    `~propositions.axiomatic_systems.MP`, `~propositions.axiomatic_systems.I0`,
    `~propositions.axiomatic_systems.I1`, `~propositions.axiomatic_systems.D`,
    `~propositions.axiomatic_systems.N`, and
    `~propositions.axiomatic_systems.AE1`.

    Returns:
        A valid proof of `~propositions.axiomatic_systems.NA1` via the inference
        rules `~propositions.axiomatic_systems.MP`,
        `~propositions.axiomatic_systems.I0`,
        `~propositions.axiomatic_systems.I1`,
        `~propositions.axiomatic_systems.D`, and
        `~propositions.axiomatic_systems.AE1`.
    """
    # Optional Task 6.9a

    # We use _CP and then remove it.
    rules = {MP, I0, I1, D, N, AE1, _CP}
    lines = [
        Proof.Line(Formula.parse("((p&q)->q)"), AE1, ()),
        Proof.Line(Formula.parse("(((p&q)->q)->(~q->~(p&q)))"), _CP, ()),
        Proof.Line(Formula.parse("(~q->~(p&q))"), MP, (0, 1)),
    ]
    return inline_proof(Proof(NA1, rules, lines), _prove_CP())


def prove_NA2() -> Proof:
    """Proves `~propositions.axiomatic_systems.NA2` via
    `~propositions.axiomatic_systems.MP`, `~propositions.axiomatic_systems.I0`,
    `~propositions.axiomatic_systems.I1`, `~propositions.axiomatic_systems.D`,
    `~propositions.axiomatic_systems.N`, and
    `~propositions.axiomatic_systems.AE2`.

    Returns:
        A valid proof of `~propositions.axiomatic_systems.NA2` via the inference
        rules `~propositions.axiomatic_systems.MP`,
        `~propositions.axiomatic_systems.I0`,
        `~propositions.axiomatic_systems.I1`,
        `~propositions.axiomatic_systems.D`, and
        `~propositions.axiomatic_systems.AE2`.
    """
    # Optional Task 6.9b

    # We use _CP and then remove it.
    rules = {MP, I0, I1, D, N, AE2, _CP}
    lines = [
        Proof.Line(Formula.parse("((p&q)->p)"), AE2, ()),
        Proof.Line(Formula.parse("(((p&q)->p)->(~p->~(p&q)))"), _CP, ()),
        Proof.Line(Formula.parse("(~p->~(p&q))"), MP, (0, 1)),
    ]
    return inline_proof(Proof(NA2, rules, lines), _prove_CP())


def prove_NO() -> Proof:
    """Proves `~propositions.axiomatic_systems.NO` via
    `~propositions.axiomatic_systems.MP`, `~propositions.axiomatic_systems.I0`,
    `~propositions.axiomatic_systems.I1`, `~propositions.axiomatic_systems.D`,
    `~propositions.axiomatic_systems.N`, and
    `~propositions.axiomatic_systems.OE`.

    Returns:
        A valid proof of `~propositions.axiomatic_systems.NO` via the inference
        rules `~propositions.axiomatic_systems.MP`,
        `~propositions.axiomatic_systems.I0`,
        `~propositions.axiomatic_systems.I1`,
        `~propositions.axiomatic_systems.D`, and
        `~propositions.axiomatic_systems.OE`.
    """
    # Optional Task 6.9c

    # (1) Prove {~p, ~q}|-~(p|q) using I2, _NNE, HS, and _CM
    statement = InferenceRule(
        (Formula.parse("~p"), Formula.parse("~q")), Formula.parse("~(p|q)")
    )
    rules = {MP, I0, I1, D, N, OE, I2, _NNE, HS, _CM}
    lines = [
        Proof.Line(
            Formula.parse("((p->~(p|q))->((q->~(p|q))->((p|q)->~(p|q))))"), OE, ()
        ),
        Proof.Line(Formula.parse("~p")),
        Proof.Line(Formula.parse("~q")),
        Proof.Line(Formula.parse("(~p->(p->~(p|q)))"), I2, ()),
        Proof.Line(Formula.parse("(p->~(p|q))"), MP, (1, 3)),
        Proof.Line(Formula.parse("((q->~(p|q))->((p|q)->~(p|q)))"), MP, (4, 0)),
        Proof.Line(Formula.parse("(~q->(q->~(p|q)))"), I2, ()),
        Proof.Line(Formula.parse("(q->~(p|q))"), MP, (2, 6)),
        Proof.Line(Formula.parse("((p|q)->~(p|q))"), MP, (7, 5)),
        Proof.Line(Formula.parse("(~~(p|q)->(p|q))"), _NNE, ()),
        Proof.Line(Formula.parse("(~~(p|q)->~(p|q))"), HS, (9, 8)),
        Proof.Line(Formula.parse("~(p|q)"), _CM, (10,)),
    ]
    proof = Proof(statement, rules, lines)

    # (2) Get rid of _CM and HS
    proof = inline_proof(proof, _prove_CM())
    proof = inline_proof(proof, prove_hypothetical_syllogism())

    # (3) Use the deduction theorem to get (~p->(~q->~(p|q)))
    proof = remove_assumption(remove_assumption(proof))

    # (4) Get rid of _NNE and I2
    proof = inline_proof(proof, _prove_NNE())
    return inline_proof(proof, prove_I2())
