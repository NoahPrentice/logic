# This file is part of the materials accompanying the book
# "Mathematical Logic through Python" by Gonczarowski and Nisan,
# Cambridge University Press. Book site: www.LogicThruPython.org
# (c) Yannai A. Gonczarowski and Noam Nisan, 2017-2022
# File name: propositions/reductions.py

"""Reduction between computational search problems."""

from __future__ import annotations
from typing import AbstractSet, Mapping, Tuple, Union

from propositions.syntax import *
from propositions.semantics import *

#: A graph on a vertex set of the form ``(1,``...\ ``,``\ `n_vertices`\ ``)``,
#: represented by the number of vertices `n_vertices` and a set of edges over
#: the vertices.
Graph = Tuple[int, AbstractSet[Tuple[int, int]]]


def is_graph(graph: Graph) -> bool:
    """Checks if the given data structure is a valid representation of a graph.

    Parameters:
        graph: data structure to check.

    Returns:
        ``True`` if the given data structure is a valid representation of a
        graph, ``False`` otherwise.
    """
    (n_vertices, edges) = graph
    for edge in edges:
        for vertex in edge:
            if not 1 <= vertex <= n_vertices:
                return False
        if edge[0] == edge[1]:
            return False
    return True


def is_valid_3coloring(graph: Graph, coloring: Mapping[int, int]) -> bool:
    """Checks whether the given coloring is a valid coloring of the given graph
    by the colors 1, 2, and 3.

    Parameters:
        graph: graph to check.
        coloring: mapping from the vertices of the given graph to colors,
            to check.

    Returns:
        ``True`` if the given coloring is a valid coloring of the given graph by
        the colors 1, 2, and 3; ``False`` otherwise.
    """
    assert is_graph(graph)
    (n_vertices, edges) = graph
    for vertex in range(1, n_vertices + 1):
        if vertex not in coloring.keys() or coloring[vertex] not in {1, 2, 3}:
            return False
    for edge in edges:
        if coloring[edge[0]] == coloring[edge[1]]:
            return False
    return True


def graph3coloring_to_formula(graph: Graph) -> Formula:
    """Efficiently reduces the 3-coloring problem of the given graph into a
    satisfiability problem.

    Parameters:
        graph: graph whose 3-coloring problem to reduce.

    Returns:
        A propositional formula that is satisfiable if and only if the given
        graph is 3-colorable.
    """
    assert is_graph(graph)
    # Optional Task 2.10a

    # (1) Create a list of formulas for each possible coloring of the vertices
    number_of_vertices, edges = graph
    formula_list = []
    for vertex_number in range(1, number_of_vertices + 1):
        v = str(vertex_number)
        formula_list.append(Formula.parse("(x" + v + "1|(x" + v + "2|x" + v + "3))"))
    
    # (2) Add formulas constraining the color of neighboring vertices
    for edge in edges:
        v1, v2 = str(edge[0]), str(edge[1])
        formula_list.append(Formula.parse("~(x" + v1 + "1&x" + v2 + "1)"))
        formula_list.append(Formula.parse("~(x" + v1 + "2&x" + v2 + "2)"))
        formula_list.append(Formula.parse("~(x" + v1 + "3&x" + v2 + "3)"))
    
    # (3) Conjoin the formulas together
    if len(formula_list) == 0:
            return Formula("x" + str(number_of_vertices) + "1")
    if len(formula_list) == 1:
        return formula_list[0]
    formula = Formula("&", formula_list.pop(), formula_list.pop())
    while len(formula_list) > 0:
        temp_formula = formula
        formula = Formula("&", temp_formula, formula_list.pop())
    return formula


def assignment_to_3coloring(graph: Graph, assignment: Model) -> Mapping[int, int]:
    """Efficiently transforms an assignment to the formula corresponding to the
    3-coloring problem of the given graph, to a 3-coloring of the given graph so
    that the 3-coloring is valid if and only if the given assignment is
    satisfying.

    Parameters:
        graph: graph to produce a 3-coloring for.
        assignment: assignment to the variable names of the formula returned by
            `graph3coloring_to_formula`\ ``(``\ `graph`\ ``)``.

    Returns:
        A 3-coloring of the given graph by the colors 1, 2, and 3 that is valid
        if and only if the given assignment satisfies the formula
        `graph3coloring_to_formula`\ ``(``\ `graph`\ ``)``.
    """
    assert is_graph(graph)
    formula = graph3coloring_to_formula(graph)
    assert evaluate(formula, assignment)
    # Optional Task 2.10b

    coloring = dict()
    for variable in assignment:
        if assignment[variable]:
            # Each variable in assignment is xvc, where v is the vertex number and c is
            # the color of the vertex. If assignment[variable] is true, then v is colored
            # as c, so we add it to our dict.
            v = int(variable[1:-1])
            c = int(variable[-1])
            coloring[v] = c
    return coloring


def tricolor_graph(graph: Graph) -> Union[Mapping[int, int], None]:
    """Computes a 3-coloring of the given graph.

    Parameters:
        graph: graph to 3-color.

    Returns:
        An arbitrary 3-coloring of the given graph if it is 3-colorable,
        ``None`` otherwise.
    """
    assert is_graph(graph)
    formula = graph3coloring_to_formula(graph)
    for assignment in all_models(list(formula.variables())):
        if evaluate(formula, assignment):
            return assignment_to_3coloring(graph, assignment)
    return None
