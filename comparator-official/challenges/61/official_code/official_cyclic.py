#!/usr/bin/env python3
# -*- coding: utf-8 -*-
# =============================================================================
# OFFICIAL DeepMind FunSearch code - VERBATIM EXTRACT (cyclic_graphs module).
#
# Source repo : github.com/google-deepmind/funsearch (fresh GitHub clone
#               2026-11-17, NOT reused from any prior campaign artifact)
# Source path : cyclic_graphs/cyclic_graphs.ipynb
# Commit      : cc53f274237d7ab05c19df939edbc1f9616a7c19 (HEAD at clone)
# License     : Apache-2.0 - Copyright 2023 DeepMind Technologies Limited.
#               Licensed under the Apache License, Version 2.0; you may not
#               use this file except in compliance with the License. You may
#               obtain a copy at:
#               https://www.apache.org/licenses/LICENSE-2.0
#
# Cells extracted (0-based notebook indices; source strings joined verbatim,
# delimited by the OFFICIAL CELL markers below):
#   cell 2  - skeleton: evaluate() / solve() + the trivial priority
#             (the @funsearch.run / @funsearch.evolve entry points)
#   cell 6  - official priority #1: independent set of size 367 in C_7^5
#   cell 7  - official assertion: evaluate(num_nodes=7, n=5) == 367
#   cell 9  - official priority #2: best known independent sets in C_9^n
#   cell 11 - official expected sizes {3:81, 4:324, 5:1458, 6:6561, 7:26244}
#             + assertions for n = 3..5 (range_n = range(3, 6))
#   cell 13 - official priority #3: independent set of size 754 in C_11^4
#   cell 14 - official assertion: evaluate(num_nodes=11, n=4) == 754
#
# REPAIR NOTE (the ONLY permitted repair, per the W72-61C brief and
# PROTOCOL.md): the brief records the published cell-2 line
#     max_set = np.concatenate(ax_set, child], axis=0)
# as bracket-eaten and permits exactly one repair, to
#     max_set = np.concatenate([max_set, child], axis=0)
# STATE AT THIS CLONE: at commit cc53f27 the notebook's cell-2 line already
# matches the repaired form byte-for-byte (the extraction tool asserts this by
# in-process containment tests before and after), so the repair is a NO-OP and
# every extracted cell below is byte-identical to the notebook JSON source
# strings. No byte of any extracted cell is altered by this extraction.
#
# Execution semantics (identical to the published notebook): the cells run in
# notebook order 2, 6, 7, 9, 11, 13, 14 in a single namespace; each
# `def priority` rebinding takes effect for the assertions that follow it.
# Executing this file top to bottom therefore runs the official assertions of
# cells 7, 11 and 14 against exactly the priorities they were published with.
# =============================================================================

# ---- OFFICIAL CELL 2 (verbatim) ----
"""Obtains maximal independent sets."""
import itertools
import numpy as np


# @funsearch.run
def evaluate(num_nodes: int, n: int) -> int:
  """Returns the size of an independent set."""
  independent_set = solve(num_nodes, n)
  return len(independent_set)


def solve(num_nodes: int, n: int) -> list[tuple[int, ...]]:
  """Gets independent set with maximal size.

  Args:
    num_nodes: The number of nodes of the base cyclic graph.
    n: The power we raise the graph to.

  Returns:
    A list of `n`-tuples in `{0, 1, 2, ..., num_nodes - 1}`.
  """
  to_block = np.array(list(itertools.product([-1, 0, 1], repeat=n)))

  # Powers in decreasing order for compatibility with `itertools.product`, so
  # that the relationship `i = children[i] @ powers` holds for all `i`.
  powers = num_nodes ** np.arange(n - 1, -1, -1)

  # Precompute the priority scores.
  children = np.array(
      list(itertools.product(range(num_nodes), repeat=n)), dtype=np.int32)
  scores = np.array([priority(tuple(child), num_nodes, n)
                     for child in children])

  # Build `max_set` greedily, using scores for prioritization.
  max_set = np.empty(shape=(0, n), dtype=np.int32)
  while np.any(scores != -np.inf):
    # Add a child with a maximum score to `max_set`, and set scores of
    # invalidated children to -inf, so that they never get selected.
    max_index = np.argmax(scores)
    child = children[None, max_index]  # [1, n]

    blocking = np.einsum(
        'cn,n->c', (to_block + child) % num_nodes, powers)  # [C]
    scores[blocking] = -np.inf
    max_set = np.concatenate([max_set, child], axis=0)

  return [tuple(map(int, el)) for el in max_set]


# @funsearch.evolve
def priority(el: tuple[int, ...], num_nodes: int, n: int) -> float:
  """Returns the priority with which we want to add `el` to the set.

  Args:
    el: an n-tuple representing the element to consider whether to add.
    num_nodes: the number of nodes of the base graph.
    n: an integer, power of the graph.

  Returns:
    A number reflecting the priority with which we want to add `el` to the
    independent set.
  """
  return 0.
# ---- OFFICIAL CELL 6 (verbatim) ----
def priority(el: tuple[int, ...], num_nodes: int, n: int) -> float:
  """Returns the priority with which we want to add `el` to the set."""
  score = 0.
  for i in range(n):
    if el[i] == el[(i + 2) % n]:
      score += 1
    else:
      score -= 1
    x = ((n - 2) * el[i] - el[(i + 1) % n]
         - el[(i + 2) % n] - (n + 1) * el[(i + 3) % n]) % num_nodes
    score -= 0.5 * (x - el[(i + 1) % n]) ** 2
    score += 0.1 * (num_nodes - 1 - (x - 1) % num_nodes) ** 2
    score += 0.2 * (num_nodes - 1 - (x - 2) % num_nodes) ** 2
  return score
# ---- OFFICIAL CELL 7 (verbatim) ----
assert evaluate(num_nodes=7, n=5) == 367
# ---- OFFICIAL CELL 9 (verbatim) ----
def priority(el: tuple[int, ...], num_nodes: int, n: int) -> float:
  """Returns the priority with which we want to add `el` to the set."""
  s = 0.
  for i in range(n):
    s += el[i] << i
    s %= num_nodes
  return (2 * el[2] - 4 * el[0] + el[1]) % num_nodes + s
# ---- OFFICIAL CELL 11 (verbatim) ----
expected_sizes = {
    3: 81,
    4: 324,
    5: 1458,
    6: 6561,
    7: 26244
}
range_n = range(3, 6)
# range_n = range(3, 8)  # Uncomment to run up until n=7.
for n in range_n:
  assert evaluate(num_nodes=9, n=n) == expected_sizes[n]
# ---- OFFICIAL CELL 13 (verbatim) ----
def priority(el: tuple[int, ...], num_nodes: int, n: int) -> float:
  """Returns the priority with which we want to add `el` to the set."""
  el_clipped = np.clip(el, a_min=None, a_max=num_nodes - 3)
  values = 2 * np.array(list(itertools.product(range(1, n), repeat=n)))
  multipliers = np.array(
      [num_nodes ** i for i in range(n - 1, -1, -1)], dtype=np.int32)
  x = np.sum((1 + values + el_clipped) * multipliers, axis=-1)
  return np.sum(x % (num_nodes - 2), dtype=float)
# ---- OFFICIAL CELL 14 (verbatim) ----
assert evaluate(num_nodes=11, n=4) == 754