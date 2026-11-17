# -*- coding: utf-8 -*-
"""OFFICIAL DeepMind FunSearch cap_set code — verbatim extract (W72-142C).

Provenance (see ../../../../OFFICIAL_PROVENANCE.md):
  source repo : github.com/google-deepmind/funsearch (fresh clone 2026-11-17)
  source path : cap_set/cap_set.ipynb
  commit      : cc53f274237d7ab05c19df939edbc1f9616a7c19 (HEAD at clone)
  license     : Apache-2.0 (see funsearch/LICENSE in the clone)
  cells       : 2 (evaluate/solve + trivial priority), 6 (first official
                priority), 8 (is_cap_set — THE OFFICIAL VERIFIER),
                12 (build_512_cap), 14 (second official priority)

The code below each `NOTEBOOK CELL n` marker is the notebook cell's source
string copied byte-for-byte, in original notebook order, so importing this
module reproduces the notebook's execution flow: cell 6 rebinds `priority`
and computes `cap_set_n8 = solve(8)` (asserted (512, 8)); cell 12 builds the
explicit 512-cap and asserts set-equality with the greedy one; cell 14
rebinds `priority` again and computes `cap_set_n9 = solve(9)` (asserted
(1082, 9)).

DOCUMENTED REPAIR (the only one permitted by the W72-142C brief), on one
line of cell 2:
  published bracket-eaten rendering : prioritiesax_index] = -np.inf
  repaired / intact form            : priorities[max_index] = -np.inf
(max_index is the argmax selected two lines above; the bracket-eaten
rendering is a NameError.)
FORM FOUND IN THE FRESH CLONE: already intact. The extraction enforces that the
line is present in exactly one of the two forms and normalises it to the
intact form; no other character of any cell is changed.
"""

# ------------------------- NOTEBOOK CELL 2 (verbatim) -------------------------
"""Finds large cap sets."""
import itertools
import numpy as np


# @funsearch.run
def evaluate(n: int) -> int:
  """Returns the size of an `n`-dimensional cap set."""
  capset = solve(n)
  return len(capset)


def solve(n: int) -> np.ndarray:
  """Returns a large cap set in `n` dimensions."""
  all_vectors = np.array(list(itertools.product((0, 1, 2), repeat=n)), dtype=np.int32)

  # Powers in decreasing order for compatibility with `itertools.product`, so
  # that the relationship `i = all_vectors[i] @ powers` holds for all `i`.
  powers = 3 ** np.arange(n - 1, -1, -1)

  # Precompute all priorities.
  priorities = np.array([priority(tuple(vector), n) for vector in all_vectors])

  # Build `capset` greedily, using priorities for prioritization.
  capset = np.empty(shape=(0, n), dtype=np.int32)
  while np.any(priorities != -np.inf):
    # Add a vector with maximum priority to `capset`, and set priorities of
    # invalidated vectors to `-inf`, so that they never get selected.
    max_index = np.argmax(priorities)
    vector = all_vectors[None, max_index]  # [1, n]
    blocking = np.einsum('cn,n->c', (- capset - vector) % 3, powers)  # [C]
    priorities[blocking] = -np.inf
    priorities[max_index] = -np.inf
    capset = np.concatenate([capset, vector], axis=0)

  return capset


# @funsearch.evolve
def priority(el: tuple[int, ...], n: int) -> float:
  """Returns the priority with which we want to add `element` to the cap set."""
  return 0.0

# ------------------------- NOTEBOOK CELL 6 (verbatim) -------------------------
def priority(el: tuple[int, ...], n: int) -> float:
  score = n
  in_el = 0
  el_count = el.count(0)

  if el_count == 0:
    score += n ** 2
    if el[1] == el[-1]:
      score *= 1.5
    if el[2] == el[-2]:
      score *= 1.5
    if el[3] == el[-3]:
      score *= 1.5
  else:
    if el[1] == el[-1]:
      score *= 0.5
    if el[2] == el[-2]:
      score *= 0.5

  for e in el:
    if e == 0:
      if in_el == 0:
        score *= n * 0.5
      elif in_el == el_count - 1:
        score *= 0.5
      else:
        score *= n * 0.5 ** in_el
      in_el += 1
    else:
      score += 1

  if el[1] == el[-1]:
    score *= 1.5
  if el[2] == el[-2]:
    score *= 1.5

  return score


# We call the `solve` function instead of `evaluate` so that we get access to
# the cap set itself (rather than just its size), for verification and
# inspection purposes.
cap_set_n8 = solve(8)
assert cap_set_n8.shape == (512, 8)

# ------------------------- NOTEBOOK CELL 8 (verbatim) -------------------------
def is_cap_set(vectors: np.ndarray) -> bool:
  """Returns whether `vectors` form a valid cap set.

  Checking the cap set property naively takes O(c^3 n) time, where c is the size
  of the cap set. This function implements a faster check that runs in O(c^2 n).

  Args:
    vectors: [c, n] array containing c n-dimensional vectors over {0, 1, 2}.
  """
  _, n = vectors.shape

  # Convert `vectors` elements into raveled indices (numbers in [0, 3^n) ).
  powers = np.array([3 ** j for j in range(n - 1, -1, -1)], dtype=int)  # [n]
  raveled = np.einsum('in,n->i', vectors, powers)  # [c]

  # Starting from the empty set, we iterate through `vectors` one by one and at
  # each step check that the vector can be inserted into the set without
  # violating the defining property of cap set. To make this check fast we
  # maintain a vector `is_blocked` indicating for each element of Z_3^n whether
  # that element can be inserted into the growing set without violating the cap
  # set property.
  is_blocked = np.full(shape=3 ** n, fill_value=False, dtype=bool)
  for i, (new_vector, new_index) in enumerate(zip(vectors, raveled)):
    if is_blocked[new_index]:
      return False  # Inserting the i-th element violated the cap set property.
    if i >= 1:
      # Update which elements are blocked after the insertion of `new_vector`.
      blocking = np.einsum(
          'nk,k->n',
          (- vectors[:i, :] - new_vector[None, :]) % 3, powers)
      is_blocked[blocking] = True
    is_blocked[new_index] = True  # In case `vectors` contains duplicates.
  return True  # All elements inserted without violating the cap set property.


assert is_cap_set(cap_set_n8)

# ------------------------- NOTEBOOK CELL 12 (verbatim) -------------------------
def build_512_cap() -> list[tuple[int, ...]]:
  """Returns a cap set of size 512 in `n=8` dimensions."""
  n = 8
  V = list(itertools.product(range(3), repeat=n))
  support = lambda v: tuple(i for i in range(n) if v[i] != 0)
  reflections = lambda v: sum(1 for i in range(1, n // 2) if v[i] == v[-i])

  # Add all 128 weight-8 vectors that have >= 2 reflections.
  weight8_vectors = [v for v in V
                     if len(support(v)) == 8  # Weight is 8.
                     and reflections(v) >= 2]  # At least 2 reflections.

  # Add all 128 weight-4 vectors that have specific support.
  supports_16 = [(0, 1, 2, 3), (0, 1, 2, 5), (0, 3, 6, 7), (0, 5, 6, 7),
                 (1, 3, 4, 6), (1, 4, 5, 6), (2, 3, 4, 7), (2, 4, 5, 7)]
  weight4_vectors = [v for v in V
                     if support(v) in supports_16]

  # Add all 128 weight-4 vectors with specific support and 1 reflection.
  supports_8 = [(0, 1, 2, 7), (0, 1, 2, 6), (0, 1, 3, 7), (0, 1, 6, 7),
                (0, 1, 5, 7), (0, 2, 3, 6), (0, 2, 6, 7), (0, 2, 5, 6),
                (1, 2, 4, 7), (1, 2, 4, 6), (1, 3, 4, 7), (1, 4, 6, 7),
                (1, 4, 5, 7), (2, 3, 4, 6), (2, 4, 6, 7), (2, 4, 5, 6)]
  weight4_vectors_2 = [v for v in V
                       if support(v) in supports_8
                       and reflections(v) == 1]  # Exactly 1 reflection.

  # Add 128 weight-5 vectors with <= 1 reflections and one more condition.
  allowed_zeros = [(0, 4, 7), (0, 2, 4), (0, 1, 4), (0, 4, 6),
                   (1, 2, 6), (2, 6, 7), (1, 2, 7), (1, 6, 7)]
  weight5_vectors = [
      v for v in V
      if tuple(i for i in range(n) if v[i] == 0) in allowed_zeros
      and reflections(v) <= 1  # At most 1 reflection.
      and (v[1] * v[7]) % 3 != 1 and (v[2] * v[6]) % 3 != 1]

  return weight8_vectors + weight4_vectors + weight4_vectors_2 + weight5_vectors


explicit = np.array(build_512_cap(), dtype=np.int32)
assert explicit.shape == (512, 8)
assert is_cap_set(explicit)
# The explicit construction builds the same cap set as a set (i.e. up to
# permutation of rows).
assert set(map(tuple, explicit)) == set(map(tuple, cap_set_n8))

# ------------------------- NOTEBOOK CELL 14 (verbatim) -------------------------
def priority(el: tuple[int, ...], n: int) -> float:
  el = np.array(el, dtype=np.float32)
  weight = (el @ el) % 3  # Weight (mod 3) of the full vector.
  a = n // 3
  b = n - n // 3
  s_1 = (el[:b] @ el[:b]) % 3  # Weight (mod 3) of first two thirds.
  s_3 = (2 * (el[:a] @ el[:a])) % 3  # Double norm of first third.
  s_4 = (el[:a] @ el[a:b]) % 3  # Cross correlation.
  s_5 = np.sum(el[:a] == el[-1]) % 3
  return - 3 ** 3 * s_1 + 3 ** 2 * weight + 3 ** 3 * s_3 + 3 ** 2 * s_4 + s_5


n = 9
cap_set_n9 = solve(n)
assert cap_set_n9.shape == (1082, 9)
assert is_cap_set(cap_set_n9)

