#!/usr/bin/env python3
"""
z3 CERTIFICATE LIBRARY for the Erdos #61 doubter census (W67-61D).

Encodes "there exists an H-free graph on n vertices with omega < k and
alpha < k" as a SAT instance over edge booleans and solves it with z3.
UNSAT certifies the lower bound max(omega, alpha) >= k for every H-free
graph on n vertices; SAT yields an explicit witness graph.

This is the independent third engine (after the bitmask ENGINE A and the
adjacency-set ENGINE B): it shares no enumeration code with either.
"""

import itertools

try:
    import z3
    Z3_AVAILABLE = True
except ImportError:  # pragma: no cover
    Z3_AVAILABLE = False


def pair_vars(n):
    vs = {}
    for i in range(n):
        for j in range(i + 1, n):
            vs[(i, j)] = z3.Bool(f"e_{i}_{j}")
    return vs


def edge_lit(vs, u, v):
    return vs[(u, v)] if u < v else vs[(v, u)]


def _h_edge_set(h_edges):
    return {frozenset(e) for e in h_edges}


def add_hfree(s, vs, n, h_edges, h):
    """Forbid every induced copy of the graph H (h vertices, edge list
    h_edges) in the n-vertex graph described by vs."""
    hset = _h_edge_set(h_edges)
    for S in itertools.combinations(range(n), h):
        for perm in itertools.permutations(S):
            lits = []
            for a, b in itertools.combinations(range(h), 2):
                want = frozenset((a, b)) in hset
                lit = edge_lit(vs, perm[a], perm[b])
                lits.append(lit if want else z3.Not(lit))
            s.add(z3.Or([z3.Not(l) for l in lits]))


def add_omega_le(s, vs, n, k):
    """omega <= k: forbid cliques of size k+1."""
    for S in itertools.combinations(range(n), k + 1):
        s.add(
            z3.Or(
                [z3.Not(edge_lit(vs, a, b)) for a, b in itertools.combinations(S, 2)]
            )
        )


def add_alpha_le(s, vs, n, k):
    """alpha <= k: forbid independent sets of size k+1."""
    for S in itertools.combinations(range(n), k + 1):
        s.add(z3.Or([edge_lit(vs, a, b) for a, b in itertools.combinations(S, 2)]))


def solve_hfree_bound(n, h_edges, h, k, timeout_ms=120000):
    """Decide: exists H-free graph on n vertices with omega < k and
    alpha < k?  Returns (status, witness_edges or None) where status is
    'sat' / 'unsat' / 'unknown'."""
    if not Z3_AVAILABLE:
        raise RuntimeError("z3 not available")
    vs = pair_vars(n)
    s = z3.Solver()
    s.set("timeout", timeout_ms)
    add_hfree(s, vs, n, h_edges, h)
    add_omega_le(s, vs, n, k - 1)
    add_alpha_le(s, vs, n, k - 1)
    res = s.check()
    if res == z3.sat:
        model = s.model()
        edges = []
        for (i, j), v in sorted(vs.items()):
            if z3.is_true(model.eval(v, model_completion=True)):
                edges.append((i, j))
        return "sat", edges
    if res == z3.unsat:
        return "unsat", None
    return "unknown", None


def solve_general_bound(n, k, timeout_ms=120000):
    """Decide: exists ANY graph on n vertices with omega < k and alpha <
    k (the Ramsey question)?  Returns (status, witness or None)."""
    if not Z3_AVAILABLE:
        raise RuntimeError("z3 not available")
    vs = pair_vars(n)
    s = z3.Solver()
    s.set("timeout", timeout_ms)
    add_omega_le(s, vs, n, k - 1)
    add_alpha_le(s, vs, n, k - 1)
    res = s.check()
    if res == z3.sat:
        model = s.model()
        edges = []
        for (i, j), v in sorted(vs.items()):
            if z3.is_true(model.eval(v, model_completion=True)):
                edges.append((i, j))
        return "sat", edges
    if res == z3.unsat:
        return "unsat", None
    return "unknown", None


def class_minmax_cert(cls_name, h_edges, h, n, timeout_ms=120000):
    """Pin down min over H-free n-vertex graphs of max(omega, alpha).

    Semantics: solve_hfree_bound(n, ..., k) asks for an H-free graph with
    omega < k AND alpha < k.  UNSAT at k certifies min-max >= k; SAT at k
    certifies min-max <= k-1.  UNSAT is monotone downward in k (it holds
    for all k <= min-max), so we ramp k upward past the last UNSAT: the
    first SAT at k gives the exact value min-max = k-1 together with an
    explicit witness."""
    results = {
        "class": cls_name,
        "n": n,
        "per_k": {},
        "value": None,
        "witness": None,
        "unsat_k": None,
    }
    k = 1
    while k <= n + 1:
        status, wit = solve_hfree_bound(n, h_edges, h, k, timeout_ms)
        results["per_k"][str(k)] = status
        if status == "unsat":
            results["unsat_k"] = k  # certified: min-max >= k so far
            k += 1
            continue
        if status == "sat":
            results["value"] = k - 1
            results["witness"] = wit
            results["witness_note"] = (
                f"witness has omega <= {k-1} and alpha <= {k-1}; "
                f"combined with UNSAT at k={k-1} (min-max >= {k-1}), "
                f"min max(omega,alpha) = {k-1} exactly"
            )
            break
        results["error"] = f"z3 unknown at k={k}"
        break
    return results


def general_minmax_cert(n, timeout_ms=120000):
    """Same ramping certificate for ALL graphs on n vertices (the Ramsey
    floor): min over all graphs of max(omega, alpha)."""
    results = {
        "class": "all-graphs",
        "n": n,
        "per_k": {},
        "value": None,
        "witness": None,
        "unsat_k": None,
    }
    k = 1
    while k <= n + 1:
        status, wit = solve_general_bound(n, k, timeout_ms)
        results["per_k"][str(k)] = status
        if status == "unsat":
            results["unsat_k"] = k
            k += 1
            continue
        if status == "sat":
            results["value"] = k - 1
            results["witness"] = wit
            break
        results["error"] = f"z3 unknown at k={k}"
        break
    return results
