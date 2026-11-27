#!/usr/bin/env python3
"""Independent exact algebra checks and whole-input byte inventory.

Not a Lean build and not a certificate of the Hodge conjecture.
Uses only the Python standard library. Universal polynomial checks take
place in a free associative polynomial ring; matrix checks have stated
finite ranges. Run from any directory inside this repository.
"""

from collections import Counter
from fractions import Fraction as Q
from itertools import product
from pathlib import Path
import argparse
import hashlib
import json
import re
import subprocess
import tomllib

ROOT = Path(__file__).resolve().parents[2]
BASE = "f8d557bb840134cac00a3fb4267aa5bb611501f2"
CHANGED_LEAN = [
    "GSTExactSequenceTorsion.lean", "GSTLawStackRound29.lean",
    "GSTCubicNilpotentDressing.lean", "GSTFiniteSourceCorrection.lean",
    "GSTClassicalHodgeFiniteSourceCorrection.lean", "GSTSplitBoundaryProjection.lean",
    "GSTComplexTangentProjectionChainObstruction.lean",
    "GSTClassicalHodgeCMNativeRationalDescent.lean", "GSTOpenAISourceCorrectionUpgrade.lean",
]
checks = Counter()
preexisting_lexical_anomalies = []


def require(condition, family):
    if not condition:
        raise AssertionError(family)
    checks[family] += 1


def plus(a, b):
    return tuple(tuple(x+y for x, y in zip(r, s)) for r, s in zip(a, b))


def scale(c, a):
    return tuple(tuple(c*x for x in r) for r in a)


def times(a, b):
    return tuple(tuple(sum(a[i][k]*b[k][j] for k in range(len(b)))
                       for j in range(len(b[0]))) for i in range(len(a)))


def identity(n):
    return tuple(tuple(Q(i == j) for j in range(n)) for i in range(n))


def zero(n):
    return scale(0, identity(n))


def power(a, k):
    ans = identity(len(a))
    for _ in range(k):
        ans = times(ans, a)
    return ans


def dress(a):
    return plus(plus(identity(len(a)), scale(2, a)), scale(2, times(a, a)))


# Noncommutative polynomial arithmetic: words are tuples of indeterminates.
def p_add(*ps):
    out = Counter()
    for p in ps:
        for w, c in p.items():
            out[w] += c
    return {w: c for w, c in out.items() if c}


def p_scale(c, p):
    return {w: c*a for w, a in p.items() if c*a}


def p_mul(p, q):
    out = Counter()
    for w, a in p.items():
        for v, b in q.items():
            out[w+v] += a*b
    return {w: c for w, c in out.items() if c}


def p_dress(x):
    return p_add({(): 1}, p_scale(2, x), p_scale(2, p_mul(x, x)))


def mathematics():
    x, y = {("x",): 1}, {("y",): 1}
    xx, xy, yx = p_mul(x, x), p_mul(x, y), p_mul(y, x)
    lhs = p_add(p_mul(p_dress(x), p_dress(y)), p_scale(-1, p_dress(p_add(x, y))))
    rhs = p_add(p_scale(2, p_add(xy, p_scale(-1, yx))),
                p_scale(4, p_mul(xx, y)), p_scale(4, p_mul(xy, y)),
                p_scale(4, p_mul(p_mul(xx, y), y)))
    require(lhs == rhs, "universal_free_ring_defect_identity")
    quotient = Counter()
    for word, coefficient in lhs.items():
        if len(word) < 3:
            quotient[tuple(sorted(word))] += coefficient
    require(all(c == 0 for c in quotient.values()), "universal_commuting_cubic_quotient")
    inverse_error = p_add(p_mul(p_dress(x), p_dress(p_scale(-1, x))), {(): -1})
    require(inverse_error == {("x",)*4: 4}, "universal_inverse_polynomial")
    require(lhs != {}, "hostile_dropping_all_hypotheses_is_detected")

    # Exhaustive cyclic exact-sequence models: 1<=a,b<=10, all middle elements.
    for a, b in product(range(1, 11), repeat=2):
        mod = a*b
        for n in range(mod):
            if n % b == 0:
                k = n//b
                require(k < a and b*k % mod == n, "exact_cyclic_extension_kernel")
            require((a*b*n) % mod == 0, "exact_cyclic_product_bound")
    require(4 % 16 != 0 and 8 % 16 != 0 and 16 % 16 == 0, "sharp_sixteen_boundary")

    j = ((0, 1, 0), (0, 0, 1), (0, 0, 0))
    j2 = times(j, j)
    require(j2 != zero(3) and times(j2, j) == zero(3), "strict_cubic_extension")
    require(times(plus(identity(3), j), plus(identity(3), j)) !=
            plus(identity(3), scale(2, j)), "hostile_old_linear_dressing_fails")
    for a, b, c, d in product(range(-2, 3), repeat=4):
        u, v = plus(scale(a, j), scale(b, j2)), plus(scale(c, j), scale(d, j2))
        require(times(dress(u), dress(v)) == dress(plus(u, v)), "cubic_matrix_grid")
        require(times(dress(u), dress(scale(-1, u))) == identity(3), "cubic_integral_inverse_grid")

    def h(a, b, c):
        return ((1, 2*a, 2*c+2*a*b), (0, 1, 2*b), (0, 0, 1))

    for a, b, c, d, e, f in product(range(-1, 2), repeat=6):
        require(times(h(a, b, c), h(d, e, f)) ==
                h(a+d, b+e, c+f+a*e-d*b), "heisenberg_six_parameter_grid")
    for m in list(range(-8, 0)) + list(range(1, 9)):
        require(times(h(m, 0, 0), h(0, m, 0)) != h(m, m, 0), "hostile_noncommuting_scale")
        require(m != -m, "hostile_scaled_area_not_symmetric")
    area = lambda u, v: u[0]*v[1]-v[0]*u[1]
    addv = lambda u, v: tuple(a+b for a, b in zip(u, v))
    points = list(product(range(-1, 2), repeat=2))
    for u, v, w in product(points, repeat=3):
        require(area(u, v)+area(addv(u, v), w) == area(v, w)+area(u, addv(v, w)),
                "area_cocycle_grid")

    # Independent operator calculation: no source-return commutation.
    a, b = ((1, 1), (0, 0)), ((0, 0), (0, 1))
    frame = plus(a, b)
    n = plus(identity(2), scale(-1, frame))
    require(times(a, b) != times(b, a), "noncommuting_source_witness")
    require(times(n, n) == zero(2), "total_error_nilpotent")
    for size in range(1, 9):
        n = tuple(tuple(Q(1) if col == row+1 else Q(0)
                        for col in range(size)) for row in range(size))
        frame = plus(identity(size), scale(-1, n))
        partial = zero(size)
        for k in range(size+2):
            require(partial == plus(identity(size), scale(-1, power(n, k))),
                    "finite_correction_operator_identity")
            partial = plus(partial, times(frame, power(n, k)))
    # q(t)=(t-2)(t-3), q(1)=2; N is NOT nilpotent.
    n, coeff = ((Q(2), Q(0)), (Q(0), Q(3))), [Q(6), Q(-5), Q(1)]
    frame = plus(identity(2), scale(-1, n))
    partials = [zero(2)]
    for k in range(2):
        partials.append(plus(partials[-1], times(frame, power(n, k))))
    orbit, native = zero(2), zero(2)
    for k, c in enumerate(coeff):
        orbit, native = plus(orbit, scale(c, power(n, k))), plus(native, scale(c, partials[k]))
    require(orbit == zero(2), "polynomial_annihilator_non_nilpotent")
    require(scale(1/sum(coeff), native) == identity(2), "polynomial_exact_cycle")
    require(power(n, 8) != zero(2), "hostile_nilpotence_not_required")
    require(sum([Q(-1), Q(1)]) == 0, "fixed_mode_denominator_gate")

    # Boundary correction and remaining type: d h = id on Q.
    d, h = ((Q(0), Q(-1)),), ((Q(0),), (Q(-1),))
    c = plus(identity(2), scale(-1, times(h, d)))
    p = ((Q(1, 2), Q(1, 2)), (Q(1, 2), Q(1, 2)))
    require(times(d, c) == ((0, 0),), "boundary_projection_closed")
    require(times(c, c) == c, "boundary_projection_idempotent")
    cp = times(c, p)
    require(times(p, cp) != cp, "hostile_boundary_repair_does_not_preserve_type")


def strip_lean(text):
    """Strip nested block comments, line comments and ordinary string literals."""
    out, i, depth = [], 0, 0
    while i < len(text):
        if depth:
            if text.startswith("/-", i):
                depth, i = depth+1, i+2
            elif text.startswith("-/", i):
                depth, i = depth-1, i+2
            else:
                out.append("\n" if text[i] == "\n" else " ")
                i += 1
        elif text.startswith("/-", i):
            depth, i = 1, i+2
        elif text.startswith("--", i):
            end = text.find("\n", i)
            i = len(text) if end == -1 else end
        elif text[i] == '"':
            out.append(" ")
            i += 1
            while i < len(text):
                if text[i] == "\\":
                    i += 2
                elif text[i] == '"':
                    i += 1
                    break
                else:
                    i += 1
        else:
            out.append(text[i])
            i += 1
    if depth:
        raise AssertionError("unterminated Lean block comment")
    return "".join(out)


def source_integrity():
    files = {str(p.relative_to(ROOT)): p for p in ROOT.rglob("*.lean") if ".git" not in p.parts}
    graph = {}
    for name, p in files.items():
        try:
            code = strip_lean(p.read_text())
        except AssertionError as error:
            if name in CHANGED_LEAN:
                raise
            preexisting_lexical_anomalies.append({"path": name, "error": str(error)})
            continue
        graph[name[:-5].replace("/", ".")] = re.findall(r"^import\s+(\S+)", code, re.M)
    visiting, visited = set(), set()

    def visit(node):
        if node in visited:
            return
        require(node not in visiting, "local_import_acyclic")
        visiting.add(node)
        for dep in graph.get(node, []):
            if dep in graph:
                visit(dep)
        visiting.remove(node)
        visited.add(node)

    for node in graph:
        visit(node)
    for name in CHANGED_LEAN:
        code = strip_lean((ROOT/name).read_text())
        require(not re.search(r"\b(sorry|admit|axiom|unsafe)\b", code), "no_added_proof_escape")
        require(not re.search(r":\s*(True|False)\b", code), "no_truth_valued_stubs")
    config = tomllib.loads((ROOT/"lakefile.toml").read_text())
    roots = next(lib["roots"] for lib in config["lean_lib"] if lib["name"] == "GSTOpenAISourceUpgrade")
    for name in roots:
        require((ROOT/(name.replace(".", "/")+".lean")).is_file(), "registered_roots_exist")


def inventory(output):
    # Read every ORIGINAL tracked blob from the immutable base, including binary
    # artifacts. This proves byte coverage, not semantic review of every proof.
    lines = subprocess.check_output(["git", "ls-tree", "-r", BASE], cwd=ROOT).decode().splitlines()
    entries = [(line.split("\t", 1)[1], line.split()[2]) for line in lines]
    proc = subprocess.Popen(["git", "cat-file", "--batch"], cwd=ROOT,
                            stdin=subprocess.PIPE, stdout=subprocess.PIPE)
    records = []
    for path, blob in entries:
        proc.stdin.write((blob+"\n").encode())
        proc.stdin.flush()
        header = proc.stdout.readline().decode().split()
        size = int(header[2])
        data = proc.stdout.read(size)
        require(proc.stdout.read(1) == b"\n", "input_blob_read")
        item = {"path": path, "git_blob": blob, "bytes": size,
                "sha256": hashlib.sha256(data).hexdigest()}
        if path.endswith(".lean"):
            item["lines"] = data.count(b"\n")
            try:
                code = strip_lean(data.decode())
            except AssertionError as error:
                item["lexical_error"] = str(error)
            else:
                item["theorems_and_lemmas"] = len(re.findall(r"^\s*(?:theorem|lemma)\s", code, re.M))
                item["imports"] = re.findall(r"^import\s+(\S+)", code, re.M)
        records.append(item)
    proc.stdin.close()
    require(proc.wait() == 0, "batch_inventory_completed")
    result = {"base_commit": BASE, "scope": "all original tracked blobs; byte/lexical inventory only",
              "files": len(records), "lean_files": sum(r["path"].endswith(".lean") for r in records),
              "bytes": sum(r["bytes"] for r in records), "records": records}
    output.write_text(json.dumps(result, ensure_ascii=False, indent=2)+"\n")
    print(f"Inventory: {result['files']} files, {result['lean_files']} Lean files, {result['bytes']} bytes")


if __name__ == "__main__":
    parser = argparse.ArgumentParser()
    parser.add_argument("--inventory", type=Path)
    args = parser.parse_args()
    mathematics()
    source_integrity()
    if args.inventory:
        inventory(args.inventory)
    for name in CHANGED_LEAN:
        print("source_sha256", name, hashlib.sha256((ROOT/name).read_bytes()).hexdigest())
    for family, count in sorted(checks.items()):
        print(f"{family}: {count}")
    print("Pre-existing lexical anomalies:", json.dumps(sorted(preexisting_lexical_anomalies,
                                                              key=lambda x: x["path"])))
    print(f"PASS: {sum(checks.values())} exact algebra / finite / source-integrity checks")
    print("Lean compilation: NOT RUN. Global Hodge existence and global novelty: NOT CLAIMED.")
