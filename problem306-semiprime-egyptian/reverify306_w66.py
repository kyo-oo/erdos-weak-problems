#!/usr/bin/env python3
"""W66-P306-E SECOND-METHOD REVERIFICATION of every surviving #306 receipt.

Fresh code path (no reuse of the hunt engines' verification):
  * pure `fractions.Fraction` exact arithmetic for every claimed identity;
  * every denominator certified a DISTINCT-PRIME semiprime n = p*q, p < q,
    with p and q certified prime by trial division (independent of sympy);
  * pairwise distinctness of each term list.

Corpus (the receipts of record surviving on git):
  SRC-A  problem306-semiprime-egyptian/EVIDENCE_306_W63.json  (W63-D5 census)
  SRC-B  EVIDENCE_306.txt                                      (round-1 hunt output, root)
  SRC-C  the 19 decide-certified identities embedded in Erdos306.lean
         (e306_rep_board), parsed straight out of the Lean source.

Verdict file: REVERIFY306_W66.txt.  Any mismatch is reported CRITICAL.
"""
import json
import re
import sys
from fractions import Fraction

HERE = "/home/z/waves/w66-p306-e/problem306-semiprime-egyptian"
ROOT = "/home/z/waves/w66-p306-e"

# ---------------------------------------------------------------- primes
def is_prime_trial(n: int) -> bool:
    """Trial division primality (fresh, independent of sympy)."""
    if n < 2:
        return False
    if n % 2 == 0:
        return n == 2
    if n % 3 == 0:
        return n == 3
    d = 5
    while d * d <= n:
        if n % d == 0 or n % (d + 2) == 0:
            return False
        d += 6
    return True

def semiprime_p_lt_q(n: int):
    """Return (p, q) with p < q both prime and p*q == n, else None."""
    if n < 6:
        return None
    d = 2
    while d * d <= n:
        if n % d == 0:
            p, q = d, n // d
            if p < q and is_prime_trial(p) and is_prime_trial(q):
                return (p, q)
            return None  # any other divisor pattern fails p<q distinct-prime
        d += 1
    return None

def certify_dens(dens):
    """Certify each denominator is a distinct-prime semiprime p<q (p,q prime
    by trial division).  Returns list of (p,q) or None on failure."""
    out = []
    for n in dens:
        pq = semiprime_p_lt_q(n)
        if pq is None:
            return None
        out.append(pq)
    return out

# ---------------------------------------------------------------- sources
def parse_rational(key: str):
    a, b = key.split("/")
    return int(a), int(b)

def load_src_a():
    """EVIDENCE_306_W63.json: {'done': {key: [dens...]}, 'failed': [...]}."""
    st = json.load(open(f"{HERE}/EVIDENCE_306_W63.json"))
    return {k: v for k, v in st["done"].items()}

def load_src_b():
    """EVIDENCE_306.txt lines 'a/b = 1/n1 + 1/n2 + ...' (skip header lines)."""
    receipts = {}
    for line in open(f"{ROOT}/EVIDENCE_306.txt"):
        line = line.strip()
        if not line or line.startswith("#") or "=" not in line:
            continue
        m = re.match(r"^(\d+)/(\d+)\s*=\s*(.*)$", line)
        if not m:
            continue
        a, b = int(m.group(1)), int(m.group(2))
        dens = [int(x) for x in re.findall(r"1/(\d+)", m.group(3))]
        receipts[f"{a}/{b}"] = dens
    return receipts

def load_src_c():
    """The 19 embedded receipts from Erdos306.lean e306_rep_board.

    Each conjunct: `D / n1 + D / n2 + ... = D / b` | `k * (D / b)` | `D / D`.
    The first conjunct `6 / 6 = 1` is the 1/6 single-term rep (D=6).
    Returns {key: dens} with key the reduced a/b name, cross-checked."""
    text = open(f"{HERE}/Erdos306.lean").read()
    i = text.index("theorem e306_rep_board")
    j = text.index(":=", i)  # end of the statement (proof block follows)
    body = text[i:j]
    k = body.index(":")  # drop the 'theorem ... :' header
    body = body[k + 1:]
    conjuncts = [c.strip().strip("()") for c in body.split("∧")]
    receipts = {}
    notes = []
    for c in conjuncts:
        c = c.replace("\n", " ")
        # rhs: either `D / b` or `k * (D / b)`
        m2 = re.match(r"^(.*?)=\s*(?:(\d+)\s*\*\s*)?\(?\s*(\d+)\s*/\s*(\d+)\s*\)?\s*$", c)
        if m2:
            lhs, k, D, b = m2.group(1), m2.group(2), int(m2.group(3)), int(m2.group(4))
            a = int(k) if k else 1
        else:
            # `6 / 6 = 1` form (the 1/6 receipt)
            m3 = re.match(r"^(\d+)\s*/\s*(\d+)\s*=\s*1$", c)
            assert m3, f"unparsed conjunct: {c!r}"
            D = b = int(m3.group(1))
            lhs, a = f"{D} / {D}", 1
        pairsL = re.findall(r"(\d+)\s*/\s*(\d+)", lhs)
        dens = [int(n) for (p, n) in pairsL if int(p) == D]  # keep D/n items only
        assert all(int(p) == D for p, _ in pairsL), c
        # name: reduce a/b
        from math import gcd
        g = gcd(a, b)
        key = f"{a // g}/{b // g}"
        receipts[key] = dens
        notes.append((key, D, a, b))
    return receipts, notes

# ---------------------------------------------------------------- verify
def verify_receipt(a, b, dens, src, failures):
    """Full second-method verification of one claimed receipt."""
    tag = f"[{src}] {a}/{b}"
    ok = True
    if not dens:
        failures.append(f"CRITICAL {tag}: EMPTY TERM LIST")
        return False
    if len(dens) != len(set(dens)):
        dups = sorted({n for n in dens if dens.count(n) > 1})
        failures.append(f"CRITICAL {tag}: DUPLICATE DENOMINATORS {dups}")
        ok = False
    pq = certify_dens(dens)
    if pq is None:
        bad = [n for n in dens if semiprime_p_lt_q(n) is None]
        failures.append(f"CRITICAL {tag}: NON-(p<q)-SEMIPRIME DENOMINATORS {bad}")
        ok = False
    s = sum(Fraction(1, n) for n in dens)
    if s != Fraction(a, b):
        failures.append(
            f"CRITICAL {tag}: SUM MISMATCH  sum={s}  claimed={a}/{b}  dens={dens}")
        ok = False
    return ok

def main():
    lines = []
    P = lines.append
    P("=" * 78)
    P("W66-P306-E SECOND-METHOD REVERIFICATION — full surviving receipt corpus")
    P("=" * 78)

    srcA = load_src_a()
    srcB = load_src_b()
    srcC, notesC = load_src_c()
    P(f"SRC-A EVIDENCE_306_W63.json : {len(srcA)} receipts (W63-D5 census, b<=21 families)")
    P(f"SRC-B EVIDENCE_306.txt      : {len(srcB)} receipts (round-1 hunt, b<=30 scattered)")
    P(f"SRC-C Erdos306.lean embedded : {len(srcC)} receipts (decide-certified kernel identities)")

    failures = []
    okA = sum(verify_receipt(*parse_rational(k), v, "SRC-A", failures) for k, v in srcA.items())
    okB = sum(verify_receipt(*parse_rational(k), v, "SRC-B", failures) for k, v in srcB.items())
    okC = sum(verify_receipt(*parse_rational(k), v, "SRC-C", failures) for k, v in srcC.items())

    P("")
    P("-" * 78)
    P(f"SRC-A verified {okA}/{len(srcA)}")
    P(f"SRC-B verified {okB}/{len(srcB)}")
    P(f"SRC-C verified {okC}/{len(srcC)}")

    # union represented set with provenance names
    union = {}
    for k, v in srcA.items():
        union.setdefault(k, {"dens": v, "srcs": []})["srcs"].append("A")
    for k, v in srcB.items():
        u = union.setdefault(k, {"dens": v, "srcs": []})
        u["srcs"].append("B")
    for k, v in srcC.items():
        u = union.setdefault(k, {"dens": v, "srcs": []})
        u["srcs"].append("C")
    # cross-source consistency for shared keys
    for k, u in union.items():
        if "A" in u["srcs"] and "B" in u["srcs"] and srcA[k] != srcB[k]:
            P(f"NOTE {k}: SRC-A and SRC-B disagree on the witness list "
              f"(A {len(srcA[k])} terms vs B {len(srcB[k])}) — both independently "
              f"verified, distinct valid representations.")
        if "C" in u["srcs"] and "A" in u["srcs"] and srcC.get(k) != srcA.get(k):
            P(f"NOTE {k}: kernel receipt differs from census receipt "
              f"(both verified independently — distinct valid representations).")

    P("")
    P("-" * 78)
    P(f"UNION REPRESENTED SET: {len(union)} distinct rationals "
      f"(all second-method verified unless listed CRITICAL below)")

    # the 181 universe
    from math import gcd as _gcd
    def squarefree(b):
        f = []
        d, n = 2, b
        while d * d <= n:
            while n % d == 0:
                f.append(d)
                n //= d
            d += 1
        if n > 1:
            f.append(n)
        return len(f) == len(set(f))
    uni = []
    for b in range(2, 31):
        if squarefree(b):
            for a in range(1, b):
                if _gcd(a, b) == 1:
                    uni.append((a, b))
    repd = [t for t in uni if f"{t[0]}/{t[1]}" in union]
    P(f"census box position: {len(repd)}/{len(uni)} rationals "
      f"(b squarefree <= 30) already represented by verified receipts")
    remain = [f"{a}/{b}" for a, b in uni if f"{a}/{b}" not in union]
    P(f"remaining: {len(remain)}: {remain}")

    P("")
    P("-" * 78)
    P("THE FULL REPRESENTED-SET LIST (name: terms, provenance A/B/C):")
    for k in sorted(union, key=lambda s: (int(s.split('/')[1]), int(s.split('/')[0]))):
        u = union[k]
        P(f"  {k:6s} {len(u['dens']):3d} terms  max den {max(u['dens']):8d}  "
          f"src={''.join(u['srcs'])}")

    P("")
    if failures:
        P("!" * 78)
        P("CRITICAL FAILURES — THE CORPUS HAS MISMATCHES:")
        for f_ in failures:
            P(f"  {f_}")
        P("!" * 78)
    else:
        P("VERDICT: ALL RECEIPTS REVERIFIED CLEAN — zero mismatches, zero "
          "non-(p<q)-semiprime denominators, zero duplicate denominators, "
          "zero sum mismatches.")
    open(f"{HERE}/REVERIFY306_W66.txt", "w").write("\n".join(lines) + "\n")
    print("\n".join(lines))
    return 1 if failures else 0

if __name__ == "__main__":
    sys.exit(main())
