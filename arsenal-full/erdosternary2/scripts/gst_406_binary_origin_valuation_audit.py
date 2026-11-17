#!/usr/bin/env python3
"""
Exact GST Problem 406 binary-origin valuation discriminator.

This is NOT a proof of the unbounded valuation conjecture or the
unconditional CommonTwo(K) target. The program checks all positive R<3^L,
R=1 (mod 3), divisible by 2^(floor(3L/2)+1), for each selected length L.
It asks if R and 4R avoid a shared ternary digit 2 at every positive row.

The source-neighbor predicate is computed independently in TWO forms:
(1) GST four-carry automaton (fast);
(2) literal ternary integer digit quotient (exhaustively cross-checked
    on the first 3^8 positive sources before the large test).
"""
from __future__ import annotations
import argparse
import sys

def gst_bad_source(source: int) -> bool:
    assert source > 0
    carry = 0
    row = 0
    while source:
        trit = source % 3
        if row >= 1 and trit == 2 and carry in (0, 3):
            return False
        carry = (4 * trit + carry) // 3
        source //= 3
        row += 1
    return True

def physical_bad_source(source: int) -> bool:
    source_neighbor = 4 * source
    row = 0
    while source:
        if row >= 1 and source % 3 == 2 and source_neighbor % 3 == 2:
            return False
        source //= 3
        source_neighbor //= 3
        row += 1
    return True

def audit(lo: int, hi: int) -> tuple[int, list[tuple[int,int,int]]]:
    for source in range(1, 3**8):
        assert gst_bad_source(source) == physical_bad_source(source), source
    seen = 0
    violations = []
    for L in range(lo, hi + 1):
        t = (3 * L)//2 + 1
        max_multiplier = (3**L - 1) // (1 << t)
        required_mod_three = 1 if t % 2 == 0 else 2
        count = 0
        for q in range(required_mod_three, max_multiplier + 1, 3):
            source = q << t
            assert 0 < source < 3**L and source % 3 == 1
            count += 1
            if gst_bad_source(source):
                assert physical_bad_source(source)
                violations.append((L,t,source))
                print("EXACT_BARRIER_COUNTEREXAMPLE",L,t,source,flush=True)
        seen += count
        if L % 20 == 0 or L == hi:
            print(f"L={L} candidate_count={count} cumulative={seen}",flush=True)
    return seen, violations

def main() -> int:
    parser = argparse.ArgumentParser()
    parser.add_argument("--from-length",type=int,default=10)
    parser.add_argument("--to-length",type=int,default=240)
    a=parser.parse_args()
    if a.from_length<1 or a.to_length<a.from_length:
        parser.error("invalid length bounds")
    count, violations=audit(a.from_length,a.to_length)
    print(f"EXACT_SOURCE_CANDIDATES_CHECKED={count}")
    print(f"EXACT_HIGH_VALUATION_BAD_SOURCE_VIOLATIONS={len(violations)}")
    print("NONCLAIM=No universal exponent theorem is established by this finite check.")
    return 1 if violations else 0

if __name__=="__main__":
    sys.exit(main())
