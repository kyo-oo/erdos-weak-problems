#!/usr/bin/env python3
"""Exact bounded physical CommonTwo first-hit experiment (NOT a universal proof).

For each K in 5..max_K, compute literal 4^K and 4^(K+1), divide them
by three digit-by-digit, and test every possible positive ternary row.
The loop continues until every source digit above the current row is zero.
No floating-point values, random samples, fixed digit cutoff, or
hypothetical HGate are used.
"""
import argparse

def scan(max_k: int):
    if max_k < 5:
        raise ValueError("max_k must be at least 5")
    source = 4**5
    missing = []
    records = []
    max_first_row = 0
    total = 0
    for k in range(5, max_k + 1):
        if k > 5:
            source *= 4
        left, right, row, found = source, 4 * source, 0, None
        while left:
            if row >= 1 and left % 3 == 2 and right % 3 == 2:
                found = row
                break
            left //= 3
            right //= 3
            row += 1
        total += 1
        if found is None:
            missing.append(k)
        elif found > max_first_row:
            max_first_row = found
            records.append((k, found))
    return total, missing, max_first_row, records


def main():
    parser = argparse.ArgumentParser()
    parser.add_argument("--max-k", type=int, default=50000)
    args = parser.parse_args()
    count, missing, max_row, records = scan(args.max_k)
    print("SCAN_K=5..", args.max_k, sep="")
    print("EXACT_EXPONENTS=", count, sep="")
    print("NO_COMMON_TWO_K=", missing, sep="")
    print("MAX_FIRST_HIT_ROW=", max_row, sep="")
    print("RECORD_FIRST_HIT_ROWS=", records, sep="")
    print("FINITE_EXPERIMENT_ONLY=1")


if __name__ == "__main__":
    main()
