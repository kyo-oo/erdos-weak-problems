# AUDIT939 — THE PRIOR-HUNT ENUMERATION BUG (found W62, Task 1-b)

**Erdős #939, r=4 lane. Verdict: every prior Python hunt for this problem
enumerated the WRONG SET. All recorded r=4 "zero" coverage claims are void.**

## The bug

`hunt939b.py` (≤ 10^15 pair sweep) and `hunt939c.py` (Routes 2 and 3) generate
their "4-powerful" lists with this recursion:

```python
v = val * q           # q = p ** 4
while v <= LIMIT:
    rec(j + 1, v)
    v *= q            # <-- exponents 4, 8, 12, ... MULTIPLES OF 4 ONLY
```

Multiplying only by `p**4` at every step produces exactly the numbers whose
prime exponents are **multiples of 4** — i.e. the **perfect fourth powers**
`m^4`. The TRUE 4-powerful numbers (definition of the campaign's own K60 Lean
kernel: every prime divisor `p` of `n` satisfies `p^4 | n`, i.e. every prime
exponent `>= 4`) include `2^5 = 32`, `2^5*3^4 = 2592`, `2^4*3^5 = 3888`,
`5^5 = 3125`, ... — **none of which are fourth powers** — and all of them are
missing from the prior engines' lists.

## The receipts

1. Reproduced this round (see `hunt939d_output.txt` Phase A): the hunt939b-style
   generator yields exactly **1777** values ≤ 10^13 = the number of fourth powers
   `m^4 <= 10^13` (`m = 2..1778`), matching the WORKLOG S062 record "1,777
   4-powerfuls". `32 = 2^5` — certified `rpow 4 32 = true` in
   `Erdos939R4.lean` and a member of the K60 census row — is **absent** from
   that list. Same for `2592 = 2^5*3^4` (also in the K60 census row).
2. hunt939c's Phase-A line "4-powerful <= 1e16: 9999" = the number of fourth
   powers ≤ 10^16 (m = 2..10^4). The TRUE count is **73,698**.
3. The TRUE counts (correct enumerator, validated to reproduce the K60 Lean
   census row exactly at 10^4):
   - 10^13: **11,653** (vs 1,777 enumerated by the buggy engine)
   - 10^15: **40,048**
   - 10^16: **73,698** (vs 9,999)
   - 10^17: **135,058**
   - 10^18: **246,652**
   - 10^19: **449,087**

## What the prior claims actually covered

- "ZERO ≤ 10^13 / 10^15" (hunt939b): the pairs swept were pairs of **fourth
  powers** with sums checked against a list of **fourth powers** — i.e. the
  equation `x^4 + y^4 = z^4`, which is **Fermat's Last Theorem for exponent 4**
  (Fermat's own descent). Zero solutions, unconditionally — but this is
  FLT-void coverage: it says nothing about the 4-powerful problem.
- hunt939c Route 2 ("all coprime 4th-power pairs x^4+y^4 with sum 4-powerful,
  c ≤ 10^16: ZERO"): the c-list was fourth powers — again `x^4 + y^4 = z^4`
  (FLT-void).
- hunt939c Route 3 (Sophene-Germain family): the factor membership test used
  the same fourth-power list, so the "ZERO factor-hits" statement again only
  tested `x^2 ± 4xz + 8z^2` being a fourth power — not the 4-powerful property.
- The Lean kernels (Erdos939.lean / Erdos939R4.lean) are **unaffected**: their
  `rpow` definition and all 25 census values are correct. The bug was in the
  Python hunt engines only.

## The corrected engine (this round)

`hunt939d.py` / `hunt939e.py`: correct enumeration (exponents 4, 5, 6, ...),
generator validated two ways (Lean census row reproduction at 10^4 + brute-force
cross-check of the bucketed pair lanes at 10^7), with the exhaustive box swept
to 10^18 and 10^19 and the algebraic families (diff-of-fourth-powers,
Sophie-Germain, Route-2 quartic twists) swept far beyond the box. See
`hunt939d_output.txt`, `hunt939e_output.txt`, `STATUS.md`.
