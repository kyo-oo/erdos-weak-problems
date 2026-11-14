# table939_w66/ — THE W66-P939-E WITNESS-TABLE PACKAGE (Erdős #939, r=4)

Independent second-method census + kernel-embeddable witness tables for the
**box theorem**: *every pair (a, b) of 4-powerful numbers with a + b
4-powerful and a + b ≤ B has gcd(a, b) > 1* — equivalently (gcd-equality
lemma below) there is **no pairwise-coprime 4-powerful triple a + b = c ≤ B**.

Engine: `../engine939_w66.py` (generation = layered per-prime sorted-merge DP;
sum census = mod-16 lane decomposition, cross-validated at 1e13 by a
transparent structure-free double loop, EXACT agreement).
Self-audit: `check939_w66.py` (independent re-derivation: recursive-DFS
generation + brute double-loop census) → `CHECK939_W66_RESULT.txt`.

## Predicate and conventions

- **Predicate** (verbatim semantics of `Erdos939R4.lean`):
  `rpow 4 n = decide (1 ≤ n ∧ divAll 4 n n)`, i.e. n ≥ 1 and every prime
  divisor p of n satisfies p⁴ ∣ n. Equivalence with the Lean fold was
  verified **literally** (divAll simulated over every e ≤ n, Lean `prime`
  fold simulated) on all n ≤ 3000 for r = 3, 4 — zero disagreements
  (engine log, phase `validate`, V1).
- **n = 1 edge**: 1 is vacuously 4-powerful (empty factorization; the
  divAll e = 1 row passes since `prime 1 = false`). **All emitted value
  lists INCLUDE 1**, matching the Lean predicate. The prior hunts
  (`hunt939d.py` gen4) dropped 1; counts are therefore reported BOTH ways
  (`count_incl_1` / `count_excl_1`) for comparability. `rpow4(0) = false`.
- **The triple 1+1=2 fails** since 2 is not 4-powerful (2¹ ∣ 2 but 2⁴ ∤ 2);
  in fact the census finds NO sum-hit involving the value 1 at any swept
  bound (any such hit would be a coprime witness; there are none).

## File inventory (per bound tag `T ∈ {1e13, 1e14, 1e15, 1e19}`)

| file | content |
|---|---|
| `values939_T.txt` | the FULL sorted 4-powerful value list ≤ T (incl 1), one per line |
| `values939_T.delta.txt` | delta encoding: first value, then successive gaps |
| `values939_T.lean.txt` | Lean list-literal chunks, 25 values per line (K60 census-row style) |
| `sumhits939_T.tsv` | every sum-hit pair: `a  b  c  gcd(a,b)  lane  pairwise_coprime` |
| `coverage939_T.json` | the coverage certificate (below) |
| `census939_T.progress.json` | transient lane checkpoint (deleted on clean finish) |
| `box19_progress.json` / `box19_stdout.txt` | the 1e19 background-box checkpoint/log |

1e19: values emitted as plain list only (EO/OO lanes swept; EE lane skipped —
it is never coprime-relevant since gcd ≥ 16, see lanes).

## The lane decomposition (why the census is COMPLETE)

For 4-powerful a, b, c with a + b = c ≤ B, parity forces exactly one lane:

- **EE**: a, b both even. Then 16 ∣ a, 16 ∣ b, so gcd(a, b) ≥ 16 — **never
  pairwise-coprime**; emitted for the full sum-hit table at 1e13–1e15 only.
- **EO**: e even, o odd, c odd. 16 ∣ e ⇒ **c ≡ o (mod 16)**. Sweep: for each
  odd mod-16 bucket r, all pairs o < c in the bucket with e = c − o tested
  for membership in the even list.
- **OO**: a, b both odd, c even 4-powerful ⇒ 16 ∣ c ⇒ **b ≡ −a (mod 16)**
  (the K60 `mod16_obstruction`). Sweep: complementary bucket pairs
  (r, 16−r), r ∈ {1,3,5,7}. (a = b is impossible in OO: 2a ≡ 0 mod 16
  forces a even.)

Every unordered pair of 4-powerful values falls in exactly one lane
(parity), and the mod-16 constraint inside EO/OO is forced by the sum being
4-powerful — so the three sweeps together see **every** candidate pair.
The 1e13 census additionally ran the **structure-free transparent double
loop** (all pairs of the sorted list, set-membership on the sum) and the
two hit lists agree **EXACTLY** (42,923 rows), certifying both the lane
logic and the implementation.

## The gcd-equality lemma (Lean-side, verified numerically on every hit)

For a + b = c: gcd(a, b) = gcd(a, c) = gcd(b, c) (any common divisor of a
and b divides c; any common divisor of a and c divides b = c − a). Hence
"pairwise coprime triple" ⟺ "gcd(a, b) = 1", and the single `gcd(a,b)`
column decides witness-hood. The engine asserts the equality on every
emitted hit (machine receipt in the log; 42,923 / 88,627 / 180,228 rows).

## Coverage certificate (`coverage939_T.json`)

- `count_incl_1` / `count_excl_1`, `parity`, `mod16_odd_buckets`,
  `per_decade_counts` (exact member count of each decade [10^k, 10^{k+1})),
  `min_gap` + `min_gap_pair` (13 at (243, 256) for 1e13 — the K60 gap law),
- `sorted_disjoint_ranges`: the value list compressed into consecutive
  maximal runs with gap ≤ 100 as `[lo, hi, count]` rows — disjoint, sorted,
  ordered; Σ count = `count_incl_1`; the checker re-validates every row;
- `lane_receipts`: per-lane check counts (EO per-bucket sizes; OO; EE);
- `sum_hits_total` / `sum_hits_by_lane`, `gcd_histogram` (all distinct
  gcd(a,b) values among hits), `min_hit_gcd` (16),
- **`zero_coprime_witnesses`: true** — no row of the sum-hit table has
  gcd(a, b) = 1; i.e. NO pairwise-coprime 4-powerful triple ≤ T;
- `sha256` of every emitted file (tamper-evidence).

## Intended Lean kernel route (for the killer lane)

1. Embed the value list as chunks (`values939_T.lean.txt`, 25/chunk) or the
   chunked bucket lists; membership rows via `List.all (rpow 4 ·)` in the
   K60 style (`census_r4_members`, closed goals — the S059 native_decide
   law applies to closed literal goals).
2. Prove the lane classification (parity ⇒ EE/EO/OO; the mod-16 forcing
   lemmas are one-liners from `rpow_prime_div`: `2 ∣ c → 2⁴ ∣ c`).
3. Prove the gcd-equality lemma (Nat.dvd_sub machinery).
4. Consume the sum-hit table: every row has gcd(a, b) ≥ 16 (min_hit_gcd),
   so EE is trivial and EO/OO rows each fail coprimality — the box theorem
   for T follows from (2) + the embedded, checksummed hit table + coverage
   certificate (the checker's independent re-derivation is the python-side
   soundness receipt).

## Reproducibility

- `python3 ../engine939_w66.py validate` — Lean-fold equivalence + brute
  cross-checks (16 s).
- `python3 ../engine939_w66.py census 13|14|15` — full census + emission.
- `python3 ../engine939_w66.py counts` — generation-only counts.
- `python3 ../engine939_w66.py box19` — the 1e19 box (background; writes
  `box19_progress.json` checkpoints, resumable).
- `python3 check939_w66.py` — independent re-derivation + file audit.
