# Audit — Round 43 — 2026-11-07

## Verdict: PASS

## Fidelity
The audit's own clean re-run of the canonical certificate: exit 0, 96 checks,
0 failures, **byte-identical to runA.txt (md5 2aced9a3583eff2b104b089391936e12)** —
the third independent run (after the double-run seal). Deterministic ✓.

## Sabotage battery (every control FIRED with the predicted failure class)

- **S1 (the rigidity law)**: the T-stability filter weakened to the first 20
  subspaces → exit 1, the RIGIDITY LAW checks FAILED at 4+ T-classes
  ("EXACTLY 20 T-stable K's" ≠ 2) — the rigidity claim is load-bearing. FIRED ✓
- **S2 (the census exhaustion)**: one world deleted before the census count →
  exit 1, "CENSUS CROSS-CHECK DISAGREEMENT at T4 K|32|: pair-sweep 1 vs
  cohomology 0 worlds" — the census two-algorithm receipt caught the deleted
  world. FIRED ✓
- **S3 (the two-algorithm sign)**: the y-space parity bit inverted → exit 1,
  **160 TWO-ALGORITHM DISAGREEMENTS** (775/935 vs the sealed 935/935) — the
  sparse engine is load-bearing at every stabilizer-signed orbit. FIRED ✓
- **S4 (the split-surplus rigging)**: one basis system dropped from the split
  battery → exit 1, THE SPLIT-TYPE SURPLUS check FAILED (a nonzero surplus
  appeared under the rigged span). FIRED ✓
- **S5 (the leaf lattice)**: the full-lattice basis truncated by one → exit 1,
  THE LEAF LATTICE CERTIFICATE check FAILED (rank mismatch). FIRED ✓

## Claim match (the header COVERAGE vs the checks inventory): 14/14 matched

(a) the W-model receipts (9 checks) ✓ (b) THE RIGIDITY LAW at 5 T-classes ✓
(c) the cohomology receipts at all 10 (T,K) pairs (cocycle counts, B¹ ⊆ Z¹,
the full-cocycle paranoia) ✓ (d) the census two-algorithm 6/6 ✓ (e) the
two-algorithm 935/935 + the dense-RREF 336/336 ✓ (f) the boundary laws:
binomial 197 / split 80 / the deeper bucket EMPTY (the rigidity corollary) ✓
(g) THE EXCEPTIONAL-CLASS LAW at degree 10 (no recurrence; the measured
statement) ✓ (h) the split-type surplus (3 reps, full p-range) ✓ (i) the
E×A disjoint-frame law (3 disjoint + 1 coupled disclosed) ✓ (j) the
g-uniformity at g = 2, 3, 5 ✓ (k) the degree-8 re-run (114 worlds / 58
boundary / 16 exceptional types — the R41 reproduction) ✓ (l) THE LEAF
LATTICE (16 types, free rank-2, torsion-free, saturation 1) ✓ (m) the R3
extension (h = 3, 4 vanishing + the matched 2h control) ✓ (n) the hostiles
H1–H7 + the mechanical vacuity scan ✓.

## Findings

- **F1 (minor)**: the E×A section header says "bounded: 4 frames"; the run
  measured 3 disjoint frames (1 coupled frame skipped per the disclosed
  bound). The check message discloses the skip honestly — no repair required.
- **F2 (minor, process)**: the independent-agent dispatch failed (the
  infrastructure context deadline — the documented R32/R37/R41 class, third
  occurrence); the audit was orchestrator-discharged with the full battery
  above. Disclosed.
- **F3 (minor)**: the pair-sweep census cross-check covers 6/10 (T,K) pairs
  (the A₅/S₅-⟨ρ₀⟩ pairs outside the |T| ≤ 24 bound); the cohomology engine
  carries them with the closure/centrality/cocycle receipts. Disclosed in
  the check message.

## Required repairs before claiming success

- [ ] none (PASS)
