# WORKLOG S074 — THE CAP-LAW REDUCTION ROUND (W75)

**Session type:** hypothesis assault (BOSS's order: "crack the hTailF
hypothesis, completely, go full proof the hypothesis"). English only.

## The order and the intake

BOSS ordered: get the zip bag from the chat share link (done: Drive
download, token restored, campaign branch cloned at `da24660` = S073
FINAL SEAL), read the entire #406 history (done: the climb, the act, the
two primitives, the feedback tree, the dust, the third-wave gate, the
countermodel walls, the 2.482^p entropy row, Postulate II), and crack
`hTailF` completely, using only BOSS's own mathematics, GitHub CI for
Lean, and the DeepMind comparator statements.

## The war council (MATHS §6, both modes)

- Strategist agent (external): verified the kill chain end-to-end,
  audited the provenance, found the HOLE — `MonolithBoundary.lean`'s
  terminal identity is an unverified external postulate in this repo
  (the proofs live in the unvendored `sol/kyo-gate-universe-wire` branch,
  18,493 lines; the repo's copy is the bulldoze branch at 17,051) — and
  specified the DIRECT PORT (the act + green odd half + decide
  instances → the challenge statement, zero external inputs).
  ALSO found: the cap law at C=3 IS the monolith's POSTULATE II
  (ErdosTernary2.lean:858, certified only below 3^9, universal case
  stalled), and the monolith itself says "From Postulate II the Erdős
  conjecture follows" — without the constant arithmetic.
- Doubter + Attacker dispositions (internal, §6 Mode B): the dust census
  to 200000 (no counterexample; death depth ≤ 35); the extremal 2-adic
  curve v2*(M) to M=34 (excess ≤ +4); the ladder/binomial-transform
  analysis (the three disguises of the alternating binomial transform:
  the mod-8 multiplicity cascade, the (4−1)^i expansion, the moment
  ladder — all the same object); the anti-concentration wall confirmed
  as the obstruction (the rider sits exactly at the trivial magnitude
  bound; every known route caps at ~2M).

## THE BREAKTHROUGH (the actual truth of this round)

The kill chain: a rider K has v2(4^K) = 2K EXACTLY and leading position
M = ⌊log₃ 4^K⌋ ≤ 1.26186·K. A cap law v2 ≤ M + C forces
2K ≤ 1.26186K + C → K ≤ 1.3547·C. With C = 185: K ≤ 250 — EXACTLY
inside the Kernel-38 census range (62·250 = 15500 < 15540 = 84·185 <
15562 = 62·251, certificate 2^84 < 3^53, kernel-decided). **The
monolith's stalled Postulate II (C=3) is SIXTY TIMES STRONGER than what
the full kill needs. The campaign's target is now C ≤ 185.**

## The delivery (this push)

1. `problem406-ternary-powers/CapLaw406.lean` (Kernel 68): the rider
   squeeze (`cap_squeeze`: the 2^84 < 3^53 certificate + the power-chain
   absurdity), the rider bound (`cap_rider_bound`), the Postulate-II
   instantiation (C=3 → complete classification {0,1,4} at every
   exponent, K=2,3 by kernel decide), the C=185 weak-cap instantiation
   (`erdos406_no_riders_above_250_of_cap`), the census composition
   (`erdos406_classification_of_cap_and_census`). Zero sorry, axiom
   receipts printed, self-contained monotonicity toolkit (only green
   idioms: omega, decide, Nat.mul_le_mul, Nat.pow_succ/pow_add/pow_mul,
   .eq_def, Nat.strongRecOn, Nat.mul_pos).
2. `problem406-ternary-powers/caplaw/`: battery_caplaw.py (dual-method,
   ALL GREEN: certificate, boundaries, small table, v2* curve, witnesses,
   census, the C=3 cap on primitive Cantor n < 3^12 with equality only at
   256), v2star_table.json (M=0..34), dust_census.md, MANIFEST.md.
3. `COMPLETE_PROOF.md` §10: the reduction theorems with FULL proofs,
   the empirical backbone, the honest boundary.
4. `kills.yml`: Kernel 68 job (Kernel-38 pattern, arsenal prebuild +
   lake env lean + axiom greps + battery).

## The honest scope

The cap law CAP(C) is not proven for any C at unbounded range — the
anti-concentration wall stands (same class as the registry's Stewart
verdict; the war council's ladder analysis shows every deterministic
route caps at ~2M = the trivial bound). What is delivered: the
machine-checked reduction with the sixty-fold weakened target, the
extended censuses, the provenance repair route (direct port), and the
extremal-curve intelligence (the extremals are MITM blocks, not
self-similar — no known infinite ascent).

## Next strikes

(a) Attack CAP(C) at C ≤ 185 directly: the multiplicity-cascade descent
with constraint propagation (the 9 ≡ 1 mod 8 ladder), the binomial
lattice counting, the group-theoretic zero-sum angle (subset sums of
geometric progressions mod 2^t).
(b) The direct-port assembly to the DeepMind challenge surface
(the tern01/noTernaryTwo bridge, then full_erdos_of_the_act + the odd
half + no22_four_pow_five/six/seven → erdos_ternary_2, the challenge
statement verbatim) + the comparator-official/challenges/406 gate.
(c) The dust-tree census to 3^23 (the DOUBTER's channel, deferred under
context pressure this round).

The engine never stops; it never lies. In English, always.

---

## E05 — LANDED WORK (the wave + the commander surgery)

The dispatcher context-deadline mode killed the launch reports (the W64-W66
false-negative law); all six lanes LANDED and executed — four delivered
substantial artifacts before falling (the documented W66 mode); the commander
executed the remainder directly. Lane branches all pushed:

- **w75-61K (e03798a + the correction commit)**: THE 4-VERTEX COMPLETION —
  THEOREM PAW (max(α,ω) ≥ √(n/5) via the component law n ≤ 4α² + αω; the
  Olariu structure theorem re-derived in-package; the first draft's α-only
  form REFUTED by the 61E negative control and corrected in-round),
  THEOREM DIAMOND (max ≥ n^{1/3}/2 via the N(v)-cluster law), the 2K2
  package (THEOREM 2K2-TF triangle-free √n/2, THEOREM 2K2-DEC the
  eight-class triangle decomposition with the proved laws, the C5-attachment
  17-type law), the P3+K1/K2+2K1 complement transfers — NINE of eleven
  4-vertex graphs EH-closed in-package. Engine 14/14 GREEN + the 731,523-graph
  2K2 census addendum (αω ≥ 4n/5 verified, equality exactly at C5).
- **w75-61E (5ac477d)**: THE COMPLETE CENSUS n=1..8 ALL GREEN (537s) — the
  five targets' h-rows [2,2,2,2,3,3,3] certified (n=8 via the exhaustive
  2^28 m=3-stratum scan), dual-lane agreement, complement self-test clean,
  the corrected inheritance law, the L4a refutation + L4b/L4c correct laws,
  the L5 checker bug found and fixed (transitivity), witness families,
  banked claims re-derived.
- **w75-107K (672f895)**: the n=8 order-type enumeration with the commander's
  REALIZATION-DIVERSITY FIX — ROOT-CAUSE DISCOVERY: the cell set of the
  pair-line arrangement is NOT an order-type invariant (cells cross 3-line-
  concurrency walls within a type's realization space; single-realization
  insertion provably misses children; 1 mirror-closure failure exhibited and
  diagnosed; diversification recovers 13 identified types: 3313/3315).
  The adversarial six-point-lemma refutation (the engine caught the brief's
  false lemma with an exact counterexample before it shipped).
- **w75-107E (5af0c4e)**: the order-type C-accelerated engine, THEOREM
  CUPCON (every k-cup in convex position — the full orientation-sign proof)
  ⟹ f(6) ≤ 71 complete in-package; the certified E-cluster family for the
  32-point n=7 witness (all six clusters green); the honest grid-stabilization
  scoping.
- **w75-142K (01a216a)**: THE DENSITY-INCREMENT PACKAGE — THEOREM V
  (Varnavides amplification, explicit constants), THEOREM F1/F2 (the exact
  Fourier counting identity machine-exact at p=101/199 + the δ²p/2
  large-coefficient extraction), LEMMA I (the circle-arc density increment
  δ + δ²/256 on progressions of length pδ/64), the transfer law, ITER-CK
  model-step checkpoints — engine 25/25 GREEN; the full Roth assembly's
  status stated exactly (the model-step induction is the named remaining
  component).
- **w75-142E (the SAT table)**: r_3(31..48) = 12,13,13,13,13,14,14,14,14,15,
  16,16,16,16,16,16,16,16 — every value TRIPLE-SOLVER certified (MinisatGH +
  Cadical153 + z3 all UNSAT at t+1) with brute-checked witnesses;
  **THEOREM BLOCK-SHARP: r_3(N) ≤ N/3 + 48** (the certified ratio exactly
  1/3 at m=48). The table is monotone N=1..48.

The engine-level adversarial catches this round (each made the mathematics
correct): the α-only PAW form refuted (complete multipartite control); the
naive 6-point lemma refuted (concentric triangles); the B4 inheritance
direction flipped (h_P3(5)=3 > h_P4(5)=2); the L5 checker bug; the L4a→L4b
law correction; the arrangement-cell realization-dependence discovery.

## E06 — THE GATE INTEGRATION (the triple OKAY)

The three official DeepMind comparator ledgers extended: 142: 8 → 14 claims
(+C142-R3-TABLE-EXT, C142-BLOCK-SHARP, C142-VARNVIDES, C142-FOURIER-KEY,
C142-INCREMENT-ARC, C142-SUBLINEAR-PACKAGE); 61: 9 → 15 (+C61-PAW, C61-P3K1,
C61-DIAMOND, C61-K2-2K1, C61-2K2-STRUCTURE, C61-FOURVERTEX-CLASSIFICATION);
107: 9 → 13 (+C107-CUPCON, C107-CLUSTER7, C107-OT8, C107-SIXPOINT-REFUTATION).
New self-contained driver checks: S-TABLE-EXT (embedded witnesses + live z3
UNSAT), S-BLOCK-SHARP, S-VARNVIDES, S-FOURIER (142); S-PAW, S-CENSUS-61,
S-2K2-STRUCT (61); S-CUPCON, S-CLUSTER7, S-OT8 (107). kills.yml thresholds
raised to the new exact floors (142 ≥ 20, 61 ≥ 14, 107 ≥ 13).

LOCAL GATE VERDICTS (this round, after the in-round defect repairs):
- `official_gate.py 142`: **20/20 PASS — VERDICT: YOUR SOLUTION IS OKAY**
- `official_gate.py 61`: **14/14 PASS — VERDICT: YOUR SOLUTION IS OKAY**
- `official_gate.py 107`: **14/14 PASS — VERDICT: YOUR SOLUTION IS OKAY**

(The repairs: S-FOURIER's math→cmath; S-PAW's pattern unpacking + the
max-form correction cascade; S-OT8's bucket-then-canonicalize; absl-py
installed locally — the CI route already carried it.)
