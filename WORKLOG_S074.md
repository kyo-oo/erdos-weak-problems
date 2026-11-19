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
