# AUDIT-36 — the independent adversarial audit of Round 36 (the field-letter pairing-generation strike)

**Date**: 2026-11-04 (session clock). **Scope**: the certificate
`research/experiments/field_letter_generation_round36_checks.py`, its receipts, the
round record, the derivation's finite claims, the Lean face labels.
**Composition** (the §36 budget line: strike = the full authoring session; audit +
repair + push = this continuation session; ONE loop): Part A — an independent
fresh-agent adversarial audit (certificate scope; the full-scope dispatch hit the
infra deadline twice — the documented Round-32/35 class — so the audit was split
per that precedent); Part B — the orchestrator's different-algorithm recompute of
the mathematics, the citation/label checks, and the batched repairs.

**Provenance note (the scar, recorded honestly)**: the Round-36 record as left by
the authoring session REFERENCED this audit file before any audit had run — the
authoring session died between writing the record and executing the audit. The
reference was a receipt for work not yet done (the ledger-099/102 family at the
record layer). This file is the audit actually executed; ledger entry 110 records
the scar. Nothing in this file was written before the audit it reports.

---

## Part A — the fresh-agent adversarial audit (certificate scope)

**Verdict: PASS_WITH_REPAIRS_REQUIRED** — the certificate is live, deterministic,
and reproducible; every targeted sabotage makes the correct checks fail; nothing
is vacuous in the ledger-107 sense; but the ledger-109 label-predicate discipline
is violated in two material places (F1, F2) and weakened in four minors.

**Re-run receipts (the auditor's own)**: exit 0 twice; `RESULT: 660 checks
passed, 0 failed` twice; the two outputs byte-identical except the volatile
`runtime:` wall-clock line (stderr); the committed `runA.txt` byte-identical to
the auditor's re-run modulo that line; 660 `ok` lines, zero FAIL lines.

**Sabotage results (the auditor's, in /tmp copies only)**:
- sign flip in the descent epsilon → exactly the 4 descent-relation checks FAIL
  (clean isolation; the wrong-sign control still passes);
- orbit-count total perturbed (`|O|` → `1`) → 301 checks FAIL (64 two-algorithm
  agreements + 236 type-class invariance + 1 garbage control) — the two
  algorithms are genuinely different computations;
- deg-4 product truncation → 19 THE SPAN checks FAIL;
- unsigned brute-force character → FAILS at m=2 (10≠8) and m=4 (70≠64);
- a valid type fed to the garbage control → the garbage control FAILS (it is
  load-bearing);
- planted `or True` + self-comparison in a mutated copy → both self-scan checks
  flip to FAIL (the certificate's own scanners are live, not decorative).

**Vacuity scan (ledger-107 battery, run independently)**: zero hits for
`or True` / `and False` / `ok(True` / dead conditionals / self-comparisons /
arithmetic `is not None`; all 9 `sum(` sites genuine counting; ONE definitional
tautology found (the cross-field control, F4 below).

**Label-predicate review (ledger-109, per family)**: V1 descent instances OK;
the two-algorithm dim checks OK (call-graph verified independent); the degree-4
SPAN checks OK (span + membership both present); the degree-6 SPAN label GAP
(F1); degree-8 coverage claim in the header with NO degree-8 check (F2); the
hostile controls OK except F4; V5 totals OK but the brute-force cap (m ≤ 4)
contradicts the header's "(two algorithms)" for 208 and 688 (F5).

**Part A findings** (severity / location / issue / repair):
- **F1 (major)**: the degree-6 SPAN messages promise "the three-fold divisor
  products span Hdg_6" but only `product_rank_6 == dim Hdg_6` is tested — no
  membership check exists at degree 6 (degree 4 has one). If the triple products
  lay outside Hdg_6 with matching rank, the check would print ok on a false
  label.
- **F2 (major)**: the file header claims degree-8 span coverage
  ("and 6, 8: SURPLUS = 0 everywhere") but NO degree-8 product-span check exists
  anywhere in the file or receipt — the self-description overstates the coverage
  of the crux theorem.
- **F3 (minor)**: the non-diagonal pair hostile claims "EVERY off-diagonal
  balanced pair's G-orbit is MIXED" but a `break` limited the test to pairs
  anchored at Phi[0].
- **F4 (minor)**: `cross_field_check()` is a definitional tautology —
  `word_balance((a,b), Phi1∪Phi2) == 2` holds for any inputs by construction;
  the "Hom^0 = 0 transports nothing" parenthetical is not computed.
- **F5 (minor)**: the brute-force arity-total algorithm is capped at m ≤ 4
  while the header says "(two algorithms)" — the two largest committed totals
  (208 at m=5, 688 at m=6) were verified by the formula alone (the auditor's
  own timing: brute force costs 0.01 s / 0.05 s at m=5/6 and agrees).
- **F6 (minor)**: `res.get('subspan_rank_4', -1) < ...` is a fail-open default
  for the subspan hostile control.
- **F7 (nitpick)**: `Phi` is an unused parameter of `descent_instance`; the ok
  messages cite "Phi=[…]" as though type-dependence were exercised.

## Part B — the orchestrator's checks (this session)

**Different-algorithm recompute of the mathematics** —
`orchestrator_recompute_r36.py` (38/38 PASS, exit 0), engines deliberately
different at every load-bearing point: Φ_m from `sympy.cyclotomic_poly` (vs the
certificate's recursive division); inversion-count Leibniz determinants (vs
cycle-parity); `sympy.Matrix` nullspace/rank (vs the hand-rolled Fraction RREF)
**plus** own-code 𝔽_p Gaussian elimination at three primes (10007/10009/10037)
on the modular images (rational→modular via exact inverses); BFS frozenset orbit
counting (vs sorted-tuple orbit sets); permutation-matrix determinants for the
arity totals (vs the closed formula and the subset enumeration). Reproduced:
the orbit-count dims at every primitive shape (2/3/3/4; the binomial sequences
[2,1], [3,3,1], [4,6,4,1] at all four octic worlds); dim Hdg_2 = 4 and dim
Hdg_4 = 6 at m=15 primitive by sympy nullspace; THE SPAN rank 6 over Q and over
all three finite fields; the degree-4 product membership by independent
determinants; all six arity totals 4/8/24/64/208/688 by permutation
determinants. (Two orchestrator-side sampler defects were found and fixed
during this recompute — a truncating `int(c % p)` rational-to-modular
conversion, and `sympy.Matrix.rank()` computing the rational rank of residue
entries instead of the 𝔽_p rank — both were MY defects, not the certificate's;
both fixed by own-code exact conversion + own-code 𝔽_p elimination.)

**Citation checks (ledger-099, grepped against the sources in the clone at
HEAD 9911800)**: Round 35's Theorem S13(iii) names the non-elliptic high-End
face verbatim in both the Round-35 tex (§425–443) and the Round-35 record;
Round 35's Lemma 3.2 (the conjugation-stable Q(i)-descent) is named in the
Round-35 record's artifact line; Round 33's Theorem S5 (the divisor-twisted
curve-channel supply) exists as cited (§378 of the Round-33 tex). All
load-bearing citations verified against their sources.

**Receipt-number checks**: the record's numeric claims appear in the receipts —
the span receipts 1/3/9 (quartic/sextic) and 6/18/36 (octic, sixteen type
classes), SURPLUS = 0 at every world; the Rosati calibration 2/3/3/4/4/4/4 at
m=5,7,9,15,16,20,24; the m=6 control 688; the operator's arity totals
4/8/24/64/208 by TWO algorithms each; 660 ok lines / 0 FAIL / exit 0; runA ≡
runB byte-identical (md5 2d9d605f4c0140dd0cdb24f4ceb124fd pre-repair).

**Derivation checks**: tectonic 0.15.0 recompile of the Round-36 tex — zero
errors (two cosmetic overfull-hbox warnings), PDF 131.29 KiB. The Lean face
GSTLawStackRound36.lean carries the ledger-108 per-part labels correctly (PART A
[Genuine proof-shape]: the three finite receipts; PARTS B–E [Shape record]:
14 `trivial`-discharged fields, honestly labeled in the header); no sorry, no
native_decide, no new axioms.

## The batched repairs (ONE round, all findings)

- **F1 → repaired**: a degree-6 membership check added on a bounded, honestly
  labeled sample (2 worlds: m=15/m=16 primitive; the first nonzero triple
  product among three sampled triples; the first 8 unbalanced 6-words) — the
  triple products' components vanish on the unbalanced 6-words (they lie in
  Hdg_6); the rank equality covers every world; the label states the sample.
- **F2 → repaired**: degree-8 span receipts added at EVERY octic world (17
  checks): a four-fold cup product of divisor classes with nonzero top
  component exists — the multi-quadruple pass (repetitions allowed, cap 20; the
  cup-powers d⁴ included) or a deterministic random-class pass (40 trials,
  xorshift64*, v⁴ for a Q-combination v of the divisor basis — v is itself a
  divisor class, so v⁴ is a four-fold product). The header corrected to state
  the exact coverage. **Repair trajectory note**: the first repair draft
  sampled DISTINCT basis quadruples only — it fired at the primitive worlds and
  missed the seven 16-dim-divisor imprimitive worlds, because the firing
  products there are cup-POWERS (the polarization-type receipts Θ⁴, which
  repeated-index sampling reaches and distinct-only sampling cannot). The
  mathematics was never in doubt (any polarization Θ has Θ⁴ ≠ 0; by the
  polarization identity a nonzero symmetric form fires on the diagonal); the
  sampler's coverage had to match the claim's product space. Recorded in ledger
  entry 111.
- **F3 → repaired**: the `break` removed — the non-diagonal pair hostile now
  enumerates EVERY off-diagonal balanced pair (the label's "every" is now the
  predicate).
- **F4 → repaired**: `cross_field_check()` replaced by a real control: at the
  product world m=5 × m=7 (the type Φ₁∪Φ₂ on disjoint letter sets), all 24
  cross pairs {a∈G₁, b∈G₂} have MIXED (G₁×G₂)-orbits (0 pure-balanced) — the
  control can fail and computes the "Hom⁰ = 0 transports nothing" receipt for
  real.
- **F5 → repaired**: the brute-force cap extended to m ≤ 6 (2^{2m} ≤ 4096) —
  208 and 688 now verified by BOTH algorithms (the m=6 control gained its
  second-algorithm check).
- **F6 → repaired**: the subspan default is now fail-closed (equality fails).
- **F7 → repaired**: the descent-relation messages state that the relation is
  type-independent and that Phi names the world.

## The closing re-check

`field_letter_generation_round36_checks.py` post-repair: **681 checks, 0
failures, exit 0**, deterministic double-run byte-identical (runA.txt ≡ runB.txt,
md5 `5c5cf3bc8180451205e4e317e9b841d2`, xorshift64* seed `0xABCDEF9876543210`,
runtime ≈ 24 s, exact arithmetic, zero floats; pre-repair: 660 checks, md5
`2d9d605f4c0140dd0cdb24f4ceb124fd`). The certificate's own vacuity and
self-comparison scans pass (checks 679/680); every hostile control fires on the
deterministic run; the new checks all carry ledger-109-honest labels.

## Verdict

**PASS** (after the one batched repair round — loop CLOSED per §36). The
computational core survived every attack: the descent machinery, the
orbit-count/RREF dual-algorithm dimensions, the span arithmetic, the hostile
battery, the arity-total calibrations, and the determinism/receipt fidelity.
The findings were label-fidelity and coverage-fidelity gaps (F1/F2 the
material ones), all repaired by STRENGTHENING the checks to their labels —
never by weakening the labels. No blocker stands. The mathematics of the round
— S14, S15, S16, S17 — is independently reproduced by the orchestrator's
different-algorithm recompute at every load-bearing number.

**The boundary (unchanged by the audit)**: Q1 remains proven and certified; Q2
is NOT claimed; the closing string is NOT emitted; the falsifiable line after
Round 36 is (a′) the non-Galois CM shapes, (b) the non-split Weil fourfold
world, R3, R4.
