# A(4) STATUS — structural verdict from the verified k ≤ 20 census

**Erdős #271, the open core.** A(4) = the greedy 3-AP-free sequence seeded {0,4}
(OEIS A005487: 0, 4, 5, 7, 11, 12, 16, 23, 26, 31, 33, 37, 38, 44, …). Seed 4 is
the smallest seed NOT in the Odlyzko–Stanley family {3^k, 2·3^k} — hence the
frontier case for the dichotomy conjecture (Type-1: a_m ≍ m^{log₂3} ≈ m^1.585,
like every known closed form; Type-2: a_m ≍ m²/log m, no example known).

Census: complete on [0, 3^20) (3,486,784,401), c_20 = 347,370 members.
Engine `a4-census/stanley_census.c` (bitset greedy, cross-checked); dumps
`a4-census/data/a4_members_3k{13,15,17,18,19,20}.txt`; independent verifier
`a4-census/verify_dump.c`; analysis `a4-census/analyze_a4.py` →
`a4-census/analysis_full_output.txt` + `a4-census/analysis/*.txt` +
`a4-census/analysis_light_output.txt` (this session's completion of the
missing gap/overlap/fit sections).

---

## 0. BOTTOM LINE

1. **Growth: Type-2 family.** Cumulative exponent α_k = ln c_k/(k ln 3) =
   0.5806 at k=20, drifting DOWN from the k=4 peak 0.6700; Type-1 (0.6309) is
   quantitatively rejected, Type-2 (1/2 + polylog) fits with R² ≥ 0.998.
   Projected c_25 ≈ 6.0–6.8×10⁶ (Type-2) vs 1.11×10⁷ (Type-1): **census to
   k=25 (same 3^5-phase as k=20) decides.**
2. **Digit law: A(4) has no digit language.** Interior ternary digits of
   members are uniform and independent (P(2)=1/3 per position, adjacent
   conditional 0.3346); all structure lives in the top 2–3 digits, which
   follow a **period-5-in-scale cycle** (leading-digit-2 fraction cycles
   0.73 → 0.64 → 0.20 → 0.007 → 0.34 over k = 16..20).
3. **No self-similarity.** ≥ 100,428 distinct subtree types at residual
   depth 8 (A(2): exactly 2). No block recursion (B1 ≠ B0, B2 ≠ ∅, overlaps
   ≤ 25 elements), no linear recurrence of c_k of order ≤ 4, no
   Odlyzko–Stanley skeleton (4·3^j ∈ A(4) only for j ≤ 1; 2·3^j, 3^j never;
   |A(4)∩A(2)| = 51 of 8192). A(4) is empirically a *random-like* (generic)
   Stanley sequence — the opposite of the rigid Cantor-type A(1), A(2).
4. **Member growth: quadratic-with-log.** a_m·ln m/m² oscillates in
   [0.30, 0.48] with no trend over m = 10³…3.4×10⁵ (Type-2 signature);
   a_m/m^1.585 rises ×7.4 (0.80 → 5.89) — Type-1 excluded. Doubling
   exponents 1.51–2.31 (mean 1.81), bracketing 2, never pinning 1.585.

---

## 1. WHAT IS CERTIFIED (and what is not)

- **CERTAIN** (complete census on fixed ranges): all c_k (k ≤ 20), block
  splits b0/b1/b2, LSB-digit frequencies, mod-3 counts, gaps, overlaps.
- **Engine cross-checks**: naive pair-scan recompute bit-for-bit to 3^10
  (default NAIVE_LIMIT; the 3^20 run used NOMEMBER=1, which disables the
  in-process cross-checks — see stanley_census.c header).
- **Independent verification** (verify_dump.c: checks the dump IS the greedy
  sequence — seeds, strict ascent, AP-freeness over all member pairs,
  maximality = every non-member blocked, mark-count recomputation):
  **PASS logged for k=13 (self-test), k=17, k=18, k=19, k=20** — all t=4,
  aps=0, unblocked=0, members = c_k exactly (task 1-d, fresh runs
  2026-11-03; `verify_log.txt` + `verify_log_k{17,18,19,20}.txt` +
  `run_1d_status.txt`): k=17 marks=1,168,684,137; k=18 members=108103
  marks=3,956,010,418; k=19 members=177194 marks=13,762,802,366; k=20
  members=347370 marks=42,288,440,159 (wall 28/95/330 s, nice -n 10).
  **§8.1 verification gap CLOSED — every dump k ≤ 20 is certified as the
  exact greedy sequence S(0,4) ∩ [0,3^k).**
- **EMPIRICAL to the depth-20 horizon** (presence certain, absence refutable
  only by members ≥ 3^20): prefix-tree/leading-digit language, subtree-type
  counts. Note the "collapse" of the prefix tree at depth ≥ 13 is partly a
  horizon artifact (nodes at depth d require members with ≥ d digits); the
  subtree-type counts at residual depth r are *lower bounds* on the true
  infinite-trie type counts.
- Analyzer note: `analyze_a4.py`'s empty-blocks section stalled (Python loop
  over range(3^19)), which is why sections after (e) never appeared in
  `analysis_full_output.txt`; gaps/overlap/fits were completed by
  `analyze_gaps_light.py` → `analysis_light_output.txt`, and empty-blocks/
  phase profiles by this session → `analysis/empty_blocks_a4.txt`,
  `analysis/phase_profile_a4.txt`.

---

## 2. GROWTH TYPE (the central question)

### 2.1 Exact counts and exponents  [analysis/counts_a4.txt, growth_a4.txt]

c_k = 1, 1, 4, 9, 19, 37, 79, 147, 266, 476, 919, 1790, 3210, 5425, 9093,
19206, 38367, 65794, 108103, 177194, 347370 (k = 0..20). Task-stated census
k ≤ 7 MATCH; A(2) comparison c_k = 2^k exactly (Lean-proven, Kill #3).

Cumulative exponent α_k: 0.6309 (k=2) → peak 0.6700 (k=4) → 0.6211 (k=10) →
0.5985 (k=15) → **0.5806 (k=20)**. Not monotone: period-5 oscillation
(§2.4) rides on a decaying trend. Local exponents k=10..20: min 0.4498,
max 0.6806, mean 0.5455. r_k = c_k/c_{k−1} ∈ [1.639, 2.112] for k ≥ 12
(A(2)'s is exactly 2 forever).

### 2.2 Type-1 is quantitatively rejected  [growth_a4.txt; analysis_light_output.txt §E]

Type-1 requires c_k/2^k → const > 0. Observed: **monotone-ish collapse
1.039 (k=8) → 0.331 (k=20)**, ×3.1 over 12 scales, no flattening (k=13:
0.662, k=16: 0.585, k=19: 0.338, k=20: 0.331). Fitting the Type-1 form
c_k = C′·2^k with C′ = 0.3313 (through k=20) mispredicts α_k by up to
**+0.091** (k=10: pred 0.5304 vs obs 0.6211; k=15: +0.035) with a
systematic wrong shape. Also `2c_{k−1} − c_k` grows: +39012 at k=19 — the
sequence is increasingly unable to double per scale.

### 2.3 The Type-2 family fits  [analysis_light_output.txt §E]

Type-2 (dichotomy form a_m ≍ m²/log m) ⟺ **c_k ≍ C·3^{k/2}·k^{1/2}**.
- c_k/(3^{k/2}·√k) stays in the bounded band **[1.11, 1.46]** over k=8..20
  (the period-5 wave), vs the collapsing Type-1 normalizer.
- Fixed-β=1/2 LSQ on ln c_k − ½ln k = ln C + α·k ln 3:
  k∈[8,20]: **α = 0.5099**, C = 1.075, R² = 0.99896; k∈[10,20]: α = 0.5070,
  C = 1.134, R² = 0.99838; k∈[13,20]: α = 0.5105. Stable around α ≈ 0.51.
- Free LSQ (analyzer, k∈[8,20]): (α, β) = (0.4792, 0.9506), R² = 0.99914 —
  the α/β tradeoff is unresolved at depth 20, but **every good fit has
  α ≤ 0.51 ≪ 0.6309 with a positive log power β ∈ [½, 1]** — i.e. Type-2
  family; the Type-1 point (α = log₃2, β = 0) lies far off the fit family.
- Single-constant check: C = 1.3154 (fitted at k=20 only) reproduces ALL
  α_k, k = 10..20, within **±0.011** (residuals −0.0087, −0.0021, −0.0026,
  −0.0069, −0.0110, −0.0003, +0.0060, +0.0035, −0.0008, −0.0047, 0.0000).
  The same exercise for Type-1 misses by up to 0.091 (8× larger).
- Marginal (5-scale-block) exponents: 0.5864 (k=5–9), 0.5370 (k=10–14),
  **0.5406 (k=15–19)** — the last two periods agree at ≈ 0.54, i.e. α ≈ ½
  plus the slowly-decaying log correction, exactly the Type-2 shape.
  Member-density at scale: density of d-digit members falls ×1.738/scale
  over d=16..20 (√3 = 1.732 for α = ½ exactly).

**Fit answer:** yes — c_k = C·3^{αk}·k^β describes it with α ≈ 0.507–0.511
(β = ½) or α ≈ 0.479 (β ≈ 0.95); the k ≤ 20 data cannot separate β ∈ [½, 1]
but excludes β = 0 & α = log₃ 2.

### 2.4 Period-5 modulation (new structural finding)  [analysis_light_output.txt §D; analysis/phase_profile_a4.txt]

r_k by k mod 5: mod 0 → 1.93–2.11; mod 1 → 2.00–2.14; mod 2 → 1.71–1.86;
mod 3 → 1.64–1.81; mod 4 → 1.64–1.79. Clean phase classes for k = 5..20.
The carrier is the **leading-digit-2 population**: fraction of k-digit
members with top digit 2 = 0.610, 0.525, 0.246, 0.088, 0.440, 0.726, 0.638,
0.203, **0.0066**, 0.336 (k = 11..20) — collapse at k ≡ 4 (mod 5), peak at
k ≡ 1 (mod 5); equivalently b2/c_{k−1} = 0.004–0.06 at k ≡ 4 vs 0.58–0.72
at k ≡ 1. Same-phase cumulative exponents: α_10 = 0.6211, α_15 = 0.5985,
α_20 = 0.5806 (declines −0.0226, −0.0179; Type-2 predicts −0.0138 next).
Mechanism unidentified — prime theory target. (Phase profile itself still
drifting: k=11–15 vs k=16–20 profiles differ; not yet a stable cycle law.)

### 2.5 Projections

| model | c_21 | c_22 | c_25 | c_30 | α_25 |
|---|---|---|---|---|---|
| Type-2 fit (α=½, β=½, C=1.3154) | 6.17e5 | 1.09e6 | 6.05e6 | 1.03e8 | 0.5686 |
| marginal frozen (α = 0.5406) | — | — | 6.77e6 | 1.32e8 | 0.5726 |
| Type-1 (c_k/2^k = 0.3313) | 6.94e5 | 1.39e6 | 1.11e7 | 3.56e8 | ≥ 0.5806, rising |

At k=25 (≡ 0 mod 5, same phase as k=20, so oscillation noise cancels):
Type-2 vs Type-1 differ by 63–84% in c_25 and ≈ 0.008–0.012 in α_25 vs
same-phase fit scatter ±0.005 → **decisive**.

---

## 3. DIGIT-2 LAW  [analysis/digit2_stats_a4.txt, digit2_stats_a2.txt; analysis_light_output.txt §C]

A(2) (Lean-proven): P(digit = 2) = ½ at position 0, **0 at every higher
position** — rigid Cantor. A(4): **P(2) = 1/3 at every interior position**,
to 3 decimals, at every scale d = 13..20 (e.g. d=20, n = 170176: positions
0..16 all in [0.328, 0.337]; mean #2s = 6.681 vs 20/3 = 6.667).

Sharpened this session (d=20 members):
- pooled interior P(0)/P(1)/P(2) = **0.33188 / 0.33340 / 0.33472**;
- adjacent independence: P(pos_i = 2 | pos_{i+1} = 2) = **0.33455** (iid → ⅓);
- #2s per member: mean 6.6814 (binomial 6.6667), var 5.0295 vs binomial
  4.4444 — ~13% overdispersion (slight long-range correlation; not iid);
- %members with no 2 ≈ (2/3)^d (0.0–0.1% for d ≥ 13) — vanishing.
- Boundary layer: only the top 3 digits deviate (d=20: pos 17 =
  0.270/0.404/0.326, pos 18 = 0.438/0.234/0.329, top pos = 0/0.664/0.336),
  and those deviations are the period-5 cycle of §2.4 (e.g. d=19 top digit
  is 2 for only 0.7% of members — the k=19 top block is a near-desert).

**Law: membership in A(4) is invisible in interior ternary digits — the
greedy AP filter is digit-global, not digit-local. All digit structure is
compressed into the top O(1) digits, which cycle with period 5 in scale.**
This kills any A(2)-style digit-automaton characterization: the interior
marginals are maximal-entropy.

---

## 4. BLOCK & PREFIX-TREE STRUCTURE  [analysis/block_split_a4.txt, block_split_a2.txt, prefix_tree_*.txt, subtree_types_a4.txt, empty_blocks_a4.txt]

- **No block recursion.** A(2): c_k = c_{k−1} + c_{k−1} + 0 with B1 = B0
  *exactly* at every k ≥ 2 (the 2-block Cantor recursion). A(4): b1, b2
  volatile and phase-cycled (k=19: 68634 + **457**; k=20: 112938 + 57238);
  |B1∩B0| ≤ 25 elements at all k ≤ 20 (vs |B0| = 177194 at k=20) — shifted
  blocks are *not* copies; overlap is coincidence-level.
- **Leading-digit language**: complete ternary tree to depth 8 (nodes =
  2·3^{d−1}, d ≤ 8 — every string not starting with 0 is a prefix of some
  member); **first hole at depth 9: prefix 202221000₃ = 15255** — the
  aligned block [2702377485, 2702554632) (length 3^11) inside the k=20 top
  block is empty. Restrictions multiply with depth; 85.4% of depth-13 and
  ≥ 94% of depth-14+ nodes have exactly one child; the deep tree is a bundle
  of near-unique chains (members at large scales share long leading prefixes).
- **No finite self-similarity**: distinct subtree types by residual depth:
  9, 83, 483, 2146, 7608, 23320, 58165, **100428** (r=8), then horizon
  artifacts. A(2): exactly **2** types at every depth. Since distinct
  truncated subtrees ⇒ distinct infinite subtrees, A(4)'s trie has ≥ 10⁵
  types — no substitution/automaton/finite-type structure exists (to depth
  20).
- **Empty aligned blocks** (empty_blocks_a4.txt): A(2)'s occupied blocks are
  exactly Cantor indices (no digit 2) at every scale; A(4)'s first empty
  blocks are 2000₃, 11011₃, 11012₃, 11101₃ … (size 3^6) — mixed digits, no
  digit-law; occupied fraction 6.3% (3^6-blocks) → 92.6% (3^16-blocks).
- **No exact linear recurrence** for c_k of order 1–4 (exact rational solve:
  inconsistent).

---

## 5. MEMBER GROWTH LAW  [analysis/member_growth_a4.txt, doubling_exp_a4.txt]

- a_m/m^1.585 (Type-1 normalizer): **rises ×7.4**, 0.8025 (m=100) → 5.8856
  (m=340000) — monotone-ish increase, exactly what m²/log m predicts
  (m^0.415/ln m) and Type-1 forbids.
- a_m·ln m/m² (Type-2 normalizer): **no trend**, oscillating 0.30–0.48 over
  m = 10³…3.4×10⁵ (≈ 0.36–0.38 recent; 0.55 at m = 10²) — consistent with the
  c_k fit (C = 1.3154 ⇒ c(x) ≈ 1.256·√(x ln x) ⇒ a_m ≈ 0.63·m²/ln a_m, i.e.
  a_m·ln m/m² → ≈ 0.37, as observed).
- a_m/m² (pure quadratic): falls 0.119 → 0.030 — pure m² overshoots; the
  log factor is present.
- Doubling exponents ln(a_{2m}/a_m)/ln 2 = 1.6183, 2.2153, 1.5104, 1.5635,
  1.6700, **2.3054** (m = 500…173685): oscillate around ~1.8 with amplitude
  ±0.4 (the period-5 blockiness), mean 1.814 → effective α ≈ 0.55; Type-1's
  1.585 is at the extreme bottom of the observed range and the largest
  samples (1.67, 2.31) sit above 2's approach from below.
- Gap scaling γ = d ln gap/d ln index (analysis_light_output.txt §A):
  0.61–1.41 depending on window (phase-contaminated; full-period windows
  ≈ 0.65–0.70, between Type-1's 0.585 and Type-2's ~0.92) — not a clean
  discriminator at this depth; member normalizers above are cleaner.
- Gaps themselves: min 1 (×196), max **174,790,355** (≈ 5% of 3^20, inside
  the leading-2 desert), 31,399 distinct values; the 12 largest gaps all
  live in top blocks [2·3^{k−1}, 3^k); max gap within [0,3^k): 29324 (k=13)
  → 91,543,408 (k=19) → 174,790,355 (k=20).

**Verdict: a_m ≍ m²/log m (Type-2), not m^1.585 (Type-1).** This confirms,
with 20 scales of certified data, Lindhurst's suggestion that A(4) is of
the second type — and makes A(4) the leading candidate for the first
Type-2 Stanley sequence (the dichotomy's existence question).

---

## 6. ANCILLARY STRUCTURE

- **mod 3** [mod3_by_scale_a4.txt]: residues equidistribute from k ≈ 11 on
  (k=20: 57049/56501/56626 of 170176); early scales biased (k=2: [0,2,1] —
  no member ≡ 0 mod 3 among 4,5,7,8).
- **vs A(2)**: |A(4) ∩ A(2) ∩ [0,3^13)| = **51** of 8192 — A(4) is not a
  superset/translate/coset-mate of the Cantor-type sequence.
- **Family membership** (analysis_light_output.txt §B): 4·3^j ∈ A(4) only
  j = 0, 1 (4, 12); 2·3^j ∉ A(4) ∀j; 3^j ∉ A(4) ∀j. No Odlyzko–Stanley
  skeleton survives inside A(4).

---

## 7. WHAT THE CHARACTERIZATION THEOREM WOULD LOOK LIKE

Not a digit-automaton/substitution theorem (A(2)-style) — refuted
empirically (§3, §4). The realistic target, matching all census laws:

> **Conjecture (A(4) is Type-2).** a_m = Θ(m²/log m); equivalently
> c(x) = Θ(√(x log x)); more precisely c_k·3^{−k/2}·k^{−β} is bounded and
> oscillating for some β ∈ [½, 1] (β = ½ iff the dichotomy form is sharp),
> with the oscillation asymptotically period-5 in k and carried by the
> leading-digit-2 block population (b2/c_{k−1} cycling between ≈ 0 and
> ≈ 0.7 with phase k mod 5).

Plus the two structural companions the census directly supports:
> **Digit-mixing.** For every fixed word w ∈ {0,1,2}^L and interior
> position window, the fraction of k-digit A(4)-members matching w there →
> 3^{−L} as k → ∞ (observed: marginals ±0.002, adjacent conditionals
> ±0.0015 at k=20; slight overdispersion var/σ² ≈ 1.13).
> **Desert law.** Empty corridors of length Θ(3^{k−O(1)}) exist inside the
> leading-2 annuli at collapse phases (k ≡ 4 mod 5), with max gap a fixed
> fraction (~2–8%) of 3^k.

Mechanism (heuristic, to be proven): A(4) behaves like the *random greedy
3-AP-free process*: the greedy filter has no digit-local signature (§3), so
member density in the annulus [3^k, 3^{k+1}) is governed by the AP-feedback
equation ρ ≈ exp(−Θ(ρ²·3^k)) whose solution scales like √(k·3^{−k}) — the
√(x log x) law. The period-5 resonance is presumably anchored in the seed
pair (0,4) and the 3^5 = 243 window; identifying it is the key lemma a
proof attempt needs (the census gives exact b0/b1/b2 calibration to k=20).

A proof would be the **first Type-2 example**, resolving the existence half
of the Odlyzko–Stanley dichotomy conjecture and reducing #271's "how fast
do they grow" for the frontier seed to explicit Θ-bounds.

---

## 8. EVIDENCE GAPS & DECISION DEPTH

1. ~~**Verification gap**~~ **CLOSED (task 1-d, 2026-11-03)**: independent
   verify_dump PASS now logged for k=13 (self-test, members=5425), k=17, and
   FRESH for k=18/19/20 — `verify_log_k{18,19,20}.txt`: members =
   108103/177194/347370 = c_k exactly, aps=0, unblocked=0, marks recomputed
   (3.96×10⁹ / 1.38×10¹⁰ / 4.23×10¹⁰). All census dumps k ≤ 20 are
   certified exact greedy S(0,4) ∩ [0,3^k).
2. **(α, β) separation**: at k ≤ 20 the fits cannot separate β ∈ [½, 1];
   every fit excludes Type-1, but the sharp dichotomy constant (β = ½ vs
   a_m ≍ m²/log^{1±ε}m) needs deeper data or theory.
3. **Decision depth for Type-1 vs Type-2** (from §2.5): the same-phase
   (k mod 5) α-trend decides. Type-2: α_21 ≈ 0.578, α_22 ≈ 0.575,
   α_24 ≈ 0.571, α_25 ≈ 0.569–0.573; Type-1: α_k ≥ 0.5806 and rising.
   - **k=21** (N = 3^21 ≈ 1.05×10¹⁰; 1.3 GB NOMEMBER bitset; ~10¹¹ marks,
     minutes): first strong point — α_21 gap ≈ 0.020 vs same-phase scatter
     ±0.005.
   - **k=22** (3.9 GB bitset; ~3×10¹¹ marks, ~1 h): c_22 = 1.09×10⁶ (Type-2)
     vs 1.39×10⁶ (Type-1) — 27% apart.
   - **k=24–25 = DECISIVE** (same phase as k=19/k=20): c_25 = 6.0–6.8×10⁶
     (Type-2) vs 1.11×10⁷ (Type-1), 63–84% apart; α_25 gap 0.008–0.012 ≈
     2× the same-phase residual scatter. Cost: k=24 needs a 35 GB bitset
     (64-GB box); k=25 needs 106 GB → out-of-core bitset or a windowed
     mark-pass over the ~6–7×10⁶ members (~2×10¹³ pair-marks, hours).
4. **Phase law**: the period-5 profile (b1/c, b2/c) is still drifting
   between k=11–15 and k=16–20; depth 25 would show whether it stabilizes
   into a limit cycle (needed for any theorem statement of §7).

---

## 9. NEXT ACTIONS (ordered)

1. ~~Run `verify_dump` on the k=18, k=19, k=20 dumps~~ **DONE (task 1-d,
   2026-11-03)**: all three PASS (members=c_k, aps=0, unblocked=0; receipts
   in `verify_log_k{18,19,20}.txt`, timings in `run_1d_status.txt`) — gap
   §8.1 closed.
2. Census k=21 and k=22 (NOMEMBER mode; trivial on this box class) + rerun
   the analyzer → first out-of-sample test of the Type-2 projections
   (c_21 = 6.17×10⁵, c_22 = 1.09×10⁶ predicted).
3. Fix `analyze_a4.py`'s empty-blocks loop (iterate over the occupancy
   counter, not range(3^{K−j})) so the full report regenerates cleanly.
4. Engineer the streaming/out-of-core verifier (windowed mark pass) and
   census k=24/25 — the decisive same-phase depths.
5. Theory strike: formalize the density-feedback heuristic on ternary
   annuli (b0/b1/b2 recursion bounds), targeting first the weaker
   statement "c_k = 3^{k/2+o(k)}" (excludes Type-1) and the digit-mixing
   law; the period-5 leading-digit cycle is the phenomenon any inductive
   proof must reproduce.
