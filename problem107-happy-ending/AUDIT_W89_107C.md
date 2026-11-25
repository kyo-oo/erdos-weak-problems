# AUDIT W89-A107 — ADVERSARIAL AUDIT OF KERNEL 107DM-C (`DM107_Proof_C.lean`)

**Auditor:** W89 (proof-audit lane). **Repo:** `campaign` branch, tip `d290274` (clean).
**Target:** `problem107-happy-ending/DM107_Proof_C.lean` (2763 lines + trailing `#print` block, 194 decls).
**Claimed CI-green:** GitHub Actions job `kernel-dm-w85`, run **45497202986** (archived log
`problem406-ternary-powers/CI_LOGS_W89/kernel-dm-w85.log`, commit `8a96fa5`).
**Method:** static adversarial audit — no `lake`/`lean` run (CI is the only Lean verdict);
mechanical diffs (full-region, not sampled), word-boundary greps, and independent Python
re-verification of all witness mathematics.

---

## VERDICT

**THE GREEN IS REAL.** Kernel 107DM-C is a complete, faithful, honestly-scoped proof of its
three headline theorems over byte-identical official definitions. Zero sorry / admit /
native_decide / axiom declarations; no unsafe/`implemented_by`/`extern`/`ofReduceBool` tricks;
the two designed deviations are real, statement-preserving, and are the ONLY mathematical
divergences from the vendored cone; every `decide` is on a closed term; the axiom profile is
exactly `[propext, Classical.choice, Quot.sound]` for all 10 receipted theorems, verified in
the archived CI log of run 45497202986, and the kernel file is **unchanged** between that
run's commit (`8a96fa5`) and the audited tip (`d290274`; `git diff --stat` empty).
4 defects/notes found, **none affecting the kernel's soundness or its green status** (see §7).

---

## 1. STATEMENT FIDELITY (official #107 — Happy Ending, f(n) = smallest N forcing a convex n-gon)

Official sources read side-by-side: `deepmind-comparator/DM_107.lean`
(google-deepmind/formal-conjectures @ 2207c54d), `DM107_Official.lean` (campaign's certified
copy; compiled in CI job `kernel-fc` with the three verbatim anchors → `DM107_ANCHORS_GREEN`),
`comparator-official/challenges/107/challenge.json` (statement_verbatim matches the Lean).

| Object | Official (`DM_107.lean` L37–42) | Kernel C (L123–128) | Match |
|---|---|---|---|
| `cardSet` | `def cardSet (n : ℕ) := { N \| ∀ (pts : Finset ℝ²), pts.card = N → NonTrilinear (pts : Set ℝ²) → HasConvexNGon n pts }` | same, char-for-char | **BYTE-IDENTICAL** (diff empty) |
| `f` | `noncomputable def f (n : ℕ) : ℕ := sInf (cardSet n)` | same | **BYTE-IDENTICAL** |
| ambient defs | `FC/Geometry/TwoD.lean`: `NonTrilinear A := A.Triplewise (fun x y z ↦ ¬ Collinear ℝ {x,y,z})` (general position), `ConvexIndep S := ∀ a ∈ S, a ∉ convexHull ℝ (S \ {a})`, `HasConvexNGon n P := ∃ S : Finset ℝ², S.card = n ∧ ↑S ⊆ P ∧ ConvexIndep S` | imports `FC.Geometry.TwoD` verbatim (L102) — same instances, no redefinition | **IDENTICAL (by import)** |

Headline theorem signatures (kernel C vs the vendored entry points the upstream
formal-conjectures file cites as its `formal_proof` witness, `vendor_linrock/Solution.lean`):

| Kernel C theorem | Line | Statement | Official relationship |
|---|---|---|---|
| `f_eq_conjectured_of_le_four` | L2699 | `∀ n, 3 ≤ n → n ≤ 4 → f n = 2 ^ (n - 2) + 1` | **byte-identical to Solution.lean L69** (the exact-values theorem: f 3 = 3, f 4 = 5); the open core `erdos_107 : ∀ n ≥ 3, …` is honestly NOT claimed (header L84–88) |
| `ersz_lower_le_five` | L2711 | `∀ n, 3 ≤ n → n ≤ 5 → 2 ^ (n - 2) + 1 ≤ f n` | the LOWER side of official `ersz_bounds` (vendor twin `conjectured_lower_bound_of_le_five`, Blueprint107 L784), restricted n ≤ 5 — honestly scoped (L84–88, marker L2741) |
| `ersz_bounds_of_le_five` | L2723–25 | `∀ n, 3 ≤ n → n ≤ 5 → 2 ^ (n - 2) + 1 ≤ f n ∧ f n ≤ Nat.choose (2 * n - 4) (n - 2) + 1` | **token-identical to Solution.lean L74–75** (one line-wrap only, diff shows whitespace-only); official two-sided shape, n ≤ 5 |

The inequality orientation of the lower bound is correct: `2 ^ (n - 2) + 1 ≤ f n` **is**
f(n) ≥ 2^(n−2)+1 (a LOWER bound on f), matching ES-1960. No orientation flip.

## 2. ZERO-SORRY SCAN

Word-boundary regex `\b(sorry|admit|native_decide|axiom)\b` over `DM107_Proof_C.lean`:
**one hit, line 97 — inside the header comment** ("Zero sorry, zero native_decide…").
Looser scan adds only the ten `#print axioms …` receipt lines (L2754–2763), which *print*
dependencies, they do not declare axioms. **Zero `sorry`, zero `admit`, zero `native_decide`,
zero `axiom` declarations. CONFIRMED.** Additional safety greps: zero `unsafe`,
`implemented_by`, `@[extern]`, `ofReduceBool`, `macro_rules`/`elab` metaprogramming.
`set_option`s are benign (linters off; `maxHeartbeats 16000000` / `maxRecDepth 262144` are
elaboration-budget raises, not kernel soundness waivers). CI's negative gate
`! grep -E 'error[:(]|sorryAx|unknown identifier|unsolved goals|declaration uses .sorry.'`
passed on run 45497202986.

## 3. PORT AUDIT

### 3a. The B-clone (§0–§14, C L117–1595) — byte identity
Claim: 115-decl clone of `DM107_Proof_B.lean` L94–1572 with the single namespace swap
`Erdos107` → `Erdos107C`. **Audited by FULL diff, not spot-check:** extracted both regions
(1479 lines each), applied the namespace swap to C's copy, `diff` → **EMPTY (1479/1479 lines
identical)**. Declaration count: 115/115 (region grep). Stronger than the CI note's 20/20
spot check. Ten-representative spot table (B line ↔ C line):
`cardSet 100↔123`, `lineSide 211↔234`, `slopeLt_iff_lineSide_pos 302↔325`,
`erdos_szekeres_cup_cap_theorem_on 537↔560`, `convexIndep_of_isCupSet 759↔782`,
`xSortedSeq 1070↔1093`, `shearPt 1165↔1188`, `goodShearSlope 1288↔1311`,
`erdosSzekeresUpper_mem_cardSet 1413↔1436`, `ersz_upper 1445↔1468`.
No cross-namespace code references (`Erdos107.` appears only in header comments, L39–40) —
the kernel is genuinely standalone. **CONFIRMED.**

### 3b. The fresh ports (§15–§21, C L1596–2763) — the two deviations are the only divergences
79 declarations. Automated comparison against the vendored cone
(`vendor_linrock/Erdos107Unified435.lean`, `vendor_linrock/Blueprint107.lean`), comments
stripped, whitespace normalized:

- **67/79 code-identical** to their vendor twins (including the whole `InPosTriangle`
  barycentric calculus, the Klein 5-point theorem chain, the cap/cup split, and the master
  no-pentagon certificate body).
- **11 divergent + 1 C-only**, all fully accounted for:
  1. `f_three_eq` (C L2424–2452) — **designed deviation #1**: vendor route
     (`f_eq_self_of_le_three (by decide)`, the parabola sub-cone) replaced by the official
     CI-green anchor proof. **Byte-identical to `DM107_Official.lean` L106–134 (diff empty)**;
     its supporting lemma `convexIndep_triple_of_not_collinear` (C L1366–1384) is
     code-identical to the official L78–99 (only `private lemma` → `theorem`).
  2. `five_le_of_mem_cardSet_four` (C L2178–2181) — **designed deviation #2**: vendor's
     parabola-based `le_of_mem_cardSet` replaced by `by_contra` + `cardSet_upward_closed`
     (mirroring the vendor's own `nine_le_of_mem_cardSet_five` pattern). Statement identical.
  3. `cardSet_upward_closed` (C L2033) — recorded micro-adaptation: `hle.trans_eq hcard.symm`
     → `(by omega : N₁ ≤ pts.card)`.
  4. `inPosTriangle_mem_convexHull` (C L1940), 5. `ptC_mem_convexHull_triangle` (C L2115) —
     recorded micro-adaptation: named argument `(𝕜 := ℝ)` on `subset_convexHull` /
     `convex_convexHull` (v4.33 elaboration).
  6. `esEightFinset_nonTrilinear` (C L2556) — recorded micro-adaptation: `rw […]` → `simp
     only […, Set.mem_image]`.
  7–8. `not_hasConvexFiveGon_esEightFinset` (C L2626), `exists_strict_ordered_triple_of_three_le_card`
     (C L2481) — **cosmetic line-wraps only**, zero token changes.
  9–11. the three headline theorems — signature alignment from Blueprint107's implicit-`{n}`
     form to the **∀-form, byte-matching the vendored Solution.lean entry points L69/L74**
     (a fidelity *improvement*), plus the rename `conjectured_lower_bound_of_le_five` →
     `ersz_lower_le_five` (C-named, vendor proof body verbatim).
- **1 C-only declaration:** `ersz_lower_scope_pos` (C L2741) — the honest scope marker
  (n ≥ 6 open stretch compatibility), no vendor twin, correctly not counted as a port.

**CONFIRMED: the two designed deviations + three recorded micro-adaptations are the complete
divergence set from the vendored cone; everything else is comments, wraps, and the
entry-point signature alignment.** Header claims (L66–82) match reality exactly.

### 3c. Decide-block legality (campaign NO-OOM rules)
All 17 `decide` tokens in C, classified:

| Site | Line(s) | Form | Cases | Legal? |
|---|---|---|---|---|
| `esEightX_ne_of_ne` | 2530–2531 | `∀ i j : Fin 8, …` on closed literal `esEightX` | 64 | ✓ closed, per-∀ domain 8 |
| `esEightCross_ne_zero_of_distinct` | 2548–2550 | `∀ i j k : Fin 8, …` on closed integer crosses | 512 | ✓ closed, domain 8 each |
| `esEight_cap_triple_with_cup_pt` | 2576–2580 | `∀ i j k u : Fin 8, …` | 4096 | ✓ closed; each ∀ over Fin 8 (≪ 501); see note D3 |
| `esEight_cup_triple_with_cap_pt` | 2586–2590 | `∀ u v w i : Fin 8, …` | 4096 | ✓ as above |
| `fin8_cap_cup_split` card facts | 2615, 2616 | closed `(Finset.univ.filter …).card = 4` | 2 goals | ✓ closed terms |
| targets, after `rw` | 2715, 2716 | `2^(3-2)+1 ≤ 3`, `2^(4-2)+1 ≤ 5` | closed ℕ | ✓ |
| cloned cone (B, already green) | 1496, 1524, 1534, 1575–77, 1592–93 | closed numerals / `by decide` ≤ 3 bounds | closed | ✓ |

Every `decide` is on a **closed term** (no free variables — `esEightX/esEightY/esEightCross`
are closed literal functions; the target decides close only after the `rw`). No
`set_option exponentiation.threshold` anywhere and none needed: the largest exponent in any
decided goal is `2 ^ 2` (kernel default cap 256, far clear). No `decide` on any single
`∀ k < N` with N > 501 — every quantifier is over `Fin 8`. The 4096-case blocks are
4-fold products of 8-element quantifiers with |cross| ≤ ~4600 small-integer arithmetic,
kept vendor-faithful (same blocks upstream, Blueprint107 L635–649), and empirically
kernel-feasible: run 45497202986 completed green. See defect note D3 for the boundary remark.

## 4. MATH SPOT-CHECKS

- **f 3 = 3** (C L2424, official anchor): upper `3 ∈ cardSet 3` — from `card = 3` obtain
  distinct a,b,c; `NonTrilinear` (FC's Triplewise over the coerced set) → `¬ Collinear {a,b,c}`
  → `convexIndep_triple_of_not_collinear` → the whole 3-set is `ConvexIndep`. General
  position is used correctly (3 *non-collinear* points are the convex position; collinear
  triples would fail). Lower — if N < 3, take N distinct x-axis points: `NonTrilinear` holds
  **vacuously** via `Set.triplewise_of_encard_lt` (no three distinct points exist), and
  `HasConvexNGon 3` would need a 3-element subset of a < 3-element set — contradiction.
  Correct Lean capture of the mathematical content on both sides.
- **f 4 = 5** (Esther Klein, C §17–§18): upper `5 ∈ cardSet 4` (L2382) via the universal
  4-point dichotomy (convex quadrilateral or one point inside the positive triangle of three
  others), the 3-outer/2-interior sign pigeonhole, and the `InPosTriangle` convex-hull
  calculus; lower `4 ∉ cardSet 4` (L2164) via the witness {(0,0),(3,0),(0,3),(1,1)} —
  (1,1) = ⅓(0,0)+⅓(3,0)+⅓(0,3) is the strict barycenter (L2106–2131), so not
  `ConvexIndep`, while no three are collinear. Assembly: `f 4 ≤ 5` (sInf_le) ∧ `5 ≤ f 4`
  (upward closure kills all N ≤ 4) → **f 4 = 5 exact** (L2406–2411). Independently
  re-verified in Python (barycenter identity; the three cross products 3, −3, 3 ≠ 0).
- **ES-1960 lower bound at n = 5** (C §20): witness = 4-cap {(0,0),(1,3),(2,5),(3,6)} ⊕
  4-cup {(20,100),(21,97),(22,95),(23,94)}. **Independently re-verified by fresh Python
  (this audit): zero collinear triples among C(8,3)=56; zero convex 5-subsets among
  C(8,5)=56; 38 of 70 four-subsets convex (consistent — convex 4-gons exist, as they must
  since f 4 = 5).** Chain: `8 ∉ cardSet 5` (L2676) → upward closure → `9 ≤ N` for every
  N ∈ cardSet 5 (L2683) → `le_csInf` (needs `cardSet 5` nonempty — supplied by the cloned
  ES-1935 cone `nonempty_cardSet_all 5`) → **9 ≤ f 5** (L2690). Arithmetic: 2^(3−2)+1=3,
  2^(4−2)+1=5, 2^(5−2)+1=9, upper C(6,3)+1=21 — all exact.
- **Orientation**: `ersz_lower_le_five` states `2 ^ (n - 2) + 1 ≤ f n` — the lower bound on
  f, matching the mathematical ES-1960 claim. No flip anywhere (also checked the n=3/n=4
  legs: both close by `decide` on `3 ≤ 3` / `5 ≤ 5`).

## 5. SUPPORTING KERNELS & CI GATES (`.github/workflows/kills.yml`)

| Kernel | CI gate | What it proves | Status |
|---|---|---|---|
| `DM107_Official.lean` | `kernel-fc` (L71–101) | official defs + the three verbatim anchors (`f_zero_eq`, `convexIndep_triple…`, `f_three_eq`) → `DM107_ANCHORS_GREEN` | gated ✓ |
| `DM107_Proof_A.lean` | `kernel-dm-w82` step "Kernel 107DM-A" (L103–137) | `Erdos107.nonempty_cardSet` ∀ n ≥ 3 | gated ✓ |
| `DM107_Proof_B.lean` | `kernel-107dm-b` (L2422–2450) | `ersz_upper` + `f_le_erdosSzekeresUpper` + scope marker | gated ✓ |
| `DM107_Proof_C.lean` | `kernel-dm-w85` step "Kernel 107DM-C" (L262–274) | the three targets + axiom-profile greps + `! grep sorryAx` negative gate | gated ✓ (run 45497202986) |
| `Erdos107.lean` (witness kernel) | `kernel-107k` (L2395–2420) | arsenal-only f(3)=3, f(4)≥5, f(5)≥9 witnesses | gated ✓ |
| comparator | `kernel-107cmp` (L2510–2543) + `gate-107-official` (L2636–2655) | 11-lane direct verification, `VERDICT: YOUR SOLUTION IS OKAY` | gated ✓ |
| `DM107_Proof_D.lean` | **NONE** | (the W84-107B "insurance lane", same lower bound n ≤ 5 by pure finite witnesses) | **archived unwired** — see D1 |

Zero-sorry on the gated siblings confirmed (A/B/D/Official: only header mentions; the 5
`sorry`s in `deepmind-comparator/DM_107.lean` are the upstream open-problem placeholders,
which is exactly what the kernels discharge).

## 6. COMPARATOR

`comparator-official/challenges/107/RECEIPTS_official.txt` (2026-11-24): **16/16 PASS**
(official=2, solution=9, controls=5), WALL 44.69s, final line
**"VERDICT: YOUR SOLUTION IS OKAY"** — the official funsearch Evaluator (`_sample_to_program`
+ analyse, claim groups scoring 3/3/1/3/2), admissible_set data integrity, engine re-runs,
and five negative controls (broken program rejected, planted pentagon detected, corrupted
binomial detected, corrupted H107 threshold refuted). **CONFIRMED.**

## 7. DEFECTS & NOTES (severity, with line numbers)

- **D1 (LOW, repo hygiene — not kernel C):** `DM107_Proof_D.lean` (2121 lines) is compiled
  by **no CI job** (kernel-dm-w84 gates only DM61_Proof_D and DM142_Proof_D), and its header
  cites `WORKLOG_W84_107B.md §2`, a file that does not exist in the repo. Mitigation: the
  campaign ledger honestly records it as "archived in-repo unwired" (WORKLOG.md ~L5397), and
  its headline (`ersz_lower_floor`, same n ≤ 5 lower bound) is independently proven and
  CI-gated by kernel C itself. No impact on C's green; the D file simply carries no
  machine verdict and must not be cited as green.
- **D2 (INFO, bookkeeping):** header L22–23 and §20 head (L2458) say "five `decide` blocks
  (64 / 512 / 4096 / 4096 / 2 cases)"; there are literally six `decide` tokens in §20 — the
  "2-case" block is the two one-line closed-card facts at L2615/L2616. Count semantics
  (blocks vs tokens), no mathematical effect.
- **D3 (LOW, boundary note on the NO-OOM law):** the two 4096-case `decide` blocks (L2580,
  L2590) exceed a naive "≤ 501 cases per decide" reading in raw case count, though every
  individual quantifier is over `Fin 8` (8 ≤ 501) and the arithmetic per case is
  small-integer (|cross| ≤ ~4600). They are vendor-faithful (upstream Blueprint107
  L635–649 uses the same blocks) and empirically kernel-feasible (run 45497202986 green,
  no OOM). Recorded here so the precedent is deliberate, not accidental.
- **D4 (INFO, positive):** the three headline signatures deviate from Blueprint107's
  implicit-`{n}` form — but toward the **∀-form byte-identical to the vendored Solution.lean
  entry points L69/L74**, i.e. the signatures the upstream formal-conjectures file actually
  exposes. This is a fidelity alignment; documented in-file (L2695–2697, L2719–2721).

No defects of substance found in `DM107_Proof_C.lean` itself: no statement drift, no hidden
sorry/axiom, no unsafe cast, no orientation error, no unfaithful port, no decide blow-up,
no dishonest scope claim (the n ≥ 6 stretch and the open core `erdos_107` are explicitly
marked NOT claimed, L84–88 and L2741).

**W89 verdict: SHIP. The W85-107C green is real and the kernel stands.**
