# WORKLOG — W85-107C: the #107 LOWER-bound kernel port (DM107_Proof_C.lean)

TASK ID: W85-107C (K2, the writer phase; cone/plan = W85-107C-A, AUDIT_W85_107C.md)
LANE: problem107 | Agent: WRITER W85-107C. English only. CI is the only Lean verdict.
STATUS: **KERNEL WRITTEN — awaiting CI** (not wired into kills.yml per the mission
rules; the wiring is the next lane's one-step job, spec in §7).

## 1. THE DELIVERABLE

`problem107-happy-ending/DM107_Proof_C.lean` — **2764 lines, 194 declarations,
zero sorry / admit / native_decide**, standalone `lake env lean` kernel over the
vendored OFFICIAL definitions (FC.Geometry.TwoD + the verbatim `cardSet`/`f` block
from DM107_Official.lean), namespace `Erdos107C`, toolchain v4.33.0-rc2.

THE THREE TARGETS (verbatim signatures as specified by the mission; vendor twins
Blueprint107.lean L773 / L784 / L796 via Solution.lean L69 / L74):

    theorem f_eq_conjectured_of_le_four : ∀ n, 3 ≤ n → n ≤ 4 → f n = 2 ^ (n - 2) + 1
    theorem ersz_lower_le_five         : ∀ n, 3 ≤ n → n ≤ 5 → 2 ^ (n - 2) + 1 ≤ f n
    theorem ersz_bounds_of_le_five :
        ∀ n, 3 ≤ n → n ≤ 5 → 2 ^ (n - 2) + 1 ≤ f n ∧
          f n ≤ Nat.choose (2 * n - 4) (n - 2) + 1

Footer: `#eval "DM107C_LOWER_GREEN"` + `#print axioms` on the 3 targets and the
7 supporting headliners (f_three_eq, f_four_eq_five_unconditional,
five_mem_cardSet_four, not_hasConvexFiveGon_esEightFinset, nine_le_f_five,
f_le_erdosSzekeresUpper, nonempty_cardSet).

## 2. AS-BUILT STRUCTURE (per AUDIT_W85_107C.md §4, executed)

| Part | Lines | Declarations | Content |
|---|---|---|---|
| header | 1–112 | — | mission docstring (provenance, deviations, risks, honest scope), imports (Mathlib, FC.Geometry.TwoD, Arsenal.ErdosTernary2.Basic, Arsenal.CardinalWorlds), B's set_option block with **maxHeartbeats 16000000 + maxRecDepth 262144** |
| §0–§14 (CLONE) | 113–1595 | 115 | DM107_Proof_B.lean L89–1571 verbatim, namespace Erdos107 → Erdos107C: official defs §0, mkPt/cross §1, nonTrilinear_iff §2, slopeLt/slopeGt §3, lineSide §4, half-plane sep §5, ES 1935 cup–cap core + erdosSzekeresUpper §6, IsCupSet/IsCapSet §7, x-sorting §8, shear §9 (the one `Set.image_diff` deprecated-alias site, silenced by the header), small base cases §10, ES theorem + membership §11, the sInf upper bridge `f_le_erdosSzekeresUpper` §12, binomial laws + arsenal bridge §13, `nonempty_cardSet_all`/`nonempty_cardSet` §14 |
| §15 (FRESH) | 1596– | 10 | lineSide sign dichotomy, lineSide_sep_of_neg_pos, convexIndep_four_of_strict_sep, opposite-diagonals, same-open-side (×2), 3-sign pigeonhole, 5-pt line pigeonhole, same-open-side edge, triangle-two-interior (Erdos107Unified435 L1773–1962 + L1097–1148) |
| §16 (FRESH) | — | 10 | InPosTriangle calculus: def, triangle-sum, both Cramer syzygies, cycle, pos_outer, trans, barycentric identity, convex-hull membership, non-convexity criterion (Blueprint L85–244) |
| §17 (FRESH) | — | 22 | nonTrilinear_mono, hasConvexNGon_mono_pts, cardSet_upward_closed, not_collinear_of_cross_ne_zero, the Klein 4-point witness block (ptO/ptA/ptB/ptC, 6 ≠-lemmas, card, barycentric, hull membership, ¬ConvexIndep, NonTrilinear), 4 ∉ cardSet 4, **deviation #2** five_le_of_mem_cardSet_four, five_le_f_four |
| §18 (FRESH) | — | 12 | Esther Klein's 5-point theorem: two-pos-one-neg, the dichotomy, two-inPosTriangle, fifth-point case split, pos-outer-and-two-points, five-distinct, exists_five_distinct_of_card_eq_five, 5 ∈ cardSet 4, f_four_eq_five_of_mem_cardSet, f_four_eq_five, f_four_eq_five_unconditional (Blueprint L246–461 + Unified435 L1610–1615) |
| §19 (FRESH) | — | 1 | **deviation #1**: f_three_eq ported VERBATIM from the CI-GREEN official anchor DM107_Official.lean L106–134 |
| §20 (FRESH) | — | 24 | the 8-point ES-1960 witness: 2 extraction lemmas, 5 witness defs, lineSide_esEightPt, injectivity/card, the **five decide blocks** (64 / 512 / 4096 / 4096 / 2), fin8_cap_cup_split, the master no-pentagon certificate, 8 ∉ cardSet 5, 9 ≤ N, 9 ≤ f 5 (Blueprint L519–757 minus the 4 excluded presentational cap/cup lemmas) |
| §21 (FRESH) | — | 4 | the three targets + the honest scope marker `ersz_lower_scope_pos` |
| footer | 2650–2764 | — | `end Erdos107C`, #eval, 10 × #print axioms |

## 3. FIDELITY RECEIPTS (mechanical verification, all in this session)

- **B-clone**: extracted mechanically with python (B:89–1571), the ONLY change the
  namespace line (verified: exactly 1 swap). 20/20 spot-check declarations
  (cardSet, f, mkPt, lineSide, convexIndep_of_pointwise_strict_sep,
  erdos_szekeres_cup_cap_theorem_on, hasConvexNGon_of_nonTrilinear_and_card_ge,
  f_le_erdosSzekeresUpper, nonempty_cardSet_all, dm107b_arsenal_bridge,
  self_mem_cardSet_of_le_three, convexIndep_triple_of_not_collinear, shearPt,
  goodShearSlope, IsCupSet, cup_end_meets_cap_start_on, xSortedSeq,
  erdosSzekeresUpper, erdosSzekeresConjectured, ersz_upper) **byte-identical
  (whitespace-normalized, comment-stripped) to DM107_Proof_B.lean** — i.e. to a
  CI-GREEN v4.33-verified unit.
- **f_three_eq**: **byte-identical to the CI-GREEN official anchor**
  (DM107_Official.lean L106–134).
- **The 50 substantive fresh ports**: **46/46 of the non-adapted ones
  byte-identical** to the vendor sources; the remaining 4 differ in EXACTLY the
  documented micro-adaptations (§4 below). Verified by automated normalized diff.
- Zero duplicate declaration names (194 checked). Parens/brackets/braces/block
  comments balanced. Namespace balanced (open :117, end :2750; the anonymous
  `noncomputable section` stays open to EOF — B's own GREEN shape).
- The fresh cone-name cross-reference: 84 cone-prefixed identifiers used in §15+,
  all declared in-file (the 3 "missing" flags are doc-comment words + the Mathlib
  `le_csInf`); NO parabola/le_of_mem_cardSet/kleinFive/kks/cupCapBound leaks
  (grep-verified: 'parabola' and 'le_of_mem_cardSet' occur only in doc comments).

## 4. DEVIATIONS + MICRO-ADAPTATIONS (all recorded, all statement-preserving)

The two designed cone deviations (AUDIT_W85_107C.md):
1. `f_three_eq` ← the official GREEN anchor (collinear x-axis witness, vacuous
   `NonTrilinear` via `Set.triplewise_of_encard_lt`), not the vendor parabola
   route — deletes the whole parabola sub-cone.
2. `five_le_of_mem_cardSet_four` via `cardSet_upward_closed` (the mirror of
   Blueprint L740 `nine_le_of_mem_cardSet_five`), not `le_of_mem_cardSet`.

Mission-mandated statement adaptations (proof bodies unchanged):
3. The three targets use the explicit `∀ n, 3 ≤ n → …` binder form (the
   Solution.lean entry shape) with `intro n hn3 hn4/hn5`; the second target is
   named `ersz_lower_le_five` (vendor: `conjectured_lower_bound_of_le_five`).

v4.33-compatibility micro-adaptations (the audit's risk list, pre-hardened):
4. `esEightFinset_nonTrilinear`: vendor `rw [esEightFinset, Finset.coe_image] at
   ha hb hc` → `simp only [esEightFinset, Finset.coe_image, Set.mem_image] at ha
   hb hc` (definition-unfolding inside `rw` unattested at v4.33; simp-only
   def-unfolding is core-stable behavior).
5. `cardSet_upward_closed`: vendor `Finset.exists_subset_card_eq
   (hle.trans_eq hcard.symm)` → `(by omega : N₁ ≤ pts.card)` (`Nat.le_trans_eq`
   unattested at v4.33; omega is free).
6. `inPosTriangle_mem_convexHull` + `ptC_mem_convexHull_triangle`: vendor
   `convex_convexHull ℝ _` / `subset_convexHull ℝ _ h` → the named-argument form
   `(𝕜 := ℝ)` — signature-agnostic (works whether 𝕜 is explicit or implicit at
   v4.33; the modern tree shows it explicit, matching the vendor's v4.35 usage).

## 5. RISK LIST (unattested-at-v4.33 API + fallbacks) — for the CI repair loop

No Lean toolchain exists in this workspace (verified: no lean/lake/elan binaries
anywhere; the local Mathlib trees are 2026 masters, NOT the CI's v4.33.0-rc2) —
so every v4.33-specific claim rests on (a) GREEN-kernel attestation
(DM107_Proof_B/A/Official), (b) the vendor's v4.35-rc2 compilation, (c) signature
checks against the modern tree. Ranked:

- **R1 (MEDIUM, math-bearing): the two 4096-case `decide` blocks**
  (`esEight_cap_triple_with_cup_pt`, `esEight_cup_triple_with_cap_pt`) plus the
  512-case `esEightCross_ne_zero_of_distinct` and 64-case `esEightX_ne_of_ne`.
  Kept vendor-faithful; header sets maxHeartbeats 16000000 + maxRecDepth 262144
  (the vendor compiled them at v4.35 with only 800000 heartbeats and default
  maxRecDepth, and the real surviving case count is small — the i<j<k<4 / 4≤u
  guards cut the 4096 quadruples to 16 live ones; the rest die on the implication
  short-circuit). The `Decidable (p → q)` instance needed for the ∀-implication
  shape is deduced present at v4.33 (it must be in core for the vendor's v4.35
  compile, and the core Decidable hierarchy is frozen across v4.33→v4.35).
  FALLBACKS: (a) split each into two half-lemmas (fix the first quantifier's
  half: 2048 cases each); (b) explicit `Fin 8` literal enumeration + norm_num;
  (c) raise maxRecDepth further (512K).
- **R2 (MEDIUM-LOW): `Finset.subset_image_iff`'s RHS shape.** Modern tree:
  `t ⊆ s.image f ↔ ∃ s' : Finset α, s' ⊆ s ∧ s'.image f = t` — exactly the
  vendor's ⟨I, _, rfl⟩ destructuring; ancient lemma, but not attested by the
  GREEN kernels. FALLBACK: construct `I := S.preimage esEightPt
  (esEightPt_injective.preimage …)` and close the two facts by
  `Finset.card_image_of_injective` + preimage image lemmas (≈6 lines).
- **R3 (LOW): five unattested-by-GREEN-kernels Mathlib names** —
  `Finset.exists_subset_card_eq` (Card.lean:664, `∃ t ⊆ s, #t = n` — the
  destructuring shape matches), `Finset.card_eq_succ` (:776 — `card_eq_three`
  :789 IS GREEN-attested via B:1370 and sits in the same section),
  `Finset.eq_of_subset_of_card_le` (:282), `Finset.card_pos` (:78),
  `convex_convexHull`/`subset_convexHull` (hull call sites already hardened with
  `(𝕜 := ℝ)`). All ancient and shape-verified in the modern tree. FALLBACKS are
  one-liners (omega / explicit subsets / `Finset.exists_inter`).
- **R4 (LOW): simp/norm_num micro-drift on the coordinate computations** —
  `ptC_eq_barycentric` (`ext i; fin_cases i <;> simp [ptO, ptA, ptB, ptC, mkPt]
  <;> norm_num`), the 64-case `kleinFourPts_nonTrilinear` bash, and
  `lineSide_esEightPt`'s `push_cast; ring`. All coordinates are tiny integers;
  the idioms (`mkPt_zero/one` @[simp] from the clone, `PiLp.*_apply`,
  `norm_num`, `push_cast`) are B-GREEN-attested patterns. FALLBACK: explicit
  `simp only [ptO, ptA, ptB, ptC, mkPt_zero, mkPt_one, PiLp.add_apply,
  PiLp.smul_apply, smul_eq_mul]` + `norm_num`/`ring` per goal.
- **R5 (LOW): omega-through-`let` in the master certificate** —
  `by omega : 0 < (I \ I.filter …).card` after `rcases` of the let-bound
  `fin8_cap_cup_split` disjunction (hI₁/hI₂ may arrive as let-bound fvars;
  omega zeta-reduces, unchanged between v4.33/v4.35). FALLBACK: insert defeq
  `have` normalizations (`have hI₂' : 1 ≤ (I \ I.filter …).card := hI₂`) before
  each omega.
- **R6 (LOW): `simpa using f_three_eq` / `simpa using nine_le_f_five`** numeral
  normalization (`2^(3-2)+1 = 3`, `2^(5-2)+1 = 9` via the Nat.reduceSub/Pow/Add
  simprocs — present at v4.33). FALLBACK: `rw [show (2:ℕ) ^ (3 - 2) + 1 = 3 by
  decide]; exact f_three_eq` (the rw/decide variants are already in the file for
  the n = 3 / n = 4 cases of `ersz_lower_le_five`).

## 6. HONEST SCOPE (never dress partial as complete)

- The lower bound 2^(n−2)+1 ≤ f(n) is proved for **3 ≤ n ≤ 5 ONLY** (the ES-1960
  8-point witness at n=5, the Klein 4-point witness at n=4, the official anchor
  at n=3). The stretch **n ≥ 6** (the ES-1960 doubling construction) remains
  open — neither linrock's public proof nor this cone covers it. Marker:
  `Erdos107C.ersz_lower_scope_pos` (positivity + compatibility of the open side).
- The open core `erdos_107 : ∀ n ≥ 3, f n = 2^(n−2)+1` is NOT claimed.
- The vendor's conditional `f(5) = 9` upgrades (needing 9 ∈ cardSet 5) are NOT
  ported (out of scope, grep-verified absent).

## 7. NEXT ACTIONS (not done — outside this mission's rules)

1. CI wiring: a step in the kernel-dm job family mirroring kernel-107dm-b
   (`.github/workflows/kills.yml`): `lake build FC` + the two Arsenal builds →
   `lake env lean problem107-happy-ending/DM107_Proof_C.lean` →
   `! grep -E 'error:|sorryAx|unknown identifier|unsolved goals|declaration uses
   .sorry.'` → `grep -F "DM107C_LOWER_GREEN"` → `#print axioms` greps for
   `Erdos107C.f_eq_conjectured_of_le_four`, `Erdos107C.ersz_lower_le_five`,
   `Erdos107C.ersz_bounds_of_le_five`.
2. The CI repair loop against the §5 risk list (R1's decide blocks are the
   first thing to watch in the log: kernel `maxRecDepth` / elaboration time).
3. Comparator claim update + receipt once GREEN.
