/-
W84-107B — PROOF KERNEL D for Erdős Problem #107 (Happy Ending): the LOWER
side of the official bound for the range 3 ≤ n ≤ 5, via explicit finite
witnesses (the insurance lane: this kernel alone guarantees the #107 lower
side lands green for n ≤ 5 whatever happens on the all-n lane W84-107A):

    theorem Erdos107D.ersz_lower_floor : ∀ n, 3 ≤ n → n ≤ 5 → 2 ^ (n - 2) + 1 ≤ f n

that is, the lower side of the official `ersz_bounds` variant
(DeepMind formal-conjectures @ 2207c54d, FormalConjectures/ErdosProblems/
107.lean, `Erdos107.variants.ersz_bounds`:

    ∀ n ≥ 3, 2^(n - 2) + 1 ≤ f n ∧ f n ≤ Nat.choose (2 * n - 4) (n - 2) + 1)

restricted to 3 ≤ n ≤ 5 — exactly the range where the classical FINITE
witnesses live. The combined two-sided statement for 3 ≤ n ≤ 5 is the
in-kernel corollary `ersz_bounds_of_le_five` below.

THE PLAN (all classical, all finite — no infinitary construction anywhere):
  f n ≥ 2^(n-2)+1 ⟺ every N ∈ cardSet n satisfies N ≥ 2^(n-2)+1. For each
  n ∈ {3, 4, 5} a size-2^(n-2) general-position set with NO convex n-gon is
  exhibited, killing 2^(n-2) out of cardSet n:
    * n = 3 (size 2 = 2^1):  any two distinct points — no 3-point subset
      exists (§D2; `twoPts`, `two_not_mem_cardSet_three`);
    * n = 4 (size 4 = 2^2):  the Esther Klein configuration
      {(0,0), (3,0), (0,3)} + interior point (1,1) — no three collinear
      (four norm_num cross certificates) and (1,1) lies strictly inside the
      outer triangle (three norm_num oriented-area certificates), so the set
      is not convex independent (§D4; `kleinFourPts`,
      `four_not_mem_cardSet_four`);
    * n = 5 (size 8 = 2^3):  the classical Erdős–Szekeres 8-point
      4-cap {(0,0),(1,3),(2,5),(3,6)} ⊕ 4-cup {(20,100),(21,97),(22,95),
      (23,94)} — general position by an 8-choose-3 decide certificate, and
      NO convex 5-gon: every 5-subset has ≥ 3 cap-points + 1 cup-point or
      ≥ 3 cup-points + 1 cap-point (a 4-way decide pigeonhole on Fin 8), and
      in either case a middle chain vertex lies strictly inside a triangle of
      three others (§D5; `esEightFinset`, `eight_not_mem_cardSet_five`).
  Upward closure of cardSet (§D1, `cardSet_upward_closed`) then kills every
  N ≤ 2^(n-2) at once; with cardSet n NONEMPTY (the copied W82-107B cone,
  §11–§12: the Erdős–Szekeres 1935 cup–cap witness C(2n-4, n-2)+1 ∈ cardSet n
  for ALL n ≥ 3) `le_csInf` delivers 2^(n-2)+1 ≤ f n for each n ∈ {3,4,5},
  and the three literals assemble the headline.

PORTED DEPENDENCY CONE (§0–§12 below, VERBATIM from the CI-green sibling
kernel DM107_Proof_B.lean, the W82-107B lane — namespace changed
Erdos107 → Erdos107D and lane-attribution comments adjusted; code otherwise
byte-identical, reused with attribution). That cone is in turn ported from
the public Lean 4 proof chain cited by the upstream
google-deepmind/formal-conjectures file as the `formal_proof using lean4`
witness (linrock/math-proofs @ cd3cf0b176e95209584bf35555a7c0e501255f6e,
vendored under problem107-happy-ending/vendor_linrock/), providing:
    erdosSzekeresUpper_mem_cardSet  (C(2n-4, n-2)+1 ∈ cardSet n, all n ≥ 3)
    f_le_erdosSzekeresUpper         (f n ≤ C(2n-4, n-2)+1, all n ≥ 3)
    nonempty_cardSet_all            (cardSet n nonempty for EVERY n)
— the nonemptiness input that `le_csInf` needs. The decision to copy the
whole cone (rather than porting only 5 ∈ cardSet 4 / 21 ∈ cardSet 5 from
the vendor) follows the cheapest-complete-route analysis in
WORKLOG_W84_107B.md §2: the vendor has NO unconditional 9 ∈ cardSet 5, so
cardSet 5 ≠ ∅ necessarily goes through the ES-1935 general membership,
whose full cone is exactly what W82-107B already banked green.

NEW IN THIS KERNEL (§D1–§D6), ported from the same vendored upstream
(linrock/math-proofs, Apache-2.0, Copyright 2026 The Formal Conjectures
Authors / Linmiao Xu; file:line citations read before porting):
  * Erdos107Unified435.lean §0 (L49 `nonTrilinear_mono`, L207
    `hasConvexNGon_mono_pts`, L215 `cardSet_upward_closed`) — the heredity
    laws of the plan.
  * Erdos107Unified435.lean §1 (L364–510 the Klein 4-point witness) — with
    the hull-membership step recast through the InPosTriangle machinery
    (three norm_num oriented-area certificates instead of the upstream
    barycentric decomposition; see §D4).
  * Erdos107Unified435.lean §0 L119 `not_collinear_of_cross_ne_zero`.
  * Blueprint107.lean §1 (L87–244 the InPosTriangle machinery:
    `lineSide_triangle_sum`, `barycentric_of_lineSide_ne_zero`,
    `inPosTriangle_mem_convexHull`, `not_convexIndep_of_inPosTriangle`).
  * Blueprint107.lean §3 (L519–752 the 8-point pentagon-free certificate:
    the strict-order triple extraction, the Fin 8 cap/cup decide
    certificates, the cap/cup pigeonhole split, and
    `not_hasConvexFiveGon_esEightFinset`).
The toolchain adaptation is the one already executed for the shared cone by
the W82-107A/W82-107B lanes (module syntax stripped; the vendored official
definitions; `nonTrilinear_iff` (Iff.rfl) as the Set.Triplewise bridge).

ARSENAL BRIDGE (BOSS's law): imports Arsenal.ErdosTernary2.Basic and
Arsenal.CardinalWorlds; citations by file:line, read-before-cite:
    ErdosTernary2.lt_three_cases  (Arsenal/ErdosTernary2/Basic.lean:16)
    two_pow_pos                   (Arsenal/CardinalWorlds.lean:420)
    two_pow_ge2                   (Arsenal/CardinalWorlds.lean:431)

VERIFIED v4.33.0-rc2 API RECEIPTS for the NEW code (fetched at the tag,
never guessed; the cone's receipts are inherited from the green B kernel):
    Decidable (p → q) instance           Lean core Init/Core.lean:1157
    Fintype.decidableForallFintype       Mathlib/Data/Fintype/Defs.lean:209
    LinearOrder.toDecidableLT (Fin 8 lt) Mathlib/Order/Fin/Basic.lean:61 +
                                         Mathlib/Order/Defs/LinearOrder.lean:65–69,85
    Finset.exists_subset_card_eq         Mathlib/Data/Finset/Card.lean:664
    Finset.eq_of_subset_of_card_le       Mathlib/Data/Finset/Card.lean:282
    Finset.card_image_of_injective       Mathlib/Data/Finset/Card.lean:254
    Finset.card_pos                      Mathlib/Data/Finset/Card.lean:78
    Finset.card_univ                     Mathlib/Data/Fintype/Card.lean:104
    Fintype.card_fin                     Mathlib/Data/Fintype/Card.lean:497
    Finset.subset_image_iff              Mathlib/Data/Finset/Image.lean:717
    Finset.filter_subset_filter          Mathlib/Data/Finset/Filter.lean:185–186
    Finset.subset_univ                   Mathlib/Data/Fintype/Defs.lean:113
    Finset.coe_insert / coe_singleton    Mathlib/Data/Finset/Insert.lean:389/114
    subset_convexHull / convex_convexHull / convexHull_mono
                                         Mathlib/Analysis/Convex/Hull.lean:50/53/70
    Int.cast_inj / Int.cast_eq_zero      Mathlib/Data/Int/Cast/Lemmas.lean:67/57
    Int.cast_lt                          Mathlib/Algebra/Order/Ring/Cast.lean:62
Zero sorry, zero native_decide, no new axioms. Complete proof only.

HONEST SCOPE: this kernel claims the official lower side ONLY for 3 ≤ n ≤ 5
(the insurance range of the lane charter). The all-n lower side (the ES-1960
doubling construction) is NOT claimed here — that is lane W84-107A's war.
The all-n UPPER side is not re-claimed either (banked green by W82-107B's
`Erdos107.ersz_upper`); the in-kernel `f_le_erdosSzekeresUpper` is only the
copied cone lemma feeding the two-sided corollary.
-/
import Mathlib
import FC.Geometry.TwoD
import Arsenal.ErdosTernary2.Basic
import Arsenal.CardinalWorlds

set_option linter.deprecated false
set_option linter.unnecessarySimpa false
set_option linter.unusedSimpArgs false
set_option linter.unnecessarySeqFocus false
set_option maxHeartbeats 800000

noncomputable section

open Filter
open EuclideanGeometry

namespace Erdos107D

/-! ## §0 THE OFFICIAL DEFINITIONS (verbatim from DM107_Official.lean) -/

/-- The set of $N$ such that any $N$ points in the plane, no three on a line,
contain a convex $n$-gon. -/
def cardSet (n : ℕ) := { N | ∀ (pts : Finset ℝ²), pts.card = N → NonTrilinear (pts : Set ℝ²) →
  HasConvexNGon n pts }

/-- The function $f(n)$ specified in `erdos_107`. -/
noncomputable def f (n : ℕ) : ℕ :=
  sInf (cardSet n)

/-! ## §1 POINT ARITHMETIC (port of Erdos107Unified435.lean §1, `mkPt` + cross product;
copied verbatim from the green DM107_Proof_B.lean cone with the lane's one
addition `not_collinear_of_cross_ne_zero` from Erdos107Unified435.lean:119) -/

/-- Coordinate constructor for a point $(x, y) \in \mathbb{R}^2$. -/
def mkPt (x y : ℝ) : ℝ² :=
  EuclideanSpace.single (0 : Fin 2) x + EuclideanSpace.single (1 : Fin 2) y

@[simp]
theorem mkPt_zero (x y : ℝ) : mkPt x y 0 = x := by
  simp [mkPt]

@[simp]
theorem mkPt_one (x y : ℝ) : mkPt x y 1 = y := by
  simp [mkPt]

theorem mkPt_ext {x₁ y₁ x₂ y₂ : ℝ} (hx : x₁ = x₂) (hy : y₁ = y₂) :
    mkPt x₁ y₁ = mkPt x₂ y₂ := by
  rw [hx, hy]

/-- Collinear triples in $\mathbb{R}^2$ have vanishing 2D cross product. -/
theorem cross_eq_zero_of_collinear {a b c : ℝ²} (h : Collinear ℝ ({a, b, c} : Set ℝ²)) :
    (b 0 - a 0) * (c 1 - a 1) - (b 1 - a 1) * (c 0 - a 0) = 0 := by
  rw [collinear_iff_of_mem (by simp : a ∈ ({a, b, c} : Set ℝ²))] at h
  rcases h with ⟨v, hv⟩
  obtain ⟨rb, hrb⟩ := hv b (by simp)
  obtain ⟨rc, hrc⟩ := hv c (by simp)
  have hb0 : b 0 = rb * v 0 + a 0 := by
    have := congrArg (fun w : ℝ² => w 0) hrb
    simpa using this
  have hb1 : b 1 = rb * v 1 + a 1 := by
    have := congrArg (fun w : ℝ² => w 1) hrb
    simpa using this
  have hc0 : c 0 = rc * v 0 + a 0 := by
    have := congrArg (fun w : ℝ² => w 0) hrc
    simpa using this
  have hc1 : c 1 = rc * v 1 + a 1 := by
    have := congrArg (fun w : ℝ² => w 1) hrc
    simpa using this
  rw [hb0, hb1, hc0, hc1]
  ring

/-- Non-vanishing 2D cross product certifies non-collinearity of three points
in $\mathbb{R}^2$ (port of Erdos107Unified435.lean:119). -/
theorem not_collinear_of_cross_ne_zero {a b c : ℝ²}
    (h : (b 0 - a 0) * (c 1 - a 1) - (b 1 - a 1) * (c 0 - a 0) ≠ 0) :
    ¬ Collinear ℝ ({a, b, c} : Set ℝ²) :=
  fun hcoll => h (cross_eq_zero_of_collinear hcoll)

/-! ## §2 THE OFFICIAL `NonTrilinear` BRIDGE (definitional, for the vendored
`Set.Triplewise` packaging) -/

/-- The official `NonTrilinear` (a `Set.Triplewise` package, FC.Geometry.TwoD)
is definitionally the explicit six-binder statement used by the upstream
proof. -/
theorem nonTrilinear_iff {A : Set ℝ²} :
    NonTrilinear A ↔ ∀ ⦃x : ℝ²⦄, x ∈ A → ∀ ⦃y : ℝ²⦄, y ∈ A → ∀ ⦃z : ℝ²⦄, z ∈ A →
      x ≠ y → y ≠ z → x ≠ z → ¬ Collinear ℝ ({x, y, z} : Set ℝ²) :=
  Iff.rfl

/-! ## §3 SLOPE-TURN CALCULUS (port of Erdos107Unified435.lean §3, slopeLt/slopeGt) -/

/-- Strict upward turn (cup step) for three points ordered by $x$-coordinate. -/
def slopeLt (a b c : ℝ²) : Prop :=
  (b 1 - a 1) * (c 0 - b 0) < (c 1 - b 1) * (b 0 - a 0)

/-- Strict downward turn (cap step) for three points ordered by $x$-coordinate. -/
def slopeGt (a b c : ℝ²) : Prop :=
  (c 1 - b 1) * (b 0 - a 0) < (b 1 - a 1) * (c 0 - b 0)

/-- Any three non-collinear points with $a_0 \ne b_0$ form either a strict cup turn or a strict cap turn. -/
theorem slopeLt_or_slopeGt_of_not_collinear {a b c : ℝ²}
    (hab : a 0 ≠ b 0) (hnc : ¬ Collinear ℝ ({a, b, c} : Set ℝ²)) :
    slopeLt a b c ∨ slopeGt a b c := by
  rcases lt_trichotomy ((b 1 - a 1) * (c 0 - b 0)) ((c 1 - b 1) * (b 0 - a 0)) with hlt | heq | hgt
  · exact Or.inl hlt
  · exfalso
    apply hnc
    apply collinear_of_cross_eq_zero hab
    linarith
  · exact Or.inr hgt

/-! ## §4 THE ORIENTED CROSS-PRODUCT FUNCTIONAL `lineSide`
(port of Erdos107Unified435.lean §6) -/

/-- Signed 2D area (oriented cross product) of the triple $(p, q, r)$ in $\mathbb{R}^2$. -/
def lineSide (p q r : ℝ²) : ℝ :=
  (q 0 - p 0) * (r 1 - p 1) - (q 1 - p 1) * (r 0 - p 0)

/-- First coordinate of the normal vector to the directed line $p \to q$. -/
def lineNormX (p q : ℝ²) : ℝ :=
  -(q 1 - p 1)

/-- Second coordinate of the normal vector to the directed line $p \to q$. -/
def lineNormY (p q : ℝ²) : ℝ :=
  q 0 - p 0

/-- Affine constant of the directed line $p \to q$. -/
def lineConst (p q : ℝ²) : ℝ :=
  p 1 * q 0 - p 0 * q 1

/-- The oriented cross product vanishes at the first base point $p$. -/
theorem lineSide_self_left (p q : ℝ²) : lineSide p q p = 0 := by
  dsimp [lineSide]
  ring

/-- The oriented cross product vanishes at the second base point $q$. -/
theorem lineSide_self_right (p q : ℝ²) : lineSide p q q = 0 := by
  dsimp [lineSide]
  ring

/-- Swapping the two base points negates `lineSide`. -/
theorem lineSide_swap_left (p q r : ℝ²) : lineSide q p r = - lineSide p q r := by
  dsimp [lineSide]
  ring

/-- Swapping the second and third points negates `lineSide`. -/
theorem lineSide_swap_right (p q r : ℝ²) : lineSide p r q = - lineSide p q r := by
  dsimp [lineSide]
  ring

/-- Cyclic permutation of $(p, q, r)$ preserves `lineSide`. -/
theorem lineSide_cycle (p q r : ℝ²) : lineSide q r p = lineSide p q r := by
  dsimp [lineSide]
  ring

/-- Universal affine-linear decomposition of `lineSide p q r` in the test point $r$. -/
theorem lineSide_affine_decomp (p q r : ℝ²) :
    lineNormX p q * r 0 + lineNormY p q * r 1 = lineConst p q + lineSide p q r := by
  dsimp [lineNormX, lineNormY, lineConst, lineSide]
  ring

/-- Unconditional converse of `cross_eq_zero_of_collinear`: vanishing `lineSide p q r = 0`
implies `Collinear ℝ {p, q, r}` for all $p, q, r \in \mathbb{R}^2$ without any coordinate restriction. -/
theorem collinear_of_lineSide_eq_zero {p q r : ℝ²} (h : lineSide p q r = 0) :
    Collinear ℝ ({p, q, r} : Set ℝ²) := by
  by_cases hpq0 : p 0 = q 0
  · by_cases hpq1 : p 1 = q 1
    · have hpq : p = q := by
        ext i
        fin_cases i
        · exact hpq0
        · exact hpq1
      subst hpq
      have hpair : ({p, p, r} : Set ℝ²) = ({p, r} : Set ℝ²) := by ext; simp
      rw [hpair]
      exact collinear_pair ℝ p r
    · rw [collinear_iff_of_mem (by simp : p ∈ ({p, q, r} : Set ℝ²))]
      refine ⟨q - p, fun x hx => ?_⟩
      simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hx
      have hqp1 : q 1 - p 1 ≠ 0 := sub_ne_zero.mpr (Ne.symm hpq1)
      have hr0 : r 0 = p 0 := by
        dsimp [lineSide] at h
        have h0 : q 0 - p 0 = 0 := by linarith
        rw [h0, zero_mul, zero_sub, neg_eq_zero] at h
        rcases mul_eq_zero.mp h with h1 | h2
        · exact False.elim (hqp1 h1)
        · linarith
      rcases hx with rfl | rfl | rfl
      · exact ⟨0, by simp⟩
      · exact ⟨1, by simp⟩
      · refine ⟨(x 1 - p 1) / (q 1 - p 1), ?_⟩
        ext i
        fin_cases i
        · simp only [Fin.zero_eta, vadd_eq_add, PiLp.add_apply, PiLp.smul_apply,
            PiLp.sub_apply, smul_eq_mul]
          have hsub0 : q 0 - p 0 = 0 := by linarith
          rw [hsub0, mul_zero, zero_add]
          linarith
        · simp only [Fin.mk_one, vadd_eq_add, PiLp.add_apply, PiLp.smul_apply,
            PiLp.sub_apply, smul_eq_mul]
          have hmul : (x 1 - p 1) / (q 1 - p 1) * (q 1 - p 1) = x 1 - p 1 :=
            div_mul_cancel₀ _ hqp1
          linarith
  · exact collinear_of_cross_eq_zero hpq0 h

/-- `slopeLt a b c` is equivalent to `0 < lineSide a b c`. -/
theorem slopeLt_iff_lineSide_pos (a b c : ℝ²) :
    slopeLt a b c ↔ 0 < lineSide a b c := by
  dsimp [slopeLt, lineSide]
  constructor <;> intro h <;> linarith

/-- `slopeGt a b c` is equivalent to `lineSide a b c < 0`. -/
theorem slopeGt_iff_lineSide_neg (a b c : ℝ²) :
    slopeGt a b c ↔ lineSide a b c < 0 := by
  dsimp [slopeGt, lineSide]
  constructor <;> intro h <;> linarith

/-- Universal 4-point secant syzygy for `lineSide a b d` in terms of `lineSide a b c` and `lineSide b c d`. -/
theorem lineSide_four_step_syzygy_left (a b c d : ℝ²) :
    (c 0 - b 0) * lineSide a b d =
      (d 0 - b 0) * lineSide a b c + (b 0 - a 0) * lineSide b c d := by
  dsimp [lineSide]
  ring

/-- Universal 4-point secant syzygy for `lineSide a c d` in terms of `lineSide a b c` and `lineSide b c d`. -/
theorem lineSide_four_step_syzygy_right (a b c d : ℝ²) :
    (c 0 - b 0) * lineSide a c d =
      (d 0 - c 0) * lineSide a b c + (c 0 - a 0) * lineSide b c d := by
  dsimp [lineSide]
  ring

/-- Slope-turn transitivity on 4 points with $a_0 < b_0 < c_0 < d_0$:
if $(a, b, c)$ and $(b, c, d)$ are strict cup turns, then $(a, b, d)$ and $(a, c, d)$ are strict cup turns. -/
theorem slopeLt_trans_left_and_right {a b c d : ℝ²}
    (hab : a 0 < b 0) (hbc : b 0 < c 0) (hcd : c 0 < d 0)
    (h₁ : slopeLt a b c) (h₂ : slopeLt b c d) :
    slopeLt a b d ∧ slopeLt a c d := by
  rw [slopeLt_iff_lineSide_pos] at h₁ h₂ ⊢
  rw [slopeLt_iff_lineSide_pos]
  have hcb : 0 < c 0 - b 0 := sub_pos.mpr hbc
  have hdb : 0 < d 0 - b 0 := by linarith
  have hba : 0 < b 0 - a 0 := sub_pos.mpr hab
  have hdc : 0 < d 0 - c 0 := sub_pos.mpr hcd
  have hca : 0 < c 0 - a 0 := by linarith
  have hsyz₁ := lineSide_four_step_syzygy_left a b c d
  have hsyz₂ := lineSide_four_step_syzygy_right a b c d
  have hpos₁ : 0 < (c 0 - b 0) * lineSide a b d := by
    rw [hsyz₁]
    positivity
  have hpos₂ : 0 < (c 0 - b 0) * lineSide a c d := by
    rw [hsyz₂]
    positivity
  exact ⟨pos_of_mul_pos_right hpos₁ (le_of_lt hcb),
    pos_of_mul_pos_right hpos₂ (le_of_lt hcb)⟩

/-- Slope-turn transitivity on 4 points with $a_0 < b_0 < c_0 < d_0$ for cap turns:
if $(a, b, c)$ and $(b, c, d)$ are strict cap turns, then $(a, b, d)$ and $(a, c, d)$ are strict cap turns. -/
theorem slopeGt_trans_left_and_right {a b c d : ℝ²}
    (hab : a 0 < b 0) (hbc : b 0 < c 0) (hcd : c 0 < d 0)
    (h₁ : slopeGt a b c) (h₂ : slopeGt b c d) :
    slopeGt a b d ∧ slopeGt a c d := by
  rw [slopeGt_iff_lineSide_neg] at h₁ h₂ ⊢
  rw [slopeGt_iff_lineSide_neg]
  have hcb : 0 < c 0 - b 0 := sub_pos.mpr hbc
  have hdb : 0 < d 0 - b 0 := by linarith
  have hba : 0 < b 0 - a 0 := sub_pos.mpr hab
  have hdc : 0 < d 0 - c 0 := sub_pos.mpr hcd
  have hca : 0 < c 0 - a 0 := by linarith
  have hsyz₁ := lineSide_four_step_syzygy_left a b c d
  have hsyz₂ := lineSide_four_step_syzygy_right a b c d
  have hneg₁ : (c 0 - b 0) * lineSide a b d < 0 := by rw [hsyz₁]; nlinarith
  have hneg₂ : (c 0 - b 0) * lineSide a c d < 0 := by rw [hsyz₂]; nlinarith
  exact ⟨by nlinarith, by nlinarith⟩

/-! ## §5 HALF-PLANE SEPARATION AND `ConvexIndep`
(port of Erdos107Unified435.lean §4) -/

/-- Closed affine half-plane $\{p \in \mathbb{R}^2 \mid u p_0 + v p_1 \le c\}$. -/
def halfPlaneLe (u v c : ℝ) : Set ℝ² :=
  { p : ℝ² | u * p 0 + v * p 1 ≤ c }

/-- Every closed affine half-plane in $\mathbb{R}^2$ is convex. -/
theorem convex_halfPlaneLe (u v c : ℝ) : Convex ℝ (halfPlaneLe u v c) := by
  intro x hx y hy a b ha hb hab
  change u * x 0 + v * x 1 ≤ c at hx
  change u * y 0 + v * y 1 ≤ c at hy
  change u * (a • x + b • y) 0 + v * (a • x + b • y) 1 ≤ c
  have h0 : (a • x + b • y) 0 = a * x 0 + b * y 0 := rfl
  have h1 : (a • x + b • y) 1 = a * x 1 + b * y 1 := rfl
  rw [h0, h1]
  have hax : a * (u * x 0 + v * x 1) ≤ a * c := mul_le_mul_of_nonneg_left hx ha
  have hby : b * (u * y 0 + v * y 1) ≤ b * c := mul_le_mul_of_nonneg_left hy hb
  have hc : a * c + b * c = c := by linear_combination c * hab
  linarith

/-- If a point set $S \subseteq \mathbb{R}^2$ lies in a closed affine half-plane, so does its convex hull. -/
theorem convexHull_subset_halfPlaneLe {u v c : ℝ} {S : Set ℝ²}
    (hS : ∀ y ∈ S, u * y 0 + v * y 1 ≤ c) :
    convexHull ℝ S ⊆ halfPlaneLe u v c :=
  convexHull_min hS (convex_halfPlaneLe u v c)

/-- Universal strict linear separation exclusion: if $u y_0 + v y_1 \le c$ for all $y \in S$
and $c < u x_0 + v x_1$, then $x \notin \mathrm{convexHull}\,\mathbb{R}\,S$. -/
theorem not_mem_convexHull_of_strict_linear_sep {u v c : ℝ} {S : Set ℝ²} {x : ℝ²}
    (hS : ∀ y ∈ S, u * y 0 + v * y 1 ≤ c)
    (hx : c < u * x 0 + v * x 1) :
    x ∉ convexHull ℝ S := by
  intro hmem
  have hle : u * x 0 + v * x 1 ≤ c := convexHull_subset_halfPlaneLe hS hmem
  linarith

/-- Universal pointwise linear separation criterion for `ConvexIndep`. -/
theorem convexIndep_of_pointwise_strict_sep {S : Set ℝ²}
    (hsep : ∀ x ∈ S, ∃ u v c : ℝ,
      (∀ y ∈ S \ {x}, u * y 0 + v * y 1 ≤ c) ∧ c < u * x 0 + v * x 1) :
    ConvexIndep S := by
  intro x hx
  rcases hsep x hx with ⟨u, v, c, hle, hlt⟩
  exact not_mem_convexHull_of_strict_linear_sep hle hlt

/-! ## §6 SEQUENCES, CUP/CAP CHAINS, AND THE ES 1935 PIGEONHOLE CORE
(port of Erdos107Unified435.lean §3 + the `_on` localization from
XMonotonePerturbation107.lean §2) -/

/-- A point sequence $P : \mathbb{N} \to \mathbb{R}^2$ is $x$-monotone if its $x$-coordinates are strictly increasing. -/
def IsXMonotone (P : ℕ → ℝ²) : Prop :=
  StrictMono (fun i => P i 0)

/-- Strictly increasing indices in an $x$-monotone sequence map to distinct points. -/
theorem xMonotone_ne_of_lt {P : ℕ → ℝ²} (hmono : IsXMonotone P) {i j : ℕ} (hij : i < j) :
    P i ≠ P j := by
  intro h
  have h0 := congrArg (fun w : ℝ² => w 0) h
  exact (ne_of_lt (hmono hij)) h0

/-- Localized non-trilinearity of a sequence $P : \mathbb{N} \to \mathbb{R}^2$ restricted to $S : \text{Finset}\,\mathbb{N}$. -/
def IsSeqNonTrilinearOn (P : ℕ → ℝ²) (S : Finset ℕ) : Prop :=
  ∀ ⦃i j k : ℕ⦄, i ∈ S → j ∈ S → k ∈ S → i < j → j < k →
    ¬ Collinear ℝ ({P i, P j, P k} : Set ℝ²)

theorem isSeqNonTrilinearOn_mono {P : ℕ → ℝ²} {S T : Finset ℕ}
    (hST : S ⊆ T) (hT : IsSeqNonTrilinearOn P T) :
    IsSeqNonTrilinearOn P S :=
  fun _ _ _ hi hj hk hij hjk => hT (hST hi) (hST hj) (hST hk) hij hjk

/-- `CupChainEnding P S m a b` means $S$ contains an $(m + 2)$-cup whose last two indices are $a < b$. -/
def CupChainEnding (P : ℕ → ℝ²) (S : Finset ℕ) : ℕ → ℕ → ℕ → Prop
  | 0, a, b => a ∈ S ∧ b ∈ S ∧ a < b
  | m + 1, b, c => b ∈ S ∧ c ∈ S ∧ b < c ∧ ∃ a, CupChainEnding P S m a b ∧ slopeLt (P a) (P b) (P c)

/-- `CapChainStarting P S k b c` means $S$ contains a $(k + 2)$-cap whose first two indices are $b < c$. -/
def CapChainStarting (P : ℕ → ℝ²) (S : Finset ℕ) : ℕ → ℕ → ℕ → Prop
  | 0, b, c => b ∈ S ∧ c ∈ S ∧ b < c
  | k + 1, a, b => a ∈ S ∧ b ∈ S ∧ a < b ∧ ∃ c, slopeGt (P a) (P b) (P c) ∧ CapChainStarting P S k b c

/-- `HasCup P S m` means $S$ contains an $(m + 2)$-cup. -/
def HasCup (P : ℕ → ℝ²) (S : Finset ℕ) (m : ℕ) : Prop :=
  ∃ a b, CupChainEnding P S m a b

/-- `HasCap P S k` means $S$ contains a $(k + 2)$-cap. -/
def HasCap (P : ℕ → ℝ²) (S : Finset ℕ) (k : ℕ) : Prop :=
  ∃ b c, CapChainStarting P S k b c

theorem cupChainEnding_left_mem {P : ℕ → ℝ²} {S : Finset ℕ} {m a b : ℕ}
    (h : CupChainEnding P S m a b) : a ∈ S := by
  cases m with
  | zero => exact h.1
  | succ _ => exact h.1

theorem cupChainEnding_right_mem {P : ℕ → ℝ²} {S : Finset ℕ} {m a b : ℕ}
    (h : CupChainEnding P S m a b) : b ∈ S := by
  cases m with
  | zero => exact h.2.1
  | succ _ => exact h.2.1

theorem cupChainEnding_lt {P : ℕ → ℝ²} {S : Finset ℕ} {m a b : ℕ}
    (h : CupChainEnding P S m a b) : a < b := by
  cases m with
  | zero => exact h.2.2
  | succ _ => exact h.2.2.1

theorem capChainStarting_left_mem {P : ℕ → ℝ²} {S : Finset ℕ} {k b c : ℕ}
    (h : CapChainStarting P S k b c) : b ∈ S := by
  cases k with
  | zero => exact h.1
  | succ _ => exact h.1

theorem capChainStarting_right_mem {P : ℕ → ℝ²} {S : Finset ℕ} {k b c : ℕ}
    (h : CapChainStarting P S k b c) : c ∈ S := by
  cases k with
  | zero => exact h.2.1
  | succ _ => exact h.2.1

theorem capChainStarting_lt {P : ℕ → ℝ²} {S : Finset ℕ} {k b c : ℕ}
    (h : CapChainStarting P S k b c) : b < c := by
  cases k with
  | zero => exact h.2.2
  | succ _ => exact h.2.2.1

theorem cupChainEnding_mono {P : ℕ → ℝ²} {S T : Finset ℕ} (hST : S ⊆ T) :
    ∀ {m a b : ℕ}, CupChainEnding P S m a b → CupChainEnding P T m a b
  | 0, _, _, ⟨ha, hb, hab⟩ => ⟨hST ha, hST hb, hab⟩
  | _ + 1, _, _, ⟨hb, hc, hbc, a, hcup, hsl⟩ =>
      ⟨hST hb, hST hc, hbc, a, cupChainEnding_mono hST hcup, hsl⟩

theorem capChainStarting_mono {P : ℕ → ℝ²} {S T : Finset ℕ} (hST : S ⊆ T) :
    ∀ {k b c : ℕ}, CapChainStarting P S k b c → CapChainStarting P T k b c
  | 0, _, _, ⟨hb, hc, hbc⟩ => ⟨hST hb, hST hc, hbc⟩
  | _ + 1, _, _, ⟨ha, hb, hab, c, hsg, hcap⟩ =>
      ⟨hST ha, hST hb, hab, c, hsg, capChainStarting_mono hST hcap⟩

theorem hasCup_mono {P : ℕ → ℝ²} {S T : Finset ℕ} {m : ℕ}
    (hST : S ⊆ T) (h : HasCup P S m) : HasCup P T m := by
  rcases h with ⟨a, b, hab⟩
  exact ⟨a, b, cupChainEnding_mono hST hab⟩

theorem hasCap_mono {P : ℕ → ℝ²} {S T : Finset ℕ} {k : ℕ}
    (hST : S ⊆ T) (h : HasCap P S k) : HasCap P T k := by
  rcases h with ⟨b, c, hbc⟩
  exact ⟨b, c, capChainStarting_mono hST hbc⟩

/-- Localized Endpoint-Gluing Lemma on a finite index set $S$
(port of `cup_end_meets_cap_start_on`, XMonotonePerturbation107.lean). -/
theorem cup_end_meets_cap_start_on {P : ℕ → ℝ²} {S : Finset ℕ} {m k a b c : ℕ}
    (hmono : IsXMonotone P) (hnontri : IsSeqNonTrilinearOn P S)
    (hcup : CupChainEnding P S m a b) (hcap : CapChainStarting P S k b c) :
    HasCup P S (m + 1) ∨ HasCap P S (k + 1) := by
  have hab : a < b := cupChainEnding_lt hcup
  have hbc : b < c := capChainStarting_lt hcap
  have haS : a ∈ S := cupChainEnding_left_mem hcup
  have hbS : b ∈ S := cupChainEnding_right_mem hcup
  have hcS : c ∈ S := capChainStarting_right_mem hcap
  have hxne : P a 0 ≠ P b 0 := ne_of_lt (hmono hab)
  have hnc : ¬ Collinear ℝ ({P a, P b, P c} : Set ℝ²) := hnontri haS hbS hcS hab hbc
  rcases slopeLt_or_slopeGt_of_not_collinear hxne hnc with hsl | hsg
  · exact Or.inl ⟨b, c, hbS, hcS, hbc, a, hcup, hsl⟩
  · exact Or.inr ⟨a, b, haS, hbS, hab, c, hsg, hcap⟩

/-- Localized Erdős–Szekeres Cup–Cap Theorem on any finite index set $S$ where `IsSeqNonTrilinearOn P S` holds
(port of `erdos_szekeres_cup_cap_theorem_on`, XMonotonePerturbation107.lean —
the ES 1935 Pascal-splitting pigeonhole induction). -/
theorem erdos_szekeres_cup_cap_theorem_on {P : ℕ → ℝ²} (hmono : IsXMonotone P) :
    ∀ (m k : ℕ) (S : Finset ℕ),
      IsSeqNonTrilinearOn P S →
      (m + k).choose m + 1 ≤ S.card → HasCup P S m ∨ HasCap P S k
  | 0, _, S, _, hcard => by
      simp only [Nat.zero_add, Nat.choose_zero_right] at hcard
      obtain ⟨x, y, hx, hy, hxy⟩ := Finset.one_lt_card_iff.mp (by omega : 1 < S.card)
      rcases lt_or_gt_of_ne hxy with hlt | hgt
      · exact Or.inl ⟨x, y, hx, hy, hlt⟩
      · exact Or.inl ⟨y, x, hy, hx, hgt⟩
  | _ + 1, 0, S, _, hcard => by
      simp only [Nat.add_zero, Nat.choose_self] at hcard
      obtain ⟨x, y, hx, hy, hxy⟩ := Finset.one_lt_card_iff.mp (by omega : 1 < S.card)
      rcases lt_or_gt_of_ne hxy with hlt | hgt
      · exact Or.inr ⟨x, y, hx, hy, hlt⟩
      · exact Or.inr ⟨y, x, hy, hx, hgt⟩
  | m + 1, k + 1, S, hnontri, hcard => by
      classical
      let E : Finset ℕ := S.filter (fun b => ∃ a, CupChainEnding P S m a b)
      have hES : E ⊆ S := Finset.filter_subset _ _
      have hpart : (S \ E).card + E.card = S.card := Finset.card_sdiff_add_card_eq_card hES
      have hchoose : ((m + 1) + (k + 1)).choose (m + 1) =
          (m + (k + 1)).choose m + ((m + 1) + k).choose (m + 1) := by
        simpa [Nat.add_assoc, Nat.add_left_comm, Nat.add_comm] using
          Nat.choose_succ_succ (m + k + 1) m
      by_cases hSE : (m + (k + 1)).choose m + 1 ≤ (S \ E).card
      · rcases erdos_szekeres_cup_cap_theorem_on hmono m (k + 1) (S \ E)
            (isSeqNonTrilinearOn_mono Finset.sdiff_subset hnontri) hSE with hcup | hcap
        · rcases hcup with ⟨a, b, hab⟩
          have hb_mem : b ∈ S \ E := cupChainEnding_right_mem hab
          have hb_cup : CupChainEnding P S m a b := cupChainEnding_mono Finset.sdiff_subset hab
          rw [Finset.mem_sdiff, Finset.mem_filter] at hb_mem
          exact False.elim (hb_mem.2 ⟨hb_mem.1, a, hb_cup⟩)
        · exact Or.inr (hasCap_mono Finset.sdiff_subset hcap)
      · have hE_card : ((m + 1) + k).choose (m + 1) + 1 ≤ E.card := by omega
        rcases erdos_szekeres_cup_cap_theorem_on hmono (m + 1) k E
            (isSeqNonTrilinearOn_mono hES hnontri) hE_card with hcupE | hcapE
        · exact Or.inl (hasCup_mono hES hcupE)
        · rcases hcapE with ⟨b, c, hcap⟩
          have hbE : b ∈ E := capChainStarting_left_mem hcap
          rw [Finset.mem_filter] at hbE
          rcases hbE.2 with ⟨a, hcup⟩
          have hcapS : CapChainStarting P S k b c := capChainStarting_mono hES hcap
          exact cup_end_meets_cap_start_on hmono hnontri hcup hcapS

/-- The Erdős–Szekeres diagonal upper bound $\binom{2n-4}{n-2} + 1$ for $f(n)$. -/
def erdosSzekeresUpper (n : ℕ) : ℕ :=
  (2 * n - 4).choose (n - 2) + 1

/-! ## §7 ALL-TRIPLE CUP/CAP SETS AND CONVEX INDEPENDENCE
(port of InductiveKCupKCapConvexityAndKKSWedgePentagonForcing107.lean §1) -/

/-- A finite index set $C \subseteq \mathbb{N}$ is an all-triple cup set for $P$ if every strictly increasing
triple $x < y < z$ in $C$ has strictly positive oriented area `0 < lineSide (P x) (P y) (P z)`. -/
def IsCupSet (P : ℕ → ℝ²) (C : Finset ℕ) : Prop :=
  ∀ ⦃x y z : ℕ⦄, x ∈ C → y ∈ C → z ∈ C → x < y → y < z → 0 < lineSide (P x) (P y) (P z)

/-- A finite index set $C \subseteq \mathbb{N}$ is an all-triple cap set for $P$ if every strictly increasing
triple $x < y < z$ in $C$ has strictly negative oriented area `lineSide (P x) (P y) (P z) < 0`. -/
def IsCapSet (P : ℕ → ℝ²) (C : Finset ℕ) : Prop :=
  ∀ ⦃x y z : ℕ⦄, x ∈ C → y ∈ C → z ∈ C → x < y → y < z → lineSide (P x) (P y) (P z) < 0

/-- Any two-element index set $\{a, b\}$ satisfies `IsCupSet P {a, b}`. -/
theorem isCupSet_pair (P : ℕ → ℝ²) (a b : ℕ) : IsCupSet P ({a, b} : Finset ℕ) := by
  intro x y z hx hy hz hxy hyz
  simp only [Finset.mem_insert, Finset.mem_singleton] at hx hy hz
  rcases hx with rfl | rfl <;> rcases hy with rfl | rfl <;> rcases hz with rfl | rfl <;> omega

/-- Any two-element index set $\{b, c\}$ satisfies `IsCapSet P {b, c}`. -/
theorem isCapSet_pair (P : ℕ → ℝ²) (b c : ℕ) : IsCapSet P ({b, c} : Finset ℕ) := by
  intro x y z hx hy hz hxy hyz
  simp only [Finset.mem_insert, Finset.mem_singleton] at hx hy hz
  rcases hx with rfl | rfl <;> rcases hy with rfl | rfl <;> rcases hz with rfl | rfl <;> omega

/-- **Universal Right End-Extension Theorem for Cup Sets**:
If $C$ is an all-triple cup set for an $x$-monotone sequence $P$ whose largest two elements are $a < b$,
and $b < c$ satisfies the single adjacent turn condition `slopeLt (P a) (P b) (P c)`, then `insert c C`
is also an all-triple cup set for $P$. -/
theorem isCupSet_insert_right {P : ℕ → ℝ²} (hmono : IsXMonotone P) {C : Finset ℕ} {a b c : ℕ}
    (haC : a ∈ C) (hbC : b ∈ C) (hab : a < b) (hbc : b < c)
    (hle_b : ∀ x ∈ C, x ≤ b) (hle_a : ∀ x ∈ C, x < b → x ≤ a)
    (hcup : IsCupSet P C) (hturn : slopeLt (P a) (P b) (P c)) :
    IsCupSet P (insert c C) := by
  have h_ubc : ∀ u ∈ C, u < b → slopeLt (P u) (P b) (P c) := by
    intro u hu hub
    have hua : u ≤ a := hle_a u hu hub
    rcases lt_or_eq_of_le hua with hlt | rfl
    · have huab : slopeLt (P u) (P a) (P b) :=
        (slopeLt_iff_lineSide_pos _ _ _).mpr (hcup hu haC hbC hlt hab)
      exact (slopeLt_trans_left_and_right (hmono hlt) (hmono hab) (hmono hbc) huab hturn).2
    · exact hturn
  intro x y z hx hy hz hxy hyz
  have hxC : x ∈ C := by
    rcases Finset.mem_insert.mp hx with rfl | hxC
    · exfalso
      rcases Finset.mem_insert.mp hz with rfl | hzC
      · omega
      · have := hle_b z hzC; omega
    · exact hxC
  have hyC : y ∈ C := by
    rcases Finset.mem_insert.mp hy with rfl | hyC
    · exfalso
      rcases Finset.mem_insert.mp hz with rfl | hzC
      · omega
      · have := hle_b z hzC; omega
    · exact hyC
  rcases Finset.mem_insert.mp hz with hzc | hzC
  · rw [hzc]
    have hyb : y ≤ b := hle_b y hyC
    rcases lt_or_eq_of_le hyb with hyb_lt | rfl
    · have hxyb : slopeLt (P x) (P y) (P b) :=
        (slopeLt_iff_lineSide_pos _ _ _).mpr (hcup hxC hyC hbC hxy hyb_lt)
      have hybc : slopeLt (P y) (P b) (P c) := h_ubc y hyC hyb_lt
      have hxyc : slopeLt (P x) (P y) (P c) :=
        (slopeLt_trans_left_and_right (hmono hxy) (hmono hyb_lt) (hmono hbc) hxyb hybc).1
      exact (slopeLt_iff_lineSide_pos _ _ _).mp hxyc
    · exact (slopeLt_iff_lineSide_pos _ _ _).mp (h_ubc x hxC hxy)
  · exact hcup hxC hyC hzC hxy hyz

/-- **Universal Left End-Extension Theorem for Cap Sets**:
If $C$ is an all-triple cap set for an $x$-monotone sequence $P$ whose smallest two elements are $b < c$,
and $a < b$ satisfies the single adjacent turn condition `slopeGt (P a) (P b) (P c)`, then `insert a C`
is also an all-triple cap set for $P$. -/
theorem isCapSet_insert_left {P : ℕ → ℝ²} (hmono : IsXMonotone P) {C : Finset ℕ} {a b c : ℕ}
    (hbC : b ∈ C) (hcC : c ∈ C) (hab : a < b) (hbc : b < c)
    (hge_b : ∀ x ∈ C, b ≤ x) (hge_c : ∀ x ∈ C, b < x → c ≤ x)
    (hcap : IsCapSet P C) (hturn : slopeGt (P a) (P b) (P c)) :
    IsCapSet P (insert a C) := by
  have h_abw : ∀ w ∈ C, b < w → slopeGt (P a) (P b) (P w) := by
    intro w hw hbw
    have hcw : c ≤ w := hge_c w hw hbw
    rcases lt_or_eq_of_le hcw with hlt | rfl
    · have hbcw : slopeGt (P b) (P c) (P w) :=
        (slopeGt_iff_lineSide_neg _ _ _).mpr (hcap hbC hcC hw hbc hlt)
      exact (slopeGt_trans_left_and_right (hmono hab) (hmono hbc) (hmono hlt) hturn hbcw).1
    · exact hturn
  intro x y z hx hy hz hxy hyz
  have hzC : z ∈ C := by
    rcases Finset.mem_insert.mp hz with rfl | hzC
    · exfalso
      rcases Finset.mem_insert.mp hx with rfl | hxC
      · omega
      · have := hge_b x hxC; omega
    · exact hzC
  have hyC : y ∈ C := by
    rcases Finset.mem_insert.mp hy with rfl | hyC
    · exfalso
      rcases Finset.mem_insert.mp hx with rfl | hxC
      · omega
      · have := hge_b x hxC; omega
    · exact hyC
  rcases Finset.mem_insert.mp hx with hxa | hxC
  · rw [hxa]
    have hby : b ≤ y := hge_b y hyC
    rcases lt_or_eq_of_le hby with hby_lt | rfl
    · have haby : slopeGt (P a) (P b) (P y) := h_abw y hyC hby_lt
      have hbyz : slopeGt (P b) (P y) (P z) :=
        (slopeGt_iff_lineSide_neg _ _ _).mpr (hcap hbC hyC hzC hby_lt hyz)
      have hayz : slopeGt (P a) (P y) (P z) :=
        (slopeGt_trans_left_and_right (hmono hab) (hmono hby_lt) (hmono hyz) haby hbyz).2
      exact (slopeGt_iff_lineSide_neg _ _ _).mp hayz
    · exact (slopeGt_iff_lineSide_neg _ _ _).mp (h_abw z hzC hyz)
  · exact hcap hxC hyC hzC hxy hyz

/-- **Universal Skipped-Vertex Chord Separation Lemma for Cup Sets**:
For any three consecutive indices $l < v < r$ in an all-triple cup set $C$, the directed chord
$P(r) \to P(l)$ keeps all $P(z)$ ($z \in C \setminus \{v\}$) on its non-positive side while placing
$P(v)$ on its strictly positive side. -/
theorem isCupSet_skipped_chord_sep {P : ℕ → ℝ²} {C : Finset ℕ} (hcup : IsCupSet P C)
    {l v r : ℕ} (hlC : l ∈ C) (hvC : v ∈ C) (hrC : r ∈ C)
    (hlv : l < v) (hvr : v < r) (hgap : ∀ z ∈ C, z ≠ v → z ≤ l ∨ r ≤ z) :
    (∀ z ∈ C, z ≠ v → lineSide (P r) (P l) (P z) ≤ 0) ∧ 0 < lineSide (P r) (P l) (P v) := by
  have hlr : l < r := lt_trans hlv hvr
  refine ⟨?_, ?_⟩
  · intro z hzC hzv
    rcases hgap z hzC hzv with hzl | hrz
    · rcases lt_or_eq_of_le hzl with hlt | rfl
      · have hpos : 0 < lineSide (P z) (P l) (P r) := hcup hzC hlC hrC hlt hlr
        have hrel : lineSide (P r) (P l) (P z) = - lineSide (P z) (P l) (P r) := by
          dsimp [lineSide]; ring
        linarith
      · rw [lineSide_self_right]
    · rcases lt_or_eq_of_le hrz with hlt | rfl
      · have hpos : 0 < lineSide (P l) (P r) (P z) := hcup hlC hrC hzC hlr hlt
        have hrel : lineSide (P r) (P l) (P z) = - lineSide (P l) (P r) (P z) :=
          lineSide_swap_left _ _ _
        linarith
      · rw [lineSide_self_left]
  · have hpos : 0 < lineSide (P l) (P v) (P r) := hcup hlC hvC hrC hlv hvr
    have hrel : lineSide (P r) (P l) (P v) = lineSide (P l) (P v) (P r) := by
      dsimp [lineSide]; ring
    linarith

/-- **Universal Skipped-Vertex Chord Separation Lemma for Cap Sets**:
For any three consecutive indices $l < v < r$ in an all-triple cap set $C$, the directed chord
$P(l) \to P(r)$ keeps all $P(z)$ ($z \in C \setminus \{v\}$) on its non-positive side while placing
$P(v)$ on its strictly positive side. -/
theorem isCapSet_skipped_chord_sep {P : ℕ → ℝ²} {C : Finset ℕ} (hcap : IsCapSet P C)
    {l v r : ℕ} (hlC : l ∈ C) (hvC : v ∈ C) (hrC : r ∈ C)
    (hlv : l < v) (hvr : v < r) (hgap : ∀ z ∈ C, z ≠ v → z ≤ l ∨ r ≤ z) :
    (∀ z ∈ C, z ≠ v → lineSide (P l) (P r) (P z) ≤ 0) ∧ 0 < lineSide (P l) (P r) (P v) := by
  have hlr : l < r := lt_trans hlv hvr
  refine ⟨?_, ?_⟩
  · intro z hzC hzv
    rcases hgap z hzC hzv with hzl | hrz
    · rcases lt_or_eq_of_le hzl with hlt | rfl
      · have hneg : lineSide (P z) (P l) (P r) < 0 := hcap hzC hlC hrC hlt hlr
        have hrel : lineSide (P l) (P r) (P z) = lineSide (P z) (P l) (P r) := by
          dsimp [lineSide]; ring
        linarith
      · rw [lineSide_self_left]
    · rcases lt_or_eq_of_le hrz with hlt | rfl
      · exact le_of_lt (hcap hlC hrC hzC hlr hlt)
      · rw [lineSide_self_right]
  · have hneg : lineSide (P l) (P v) (P r) < 0 := hcap hlC hvC hrC hlv hvr
    have hrel : lineSide (P l) (P r) (P v) = - lineSide (P l) (P v) (P r) := by
      dsimp [lineSide]; ring
    linarith

/-- **Universal All-Triple Cup Convex Independence Theorem**:
For every finite index set $C \subseteq \mathbb{N}$ of arbitrary cardinality and every $x$-monotone
sequence $P$, if `IsCupSet P C` holds then the point set $P(C)$ is convex independent (`ConvexIndep`). -/
theorem convexIndep_of_isCupSet {P : ℕ → ℝ²} (hmono : IsXMonotone P) {C : Finset ℕ}
    (hcup : IsCupSet P C) : ConvexIndep (P '' (C : Set ℕ)) := by
  apply convexIndep_of_pointwise_strict_sep
  rintro x ⟨v, hvC_coe, rfl⟩
  have hvC : v ∈ C := hvC_coe
  let L := C.filter (fun z => z < v)
  let R := C.filter (fun z => v < z)
  by_cases hL : L.Nonempty
  · by_cases hR : R.Nonempty
    · let l := L.max' hL
      let r := R.min' hR
      have hlL : l ∈ L := Finset.max'_mem L hL
      have hrR : r ∈ R := Finset.min'_mem R hR
      have hlC : l ∈ C := (Finset.mem_filter.mp hlL).1
      have hlv : l < v := (Finset.mem_filter.mp hlL).2
      have hrC : r ∈ C := (Finset.mem_filter.mp hrR).1
      have hvr : v < r := (Finset.mem_filter.mp hrR).2
      have hgap : ∀ z ∈ C, z ≠ v → z ≤ l ∨ r ≤ z := by
        intro z hzC hzv
        rcases lt_or_gt_of_ne hzv with hlt | hgt
        · left
          exact Finset.le_max' L z (Finset.mem_filter.mpr ⟨hzC, hlt⟩)
        · right
          exact Finset.min'_le R z (Finset.mem_filter.mpr ⟨hzC, hgt⟩)
      obtain ⟨h_le, h_pos⟩ := isCupSet_skipped_chord_sep hcup hlC hvC hrC hlv hvr hgap
      refine ⟨lineNormX (P r) (P l), lineNormY (P r) (P l), lineConst (P r) (P l), ?_, ?_⟩
      · rintro y ⟨⟨z, hzC_coe, rfl⟩, hy_ne⟩
        have hzv : z ≠ v := fun h => hy_ne (congrArg P h)
        have h_side := h_le z hzC_coe hzv
        rw [lineSide_affine_decomp]
        linarith
      · rw [lineSide_affine_decomp]
        linarith
    · let l := L.max' hL
      have hlL : l ∈ L := Finset.max'_mem L hL
      have hlv : l < v := (Finset.mem_filter.mp hlL).2
      have hxlv : P l 0 < P v 0 := hmono hlv
      refine ⟨1, 0, P l 0, ?_, by linarith⟩
      rintro y ⟨⟨z, hzC_coe, rfl⟩, hy_ne⟩
      have hzv : z ≠ v := fun h => hy_ne (congrArg P h)
      rcases lt_or_gt_of_ne hzv with hlt | hgt
      · have hzl : z ≤ l := Finset.le_max' L z (Finset.mem_filter.mpr ⟨hzC_coe, hlt⟩)
        have hxz : P z 0 ≤ P l 0 := hmono.monotone hzl
        linarith
      · exfalso
        exact hR ⟨z, Finset.mem_filter.mpr ⟨hzC_coe, hgt⟩⟩
  · by_cases hR : R.Nonempty
    · let r := R.min' hR
      have hrR : r ∈ R := Finset.min'_mem R hR
      have hvr : v < r := (Finset.mem_filter.mp hrR).2
      have hxvr : P v 0 < P r 0 := hmono hvr
      refine ⟨-1, 0, -P r 0, ?_, by linarith⟩
      rintro y ⟨⟨z, hzC_coe, rfl⟩, hy_ne⟩
      have hzv : z ≠ v := fun h => hy_ne (congrArg P h)
      rcases lt_or_gt_of_ne hzv with hlt | hgt
      · exfalso
        exact hL ⟨z, Finset.mem_filter.mpr ⟨hzC_coe, hlt⟩⟩
      · have hrz : r ≤ z := Finset.min'_le R z (Finset.mem_filter.mpr ⟨hzC_coe, hgt⟩)
        have hxz : P r 0 ≤ P z 0 := hmono.monotone hrz
        linarith
    · refine ⟨0, 0, -1, ?_, by linarith⟩
      rintro y ⟨⟨z, hzC_coe, rfl⟩, hy_ne⟩
      have hzv : z ≠ v := fun h => hy_ne (congrArg P h)
      rcases lt_or_gt_of_ne hzv with hlt | hgt
      · exfalso
        exact hL ⟨z, Finset.mem_filter.mpr ⟨hzC_coe, hlt⟩⟩
      · exfalso
        exact hR ⟨z, Finset.mem_filter.mpr ⟨hzC_coe, hgt⟩⟩

/-- **Universal All-Triple Cap Convex Independence Theorem**:
For every finite index set $C \subseteq \mathbb{N}$ of arbitrary cardinality and every $x$-monotone
sequence $P$, if `IsCapSet P C` holds then the point set $P(C)$ is convex independent (`ConvexIndep`). -/
theorem convexIndep_of_isCapSet {P : ℕ → ℝ²} (hmono : IsXMonotone P) {C : Finset ℕ}
    (hcap : IsCapSet P C) : ConvexIndep (P '' (C : Set ℕ)) := by
  apply convexIndep_of_pointwise_strict_sep
  rintro x ⟨v, hvC_coe, rfl⟩
  have hvC : v ∈ C := hvC_coe
  let L := C.filter (fun z => z < v)
  let R := C.filter (fun z => v < z)
  by_cases hL : L.Nonempty
  · by_cases hR : R.Nonempty
    · let l := L.max' hL
      let r := R.min' hR
      have hlL : l ∈ L := Finset.max'_mem L hL
      have hrR : r ∈ R := Finset.min'_mem R hR
      have hlC : l ∈ C := (Finset.mem_filter.mp hlL).1
      have hlv : l < v := (Finset.mem_filter.mp hlL).2
      have hrC : r ∈ C := (Finset.mem_filter.mp hrR).1
      have hvr : v < r := (Finset.mem_filter.mp hrR).2
      have hgap : ∀ z ∈ C, z ≠ v → z ≤ l ∨ r ≤ z := by
        intro z hzC hzv
        rcases lt_or_gt_of_ne hzv with hlt | hgt
        · left
          exact Finset.le_max' L z (Finset.mem_filter.mpr ⟨hzC, hlt⟩)
        · right
          exact Finset.min'_le R z (Finset.mem_filter.mpr ⟨hzC, hgt⟩)
      obtain ⟨h_le, h_pos⟩ := isCapSet_skipped_chord_sep hcap hlC hvC hrC hlv hvr hgap
      refine ⟨lineNormX (P l) (P r), lineNormY (P l) (P r), lineConst (P l) (P r), ?_, ?_⟩
      · rintro y ⟨⟨z, hzC_coe, rfl⟩, hy_ne⟩
        have hzv : z ≠ v := fun h => hy_ne (congrArg P h)
        have h_side := h_le z hzC_coe hzv
        rw [lineSide_affine_decomp]
        linarith
      · rw [lineSide_affine_decomp]
        linarith
    · let l := L.max' hL
      have hlL : l ∈ L := Finset.max'_mem L hL
      have hlv : l < v := (Finset.mem_filter.mp hlL).2
      have hxlv : P l 0 < P v 0 := hmono hlv
      refine ⟨1, 0, P l 0, ?_, by linarith⟩
      rintro y ⟨⟨z, hzC_coe, rfl⟩, hy_ne⟩
      have hzv : z ≠ v := fun h => hy_ne (congrArg P h)
      rcases lt_or_gt_of_ne hzv with hlt | hgt
      · have hzl : z ≤ l := Finset.le_max' L z (Finset.mem_filter.mpr ⟨hzC_coe, hlt⟩)
        have hxz : P z 0 ≤ P l 0 := hmono.monotone hzl
        linarith
      · exfalso
        exact hR ⟨z, Finset.mem_filter.mpr ⟨hzC_coe, hgt⟩⟩
  · by_cases hR : R.Nonempty
    · let r := R.min' hR
      have hrR : r ∈ R := Finset.min'_mem R hR
      have hvr : v < r := (Finset.mem_filter.mp hrR).2
      have hxvr : P v 0 < P r 0 := hmono hvr
      refine ⟨-1, 0, -P r 0, ?_, by linarith⟩
      rintro y ⟨⟨z, hzC_coe, rfl⟩, hy_ne⟩
      have hzv : z ≠ v := fun h => hy_ne (congrArg P h)
      rcases lt_or_gt_of_ne hzv with hlt | hgt
      · exfalso
        exact hL ⟨z, Finset.mem_filter.mpr ⟨hzC_coe, hlt⟩⟩
      · have hrz : r ≤ z := Finset.min'_le R z (Finset.mem_filter.mpr ⟨hzC_coe, hgt⟩)
        have hxz : P r 0 ≤ P z 0 := hmono.monotone hrz
        linarith
    · refine ⟨0, 0, -1, ?_, by linarith⟩
      rintro y ⟨⟨z, hzC_coe, rfl⟩, hy_ne⟩
      have hzv : z ≠ v := fun h => hy_ne (congrArg P h)
      rcases lt_or_gt_of_ne hzv with hlt | hgt
      · exfalso
        exact hL ⟨z, Finset.mem_filter.mpr ⟨hzC_coe, hlt⟩⟩
      · exfalso
        exact hR ⟨z, Finset.mem_filter.mpr ⟨hzC_coe, hgt⟩⟩

/-- Every $(m + 2)$-cup chain in $S$ ending at $(a, b)$ extracts an $(m + 2)$-element subset
$C \subseteq S$ with maximum $b$, second-largest element $a$, and `IsCupSet P C`. -/
theorem cupChainEnding_exists_isCupSet {P : ℕ → ℝ²} (hmono : IsXMonotone P) {S : Finset ℕ} :
    ∀ {m a b : ℕ}, CupChainEnding P S m a b →
      ∃ C : Finset ℕ, C ⊆ S ∧ C.card = m + 2 ∧ a ∈ C ∧ b ∈ C ∧
        (∀ x ∈ C, x ≤ b) ∧ (∀ x ∈ C, x < b → x ≤ a) ∧ IsCupSet P C
  | 0, a, b, ⟨ha, hb, hab⟩ => by
      refine ⟨{a, b}, ?_, ?_, by simp, by simp, ?_, ?_, isCupSet_pair P a b⟩
      · intro x hx
        simp only [Finset.mem_insert, Finset.mem_singleton] at hx
        rcases hx with rfl | rfl <;> assumption
      · have hne : a ≠ b := ne_of_lt hab
        simp [hne]
      · intro x hx
        simp only [Finset.mem_insert, Finset.mem_singleton] at hx
        rcases hx with rfl | rfl <;> omega
      · intro x hx hxb
        simp only [Finset.mem_insert, Finset.mem_singleton] at hx
        rcases hx with rfl | rfl <;> omega
  | _ + 1, b, c, ⟨_, hc, hbc, a, hcup, hsl⟩ => by
      obtain ⟨C₀, hC₀sub, hC₀card, haC₀, hbC₀, hC₀le_b, hC₀le_a, hC₀cup⟩ :=
        cupChainEnding_exists_isCupSet hmono hcup
      have hab : a < b := cupChainEnding_lt hcup
      have hc_not_mem : c ∉ C₀ := fun hcC₀ => by
        have := hC₀le_b c hcC₀
        omega
      refine ⟨insert c C₀, ?_, ?_, by simp [hbC₀], by simp, ?_, ?_,
        isCupSet_insert_right hmono haC₀ hbC₀ hab hbc hC₀le_b hC₀le_a hC₀cup hsl⟩
      · exact Finset.insert_subset_iff.mpr ⟨hc, hC₀sub⟩
      · rw [Finset.card_insert_of_notMem hc_not_mem, hC₀card]
      · intro x hx
        rcases Finset.mem_insert.mp hx with rfl | hx₀
        · exact le_rfl
        · exact le_trans (hC₀le_b x hx₀) (le_of_lt hbc)
      · intro x hx hxc
        rcases Finset.mem_insert.mp hx with rfl | hx₀
        · omega
        · exact hC₀le_b x hx₀

/-- Every $(k + 2)$-cap chain in $S$ starting at $(b, c)$ extracts a $(k + 2)$-element subset
$C \subseteq S$ with minimum $b$, second-smallest element $c$, and `IsCapSet P C`. -/
theorem capChainStarting_exists_isCapSet {P : ℕ → ℝ²} (hmono : IsXMonotone P) {S : Finset ℕ} :
    ∀ {k b c : ℕ}, CapChainStarting P S k b c →
      ∃ C : Finset ℕ, C ⊆ S ∧ C.card = k + 2 ∧ b ∈ C ∧ c ∈ C ∧
        (∀ x ∈ C, b ≤ x) ∧ (∀ x ∈ C, b < x → c ≤ x) ∧ IsCapSet P C
  | 0, b, c, ⟨hb, hc, hbc⟩ => by
      refine ⟨{b, c}, ?_, ?_, by simp, by simp, ?_, ?_, isCapSet_pair P b c⟩
      · intro x hx
        simp only [Finset.mem_insert, Finset.mem_singleton] at hx
        rcases hx with rfl | rfl <;> assumption
      · have hne : b ≠ c := ne_of_lt hbc
        simp [hne]
      · intro x hx
        simp only [Finset.mem_insert, Finset.mem_singleton] at hx
        rcases hx with rfl | rfl <;> omega
      · intro x hx hbx
        simp only [Finset.mem_insert, Finset.mem_singleton] at hx
        rcases hx with rfl | rfl <;> omega
  | _ + 1, a, b, ⟨ha, _, hab, c, hsg, hcap⟩ => by
      obtain ⟨C₀, hC₀sub, hC₀card, hbC₀, hcC₀, hC₀ge_b, hC₀ge_c, hC₀cap⟩ :=
        capChainStarting_exists_isCapSet hmono hcap
      have hbc : b < c := capChainStarting_lt hcap
      have ha_not_mem : a ∉ C₀ := fun haC₀ => by
        have := hC₀ge_b a haC₀
        omega
      refine ⟨insert a C₀, ?_, ?_, by simp, by simp [hbC₀], ?_, ?_,
        isCapSet_insert_left hmono hbC₀ hcC₀ hab hbc hC₀ge_b hC₀ge_c hC₀cap hsg⟩
      · exact Finset.insert_subset_iff.mpr ⟨ha, hC₀sub⟩
      · rw [Finset.card_insert_of_notMem ha_not_mem, hC₀card]
      · intro x hx
        rcases Finset.mem_insert.mp hx with rfl | hx₀
        · exact le_rfl
        · exact le_trans (le_of_lt hab) (hC₀ge_b x hx₀)
      · intro x hx hax
        rcases Finset.mem_insert.mp hx with rfl | hx₀
        · omega
        · exact hC₀ge_b x hx₀

/-- Any $x$-monotone sequence $P : \mathbb{N} \to \mathbb{R}^2$ is injective. -/
theorem xMonotone_injective {P : ℕ → ℝ²} (hmono : IsXMonotone P) :
    Function.Injective P := by
  intro i j hij
  have h0 : P i 0 = P j 0 := congrArg (fun w : ℝ² => w 0) hij
  rcases lt_trichotomy i j with hlt | rfl | hgt
  · have := hmono hlt; linarith
  · rfl
  · have := hmono hgt; linarith

/-- **Inductive $(m + 2)$-Cup Convex Polygon Forcing Theorem**:
For every $m \in \mathbb{N}$, any $x$-monotone sequence $P$ on $S$ satisfying `HasCup P S m`
contains a convex $(m + 2)$-gon in $P(S)$. -/
theorem hasConvexNGon_of_hasCup {P : ℕ → ℝ²} {S : Finset ℕ} {m : ℕ}
    (hmono : IsXMonotone P) (hcup : HasCup P S m) :
    HasConvexNGon (m + 2) (P '' (S : Set ℕ)) := by
  rcases hcup with ⟨a, b, hab⟩
  obtain ⟨C, hCS, hCcard, _, _, _, _, hCcup⟩ := cupChainEnding_exists_isCupSet hmono hab
  refine ⟨C.image P, ?_, ?_, ?_⟩
  · rw [Finset.card_image_of_injective C (xMonotone_injective hmono), hCcard]
  · rw [Finset.coe_image]
    exact Set.image_mono (Finset.coe_subset.mpr hCS)
  · rw [Finset.coe_image]
    exact convexIndep_of_isCupSet hmono hCcup

/-- **Inductive $(k + 2)$-Cap Convex Polygon Forcing Theorem**:
For every $k \in \mathbb{N}$, any $x$-monotone sequence $P$ on $S$ satisfying `HasCap P S k`
contains a convex $(k + 2)$-gon in $P(S)$. -/
theorem hasConvexNGon_of_hasCap {P : ℕ → ℝ²} {S : Finset ℕ} {k : ℕ}
    (hmono : IsXMonotone P) (hcap : HasCap P S k) :
    HasConvexNGon (k + 2) (P '' (S : Set ℕ)) := by
  rcases hcap with ⟨b, c, hbc⟩
  obtain ⟨C, hCS, hCcard, _, _, _, _, hCcap⟩ := capChainStarting_exists_isCapSet hmono hbc
  refine ⟨C.image P, ?_, ?_, ?_⟩
  · rw [Finset.card_image_of_injective C (xMonotone_injective hmono), hCcard]
  · rw [Finset.coe_image]
    exact Set.image_mono (Finset.coe_subset.mpr hCS)
  · rw [Finset.coe_image]
    exact convexIndep_of_isCapSet hmono hCcap

/-- **Universal Inductive $k$-Cup / $k$-Cap Convex $k$-Gon Forcing Theorem**:
For every $k \ge 2$ (and in particular every $k \ge 3$), if an $x$-monotone sequence $P$ on $S$
satisfies `HasCup P S (k - 2) ∨ HasCap P S (k - 2)`, then $P(S)$ contains the vertices of a convex $k$-gon. -/
theorem hasConvexNGon_of_hasCup_or_hasCap {P : ℕ → ℝ²} {S : Finset ℕ} {k : ℕ}
    (hmono : IsXMonotone P) (hk : 2 ≤ k)
    (h : HasCup P S (k - 2) ∨ HasCap P S (k - 2)) :
    HasConvexNGon k (P '' (S : Set ℕ)) := by
  have hk_eq : k - 2 + 2 = k := Nat.sub_add_cancel hk
  rcases h with hcup | hcap
  · rw [← hk_eq]
    exact hasConvexNGon_of_hasCup hmono hcup
  · rw [← hk_eq]
    exact hasConvexNGon_of_hasCap hmono hcap

/-! ## §8 THE GENERAL-POSITION $x$-COORDINATE SORTING BRIDGE
(port of XMonotonePerturbation107.lean §2) -/

/-- Inverse lookup of a point in $T$ by its $x$-coordinate, defaulting to $(x, 0)$ outside the $x$-projection of $T$. -/
def pointOfX (T : Finset ℝ²) (x : ℝ) : ℝ² :=
  if hx : x ∈ T.image (fun p : ℝ² => p 0) then
    Classical.choose (Finset.mem_image.mp hx)
  else
    mkPt x 0

@[simp]
theorem pointOfX_zero (T : Finset ℝ²) (x : ℝ) : pointOfX T x 0 = x := by
  dsimp [pointOfX]
  split_ifs with hx
  · exact (Classical.choose_spec (Finset.mem_image.mp hx)).2
  · simp

theorem pointOfX_mem (T : Finset ℝ²) {x : ℝ} (hx : x ∈ T.image (fun p : ℝ² => p 0)) :
    pointOfX T x ∈ T := by
  dsimp [pointOfX]
  rw [dif_pos hx]
  exact (Classical.choose_spec (Finset.mem_image.mp hx)).1

theorem pointOfX_self {T : Finset ℝ²} (hinj : Set.InjOn (fun p : ℝ² => p 0) (T : Set ℝ²))
    {p : ℝ²} (hp : p ∈ T) : pointOfX T (p 0) = p := by
  have hx : p 0 ∈ T.image (fun q : ℝ² => q 0) := Finset.mem_image_of_mem _ hp
  exact hinj (pointOfX_mem T hx) hp (pointOfX_zero T (p 0))

/-- Strictly increasing $x$-coordinate sequence enumerating `T.image (· 0)` via `Finset.orderEmbOfFin`
on $0 \dots |X| - 1$ and extending linearly for $i \ge |X|$. -/
def xSortedX (T : Finset ℝ²) (i : ℕ) : ℝ :=
  let X := T.image (fun p : ℝ² => p 0)
  if hi : i < X.card then
    X.orderEmbOfFin rfl ⟨i, hi⟩
  else
    (if hX : X.Nonempty then X.max' hX else 0) + ((i - X.card + 1 : ℕ) : ℝ)

/-- Canonical $x$-sorted point sequence `xSortedSeq T : ℕ → ℝ²` associated to a finite point set $T$. -/
def xSortedSeq (T : Finset ℝ²) (i : ℕ) : ℝ² :=
  pointOfX T (xSortedX T i)

/-- For every finite point set $T \subseteq \mathbb{R}^2$, `xSortedSeq T` is globally $x$-monotone (`IsXMonotone`). -/
theorem isXMonotone_xSortedSeq (T : Finset ℝ²) : IsXMonotone (xSortedSeq T) := by
  intro i j hij
  simp only [xSortedSeq, pointOfX_zero, xSortedX]
  let X := T.image (fun p : ℝ² => p 0)
  by_cases hj : j < X.card
  · have hi : i < X.card := lt_trans hij hj
    rw [dif_pos hi, dif_pos hj]
    exact (X.orderEmbOfFin rfl).strictMono (Fin.mk_lt_mk.mpr hij)
  · rw [dif_neg hj]
    by_cases hi : i < X.card
    · rw [dif_pos hi]
      have hmem : X.orderEmbOfFin rfl ⟨i, hi⟩ ∈ X := Finset.orderEmbOfFin_mem X rfl ⟨i, hi⟩
      have hX : X.Nonempty := ⟨_, hmem⟩
      rw [dif_pos hX]
      have hle : X.orderEmbOfFin rfl ⟨i, hi⟩ ≤ X.max' hX := Finset.le_max' X _ hmem
      have hpos : (0 : ℝ) < ((j - X.card + 1 : ℕ) : ℝ) := by exact_mod_cast Nat.succ_pos _
      linarith
    · rw [dif_neg hi]
      have hlt_nat : i - X.card + 1 < j - X.card + 1 := by omega
      have hlt_real : ((i - X.card + 1 : ℕ) : ℝ) < ((j - X.card + 1 : ℕ) : ℝ) := by
        exact_mod_cast hlt_nat
      linarith

/-- **Exact Range Identification for $x$-Injective Finite Point Sets**:
Whenever $T$ has distinct $x$-coordinates, `xSortedSeq T` maps `Finset.range T.card` onto $T$. -/
theorem image_xSortedSeq_range {T : Finset ℝ²}
    (hinj : Set.InjOn (fun p : ℝ² => p 0) (T : Set ℝ²)) :
    xSortedSeq T '' ((Finset.range T.card : Finset ℕ) : Set ℕ) = (T : Set ℝ²) := by
  let X := T.image (fun p : ℝ² => p 0)
  have hXcard : X.card = T.card := Finset.card_image_of_injOn hinj
  ext p
  simp only [Set.mem_image, Finset.mem_coe, Finset.mem_range]
  constructor
  · rintro ⟨i, hi, rfl⟩
    have hiX : i < X.card := by omega
    have hxmem : xSortedX T i ∈ X := by
      dsimp [xSortedX]
      rw [dif_pos hiX]
      exact Finset.orderEmbOfFin_mem X rfl ⟨i, hiX⟩
    exact pointOfX_mem T hxmem
  · intro hp
    have hpX : p 0 ∈ (X : Set ℝ) := Finset.mem_coe.mpr (Finset.mem_image_of_mem _ hp)
    rw [← Finset.range_orderEmbOfFin X rfl] at hpX
    rcases hpX with ⟨⟨i, hiX⟩, hi_eq⟩
    refine ⟨i, by omega, ?_⟩
    dsimp [xSortedSeq, xSortedX]
    rw [dif_pos hiX, hi_eq]
    exact pointOfX_self hinj hp

/-- If $T \subseteq \mathbb{R}^2$ is `NonTrilinear` and has distinct $x$-coordinates, then `xSortedSeq T`
satisfies `IsSeqNonTrilinearOn` on `Finset.range T.card`. -/
theorem isSeqNonTrilinearOn_xSortedSeq {T : Finset ℝ²}
    (hinj : Set.InjOn (fun p : ℝ² => p 0) (T : Set ℝ²))
    (hnt : NonTrilinear (T : Set ℝ²)) :
    IsSeqNonTrilinearOn (xSortedSeq T) (Finset.range T.card) := by
  intro i j k hi hj hk hij hjk
  have hmono := isXMonotone_xSortedSeq T
  have himg := image_xSortedSeq_range hinj
  have hiT : xSortedSeq T i ∈ (T : Set ℝ²) := by
    rw [← himg]; exact ⟨i, hi, rfl⟩
  have hjT : xSortedSeq T j ∈ (T : Set ℝ²) := by
    rw [← himg]; exact ⟨j, hj, rfl⟩
  have hkT : xSortedSeq T k ∈ (T : Set ℝ²) := by
    rw [← himg]; exact ⟨k, hk, rfl⟩
  exact hnt hiT hjT hkT
    (xMonotone_ne_of_lt hmono hij)
    (xMonotone_ne_of_lt hmono hjk)
    (xMonotone_ne_of_lt hmono (lt_trans hij hjk))

/-- Any $x$-injective `NonTrilinear` finite point set $T \subseteq \mathbb{R}^2$ of size at least
`erdosSzekeresUpper k` ($k \ge 2$) contains a convex $k$-gon. -/
theorem hasConvexNGon_of_x_injOn_and_nonTrilinear {T : Finset ℝ²} {k : ℕ}
    (hk : 2 ≤ k) (hinj : Set.InjOn (fun p : ℝ² => p 0) (T : Set ℝ²))
    (hnt : NonTrilinear (T : Set ℝ²)) (hcard : erdosSzekeresUpper k ≤ T.card) :
    HasConvexNGon k (T : Set ℝ²) := by
  have hmono := isXMonotone_xSortedSeq T
  have hnt_seq := isSeqNonTrilinearOn_xSortedSeq hinj hnt
  have hcard_range : (Finset.range T.card).card = T.card := Finset.card_range T.card
  have hbound : ((k - 2) + (k - 2)).choose (k - 2) + 1 ≤ (Finset.range T.card).card := by
    have hsum : (k - 2) + (k - 2) = 2 * k - 4 := by omega
    rw [hsum, hcard_range]
    exact hcard
  have hcupcap := erdos_szekeres_cup_cap_theorem_on hmono (k - 2) (k - 2)
    (Finset.range T.card) hnt_seq hbound
  have hngon := hasConvexNGon_of_hasCup_or_hasCap hmono hk hcupcap
  rwa [image_xSortedSeq_range hinj] at hngon

/-! ## §9 HORIZONTAL SHEAR: FROM GENERAL POSITION TO DISTINCT $x$-COORDINATES
(port of XMonotonePerturbation107.lean §1) -/

/-- Horizontal shear transformation $T_m(x, y) = (x + m y, y)$ on $\mathbb{R}^2$. -/
def shearPt (m : ℝ) (p : ℝ²) : ℝ² :=
  mkPt (p 0 + m * p 1) (p 1)

@[simp]
theorem shearPt_zero (m : ℝ) (p : ℝ²) : shearPt m p 0 = p 0 + m * p 1 := by
  simp [shearPt]

@[simp]
theorem shearPt_one (m : ℝ) (p : ℝ²) : shearPt m p 1 = p 1 := by
  simp [shearPt]

/-- Horizontal shear with slope $-m$ is the exact two-sided inverse of `shearPt m`. -/
theorem shearPt_neg_cancel (m : ℝ) (p : ℝ²) : shearPt (-m) (shearPt m p) = p := by
  ext i; fin_cases i
  · simp [shearPt]
  · simp [shearPt]

/-- Every horizontal shear transformation `shearPt m` is injective on $\mathbb{R}^2$. -/
theorem shearPt_injective (m : ℝ) : Function.Injective (shearPt m) := by
  intro p q hpq
  have h := congrArg (shearPt (-m)) hpq
  simpa [shearPt_neg_cancel] using h

/-- **Exact Oriented Area Invariance Under Horizontal Shear**:
For every $m \in \mathbb{R}$ and $p, q, r \in \mathbb{R}^2$, `shearPt m` preserves `lineSide` identically. -/
theorem lineSide_shearPt (m : ℝ) (p q r : ℝ²) :
    lineSide (shearPt m p) (shearPt m q) (shearPt m r) = lineSide p q r := by
  dsimp [lineSide, shearPt]
  simp only [mkPt_zero, mkPt_one]
  ring

/-- Collinearity of any triple in $\mathbb{R}^2$ is invariant under `shearPt m`. -/
theorem collinear_shearPt_iff (m : ℝ) (p q r : ℝ²) :
    Collinear ℝ ({shearPt m p, shearPt m q, shearPt m r} : Set ℝ²) ↔
      Collinear ℝ ({p, q, r} : Set ℝ²) := by
  constructor
  · intro h
    apply collinear_of_lineSide_eq_zero
    rw [← lineSide_shearPt m]
    exact cross_eq_zero_of_collinear h
  · intro h
    apply collinear_of_lineSide_eq_zero
    rw [lineSide_shearPt m]
    exact cross_eq_zero_of_collinear h

/-- General position (`NonTrilinear`) of any planar point set is preserved under `shearPt m`. -/
theorem nonTrilinear_image_shearPt {A : Set ℝ²} (m : ℝ) (hA : NonTrilinear A) :
    NonTrilinear (shearPt m '' A) := by
  rw [nonTrilinear_iff] at hA ⊢
  rintro _ ⟨x, hx, rfl⟩ _ ⟨y, hy, rfl⟩ _ ⟨z, hz, rfl⟩ hxy hyz hxz
  rw [collinear_shearPt_iff]
  exact hA hx hy hz (fun h => hxy (congrArg (shearPt m) h))
    (fun h => hyz (congrArg (shearPt m) h)) (fun h => hxz (congrArg (shearPt m) h))

/-- Linear map packaging of `shearPt m`. -/
def shearLinearMap (m : ℝ) : ℝ² →ₗ[ℝ] ℝ² where
  toFun := shearPt m
  map_add' p q := by
    ext i; fin_cases i
    · simp [shearPt]; ring
    · simp [shearPt]
  map_smul' c p := by
    ext i; fin_cases i
    · simp [shearPt]; ring
    · simp [shearPt]

/-- Horizontal shear commutes with `convexHull ℝ`. -/
theorem image_shearPt_convexHull (m : ℝ) (s : Set ℝ²) :
    shearPt m '' convexHull ℝ s = convexHull ℝ (shearPt m '' s) :=
  LinearMap.image_convexHull (shearLinearMap m) s

/-- Convex independence (`ConvexIndep`) is preserved under `shearPt m`. -/
theorem convexIndep_image_shearPt {S : Set ℝ²} (m : ℝ) (hS : ConvexIndep S) :
    ConvexIndep (shearPt m '' S) := by
  rintro _ ⟨a, ha, rfl⟩ hmem
  have hdiff : (shearPt m '' S) \ {shearPt m a} = shearPt m '' (S \ {a}) :=
    (Set.image_diff (shearPt_injective m) S {a}).symm ▸ by simp
  rw [hdiff, ← image_shearPt_convexHull] at hmem
  rcases hmem with ⟨b, hb, hba⟩
  have hab : b = a := shearPt_injective m hba
  subst hab
  exact hS b ha hb

/-- Existence of a convex $n$-gon (`HasConvexNGon n`) is invariant under `shearPt m`. -/
theorem hasConvexNGon_image_shearPt_iff (m : ℝ) (n : ℕ) (A : Set ℝ²) :
    HasConvexNGon n (shearPt m '' A) ↔ HasConvexNGon n A := by
  constructor
  · rintro ⟨T, hTcard, hTsub, hTconv⟩
    refine ⟨T.image (shearPt (-m)), ?_, ?_, ?_⟩
    · rw [Finset.card_image_of_injective _ (shearPt_injective (-m)), hTcard]
    · intro x hx
      rw [Finset.coe_image] at hx
      rcases hx with ⟨y, hy, rfl⟩
      rcases hTsub hy with ⟨z, hz, rfl⟩
      simpa [shearPt_neg_cancel] using hz
    · rw [Finset.coe_image]
      exact convexIndep_image_shearPt (-m) hTconv
  · rintro ⟨S, hScard, hSsub, hSconv⟩
    refine ⟨S.image (shearPt m), ?_, ?_, ?_⟩
    · rw [Finset.card_image_of_injective _ (shearPt_injective m), hScard]
    · rw [Finset.coe_image]
      exact Set.image_mono hSsub
    · rw [Finset.coe_image]
      exact convexIndep_image_shearPt m hSconv

/-- Explicit real selector avoiding any finite set $B \subseteq \mathbb{R}$. -/
def avoidFinsetReal (B : Finset ℝ) : ℝ :=
  if h : B.Nonempty then B.max' h + 1 else 0

theorem avoidFinsetReal_not_mem (B : Finset ℝ) : avoidFinsetReal B ∉ B := by
  dsimp [avoidFinsetReal]
  split_ifs with h
  · intro hmem
    have hle := Finset.le_max' B (B.max' h + 1) hmem
    linarith
  · intro hmem
    exact h ⟨0, hmem⟩

/-- The finite set of forbidden shear slopes $(q_0 - p_0)/(p_1 - q_1)$ for pairs $(p, q) \in \text{pts}^2$. -/
def forbiddenShearSlopes (pts : Finset ℝ²) : Finset ℝ :=
  (pts ×ˢ pts).image (fun pq => (pq.2 0 - pq.1 0) / (pq.1 1 - pq.2 1))

/-- Canonical shear slope avoiding all forbidden slopes of `pts`. -/
def goodShearSlope (pts : Finset ℝ²) : ℝ :=
  avoidFinsetReal (forbiddenShearSlopes pts)

/-- **Universal Finite-Point-Set $x$-Coordinate Perturbation Lemma**:
For every finite point set `pts : Finset ℝ²`, the sheared point set under `goodShearSlope pts`
has strictly distinct $x$-coordinates (`Set.InjOn (fun p => shearPt (goodShearSlope pts) p 0) pts`). -/
theorem shearPt_x_injOn_goodShearSlope (pts : Finset ℝ²) :
    Set.InjOn (fun p => shearPt (goodShearSlope pts) p 0) (pts : Set ℝ²) := by
  intro p hp q hq heq
  simp only [shearPt_zero] at heq
  by_cases hpq1 : p 1 = q 1
  · have hpq0 : p 0 = q 0 := by rw [hpq1] at heq; linarith
    ext i; fin_cases i
    · exact hpq0
    · exact hpq1
  · exfalso
    have hsub : p 1 - q 1 ≠ 0 := sub_ne_zero.mpr hpq1
    have hm : goodShearSlope pts = (q 0 - p 0) / (p 1 - q 1) := by
      rw [eq_div_iff hsub]
      linarith
    have hmem : goodShearSlope pts ∈ forbiddenShearSlopes pts := by
      rw [hm]
      exact Finset.mem_image.mpr ⟨(p, q), Finset.mem_product.mpr ⟨hp, hq⟩, rfl⟩
    exact avoidFinsetReal_not_mem (forbiddenShearSlopes pts) hmem

/-! ## §10 SMALL CONVEX-INDEPENDENCE BASE CASES
(port of Erdos107Unified435.lean §2; `convexIndep_triple_of_not_collinear` is byte-identical
to the verbatim anchor in DM107_Official.lean, which certifies the vendored definitions) -/

/-- Every point set of cardinality at most $2$ is convex independent. -/
theorem convexIndep_of_card_le_two {S : Finset ℝ²} (hcard : S.card ≤ 2) :
    ConvexIndep (S : Set ℝ²) := by
  intro x hx hmem
  have hsub : ((S : Set ℝ²) \ {x}) = ((S.erase x : Finset ℝ²) : Set ℝ²) := by
    ext y
    simp [Finset.mem_erase, and_comm]
  rw [hsub] at hmem
  have herase : (S.erase x).card ≤ 1 := by
    have hxS : x ∈ S := Finset.mem_coe.mp hx
    have := Finset.card_erase_of_mem hxS
    omega
  rcases Nat.le_one_iff_eq_zero_or_eq_one.mp herase with h0 | h1
  · rw [Finset.card_eq_zero.mp h0] at hmem
    simp at hmem
  · obtain ⟨y, hy⟩ := Finset.card_eq_one.mp h1
    have hy_ne : x ≠ y := by
      intro hxy
      subst hxy
      have hmem_erase : x ∈ S.erase x := hy ▸ Finset.mem_singleton_self x
      simp at hmem_erase
    rw [hy] at hmem
    simp [convexHull_singleton] at hmem
    exact hy_ne hmem

/-- Three distinct non-collinear points in $\mathbb{R}^2$ form a convex-independent set. -/
theorem convexIndep_triple_of_not_collinear {a b c : ℝ²}
    (hab : a ≠ b) (hac : a ≠ c) (hbc : b ≠ c)
    (hcoll : ¬ Collinear ℝ ({a, b, c} : Set ℝ²)) :
    ConvexIndep ({a, b, c} : Set ℝ²) := by
  intro x hx hmem
  apply hcoll
  have hx_aff : x ∈ affineSpan ℝ (({a, b, c} : Set ℝ²) \ {x}) :=
    convexHull_subset_affineSpan _ hmem
  rw [show ({a, b, c} : Set ℝ²) = insert x (({a, b, c} : Set ℝ²) \ {x}) from
        (Set.insert_sdiff_self_of_mem hx).symm,
      collinear_insert_iff_of_mem_affineSpan hx_aff]
  simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hx
  rcases hx with rfl | rfl | rfl
  · rw [show ({x, b, c} : Set ℝ²) \ {x} = ({b, c} : Set ℝ²) by ext; aesop]
    exact collinear_pair ℝ b c
  · rw [show ({a, x, c} : Set ℝ²) \ {x} = ({a, c} : Set ℝ²) by ext; aesop]
    exact collinear_pair ℝ a c
  · rw [show ({a, b, x} : Set ℝ²) \ {x} = ({a, b} : Set ℝ²) by ext; aesop]
    exact collinear_pair ℝ a b

/-- For $n \le 3$, $n \in \text{cardSet}(n)$. -/
theorem self_mem_cardSet_of_le_three {n : ℕ} (hn : n ≤ 3) : n ∈ cardSet n := by
  intro pts hpts hnontri
  rcases le_or_gt n 2 with hn2 | hn3
  · exact ⟨pts, hpts, subset_refl _, convexIndep_of_card_le_two (hpts ▸ hn2)⟩
  · have hn_eq : n = 3 := by omega
    subst hn_eq
    obtain ⟨a, b, c, hab, hac, hbc, rfl⟩ := Finset.card_eq_three.mp hpts
    refine ⟨{a, b, c}, by simp [hab, hac, hbc], subset_refl _, ?_⟩
    have hcoerce : (({a, b, c} : Finset ℝ²) : Set ℝ²) = ({a, b, c} : Set ℝ²) := by simp
    have hmem : ∀ {y : ℝ²}, y ∈ ({a, b, c} : Set ℝ²) →
        y ∈ (({a, b, c} : Finset ℝ²) : Set ℝ²) := fun h => hcoerce ▸ h
    have hnc : ¬ Collinear ℝ ({a, b, c} : Set ℝ²) :=
      hnontri (hmem (by simp)) (hmem (by simp)) (hmem (by simp)) hab hbc hac
    rw [hcoerce]
    exact convexIndep_triple_of_not_collinear hab hac hbc hnc

/-! ## §11 THE UNCONDITIONAL ERDŐS–SZEKERES THEOREM ON $\mathbb{R}^2$
(port of XMonotonePerturbation107.lean §2, `hasConvexNGon_of_nonTrilinear_and_card_ge` +
`erdosSzekeresUpper_mem_cardSet`) -/

/-- **Unconditional General-Position Erdős–Szekeres Convex $k$-Gon Theorem on $\mathbb{R}^2$**:
For every $k \ge 2$, any `NonTrilinear` finite point set `pts : Finset ℝ²` (without any $x$-coordinate
distinctness hypothesis) of cardinality at least `erdosSzekeresUpper k` contains a convex $k$-gon. -/
theorem hasConvexNGon_of_nonTrilinear_and_card_ge {pts : Finset ℝ²} {k : ℕ}
    (hk : 2 ≤ k) (hnt : NonTrilinear (pts : Set ℝ²))
    (hcard : erdosSzekeresUpper k ≤ pts.card) :
    HasConvexNGon k (pts : Set ℝ²) := by
  let m := goodShearSlope pts
  let T := pts.image (shearPt m)
  have hTcoe : (T : Set ℝ²) = shearPt m '' (pts : Set ℝ²) := Finset.coe_image
  have hTcard : T.card = pts.card :=
    Finset.card_image_of_injective _ (shearPt_injective m)
  have hinj : Set.InjOn (fun p : ℝ² => p 0) (T : Set ℝ²) := by
    intro a ha b hb hab
    rw [hTcoe] at ha hb
    rcases ha with ⟨pa, hpa, rfl⟩
    rcases hb with ⟨pb, hpb, rfl⟩
    have hpab : pa = pb := shearPt_x_injOn_goodShearSlope pts hpa hpb hab
    rw [hpab]
  have hntT : NonTrilinear (T : Set ℝ²) := by
    rw [hTcoe]
    exact nonTrilinear_image_shearPt m hnt
  have hTngon : HasConvexNGon k (T : Set ℝ²) :=
    hasConvexNGon_of_x_injOn_and_nonTrilinear hk hinj hntT (hTcard.symm ▸ hcard)
  rw [hTcoe, hasConvexNGon_image_shearPt_iff] at hTngon
  exact hTngon

/-- **Unconditional Membership of `erdosSzekeresUpper k` in `cardSet k`**:
For every $k \ge 2$, $\binom{2k-4}{k-2} + 1 \in \mathrm{cardSet}\,k$. -/
theorem erdosSzekeresUpper_mem_cardSet {k : ℕ} (hk : 2 ≤ k) :
    erdosSzekeresUpper k ∈ cardSet k := by
  intro pts hcard hnt
  exact hasConvexNGon_of_nonTrilinear_and_card_ge hk hnt (le_of_eq hcard.symm)

/-! ## §12 THE MEMBERSHIP-TO-UPPER-BOUND LEMMA + NONEMPTINESS
(the cone tail feeding this kernel: the sInf packaging of the ES 1935 membership
(§12 of DM107_Proof_B.lean) and the all-n nonemptiness with the arsenal trichotomy
(§14 there); the all-n upper-bound headline itself stays banked in lane W82-107B) -/

/-- Membership of the Erdős–Szekeres witness in `cardSet n` bounds `f n` from
above through the infimum (port of Erdos107Unified435.lean L1620–1623). -/
theorem f_le_erdosSzekeresUpper_of_mem_cardSet {n : ℕ}
    (hmem : erdosSzekeresUpper n ∈ cardSet n) :
    f n ≤ erdosSzekeresUpper n :=
  Nat.sInf_le hmem

/-- **Unconditional Erdős–Szekeres 1935 upper bound**: for all $k \ge 2$,
$f(k) \le \binom{2k-4}{k-2} + 1$ (port of XMonotonePerturbation107.lean
L589–591; the cone lemma feeding `ersz_bounds_of_le_five` below). -/
theorem f_le_erdosSzekeresUpper {k : ℕ} (hk : 2 ≤ k) :
    f k ≤ erdosSzekeresUpper k :=
  f_le_erdosSzekeresUpper_of_mem_cardSet (erdosSzekeresUpper_mem_cardSet hk)

/-- Every `cardSet n` ($n \in \mathbb{N}$) is unconditionally nonempty. The $n < 3$ base case
splits through the arsenal law `ErdosTernary2.lt_three_cases`
(Arsenal/ErdosTernary2/Basic.lean:16); the $n \ge 3$ case uses the Erdős–Szekeres
cup–cap witness `erdosSzekeresUpper n`. -/
theorem nonempty_cardSet_all (n : ℕ) : (cardSet n).Nonempty := by
  rcases lt_or_ge n 3 with hn | hn
  · rcases ErdosTernary2.lt_three_cases n hn with rfl | rfl | rfl
    · exact ⟨0, self_mem_cardSet_of_le_three (by decide)⟩
    · exact ⟨1, self_mem_cardSet_of_le_three (by decide)⟩
    · exact ⟨2, self_mem_cardSet_of_le_three (by decide)⟩
  · exact ⟨erdosSzekeresUpper n, erdosSzekeresUpper_mem_cardSet (by omega)⟩

/-! ## §D1 HEREDITY: subsets, monotonicity, upward closure of `cardSet`
(port of Erdos107Unified435.lean §0, `nonTrilinear_mono` L49,
`hasConvexNGon_mono_pts` L207, `cardSet_upward_closed` L215 — the heredity
laws of the plan: (a) any subset of a NonTrilinear set is NonTrilinear, (b)
`HasConvexNGon n` is monotone increasing in the ambient point set, so
`cardSet n` is upward closed in N — one size-2^(n-2) witness kills every
N ≤ 2^(n-2) at once, no per-N subset construction needed). -/

/-- Heredity of `NonTrilinear` under subsets (any subset of a general-position
set is in general position). -/
theorem nonTrilinear_mono {P Q : Set ℝ²} (hPQ : P ⊆ Q) (hQ : NonTrilinear Q) :
    NonTrilinear P :=
  fun _ hx _ hy _ hz hxy hyz hxz => hQ (hPQ hx) (hPQ hy) (hPQ hz) hxy hyz hxz

/-- Containing a convex $n$-gon is monotone increasing in the ambient point set. -/
theorem hasConvexNGon_mono_pts {n : ℕ} {P Q : Set ℝ²}
    (h : HasConvexNGon n P) (hPQ : P ⊆ Q) : HasConvexNGon n Q := by
  rcases h with ⟨S, hcard, hsub, hconv⟩
  exact ⟨S, hcard, hsub.trans hPQ, hconv⟩

/-- **Upward closure of `cardSet n`**: if $N_1 \le N_2$ and $N_1 \in \text{cardSet}(n)$,
then $N_2 \in \text{cardSet}(n)$ (port of Erdos107Unified435.lean L215–221). -/
theorem cardSet_upward_closed {n N₁ N₂ : ℕ}
    (hle : N₁ ≤ N₂) (hN₁ : N₁ ∈ cardSet n) : N₂ ∈ cardSet n := by
  intro pts hcard hnontri
  obtain ⟨pts₁, hsub, hcard₁⟩ := Finset.exists_subset_card_eq (hle.trans_eq hcard.symm)
  have hcoe : (pts₁ : Set ℝ²) ⊆ (pts : Set ℝ²) := Finset.coe_subset.mpr hsub
  have hnontri₁ : NonTrilinear (pts₁ : Set ℝ²) := nonTrilinear_mono hcoe hnontri
  exact hasConvexNGon_mono_pts (hN₁ pts₁ hcard₁ hnontri₁) hcoe

/-! ## §D2 THE n = 3 WITNESS: two distinct points (size 2 = 2^(3-2))
(the plan's base case: a 2-point set is trivially `NonTrilinear` — no three
distinct points exist in it — and has no 3-point subset, so no convex 3-gon) -/

/-- The two points $(0,0)$ and $(1,0)$ are distinct. -/
theorem mkPt00_ne_mkPt10 : (mkPt 0 0 : ℝ²) ≠ mkPt 1 0 := by
  intro h
  have h0 : (mkPt 0 0 : ℝ²) 0 = (mkPt 1 0 : ℝ²) 0 := congrArg (fun w : ℝ² => w 0) h
  simp only [mkPt_zero] at h0
  norm_num at h0

/-- The size-2 witness: any two distinct points. -/
def twoPts : Finset ℝ² := {mkPt 0 0, mkPt 1 0}

theorem twoPts_card : twoPts.card = 2 := by
  simp [twoPts, mkPt00_ne_mkPt10]

/-- A 2-point set is `NonTrilinear`: three pairwise-distinct points cannot be
drawn from a 2-element set (pigeonhole over the eight membership cases). -/
theorem twoPts_nonTrilinear : NonTrilinear (twoPts : Set ℝ²) := by
  intro x hx y hy z hz hxy hyz hxz
  simp only [twoPts, Finset.coe_insert, Finset.coe_singleton,
    Set.mem_insert_iff, Set.mem_singleton_iff] at hx hy hz
  rcases hx with rfl | rfl <;> rcases hy with rfl | rfl <;> rcases hz with rfl | rfl
  all_goals first
    | exact False.elim (hxy rfl)
    | exact False.elim (hyz rfl)
    | exact False.elim (hxz rfl)

/-- The 2-point witness contains no convex 3-gon: no 3-element subset exists. -/
theorem twoPts_not_hasConvexNGon_three : ¬ HasConvexNGon 3 (twoPts : Set ℝ²) := by
  rintro ⟨S, hScard, hSsub, _⟩
  have hcard : S.card ≤ 2 := by
    have hle := Finset.card_le_card (Finset.coe_subset.mp hSsub)
    rwa [twoPts_card] at hle
  omega

/-- $2 \notin \text{cardSet}(3)$: two general-position points need not contain a convex 3-gon. -/
theorem two_not_mem_cardSet_three : (2 : ℕ) ∉ cardSet 3 := by
  intro h
  exact twoPts_not_hasConvexNGon_three (h twoPts twoPts_card twoPts_nonTrilinear)

/-- Any $N \in \text{cardSet}(3)$ satisfies $3 \le N$ (upward closure from the size-2 witness). -/
theorem three_le_of_mem_cardSet_three {N : ℕ} (hN : N ∈ cardSet 3) : 3 ≤ N := by
  by_contra hlt
  have h2 : N ≤ 2 := by omega
  exact two_not_mem_cardSet_three (cardSet_upward_closed h2 hN)

/-- Lower bound $3 \le f(3)$ (i.e. $2^{3-2} + 1 \le f(3)$). -/
theorem three_le_f_three : 3 ≤ f 3 :=
  le_csInf (nonempty_cardSet_all 3) fun _ hN => three_le_of_mem_cardSet_three hN

/-! ## §D3 THE STRICT TRIANGLE-INTERIOR MACHINERY
(port of Blueprint107.lean §1: `InPosTriangle` L87, `lineSide_triangle_sum` L93,
`inPosTriangle_cycle` L120, `inPosTriangle_pos_outer` L127,
`barycentric_of_lineSide_ne_zero` L163, `inPosTriangle_mem_convexHull` L178,
`not_convexIndep_of_inPosTriangle` L223 — the shared geometric core of both
finite witnesses: an interior point of a positively oriented triangle lies in
its convex hull, so a set containing a triangle and an interior point is not
convex independent. The `field_simp` closers are hedged with `<;> ring` /
`<;> linarith` so they are insensitive to whether the v4.33.0-rc2 `field_simp`
normalizer finishes the goal itself or leaves the cleared-denominator
identity). -/

/-- A point $d \in \mathbb{R}^2$ lies in the open interior of the positively oriented
triangle $(a, b, c)$ if it lies on the strictly positive open side of all three directed
edges $a \to b$, $b \to c$, and $c \to a$. -/
def InPosTriangle (a b c d : ℝ²) : Prop :=
  0 < lineSide a b d ∧ 0 < lineSide b c d ∧ 0 < lineSide c a d

/-- **Universal oriented-area triangle-sum identity**: for any four points
$a, b, c, d \in \mathbb{R}^2$, the signed areas of $\triangle abd$, $\triangle bcd$,
and $\triangle cad$ sum identically to the signed area of $\triangle abc$. -/
theorem lineSide_triangle_sum (a b c d : ℝ²) :
    lineSide a b d + lineSide b c d + lineSide c a d = lineSide a b c := by
  dsimp [lineSide]; ring

/-- Cyclic permutation of the outer triangle vertices preserves `InPosTriangle`. -/
theorem inPosTriangle_cycle {a b c d : ℝ²} (h : InPosTriangle a b c d) :
    InPosTriangle b c a d :=
  ⟨h.2.1, h.2.2, h.1⟩

/-- Any triangle $(a, b, c)$ containing a point $d$ with `InPosTriangle a b c d` is
positively oriented. -/
theorem inPosTriangle_pos_outer {a b c d : ℝ²} (h : InPosTriangle a b c d) :
    0 < lineSide a b c := by
  have hsum := lineSide_triangle_sum a b c d
  linarith [h.1, h.2.1, h.2.2]

/-- **Universal Cramer barycentric identity in $\mathbb{R}^2$**: for any non-collinear
triple $(a, b, c)$ with $\operatorname{lineSide}(a,b,c) \ne 0$ and any point $p$, $p$ equals
the affine combination of $a, b, c$ with weights
$\operatorname{lineSide}(b,c,p)/\operatorname{lineSide}(a,b,c)$ etc. -/
theorem barycentric_of_lineSide_ne_zero (a b c p : ℝ²) (h : lineSide a b c ≠ 0) :
    (lineSide b c p / lineSide a b c) • a +
    (lineSide c a p / lineSide a b c) • b +
    (lineSide a b p / lineSide a b c) • c = p := by
  ext i
  fin_cases i <;>
  · simp only [PiLp.add_apply, PiLp.smul_apply, smul_eq_mul]
    field_simp [h]
    dsimp [lineSide]
    ring

/-- **Universal positive-triangle convex-hull membership theorem**: whenever
`InPosTriangle a b c p` holds, $p \in \mathrm{convexHull}\,\mathbb{R}\,\{a, b, c\}$. -/
theorem inPosTriangle_mem_convexHull {a b c p : ℝ²} (h : InPosTriangle a b c p) :
    p ∈ convexHull ℝ ({a, b, c} : Set ℝ²) := by
  have habc : 0 < lineSide a b c := inPosTriangle_pos_outer h
  have habc_ne : lineSide a b c ≠ 0 := ne_of_gt habc
  have hbc : 0 < lineSide b c p := h.2.1
  have hca : 0 < lineSide c a p := h.2.2
  have hab : 0 < lineSide a b p := h.1
  have hbcca : 0 < lineSide b c p + lineSide c a p := by linarith
  have hbcca_ne : lineSide b c p + lineSide c a p ≠ 0 := ne_of_gt hbcca
  have hsum := lineSide_triangle_sum a b c p
  rw [← barycentric_of_lineSide_ne_zero a b c p habc_ne]
  have hdecomp :
      (lineSide b c p / lineSide a b c) • a +
      (lineSide c a p / lineSide a b c) • b +
      (lineSide a b p / lineSide a b c) • c =
      ((lineSide b c p + lineSide c a p) / lineSide a b c) •
        ((lineSide b c p / (lineSide b c p + lineSide c a p)) • a +
         (lineSide c a p / (lineSide b c p + lineSide c a p)) • b) +
      (lineSide a b p / lineSide a b c) • c := by
    ext i
    fin_cases i <;>
    · simp only [PiLp.add_apply, PiLp.smul_apply, smul_eq_mul]
      field_simp [habc_ne, hbcca_ne] <;> ring
  rw [hdecomp]
  have h_conv := convex_convexHull ℝ ({a, b, c} : Set ℝ²)
  have ha_mem : a ∈ convexHull ℝ ({a, b, c} : Set ℝ²) := subset_convexHull ℝ _ (by simp)
  have hb_mem : b ∈ convexHull ℝ ({a, b, c} : Set ℝ²) := subset_convexHull ℝ _ (by simp)
  have hc_mem : c ∈ convexHull ℝ ({a, b, c} : Set ℝ²) := subset_convexHull ℝ _ (by simp)
  have hmid :
      (lineSide b c p / (lineSide b c p + lineSide c a p)) • a +
      (lineSide c a p / (lineSide b c p + lineSide c a p)) • b ∈
        convexHull ℝ ({a, b, c} : Set ℝ²) := by
    apply h_conv ha_mem hb_mem
    · exact div_nonneg (le_of_lt hbc) (le_of_lt hbcca)
    · exact div_nonneg (le_of_lt hca) (le_of_lt hbcca)
    · field_simp [hbcca_ne] <;> ring
  apply h_conv hmid hc_mem
  · exact div_nonneg (le_of_lt hbcca) (le_of_lt habc)
  · exact div_nonneg (le_of_lt hab) (le_of_lt habc)
  · field_simp [habc_ne] <;> linarith

/-- **Universal interior-point non-convexity criterion**: if $a, b, c, p \in S$
satisfy `InPosTriangle a b c p`, then $S$ is not convex independent. -/
theorem not_convexIndep_of_inPosTriangle {S : Set ℝ²} {a b c p : ℝ²}
    (haS : a ∈ S) (hbS : b ∈ S) (hcS : c ∈ S) (hpS : p ∈ S)
    (h : InPosTriangle a b c p) :
    ¬ ConvexIndep S := by
  intro hci
  apply hci p hpS
  have hpa : p ≠ a := by
    intro heq; subst heq
    have h1 := h.1
    rw [lineSide_self_left] at h1
    linarith
  have hpb : p ≠ b := by
    intro heq; subst heq
    have h1 := h.1
    rw [lineSide_self_right] at h1
    linarith
  have hpc : p ≠ c := by
    intro heq; subst heq
    have h1 := h.2.1
    rw [lineSide_self_right] at h1
    linarith
  have hsub : ({a, b, c} : Set ℝ²) ⊆ S \ {p} := by
    intro z hz
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hz
    rcases hz with rfl | rfl | rfl
    · exact ⟨haS, hpa.symm⟩
    · exact ⟨hbS, hpb.symm⟩
    · exact ⟨hcS, hpc.symm⟩
  exact convexHull_mono hsub (inPosTriangle_mem_convexHull h)

/-! ## §D4 THE n = 4 KLEIN WITNESS: triangle + interior point (size 4 = 2^(4-2))
(port of Erdos107Unified435.lean §1: ptO/ptA/ptB/ptC/kleinFourPts L364–377,
the pairwise-distinctness laws L379–419, kleinFourPts_card L421,
not_convexIndep_kleinFourPts L454, kleinFourPts_nonTrilinear L469,
four_not_mem_cardSet_four L487, five_le_of_mem_cardSet_four L500,
five_le_f_four L508. The hull-membership step `ptC_mem_convexHull_triangle`
(upstream L427–451 via a barycentric decomposition) is recast through the
§D3 InPosTriangle machinery: $(1,1)$ is certified strictly inside the outer
triangle by three norm_num oriented-area certificates, all equal to 3 > 0.) -/

/-- Origin vertex $(0, 0)$ of the outer triangle. -/
def ptO : ℝ² := mkPt 0 0

/-- Right vertex $(3, 0)$ of the outer triangle. -/
def ptA : ℝ² := mkPt 3 0

/-- Top vertex $(0, 3)$ of the outer triangle. -/
def ptB : ℝ² := mkPt 0 3

/-- Interior point $(1, 1)$ of the outer triangle. -/
def ptC : ℝ² := mkPt 1 1

/-- The 4-point Esther Klein witness $\{(0,0), (3,0), (0,3), (1,1)\}$ in general position
forming a triangle with an interior point. -/
def kleinFourPts : Finset ℝ² := {ptO, ptA, ptB, ptC}

theorem ptO_ne_ptA : ptO ≠ ptA := by
  intro h
  have h0 := congrArg (fun w : ℝ² => w 0) h
  simp [ptO, ptA] at h0

theorem ptO_ne_ptB : ptO ≠ ptB := by
  intro h
  have h1 := congrArg (fun w : ℝ² => w 1) h
  simp [ptO, ptB] at h1

theorem ptO_ne_ptC : ptO ≠ ptC := by
  intro h
  have h0 := congrArg (fun w : ℝ² => w 0) h
  simp [ptO, ptC] at h0

theorem ptA_ne_ptB : ptA ≠ ptB := by
  intro h
  have h0 := congrArg (fun w : ℝ² => w 0) h
  simp [ptA, ptB] at h0

theorem ptA_ne_ptC : ptA ≠ ptC := by
  intro h
  have h0 := congrArg (fun w : ℝ² => w 0) h
  simp [ptA, ptC] at h0

theorem ptB_ne_ptC : ptB ≠ ptC := by
  intro h
  have h0 := congrArg (fun w : ℝ² => w 0) h
  simp [ptB, ptC] at h0

theorem kleinFourPts_card : kleinFourPts.card = 4 := by
  simp [kleinFourPts, ptO_ne_ptA, ptO_ne_ptB, ptO_ne_ptC, ptA_ne_ptB, ptA_ne_ptC, ptB_ne_ptC]

/-- The interior point $(1,1)$ lies strictly inside the positively oriented outer
triangle $((0,0), (3,0), (0,3))$: all three oriented edge areas equal $3 > 0$
(three norm_num certificates). -/
theorem ptC_inPosTriangle : InPosTriangle ptO ptA ptB ptC :=
  ⟨by simp only [lineSide, ptO, ptA, ptC, mkPt_zero, mkPt_one]; norm_num,
   by simp only [lineSide, ptA, ptB, ptC, mkPt_zero, mkPt_one]; norm_num,
   by simp only [lineSide, ptB, ptO, ptC, mkPt_zero, mkPt_one]; norm_num⟩

/-- The interior point $(1, 1)$ lies in the convex hull of the three outer vertices. -/
theorem ptC_mem_convexHull_triangle :
    ptC ∈ convexHull ℝ ({ptO, ptA, ptB} : Set ℝ²) :=
  inPosTriangle_mem_convexHull ptC_inPosTriangle

/-- The 4-point configuration `kleinFourPts` is not convex independent. -/
theorem not_convexIndep_kleinFourPts :
    ¬ ConvexIndep (kleinFourPts : Set ℝ²) := by
  intro hci
  have hC : ptC ∈ (kleinFourPts : Set ℝ²) := by simp [kleinFourPts]
  refine hci ptC hC (convexHull_mono ?_ ptC_mem_convexHull_triangle)
  intro x hx
  simp only [kleinFourPts, Finset.coe_insert, Finset.coe_singleton,
    Set.mem_insert_iff, Set.mem_singleton_iff] at hx
  rcases hx with rfl | rfl | rfl
  · simp [kleinFourPts, ptO_ne_ptC]
  · simp [kleinFourPts, ptA_ne_ptC]
  · simp [kleinFourPts, ptB_ne_ptC]

/-- No three points of `kleinFourPts` are collinear (four norm_num cross certificates). -/
theorem kleinFourPts_nonTrilinear :
    NonTrilinear (kleinFourPts : Set ℝ²) := by
  intro x hx y hy z hz hxy hyz hxz
  simp only [kleinFourPts, Finset.coe_insert, Finset.coe_singleton,
    Set.mem_insert_iff, Set.mem_singleton_iff] at hx hy hz
  rcases hx with rfl | rfl | rfl | rfl <;>
    rcases hy with rfl | rfl | rfl | rfl <;>
    rcases hz with rfl | rfl | rfl | rfl
  all_goals
    first
    | exact False.elim (hxy rfl)
    | exact False.elim (hyz rfl)
    | exact False.elim (hxz rfl)
    | (apply not_collinear_of_cross_ne_zero;
        norm_num [ptO, ptA, ptB, ptC, mkPt_zero, mkPt_one])

/-- $4 \notin \text{cardSet}(4)$: four points in general position need not form a
convex quadrilateral. -/
theorem four_not_mem_cardSet_four : (4 : ℕ) ∉ cardSet 4 := by
  intro h4
  obtain ⟨S, hScard, hSsub, hSconv⟩ :=
    h4 kleinFourPts kleinFourPts_card kleinFourPts_nonTrilinear
  have hkcard := kleinFourPts_card
  have hSeq : S = kleinFourPts :=
    Finset.eq_of_subset_of_card_le (Finset.coe_subset.mp hSsub) (by omega)
  subst hSeq
  exact not_convexIndep_kleinFourPts hSconv

/-- Any $N \in \text{cardSet}(4)$ satisfies $5 \le N$ (upward closure from the
size-4 Klein witness). -/
theorem five_le_of_mem_cardSet_four {N : ℕ} (hN : N ∈ cardSet 4) : 5 ≤ N := by
  by_contra hlt
  have h4 : N ≤ 4 := by omega
  exact four_not_mem_cardSet_four (cardSet_upward_closed h4 hN)

/-- Lower bound $5 \le f(4)$ (i.e. $2^{4-2} + 1 \le f(4)$). -/
theorem five_le_f_four : 5 ≤ f 4 :=
  le_csInf (nonempty_cardSet_all 4) fun _ hN => five_le_of_mem_cardSet_four hN

/-! ## §D5 THE n = 5 WITNESS: the 8-point Erdős–Szekeres 4-cap ⊕ 4-cup set
(size 8 = 2^(5-2); port of Blueprint107.lean §3: the strict-order triple
extraction L519–554, the witness coordinates L556–573, the exact
`lineSide`/`esEightCross` bridge L576–581, the injectivity/cardinality/
general-position laws L585–631, the two decide-certified cap/cup triangle
containment laws L633–651, the cap/cup pigeonhole split L653–679, the
pentagon-free certificate `not_hasConvexFiveGon_esEightFinset` L681–728,
and the cardSet consequences L730–752. The four `decide` proofs are
kernel-checked over the 8-element index type: 8², 8³ and two 8⁴ passes of
tiny integer cross-product evaluations — the `Decidable (p → q)` core
instance (Init/Core.lean:1157) and `Fintype.decidableForallFintype`
(Mathlib/Data/Fintype/Defs.lean:209) were both verified at the pinned tag
before relying on them). -/

/-- Any finite set $J$ of size at least 3 contains three pairwise distinct elements. -/
theorem exists_three_distinct_of_three_le_card {α : Type*} [DecidableEq α] {J : Finset α}
    (hcard : 3 ≤ J.card) :
    ∃ x y z : α, x ∈ J ∧ y ∈ J ∧ z ∈ J ∧ x ≠ y ∧ y ≠ z ∧ x ≠ z := by
  obtain ⟨x, hxJ⟩ := Finset.card_pos.mp (by omega : 0 < J.card)
  have hcard1 : 2 ≤ (J.erase x).card := by
    rw [Finset.card_erase_of_mem hxJ]; omega
  obtain ⟨y, hyJ1⟩ := Finset.card_pos.mp (by omega : 0 < (J.erase x).card)
  have hcard2 : 1 ≤ ((J.erase x).erase y).card := by
    rw [Finset.card_erase_of_mem hyJ1]; omega
  obtain ⟨z, hzJ2⟩ := Finset.card_pos.mp (by omega : 0 < ((J.erase x).erase y).card)
  obtain ⟨hyx, hyJ⟩ := Finset.mem_erase.mp hyJ1
  obtain ⟨hzy, hzJ1⟩ := Finset.mem_erase.mp hzJ2
  obtain ⟨hzx, hzJ⟩ := Finset.mem_erase.mp hzJ1
  exact ⟨x, y, z, hxJ, hyJ, hzJ, hyx.symm, hzy.symm, hzx.symm⟩

/-- Any finite set $J$ in a linear order with $3 \le |J|$ contains a strictly
increasing triple $a < b < c$. -/
theorem exists_strict_ordered_triple_of_three_le_card {α : Type*} [LinearOrder α] {J : Finset α}
    (hcard : 3 ≤ J.card) :
    ∃ a b c : α, a ∈ J ∧ b ∈ J ∧ c ∈ J ∧ a < b ∧ b < c := by
  obtain ⟨x, y, z, hx, hy, hz, hxy, hyz, hxz⟩ := exists_three_distinct_of_three_le_card hcard
  rcases lt_or_gt_of_ne hxy with h1 | h1 <;>
  rcases lt_or_gt_of_ne hyz with h2 | h2 <;>
  rcases lt_or_gt_of_ne hxz with h3 | h3
  · exact ⟨x, y, z, hx, hy, hz, h1, h2⟩
  · exfalso; exact lt_asymm (lt_trans h1 h2) h3
  · exact ⟨x, z, y, hx, hz, hy, h3, h2⟩
  · exact ⟨z, x, y, hz, hx, hy, h3, h1⟩
  · exact ⟨y, x, z, hy, hx, hz, h1, h3⟩
  · exact ⟨y, z, x, hy, hz, hx, h2, h3⟩
  · exfalso; exact lt_asymm h3 (lt_trans h2 h1)
  · exact ⟨z, y, x, hz, hy, hx, h2, h1⟩

/-- $x$-coordinates of the 8-point Erdős–Szekeres (1960) 4-cap + 4-cup
pentagon-free witness. -/
def esEightX : Fin 8 → ℤ := ![0, 1, 2, 3, 20, 21, 22, 23]

/-- $y$-coordinates of the 8-point Erdős–Szekeres (1960) 4-cap + 4-cup
pentagon-free witness. -/
def esEightY : Fin 8 → ℤ := ![0, 3, 5, 6, 100, 97, 95, 94]

/-- The 8-point Erdős–Szekeres point map `Fin 8 → ℝ²`. -/
def esEightPt (i : Fin 8) : ℝ² :=
  mkPt (esEightX i : ℝ) (esEightY i : ℝ)

/-- The 8-point Erdős–Szekeres finite point set in $\mathbb{R}^2$. -/
def esEightFinset : Finset ℝ² :=
  Finset.univ.image esEightPt

/-- Exact integer oriented-area determinant for triples in `esEightPt`. -/
def esEightCross (i j k : Fin 8) : ℤ :=
  (esEightX j - esEightX i) * (esEightY k - esEightY i) -
  (esEightY j - esEightY i) * (esEightX k - esEightX i)

/-- `lineSide` on `esEightPt` equals the cast of `esEightCross`. -/
theorem lineSide_esEightPt (i j k : Fin 8) :
    lineSide (esEightPt i) (esEightPt j) (esEightPt k) = (esEightCross i j k : ℝ) := by
  dsimp [lineSide, esEightPt, esEightCross]
  simp only [mkPt_zero, mkPt_one]
  push_cast
  ring

theorem esEightX_ne_of_ne : ∀ i j : Fin 8, i ≠ j → esEightX i ≠ esEightX j := by
  decide

/-- `esEightPt` is injective on `Fin 8`. -/
theorem esEightPt_injective : Function.Injective esEightPt := by
  intro i j hij
  by_contra hne
  have hx := congrArg (fun p : ℝ² => p 0) hij
  simp only [esEightPt, mkPt_zero, Int.cast_inj] at hx
  exact esEightX_ne_of_ne i j hne hx

/-- `esEightFinset` has cardinality 8. -/
theorem esEightFinset_card : esEightFinset.card = 8 := by
  dsimp [esEightFinset]
  rw [Finset.card_image_of_injective _ esEightPt_injective, Finset.card_univ, Fintype.card_fin]

/-- No three distinct indices in `Fin 8` have zero oriented area in `esEightPt`
(decide certificate: the $\binom{8}{3} = 56$ integer determinants are all nonzero). -/
theorem esEightCross_ne_zero_of_distinct :
    ∀ i j k : Fin 8, i ≠ j → j ≠ k → i ≠ k → esEightCross i j k ≠ 0 := by
  decide

/-- `esEightFinset` is in general position (`NonTrilinear`). -/
theorem esEightFinset_nonTrilinear : NonTrilinear (esEightFinset : Set ℝ²) := by
  intro a ha b hb c hc hab hbc hac
  rw [esEightFinset, Finset.coe_image] at ha hb hc
  rcases ha with ⟨i, _, rfl⟩
  rcases hb with ⟨j, _, rfl⟩
  rcases hc with ⟨k, _, rfl⟩
  have hij : i ≠ j := fun h => hab (congrArg esEightPt h)
  have hjk : j ≠ k := fun h => hbc (congrArg esEightPt h)
  have hik : i ≠ k := fun h => hac (congrArg esEightPt h)
  intro hcoll
  have hzero := cross_eq_zero_of_collinear hcoll
  have hls : lineSide (esEightPt i) (esEightPt j) (esEightPt k) = 0 := by
    dsimp [lineSide]; linarith
  rw [lineSide_esEightPt, Int.cast_eq_zero] at hls
  exact esEightCross_ne_zero_of_distinct i j k hij hjk hik hls

/-- Every ordered triple $i < j < k < 4$ in the 4-cap and every index $u \ge 4$ in
the 4-cup place $j$ strictly inside the positively oriented triangle
$(i, k, u)$ (decide certificate over all $8^4$ index quadruples). -/
theorem esEight_cap_triple_with_cup_pt :
    ∀ i j k u : Fin 8,
      i < j → j < k → k.val < 4 → 4 ≤ u.val →
      0 < esEightCross i k j ∧ 0 < esEightCross k u j ∧ 0 < esEightCross u i j := by
  decide

/-- Every ordered triple $4 \le u < v < w$ in the 4-cup and every index $i < 4$ in
the 4-cap place $v$ strictly inside the positively oriented triangle
$(u, i, w)$ (decide certificate over all $8^4$ index quadruples). -/
theorem esEight_cup_triple_with_cap_pt :
    ∀ u v w i : Fin 8,
      u < v → v < w → 4 ≤ u.val → i.val < 4 →
      0 < esEightCross u i v ∧ 0 < esEightCross i w v ∧ 0 < esEightCross w u v := by
  decide

/-- Pigeonhole partition of any 5-element subset $I \subseteq \operatorname{Fin} 8$ across
the 4-cap $\{0, 1, 2, 3\}$ and 4-cup $\{4, 5, 6, 7\}$: either at least 3 elements
lie in the 4-cap and at least 1 in the 4-cup, or at least 3 lie in the 4-cup
and at least 1 in the 4-cap. -/
theorem fin8_cap_cup_split {I : Finset (Fin 8)} (hcard : I.card = 5) :
    let I₁ := I.filter (fun i : Fin 8 => i.val < 4)
    let I₂ := I \ I₁
    (3 ≤ I₁.card ∧ 1 ≤ I₂.card) ∨ (3 ≤ I₂.card ∧ 1 ≤ I₁.card) := by
  intro I₁ I₂
  have hsum : I₂.card + I₁.card = I.card :=
    Finset.card_sdiff_add_card_eq_card (Finset.filter_subset _ I)
  have hsub₁ : I₁ ⊆ Finset.univ.filter (fun i : Fin 8 => i.val < 4) :=
    Finset.filter_subset_filter _ (Finset.subset_univ I)
  have hsub₂ : I₂ ⊆ Finset.univ.filter (fun i : Fin 8 => 4 ≤ i.val) := by
    intro i hi
    rw [Finset.mem_sdiff, Finset.mem_filter] at hi
    rw [Finset.mem_filter]
    have hi4 : ¬ i.val < 4 := fun h => hi.2 ⟨hi.1, h⟩
    exact ⟨Finset.mem_univ i, by omega⟩
  have hle₁ : I₁.card ≤ (Finset.univ.filter (fun i : Fin 8 => i.val < 4)).card :=
    Finset.card_le_card hsub₁
  have hle₂ : I₂.card ≤ (Finset.univ.filter (fun i : Fin 8 => 4 ≤ i.val)).card :=
    Finset.card_le_card hsub₂
  have hc₁ : (Finset.univ.filter (fun i : Fin 8 => i.val < 4)).card = 4 := by decide
  have hc₂ : (Finset.univ.filter (fun i : Fin 8 => 4 ≤ i.val)).card = 4 := by decide
  omega

/-- **8-point pentagon-free certificate**: the 8-point general-position set
`esEightFinset` contains no convex pentagon. -/
theorem not_hasConvexFiveGon_esEightFinset :
    ¬ HasConvexNGon 5 (esEightFinset : Set ℝ²) := by
  rintro ⟨S, hScard, hSsub, hSconv⟩
  have hSsub' : S ⊆ Finset.univ.image esEightPt := Finset.coe_subset.mp hSsub
  obtain ⟨I, _, rfl⟩ := Finset.subset_image_iff.mp hSsub'
  have hIcard : I.card = 5 := by
    rwa [Finset.card_image_of_injective _ esEightPt_injective] at hScard
  rcases fin8_cap_cup_split hIcard with ⟨hI₁, hI₂⟩ | ⟨hI₂, hI₁⟩
  · obtain ⟨i, j, k, hi, hj, hk, hij, hjk⟩ := exists_strict_ordered_triple_of_three_le_card hI₁
    obtain ⟨u, hu⟩ :=
      Finset.card_pos.mp (by omega : 0 < (I \ I.filter (fun i : Fin 8 => i.val < 4)).card)
    obtain ⟨hiI, _⟩ := Finset.mem_filter.mp hi
    obtain ⟨hjI, _⟩ := Finset.mem_filter.mp hj
    obtain ⟨hkI, hk4⟩ := Finset.mem_filter.mp hk
    rw [Finset.mem_sdiff, Finset.mem_filter] at hu
    have hu4 : ¬ u.val < 4 := fun h => hu.2 ⟨hu.1, h⟩
    have hcr := esEight_cap_triple_with_cup_pt i j k u hij hjk hk4 (by omega)
    have htri : InPosTriangle (esEightPt i) (esEightPt k) (esEightPt u) (esEightPt j) := by
      refine ⟨?_, ?_, ?_⟩
      · rw [lineSide_esEightPt]; exact_mod_cast hcr.1
      · rw [lineSide_esEightPt]; exact_mod_cast hcr.2.1
      · rw [lineSide_esEightPt]; exact_mod_cast hcr.2.2
    exact not_convexIndep_of_inPosTriangle
      (Finset.mem_coe.mpr (Finset.mem_image_of_mem _ hiI))
      (Finset.mem_coe.mpr (Finset.mem_image_of_mem _ hkI))
      (Finset.mem_coe.mpr (Finset.mem_image_of_mem _ hu.1))
      (Finset.mem_coe.mpr (Finset.mem_image_of_mem _ hjI))
      htri hSconv
  · obtain ⟨u, v, w, hu, hv, hw, huv, hvw⟩ := exists_strict_ordered_triple_of_three_le_card hI₂
    obtain ⟨i, hi⟩ :=
      Finset.card_pos.mp (by omega : 0 < (I.filter (fun i : Fin 8 => i.val < 4)).card)
    rw [Finset.mem_sdiff, Finset.mem_filter] at hu hv hw
    have hu4 : ¬ u.val < 4 := fun h => hu.2 ⟨hu.1, h⟩
    obtain ⟨hiI, hi4⟩ := Finset.mem_filter.mp hi
    have hcr := esEight_cup_triple_with_cap_pt u v w i huv hvw (by omega) hi4
    have htri : InPosTriangle (esEightPt u) (esEightPt i) (esEightPt w) (esEightPt v) := by
      refine ⟨?_, ?_, ?_⟩
      · rw [lineSide_esEightPt]; exact_mod_cast hcr.1
      · rw [lineSide_esEightPt]; exact_mod_cast hcr.2.1
      · rw [lineSide_esEightPt]; exact_mod_cast hcr.2.2
    exact not_convexIndep_of_inPosTriangle
      (Finset.mem_coe.mpr (Finset.mem_image_of_mem _ hu.1))
      (Finset.mem_coe.mpr (Finset.mem_image_of_mem _ hiI))
      (Finset.mem_coe.mpr (Finset.mem_image_of_mem _ hw.1))
      (Finset.mem_coe.mpr (Finset.mem_image_of_mem _ hv.1))
      htri hSconv

/-- **Unconditional non-membership $8 \notin \text{cardSet}(5)$**: not every
8-point general-position set in $\mathbb{R}^2$ contains a convex pentagon. -/
theorem eight_not_mem_cardSet_five : (8 : ℕ) ∉ cardSet 5 := by
  intro h8
  exact not_hasConvexFiveGon_esEightFinset
    (h8 esEightFinset esEightFinset_card esEightFinset_nonTrilinear)

/-- Any $N \in \text{cardSet}(5)$ satisfies $9 \le N$ (upward closure from the
size-8 witness). -/
theorem nine_le_of_mem_cardSet_five {N : ℕ} (hN : N ∈ cardSet 5) : 9 ≤ N := by
  by_contra hlt
  have hle : N ≤ 8 := by omega
  exact eight_not_mem_cardSet_five (cardSet_upward_closed hle hN)

/-- Lower bound $9 \le f(5)$ (i.e. $2^{5-2} + 1 \le f(5)$). -/
theorem nine_le_f_five : 9 ≤ f 5 :=
  le_csInf (nonempty_cardSet_all 5) fun _ hN => nine_le_of_mem_cardSet_five hN

/-! ## §D6 THE FLOOR ASSEMBLY — the official #107 lower side for 3 ≤ n ≤ 5 -/

/-- **THE HEADLINE TARGET (verbatim signature): the official Erdős #107 lower
bound for the range $3 \le n \le 5$ via explicit finite witnesses** — for every
$n$ with $3 \le n \le 5$, $2^{n-2} + 1 \le f(n)$. The three floor literals
$2^{3-2}+1 = 3$, $2^{4-2}+1 = 5$, $2^{5-2}+1 = 9$ are decide-computed and
discharged by `three_le_f_three` / `five_le_f_four` / `nine_le_f_five`
respectively (each: a size-$2^{n-2}$ general-position witness with no convex
$n$-gon kills $2^{n-2}$ out of `cardSet n`, upward closure kills every
$N \le 2^{n-2}$, and the copied ES-1935 cone supplies the nonemptiness that
`le_csInf` needs). -/
theorem ersz_lower_floor : ∀ n, 3 ≤ n → n ≤ 5 → 2 ^ (n - 2) + 1 ≤ f n := by
  intro n hn3 hn5
  have hcases : n = 3 ∨ n = 4 ∨ n = 5 := by omega
  rcases hcases with rfl | rfl | rfl
  · rw [show 2 ^ (3 - 2) + 1 = 3 from by decide]
    exact three_le_f_three
  · rw [show 2 ^ (4 - 2) + 1 = 5 from by decide]
    exact five_le_f_four
  · rw [show 2 ^ (5 - 2) + 1 = 9 from by decide]
    exact nine_le_f_five

/-- **The official `ersz_bounds` variant restricted to $3 \le n \le 5$, fully
proven**: for all $3 \le n \le 5$,
$2^{n-2} + 1 \le f(n) \le \binom{2n-4}{n-2} + 1$ — the lower side from this
kernel's finite witnesses, the upper side from the copied ES-1935 cone. -/
theorem ersz_bounds_of_le_five {n : ℕ} (hn3 : 3 ≤ n) (hn5 : n ≤ 5) :
    2 ^ (n - 2) + 1 ≤ f n ∧ f n ≤ Nat.choose (2 * n - 4) (n - 2) + 1 :=
  ⟨ersz_lower_floor n hn3 hn5, f_le_erdosSzekeresUpper (by omega : 2 ≤ n)⟩

/-- Anchor sanity at $n = 3$: the floor is EXACT, $f(3) = 3 = 2^{3-2} + 1$
(the official anchor `f_three_eq`, DM107_Official.lean — lower side from the
size-2 witness, upper side from `3 ∈ cardSet 3`). -/
theorem f_three_eq_three : f 3 = 3 :=
  le_antisymm (Nat.sInf_le (self_mem_cardSet_of_le_three (by decide))) three_le_f_three

/-- Anchor sanity at $n = 4$: $5 \le f(4) \le 7$ (the lower side is the Klein
witness; the upper side is $\binom{4}{2} + 1 = 7$ from the ES-1935 cone). -/
theorem f_four_bounds : 5 ≤ f 4 ∧ f 4 ≤ 7 := by
  have h5 := five_le_f_four
  have hu := f_le_erdosSzekeresUpper (by decide : 2 ≤ 4)
  have h7 : erdosSzekeresUpper 4 = 7 := by decide
  omega

/-- Anchor sanity at $n = 5$: $9 \le f(5) \le 21$ (the lower side is the
8-point witness; the upper side is $\binom{6}{3} + 1 = 21$ from the ES-1935
cone). -/
theorem f_five_bounds : 9 ≤ f 5 ∧ f 5 ≤ 21 := by
  have h9 := nine_le_f_five
  have hu := f_le_erdosSzekeresUpper (by decide : 2 ≤ 5)
  have h21 : erdosSzekeresUpper 5 = 21 := by decide
  omega

/-- **WITNESS SANITY / ARSENAL BRIDGE** (BOSS's law, read-before-cite): for
every $3 \le n \le 5$ the lower-bound witness size $2^{n-2}$ is positive and
nontrivial (arsenal `two_pow_pos`, Arsenal/CardinalWorlds.lean:420;
`two_pow_ge2`, Arsenal/CardinalWorlds.lean:431), the floor bound holds, and
the official upper side is compatible with it. -/
theorem dm107d_arsenal_bridge (n : ℕ) (hn : 3 ≤ n) (hn5 : n ≤ 5) :
    0 < 2 ^ (n - 2) ∧ 2 ≤ 2 ^ (n - 2) ∧ 2 ^ (n - 2) + 1 ≤ f n ∧
      f n ≤ Nat.choose (2 * n - 4) (n - 2) + 1 :=
  ⟨two_pow_pos (n - 2), two_pow_ge2 (n - 2) (by omega),
    ersz_lower_floor n hn hn5, f_le_erdosSzekeresUpper (by omega : 2 ≤ n)⟩

end Erdos107D

#eval "DM107D_FLOOR_GREEN"

#print axioms Erdos107D.ersz_lower_floor
#print axioms Erdos107D.ersz_bounds_of_le_five
#print axioms Erdos107D.three_le_f_three
#print axioms Erdos107D.five_le_f_four
#print axioms Erdos107D.nine_le_f_five
#print axioms Erdos107D.two_not_mem_cardSet_three
#print axioms Erdos107D.four_not_mem_cardSet_four
#print axioms Erdos107D.eight_not_mem_cardSet_five
#print axioms Erdos107D.not_hasConvexFiveGon_esEightFinset
#print axioms Erdos107D.esEightFinset_nonTrilinear
#print axioms Erdos107D.kleinFourPts_nonTrilinear
#print axioms Erdos107D.twoPts_nonTrilinear
#print axioms Erdos107D.ptC_mem_convexHull_triangle
#print axioms Erdos107D.inPosTriangle_mem_convexHull
#print axioms Erdos107D.cardSet_upward_closed
#print axioms Erdos107D.f_three_eq_three
#print axioms Erdos107D.dm107d_arsenal_bridge
#print axioms Erdos107D.nonempty_cardSet_all
#print axioms Erdos107D.erdosSzekeresUpper_mem_cardSet
