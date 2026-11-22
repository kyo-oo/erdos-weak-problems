/-
W82-107B — PROOF KERNEL B for Erdős Problem #107 (Happy Ending): the OFFICIAL
upper bound of the solved two-sided variant (DeepMind formal-conjectures
@ 2207c54d, FormalConjectures/ErdosProblems/107.lean):

    theorem ersz_bounds :
        ∀ n ≥ 3, 2^(n - 2) + 1 ≤ f n ∧ f n ≤ Nat.choose (2 * n - 4) (n - 2) + 1

THE FLOOR of lane W82-107B (landed here, the spec's verbatim shape):

    theorem Erdos107.ersz_upper : ∀ n ≥ 3, f n ≤ Nat.choose (2 * n - 4) (n - 2) + 1

The LOWER side (`2^(n-2) + 1 ≤ f n`, the ES-1960 doubling construction) is NOT
claimed — see the honest scope marker `ersz_lower_scope_pos` and the ledger in
WORKLOG_W82_107B.md §5. Never dress partial as complete.

PORTED from the public Lean 4 proof chain cited by the upstream
google-deepmind/formal-conjectures file `FormalConjectures/ErdosProblems/107.lean`
(@ 2207c54d) as the `formal_proof using lean4` witness:

    https://github.com/linrock/math-proofs/blob/cd3cf0b176e95209584bf35555a7c0e501255f6e/erdos-107/Solution.lean#L59
    (pinned commit cd3cf0b176e95209584bf35555a7c0e501255f6e, Apache-2.0,
    Copyright 2026 The Formal Conjectures Authors / Linmiao Xu; vendored
    verbatim under problem107-happy-ending/vendor_linrock/ on the sibling lane
    branch w82-107a)

That repository carries the complete Lean proof of exactly this floor target —
Solution.lean:64 `f_le_erdosSzekeresUpper : ∀ n ≥ 3, f n ≤ Nat.choose
(2 * n - 4) (n - 2) + 1` — the same classical Erdős–Szekeres 1935 cups/caps
argument derived in-frame in WORKLOG_W82_107B.md §1 (the X/Y-split induction,
endpoint gluing, slope transitivity, skipped-chord separation, shear
perturbation). Upstream provenance of this kernel's dependency cone (full
file:line map in WORKLOG_W82_107B.md §2):

  * erdos-107/Solution.lean:64 — `f_le_erdosSzekeresUpper` (the official-shape
    upper bound; my headline target's upstream twin).
  * erdos-107/Proofs/Erdos107Unified435.lean:1620–1623 —
    `f_le_erdosSzekeresUpper_of_mem_cardSet` (witness membership → sInf bound).
  * erdos-107/Proofs/XMonotonePerturbation107.lean:566–571 —
    `erdosSzekeresUpper_mem_cardSet` ($\binom{2n-4}{n-2}+1 \in \mathrm{cardSet}\,n$),
    the ES 1935 cup–cap witness; plus the shear reduction and x-sorting bridge
    (§1–§2 there).
  * erdos-107/Proofs/Erdos107Unified435.lean — `mkPt`, the cross-product /
    `slopeLt`/`slopeGt` calculus, `lineSide` + the 4-point secant syzygies, the
    half-plane separation framework (`convexIndep_of_pointwise_strict_sep`),
    `CupChainEnding`/`CapChainStarting` and the ES 1935 endpoint-gluing
    Pascal-splitting pigeonhole core.
  * erdos-107/Proofs/InductiveKCupKCapConvexityAndKKSWedgePentagonForcing107.lean —
    `IsCupSet`/`IsCapSet`, the insert/skipped-chord lemmas,
    `convexIndep_of_isCupSet`/`of_isCapSet` (cup/cap → ConvexIndep).

The toolchain adaptation (upstream targets leanprover/lean4:v4.35.0-rc2; the
campaign toolchain is v4.33.0-rc2): module-system syntax stripped; the
deprecated-at-v4.33.0-rc2 alias `Set.image_diff` (of `Set.image_sdiff`,
Mathlib/Data/Set/Image.lean:382) kept with `linter.deprecated` silenced;
upstream's own `NonTrilinear`/`ConvexIndep`/`HasConvexNGon`/`cardSet`/`f`
re-definitions replaced by the VENDORED OFFICIAL ones (`FC.Geometry.TwoD` +
the verbatim `cardSet`/`f` block from DM107_Official.lean, which this
standalone out-of-library kernel cannot import), with the definitional bridge
`nonTrilinear_iff` (Iff.rfl) for the `Set.Triplewise` packaging. That
adaptation was executed for this shared dependency cone by the sibling lane
W82-107A (DM107_Proof_A.lean, branch w82-107a, the `nonempty_cardSet` kill);
§0–§11 below are that adaptation, reused verbatim with attribution, and
§12–§15 (the floor-kill assembly, the arsenal bridge, the corollaries, the
honest scope marker) are lane W82-107B's own. Only the dependency cone of the
floor target is ported (the upstream files also prove f(4) = 5, KKS pentagon
forcing, the Tóth–Valtr bounds, n ≤ 5 two-sided bounds — out of scope here).

ARSENAL BRIDGE (BOSS's law): imports Arsenal.ErdosTernary2.Basic and
Arsenal.CardinalWorlds; citations by file:line, read-before-cite:
    ErdosTernary2.lt_three_cases  (Arsenal/ErdosTernary2/Basic.lean:16)
    two_pow_pos                   (Arsenal/CardinalWorlds.lean:420)
    two_pow_ge2                   (Arsenal/CardinalWorlds.lean:431)
    two_pow_factored              (Arsenal/CardinalWorlds.lean:425)

Zero sorry, zero native_decide. Complete proof only.
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

namespace Erdos107

/-! ## §0 THE OFFICIAL DEFINITIONS (verbatim from DM107_Official.lean) -/

/-- The set of $N$ such that any $N$ points in the plane, no three on a line,
contain a convex $n$-gon. -/
def cardSet (n : ℕ) := { N | ∀ (pts : Finset ℝ²), pts.card = N → NonTrilinear (pts : Set ℝ²) →
  HasConvexNGon n pts }

/-- The function $f(n)$ specified in `erdos_107`. -/
noncomputable def f (n : ℕ) : ℕ :=
  sInf (cardSet n)

/-! ## §1 POINT ARITHMETIC (port of Erdos107Unified435.lean §1, `mkPt` + cross product) -/

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

/-- If two points have distinct $x$-coordinates and the 2D cross product with a third point vanishes,
the three points are collinear. -/
theorem collinear_of_cross_eq_zero {a b c : ℝ²} (hab : a 0 ≠ b 0)
    (hcross : (b 0 - a 0) * (c 1 - a 1) - (b 1 - a 1) * (c 0 - a 0) = 0) :
    Collinear ℝ ({a, b, c} : Set ℝ²) := by
  rw [collinear_iff_of_mem (by simp : a ∈ ({a, b, c} : Set ℝ²))]
  refine ⟨b - a, fun p hp => ?_⟩
  simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hp
  have hba0 : b 0 - a 0 ≠ 0 := sub_ne_zero.mpr hab.symm
  rcases hp with rfl | rfl | rfl
  · exact ⟨0, by simp⟩
  · exact ⟨1, by simp⟩
  · refine ⟨(p 0 - a 0) / (b 0 - a 0), ?_⟩
    ext i
    fin_cases i
    · simp only [Fin.zero_eta, vadd_eq_add, PiLp.add_apply, PiLp.smul_apply,
        PiLp.sub_apply, smul_eq_mul]
      have h0 : (p 0 - a 0) / (b 0 - a 0) * (b 0 - a 0) = p 0 - a 0 :=
        div_mul_cancel₀ _ hba0
      linarith
    · simp only [Fin.mk_one, vadd_eq_add, PiLp.add_apply, PiLp.smul_apply,
        PiLp.sub_apply, smul_eq_mul]
      have h1 : (p 0 - a 0) / (b 0 - a 0) * (b 1 - a 1) = p 1 - a 1 := by
        rw [div_mul_eq_mul_div, div_eq_iff hba0]
        linarith
      linarith

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
For every $k \in \mathbb{N}$, any $x$-monotone sequence $P$ on $S$ satisfying `HasCap P S k$
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

/-! ## §12 THE FLOOR KILL — the OFFICIAL upper bound of Erdős #107
(the upper side of `ersz_bounds`; port of Erdos107Unified435.lean L1620–1623
`f_le_erdosSzekeresUpper_of_mem_cardSet` + XMonotonePerturbation107.lean
L589–591 `f_le_erdosSzekeresUpper` + Solution.lean L64 `f_le_erdosSzekeresUpper`
— the official statement shape) -/

/-- Membership of the Erdős–Szekeres witness in `cardSet n` bounds `f n` from
above through the infimum (port of Erdos107Unified435.lean L1620–1623). -/
theorem f_le_erdosSzekeresUpper_of_mem_cardSet {n : ℕ}
    (hmem : erdosSzekeresUpper n ∈ cardSet n) :
    f n ≤ erdosSzekeresUpper n :=
  Nat.sInf_le hmem

/-- **Unconditional Erdős–Szekeres 1935 upper bound**: for all $k \ge 2$,
$f(k) \le \binom{2k-4}{k-2} + 1$ (port of XMonotonePerturbation107.lean
L589–591). -/
theorem f_le_erdosSzekeresUpper {k : ℕ} (hk : 2 ≤ k) :
    f k ≤ erdosSzekeresUpper k :=
  f_le_erdosSzekeresUpper_of_mem_cardSet (erdosSzekeresUpper_mem_cardSet hk)

/-- **THE FLOOR TARGET (verbatim signature — the upper side of the official
`ersz_bounds`, DeepMind formal-conjectures @ 2207c54d,
FormalConjectures/ErdosProblems/107.lean; port of Solution.lean L64)**: the
classical Erdős–Szekeres 1935 upper bound — for every $n \ge 3$,
$f(n) \le \binom{2n-4}{n-2} + 1$. The witness $\binom{2n-4}{n-2} + 1$ lies in
`cardSet n` (any that many points in the plane, no three on a line, contain a
convex $n$-gon), and `f n` is the infimum of `cardSet n`. -/
theorem ersz_upper : ∀ n ≥ 3, f n ≤ Nat.choose (2 * n - 4) (n - 2) + 1 := by
  intro n hn
  exact f_le_erdosSzekeresUpper (by omega : 2 ≤ n)

/-! ## §13 THE BINOMIAL COMPARISON LAWS + THE ARSENAL BRIDGE (BOSS's law —
read-before-cite, all citations verified)

Laws used in this kernel, read at their source lines before use:
  * `ErdosTernary2.lt_three_cases` — Arsenal/ErdosTernary2/Basic.lean:16
    (the $n < 3$ trichotomy $n = 0 \vee n = 1 \vee n = 2$; load-bearing in
    `nonempty_cardSet_all`, the n < 3 base case of the existence corollary).
  * `two_pow_pos`  — Arsenal/CardinalWorlds.lean:420 (`0 < 2^j`).
  * `two_pow_ge2`  — Arsenal/CardinalWorlds.lean:431 (`2 ≤ 2^j` for `1 ≤ j`).
  * `two_pow_factored` — Arsenal/CardinalWorlds.lean:425 (`2^j = 2 * 2^(j-1)` for `1 ≤ j`;
    used to prove the in-kernel `two_pow_ge_succ`).
The binomial law `two_pow_le_central_binom` ($2^k \le \binom{2k}{k}$) is ported from
linrock's Erdos107Unified435.lean §4 (proved there from Mathlib's Pascal recurrence;
not an arsenal law — recorded here per the never-fake-a-citation rule). -/

/-- The Erdős–Szekeres conjectured value $2^{n-2} + 1$ for $f(n)$ (the open core
`erdos_107`; NOT claimed here). -/
def erdosSzekeresConjectured (n : ℕ) : ℕ :=
  2 ^ (n - 2) + 1

/-- Doubling inequality for central binomial coefficients: $2 \binom{2k}{k} \le \binom{2(k+1)}{k+1}$. -/
theorem two_mul_choose_central_le_succ (k : ℕ) :
    2 * (2 * k).choose k ≤ (2 * (k + 1)).choose (k + 1) := by
  cases k with
  | zero => decide
  | succ m =>
    have h0 : 2 * (m + 1 + 1) = 2 * m + 2 + 1 + 1 := by omega
    have h0b : 2 * (m + 1) = 2 * m + 2 := by omega
    rw [h0, h0b]
    have h1 := Nat.choose_succ_succ' (2 * m + 2 + 1) (m + 1)
    have h2 := Nat.choose_succ_succ' (2 * m + 2) m
    have h3 := Nat.choose_succ_succ' (2 * m + 2) (m + 1)
    omega

/-- Universal exponential lower bound for central binomial coefficients: $2^k \le \binom{2k}{k}$. -/
theorem two_pow_le_central_binom (k : ℕ) : 2 ^ k ≤ (2 * k).choose k := by
  induction k with
  | zero => simp
  | succ k ih =>
    have hstep := two_mul_choose_central_le_succ k
    have hpow : 2 ^ (k + 1) = 2 * 2 ^ k := by ring
    omega

/-- For every $n \in \mathbb{N}$, the conjectured Erdős–Szekeres value $2^{n-2} + 1$ is bounded above
by the Erdős–Szekeres binomial upper bound $\binom{2n-4}{n-2} + 1$. -/
theorem erdosSzekeresConjectured_le_upper (n : ℕ) :
    erdosSzekeresConjectured n ≤ erdosSzekeresUpper n := by
  dsimp [erdosSzekeresConjectured, erdosSzekeresUpper]
  rcases le_or_gt n 2 with hn | hn
  · have h1 : n - 2 = 0 := by omega
    have h2 : 2 * n - 4 = 0 := by omega
    rw [h1, h2]
    decide
  · have h2n : 2 * n - 4 = 2 * (n - 2) := by omega
    rw [h2n]
    have := two_pow_le_central_binom (n - 2)
    omega

/-- In-kernel exponential growth law $m + 1 \le 2^m$, proved by induction with the arsenal's
`two_pow_factored` (Arsenal/CardinalWorlds.lean:425) supplying the successor step. -/
theorem two_pow_ge_succ (m : ℕ) : m + 1 ≤ 2 ^ m := by
  induction m with
  | zero => decide
  | succ m ih =>
    have h1 : 1 ≤ m + 1 := by omega
    have h := two_pow_factored (m + 1) h1
    have hsub : m + 1 - 1 = m := by omega
    rw [h, hsub]
    omega

/-- **WITNESS SANITY / ARSENAL BRIDGE**: for every $n \ge 3$ the open-core
conjectured threshold $2^{n-2}+1$ and $n$ itself are both dominated by the
proven upper-bound witness `erdosSzekeresUpper n` (so the convex $n$-gon found
is a proper subset of the witness configuration, and the conjectured value is
consistent with this kernel's upper bound), and the floor bound holds. Arsenal
laws: `two_pow_pos` (CardinalWorlds.lean:420), `two_pow_ge2`
(CardinalWorlds.lean:431), `two_pow_factored` (CardinalWorlds.lean:425, via
`two_pow_ge_succ`). -/
theorem dm107b_arsenal_bridge (n : ℕ) (hn : 3 ≤ n) :
    0 < 2 ^ (n - 2) ∧ 2 ≤ 2 ^ (n - 2) ∧
      erdosSzekeresConjectured n ≤ erdosSzekeresUpper n ∧ n ≤ erdosSzekeresUpper n ∧
      f n ≤ Nat.choose (2 * n - 4) (n - 2) + 1 := by
  have h1 := two_pow_pos (n - 2)
  have h2 := two_pow_ge2 (n - 2) (by omega)
  have h3 := erdosSzekeresConjectured_le_upper n
  have h4 : n ≤ erdosSzekeresConjectured n := by
    dsimp [erdosSzekeresConjectured]
    have hpow : n - 2 + 1 ≤ 2 ^ (n - 2) := two_pow_ge_succ (n - 2)
    omega
  have h5 := ersz_upper n hn
  exact ⟨h1, h2, h3, le_trans h4 h3, h5⟩

/-! ## §14 COROLLARIES — the official existence variant (sibling lane
W82-107A's target, re-derived here from the same cone as an independent
verification) and the anchor sanity case -/

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

/-- **The official existence variant (verbatim signature, DeepMind
formal-conjectures @ 2207c54d; sibling lane W82-107A's kill target)**: for
every $n \ge 3$ there is an $N$ such that every $N$-point set in the plane with
no three collinear contains $n$ points in convex position. Corollary of the
same cup–cap cone as the floor kill above. -/
theorem nonempty_cardSet : ∀ n ≥ 3, (cardSet n).Nonempty :=
  fun n _ => nonempty_cardSet_all n

/-- Anchor sanity at $n = 3$: the floor bound degenerates to $f(3) \le
\binom{2}{1} + 1 = 3$, the upper side of the official anchor `f_three_eq`
(`f 3 = 3`, DM107_Official.lean). -/
theorem ersz_upper_n3 : f 3 ≤ 3 := by
  have h := ersz_upper 3 (by decide)
  have h2 : Nat.choose (2 * 3 - 4) (3 - 2) + 1 = 3 := by decide
  omega

/-! ## §15 HONEST SCOPE — never dress partial as complete -/

/-- **HONEST SCOPE MARKER (the stretch that remains open)**: the LOWER side
`2^(n-2) + 1 ≤ f n` of the official `ersz_bounds` (the ES-1960 doubling
construction / the campaign's ES_SANDWICH_ALLN package) is NOT claimed by this
kernel — neither linrock's public proof (only $n \le 5$ witnesses) nor this
cone covers it. What IS certified here: (a) the proven upper bound
$f(n) \le \binom{2n-4}{n-2}+1$ (the floor), and (b) the COMPATIBILITY of the
lower side's witness size with it — the conjectured value $2^{n-2}+1$ is
positive (arsenal `two_pow_pos`, CardinalWorlds.lean:420), nontrivial (arsenal
`two_pow_ge2`, CardinalWorlds.lean:431), and bounded above by the proven upper
bound, so the open lower side and this kernel's upper side are consistent. -/
theorem ersz_lower_scope_pos (n : ℕ) (hn : 3 ≤ n) :
    0 < 2 ^ (n - 2) ∧ 2 ≤ 2 ^ (n - 2) ∧
      2 ^ (n - 2) + 1 ≤ Nat.choose (2 * n - 4) (n - 2) + 1 ∧
      f n ≤ Nat.choose (2 * n - 4) (n - 2) + 1 := by
  have h1 := two_pow_pos (n - 2)
  have h2 := two_pow_ge2 (n - 2) (by omega)
  have h3 := erdosSzekeresConjectured_le_upper n
  dsimp [erdosSzekeresConjectured, erdosSzekeresUpper] at h3
  have h4 := ersz_upper n hn
  exact ⟨h1, h2, h3, h4⟩

end Erdos107

#eval "DM107B_ERSZ_GREEN"

#print axioms Erdos107.ersz_upper
#print axioms Erdos107.f_le_erdosSzekeresUpper
#print axioms Erdos107.erdosSzekeresUpper_mem_cardSet
#print axioms Erdos107.erdos_szekeres_cup_cap_theorem_on
#print axioms Erdos107.hasConvexNGon_of_nonTrilinear_and_card_ge
#print axioms Erdos107.nonempty_cardSet
#print axioms Erdos107.dm107b_arsenal_bridge
#print axioms Erdos107.ersz_lower_scope_pos
