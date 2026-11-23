/-
W85-107C — PROOF KERNEL C for Erdős Problem #107 (Happy Ending): the LOWER
side of the official two-sided variant for n ≤ 5, the exact values for
n ≤ 4, and the two-sided classical bounds for n ≤ 5, over the vendored
OFFICIAL DeepMind formal-conjectures definitions:

    theorem f_eq_conjectured_of_le_four : ∀ n, 3 ≤ n → n ≤ 4 → f n = 2 ^ (n - 2) + 1
    theorem ersz_lower_le_five         : ∀ n, 3 ≤ n → n ≤ 5 → 2 ^ (n - 2) + 1 ≤ f n
    theorem ersz_bounds_of_le_five :
        ∀ n, 3 ≤ n → n ≤ 5 → 2 ^ (n - 2) + 1 ≤ f n ∧ f n ≤ Nat.choose (2 * n - 4) (n - 2) + 1

THE FLOOR of lane W85-107C (all three landed here):
  * f(3) = 3   — the official anchor route (DM107_Official.lean:106–134,
    CI-GREEN as `DM107_ANCHORS_GREEN`), NOT the vendor's parabola route
    (cone deviation #1, AUDIT_W85_107C.md §1h);
  * f(4) = 5   — Esther Klein's 5-point Happy Ending theorem (5 ∈ cardSet 4,
    the DEDICATED tight n=4 argument: Blueprint107.lean §2 L246–461; the
    general ES upper only gives f(4) ≤ 7) + the 4-point
    triangle-with-interior-point witness (4 ∉ cardSet 4,
    Erdos107Unified435.lean §1 L364–495);
  * 9 ≤ f(5)   — the 8-point Erdős–Szekeres (1960) 4-cap + 4-cup integer
    witness (8 ∉ cardSet 5, Blueprint107.lean §3 L519–757): five `decide`
    blocks at the index level (64 / 512 / 4096 / 4096 / 2 cases) plus the
    barycentric `InPosTriangle` non-convexity calculus (§1 L85–244);
  * the n = 5 upper f(5) ≤ C(6,3)+1 = 21 — the sibling lanes' already-GREEN
    Erdős–Szekeres 1935 cup–cap cone (cloned verbatim below, §0–§14).

PORTED from the public Lean 4 proof chain cited by the upstream
google-deepmind/formal-conjectures file
`FormalConjectures/ErdosProblems/107.lean` (@ 2207c54d) as the
`formal_proof using lean4` witness:

    https://github.com/linrock/math-proofs/blob/cd3cf0b176e95209584bf35555a7c0e501255f6e/erdos-107/Solution.lean#L69
    (pinned commit cd3cf0b176e95209584bf35555a7c0e501255f6e, Apache-2.0,
    Copyright 2026 The Formal Conjectures Authors / Linmiao Xu; vendored
    verbatim under problem107-happy-ending/vendor_linrock/)

The entry targets are Solution.lean L69 `f_eq_conjectured_of_le_four` and
L74 `ersz_bounds_of_le_five` (via `Erdos107.Palomar.f_eq` / `cardSet_eq`,
both `rfl`-bridges to `Erdos107.*`), i.e. Blueprint107.lean L773 / L784 /
L796. Full cone map + port plan: AUDIT_W85_107C.md (the W85-107C-A audit).

STRUCTURE of this kernel (per AUDIT_W85_107C.md §4):
  * §0–§14  — the W82-107B GREEN cone CLONED VERBATIM from
    DM107_Proof_B.lean L89–1571 (the official defs §0, point arithmetic,
    lineSide, half-plane separation, the ES 1935 cup–cap machinery,
    x-sorting, shear, the sInf upper bridge, `nonempty_cardSet`), with the
    single namespace swap Erdos107 → Erdos107C. Attributed to lanes
    W82-107A/W82-107B (CI jobs kernel-107dm-a / kernel-107dm-b,
    `DM107B_ERSZ_GREEN`). The clone is required: this is a standalone
    `lake env lean` kernel (it cannot import DM107_Proof_B.lean), and the
    n = 5 upper side of the third target has no cheaper route
    (`f_five_upper_unconditional` upstream is literally
    `f_le_erdosSzekeresUpper (by decide)`).
  * §15–§21 — the FRESH ports (the lower-bound cone): the oriented-sign
    dichotomy + line separation + the 4-point strict-separation criterion
    (Erdos107Unified435.lean L1773–1962 + L1097–1148); the InPosTriangle
    barycentric calculus (Blueprint107.lean L85–244); the Klein 4-point
    witness and the cardSet closure laws (Erdos107Unified435.lean L49–223 +
    L364–511); Esther Klein's 5-point theorem (Blueprint107.lean L246–461 +
    Erdos107Unified435.lean L1610–1615); the official f 3 = 3 anchor
    (DM107_Official.lean L106–134); the 8-point ES-1960 witness
    (Blueprint107.lean L519–757); the three targets + the honest scope
    marker.

INTENTIONAL DEVIATIONS from the vendor proofs (both statement-preserving,
both designed and risk-assessed in AUDIT_W85_107C.md; everything else in
the fresh sections is a faithful port of proofs that compiled upstream):
  1. `f_three_eq` ports the official CI-GREEN anchor proof (the collinear
     x-axis witness with vacuous `NonTrilinear` via
     `Set.triplewise_of_encard_lt`) instead of the vendor's parabola route —
     deleting the whole parabola sub-cone (~45 lines).
  2. `five_le_of_mem_cardSet_four` is proved via `cardSet_upward_closed`
     (mirroring Blueprint107.lean L740 `nine_le_of_mem_cardSet_five`)
     instead of the vendor's `le_of_mem_cardSet` (which pulls the parabola
     sub-cone).
Plus three recorded micro-adaptations for v4.33.0-rc2 compatibility
(AUDIT_W85_107C.md risk list): `simp only` instead of
`rw [esEightFinset, …]` (definition-unfolding inside `rw` unattested at
v4.33), `omega` instead of `Nat.le_trans_eq` (unattested at v4.33), and
signature-agnostic named arguments `(𝕜 := ℝ)` on `subset_convexHull` /
`convex_convexHull`.

HONEST SCOPE (never dress partial as complete): the lower bound
2^(n-2)+1 ≤ f(n) is proved here for 3 ≤ n ≤ 5 ONLY. The stretch n ≥ 6 (the
ES-1960 doubling construction) remains open — see the scope marker
`ersz_lower_scope_pos` and the ledger in WORKLOG_W85_107C.md. The open core
`erdos_107 : ∀ n ≥ 3, f n = 2^(n-2)+1` is NOT claimed.

ARSENAL BRIDGE (BOSS's law — read-before-cite; cloned verbatim with §13–§14
of the W82-107B cone): ErdosTernary2.lt_three_cases
(Arsenal/ErdosTernary2/Basic.lean:16), two_pow_pos
(Arsenal/CardinalWorlds.lean:420), two_pow_ge2
(Arsenal/CardinalWorlds.lean:431), two_pow_factored
(Arsenal/CardinalWorlds.lean:425).

Zero sorry, zero native_decide. Complete proof only. CI is the only Lean
verdict (`lake env lean problem107-happy-ending/DM107_Proof_C.lean`,
toolchain leanprover/lean4:v4.33.0-rc2, Mathlib v4.33.0-rc2).
-/
import Mathlib
import FC.Geometry.TwoD
import Arsenal.ErdosTernary2.Basic
import Arsenal.CardinalWorlds

set_option linter.deprecated false
set_option linter.unnecessarySimpa false
set_option linter.unusedSimpArgs false
set_option linter.unnecessarySeqFocus false
set_option maxHeartbeats 16000000
set_option maxRecDepth 262144
noncomputable section

open Filter
open EuclideanGeometry

namespace Erdos107C

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

/-! ## §15 ORIENTED-SIGN DICHOTOMY AND LINE SEPARATION
(fresh port of Erdos107Unified435.lean L1773–1781, L1787–1962, and the
4-point strict-separation criterion L1097–1148 — the two `lineSide` lemmas
the cloned B cone §4 does not carry, and the separation machinery that
Esther Klein's 5-point argument and the 8-point witness certificate reduce
to) -/

/-- Any three non-collinear points in $\mathbb{R}^2$ have strictly positive or strictly
negative `lineSide`. (Port of Erdos107Unified435.lean L1773–1781.) -/
theorem lineSide_pos_or_neg_of_not_collinear {p q r : ℝ²}
    (hnc : ¬ Collinear ℝ ({p, q, r} : Set ℝ²)) :
    0 < lineSide p q r ∨ lineSide p q r < 0 := by
  rcases lt_trichotomy 0 (lineSide p q r) with hpos | heq | hneg
  · exact Or.inl hpos
  · exact False.elim (hnc (collinear_of_lineSide_eq_zero heq.symm))
  · exact Or.inr hneg

/-- If $c$ lies on the non-positive side of the directed line $a \to b$ and $d$ lies on its
strictly positive side, then the affine functional of $a \to b$ strictly separates $d$ from
$\{a, b, c\}$. (Port of Erdos107Unified435.lean L1787–1800.) -/
theorem lineSide_sep_of_neg_pos {a b c d : ℝ²}
    (hc : lineSide a b c ≤ 0) (hd : 0 < lineSide a b d) :
    ∃ u v k : ℝ,
      u * a 0 + v * a 1 ≤ k ∧
      u * b 0 + v * b 1 ≤ k ∧
      u * c 0 + v * c 1 ≤ k ∧
      k < u * d 0 + v * d 1 := by
  refine ⟨lineNormX a b, lineNormY a b, lineConst a b, ?_, ?_, ?_, ?_⟩
  · rw [lineSide_affine_decomp, lineSide_self_left]; linarith
  · rw [lineSide_affine_decomp, lineSide_self_right]; linarith
  · rw [lineSide_affine_decomp]; linarith
  · rw [lineSide_affine_decomp]; linarith

/-- Universal 4-point strict-separation criterion for convex quadrilaterals in $\mathbb{R}^2$.
(Port of Erdos107Unified435.lean L1097–1148.) -/
theorem convexIndep_four_of_strict_sep {p₁ p₂ p₃ p₄ : ℝ²}
    (h₁ : ∃ u v c : ℝ, u * p₂ 0 + v * p₂ 1 ≤ c ∧ u * p₃ 0 + v * p₃ 1 ≤ c ∧
      u * p₄ 0 + v * p₄ 1 ≤ c ∧ c < u * p₁ 0 + v * p₁ 1)
    (h₂ : ∃ u v c : ℝ, u * p₁ 0 + v * p₁ 1 ≤ c ∧ u * p₃ 0 + v * p₃ 1 ≤ c ∧
      u * p₄ 0 + v * p₄ 1 ≤ c ∧ c < u * p₂ 0 + v * p₂ 1)
    (h₃ : ∃ u v c : ℝ, u * p₁ 0 + v * p₁ 1 ≤ c ∧ u * p₂ 0 + v * p₂ 1 ≤ c ∧
      u * p₄ 0 + v * p₄ 1 ≤ c ∧ c < u * p₃ 0 + v * p₃ 1)
    (h₄ : ∃ u v c : ℝ, u * p₁ 0 + v * p₁ 1 ≤ c ∧ u * p₂ 0 + v * p₂ 1 ≤ c ∧
      u * p₃ 0 + v * p₃ 1 ≤ c ∧ c < u * p₄ 0 + v * p₄ 1) :
    ConvexIndep ({p₁, p₂, p₃, p₄} : Set ℝ²) := by
  apply convexIndep_of_pointwise_strict_sep
  intro x hx
  simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hx
  rcases hx with rfl | rfl | rfl | rfl
  · rcases h₁ with ⟨u, v, c, hp₂, hp₃, hp₄, hp₁⟩
    refine ⟨u, v, c, ?_, hp₁⟩
    intro y ⟨hy_mem, hy_ne⟩
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hy_mem
    rcases hy_mem with rfl | rfl | rfl | rfl
    · exact False.elim (hy_ne rfl)
    · exact hp₂
    · exact hp₃
    · exact hp₄
  · rcases h₂ with ⟨u, v, c, hp₁, hp₃, hp₄, hp₂⟩
    refine ⟨u, v, c, ?_, hp₂⟩
    intro y ⟨hy_mem, hy_ne⟩
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hy_mem
    rcases hy_mem with rfl | rfl | rfl | rfl
    · exact hp₁
    · exact False.elim (hy_ne rfl)
    · exact hp₃
    · exact hp₄
  · rcases h₃ with ⟨u, v, c, hp₁, hp₂, hp₄, hp₃⟩
    refine ⟨u, v, c, ?_, hp₃⟩
    intro y ⟨hy_mem, hy_ne⟩
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hy_mem
    rcases hy_mem with rfl | rfl | rfl | rfl
    · exact hp₁
    · exact hp₂
    · exact False.elim (hy_ne rfl)
    · exact hp₄
  · rcases h₄ with ⟨u, v, c, hp₁, hp₂, hp₃, hp₄⟩
    refine ⟨u, v, c, ?_, hp₄⟩
    intro y ⟨hy_mem, hy_ne⟩
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hy_mem
    rcases hy_mem with rfl | rfl | rfl | rfl
    · exact hp₁
    · exact hp₂
    · exact hp₃
    · exact False.elim (hy_ne rfl)

/-- **Universal Crossing-Diagonal Convex Quadrilateral Criterion**:
If the diagonal $p_1 p_3$ strictly separates $p_2$ and $p_4$ and the diagonal $p_2 p_4$
strictly separates $p_1$ and $p_3$, then $\{p_1, p_2, p_3, p_4\}$ is convex independent.
(Port of Erdos107Unified435.lean L1805–1825.) -/
theorem convexIndep_four_of_opposite_diagonals {p₁ p₂ p₃ p₄ : ℝ²}
    (hd₁ : lineSide p₁ p₃ p₄ < 0 ∧ 0 < lineSide p₁ p₃ p₂)
    (hd₂ : lineSide p₂ p₄ p₁ < 0 ∧ 0 < lineSide p₂ p₄ p₃) :
    ConvexIndep ({p₁, p₂, p₃, p₄} : Set ℝ²) := by
  apply convexIndep_four_of_strict_sep
  · have hc : lineSide p₄ p₂ p₃ ≤ 0 := by
      rw [lineSide_swap_left]; linarith [hd₂.2]
    have hd : 0 < lineSide p₄ p₂ p₁ := by
      rw [lineSide_swap_left]; linarith [hd₂.1]
    rcases lineSide_sep_of_neg_pos hc hd with ⟨u, v, k, h₄, h₂, h₃, h₁⟩
    exact ⟨u, v, k, h₂, h₃, h₄, h₁⟩
  · rcases lineSide_sep_of_neg_pos (le_of_lt hd₁.1) hd₁.2 with ⟨u, v, k, h₁, h₃, h₄, h₂⟩
    exact ⟨u, v, k, h₁, h₃, h₄, h₂⟩
  · rcases lineSide_sep_of_neg_pos (le_of_lt hd₂.1) hd₂.2 with ⟨u, v, k, h₂, h₄, h₁, h₃⟩
    exact ⟨u, v, k, h₁, h₂, h₄, h₃⟩
  · have hc : lineSide p₃ p₁ p₂ ≤ 0 := by
      rw [lineSide_swap_left]; linarith [hd₁.2]
    have hd : 0 < lineSide p₃ p₁ p₄ := by
      rw [lineSide_swap_left]; linarith [hd₁.1]
    rcases lineSide_sep_of_neg_pos hc hd with ⟨u, v, k, h₃, h₁, h₂, h₄⟩
    exact ⟨u, v, k, h₁, h₂, h₃, h₄⟩

/-- If $p, q$ lie on the positive open side of $a \to b$ and $a, b$ lie on the positive open
side of $p \to q$, then $\{a, b, p, q\}$ is convex independent.
(Port of Erdos107Unified435.lean L1831–1854.) -/
theorem convexIndep_four_of_pos_same_open_side {a b p q : ℝ²}
    (habp : 0 < lineSide a b p) (habq : 0 < lineSide a b q)
    (hpqa : 0 < lineSide p q a) (hpqb : 0 < lineSide p q b) :
    ConvexIndep ({a, b, p, q} : Set ℝ²) := by
  have hset : ({a, b, p, q} : Set ℝ²) = ({a, q, p, b} : Set ℝ²) := by
    ext x
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff]
    tauto
  rw [hset]
  apply convexIndep_four_of_opposite_diagonals
  · refine ⟨?_, ?_⟩
    · have h : lineSide a p b = - lineSide a b p := by
        dsimp [lineSide]; ring
      linarith
    · have h : lineSide a p q = lineSide p q a := by
        dsimp [lineSide]; ring
      linarith
  · refine ⟨?_, ?_⟩
    · have h : lineSide q b a = - lineSide a b q := by
        dsimp [lineSide]; ring
      linarith
    · have h : lineSide q b p = lineSide p q b := by
        dsimp [lineSide]; ring
      linarith

/-- **Universal Mutual Open-Side Convex Quadrilateral Theorem**:
If $p, q$ lie on the positive open side of $a \to b$ and $a, b$ lie on the same open side
of $p \leftrightarrow q$ (either both positive or both negative), then $\{a, b, p, q\}$ is
convex independent. (Port of Erdos107Unified435.lean L1861–1875.) -/
theorem convexIndep_four_of_same_open_side {a b p q : ℝ²}
    (habp : 0 < lineSide a b p) (habq : 0 < lineSide a b q)
    (hsame : (0 < lineSide p q a ∧ 0 < lineSide p q b) ∨
      (lineSide p q a < 0 ∧ lineSide p q b < 0)) :
    ConvexIndep ({a, b, p, q} : Set ℝ²) := by
  rcases hsame with ⟨hpqa, hpqb⟩ | ⟨hpqa, hpqb⟩
  · exact convexIndep_four_of_pos_same_open_side habp habq hpqa hpqb
  · have hset : ({a, b, p, q} : Set ℝ²) = ({a, b, q, p} : Set ℝ²) := by
      ext x
      simp only [Set.mem_insert_iff, Set.mem_singleton_iff]
      tauto
    rw [hset]
    apply convexIndep_four_of_pos_same_open_side habq habp
    · rw [lineSide_swap_left]; linarith
    · rw [lineSide_swap_left]; linarith

/-- **Universal 3-Sign Pigeonhole Principle**:
Among any three nonzero real numbers $x, y, z$, at least one of the three pairs
$(x, y)$, $(y, z)$, $(z, x)$ shares the same strict sign.
(Port of Erdos107Unified435.lean L1882–1895.) -/
theorem pigeonhole_three_signs {x y z : ℝ}
    (hx : 0 < x ∨ x < 0) (hy : 0 < y ∨ y < 0) (hz : 0 < z ∨ z < 0) :
    ((0 < x ∧ 0 < y) ∨ (x < 0 ∧ y < 0)) ∨
    ((0 < y ∧ 0 < z) ∨ (y < 0 ∧ z < 0)) ∨
    ((0 < z ∧ 0 < x) ∨ (z < 0 ∧ x < 0)) := by
  rcases hx with hx | hx <;> rcases hy with hy | hy <;> rcases hz with hz | hz
  · exact Or.inl (Or.inl ⟨hx, hy⟩)
  · exact Or.inl (Or.inl ⟨hx, hy⟩)
  · exact Or.inr (Or.inr (Or.inl ⟨hz, hx⟩))
  · exact Or.inr (Or.inl (Or.inr ⟨hy, hz⟩))
  · exact Or.inr (Or.inl (Or.inl ⟨hy, hz⟩))
  · exact Or.inr (Or.inr (Or.inr ⟨hz, hx⟩))
  · exact Or.inl (Or.inr ⟨hx, hy⟩)
  · exact Or.inl (Or.inr ⟨hx, hy⟩)

/-- **Universal 5-Point Line-Separation Pigeonhole Lemma**:
For any two points $p, q \in \mathbb{R}^2$ and any three points $a, b, c \in \mathbb{R}^2$
each non-collinear with $\{p, q\}$, at least two of $\{a, b, c\}$ lie on the same open side
of the line $pq$. (Port of Erdos107Unified435.lean L1902–1912.) -/
theorem three_vertices_same_open_side_of_line {p q a b c : ℝ²}
    (ha : ¬ Collinear ℝ ({p, q, a} : Set ℝ²))
    (hb : ¬ Collinear ℝ ({p, q, b} : Set ℝ²))
    (hc : ¬ Collinear ℝ ({p, q, c} : Set ℝ²)) :
    ((0 < lineSide p q a ∧ 0 < lineSide p q b) ∨ (lineSide p q a < 0 ∧ lineSide p q b < 0)) ∨
    ((0 < lineSide p q b ∧ 0 < lineSide p q c) ∨ (lineSide p q b < 0 ∧ lineSide p q c < 0)) ∨
    ((0 < lineSide p q c ∧ 0 < lineSide p q a) ∨ (lineSide p q c < 0 ∧ lineSide p q a < 0)) :=
  pigeonhole_three_signs
    (lineSide_pos_or_neg_of_not_collinear ha)
    (lineSide_pos_or_neg_of_not_collinear hb)
    (lineSide_pos_or_neg_of_not_collinear hc)

/-- Any two outer vertices $u, v \in P$ and two distinct points $p, q \in P$ lying on the
positive open side of $u \to v$ such that $u, v$ lie on the same open side of
$p \leftrightarrow q$ form a convex 4-gon in $P$.
(Port of Erdos107Unified435.lean L1918–1940.) -/
theorem hasConvexFourGon_of_same_open_side_edge {P : Set ℝ²} {u v p q : ℝ²}
    (huP : u ∈ P) (hvP : v ∈ P) (hpP : p ∈ P) (hqP : q ∈ P) (hpq : p ≠ q)
    (huvp : 0 < lineSide u v p) (huvq : 0 < lineSide u v q)
    (hsame : (0 < lineSide p q u ∧ 0 < lineSide p q v) ∨
      (lineSide p q u < 0 ∧ lineSide p q v < 0)) :
    HasConvexNGon 4 P := by
  have huv : u ≠ v := by
    intro h; subst h; dsimp [lineSide] at huvp; linarith
  have hup : u ≠ p := by
    intro h; subst h; dsimp [lineSide] at huvp; linarith
  have huq : u ≠ q := by
    intro h; subst h; dsimp [lineSide] at huvq; linarith
  have hvp : v ≠ p := by
    intro h; subst h; dsimp [lineSide] at huvp; linarith
  have hvq : v ≠ q := by
    intro h; subst h; dsimp [lineSide] at huvq; linarith
  refine ⟨{u, v, p, q}, ?_, ?_, ?_⟩
  · simp [huv, hup, huq, hvp, hvq, hpq]
  · intro x hx
    simp only [Finset.coe_insert, Finset.coe_singleton, Set.mem_insert_iff,
      Set.mem_singleton_iff] at hx
    rcases hx with rfl | rfl | rfl | rfl <;> assumption
  · simpa using convexIndep_four_of_same_open_side huvp huvq hsame

/-- **Universal 5-Point 3-Outer + 2-Interior Happy Ending Theorem**:
In any point set $P \subseteq \mathbb{R}^2$, if $a, b, c \in P$ form a positively oriented
triangle containing two distinct interior points $p, q \in P$ such that none of $a, b, c$ is
collinear with $\{p, q\}$, then $P$ contains the vertices of a convex 4-gon
(`HasConvexNGon 4 P`). (Port of Erdos107Unified435.lean L1948–1960.) -/
theorem hasConvexFourGon_of_triangle_two_interior {P : Set ℝ²} {a b c p q : ℝ²}
    (haP : a ∈ P) (hbP : b ∈ P) (hcP : c ∈ P) (hpP : p ∈ P) (hqP : q ∈ P) (hpq : p ≠ q)
    (habp : 0 < lineSide a b p) (habq : 0 < lineSide a b q)
    (hbcp : 0 < lineSide b c p) (hbcq : 0 < lineSide b c q)
    (hcap : 0 < lineSide c a p) (hcaq : 0 < lineSide c a q)
    (hnca : ¬ Collinear ℝ ({p, q, a} : Set ℝ²))
    (hncb : ¬ Collinear ℝ ({p, q, b} : Set ℝ²))
    (hncc : ¬ Collinear ℝ ({p, q, c} : Set ℝ²)) :
    HasConvexNGon 4 P := by
  rcases three_vertices_same_open_side_of_line hnca hncb hncc with hab | hbc | hca
  · exact hasConvexFourGon_of_same_open_side_edge haP hbP hpP hqP hpq habp habq hab
  · exact hasConvexFourGon_of_same_open_side_edge hbP hcP hpP hqP hpq hbcp hbcq hbc
  · exact hasConvexFourGon_of_same_open_side_edge hcP haP hpP hqP hpq hcap hcaq hca

/-! ## §16 THE `InPosTriangle` BARYCENTRIC CALCULUS
(fresh port of Blueprint107.lean §1 L85–244: the oriented-area triangle-sum
identity, the two five-point Plücker/Cramer syzygies, strict containment
transitivity, the explicit Cramer barycentric identity, convex-hull
membership, and the interior-point non-convexity criterion) -/

/-- A point $d \in \mathbb{R}^2$ lies in the open interior of the positively oriented
triangle $(a, b, c)$ if it lies on the strictly positive open side of all three directed
edges $a \to b$, $b \to c$, and $c \to a$. (Port of Blueprint107.lean L87–88.) -/
def InPosTriangle (a b c d : ℝ²) : Prop :=
  0 < lineSide a b d ∧ 0 < lineSide b c d ∧ 0 < lineSide c a d

/-- **Universal Oriented-Area Triangle-Sum Identity**:
For any four points $a, b, c, d \in \mathbb{R}^2$, the signed areas of $\triangle abd$,
$\triangle bcd$, and $\triangle cad$ sum identically to the signed area of
$\triangle abc$. (Port of Blueprint107.lean L93–95.) -/
theorem lineSide_triangle_sum (a b c d : ℝ²) :
    lineSide a b d + lineSide b c d + lineSide c a d = lineSide a b c := by
  dsimp [lineSide]; ring

/-- **Five-Point Plücker/Cramer Identity at Vertex $b$**:
For any five points $a, b, c, d, e \in \mathbb{R}^2$,
$\operatorname{lineSide}(a,b,c)\operatorname{lineSide}(b,e,d) =
\operatorname{lineSide}(a,b,d)\operatorname{lineSide}(b,e,c) +
\operatorname{lineSide}(b,c,d)\operatorname{lineSide}(a,b,e)$.
(Port of Blueprint107.lean L102–105.) -/
theorem lineSide_cramer_right (a b c d e : ℝ²) :
    lineSide a b c * lineSide b e d =
      lineSide a b d * lineSide b e c + lineSide b c d * lineSide a b e := by
  dsimp [lineSide]; ring

/-- **Five-Point Plücker/Cramer Identity at Vertex $a$**:
For any five points $a, b, c, d, e \in \mathbb{R}^2$,
$\operatorname{lineSide}(a,b,c)\operatorname{lineSide}(e,a,d) =
\operatorname{lineSide}(c,a,d)\operatorname{lineSide}(a,b,e) +
\operatorname{lineSide}(a,b,d)\operatorname{lineSide}(e,a,c)$.
(Port of Blueprint107.lean L112–115.) -/
theorem lineSide_cramer_left (a b c d e : ℝ²) :
    lineSide a b c * lineSide e a d =
      lineSide c a d * lineSide a b e + lineSide a b d * lineSide e a c := by
  dsimp [lineSide]; ring

/-- Cyclic permutation of the outer triangle vertices preserves `InPosTriangle`.
(Port of Blueprint107.lean L120–122.) -/
theorem inPosTriangle_cycle {a b c d : ℝ²} (h : InPosTriangle a b c d) :
    InPosTriangle b c a d :=
  ⟨h.2.1, h.2.2, h.1⟩

/-- Any triangle $(a, b, c)$ containing a point $d$ with `InPosTriangle a b c d` is
positively oriented. (Port of Blueprint107.lean L127–130.) -/
theorem inPosTriangle_pos_outer {a b c d : ℝ²} (h : InPosTriangle a b c d) :
    0 < lineSide a b c := by
  have hsum := lineSide_triangle_sum a b c d
  linarith [h.1, h.2.1, h.2.2]

/-- **Strict Triangle-Containment Transitivity (`inPosTriangle_trans`)**:
If $d$ lies strictly inside $\triangle abc$ and $c$ lies strictly inside $\triangle abe$,
then $d$ also lies strictly inside $\triangle abe$.
(Port of Blueprint107.lean L137–155.) -/
theorem inPosTriangle_trans {a b c d e : ℝ²}
    (hd : InPosTriangle a b c d) (hc : InPosTriangle a b e c) :
    InPosTriangle a b e d := by
  have habc : 0 < lineSide a b c := hc.1
  have habe : 0 < lineSide a b e := inPosTriangle_pos_outer hc
  have habd : 0 < lineSide a b d := hd.1
  have hbcd : 0 < lineSide b c d := hd.2.1
  have hcad : 0 < lineSide c a d := hd.2.2
  have hbec : 0 < lineSide b e c := hc.2.1
  have heac : 0 < lineSide e a c := hc.2.2
  have hcr₁ := lineSide_cramer_right a b c d e
  have hcr₂ := lineSide_cramer_left a b c d e
  have hprod₁ : 0 < lineSide a b c * lineSide b e d := by
    rw [hcr₁]; positivity
  have hprod₂ : 0 < lineSide a b c * lineSide e a d := by
    rw [hcr₂]; positivity
  exact ⟨habd,
    pos_of_mul_pos_right hprod₁ (le_of_lt habc),
    pos_of_mul_pos_right hprod₂ (le_of_lt habc)⟩

/-- **Universal Cramer Barycentric Identity in $\mathbb{R}^2$**:
For any non-collinear triple $(a, b, c)$ with $\operatorname{lineSide}(a,b,c) \ne 0$ and
any point $p \in \mathbb{R}^2$, $p$ equals the affine combination of $a, b, c$ with weights
$\operatorname{lineSide}(b,c,p)/\operatorname{lineSide}(a,b,c)$,
$\operatorname{lineSide}(c,a,p)/\operatorname{lineSide}(a,b,c)$, and
$\operatorname{lineSide}(a,b,p)/\operatorname{lineSide}(a,b,c)$.
(Port of Blueprint107.lean L163–172.) -/
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

/-- **Universal Positive-Triangle Convex-Hull Membership Theorem**:
Whenever `InPosTriangle a b c p` holds, $p \in \operatorname{convexHull}\,\mathbb{R}\,
\{a, b, c\}$. (Port of Blueprint107.lean L178–217; the `subset_convexHull` /
`convex_convexHull` arguments use the signature-agnostic named form
`(𝕜 := ℝ)` — see the header's micro-adaptation list.) -/
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
      field_simp [habc_ne, hbcca_ne]
  rw [hdecomp]
  have h_conv := convex_convexHull (𝕜 := ℝ) ({a, b, c} : Set ℝ²)
  have ha_mem : a ∈ convexHull ℝ ({a, b, c} : Set ℝ²) :=
    subset_convexHull (𝕜 := ℝ) _ (by simp)
  have hb_mem : b ∈ convexHull ℝ ({a, b, c} : Set ℝ²) :=
    subset_convexHull (𝕜 := ℝ) _ (by simp)
  have hc_mem : c ∈ convexHull ℝ ({a, b, c} : Set ℝ²) :=
    subset_convexHull (𝕜 := ℝ) _ (by simp)
  have hmid :
      (lineSide b c p / (lineSide b c p + lineSide c a p)) • a +
      (lineSide c a p / (lineSide b c p + lineSide c a p)) • b ∈
        convexHull ℝ ({a, b, c} : Set ℝ²) := by
    apply h_conv ha_mem hb_mem
    · exact div_nonneg (le_of_lt hbc) (le_of_lt hbcca)
    · exact div_nonneg (le_of_lt hca) (le_of_lt hbcca)
    · field_simp [hbcca_ne]
  apply h_conv hmid hc_mem
  · exact div_nonneg (le_of_lt hbcca) (le_of_lt habc)
  · exact div_nonneg (le_of_lt hab) (le_of_lt habc)
  · field_simp [habc_ne]; linarith

/-- **Universal Interior-Point Non-Convexity Criterion**:
If $a, b, c, p \in S$ satisfy `InPosTriangle a b c p`, then $S$ is not convex independent
(`¬ ConvexIndep S`). (Port of Blueprint107.lean L223–242.) -/
theorem not_convexIndep_of_inPosTriangle {S : Set ℝ²} {a b c p : ℝ²}
    (haS : a ∈ S) (hbS : b ∈ S) (hcS : c ∈ S) (hpS : p ∈ S)
    (h : InPosTriangle a b c p) :
    ¬ ConvexIndep S := by
  intro hci
  apply hci p hpS
  have hpa : p ≠ a := by
    intro heq; subst heq; have := h.1; dsimp [lineSide] at this; linarith
  have hpb : p ≠ b := by
    intro heq; subst heq; have := h.1; dsimp [lineSide] at this; linarith
  have hpc : p ≠ c := by
    intro heq; subst heq; have := h.2.1; dsimp [lineSide] at this; linarith
  have hsub : ({a, b, c} : Set ℝ²) ⊆ S \ {p} := by
    intro z hz
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hz
    rcases hz with rfl | rfl | rfl
    · exact ⟨haS, hpa.symm⟩
    · exact ⟨hbS, hpb.symm⟩
    · exact ⟨hcS, hpc.symm⟩
  exact convexHull_mono hsub (inPosTriangle_mem_convexHull h)

/-! ## §17 THE KLEIN 4-POINT WITNESS AND THE `cardSet` CLOSURE LAWS
(fresh port of Erdos107Unified435.lean L49–223 subset + §1 L364–511: the
monotonicity/closure laws for `NonTrilinear` / `HasConvexNGon` / `cardSet`,
the converse cross-product criterion, the explicit 4-point general-position
non-convex configuration $\{(0,0),(3,0),(0,3),(1,1)\}$ with the centroid
in the hull of the outer triangle, $4 \notin \mathrm{cardSet}(4)$, and
$5 \le f(4)$) -/

/-- `NonTrilinear` is hereditary under subset inclusion.
(Port of Erdos107Unified435.lean L49–51.) -/
theorem nonTrilinear_mono {P Q : Set ℝ²} (hPQ : P ⊆ Q) (hQ : NonTrilinear Q) :
    NonTrilinear P :=
  fun _ hx _ hy _ hz hxy hyz hxz => hQ (hPQ hx) (hPQ hy) (hPQ hz) hxy hyz hxz

/-- Containing a convex $n$-gon is monotone increasing in the ambient point set.
(Port of Erdos107Unified435.lean L207–210.) -/
theorem hasConvexNGon_mono_pts {n : ℕ} {P Q : Set ℝ²}
    (h : HasConvexNGon n P) (hPQ : P ⊆ Q) : HasConvexNGon n Q := by
  rcases h with ⟨S, hcard, hsub, hconv⟩
  exact ⟨S, hcard, hsub.trans hPQ, hconv⟩

/-- Upward closure of `cardSet n`: if $N_1 \le N_2$ and $N_1 \in \text{cardSet}(n)$, then
$N_2 \in \text{cardSet}(n)$. (Port of Erdos107Unified435.lean L215–221; the vendor's
`Nat.le_trans_eq` step is hardened to `omega` — see the header's
micro-adaptation list.) -/
theorem cardSet_upward_closed {n N₁ N₂ : ℕ}
    (hle : N₁ ≤ N₂) (hN₁ : N₁ ∈ cardSet n) : N₂ ∈ cardSet n := by
  intro pts hcard hnontri
  obtain ⟨pts₁, hsub, hcard₁⟩ :=
    Finset.exists_subset_card_eq (by omega : N₁ ≤ pts.card)
  have hcoe : (pts₁ : Set ℝ²) ⊆ (pts : Set ℝ²) := Finset.coe_subset.mpr hsub
  have hnontri₁ : NonTrilinear (pts₁ : Set ℝ²) := nonTrilinear_mono hcoe hnontri
  exact hasConvexNGon_mono_pts (hN₁ pts₁ hcard₁ hnontri₁) hcoe

/-- Non-vanishing 2D cross product certifies non-collinearity of three points in
$\mathbb{R}^2$. (Port of Erdos107Unified435.lean L119–122; the converse
`cross_eq_zero_of_collinear` is already in the cloned cone §1.) -/
theorem not_collinear_of_cross_ne_zero {a b c : ℝ²}
    (h : (b 0 - a 0) * (c 1 - a 1) - (b 1 - a 1) * (c 0 - a 0) ≠ 0) :
    ¬ Collinear ℝ ({a, b, c} : Set ℝ²) :=
  fun hcoll => h (cross_eq_zero_of_collinear hcoll)

/-- Origin vertex $(0, 0)$ of the outer triangle.
(Port of Erdos107Unified435.lean L364.) -/
def ptO : ℝ² := mkPt 0 0

/-- Right vertex $(3, 0)$ of the outer triangle.
(Port of Erdos107Unified435.lean L367.) -/
def ptA : ℝ² := mkPt 3 0

/-- Top vertex $(0, 3)$ of the outer triangle.
(Port of Erdos107Unified435.lean L370.) -/
def ptB : ℝ² := mkPt 0 3

/-- Interior centroid $(1, 1)$ of the outer triangle.
(Port of Erdos107Unified435.lean L373.) -/
def ptC : ℝ² := mkPt 1 1

/-- The 4-point Esther Klein witness $\{(0,0), (3,0), (0,3), (1,1)\}$ in general position
forming a triangle with an interior point.
(Port of Erdos107Unified435.lean L377.) -/
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

/-- Exact barycentric representation of $(1, 1)$ as a convex combination of
$(0, 0), (3, 0), (0, 3)$. (Port of Erdos107Unified435.lean L427–430.) -/
theorem ptC_eq_barycentric :
    ptC = (1 / 3 : ℝ) • ptO + (2 / 3 : ℝ) • ((1 / 2 : ℝ) • ptA + (1 / 2 : ℝ) • ptB) := by
  ext i
  fin_cases i <;> simp [ptO, ptA, ptB, ptC, mkPt] <;> norm_num

/-- The centroid $(1, 1)$ lies in the convex hull of the three outer vertices.
(Port of Erdos107Unified435.lean L435–449; the `subset_convexHull` /
`convex_convexHull` arguments use the signature-agnostic named form
`(𝕜 := ℝ)` — see the header's micro-adaptation list.) -/
theorem ptC_mem_convexHull_triangle :
    ptC ∈ convexHull ℝ ({ptO, ptA, ptB} : Set ℝ²) := by
  have hconv : Convex ℝ (convexHull ℝ ({ptO, ptA, ptB} : Set ℝ²)) :=
    convex_convexHull (𝕜 := ℝ) _
  have hO : ptO ∈ convexHull ℝ ({ptO, ptA, ptB} : Set ℝ²) :=
    subset_convexHull (𝕜 := ℝ) _ (by simp)
  have hA : ptA ∈ convexHull ℝ ({ptO, ptA, ptB} : Set ℝ²) :=
    subset_convexHull (𝕜 := ℝ) _ (by simp)
  have hB : ptB ∈ convexHull ℝ ({ptO, ptA, ptB} : Set ℝ²) :=
    subset_convexHull (𝕜 := ℝ) _ (by simp)
  have hAB : (1 / 2 : ℝ) • ptA + (1 / 2 : ℝ) • ptB ∈
      convexHull ℝ ({ptO, ptA, ptB} : Set ℝ²) :=
    hconv hA hB (by norm_num) (by norm_num) (by norm_num)
  rw [ptC_eq_barycentric]
  exact hconv hO hAB (by norm_num) (by norm_num) (by norm_num)

/-- The 4-point configuration `kleinFourPts` is not convex independent.
(Port of Erdos107Unified435.lean L454–464.) -/
theorem not_convexIndep_kleinFourPts :
    ¬ ConvexIndep (kleinFourPts : Set ℝ²) := by
  intro hci
  have hC : ptC ∈ (kleinFourPts : Set ℝ²) := by simp [kleinFourPts]
  refine hci ptC hC (convexHull_mono ?_ ptC_mem_convexHull_triangle)
  intro x hx
  simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hx
  rcases hx with rfl | rfl | rfl
  · simp [kleinFourPts, ptO_ne_ptC]
  · simp [kleinFourPts, ptA_ne_ptC]
  · simp [kleinFourPts, ptB_ne_ptC]

/-- No three points of `kleinFourPts` are collinear.
(Port of Erdos107Unified435.lean L469–482.) -/
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
    | (apply not_collinear_of_cross_ne_zero; norm_num [ptO, ptA, ptB, ptC, mkPt_zero, mkPt_one])

/-- $4 \notin \text{cardSet}(4)$: four points in general position need not form a convex
quadrilateral. (Port of Erdos107Unified435.lean L487–495.) -/
theorem four_not_mem_cardSet_four : (4 : ℕ) ∉ cardSet 4 := by
  intro h4
  obtain ⟨S, hScard, hSsub, hSconv⟩ :=
    h4 kleinFourPts kleinFourPts_card kleinFourPts_nonTrilinear
  have hkcard := kleinFourPts_card
  have hSeq : S = kleinFourPts :=
    Finset.eq_of_subset_of_card_le (Finset.coe_subset.mp hSsub) (by omega)
  subst hSeq
  exact not_convexIndep_kleinFourPts hSconv

/-- Every member of $\text{cardSet}(4)$ is at least $5$. **Cone deviation #2**: proved via
`cardSet_upward_closed` (mirroring Blueprint107.lean L740
`nine_le_of_mem_cardSet_five`) instead of the vendor's parabola-based
`le_of_mem_cardSet` — see the header's deviation list. -/
theorem five_le_of_mem_cardSet_four {N : ℕ} (hN : N ∈ cardSet 4) : 5 ≤ N := by
  by_contra hlt
  have hle : N ≤ 4 := by omega
  exact four_not_mem_cardSet_four (cardSet_upward_closed hle hN)

/-- Lower bound $5 \le f(4)$ (i.e. $2^{4-2} + 1 \le f(4)$) whenever $\text{cardSet}(4)$ is
nonempty. (Port of Erdos107Unified435.lean L508–509.) -/
theorem five_le_f_four (hne : (cardSet 4).Nonempty) : 5 ≤ f 4 :=
  le_csInf hne fun _ hN => five_le_of_mem_cardSet_four hN

/-! ## §18 ESTHER KLEIN'S 5-POINT HAPPY ENDING THEOREM (`5 ∈ cardSet 4`, `f 4 = 5`)
(fresh port of Blueprint107.lean §2 L246–461 + Erdos107Unified435.lean
L1610–1615: the DEDICATED tight n = 4 upper argument — the universal
4-point convex-quadrilateral-or-interior-triangle dichotomy, the
3-outer + 2-interior pigeonhole, the fifth-point interior case split, and
the sInf assembly. The general ES upper bound only gives f(4) ≤ 7 — this
is the tight 5) -/

/-- When $d$ lies on the positive side of $a \to b$ and $b \to c$ and on the negative side
of $c \to a$ around a positively oriented triangle $(a, b, c)$, the four points
$\{a, b, c, d\}$ form a convex 4-gon in $P$.
(Port of Blueprint107.lean L250–263.) -/
theorem hasConvexFourGon_of_two_pos_one_neg {P : Set ℝ²} {a b c d : ℝ²}
    (ha : a ∈ P) (hb : b ∈ P) (hc : c ∈ P) (hd : d ∈ P)
    (habc : 0 < lineSide a b c)
    (habd : 0 < lineSide a b d) (hbcd : 0 < lineSide b c d) (hcad : lineSide c a d < 0) :
    HasConvexNGon 4 P := by
  have hcd : c ≠ d := by
    intro h; subst h; dsimp [lineSide] at hcad; linarith
  have hcda : 0 < lineSide c d a := by
    have h : lineSide c d a = - lineSide c a d := by dsimp [lineSide]; ring
    linarith
  have hcdb : 0 < lineSide c d b := by
    have h : lineSide c d b = lineSide b c d := by dsimp [lineSide]; ring
    linarith
  exact hasConvexFourGon_of_same_open_side_edge ha hb hc hd hcd habc habd (Or.inl ⟨hcda, hcdb⟩)

/-- **Universal Four-Point Convex-Quadrilateral or Interior-Triangle Dichotomy**:
For any positively oriented triangle $(a, b, c)$ in $P$ and any fourth point $d \in P$
non-collinear with the three edges of $\triangle abc$, either $\{a, b, c, d\}$ forms a
convex 4-gon in $P$, or one of the four points lies strictly inside the positively
oriented triangle formed by the other three.
(Port of Blueprint107.lean L271–308.) -/
theorem four_point_pos_triangle_dichotomy {P : Set ℝ²} {a b c d : ℝ²}
    (ha : a ∈ P) (hb : b ∈ P) (hc : c ∈ P) (hd : d ∈ P)
    (habc : 0 < lineSide a b c)
    (habd_nc : ¬ Collinear ℝ ({a, b, d} : Set ℝ²))
    (hbcd_nc : ¬ Collinear ℝ ({b, c, d} : Set ℝ²))
    (hcad_nc : ¬ Collinear ℝ ({c, a, d} : Set ℝ²)) :
    HasConvexNGon 4 P ∨
    InPosTriangle a b c d ∨
    InPosTriangle a b d c ∨
    InPosTriangle b c d a ∨
    InPosTriangle c a d b := by
  have hbca : 0 < lineSide b c a := by rw [lineSide_cycle]; exact habc
  have hcab : 0 < lineSide c a b := by rw [lineSide_cycle]; exact hbca
  rcases lineSide_pos_or_neg_of_not_collinear habd_nc with s1p | s1n <;>
  rcases lineSide_pos_or_neg_of_not_collinear hbcd_nc with s2p | s2n <;>
  rcases lineSide_pos_or_neg_of_not_collinear hcad_nc with s3p | s3n
  · exact Or.inr (Or.inl ⟨s1p, s2p, s3p⟩)
  · exact Or.inl (hasConvexFourGon_of_two_pos_one_neg ha hb hc hd habc s1p s2p s3n)
  · exact Or.inl (hasConvexFourGon_of_two_pos_one_neg hc ha hb hd hcab s3p s1p s2n)
  · right; right; left
    refine ⟨habc, ?_, ?_⟩
    · rw [lineSide_swap_right]; linarith
    · have h : lineSide d a c = - lineSide c a d := by dsimp [lineSide]; ring
      linarith
  · exact Or.inl (hasConvexFourGon_of_two_pos_one_neg hb hc ha hd hbca s2p s3p s1n)
  · right; right; right; left
    refine ⟨hbca, ?_, ?_⟩
    · rw [lineSide_swap_right]; linarith
    · have h : lineSide d b a = - lineSide a b d := by dsimp [lineSide]; ring
      linarith
  · right; right; right; right
    refine ⟨hcab, ?_, ?_⟩
    · rw [lineSide_swap_right]; linarith
    · have h : lineSide d c b = - lineSide b c d := by dsimp [lineSide]; ring
      linarith
  · exfalso
    have hsum := lineSide_triangle_sum a b c d
    linarith

/-- In any `NonTrilinear` point set $P$, two distinct points $p \ne q$ satisfying
`InPosTriangle a b c p` and `InPosTriangle a b c q` force a convex 4-gon in $P$.
(Port of Blueprint107.lean L314–335.) -/
theorem hasConvexFourGon_of_two_inPosTriangle {P : Set ℝ²} {a b c p q : ℝ²}
    (haP : a ∈ P) (hbP : b ∈ P) (hcP : c ∈ P) (hpP : p ∈ P) (hqP : q ∈ P)
    (hnt : NonTrilinear P) (hpq : p ≠ q)
    (hp : InPosTriangle a b c p) (hq : InPosTriangle a b c q) :
    HasConvexNGon 4 P := by
  have hpa : p ≠ a := by
    intro h; subst h; have := hp.1; dsimp [lineSide] at this; linarith
  have hqa : q ≠ a := by
    intro h; subst h; have := hq.1; dsimp [lineSide] at this; linarith
  have hpb : p ≠ b := by
    intro h; subst h; have := hp.1; dsimp [lineSide] at this; linarith
  have hqb : q ≠ b := by
    intro h; subst h; have := hq.1; dsimp [lineSide] at this; linarith
  have hpc : p ≠ c := by
    intro h; subst h; have := hp.2.1; dsimp [lineSide] at this; linarith
  have hqc : q ≠ c := by
    intro h; subst h; have := hq.2.1; dsimp [lineSide] at this; linarith
  exact hasConvexFourGon_of_triangle_two_interior haP hbP hcP hpP hqP hpq
    hp.1 hq.1 hp.2.1 hq.2.1 hp.2.2 hq.2.2
    (hnt hpP hqP haP hpq hqa hpa)
    (hnt hpP hqP hbP hpq hqb hpb)
    (hnt hpP hqP hcP hpq hqc hpc)

/-- If $d \in P$ lies strictly inside $\triangle abc$ (`InPosTriangle a b c d`), then
adjoining any fifth distinct point $e \in P$ in a `NonTrilinear` point set $P$ forces
`HasConvexNGon 4 P`. (Port of Blueprint107.lean L341–373.) -/
theorem hasConvexFourGon_of_inPosTriangle_and_fifth_point {P : Set ℝ²} {a b c d e : ℝ²}
    (haP : a ∈ P) (hbP : b ∈ P) (hcP : c ∈ P) (hdP : d ∈ P) (heP : e ∈ P)
    (hnt : NonTrilinear P) (hd : InPosTriangle a b c d)
    (hae : a ≠ e) (hbe : b ≠ e) (hce : c ≠ e) (hde : d ≠ e) :
    HasConvexNGon 4 P := by
  have habc : 0 < lineSide a b c := inPosTriangle_pos_outer hd
  have hab : a ≠ b := by
    intro h; subst h; dsimp [lineSide] at habc; linarith
  have hbc : b ≠ c := by
    intro h; subst h; dsimp [lineSide] at habc; linarith
  have hca : c ≠ a := by
    intro h; subst h; dsimp [lineSide] at habc; linarith
  have had : a ≠ d := by
    intro h; subst h; have := hd.1; dsimp [lineSide] at this; linarith
  have hbd : b ≠ d := by
    intro h; subst h; have := hd.1; dsimp [lineSide] at this; linarith
  have hcd : c ≠ d := by
    intro h; subst h; have := hd.2.1; dsimp [lineSide] at this; linarith
  rcases four_point_pos_triangle_dichotomy haP hbP hcP heP habc
      (hnt haP hbP heP hab hbe hae)
      (hnt hbP hcP heP hbc hce hbe)
      (hnt hcP haP heP hca hae hce) with
    h4 | he | habec | hbcea | hcaeb
  · exact h4
  · exact hasConvexFourGon_of_two_inPosTriangle haP hbP hcP hdP heP hnt hde hd he
  · exact hasConvexFourGon_of_two_inPosTriangle haP hbP heP hcP hdP hnt hcd
      habec (inPosTriangle_trans hd habec)
  · have hd_bca : InPosTriangle b c a d := inPosTriangle_cycle hd
    exact hasConvexFourGon_of_two_inPosTriangle hbP hcP heP haP hdP hnt had
      hbcea (inPosTriangle_trans hd_bca hbcea)
  · have hd_cab : InPosTriangle c a b d := inPosTriangle_cycle (inPosTriangle_cycle hd)
    exact hasConvexFourGon_of_two_inPosTriangle hcP haP heP hbP hdP hnt hbd
      hcaeb (inPosTriangle_trans hd_cab hcaeb)

/-- Any five distinct points $a, b, c, d, e$ in a `NonTrilinear` set $P$ with
$0 < \operatorname{lineSide}(a,b,c)$ contain a convex 4-gon.
(Port of Blueprint107.lean L379–395.) -/
theorem hasConvexFourGon_of_pos_outer_and_two_points {P : Set ℝ²} {a b c d e : ℝ²}
    (haP : a ∈ P) (hbP : b ∈ P) (hcP : c ∈ P) (hdP : d ∈ P) (heP : e ∈ P)
    (hnt : NonTrilinear P) (habc : 0 < lineSide a b c)
    (hab : a ≠ b) (hbc : b ≠ c) (hca : c ≠ a)
    (had : a ≠ d) (hbd : b ≠ d) (hcd : c ≠ d)
    (hae : a ≠ e) (hbe : b ≠ e) (hce : c ≠ e) (hde : d ≠ e) :
    HasConvexNGon 4 P := by
  rcases four_point_pos_triangle_dichotomy haP hbP hcP hdP habc
      (hnt haP hbP hdP hab hbd had)
      (hnt hbP hcP hdP hbc hcd hbd)
      (hnt hcP haP hdP hca had hcd) with
    h4 | habcd | habdc | hbcda | hcadb
  · exact h4
  · exact hasConvexFourGon_of_inPosTriangle_and_fifth_point haP hbP hcP hdP heP hnt habcd hae hbe hce hde
  · exact hasConvexFourGon_of_inPosTriangle_and_fifth_point haP hbP hdP hcP heP hnt habdc hae hbe hde hce
  · exact hasConvexFourGon_of_inPosTriangle_and_fifth_point hbP hcP hdP haP heP hnt hbcda hbe hce hde hae
  · exact hasConvexFourGon_of_inPosTriangle_and_fifth_point hcP haP hdP hbP heP hnt hcadb hce hae hde hbe

/-- **Esther Klein's 5-Point Happy Ending Theorem for Distinct Points**:
Any five pairwise distinct points $a, b, c, d, e$ in a `NonTrilinear` planar set
$P \subseteq \mathbb{R}^2$ contain the vertices of a convex 4-gon
(`HasConvexNGon 4 P`). (Port of Blueprint107.lean L402–414.) -/
theorem hasConvexFourGon_of_five_distinct_nonTrilinear {P : Set ℝ²} {a b c d e : ℝ²}
    (haP : a ∈ P) (hbP : b ∈ P) (hcP : c ∈ P) (hdP : d ∈ P) (heP : e ∈ P)
    (hnt : NonTrilinear P)
    (hab : a ≠ b) (hbc : b ≠ c) (hca : c ≠ a)
    (had : a ≠ d) (hbd : b ≠ d) (hcd : c ≠ d)
    (hae : a ≠ e) (hbe : b ≠ e) (hce : c ≠ e) (hde : d ≠ e) :
    HasConvexNGon 4 P := by
  rcases lineSide_pos_or_neg_of_not_collinear (hnt haP hbP hcP hab hbc hca.symm) with habc | hbac
  · exact hasConvexFourGon_of_pos_outer_and_two_points haP hbP hcP hdP heP hnt habc
      hab hbc hca had hbd hcd hae hbe hce hde
  · have hbac_pos : 0 < lineSide b a c := by rw [lineSide_swap_left]; linarith
    exact hasConvexFourGon_of_pos_outer_and_two_points hbP haP hcP hdP heP hnt hbac_pos
      hab.symm hca.symm hbc.symm hbd had hcd hbe hae hce hde

/-- Extraction of 5 pairwise distinct points from any `pts : Finset ℝ²` with
`pts.card = 5`. (Port of Blueprint107.lean L419–432.) -/
theorem exists_five_distinct_of_card_eq_five {pts : Finset ℝ²} (hcard : pts.card = 5) :
    ∃ a b c d e : ℝ²,
      a ∈ pts ∧ b ∈ pts ∧ c ∈ pts ∧ d ∈ pts ∧ e ∈ pts ∧
      a ≠ b ∧ b ≠ c ∧ c ≠ a ∧
      a ≠ d ∧ b ≠ d ∧ c ≠ d ∧
      a ≠ e ∧ b ≠ e ∧ c ≠ e ∧ d ≠ e := by
  obtain ⟨e, s₄, he_s₄, rfl, hs₄⟩ := Finset.card_eq_succ.mp hcard
  obtain ⟨d, s₃, hd_s₃, rfl, hs₃⟩ := Finset.card_eq_succ.mp hs₄
  obtain ⟨a, b, c, hab, hac, hbc, rfl⟩ := Finset.card_eq_three.mp hs₃
  simp only [Finset.mem_insert, Finset.mem_singleton, not_or] at he_s₄ hd_s₃
  refine ⟨a, b, c, d, e, by simp, by simp, by simp, by simp, by simp,
    hab, hbc, hac.symm,
    Ne.symm hd_s₃.1, Ne.symm hd_s₃.2.1, Ne.symm hd_s₃.2.2,
    Ne.symm he_s₄.2.1, Ne.symm he_s₄.2.2.1, Ne.symm he_s₄.2.2.2, Ne.symm he_s₄.1⟩

/-- **Unconditional 5-Point Happy Ending Membership Theorem (`5 ∈ cardSet 4`)**:
Every 5-point `NonTrilinear` set in $\mathbb{R}^2$ contains a convex 4-gon.
(Port of Blueprint107.lean L438–446.) -/
theorem five_mem_cardSet_four : (5 : ℕ) ∈ cardSet 4 := by
  intro pts hcard hnt
  obtain ⟨a, b, c, d, e, ha, hb, hc, hd, he,
    hab, hbc, hca, had, hbd, hcd, hae, hbe, hce, hde⟩ :=
    exists_five_distinct_of_card_eq_five hcard
  exact hasConvexFourGon_of_five_distinct_nonTrilinear
    (Finset.mem_coe.mpr ha) (Finset.mem_coe.mpr hb) (Finset.mem_coe.mpr hc)
    (Finset.mem_coe.mpr hd) (Finset.mem_coe.mpr he)
    hnt hab hbc hca had hbd hcd hae hbe hce hde

/-- Conditional closure of the 5-point Happy Ending theorem: once
$5 \in \text{cardSet}(4)$ is supplied, $f(4) = 5 = 2^{4-2} + 1$ follows by combining
`Nat.sInf_le` with the unconditional 4-point lower bound `five_le_f_four`.
(Port of Erdos107Unified435.lean L1610–1615.) -/
theorem f_four_eq_five_of_mem_cardSet (h5 : (5 : ℕ) ∈ cardSet 4) :
    f 4 = 5 ∧ f 4 = erdosSzekeresConjectured 4 := by
  have hle : f 4 ≤ 5 := Nat.sInf_le h5
  have hge : 5 ≤ f 4 := five_le_f_four ⟨5, h5⟩
  have heq : f 4 = 5 := le_antisymm hle hge
  exact ⟨heq, heq⟩

/-- **Unconditional Resolution of the 5-Point Happy Ending Value $f(4) = 5$**:
$f(4) = 5$ and $f(4) = \operatorname{erdosSzekeresConjectured}(4) = 2^{4-2} + 1$.
(Port of Blueprint107.lean L452–453.) -/
theorem f_four_eq_five : f 4 = 5 ∧ f 4 = erdosSzekeresConjectured 4 :=
  f_four_eq_five_of_mem_cardSet five_mem_cardSet_four

/-- Direct equation $f(4) = 5$. (Port of Blueprint107.lean L458–459.) -/
theorem f_four_eq_five_unconditional : f 4 = 5 :=
  f_four_eq_five.1

/-! ## §19 THE OFFICIAL ANCHOR `f 3 = 3`
(cone deviation #1: ported VERBATIM from the CI-GREEN official statement
file DM107_Official.lean L106–134 — the collinear x-axis witness with
vacuous `NonTrilinear` via `Set.triplewise_of_encard_lt` — instead of the
vendor's parabola route, which would drag the whole parabola sub-cone in;
`convexIndep_triple_of_not_collinear` is already in the cloned cone §10) -/

/-- **The official anchor** `f 3 = 3` (verbatim from DM107_Official.lean L106–134,
CI-GREEN as `DM107_ANCHORS_GREEN`; both sides: `3 ∈ cardSet 3` via
`convexIndep_triple_of_not_collinear`, and the lower bound via N collinear
x-axis points whose `NonTrilinear` holds vacuously). -/
theorem f_three_eq : f 3 = 3 := by
  -- The substantive bound: 3 ∈ cardSet 3.
  have hmem3 : (3 : ℕ) ∈ cardSet 3 := by
    intro pts hpts hnontri
    obtain ⟨a, b, c, hab, hac, hbc, rfl⟩ := Finset.card_eq_three.mp hpts
    refine ⟨{a, b, c}, by simp [hab, hac, hbc], subset_refl _, ?_⟩
    have hcoerce : (({a, b, c} : Finset ℝ²) : Set ℝ²) = ({a, b, c} : Set ℝ²) := by simp
    have hmem : ∀ {y : ℝ²}, y ∈ ({a, b, c} : Set ℝ²) →
        y ∈ (({a, b, c} : Finset ℝ²) : Set ℝ²) := fun h => hcoerce ▸ h
    have hnc : ¬ Collinear ℝ ({a, b, c} : Set ℝ²) :=
      hnontri (hmem (by simp)) (hmem (by simp)) (hmem (by simp)) hab hbc hac
    rw [hcoerce]
    exact convexIndep_triple_of_not_collinear hab hac hbc hnc
  refine le_antisymm (Nat.sInf_le hmem3) (le_csInf ⟨3, hmem3⟩ fun N hN => ?_)
  -- A set with fewer than 3 points contains no 3-element subset.
  by_contra! hlt
  let f : ℕ → ℝ² := fun i => EuclideanSpace.single 0 (i : ℝ)
  let pts : Finset ℝ² := (Finset.range N).image f
  have hinj : Function.Injective f := fun i j hij => by
    have := congrArg (fun v : ℝ² => v 0) hij; simpa [f] using this
  have hpts_card : pts.card = N := by
    simp [pts, Finset.card_image_of_injOn hinj.injOn]
  have hnontri : NonTrilinear (pts : Set ℝ²) := by
    apply Set.triplewise_of_encard_lt
    rw [Set.encard_coe_eq_coe_finsetCard, hpts_card]
    exact_mod_cast hlt
  obtain ⟨S, hScard, hSsub, _⟩ := hN pts hpts_card hnontri
  have : S.card ≤ pts.card := Finset.card_le_card (by exact_mod_cast hSsub)
  omega

/-! ## §20 THE 8-POINT ERDŐS–SZEKERES (1960) 4-CAP + 4-CUP PENTAGON-FREE
WITNESS (`8 ∉ cardSet 5`, `9 ≤ f 5`) — fresh port of Blueprint107.lean
§3 L519–757 (excluding the four presentational cap/cup lemmas L468–517,
grep-verified unused): the finite-combinatorics extraction lemmas, the
integer witness data, the five `decide` blocks (64 / 512 / 4096 / 4096 /
2 cases), the cap/cup pigeonhole split, and the master no-pentagon
certificate -/

/-- Any finite set $J$ of size at least 3 contains three pairwise distinct elements.
(Port of Blueprint107.lean L520–533.) -/
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

/-- Any finite set $J$ in a linear order with $3 \le |J|$ contains a strictly increasing
triple $a < b < c$. (Port of Blueprint107.lean L538–552.) -/
theorem exists_strict_ordered_triple_of_three_le_card {α : Type*} [LinearOrder α]
    {J : Finset α} (hcard : 3 ≤ J.card) :
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

/-- $x$-coordinates of the 8-point Erdős–Szekeres (1960) 4-cap + 4-cup pentagon-free
witness. (Port of Blueprint107.lean L557.) -/
def esEightX : Fin 8 → ℤ := ![0, 1, 2, 3, 20, 21, 22, 23]

/-- $y$-coordinates of the 8-point Erdős–Szekeres (1960) 4-cap + 4-cup pentagon-free
witness. (Port of Blueprint107.lean L560.) -/
def esEightY : Fin 8 → ℤ := ![0, 3, 5, 6, 100, 97, 95, 94]

/-- The 8-point Erdős–Szekeres point map `Fin 8 → ℝ²`.
(Port of Blueprint107.lean L563–564.) -/
def esEightPt (i : Fin 8) : ℝ² :=
  mkPt (esEightX i : ℝ) (esEightY i : ℝ)

/-- The 8-point Erdős–Szekeres finite point set in $\mathbb{R}^2$.
(Port of Blueprint107.lean L567–568.) -/
def esEightFinset : Finset ℝ² :=
  Finset.univ.image esEightPt

/-- Exact integer oriented-area determinant for triples in `esEightPt`.
(Port of Blueprint107.lean L571–573.) -/
def esEightCross (i j k : Fin 8) : ℤ :=
  (esEightX j - esEightX i) * (esEightY k - esEightY i) -
  (esEightY j - esEightY i) * (esEightX k - esEightX i)

/-- `lineSide` on `esEightPt` equals the cast of `esEightCross`.
(Port of Blueprint107.lean L576–581.) -/
theorem lineSide_esEightPt (i j k : Fin 8) :
    lineSide (esEightPt i) (esEightPt j) (esEightPt k) = (esEightCross i j k : ℝ) := by
  dsimp [lineSide, esEightPt, esEightCross]
  simp only [mkPt_zero, mkPt_one]
  push_cast
  ring

theorem esEightX_ne_of_ne : ∀ i j : Fin 8, i ≠ j → esEightX i ≠ esEightX j := by
  decide

/-- `esEightPt` is injective on `Fin 8`. (Port of Blueprint107.lean L591–596.) -/
theorem esEightPt_injective : Function.Injective esEightPt := by
  intro i j hij
  by_contra hne
  have hx := congrArg (fun p : ℝ² => p 0) hij
  simp only [esEightPt, mkPt_zero, Int.cast_inj] at hx
  exact esEightX_ne_of_ne i j hne hx

/-- `esEightFinset` has cardinality 8. (Port of Blueprint107.lean L601–603.) -/
theorem esEightFinset_card : esEightFinset.card = 8 := by
  dsimp [esEightFinset]
  rw [Finset.card_image_of_injective _ esEightPt_injective, Finset.card_univ, Fintype.card_fin]

/-- No three distinct indices in `Fin 8` have zero oriented area in `esEightPt`.
(Port of Blueprint107.lean L608–610.) -/
theorem esEightCross_ne_zero_of_distinct :
    ∀ i j k : Fin 8, i ≠ j → j ≠ k → i ≠ k → esEightCross i j k ≠ 0 := by
  decide

/-- `esEightFinset` is in general position (`NonTrilinear`).
(Port of Blueprint107.lean L615–629; the vendor's
`rw [esEightFinset, Finset.coe_image]` is hardened to `simp only […,
Set.mem_image]` — see the header's micro-adaptation list.) -/
theorem esEightFinset_nonTrilinear : NonTrilinear (esEightFinset : Set ℝ²) := by
  intro a ha b hb c hc hab hbc hac
  simp only [esEightFinset, Finset.coe_image, Set.mem_image] at ha hb hc
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

/-- Every ordered triple $i < j < k < 4$ in the 4-cap and every index $u \ge 4$ in the
4-cup place $j$ strictly inside the positively oriented triangle $(i, k, u)$.
(Port of Blueprint107.lean L635–639; the 4096-case `decide` is kept
vendor-faithful — AUDIT_W85_107C.md risk 1.) -/
theorem esEight_cap_triple_with_cup_pt :
    ∀ i j k u : Fin 8,
      i < j → j < k → k.val < 4 → 4 ≤ u.val →
      0 < esEightCross i k j ∧ 0 < esEightCross k u j ∧ 0 < esEightCross u i j := by
  decide

/-- Every ordered triple $4 \le u < v < w$ in the 4-cup and every index $i < 4$ in the
4-cap place $v$ strictly inside the positively oriented triangle $(u, i, w)$.
(Port of Blueprint107.lean L645–649; the 4096-case `decide` is kept
vendor-faithful — AUDIT_W85_107C.md risk 1.) -/
theorem esEight_cup_triple_with_cap_pt :
    ∀ u v w i : Fin 8,
      u < v → v < w → 4 ≤ u.val → i.val < 4 →
      0 < esEightCross u i v ∧ 0 < esEightCross i w v ∧ 0 < esEightCross w u v := by
  decide

/-- Pigeonhole partition of any 5-element subset $I \subseteq \operatorname{Fin} 8$
across the 4-cap $\{0, 1, 2, 3\}$ and 4-cup $\{4, 5, 6, 7\}$: either at least 3 elements
lie in the 4-cap and at least 1 in the 4-cup, or at least 3 elements lie in the 4-cup and
at least 1 in the 4-cap. (Port of Blueprint107.lean L656–677.) -/
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

/-- **8-Point Pentagon-Free Certificate (`not_hasConvexFiveGon_esEightFinset`)**:
The 8-point general-position set `esEightFinset` contains no convex pentagon.
(Port of Blueprint107.lean L683–726 — the master certificate: pull the
5-subset back through the image, split cap/cup by pigeonhole, extract an
ordered triple plus an opposite-half index, certify the three integer
crosses by the `decide` lemmas, and kill `ConvexIndep` by the barycentric
`InPosTriangle` calculus.) -/
theorem not_hasConvexFiveGon_esEightFinset :
    ¬ HasConvexNGon 5 (esEightFinset : Set ℝ²) := by
  rintro ⟨S, hScard, hSsub, hSconv⟩
  have hSsub' : S ⊆ Finset.univ.image esEightPt := Finset.coe_subset.mp hSsub
  obtain ⟨I, _, rfl⟩ := Finset.subset_image_iff.mp hSsub'
  have hIcard : I.card = 5 := by
    rwa [Finset.card_image_of_injective _ esEightPt_injective] at hScard
  rcases fin8_cap_cup_split hIcard with ⟨hI₁, hI₂⟩ | ⟨hI₂, hI₁⟩
  · obtain ⟨i, j, k, hi, hj, hk, hij, hjk⟩ := exists_strict_ordered_triple_of_three_le_card hI₁
    obtain ⟨u, hu⟩ := Finset.card_pos.mp
      (by omega : 0 < (I \ I.filter (fun i : Fin 8 => i.val < 4)).card)
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
    obtain ⟨i, hi⟩ := Finset.card_pos.mp
      (by omega : 0 < (I.filter (fun i : Fin 8 => i.val < 4)).card)
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

/-- **Unconditional Non-Membership `8 ∉ cardSet 5`**:
Not every 8-point general-position set in $\mathbb{R}^2$ contains a convex pentagon.
(Port of Blueprint107.lean L732–735.) -/
theorem eight_not_mem_cardSet_five : (8 : ℕ) ∉ cardSet 5 := by
  intro h8
  exact not_hasConvexFiveGon_esEightFinset
    (h8 esEightFinset esEightFinset_card esEightFinset_nonTrilinear)

/-- Any $N \in \operatorname{cardSet}(5)$ satisfies $9 \le N$.
(Port of Blueprint107.lean L740–743.) -/
theorem nine_le_of_mem_cardSet_five {N : ℕ} (hN : N ∈ cardSet 5) : 9 ≤ N := by
  by_contra hlt
  have hle : N ≤ 8 := by omega
  exact eight_not_mem_cardSet_five (cardSet_upward_closed hle hN)

/-- **Unconditional Lower Bound $9 \le f(5)$**:
$f(5) \ge 2^{5-2} + 1 = 9$. (Port of Blueprint107.lean L749–750.) -/
theorem nine_le_f_five : 9 ≤ f 5 :=
  le_csInf (nonempty_cardSet_all 5) (fun _ hN => nine_le_of_mem_cardSet_five hN)

/-! ## §21 THE TARGETS — the W85-107C kill + the honest scope marker -/

/-- **THE FIRST TARGET (verbatim signature — Solution.lean L69
`f_eq_conjectured_of_le_four`; vendor twin Blueprint107.lean L773)**:
for every $3 \le n \le 4$, $f(n) = 2^{n-2} + 1$ — $f(3) = 3$ and $f(4) = 5$
unconditionally. -/
theorem f_eq_conjectured_of_le_four : ∀ n, 3 ≤ n → n ≤ 4 → f n = 2 ^ (n - 2) + 1 := by
  intro n hn3 hn4
  have hcases : n = 3 ∨ n = 4 := by omega
  rcases hcases with rfl | rfl
  · simpa using f_three_eq
  · simpa using f_four_eq_five_unconditional

/-- **THE SECOND TARGET (the LOWER side of the official `ersz_bounds` for
$n \le 5$; vendor twin Blueprint107.lean L784)**: for every $3 \le n \le 5$,
$2^{n-2} + 1 \le f(n)$ — the ES-1960 8-point pentagon-free witness at
$n = 5$, the Klein 4-point witness at $n = 4$, the official anchor at
$n = 3$. -/
theorem ersz_lower_le_five : ∀ n, 3 ≤ n → n ≤ 5 → 2 ^ (n - 2) + 1 ≤ f n := by
  intro n hn3 hn5
  have hcases : n = 3 ∨ n = 4 ∨ n = 5 := by omega
  rcases hcases with rfl | rfl | rfl
  · rw [f_three_eq]; decide
  · rw [f_four_eq_five_unconditional]; decide
  · simpa using nine_le_f_five

/-- **THE THIRD TARGET (the two-sided classical bounds for $n \le 5$;
verbatim signature — Solution.lean L74 `ersz_bounds_of_le_five`; vendor twin
Blueprint107.lean L796)**: for all $3 \le n \le 5$,
$2^{n-2} + 1 \le f(n) \le \binom{2n-4}{n-2} + 1$. -/
theorem ersz_bounds_of_le_five :
    ∀ n, 3 ≤ n → n ≤ 5 → 2 ^ (n - 2) + 1 ≤ f n ∧
      f n ≤ Nat.choose (2 * n - 4) (n - 2) + 1 := by
  intro n hn3 hn5
  exact ⟨ersz_lower_le_five n hn3 hn5,
    f_le_erdosSzekeresUpper (by omega : 2 ≤ n)⟩

/-- **HONEST SCOPE MARKER (the stretch that remains open)**: the LOWER bound
$2^{n-2}+1 \le f(n)$ is proved by this kernel for $3 \le n \le 5$ only. The
stretch $n \ge 6$ (the ES-1960 doubling construction, the campaign's
ES_SANDWICH_ALLN package) is NOT claimed here — neither linrock's public
proof (only $n \le 5$ witnesses) nor this cone covers it. What IS certified:
the COMPATIBILITY of the open side with this kernel's proven upper bound —
the conjectured value $2^{n-2}+1$ is positive (arsenal `two_pow_pos`,
CardinalWorlds.lean:420), nontrivial (arsenal `two_pow_ge2`,
CardinalWorlds.lean:431), and bounded above by the proven upper bound
(`erdosSzekeresConjectured_le_upper`, cloned §13). Never dress partial as
complete. -/
theorem ersz_lower_scope_pos (n : ℕ) (hn : 6 ≤ n) :
    0 < 2 ^ (n - 2) ∧ 2 ≤ 2 ^ (n - 2) ∧
      2 ^ (n - 2) + 1 ≤ Nat.choose (2 * n - 4) (n - 2) + 1 := by
  have h1 := two_pow_pos (n - 2)
  have h2 := two_pow_ge2 (n - 2) (by omega)
  have h3 := erdosSzekeresConjectured_le_upper n
  dsimp [erdosSzekeresConjectured, erdosSzekeresUpper] at h3
  exact ⟨h1, h2, h3⟩

end Erdos107C

#eval "DM107C_LOWER_GREEN"

#print axioms Erdos107C.f_eq_conjectured_of_le_four
#print axioms Erdos107C.ersz_lower_le_five
#print axioms Erdos107C.ersz_bounds_of_le_five
#print axioms Erdos107C.f_three_eq
#print axioms Erdos107C.f_four_eq_five_unconditional
#print axioms Erdos107C.five_mem_cardSet_four
#print axioms Erdos107C.not_hasConvexFiveGon_esEightFinset
#print axioms Erdos107C.nine_le_f_five
#print axioms Erdos107C.f_le_erdosSzekeresUpper
#print axioms Erdos107C.nonempty_cardSet
