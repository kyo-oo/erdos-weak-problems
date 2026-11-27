import Mathlib
import HCUniverse2.GSTSphereUnionComponents
import HCUniverse2.GSTProjectiveOverC

/-
Copyright (c) 2026. The HC-PROOF campaign. All rights reserved.

# WAVE 3-A — THE RIEMANN-SPHERE COORDINATE EQUIVALENCE (the finite-line
analytification's arithmetic core)

The stereographic type-equivalence `unitSphereType ≃ Option ℂ` between the
corpus's honest 2-sphere (the metric sphere in `EuclideanSpace ℝ (Fin 3)`,
the analytification shape of every line of the finite-line world) and the
extended complex plane `Option ℂ = ℂ ⊔ {∞}` (the two-chart coordinate model
of the projective line: `some t` = the chart coordinate `t`, `none` = the
point at infinity on the second chart).

This is the self-contained arithmetic component of the analytification
bridge (the unconditional round's Task 2): the scheme-side point
classification (`ComplexPoint`-style, on the finite-line world) is
assembled on top in the follow-up waves, and the assembled
`AnalytificationData`'s `pointsEquiv` rides this equivalence slice-by-slice.

WAVE 3-B (the repair of run 44969885834, every site diagnosed): the
COORDINATE-COERCION DISCIPLINE — `unitSphereType` is a `Subtype`, NOT a
function type, so every coordinate application is the explicit
`(v : EuclideanSpace ℝ (Fin 3)) k` coercion (the wave-3-A draft applied
`v k` bare — the "Function expected" family); the `sq_eq_one_iff`
mis-application replaced by the deterministic factorization route
(`(1 - x) * (1 + x) = 0`, `linear_combination` + `mul_eq_zero`); the
`sq_nonneg t.re`-vs-`t.re * t.re` mismatches replaced by
`mul_self_nonneg`; the north-pole membership proof gets the
`PiLp.toLp_apply` + `Matrix.cons` normalizations before `norm_num`; the
`pow_eq_zero_iff` sites replaced by `sq_eq_zero_iff`; the pole/non-pole
denominators get `div_eq_one_iff_eq` instead of bare `field_simp`.

The arithmetic is pure real algebra on the coordinates: the sphere
equation `x² + y² + z² = 1` transports the chart identity
`(2a)² + (2b)² + (s-1)² = (s+1)²` at `s = a² + b²`, and the two
cancellation laws are field cancellations at the non-pole `z ≠ 1`.

Honesty ledger: zero `sorry`, zero new axioms, zero `native_decide`.
-/

set_option maxHeartbeats 100000000
set_option maxRecDepth 1000000

noncomputable section

open Real
open GSTProjectiveOverC GSTSphereUnionComponents

namespace GSTFiniteLineRiemann

/-! ## §0 The coordinate form of the sphere equation -/

/-- The norm-square of a 3-vector in coordinate form (the pinned
`EuclideanSpace.real_norm_sq_eq` + `Fin.sum_univ_three`, isolated once;
the two rewrites close the goal definitionally — no residual `ring`). -/
theorem sphere_norm_sq (v : EuclideanSpace ℝ (Fin 3)) :
    ‖v‖ ^ 2 = (v 0) ^ 2 + (v 1) ^ 2 + (v 2) ^ 2 := by
  rw [EuclideanSpace.real_norm_sq_eq, Fin.sum_univ_three]

/-- **THE SPHERE EQUATION IN COORDINATES** — the metric-sphere membership
is the unit equation on the three coordinates.  The backward direction is
the deterministic factorization route: `‖v‖² = 1` with `0 ≤ ‖v‖` gives
`(1 - ‖v‖) * (1 + ‖v‖) = 0` (a `linear_combination` of the equation), the
second factor is positive, so `‖v‖ = 1`. -/
theorem mem_sphere_iff_coord (v : EuclideanSpace ℝ (Fin 3)) :
    v ∈ Metric.sphere (0 : EuclideanSpace ℝ (Fin 3)) 1 ↔
      (v 0) ^ 2 + (v 1) ^ 2 + (v 2) ^ 2 = 1 := by
  rw [mem_sphere_zero_iff_norm]
  constructor
  · intro h
    have h2 : ‖v‖ ^ 2 = 1 := by rw [h, one_pow]
    rwa [sphere_norm_sq] at h2
  · intro h
    have hn : 0 ≤ ‖v‖ := norm_nonneg v
    have h2 : ‖v‖ ^ 2 = 1 := by rw [sphere_norm_sq, h]
    have hfac : (1 - ‖v‖) * (1 + ‖v‖) = 0 := by
      linear_combination -h2
    have hpos : (0 : ℝ) < 1 + ‖v‖ := by linarith
    have hz : (1 : ℝ) - ‖v‖ = 0 :=
      (mul_eq_zero.mp hfac).resolve_right (ne_of_gt hpos)
    linarith

/-! ## §1 The forward coordinate map -/

/-- The north pole (the point at infinity's sphere image). -/
def northPole : unitSphereType :=
  ⟨WithLp.toLp 2 ![0, 0, 1], by
    rw [mem_sphere_iff_coord]
    simp only [PiLp.toLp_apply, Matrix.cons_val_zero, Matrix.cons_val_one,
      Matrix.head_cons, Matrix.cons_val_two]
    norm_num⟩

/-- The coordinates of the forward stereographic image of `t ∈ ℂ`. -/
def stereoCoord (t : ℂ) : Fin 3 → ℝ :=
  ![2 * t.re / (t.re * t.re + t.im * t.im + 1),
    2 * t.im / (t.re * t.re + t.im * t.im + 1),
    (t.re * t.re + t.im * t.im - 1) / (t.re * t.re + t.im * t.im + 1)]

/-- The denominator positivity of the stereographic image. -/
theorem stereoCoord_denom_pos (t : ℂ) :
    0 < t.re * t.re + t.im * t.im + 1 := by
  have h1 : 0 ≤ t.re * t.re := mul_self_nonneg t.re
  have h2 : 0 ≤ t.im * t.im := mul_self_nonneg t.im
  linarith

/-- **THE STEREOGRAPHIC IMAGE IS ON THE SPHERE** — the chart identity
`(2a)² + (2b)² + (s-1)² = (s+1)²` at `s = a² + b²`. -/
theorem stereoCoord_mem (t : ℂ) :
    (WithLp.toLp 2 (stereoCoord t) : EuclideanSpace ℝ (Fin 3)) ∈
      Metric.sphere (0 : EuclideanSpace ℝ (Fin 3)) 1 := by
  rw [mem_sphere_iff_coord]
  have hd : t.re * t.re + t.im * t.im + 1 ≠ 0 := by
    exact ne_of_gt (stereoCoord_denom_pos t)
  have h0 : (WithLp.toLp 2 (stereoCoord t) : EuclideanSpace ℝ (Fin 3)) 0
      = 2 * t.re / (t.re * t.re + t.im * t.im + 1) := rfl
  have h1 : (WithLp.toLp 2 (stereoCoord t) : EuclideanSpace ℝ (Fin 3)) 1
      = 2 * t.im / (t.re * t.re + t.im * t.im + 1) := rfl
  have h2 : (WithLp.toLp 2 (stereoCoord t) : EuclideanSpace ℝ (Fin 3)) 2
      = (t.re * t.re + t.im * t.im - 1) /
          (t.re * t.re + t.im * t.im + 1) := rfl
  rw [h0, h1, h2]
  field_simp
  ring

/-- **THE FORWARD COORDINATE MAP** — `none` ↦ the north pole;
`some t` ↦ the stereographic image of `t`. -/
def coordToSphere : Option ℂ → unitSphereType
  | none => northPole
  | some t => ⟨WithLp.toLp 2 (stereoCoord t), stereoCoord_mem t⟩

/-! ## §2 The inverse coordinate map -/

/-- **THE INVERSE COORDINATE MAP** — `v ↦ none` at the north pole;
`v ↦ some ⟨v₀ / (1 - v₂), v₁ / (1 - v₂)⟩` elsewhere (the coordinates
read through the explicit subtype coercion). -/
def sphereToCoord (v : unitSphereType) : Option ℂ :=
  if (v : EuclideanSpace ℝ (Fin 3)) 2 = 1 then none
  else some ⟨(v : EuclideanSpace ℝ (Fin 3)) 0 / (1 - (v : EuclideanSpace ℝ (Fin 3)) 2),
    (v : EuclideanSpace ℝ (Fin 3)) 1 / (1 - (v : EuclideanSpace ℝ (Fin 3)) 2)⟩

/-- The non-pole denominator positivity. -/
theorem sphere_denom_pos {v : unitSphereType}
    (hv : (v : EuclideanSpace ℝ (Fin 3)) 2 ≠ 1) :
    0 < 1 - (v : EuclideanSpace ℝ (Fin 3)) 2 := by
  have hs : ((v : EuclideanSpace ℝ (Fin 3)) 0) ^ 2 +
      ((v : EuclideanSpace ℝ (Fin 3)) 1) ^ 2 +
      ((v : EuclideanSpace ℝ (Fin 3)) 2) ^ 2 = 1 :=
    (mem_sphere_iff_coord _).mp v.2
  have h0 : 0 ≤ ((v : EuclideanSpace ℝ (Fin 3)) 0) ^ 2 := sq_nonneg _
  have h1 : 0 ≤ ((v : EuclideanSpace ℝ (Fin 3)) 1) ^ 2 := sq_nonneg _
  have h2 : 0 ≤ ((v : EuclideanSpace ℝ (Fin 3)) 2) ^ 2 := sq_nonneg _
  have hle : (v : EuclideanSpace ℝ (Fin 3)) 2 ≤ 1 := by
    by_contra hcon
    push_neg at hcon
    nlinarith
  rcases lt_or_eq_of_le hle with h | h
  · linarith
  · exact absurd h hv

/-- The pole case: `v₂ = 1` forces the first two coordinates to vanish
(the sphere equation), so `v` IS the north pole. -/
theorem eq_northPole_of_pole {v : unitSphereType}
    (hv : (v : EuclideanSpace ℝ (Fin 3)) 2 = 1) :
    v = northPole := by
  have hs : ((v : EuclideanSpace ℝ (Fin 3)) 0) ^ 2 +
      ((v : EuclideanSpace ℝ (Fin 3)) 1) ^ 2 +
      ((v : EuclideanSpace ℝ (Fin 3)) 2) ^ 2 = 1 :=
    (mem_sphere_iff_coord _).mp v.2
  rw [show ((v : EuclideanSpace ℝ (Fin 3)) 2) = 1 from hv] at hs
  have hp0 : 0 ≤ ((v : EuclideanSpace ℝ (Fin 3)) 0) ^ 2 := sq_nonneg _
  have hp1 : 0 ≤ ((v : EuclideanSpace ℝ (Fin 3)) 1) ^ 2 := sq_nonneg _
  have h0 : ((v : EuclideanSpace ℝ (Fin 3)) 0) ^ 2 = 0 := by linarith
  have h1 : ((v : EuclideanSpace ℝ (Fin 3)) 1) ^ 2 = 0 := by linarith
  have h0' : (v : EuclideanSpace ℝ (Fin 3)) 0 = 0 := by
    exact sq_eq_zero_iff.mp h0
  have h1' : (v : EuclideanSpace ℝ (Fin 3)) 1 = 0 := by
    exact sq_eq_zero_iff.mp h1
  ext i
  fin_cases i
  · exact h0'
  · exact h1'
  · exact hv

/-! ## §3 The two cancellation laws -/

/-- **THE FIRST CANCELLATION** — the coordinate map reads the stereographic
image back to the original coordinate (the pole case by the pole lemma, the
non-pole case by the two field cancellations). -/
theorem sphereToCoord_coordToSphere (t : Option ℂ) :
    sphereToCoord (coordToSphere t) = t := by
  cases t with
  | none =>
      have hpole : ((northPole : unitSphereType) : EuclideanSpace ℝ (Fin 3)) 2 = 1 := by
        simp [northPole, PiLp.toLp_apply, Matrix.cons_val_zero, Matrix.cons_val_one,
          Matrix.head_cons, Matrix.cons_val_two]
      rw [sphereToCoord, coordToSphere, if_pos hpole]
  | some t =>
      have hz : ((⟨WithLp.toLp 2 (stereoCoord t), stereoCoord_mem t⟩ :
          unitSphereType) : EuclideanSpace ℝ (Fin 3)) 2 ≠ 1 := by
        intro hcon
        have hd := stereoCoord_denom_pos t
        have hx : ((⟨WithLp.toLp 2 (stereoCoord t), stereoCoord_mem t⟩ :
            unitSphereType) : EuclideanSpace ℝ (Fin 3)) 2
            = (t.re * t.re + t.im * t.im - 1) /
                (t.re * t.re + t.im * t.im + 1) := rfl
        rw [hx] at hcon
        rw [div_eq_one_iff_eq (by linarith : (t.re * t.re + t.im * t.im + 1 : ℝ) ≠ 0)] at hcon
        linarith
      rw [sphereToCoord, coordToSphere, if_neg hz]
      congr 1
      have hd : 1 - (t.re * t.re + t.im * t.im - 1) /
          (t.re * t.re + t.im * t.im + 1) ≠ 0 := by
        have hdS : (t.re * t.re + t.im * t.im + 1 : ℝ) ≠ 0 :=
          ne_of_gt (stereoCoord_denom_pos t)
        intro h0
        field_simp at h0
        linarith
      have hx : ((⟨WithLp.toLp 2 (stereoCoord t), stereoCoord_mem t⟩ :
          unitSphereType) : EuclideanSpace ℝ (Fin 3)) 0
          = 2 * t.re / (t.re * t.re + t.im * t.im + 1) := rfl
      have hy : ((⟨WithLp.toLp 2 (stereoCoord t), stereoCoord_mem t⟩ :
          unitSphereType) : EuclideanSpace ℝ (Fin 3)) 1
          = 2 * t.im / (t.re * t.re + t.im * t.im + 1) := rfl
      rw [hx, hy]
      simp only [Complex.ext_iff]
      constructor
      · have hz2 : stereoCoord t 2 = (t.re * t.re + t.im * t.im - 1) /
              (t.re * t.re + t.im * t.im + 1) := rfl
        have hdS : (t.re * t.re + t.im * t.im + 1 : ℝ) ≠ 0 :=
          ne_of_gt (stereoCoord_denom_pos t)
        rw [hz2]
        field_simp
        try ring
      · have hz2 : stereoCoord t 2 = (t.re * t.re + t.im * t.im - 1) /
              (t.re * t.re + t.im * t.im + 1) := rfl
        have hdS : (t.re * t.re + t.im * t.im + 1 : ℝ) ≠ 0 :=
          ne_of_gt (stereoCoord_denom_pos t)
        rw [hz2]
        field_simp
        try ring

/-- **THE SECOND CANCELLATION** — the coordinate map's image of any sphere
point is the original sphere point (the pole case by the pole lemma, the
non-pole case by the sphere-equation field cancellations). -/
theorem coordToSphere_sphereToCoord (v : unitSphereType) :
    coordToSphere (sphereToCoord v) = v := by
  by_cases hv : (v : EuclideanSpace ℝ (Fin 3)) 2 = 1
  · rw [sphereToCoord, if_pos hv, coordToSphere]
    exact (eq_northPole_of_pole hv).symm
  · have hs : ((v : EuclideanSpace ℝ (Fin 3)) 0) ^ 2 +
      ((v : EuclideanSpace ℝ (Fin 3)) 1) ^ 2 +
      ((v : EuclideanSpace ℝ (Fin 3)) 2) ^ 2 = 1 :=
      (mem_sphere_iff_coord _).mp v.2
    have h0 : 0 ≤ ((v : EuclideanSpace ℝ (Fin 3)) 0) ^ 2 := sq_nonneg _
    have h1 : 0 ≤ ((v : EuclideanSpace ℝ (Fin 3)) 1) ^ 2 := sq_nonneg _
    have hsq : ((v : EuclideanSpace ℝ (Fin 3)) 0) ^ 2 +
        ((v : EuclideanSpace ℝ (Fin 3)) 1) ^ 2 =
        1 - ((v : EuclideanSpace ℝ (Fin 3)) 2) ^ 2 := by
      ring_nf
      linarith
    have hz1 : 1 - (v : EuclideanSpace ℝ (Fin 3)) 2 ≠ 0 := by
      have := sphere_denom_pos hv
      linarith
    rw [sphereToCoord, if_neg hv]
    simp only [coordToSphere]
    have hd : ((v : EuclideanSpace ℝ (Fin 3)) 0 / (1 - (v : EuclideanSpace ℝ (Fin 3)) 2)) *
        ((v : EuclideanSpace ℝ (Fin 3)) 0 / (1 - (v : EuclideanSpace ℝ (Fin 3)) 2)) +
        ((v : EuclideanSpace ℝ (Fin 3)) 1 / (1 - (v : EuclideanSpace ℝ (Fin 3)) 2)) *
        ((v : EuclideanSpace ℝ (Fin 3)) 1 / (1 - (v : EuclideanSpace ℝ (Fin 3)) 2)) + 1 ≠ 0 := by
      have hp : 0 < 1 - (v : EuclideanSpace ℝ (Fin 3)) 2 := sphere_denom_pos hv
      have hdz : (1 : ℝ) - (v : EuclideanSpace ℝ (Fin 3)) 2 ≠ 0 := ne_of_gt hp
      have hz2 : 0 < (1 - (v : EuclideanSpace ℝ (Fin 3)) 2) ^ 2 := by positivity
      have hd2 : ((1 : ℝ) - (v : EuclideanSpace ℝ (Fin 3)) 2) ^ 2 ≠ 0 := ne_of_gt hz2
      have hnum : 0 < ((v : EuclideanSpace ℝ (Fin 3)) 0) ^ 2 +
          ((v : EuclideanSpace ℝ (Fin 3)) 1) ^ 2 +
          (1 - (v : EuclideanSpace ℝ (Fin 3)) 2) ^ 2 := by
        have hz2' : 0 < (1 - (v : EuclideanSpace ℝ (Fin 3)) 2) ^ 2 := by positivity
        have hx' : 0 ≤ ((v : EuclideanSpace ℝ (Fin 3)) 0) ^ 2 := sq_nonneg _
        have hy' : 0 ≤ ((v : EuclideanSpace ℝ (Fin 3)) 1) ^ 2 := sq_nonneg _
        nlinarith
      have hfrac : (((v : EuclideanSpace ℝ (Fin 3)) 0 / (1 - (v : EuclideanSpace ℝ (Fin 3)) 2)) * ((v : EuclideanSpace ℝ (Fin 3)) 0 / (1 - (v : EuclideanSpace ℝ (Fin 3)) 2)) + ((v : EuclideanSpace ℝ (Fin 3)) 1 / (1 - (v : EuclideanSpace ℝ (Fin 3)) 2)) * ((v : EuclideanSpace ℝ (Fin 3)) 1 / (1 - (v : EuclideanSpace ℝ (Fin 3)) 2)) + 1) = (((v : EuclideanSpace ℝ (Fin 3)) 0) ^ 2 + ((v : EuclideanSpace ℝ (Fin 3)) 1) ^ 2 + ((1 : ℝ) - (v : EuclideanSpace ℝ (Fin 3)) 2) ^ 2) / ((1 : ℝ) - (v : EuclideanSpace ℝ (Fin 3)) 2) ^ 2 := by
        field_simp
      rw [hfrac]
      exact div_ne_zero (ne_of_gt hnum) hd2
    ext i
    fin_cases i
    · have hx : ((coordToSphere (some ⟨((v : EuclideanSpace ℝ (Fin 3)) 0) / (1 - ((v : EuclideanSpace ℝ (Fin 3)) 2)), ((v : EuclideanSpace ℝ (Fin 3)) 1) / (1 - ((v : EuclideanSpace ℝ (Fin 3)) 2))⟩)) : EuclideanSpace ℝ (Fin 3)) 0
          = 2 * (((v : EuclideanSpace ℝ (Fin 3)) 0) / (1 - ((v : EuclideanSpace ℝ (Fin 3)) 2))) / ((((v : EuclideanSpace ℝ (Fin 3)) 0) / (1 - ((v : EuclideanSpace ℝ (Fin 3)) 2))) * (((v : EuclideanSpace ℝ (Fin 3)) 0) / (1 - ((v : EuclideanSpace ℝ (Fin 3)) 2))) + (((v : EuclideanSpace ℝ (Fin 3)) 1) / (1 - ((v : EuclideanSpace ℝ (Fin 3)) 2))) * (((v : EuclideanSpace ℝ (Fin 3)) 1) / (1 - ((v : EuclideanSpace ℝ (Fin 3)) 2))) + 1) := rfl
      show ((coordToSphere (some ⟨((v : EuclideanSpace ℝ (Fin 3)) 0) / (1 - ((v : EuclideanSpace ℝ (Fin 3)) 2)), ((v : EuclideanSpace ℝ (Fin 3)) 1) / (1 - ((v : EuclideanSpace ℝ (Fin 3)) 2))⟩)) : EuclideanSpace ℝ (Fin 3)) 0 = ((v : EuclideanSpace ℝ (Fin 3)) 0)
      rw [hx]
      field_simp
      have hs1 : (1 : ℝ) = ((v : EuclideanSpace ℝ (Fin 3)) 0) ^ 2 +
          ((v : EuclideanSpace ℝ (Fin 3)) 1) ^ 2 +
          ((v : EuclideanSpace ℝ (Fin 3)) 2) ^ 2 := hs.symm
      linear_combination ((v : EuclideanSpace ℝ (Fin 3)) 0) * hs1
    · have hy : ((coordToSphere (some ⟨((v : EuclideanSpace ℝ (Fin 3)) 0) / (1 - ((v : EuclideanSpace ℝ (Fin 3)) 2)), ((v : EuclideanSpace ℝ (Fin 3)) 1) / (1 - ((v : EuclideanSpace ℝ (Fin 3)) 2))⟩)) : EuclideanSpace ℝ (Fin 3)) 1
          = 2 * (((v : EuclideanSpace ℝ (Fin 3)) 1) / (1 - ((v : EuclideanSpace ℝ (Fin 3)) 2))) / ((((v : EuclideanSpace ℝ (Fin 3)) 0) / (1 - ((v : EuclideanSpace ℝ (Fin 3)) 2))) * (((v : EuclideanSpace ℝ (Fin 3)) 0) / (1 - ((v : EuclideanSpace ℝ (Fin 3)) 2))) + (((v : EuclideanSpace ℝ (Fin 3)) 1) / (1 - ((v : EuclideanSpace ℝ (Fin 3)) 2))) * (((v : EuclideanSpace ℝ (Fin 3)) 1) / (1 - ((v : EuclideanSpace ℝ (Fin 3)) 2))) + 1) := rfl
      show ((coordToSphere (some ⟨((v : EuclideanSpace ℝ (Fin 3)) 0) / (1 - ((v : EuclideanSpace ℝ (Fin 3)) 2)), ((v : EuclideanSpace ℝ (Fin 3)) 1) / (1 - ((v : EuclideanSpace ℝ (Fin 3)) 2))⟩)) : EuclideanSpace ℝ (Fin 3)) 1 = ((v : EuclideanSpace ℝ (Fin 3)) 1)
      rw [hy]
      field_simp
      have hs1 : (1 : ℝ) = ((v : EuclideanSpace ℝ (Fin 3)) 0) ^ 2 +
          ((v : EuclideanSpace ℝ (Fin 3)) 1) ^ 2 +
          ((v : EuclideanSpace ℝ (Fin 3)) 2) ^ 2 := hs.symm
      linear_combination ((v : EuclideanSpace ℝ (Fin 3)) 1) * hs1
    · have hzc : ((coordToSphere (some ⟨((v : EuclideanSpace ℝ (Fin 3)) 0) / (1 - ((v : EuclideanSpace ℝ (Fin 3)) 2)), ((v : EuclideanSpace ℝ (Fin 3)) 1) / (1 - ((v : EuclideanSpace ℝ (Fin 3)) 2))⟩)) : EuclideanSpace ℝ (Fin 3)) 2
          = ((((v : EuclideanSpace ℝ (Fin 3)) 0) / (1 - ((v : EuclideanSpace ℝ (Fin 3)) 2))) * (((v : EuclideanSpace ℝ (Fin 3)) 0) / (1 - ((v : EuclideanSpace ℝ (Fin 3)) 2))) + (((v : EuclideanSpace ℝ (Fin 3)) 1) / (1 - ((v : EuclideanSpace ℝ (Fin 3)) 2))) * (((v : EuclideanSpace ℝ (Fin 3)) 1) / (1 - ((v : EuclideanSpace ℝ (Fin 3)) 2))) - 1) / ((((v : EuclideanSpace ℝ (Fin 3)) 0) / (1 - ((v : EuclideanSpace ℝ (Fin 3)) 2))) * (((v : EuclideanSpace ℝ (Fin 3)) 0) / (1 - ((v : EuclideanSpace ℝ (Fin 3)) 2))) + (((v : EuclideanSpace ℝ (Fin 3)) 1) / (1 - ((v : EuclideanSpace ℝ (Fin 3)) 2))) * (((v : EuclideanSpace ℝ (Fin 3)) 1) / (1 - ((v : EuclideanSpace ℝ (Fin 3)) 2))) + 1) := rfl
      show ((coordToSphere (some ⟨((v : EuclideanSpace ℝ (Fin 3)) 0) / (1 - ((v : EuclideanSpace ℝ (Fin 3)) 2)), ((v : EuclideanSpace ℝ (Fin 3)) 1) / (1 - ((v : EuclideanSpace ℝ (Fin 3)) 2))⟩)) : EuclideanSpace ℝ (Fin 3)) 2 = ((v : EuclideanSpace ℝ (Fin 3)) 2)
      rw [hzc]
      field_simp
      linear_combination (1 - (v : EuclideanSpace ℝ (Fin 3)) 2) * hs

/-! ## §4 The bundled equivalence -/

/-- **THE RIEMANN-SPHERE TYPE EQUIVALENCE** — the honest 2-sphere is the
extended complex plane: the two-chart coordinate model of the projective
line, in both directions, by the two cancellation laws. -/
def riemannSphereEquiv : unitSphereType ≃ Option ℂ :=
  ⟨sphereToCoord, coordToSphere,
    coordToSphere_sphereToCoord, sphereToCoord_coordToSphere⟩

end GSTFiniteLineRiemann

end
