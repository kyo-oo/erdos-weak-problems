import Mathlib

/-!
# Integral dressing beyond square zero, and its noncommuting obstruction

Proof draft; not compiled in this session. Complete hand derivation:
research/derivations/GST_projection_correction_and_cubic_dressing_2026_10_28.tex

The existing Round-31 span law assumes xy=0. Here xy may be nonzero:
commutativity and vanishing triple products suffice for 1+2x+2x².
The alternating-area obstruction is also proved, rather than suppressed.
These are ring/transport laws, not assertions of universal geometric decks.
-/

namespace GSTCubicNilpotentDressing

section Ring
variable {R : Type*} [Ring R]

/-- Integral truncated exponential at doubled scale. -/
def dressing2 (x : R) : R := 1 + 2 * x + 2 * (x * x)

@[simp] theorem dressing2_zero : dressing2 (0 : R) = 1 := by
  simp [dressing2]

/-- Exact error formula, valid without commutativity or nilpotence. -/
theorem dressing2_multiplication_defect (x y : R) :
    dressing2 x * dressing2 y = dressing2 (x + y) +
      2 * (x * y - y * x) +
      4 * (x * x * y) + 4 * (x * y * y) + 4 * (x * x * y * y) := by
  unfold dressing2
  noncomm_ring

/-- The cubic extension of the branch's square-zero dressing theorem. -/
theorem dressing2_add (x y : R) (hcomm : x * y = y * x)
    (hxxy : x * x * y = 0) (hxyy : x * y * y = 0) :
    dressing2 x * dressing2 y = dressing2 (x + y) := by
  have hbracket : x * y - y * x = 0 := sub_eq_zero.mpr hcomm
  rw [dressing2_multiplication_defect, hbracket, hxxy, hxyy]
  simp

theorem dressing2_inverse_left (x : R) (hxxx : x * x * x = 0) :
    dressing2 x * dressing2 (-x) = 1 := by
  have hexpand : dressing2 x * dressing2 (-x) =
      1 + 4 * (x * x * x * x) := by
    unfold dressing2
    noncomm_ring
  rw [hexpand, hxxx]
  simp

theorem dressing2_inverse_right (x : R) (hxxx : x * x * x = 0) :
    dressing2 (-x) * dressing2 x = 1 := by
  have hexpand : dressing2 (-x) * dressing2 x =
      1 + 4 * (x * x * x * x) := by
    unfold dressing2
    noncomm_ring
  rw [hexpand, hxxx]
  simp

/-- A genuine unit, with an explicit integral inverse. -/
def dressing2Unit (x : R) (hxxx : x * x * x = 0) : Rˣ where
  val := dressing2 x
  inv := dressing2 (-x)
  val_inv := dressing2_inverse_left x hxxx
  inv_val := dressing2_inverse_right x hxxx

end Ring

section Realization
variable {V R : Type*} [AddCommGroup V] [Ring R]

/-- Actual algebraic hypotheses on a realization span. They permit S² ≠ 0. -/
structure CubicCommutingRealization (V R : Type*) [AddCommGroup V] [Ring R] where
  realization : V →+ R
  commute : ∀ u v, realization u * realization v = realization v * realization u
  triple_zero : ∀ u v w, realization u * realization v * realization w = 0

namespace CubicCommutingRealization

def dressed (D : CubicCommutingRealization V R) (v : V) : R :=
  dressing2 (D.realization v)

@[simp] theorem dressed_zero (D : CubicCommutingRealization V R) :
    D.dressed 0 = 1 := by simp [dressed]

theorem dressed_add (D : CubicCommutingRealization V R) (u v : V) :
    D.dressed (u + v) = D.dressed u * D.dressed v := by
  unfold dressed
  rw [map_add]
  exact (dressing2_add _ _ (D.commute u v)
    (D.triple_zero u u v) (D.triple_zero u v v)).symm

/-- Every additive realization integrates into units at doubled scale. -/
def unitLift (D : CubicCommutingRealization V R) : Multiplicative V →* Rˣ where
  toFun v := dressing2Unit (D.realization v.toAdd) (D.triple_zero _ _ _)
  map_one' := by
    apply Units.ext
    simp [dressing2Unit]
  map_mul' u v := by
    apply Units.ext
    change D.dressed (u.toAdd + v.toAdd) = D.dressed u.toAdd * D.dressed v.toAdd
    exact D.dressed_add _ _

/-- The exact multiplicative image of an additive coboundary.
An acted term g·s(h) can be substituted for v; its existence is not assumed. -/
theorem dressed_coboundary (D : CubicCommutingRealization V R) (u v w : V) :
    D.dressed u * D.dressed v * D.dressed (-w) = D.dressed (u + v - w) := by
  rw [← D.dressed_add, ← D.dressed_add]
  simp only [sub_eq_add_neg]

/-- Combines a separately established additive kill scale with cubic dressing.
No existence of a geometric primitive is concealed in this implication. -/
theorem dressed_scaled_coboundary (D : CubicCommutingRealization V R)
    (m : ℤ) (u v w c : V) (hprimitive : u + v - w = m • c) :
    D.dressed u * D.dressed v * D.dressed (-w) = D.dressed (m • c) := by
  rw [D.dressed_coboundary, hprimitive]

end CubicCommutingRealization
end Realization

section Heisenberg

def jordan3 : Matrix (Fin 3) (Fin 3) ℤ := !![0,1,0; 0,0,1; 0,0,0]

/-- A span excluded by square-zero dressing and admitted by cubic dressing:
J² is nonzero, J³ vanishes, and the doubled integral polynomial multiplies. -/
theorem cubic_extension_is_strict :
    jordan3 * jordan3 ≠ 0 ∧
      jordan3 * jordan3 * jordan3 = 0 ∧
      dressing2 jordan3 * dressing2 jordan3 = dressing2 (jordan3 + jordan3) := by
  decide

def heisenberg (a b c : ℤ) : Matrix (Fin 3) (Fin 3) ℤ :=
  !![1, 2*a, 2*c+2*a*b; 0, 1, 2*b; 0, 0, 1]

/-- The noncommuting central correction is the signed area, exactly. -/
theorem heisenberg_mul (a b c a' b' c' : ℤ) :
    heisenberg a b c * heisenberg a' b' c' =
      heisenberg (a+a') (b+b') (c+c'+a*b'-a'*b) := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    norm_num [heisenberg, Matrix.mul_apply, Fin.sum_univ_succ] <;> ring

theorem heisenberg_inverse (a b c : ℤ) :
    heisenberg a b c * heisenberg (-a) (-b) (-c) = 1 := by
  rw [heisenberg_mul]
  have hc : c + -c + a * -b - -a * b = 0 := by ring
  rw [hc]
  norm_num [heisenberg]
  decide

/-- The failed additive product remains failed at every nonzero scale. -/
theorem noncommuting_defect_survives_every_scale (m : ℤ) (hm : m ≠ 0) :
    heisenberg m 0 0 * heisenberg 0 m 0 ≠ heisenberg m m 0 := by
  intro h
  have h13 := congrArg (fun M : Matrix (Fin 3) (Fin 3) ℤ => M 0 2) h
  simp only [heisenberg, Matrix.mul_apply, Fin.sum_univ_three, Matrix.of_apply,
    Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_succ,
    Matrix.cons_val_two, Matrix.head_cons, Matrix.tail_cons] at h13
  norm_num at h13
  have hsq : m * m ≠ 0 := mul_ne_zero hm hm
  apply hsq
  rcases h13 with h | h
  · have hm0 : m = 0 := by linarith
    simp [hm0]
  · simp [h]

def area (x y : ℤ × ℤ) : ℤ := x.1 * y.2 - y.1 * x.2

/-- Universal cocycle identity, not a finite-grid assertion. -/
theorem area_cocycle (x y z : ℤ × ℤ) :
    area x y + area (x+y) z = area y z + area x (y+z) := by
  simp only [area, Prod.fst_add, Prod.snd_add]
  ring

theorem area_skew (x y : ℤ × ℤ) : area y x = -area x y := by
  unfold area
  ring

/-- No nonzero integer scale of the area cocycle is an ordinary additive
coboundary. Such a coboundary is symmetric, while the area is alternating. -/
theorem no_nonzero_scale_area_coboundary (m : ℤ) (hm : m ≠ 0) :
    ¬ ∃ f : (ℤ × ℤ) → ℤ, ∀ x y,
      f x + f y - f (x+y) = m * area x y := by
  rintro ⟨f, hf⟩
  have h1 := hf (1,0) (0,1)
  have h2 := hf (0,1) (1,0)
  norm_num [area] at h1 h2
  apply hm
  linarith

end Heisenberg

#print axioms dressing2_add
#print axioms CubicCommutingRealization.dressed_coboundary
#print axioms noncommuting_defect_survives_every_scale
#print axioms no_nonzero_scale_area_coboundary

end GSTCubicNilpotentDressing
