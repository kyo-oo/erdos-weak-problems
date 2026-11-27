import Mathlib

/-!
# GST universal doubled rotation and its integral door

Algebraic proof drafts for equations (5)--(7) of
`research/derivations/GST_fold_polarization_integrability_and_causal_defect_2026_11_02.tex`.
This constructs a rotation on a doubled carrier. It does not identify that
carrier's new weight-one structure with the original variety's Hodge structure.
No Hodge-to-Chow selector or geometric realization is a field of this API.
-/

namespace GSTFoldRotation

variable {H : Type*} [AddCommGroup H]

def rotate (v : H × H) : H × H := (-v.2, v.1)

@[simp] theorem rotate_square (v : H × H) : rotate (rotate v) = -v := by
  rcases v with ⟨x,y⟩
  simp [rotate]

@[simp] theorem rotate_fourth (v : H × H) :
    rotate (rotate (rotate (rotate v))) = v := by
  rcases v with ⟨x,y⟩
  simp [rotate]

theorem rotate_add (v w : H × H) : rotate (v + w) = rotate v + rotate w := by
  rcases v with ⟨x,y⟩
  rcases w with ⟨z,t⟩
  simp [rotate, neg_add, add_comm]

def door (v : H × H) : H × H := rotate v - v

/-- An explicit integral preimage of twice every target, on any abelian group. -/
theorem doubled_door_witness (x y : H) :
    door (y-x, -x-y) = (x+x, y+y) := by
  apply Prod.ext <;> simp [door, rotate] <;> abel

/-- Exact integer criterion, including negative coordinates and the zero target. -/
theorem integral_door_iff (x y : ℤ) :
    (∃ u v : ℤ, door (u,v) = (x,y)) ↔ ∃ k : ℤ, x+y = 2*k := by
  constructor
  · rintro ⟨u,v,h⟩
    have hx := congrArg Prod.fst h
    have hy := congrArg Prod.snd h
    simp [door, rotate] at hx hy
    exact ⟨-v, by omega⟩
  · rintro ⟨k,hk⟩
    refine ⟨y-k, -k, ?_⟩
    apply Prod.ext <;> simp [door, rotate] <;> omega

theorem odd_anchor_refused : ¬ ∃ u v : ℤ, door (u,v) = (1,0) := by
  rw [integral_door_iff]
  omega

section Rational
variable [Module ℚ H]

def rationalDoorInverse (v : H × H) : H × H :=
  ((1/2 : ℚ) • (v.2-v.1), -(1/2 : ℚ) • (v.1+v.2))

theorem rational_door_right_inverse (v : H × H) :
    door (rationalDoorInverse v) = v := by
  rcases v with ⟨x,y⟩
  apply Prod.ext <;> simp [door, rotate, rationalDoorInverse,
    smul_add, smul_sub, sub_eq_add_neg] <;> module

theorem rational_door_left_inverse (v : H × H) :
    rationalDoorInverse (door v) = v := by
  rcases v with ⟨x,y⟩
  apply Prod.ext <;> simp [door, rotate, rationalDoorInverse,
    smul_add, smul_sub, sub_eq_add_neg] <;> module

end Rational

/-- Scalar version of the actual auxiliary-torus divisor polarization identity. -/
theorem anchor_divisor_difference {R : Type*} [CommRing R] (e f a b : R) :
    (e+a)*(f+b) - (e-a)*(f-b) = 2*(e*b+a*f) := by ring

/-- An original one-dimensional rational summand has no such rotation. -/
theorem no_rational_scalar_rotation (j : ℚ) : j*j ≠ -1 := by
  nlinarith [sq_nonneg j]

section CycleCompatibility
variable {N : Type*} [AddCommGroup N]

def pairCycleClass (cl : N →+ H) (z : N × N) : H × H := (cl z.1, cl z.2)

/-- On two actual disjoint copies, the signed-swap correspondence commutes
with the canonical cycle map. The actual scheme interpretation is hand-level. -/
theorem pair_cycleClass_rotation (cl : N →+ H) (z : N × N) :
    pairCycleClass cl (rotate z) = rotate (pairCycleClass cl z) := by
  rcases z with ⟨x,y⟩
  simp [pairCycleClass, rotate]

theorem pair_representable_iff (cl : N →+ H) (x y : H) :
    (∃ z : N × N, pairCycleClass cl z = (x,y)) ↔
      (∃ a : N, cl a = x) ∧ (∃ b : N, cl b = y) := by
  constructor
  · rintro ⟨⟨a,b⟩,h⟩
    exact ⟨⟨a,congrArg Prod.fst h⟩,⟨b,congrArg Prod.snd h⟩⟩
  · rintro ⟨⟨a,ha⟩,⟨b,hb⟩⟩
    exact ⟨(a,b),by simp [pairCycleClass,ha,hb]⟩

theorem anchor_representable_iff (cl : N →+ H) (x : H) :
    (∃ z : N × N, pairCycleClass cl z = (x,0)) ↔ ∃ a : N, cl a = x := by
  rw [pair_representable_iff]
  constructor
  · exact fun h => h.1
  · intro h
    exact ⟨h,⟨0,map_zero cl⟩⟩

end CycleCompatibility

#print axioms doubled_door_witness
#print axioms integral_door_iff
#print axioms rational_door_right_inverse
#print axioms anchor_representable_iff
end GSTFoldRotation
