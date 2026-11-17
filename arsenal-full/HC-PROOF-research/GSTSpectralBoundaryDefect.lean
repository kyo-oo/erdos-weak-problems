import Mathlib

/-!
# Exact nonlinear spectral source and its boundary defects

Uncompiled proof draft. In geometric K0, x,y are actual eigenline classes.
The two defect terms record the failure of the direct-sum and determinant
relations. Neither relation is silently imposed across singular branching.
-/

namespace GSTSpectralBoundaryDefect
variable {R : Type*} [CommRing R]

def sumDefect (x y : R) : R := 2-x-y
def determinantDefect (x y : R) : R := 1-x*y

theorem anti_square_exact_defect (x y : R) :
    (x-y)^2=(sumDefect x y)^2-4*sumDefect x y+4*determinantDefect x y := by
  unfold sumDefect determinantDefect
  ring

theorem anti_square_zero (x y : R) (hs : x+y=2) (hd : x*y=1) :
    (x-y)^2=0 := by
  calc
    (x-y)^2=(x+y)^2-4*(x*y) := by ring
    _ = 0 := by rw [hs,hd]; ring

theorem line_augmentation_square_zero (x y : R) (hs : x+y=2) (hd : x*y=1) :
    (x-1)^2=0 := by
  calc
    (x-1)^2=x*(x+y-2)-(x*y-1) := by ring
    _ = 0 := by rw [hs,hd]; ring

theorem repeated_anti_power_zero (x y : R) (hs : x+y=2) (hd : x*y=1) (k : ℕ) :
    (x-y)^(k+2)=0 := by
  rw [Nat.add_comm k 2,pow_add,anti_square_zero x y hs hd,zero_mul]

theorem power_of_square_zero_augmentation (x : R) (h : (x-1)^2=0) (n : ℕ) :
    x^n=1+(n : R)*(x-1) := by
  induction n with
  | zero => simp
  | succ n ih =>
      rw [pow_succ,ih,Nat.cast_add,Nat.cast_one]
      calc
        (1+(n : R)*(x-1))*x =
            1+((n : R)+1)*(x-1)+(n : R)*(x-1)^2 := by ring
        _ = 1+((n : R)+1)*(x-1) := by rw [h]; ring

theorem all_power_sums_neutral (x y : R) (hs : x+y=2) (hd : x*y=1) (n : ℕ) :
    x^n+y^n=2 := by
  rw [power_of_square_zero_augmentation x (line_augmentation_square_zero x y hs hd),
    power_of_square_zero_augmentation y
      (line_augmentation_square_zero y x (by simpa [add_comm] using hs)
        (by simpa [mul_comm] using hd))]
  calc
    1+(n : R)*(x-1)+(1+(n : R)*(y-1))=2+(n : R)*(x+y-2) := by ring
    _ = 2 := by rw [hs]; ring

/-- Exact ideal containment, rather than an assertion that boundary defects vanish. -/
theorem anti_square_in_boundary_ideal (I : Ideal R) (x y : R)
    (hs : x+y-2∈I) (hd : x*y-1∈I) : (x-y)^2∈I := by
  have hidentity : (x-y)^2=(x+y-2)*(x+y+2)-4*(x*y-1) := by ring
  rw [hidentity]
  exact I.sub_mem (I.mul_mem_right _ hs) (I.mul_mem_left _ hd)

theorem restriction_kills_repeated_source {S : Type*} [CommRing S]
    (res : R →+* S) (x y : R)
    (hs : res x+res y=2) (hd : res x*res y=1) (k : ℕ) :
    res ((x-y)^(k+2))=0 := by
  rw [map_pow,map_sub]
  exact repeated_anti_power_zero (res x) (res y) hs hd k

/-- Mixed independent sources are intentionally not killed by the square law. -/
theorem mixed_product_exact (x y u v : R)
    (hs : x+y=2) (ht : u+v=2) :
    (x-y)*(u-v)=4*((x-1)*(u-1)) := by
  have hy : y=2-x := by linear_combination hs
  have hv : v=2-u := by linear_combination ht
  rw [hy,hv]
  ring

#print axioms anti_square_exact_defect
#print axioms anti_square_in_boundary_ideal
#print axioms all_power_sums_neutral

/-! ## Selected eigenclusters: rank-three monodromy identities

Here x,y,z are first CHERN classes, rather than the K0 line classes used
above. These exact identities are the low-rank part of the all-rank Chow
transfer proof in GST_selected_cluster_transfer_and_rational_fiber_2026_11_03.tex.
Elementary symmetric relations come from a trivial ambient bundle. We do not
impose them on a nontrivial bundle or across an unexamined discriminant.
-/

def cyclicCubic (x y z : R) : R := x^2*y+y^2*z+z^2*x
def orientationClass (x y z : R) : R := (x-y)*(x-z)*(y-z)

theorem cluster_pair_square_trace (x y z : R) :
    (x+y)^2+(x+z)^2+(y+z)^2 =
      2*(x+y+z)^2-2*(x*y+x*z+y*z) := by ring

theorem cluster_pair_square_trace_zero (x y z : R)
    (h1 : x+y+z=0) (h2 : x*y+x*z+y*z=0) :
    (x+y)^2+(x+z)^2+(y+z)^2=0 := by
  rw [cluster_pair_square_trace, h1, h2]
  ring

theorem cyclic_cubic_rotation (x y z : R) :
    cyclicCubic y z x = cyclicCubic x y z := by
  unfold cyclicCubic
  ring

theorem cyclic_cubic_difference (x y z : R) :
    cyclicCubic x y z-cyclicCubic y x z=orientationClass x y z := by
  unfold cyclicCubic orientationClass
  ring

theorem cyclic_cubic_full_trace (x y z : R) :
    cyclicCubic x y z+cyclicCubic y x z =
      (x+y+z)*(x*y+x*z+y*z)-3*(x*y*z) := by
  unfold cyclicCubic
  ring

theorem cyclic_cubic_trace_zero (x y z : R)
    (h1 : x+y+z=0) (h3 : x*y*z=0) :
    cyclicCubic x y z+cyclicCubic y x z=0 := by
  rw [cyclic_cubic_full_trace, h1, h3]
  ring

/-- Integral numerator: no division by two is smuggled into a ring. -/
theorem cyclic_cubic_orientation_numerator (x y z : R)
    (h1 : x+y+z=0) (h3 : x*y*z=0) :
    2*cyclicCubic x y z=orientationClass x y z := by
  have hs := cyclic_cubic_trace_zero x y z h1 h3
  have hd := cyclic_cubic_difference x y z
  linear_combination hs + hd

theorem orientation_reverses (x y z : R) :
    orientationClass y x z = -orientationClass x y z := by
  unfold orientationClass
  ring

theorem orientation_square_discriminant (x y z : R) :
    (orientationClass x y z)^2 =
      (x+y+z)^2*(x*y+x*z+y*z)^2-4*(x*y+x*z+y*z)^3
      -4*(x+y+z)^3*(x*y*z)-27*(x*y*z)^2
      +18*(x+y+z)*(x*y+x*z+y*z)*(x*y*z) := by
  unfold orientationClass
  ring

/-- Square zero does not assert that the orientation class itself is zero. -/
theorem orientation_square_zero (x y z : R)
    (h1 : x+y+z=0) (h2 : x*y+x*z+y*z=0) (h3 : x*y*z=0) :
    (orientationClass x y z)^2=0 := by
  rw [orientation_square_discriminant, h1, h2, h3]
  ring

#print axioms cyclic_cubic_orientation_numerator
#print axioms orientation_square_zero
end GSTSpectralBoundaryDefect
