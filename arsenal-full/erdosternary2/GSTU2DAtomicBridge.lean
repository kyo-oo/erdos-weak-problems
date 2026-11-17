import GSTGraphV2CoupledUPhysicalBridge
import GST2DMixedEmergence

set_option maxRecDepth 1000000
set_option maxHeartbeats 10000000

namespace GSTU2DAtomicBridge

open GSTGraphV2CoupledUFlux
open GSTGraphV2CoupledUPhysicalBridge
open GST2DMixedEmergence

/-- The handwritten U chart and the carry potential selected by the 2D mixed
system are the same four-state object in different gauges. -/
theorem gst_u_charge_as_carry_potential
    (C : Nat) (hC : C < 4) :
    gstUChargeExact C = 8 * (C : Int) - carryPotential C := by
  have hcases : C = 0 ∨ C = 1 ∨ C = 2 ∨ C = 3 := by omega
  rcases hcases with rfl | rfl | rfl | rfl <;>
    norm_num [gstUChargeExact, carryPotential]

/-- Equation III rewritten entirely in the carry potential used by the 2D
mixed-emergence theorem.  `childResidue - parentOffset` is the finite shared
horizontal remainder; no terminal-height assumption appears. -/
theorem gst_coupled_potential_as_mixed_boundary
    (A : Nat) (st : PhysicalState)
    (hInv : PhysicalInvariant A st)
    (hParent : st.core.parentSeed < 4)
    (hChild : st.core.childCarry < 4) :
    potentialWith gstUChargeExact A st.core =
      (A : Int) * carryPotential st.core.childCarry -
        carryPotential st.core.parentSeed +
        8 * ((st.childResidue : Int) - (st.core.parentOffset : Int)) := by
  have hP := gst_u_charge_as_carry_potential st.core.parentSeed hParent
  have hC := gst_u_charge_as_carry_potential st.core.childCarry hChild
  unfold PhysicalInvariant at hInv
  have hInvZ :
      (st.core.parentSeed : Int) + 4 * (st.core.parentOffset : Int) =
        (st.childResidue : Int) +
          (A : Int) * (st.core.childCarry : Int) := by
    exact_mod_cast hInv
  unfold potentialWith
  rw [hP, hC]
  ring_nf at hInvZ ⊢
  linarith

/-- One horizontally weighted row of the mixed 2D law.  The weight is
arbitrary: the geometric `4`-weights required by Equation III are therefore a
direct specialization of the proved identity. -/
theorem weighted_mixed_row_emergence
    (w : Nat → Int)
    (C Cnext d : Nat → Nat) (N : Nat)
    (hcell : ∀ t, t < N →
      C t < 4 ∧ d t < 3 ∧
      outDigit (C t) (d t) = d (t+1) ∧
      nextCarry (C t) (d t) = Cnext t) :
    Finset.sum (Finset.range N) (fun t =>
      w t * mixedDensity (C t) (d t)) =
      Finset.sum (Finset.range N) (fun t =>
        w t * (infoPotential (d (t+1)) - infoPotential (d t))) +
      7 * (Finset.sum (Finset.range N) (fun t =>
          w t * carryPotential (C t)) -
        3 * Finset.sum (Finset.range N) (fun t =>
          w t * carryPotential (Cnext t))) +
      56 * Finset.sum (Finset.range N) (fun t =>
        w t * surviveI (C t) (d t)) := by
  have hlocal :
      Finset.sum (Finset.range N) (fun t =>
        w t * mixedDensity (C t) (d t)) =
      Finset.sum (Finset.range N) (fun t =>
        w t * (infoPotential (d (t+1)) - infoPotential (d t)) +
        7 * (w t * carryPotential (C t) -
          3 * (w t * carryPotential (Cnext t))) +
        56 * (w t * surviveI (C t) (d t))) := by
    apply Finset.sum_congr rfl
    intro t ht
    rcases hcell t (Finset.mem_range.mp ht) with
      ⟨hC, hd, hout, hnext⟩
    rw [mixed_cell_emergence (C t) (d t) hC hd, hout, hnext]
    ring
  rw [hlocal, Finset.sum_add_distrib, Finset.sum_add_distrib]
  rw [← Finset.mul_sum, ← Finset.mul_sum]
  rw [Finset.sum_sub_distrib]
  rw [← Finset.mul_sum]

/-- **Equation III × 2D mixed divergence.**

The 2D theorem remains valid after an arbitrary fixed horizontal weighting.
The vertical `3^p` weight still telescopes the carry potential exactly, while
all BIG1/SURVIVE information remains explicit.  Choosing the reverse
base-four carry-word weights gives the physical orientation of Equation III. -/
theorem weighted_mixed_rectangle_emergence
    (w : Nat → Int)
    (C d : Nat → Nat → Nat) (N K : Nat)
    (hcell : ∀ t p, t < N → p < K →
      C t p < 4 ∧ d t p < 3 ∧
      outDigit (C t p) (d t p) = d (t+1) p ∧
      nextCarry (C t p) (d t p) = C t (p+1)) :
    Finset.sum (Finset.range K) (fun p =>
      (3 : Int)^p * Finset.sum (Finset.range N) (fun t =>
        w t * mixedDensity (C t p) (d t p))) =
      Finset.sum (Finset.range K) (fun p =>
        (3 : Int)^p * Finset.sum (Finset.range N) (fun t =>
          w t * (infoPotential (d (t+1) p) - infoPotential (d t p)))) +
      7 * (Finset.sum (Finset.range N) (fun t =>
          w t * carryPotential (C t 0)) -
        (3 : Int)^K * Finset.sum (Finset.range N) (fun t =>
          w t * carryPotential (C t K))) +
      56 * Finset.sum (Finset.range K) (fun p =>
        (3 : Int)^p * Finset.sum (Finset.range N) (fun t =>
          w t * surviveI (C t p) (d t p))) := by
  induction K with
  | zero => simp
  | succ K ih =>
      have hprefix : ∀ t p, t < N → p < K →
          C t p < 4 ∧ d t p < 3 ∧
          outDigit (C t p) (d t p) = d (t+1) p ∧
          nextCarry (C t p) (d t p) = C t (p+1) := by
        intro t p ht hp
        exact hcell t p ht (by omega)
      have ih' := ih hprefix
      have hrow := weighted_mixed_row_emergence
        w (fun t => C t K) (fun t => C t (K+1))
        (fun t => d t K) N
        (by
          intro t ht
          exact hcell t K ht (by omega))
      rw [Finset.sum_range_succ, ih', hrow]
      simp only [Finset.sum_range_succ]
      rw [pow_succ]
      ring

/-- Exact geometric horizontal summation.  This is the algebraic kernel used
when the arbitrary weight in `weighted_mixed_rectangle_emergence` is chosen to
be a power of four. -/
theorem weighted_info_boundary_exact
    (f : Nat → Int) : ∀ N : Nat,
    Finset.sum (Finset.range (N+1)) (fun t =>
      (4 : Int)^t * (f (t+1) - f t)) =
      (4 : Int)^N * f (N+1) - f 0 -
        3 * Finset.sum (Finset.range N) (fun t =>
          (4 : Int)^t * f (t+1)) := by
  intro N
  induction N with
  | zero => simp
  | succ N ih =>
      rw [Finset.sum_range_succ, ih, Finset.sum_range_succ]
      rw [pow_succ]
      ring

/-- On a physical ternary digit the horizontal potential is non-positive and
is supported exactly on BIG1. -/
theorem infoPotential_nonpositive
    (d : Nat) (hd : d < 3) : infoPotential d ≤ 0 := by
  have hcases : d = 0 ∨ d = 1 ∨ d = 2 := by omega
  rcases hcases with rfl | rfl | rfl <;>
    norm_num [infoPotential, twoI]

#check gst_u_charge_as_carry_potential
#check gst_coupled_potential_as_mixed_boundary
#check weighted_mixed_row_emergence
#check weighted_mixed_rectangle_emergence
#check weighted_info_boundary_exact
#print axioms gst_coupled_potential_as_mixed_boundary
#print axioms weighted_mixed_rectangle_emergence
#print axioms weighted_info_boundary_exact

end GSTU2DAtomicBridge
