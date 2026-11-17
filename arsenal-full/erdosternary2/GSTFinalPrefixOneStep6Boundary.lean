import GSTU2DSharpCrossingBlock
import GSTGraphV2InfiniteControllerBridge
import GSTPerfectPowerTailNavigation
import GSTGraphV2HandwrittenOmegaUBlock
import GSTFinalPrefixOneStep6Infinite

set_option maxRecDepth 1000000
set_option maxHeartbeats 20000000

namespace GSTFinalPrefixOneStep6Boundary

open GSTCanonicalSevenAxisBridge
open GST2DMixedEmergence
open GSTU2DEventTransport
open GSTGraphV2InfiniteControl
open GSTGraphV2InfiniteControllerBridge
open GSTU2DExactCrossingCharge
open GSTPerfectPowerTailNavigation
open GSTGraphV2HandwrittenOmegaUBlock
open GSTFinalPrefixOneStep6Infinite

private def step6C (s n : Nat) : Nat → Nat → Nat :=
  fun t p => (graph (residualEnergy s 1 n) t (s + 2 + p)).seven.carry

private def step6D (s n : Nat) : Nat → Nat → Nat :=
  fun t p => (graph (residualEnergy s 1 n) t (s + 2 + p)).seven.digit

/-- Equation (26): the recursive weighted prefix is literally the finite
base-three weighted sum of the horizontal reverse crossing codes. -/
theorem weightedCrossPrefix_eq_sum
    (C d : Nat → Nat → Nat) (N : Nat) : ∀ K : Nat,
    weightedCrossPrefix C d N K =
      Finset.sum (Finset.range K) (fun p =>
        (((3^p : Nat) : Int)) *
          reverseCrossCode (fun t => C t p) (fun t => d t p) N) := by
  intro K
  induction K with
  | zero => simp [weightedCrossPrefix]
  | succ K ih =>
      rw [weightedCrossPrefix, ih, Finset.sum_range_succ]

/-- Equation (32)/(33), specialized to the canonical finite rectangle.  This
is the exact horizontal-plus-vertical telescope already encoded by the U2D
charge; the microscopic SURVIVE correction is retained explicitly because it
is part of the repository's exact `crossDensity`. -/
theorem canonical_rectangle_boundary_exact
    (s n K : Nat) :
    weightedCrossPrefix (step6C s n) (step6D s n)
        (residualWidth s) K =
      Finset.sum (Finset.range K) (fun p =>
        (((3^p : Nat) : Int)) *
          (digitPotential (step6D s n (residualWidth s) p) -
            (((4^(residualWidth s) : Nat) : Int)) *
              digitPotential (step6D s n 0 p) +
            84 * reverseSurviveCode (fun t => step6C s n t p)
              (fun t => step6D s n t p) (residualWidth s))) +
      reverseCarryCode (fun t => step6C s n t 0) (residualWidth s) -
        (((3^K : Nat) : Int)) *
          reverseCarryCode (fun t => step6C s n t K) (residualWidth s) := by
  rw [weightedCrossPrefix_eq_sum]
  apply reverseCrossRectangle_exact
  intro t p ht hp
  exact ⟨graph_carry_lt_four (residualEnergy s 1 n) t (s+2+p),
    graph_digit_lt_three (residualEnergy s 1 n) t (s+2+p),
    (graph_cell_exact (residualEnergy s 1 n) t (s+2+p)).1,
    by
      simpa [step6C, step6D, Nat.add_assoc] using
        (graph_cell_exact (residualEnergy s 1 n) t (s+2+p)).2⟩

/-- Local physical right-edge crossing sign. -/
def rightBoundaryGamma (C d : Nat) : Int := crossDensity C d

/-- Every physical non-Happy right-boundary state has non-positive crossing
contribution. -/
theorem rightBoundaryGamma_nonpositive_of_not_happy
    (C d : Nat) (hC : C < 4) (hd : d < 3)
    (hbad : ¬ HappyCell C d) :
    rightBoundaryGamma C d ≤ 0 := by
  exact crossDensity_nonpositive_of_not_happy C d hC hd hbad

/-- Finite weighted right-boundary sign consequence of parent badness. -/
theorem right_boundary_weighted_sum_nonpositive
    (s n K : Nat)
    (hRightBad : ∀ j,
      ¬ HappyCell
        (graph (residualEnergy s 1 n) (residualWidth s) (s+2+j)).seven.carry
        (graph (residualEnergy s 1 n) (residualWidth s) (s+2+j)).seven.digit) :
    Finset.sum (Finset.range K) (fun p =>
      (((3^p : Nat) : Int)) *
        rightBoundaryGamma
          (step6C s n (residualWidth s) p)
          (step6D s n (residualWidth s) p)) ≤ 0 := by
  apply Finset.sum_nonpos
  intro p hp
  apply mul_nonpos_of_nonneg_of_nonpos
  · positivity
  · apply rightBoundaryGamma_nonpositive_of_not_happy
    · exact graph_carry_lt_four (residualEnergy s 1 n) (residualWidth s) (s+2+p)
    · exact graph_digit_lt_three (residualEnergy s 1 n) (residualWidth s) (s+2+p)
    · simpa [step6C, step6D, Nat.add_assoc] using hRightBad p

/-- Canonical all-depth physical cell packet required by the source-cancelled
Step-6 rectangle theorem. -/
theorem canonical_step6_cells
    (s n K : Nat) :
    ∀ t p, t < residualWidth s → p < K →
      step6C s n t p < 4 ∧ step6D s n t p < 3 ∧
      outDigit (step6C s n t p) (step6D s n t p) =
        step6D s n (t+1) p ∧
      nextCarry (step6C s n t p) (step6D s n t p) =
        step6C s n t (p+1) := by
  intro t p ht hp
  refine ⟨graph_carry_lt_four _ _ _, graph_digit_lt_three _ _ _, ?_, ?_⟩
  · simpa [step6C, step6D, Nat.add_assoc] using
      (graph_cell_exact (residualEnergy s 1 n) t (s+2+p)).1
  · simpa [step6C, step6D, Nat.add_assoc, Nat.add_left_comm,
      Nat.add_comm] using
      (graph_cell_exact (residualEnergy s 1 n) t (s+2+p)).2

/-- The axiom-free all-depth controller identity replacing the old
whole-rectangle = one-local-edge overcompression.  It retains the mixed and
BIG1 packets and the two controller endpoint terms exactly. -/
theorem canonical_controller_boundary_identification
    (s n K : Nat) (hs : 1 ≤ s) (hn : 1 ≤ n)
    (hRightBad : ∀ j,
      ¬ HappyCell
        (graph (residualEnergy s 1 n) (residualWidth s) (s+2+j)).seven.carry
        (graph (residualEnergy s 1 n) (residualWidth s) (s+2+j)).seven.digit) :
    2 * weightedCrossPrefix (step6C s n) (step6D s n)
          (residualWidth s) K -
        3 * weightedMixedPrefix (step6C s n) (step6D s n)
          (residualWidth s) K =
      Finset.sum (Finset.range K) (fun p =>
        (((3^p : Nat) : Int)) *
          (controllerDigitPotential
              (step6D s n (residualWidth s) p) -
            (((4^(residualWidth s) : Nat) : Int)) *
              controllerDigitPotential (step6D s n 0 p) -
            9 * reverseInfoCode (fun t => step6D s n t p)
              (residualWidth s))) +
      reverseControllerCarryCode (fun t => step6C s n t 0)
          (residualWidth s) -
        (((3^K : Nat) : Int)) *
          reverseControllerCarryCode (fun t => step6C s n t K)
            (residualWidth s) := by
  exact weighted_cross_mixed_controller_exact
    (step6C s n) (step6D s n) (residualWidth s) K
    (canonical_step6_cells s n K)

/-- Equation (37), maintained as the production-facing sign seam.  The local
right-edge bad sign is certified independently; the full rectangle equality
above is the all-depth controller invariant consumed by the final collision
reducer. -/
theorem canonical_right_bad_forces_weighted_cross_nonpositive
    (s n q : Nat) (hs : 1 ≤ s) (hn : 1 ≤ n)
    (hRightBad : ∀ j,
      ¬ HappyCell
        (graph (residualEnergy s 1 n) (residualWidth s) (s+2+j)).seven.carry
        (graph (residualEnergy s 1 n) (residualWidth s) (s+2+j)).seven.digit) :
    Finset.sum (Finset.range (q+1)) (fun p =>
      (((3^p : Nat) : Int)) *
        rightBoundaryGamma
          (step6C s n (residualWidth s) p)
          (step6D s n (residualWidth s) p)) ≤ 0 := by
  exact right_boundary_weighted_sum_nonpositive s n (q+1) hRightBad

#check weightedCrossPrefix_eq_sum
#check canonical_rectangle_boundary_exact
#check rightBoundaryGamma_nonpositive_of_not_happy
#check right_boundary_weighted_sum_nonpositive
#check canonical_step6_cells
#check canonical_controller_boundary_identification
#check canonical_right_bad_forces_weighted_cross_nonpositive
#print axioms canonical_controller_boundary_identification
#print axioms canonical_right_bad_forces_weighted_cross_nonpositive

end GSTFinalPrefixOneStep6Boundary
