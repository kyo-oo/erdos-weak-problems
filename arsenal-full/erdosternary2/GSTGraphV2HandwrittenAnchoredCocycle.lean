import GSTGraphV2HandwrittenExponentialLTE
import GSTGraphV2UnifiedVerticalTelescope

set_option maxRecDepth 1000000
set_option maxHeartbeats 10000000

namespace GSTGraphV2HandwrittenAnchoredCocycle

open GSTCanonicalSevenAxisBridge
open GST2DMixedEmergence
open GSTU2DEventTransport
open GSTGraphV2InfiniteControl
open GSTGraphV2CoupledUFlux
open GSTGraphV2UnifiedPowerRectangle
open GSTGraphV2UnifiedVerticalTelescope
open GSTGraphV2PerfectPowerBlock
open GSTGraphV2HandwrittenExponentialCascade
open GSTGraphV2HandwrittenExponentialLTE

/-!
# Handwritten U anchored cocycle on the full GST Graph V2

This is the missing horizontal composition law for the handwritten exponential
operator.  It does not move a Happy bit by assumption.  Instead it composes the
exact retained U potential of two adjacent rectangles of the *same* infinite
Graph-V2 sheet.
-/

/-- Direct physical U potential of an arbitrary horizontal Graph-V2 interval. -/
def graphUPotential (E start N p : Nat) : Int :=
  gstUChargeExact (graph E (start+N) p).seven.carry -
    (((4^N : Nat) : Int)) * gstUChargeExact (graph E start p).seven.carry +
    24 * (carryWord E p start N : Int)

/-- Reverse-base-four words concatenate exactly. -/
theorem carryWord_append_exact
    (E p start P : Nat) : ∀ N : Nat,
    carryWord E p start (P+N) =
      4^N * carryWord E p start P + carryWord E p (start+P) N := by
  intro N
  induction N with
  | zero => simp [carryWord]
  | succ N ih =>
      have hlen : P + (N+1) = (P+N)+1 := by omega
      have hidx : start + (P+N) = (start+P)+N := by omega
      rw [hlen, carryWord, ih, carryWord, Nat.pow_succ, hidx]
      ring

/-- **Universal Graph-V2 U cocycle.** -/
theorem graph_u_potential_cocycle_exact
    (E start P N p : Nat) :
    graphUPotential E start (P+N) p =
      graphUPotential E (start+P) N p +
        (((4^N : Nat) : Int)) * graphUPotential E start P p := by
  unfold graphUPotential
  rw [carryWord_append_exact]
  have hidx : start + (P+N) = (start+P)+N := by omega
  have hpow : 4^(P+N) = 4^P * 4^N := Nat.pow_add 4 P N
  rw [hidx, hpow]
  push_cast
  ring

/-- **Shifted Equation III on an arbitrary interval of the same Graph-V2
sheet.** -/
theorem graph_u_equationIII_shifted_exact
    (E start N p : Nat) :
    gstUJumpExact
        (graph E (start+N) p).seven.carry
        (graph E (start+N) p).seven.digit -
      (((4^N : Nat) : Int)) *
        gstUJumpExact
          (graph E start p).seven.carry
          (graph E start p).seven.digit =
      3 * graphUPotential E start N (p+1) -
        graphUPotential E start N p := by
  have hLeftNext :
      gstStepCarryExact
          (graph E start p).seven.carry
          (graph E start p).seven.digit =
        (graph E start (p+1)).seven.carry := by
    simpa [gstStepCarryExact, nextCarry] using
      (graph_cell_exact E start p).2
  have hRightNext :
      gstStepCarryExact
          (graph E (start+N) p).seven.carry
          (graph E (start+N) p).seven.digit =
        (graph E (start+N) (p+1)).seven.carry := by
    simpa [gstStepCarryExact, nextCarry] using
      (graph_cell_exact E (start+N) p).2
  have hWordNat := carryWord_vertical_balance E p start N
  have hWordInt :
      (carryWord E p start N : Int) +
          (((4^N : Nat) : Int)) * ((graph E start p).seven.digit : Int) =
        ((graph E (start+N) p).seven.digit : Int) +
          3 * (carryWord E (p+1) start N : Int) := by
    exact_mod_cast hWordNat
  unfold graphUPotential gstUJumpExact jumpWith
  rw [hLeftNext, hRightNext]
  nlinarith [hWordInt]

/-- Weighted vertical telescope of the shifted Equation III. -/
theorem graph_u_equationIII_shifted_telescope
    (E start N p K : Nat) :
    Finset.sum (Finset.range K) (fun j =>
      (((3^j : Nat) : Int)) *
        (gstUJumpExact
            (graph E (start+N) (p+j)).seven.carry
            (graph E (start+N) (p+j)).seven.digit -
          (((4^N : Nat) : Int)) *
            gstUJumpExact
              (graph E start (p+j)).seven.carry
              (graph E start (p+j)).seven.digit)) =
      (((3^K : Nat) : Int)) * graphUPotential E start N (p+K) -
        graphUPotential E start N p := by
  induction K with
  | zero => simp
  | succ K ih =>
      rw [Finset.sum_range_succ, ih]
      rw [graph_u_equationIII_shifted_exact E start N (p+K)]
      have hidx : p + (K+1) = (p+K)+1 := by omega
      rw [hidx, Nat.pow_succ]
      push_cast
      ring

/-- On the twelve physical GST cells, a Happy Gate is exactly a negative U
jump.  This gives the ordered form needed by the monolith surgery. -/
theorem happy_iff_gst_u_jump_negative
    (C d : Nat) (hC : C < 4) (hd : d < 3) :
    HappyCell C d ↔ gstUJumpExact C d < 0 := by
  have hCc : C = 0 ∨ C = 1 ∨ C = 2 ∨ C = 3 := by omega
  have hdc : d = 0 ∨ d = 1 ∨ d = 2 := by omega
  rcases hCc with rfl | rfl | rfl | rfl <;>
    rcases hdc with rfl | rfl | rfl <;>
    norm_num [HappyCell, gstUJumpExact, jumpWith, gstUChargeExact,
      gstStepCarryExact]

/-- A non-Happy physical cell has nonnegative U jump. -/
theorem gst_u_jump_nonnegative_of_not_happy
    (C d : Nat) (hC : C < 4) (hd : d < 3)
    (hbad : ¬ HappyCell C d) :
    0 ≤ gstUJumpExact C d := by
  by_contra hneg
  have hj : gstUJumpExact C d < 0 := by omega
  exact hbad ((happy_iff_gst_u_jump_negative C d hC hd).2 hj)

/-- At a child Happy Gate whose right endpoint is bad, the shifted Equation-III
derivative is strictly positive. -/
theorem graph_u_derivative_positive_of_child_happy_right_bad
    (E start N p : Nat)
    (hChild : HappyCell
      (graph E start p).seven.carry (graph E start p).seven.digit)
    (hRight : ¬ HappyCell
      (graph E (start+N) p).seven.carry (graph E (start+N) p).seven.digit) :
    0 < 3 * graphUPotential E start N (p+1) -
      graphUPotential E start N p := by
  have hLc := graph_carry_lt_four E start p
  have hLd := graph_digit_lt_three E start p
  have hRc := graph_carry_lt_four E (start+N) p
  have hRd := graph_digit_lt_three E (start+N) p
  have hLneg :
      gstUJumpExact (graph E start p).seven.carry
        (graph E start p).seven.digit < 0 :=
    (happy_iff_gst_u_jump_negative _ _ hLc hLd).1 hChild
  have hRnonneg :
      0 ≤ gstUJumpExact (graph E (start+N) p).seven.carry
        (graph E (start+N) p).seven.digit :=
    gst_u_jump_nonnegative_of_not_happy _ _ hRc hRd hRight
  have hpow : (0 : Int) < (((4^N : Nat) : Int)) := by positivity
  have hEq := graph_u_equationIII_shifted_exact E start N p
  nlinarith

/-- The horizontal cocycle and shifted Equation III commute exactly. -/
theorem graph_u_jump_cocycle_exact
    (E start P N p : Nat) :
    (gstUJumpExact
        (graph E (start+(P+N)) p).seven.carry
        (graph E (start+(P+N)) p).seven.digit -
      (((4^(P+N) : Nat) : Int)) *
        gstUJumpExact
          (graph E start p).seven.carry
          (graph E start p).seven.digit) =
      (gstUJumpExact
          (graph E ((start+P)+N) p).seven.carry
          (graph E ((start+P)+N) p).seven.digit -
        (((4^N : Nat) : Int)) *
          gstUJumpExact
            (graph E (start+P) p).seven.carry
            (graph E (start+P) p).seven.digit) +
      (((4^N : Nat) : Int)) *
        (gstUJumpExact
            (graph E (start+P) p).seven.carry
            (graph E (start+P) p).seven.digit -
          (((4^P : Nat) : Int)) *
            gstUJumpExact
              (graph E start p).seven.carry
              (graph E start p).seven.digit) := by
  have hidx : start + (P+N) = (start+P)+N := by omega
  have hpow : 4^(P+N) = 4^P * 4^N := Nat.pow_add 4 P N
  rw [hidx, hpow]
  push_cast
  ring

/-- The handwritten cascade re-coordinates the canonical full-energy sheet onto
one tail-energy sheet at a consumed-prefix horizontal phase. -/
theorem canonical_u_recoordinate_exact
    (s n q x p : Nat) :
    (graph (canonicalEnergy s n) x p).seven.carry =
        (graph (uTailEnergy (s+1) n (q+1))
          (uPhaseShift (s+1) n (q+1) + x) p).seven.carry ∧
    (graph (canonicalEnergy s n) x p).seven.digit =
        (graph (uTailEnergy (s+1) n (q+1))
          (uPhaseShift (s+1) n (q+1) + x) p).seven.digit ∧
    (graph (canonicalEnergy s n) x p).eventCode =
        (graph (uTailEnergy (s+1) n (q+1))
          (uPhaseShift (s+1) n (q+1) + x) p).eventCode ∧
    (graph (canonicalEnergy s n) x p).uCharge =
        (graph (uTailEnergy (s+1) n (q+1))
          (uPhaseShift (s+1) n (q+1) + x) p).uCharge := by
  have h := graph_u_block_observables_exact (s+1) n (q+1) x p
  simpa [canonicalEnergy] using ⟨h.1, h.2.1, h.2.2.2.2.2.1, h.2.2.2.2.2.2.1⟩

/-- **Advanced handwritten application at the production cut.** -/
theorem handwritten_u_anchored_cocycle_exact
    (s n q : Nat) (hs : 1 ≤ s) :
    let T := uTailEnergy (s+1) n (q+1)
    let P := uPhaseShift (s+1) n (q+1)
    let N := canonicalWidth s
    let p := s+2+q
    (graph T 0 p).seven.carry = 0 ∧
    (graph T 0 p).seven.digit = 0 ∧
    (graph (canonicalEnergy s n) 0 p).seven.carry =
      (graph T P p).seven.carry ∧
    (graph (canonicalEnergy s n) 0 p).seven.digit =
      (graph T P p).seven.digit ∧
    (graph (canonicalEnergy s n) N p).seven.carry =
      (graph T (P+N) p).seven.carry ∧
    (graph (canonicalEnergy s n) N p).seven.digit =
      (graph T (P+N) p).seven.digit ∧
    graphUPotential T 0 (P+N) p =
      graphUPotential T P N p +
        (((4^N : Nat) : Int)) * graphUPotential T 0 P p := by
  dsimp only
  have hneutral := canonical_child_u_cut_neutral s n q hs
  have hchild := canonical_u_recoordinate_exact s n q 0 (s+2+q)
  have hparent := canonical_u_recoordinate_exact
    s n q (canonicalWidth s) (s+2+q)
  refine ⟨hneutral.1, hneutral.2.1, ?_, ?_, ?_, ?_, ?_⟩
  · simpa using hchild.1
  · simpa using hchild.2.1
  · simpa [Nat.add_assoc] using hparent.1
  · simpa [Nat.add_assoc] using hparent.2.1
  · simpa using graph_u_potential_cocycle_exact
      (uTailEnergy (s+1) n (q+1)) 0
      (uPhaseShift (s+1) n (q+1)) (canonicalWidth s) (s+2+q)

#check carryWord_append_exact
#check graph_u_potential_cocycle_exact
#check graph_u_equationIII_shifted_exact
#check graph_u_equationIII_shifted_telescope
#check happy_iff_gst_u_jump_negative
#check graph_u_derivative_positive_of_child_happy_right_bad
#check graph_u_jump_cocycle_exact
#check canonical_u_recoordinate_exact
#check handwritten_u_anchored_cocycle_exact
#print axioms graph_u_equationIII_shifted_telescope
#print axioms graph_u_derivative_positive_of_child_happy_right_bad
#print axioms handwritten_u_anchored_cocycle_exact

end GSTGraphV2HandwrittenAnchoredCocycle
