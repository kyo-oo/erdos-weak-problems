import GSTGraphV2UnifiedPowerRectangle

set_option maxRecDepth 1000000
set_option maxHeartbeats 10000000

namespace GSTGraphV2UnifiedVerticalTelescope

open GST2DMixedEmergence
open GSTGraphV2CoupledUFlux
open GSTGraphV2UnifiedPowerRectangle
open GSTGraphV2InfiniteControl

private theorem state_eq_of_fields
    (a b : State)
    (hParentSeed : a.parentSeed = b.parentSeed)
    (hParentOffset : a.parentOffset = b.parentOffset)
    (hChildCarry : a.childCarry = b.childCarry)
    (hChildTail : a.childTail = b.childTail) : a = b := by
  cases a
  cases b
  simp_all

/-- Exact macro x4/base3 balance of one horizontal carry word. -/
theorem carryWord_vertical_balance
    (E p start : Nat) : ∀ N : Nat,
    carryWord E p start N +
        4^N * (graph E start p).seven.digit =
      (graph E (start+N) p).seven.digit +
        3 * carryWord E (p+1) start N := by
  intro N
  induction N with
  | zero =>
      simp [carryWord]
  | succ N ih =>
      let C := (graph E (start+N) p).seven.carry
      let d := (graph E (start+N) p).seven.digit
      have hcell := graph_cell_exact E (start+N) p
      have hmass0 : C + 4*d = outDigit C d + 3*nextCarry C d := by
        have h := Nat.mod_add_div (C + 4*d) 3
        dsimp [C, d]
        unfold outDigit nextCarry
        omega
      have hmass :
          C + 4*d =
            (graph E (start+(N+1)) p).seven.digit +
              3 * (graph E (start+N) (p+1)).seven.carry := by
        have hidx : (start+N)+1 = start+(N+1) := by omega
        rw [← hidx, ← hcell.1, ← hcell.2]
        exact hmass0
      rw [carryWord, carryWord, Nat.pow_succ]
      calc
        4 * carryWord E p start N + C +
            (4^N * 4) * (graph E start p).seven.digit =
          4 * (carryWord E p start N +
            4^N * (graph E start p).seven.digit) + C := by ring
        _ = 4 * ((graph E (start+N) p).seven.digit +
              3 * carryWord E (p+1) start N) + C := by rw [ih]
        _ = (graph E (start+(N+1)) p).seven.digit +
              3 * (4 * carryWord E (p+1) start N +
                (graph E (start+N) (p+1)).seven.carry) := by
          dsimp [C, d] at hmass ⊢
          omega

/-- The macro parent-offset update of Equation III is exactly the next
vertical carry word of the same rectangle. -/
theorem unifiedState_parentOffset_step_exact
    (E N p : Nat) :
    ((unifiedState E N p).core.parentOffset +
        4^N * childDigit (unifiedState E N p).core) / 3 =
      (unifiedState E N (p+1)).core.parentOffset := by
  rw [unifiedState_childDigit_exact]
  have hbal := carryWord_vertical_balance E p 0 N
  simp only [Nat.zero_add] at hbal
  dsimp [unifiedState]
  rw [hbal]
  have hd := graph_digit_lt_three E N p
  have h3 : 0 < (3:Nat) := by decide
  rw [Nat.add_mul_div_left _ _ h3, Nat.div_eq_of_lt hd, Nat.zero_add]

/-- A vertical Equation-III step is exactly the next rectangle state. -/
theorem unifiedState_core_step_exact
    (E N p : Nat) :
    stepWith gstStepCarryExact (4^N) (unifiedState E N p).core =
      (unifiedState E N (p+1)).core := by
  apply state_eq_of_fields
  · dsimp [stepWith]
    rw [unifiedState_parentDigit_exact]
    have h := (graph_cell_exact E N p).2
    simpa [unifiedState, gstStepCarryExact, nextCarry] using h
  · dsimp [stepWith]
    exact unifiedState_parentOffset_step_exact E N p
  · dsimp [stepWith]
    rw [unifiedState_childDigit_exact]
    have h := (graph_cell_exact E 0 p).2
    simpa [unifiedState, gstStepCarryExact, nextCarry] using h
  · dsimp [stepWith, unifiedState]
    rw [Nat.div_div_eq_div_mul, Nat.pow_succ]

/-- Equation III with its derivative closed entirely inside the existing graph. -/
theorem unified_equationIII_graph_closed
    (E N p : Nat) :
    gstUJumpExact
        (graph E N p).seven.carry
        (graph E N p).seven.digit -
      ((4^N : Nat) : Int) *
        gstUJumpExact
          (graph E 0 p).seven.carry
          (graph E 0 p).seven.digit =
      3 * potentialWith gstUChargeExact (4^N)
          (unifiedState E N (p+1)).core -
        potentialWith gstUChargeExact (4^N)
          (unifiedState E N p).core := by
  rw [← unifiedState_core_step_exact E N p]
  exact unified_equationIII_graph_exact E N p

/-- Exact vertical telescope of the unified rectangle. -/
theorem unified_equationIII_vertical_telescope
    (E N p K : Nat) :
    Finset.sum (Finset.range K) (fun j =>
      (((3^j : Nat) : Int)) *
        (gstUJumpExact
            (graph E N (p+j)).seven.carry
            (graph E N (p+j)).seven.digit -
          ((4^N : Nat) : Int) *
            gstUJumpExact
              (graph E 0 (p+j)).seven.carry
              (graph E 0 (p+j)).seven.digit)) =
      (((3^K : Nat) : Int)) *
          potentialWith gstUChargeExact (4^N)
            (unifiedState E N (p+K)).core -
        potentialWith gstUChargeExact (4^N)
          (unifiedState E N p).core := by
  induction K with
  | zero => simp
  | succ K ih =>
      rw [Finset.sum_range_succ, ih]
      rw [unified_equationIII_graph_closed E N (p+K)]
      have hidx : p + (K+1) = (p+K)+1 := by omega
      rw [hidx, Nat.pow_succ]
      push_cast
      ring

#check carryWord_vertical_balance
#check unifiedState_core_step_exact
#check unified_equationIII_graph_closed
#check unified_equationIII_vertical_telescope
#print axioms unifiedState_core_step_exact
#print axioms unified_equationIII_vertical_telescope

end GSTGraphV2UnifiedVerticalTelescope