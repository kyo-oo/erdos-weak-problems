import GSTGraphV2InfiniteControl
import GSTGraphV2CoupledUPhysicalBridge

set_option maxRecDepth 1000000
set_option maxHeartbeats 10000000

namespace GSTGraphV2UnifiedPowerRectangle

open GST2DMixedEmergence
open GSTU2DEventTransport
open GSTGraphV2CoupledUFlux
open GSTGraphV2CoupledUPhysicalBridge
open GSTGraphV2InfiniteControl

/-!
# Old-Sol coupled state = one finite rectangle of the main infinite GST graph

No new graph is introduced here.  `graph E t p` remains the sole arithmetic
object.  `carryWord` merely reads a finite horizontal observation of that graph
in the same reverse-base-four orientation used by Old Sol's Equation-III
physical bridge.
-/

/-- Reverse-base-four word of the physical carries in one horizontal row,
starting at graph column `start`. -/
def carryWord (E p start : Nat) : Nat → Nat
  | 0 => 0
  | N+1 => 4 * carryWord E p start N +
      (graph E (start+N) p).seven.carry

/-- A width-N carry word is a genuine N-digit base-four word. -/
theorem carryWord_lt_pow_four
    (E p start : Nat) : ∀ N : Nat,
    carryWord E p start N < 4^N := by
  intro N
  induction N with
  | zero =>
      simp [carryWord]
  | succ N ih =>
      have hc := graph_carry_lt_four E (start+N) p
      rw [carryWord, Nat.pow_succ]
      omega

/-- Split the oldest/leftmost carry from a reverse-base-four carry word. -/
theorem carryWord_head_split
    (E p start : Nat) : ∀ N : Nat,
    carryWord E p start (N+1) =
      4^N * (graph E start p).seven.carry +
        carryWord E p (start+1) N := by
  intro N
  induction N with
  | zero =>
      simp [carryWord]
  | succ N ih =>
      have hidx : start + (N+1) = (start+1) + N := by omega
      rw [carryWord, ih, carryWord, Nat.pow_succ, hidx]
      ring

/-- The same word is also rightmost carry plus four times the preceding word. -/
theorem carryWord_tail_split
    (E p N : Nat) :
    carryWord E p 0 (N+1) =
      (graph E N p).seven.carry + 4 * carryWord E p 0 N := by
  rw [carryWord]
  simp only [Nat.zero_add]
  ac_rfl

/-- Macro horizontal digit transport: the carry word plus `4^N` copies of the
left information digit emits exactly the information digit at column N. -/
theorem carryWord_digit_transport
    (E p start : Nat) : ∀ N : Nat,
    (carryWord E p start N +
        4^N * (graph E start p).seven.digit) % 3 =
      (graph E (start+N) p).seven.digit := by
  intro N
  induction N with
  | zero =>
      have hd := graph_digit_lt_three E start p
      simp [carryWord, Nat.mod_eq_of_lt hd]
  | succ N ih =>
      let C := (graph E (start+N) p).seven.carry
      let dN := (graph E (start+N) p).seven.digit
      have hcell := graph_cell_exact E (start+N) p
      have hshape :
          carryWord E p start (N+1) +
              4^(N+1) * (graph E start p).seven.digit =
            C + 4 *
              (carryWord E p start N +
                4^N * (graph E start p).seven.digit) := by
        dsimp [C]
        rw [carryWord, Nat.pow_succ]
        ring
      rw [hshape]
      have hmod :
          (C + 4 *
              (carryWord E p start N +
                4^N * (graph E start p).seven.digit)) % 3 =
            (C + 4 *
              ((carryWord E p start N +
                4^N * (graph E start p).seven.digit) % 3)) % 3 := by
        simp [Nat.add_mod, Nat.mul_mod]
      rw [hmod, ih]
      change outDigit C dN = (graph E (start + (N+1)) p).seven.digit
      have hidx : (start+N)+1 = start+(N+1) := by omega
      rw [← hidx]
      exact hcell.1

/-- Literal Old-Sol physical state extracted from one width-N rectangle of the
main infinite graph.  The low/right carry is `parentSeed`; the high/left carry
is `childCarry`; the finite interior words are retained explicitly. -/
def unifiedState (E N p : Nat) : PhysicalState :=
  {
    core := {
      parentSeed := (graph E N p).seven.carry
      parentOffset := carryWord E p 0 N
      childCarry := (graph E 0 p).seven.carry
      childTail := E / 3^p
    }
    childResidue := carryWord E p 1 N
  }

/-- The extracted rectangle satisfies Old Sol's fifth-coordinate physical
invariant exactly, with multiplier A=4^N. -/
theorem unifiedState_physicalInvariant
    (E N p : Nat) :
    PhysicalInvariant (4^N) (unifiedState E N p) := by
  unfold PhysicalInvariant unifiedState
  dsimp only
  have htail := carryWord_tail_split E p N
  have hhead := carryWord_head_split E p 0 N
  simp only [Nat.zero_add] at hhead
  calc
    (graph E N p).seven.carry + 4 * carryWord E p 0 N =
        carryWord E p 0 (N+1) := htail.symm
    _ = 4^N * (graph E 0 p).seven.carry + carryWord E p 1 N := hhead
    _ = carryWord E p 1 N + 4^N * (graph E 0 p).seven.carry := by ac_rfl

/-- The live high remainder is strictly below the macro multiplier. -/
theorem unifiedState_residue_lt
    (E N p : Nat) :
    (unifiedState E N p).childResidue < 4^N := by
  exact carryWord_lt_pow_four E p 1 N

/-- Both endpoint carries remain physical four-state GST coordinates. -/
theorem unifiedState_parentCarry_lt_four
    (E N p : Nat) :
    (unifiedState E N p).core.parentSeed < 4 := by
  exact graph_carry_lt_four E N p

theorem unifiedState_childCarry_lt_four
    (E N p : Nat) :
    (unifiedState E N p).core.childCarry < 4 := by
  exact graph_carry_lt_four E 0 p

/-- Old Sol's child information digit is literally the left boundary graph
digit. -/
theorem unifiedState_childDigit_exact
    (E N p : Nat) :
    childDigit (unifiedState E N p).core =
      (graph E 0 p).seven.digit := by
  simp [unifiedState, childDigit, graph, cell,
    GSTCanonicalSevenAxisBridge.vertex,
    GSTCanonicalSevenAxisBridge.digit3]

/-- Old Sol's macro parent digit is literally the right boundary graph digit. -/
theorem unifiedState_parentDigit_exact
    (E N p : Nat) :
    parentDigit (4^N) (unifiedState E N p).core =
      (graph E N p).seven.digit := by
  unfold parentDigit
  rw [unifiedState_childDigit_exact]
  simpa [unifiedState] using carryWord_digit_transport E p 0 N

/-- The U jump called "child" by Equation III is the actual left boundary cell
of the same rectangle. -/
theorem unifiedState_childJump_exact
    (E N p : Nat) :
    childJumpWith gstUChargeExact gstStepCarryExact
        (unifiedState E N p).core =
      gstUJumpExact
        (graph E 0 p).seven.carry
        (graph E 0 p).seven.digit := by
  unfold childJumpWith gstUJumpExact
  rw [unifiedState_childDigit_exact]
  rfl

/-- The U jump called "parent" by Equation III is the actual right boundary
cell of the same rectangle. -/
theorem unifiedState_parentJump_exact
    (E N p : Nat) :
    parentJumpWith gstUChargeExact gstStepCarryExact
        (4^N) (unifiedState E N p).core =
      gstUJumpExact
        (graph E N p).seven.carry
        (graph E N p).seven.digit := by
  unfold parentJumpWith gstUJumpExact
  rw [unifiedState_parentDigit_exact]
  rfl

/-- **Unified Equation III on the main GST graph.**
The right-boundary U jump minus `4^N` times the left-boundary U jump is exactly
the ternary derivative of Old Sol's retained coupled potential. -/
theorem unified_equationIII_graph_exact
    (E N p : Nat) :
    gstUJumpExact
        (graph E N p).seven.carry
        (graph E N p).seven.digit -
      ((4^N : Nat) : Int) *
        gstUJumpExact
          (graph E 0 p).seven.carry
          (graph E 0 p).seven.digit =
      3 * potentialWith gstUChargeExact (4^N)
          (stepWith gstStepCarryExact (4^N) (unifiedState E N p).core) -
        potentialWith gstUChargeExact (4^N) (unifiedState E N p).core := by
  have h := gst_coupled_u_flux_step_exact (4^N) (unifiedState E N p).core
  rw [unifiedState_parentJump_exact, unifiedState_childJump_exact] at h
  exact h

/-- **Unified rectangle / Equation-III physical bridge.**
Old Sol's U potential is exactly the horizontal base-four flux of the carry
word of this very same infinite-graph rectangle. -/
theorem unified_u_potential_is_graph_horizontal_flux
    (E N p : Nat) :
    potentialWith gstUChargeExact (4^N) (unifiedState E N p).core =
      Finset.sum (Finset.range N) (fun i =>
        ((4^i : Nat) : Int) *
          horizontalFluxWith gstUChargeExact
            ((unifiedState E N p).core.parentSeed +
              4 * (unifiedState E N p).core.parentOffset) i) := by
  exact gst_u_potential_is_horizontal_base4_flux
    (4^N) N (unifiedState E N p) rfl
    (unifiedState_physicalInvariant E N p)
    (unifiedState_residue_lt E N p)
    (unifiedState_parentCarry_lt_four E N p)
    (unifiedState_childCarry_lt_four E N p)

#check unifiedState_physicalInvariant
#check unifiedState_parentDigit_exact
#check unified_equationIII_graph_exact
#check unified_u_potential_is_graph_horizontal_flux
#print axioms unifiedState_physicalInvariant
#print axioms unified_equationIII_graph_exact
#print axioms unified_u_potential_is_graph_horizontal_flux

end GSTGraphV2UnifiedPowerRectangle
