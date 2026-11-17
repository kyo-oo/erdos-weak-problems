import GSTInfiniteGateTransport

set_option maxRecDepth 1000000
set_option maxHeartbeats 20000000

/-!
# Explicit countermodel inside the exact all-Nat GST V2 controller

A=64=4^3, initial=(seed0,offset0,residue0,carry0,tail46).
The child has a Happy Gate at position 2, while its parent word is
64*46=2944=(11001001)_3 and has no ternary 2 anywhere. Therefore an
infinite bad parent, complete coupled invariants, and a latent child
Happy packet are genuinely consistent unless the canonical perfect-
power source condition is imposed.

This is a counterexample to generic infinite-controller CHOKEHOLD,
not to Erdos conjecture.
-/

namespace GSTCoupledControllerCountermodel

open GSTV2

def exampleState : CoupledState :=
  { parentSeed := 0
    parentOffset := 0
    childResidue := 0
    childCarry := 0
    childTail := 46 }

theorem example_coupled_invariant :
    CoupledInvariant 64 exampleState := by
  decide

theorem example_parent_word :
    exampleState.parentWord 64 = 2944 := by decide

theorem parent_2944_has_no_happy_cell (j : Nat) :
    ¬ Happy (affineCarry 0 2944 j) (digit 2944 j) := by
  have hd : digit 2944 j ≠ 2 := by
    by_cases hj : j < 8
    · interval_cases j <;> norm_num [digit]
    · have h8 : 2944 < 3^8 := by decide
      have hpow : 3^8 ≤ 3^j :=
        Nat.pow_le_pow_of_le (by decide : 1 < 3) (by omega)
      have hz : 2944 / 3^j = 0 :=
        Nat.div_eq_of_lt (lt_of_lt_of_le h8 hpow)
      simp [digit, hz]
  exact fun h => hd h.1

theorem example_parent_bad : SeededBadTrace
    exampleState.parentSeed (exampleState.parentWord 64) := by
  change SeededBadTrace 0 2944
  intro j h
  exact (parent_2944_has_no_happy_cell j) h

theorem example_infinite_controller :
    InfiniteBadCoupledControl 64 exampleState := by
  apply infinite_bad_coupled_control 64 exampleState
  · decide
  · exact example_coupled_invariant
  · decide
  · exact example_parent_bad

theorem example_child_gate :
    Happy (coupledOrbit 64 exampleState 2).childCarry
      ((coupledOrbit 64 exampleState 2).childTail % 3) := by
  have hc := coupledOrbit_childCarry_exact 64 exampleState
    (by decide : exampleState.childCarry = 0) 2
  have hd := coupledOrbit_childDigit_exact 64 exampleState 2
  rw [hc, hd]
  norm_num [Happy, naturalCarry, digit, exampleState]

/-- Strongest exact counterexample: the entire all-depth coupled BAD
controller coexists with a genuine latent child Happy packet. -/
theorem all_depth_controller_and_child_gate_coexist :
    InfiniteBadCoupledControl 64 exampleState ∧
      LatentGateTransfer 64 exampleState 2 := by
  constructor
  · exact example_infinite_controller
  · exact coupled_happy_transports_information 64 exampleState 2
      example_infinite_controller example_child_gate

#print axioms parent_2944_has_no_happy_cell
#print axioms example_infinite_controller
#print axioms all_depth_controller_and_child_gate_coexist

end GSTCoupledControllerCountermodel
