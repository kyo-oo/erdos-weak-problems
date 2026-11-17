import GSTU2DPureDivergence83

set_option maxRecDepth 1000000
set_option maxHeartbeats 20000000

namespace GSTU2DCanonicalShiftedTerminalProbe

open GSTCanonicalSevenAxisBridge
open GSTU2DEventTransport
open GSTGraphV2InfiniteControl
open GSTU2DPureDivergence83

/-- Exact 8x3 density rectangle on a vertical window beginning at `start`.
This is the production-cut form needed by the canonical collision argument. -/
theorem graph_density83_rectangle_shifted_exact
    (E start N K : Nat) :
    Finset.sum (Finset.range K) (fun p =>
      (((3^p : Nat) : Int)) *
        reverseDensity83
          (fun t => (graph E t (start+p)).seven.carry)
          (fun t => (graph E t (start+p)).seven.digit) N) =
      Finset.sum (Finset.range K) (fun p =>
        (((3^p : Nat) : Int)) *
          (digitPotential83 (graph E N (start+p)).seven.digit -
            (((8^N : Nat) : Int)) *
              digitPotential83 (graph E 0 (start+p)).seven.digit)) +
      reverseCarry83 (fun t => (graph E t start).seven.carry) N -
        (((3^K : Nat) : Int)) *
          reverseCarry83
            (fun t => (graph E t (start+K)).seven.carry) N := by
  apply density83_rectangle_exact
  intro t p ht hp
  exact ⟨graph_carry_lt_four E t (start+p),
    graph_digit_lt_three E t (start+p),
    (graph_cell_exact E t (start+p)).1,
    by simpa [Nat.add_assoc] using (graph_cell_exact E t (start+p)).2⟩

/-- The upper carry boundary of the 8x3 rectangle is exactly zero when the
physical row is carry-neutral.  Unlike the earlier U-potential normalization,
there is no residual vacuum constant because `carryPotential83 0 = 0`. -/
theorem reverseCarry83_zero_of_neutral
    (C : Nat → Nat) : ∀ N : Nat,
    (∀ t, t < N → C t = 0) → reverseCarry83 C N = 0 := by
  intro N h
  induction N with
  | zero => simp [reverseCarry83]
  | succ N ih =>
      rw [reverseCarry83]
      have hprev : ∀ t, t < N → C t = 0 := by
        intro t ht
        exact h t (by omega)
      rw [ih hprev]
      have hlast := h N (by omega)
      rw [hlast]
      norm_num [carryPotential83]

/-- Once the shifted top row is physically neutral across the finite width,
the exact rectangle loses its live upper carry boundary. -/
theorem graph_density83_rectangle_shifted_terminal_exact
    (E start N K : Nat)
    (hTop : ∀ t, t < N →
      (graph E t (start+K)).seven.carry = 0) :
    Finset.sum (Finset.range K) (fun p =>
      (((3^p : Nat) : Int)) *
        reverseDensity83
          (fun t => (graph E t (start+p)).seven.carry)
          (fun t => (graph E t (start+p)).seven.digit) N) =
      Finset.sum (Finset.range K) (fun p =>
        (((3^p : Nat) : Int)) *
          (digitPotential83 (graph E N (start+p)).seven.digit -
            (((8^N : Nat) : Int)) *
              digitPotential83 (graph E 0 (start+p)).seven.digit)) +
      reverseCarry83 (fun t => (graph E t start).seven.carry) N := by
  rw [graph_density83_rectangle_shifted_exact]
  have hzero :
      reverseCarry83
        (fun t => (graph E t (start+K)).seven.carry) N = 0 := by
    exact reverseCarry83_zero_of_neutral _ N hTop
  rw [hzero]
  ring

#check graph_density83_rectangle_shifted_exact
#check reverseCarry83_zero_of_neutral
#check graph_density83_rectangle_shifted_terminal_exact
#print axioms graph_density83_rectangle_shifted_exact
#print axioms reverseCarry83_zero_of_neutral
#print axioms graph_density83_rectangle_shifted_terminal_exact

end GSTU2DCanonicalShiftedTerminalProbe
