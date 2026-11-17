import GSTFinalResidualEarliestGateBridge
import GSTGraphV2ProductionLaws

set_option maxRecDepth 1000000
set_option maxHeartbeats 10000000

open GSTCanonicalSevenAxisBridge
open GST2DMixedEmergence
open GSTU2DEventTransport
open GSTGraphV2InfiniteControl
open GSTInfiniteV2

namespace GSTFinalResidualBinaryBoundaryBridge

/-- Two binary columns are exactly one x4 Graph-V2 horizontal step. -/
theorem binary_column_even_is_graph_digit
    (E t p : Nat) :
    GSTPhysicalKernel.binaryColumnDigit E p (2*t) =
      (graph E t p).seven.digit := by
  simp [GSTPhysicalKernel.binaryColumnDigit,
    graph, cell, GSTCanonicalSevenAxisBridge.vertex,
    GSTCanonicalSevenAxisBridge.digit3,
    show 2^(2*t) = 4^t by
      calc
        2^(2*t) = (2^2)^t := by rw [Nat.pow_mul]
        _ = 4^t := by norm_num]

/-- A physical Graph-V2 Happy cell is exactly a binary BIG2 chord across its
corresponding pair of x2 columns.  This is the production replacement for the
old handwritten right-boundary conversion. -/
theorem graph_happy_iff_binary_big2_chord
    (E t p : Nat) :
    HappyCell (graph E t p).seven.carry (graph E t p).seven.digit ↔
      GSTPhysicalKernel.binaryColumnDigit E p (2*t) = 2 ∧
      GSTPhysicalKernel.binaryColumnDigit E p (2*(t+1)) = 2 := by
  have hcell := graph_cell_exact E t p
  have hleft := binary_column_even_is_graph_digit E t p
  have hright := binary_column_even_is_graph_digit E (t+1) p
  constructor
  · intro hHappy
    have hout := (happyCell_positive_and_preserves_big2 _ _ hHappy).2
    constructor
    · rw [hleft]
      exact hHappy.1
    · rw [hright, ← hcell.1]
      exact hout
  · rintro ⟨hd0, hd1⟩
    have hDigit : (graph E t p).seven.digit = 2 := by
      rw [← hleft]
      exact hd0
    have hOut : outDigit (graph E t p).seven.carry
        (graph E t p).seven.digit = 2 := by
      rw [hcell.1, ← hright]
      exact hd1
    have hOut2 : outDigit (graph E t p).seven.carry 2 = 2 := by
      simpa [hDigit] using hOut
    have hevent :
        GSTCanonicalSevenAxisBridge.event
          (graph E t p).seven.carry
          (graph E t p).seven.digit = 8 := by
      rw [GSTCanonicalSevenAxisBridge.event, hDigit, hOut2]
    exact (GSTCanonicalSevenAxisBridge.happy_iff_event_eight _ _
      (graph_carry_lt_four E t p)
      (graph_digit_lt_three E t p)).2 hevent

/-- Level-one parent width is six binary columns; therefore right-boundary
badness is exactly exclusion of the `6 -> 8` BIG2 chord. -/
theorem level_one_right_bad_iff_no_binary_6_8
    (E p : Nat) :
    (¬ HappyCell (graph E 3 p).seven.carry (graph E 3 p).seven.digit) ↔
      ¬ (GSTPhysicalKernel.binaryColumnDigit E p 6 = 2 ∧
         GSTPhysicalKernel.binaryColumnDigit E p 8 = 2) := by
  simpa using not_congr (graph_happy_iff_binary_big2_chord E 3 p)

/-- Before the low forced ternary prefix can contribute a binary carry, binary
columns of the full energy and of the exposed tail have exactly the same
information digit. -/
theorem prefixed_binary_column_digit_exact
    (T b q r : Nat)
    (hsmall : 2^r < 3^b) :
    GSTPhysicalKernel.binaryColumnDigit (1 + 3^b*T) (b+q) r =
      GSTPhysicalKernel.binaryColumnDigit T q r := by
  unfold GSTPhysicalKernel.binaryColumnDigit
  rw [Nat.pow_add]
  have hshape :
      2^r * (1 + 3^b*T) = 2^r + 3^b * (2^r*T) := by ring
  rw [hshape, ← Nat.div_div_eq_div_mul]
  have hbpos : 0 < 3^b := Nat.pow_pos (by decide)
  rw [Nat.add_mul_div_left _ _ hbpos, Nat.div_eq_of_lt hsmall,
    Nat.zero_add]

/-- The only first-BIG1 locations produced by a seed-zero Happy gate (1 or 3)
therefore survive unchanged when the exposed tail is put back under any forced
prefix of ternary depth at least three. -/
theorem prefixed_first_big1_transfer_le_three
    (T b q N : Nat)
    (hb : 3 ≤ b) (hN : N ≤ 3)
    (hfirst : GSTFirstBig1AtS
      (fun r => GSTPhysicalKernel.binaryColumnDigit T q r) N) :
    GSTFirstBig1AtS
      (fun r => GSTPhysicalKernel.binaryColumnDigit (1 + 3^b*T) (b+q) r) N := by
  have h27 : 27 ≤ 3^b := by
    rw [show (27 : Nat) = 3^3 by decide]
    exact Nat.pow_le_pow_of_le (by decide : 1 < 3) hb
  have hsmall : ∀ r, r ≤ 3 → 2^r < 3^b := by
    intro r hr
    interval_cases r <;> norm_num at * <;> omega
  constructor
  · change GSTPhysicalKernel.binaryColumnDigit (1 + 3^b*T) (b+q) N = 1
    rw [prefixed_binary_column_digit_exact T b q N (hsmall N hN)]
    exact hfirst.1
  · intro j hj
    change GSTPhysicalKernel.binaryColumnDigit (1 + 3^b*T) (b+q) j ≠ 1
    rw [prefixed_binary_column_digit_exact T b q j (hsmall j (by omega))]
    exact hfirst.2 j hj

#check binary_column_even_is_graph_digit
#check graph_happy_iff_binary_big2_chord
#check level_one_right_bad_iff_no_binary_6_8
#check prefixed_binary_column_digit_exact
#check prefixed_first_big1_transfer_le_three
#print axioms graph_happy_iff_binary_big2_chord
#print axioms prefixed_first_big1_transfer_le_three

end GSTFinalResidualBinaryBoundaryBridge
