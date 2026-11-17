import GSTFourPowerDirectResidue

set_option maxRecDepth 1000000
set_option maxHeartbeats 20000000

namespace GSTFourPowerDirectResidue27

open GSTFourPowerDirectResidue

/-- Row three depends only on the exponent modulo `27 = 3^3`.  In the four
listed residue classes, both consecutive powers of four have ternary digit two
at row three.  This is a finite direct-arithmetic extension of the row-two
mod-nine classifier and uses no navigation or witness transport. -/
theorem row_three_overlap_of_mod27_classes
    (K : Nat)
    (hres : K % 27 = 14 ∨ K % 27 = 18 ∨ K % 27 = 19 ∨ K % 27 = 25) :
    digit3 (4^K) 3 = 2 ∧ digit3 (4^(K+1)) 3 = 2 := by
  rcases hres with h14 | h18 | h19 | h25
  · have hm := Nat.mod_add_div K 27
    rw [h14] at hm
    have hK : K = 14 + 3^3 * (K / 27) := by
      norm_num at hm ⊢
      omega
    have hK1 : K + 1 = 15 + 3^3 * (K / 27) := by omega
    constructor
    · rw [hK]
      calc
        digit3 (4^(14 + 3^3 * (K / 27))) 3 = digit3 (4^14) 3 :=
          pow4_digit_period 3 14 (K / 27)
        _ = 2 := by norm_num [digit3]
    · rw [hK1]
      calc
        digit3 (4^(15 + 3^3 * (K / 27))) 3 = digit3 (4^15) 3 :=
          pow4_digit_period 3 15 (K / 27)
        _ = 2 := by norm_num [digit3]
  · have hm := Nat.mod_add_div K 27
    rw [h18] at hm
    have hK : K = 18 + 3^3 * (K / 27) := by
      norm_num at hm ⊢
      omega
    have hK1 : K + 1 = 19 + 3^3 * (K / 27) := by omega
    constructor
    · rw [hK]
      calc
        digit3 (4^(18 + 3^3 * (K / 27))) 3 = digit3 (4^18) 3 :=
          pow4_digit_period 3 18 (K / 27)
        _ = 2 := by norm_num [digit3]
    · rw [hK1]
      calc
        digit3 (4^(19 + 3^3 * (K / 27))) 3 = digit3 (4^19) 3 :=
          pow4_digit_period 3 19 (K / 27)
        _ = 2 := by norm_num [digit3]
  · have hm := Nat.mod_add_div K 27
    rw [h19] at hm
    have hK : K = 19 + 3^3 * (K / 27) := by
      norm_num at hm ⊢
      omega
    have hK1 : K + 1 = 20 + 3^3 * (K / 27) := by omega
    constructor
    · rw [hK]
      calc
        digit3 (4^(19 + 3^3 * (K / 27))) 3 = digit3 (4^19) 3 :=
          pow4_digit_period 3 19 (K / 27)
        _ = 2 := by norm_num [digit3]
    · rw [hK1]
      calc
        digit3 (4^(20 + 3^3 * (K / 27))) 3 = digit3 (4^20) 3 :=
          pow4_digit_period 3 20 (K / 27)
        _ = 2 := by norm_num [digit3]
  · have hm := Nat.mod_add_div K 27
    rw [h25] at hm
    have hK : K = 25 + 3^3 * (K / 27) := by
      norm_num at hm ⊢
      omega
    have hK1 : K + 1 = 26 + 3^3 * (K / 27) := by omega
    constructor
    · rw [hK]
      calc
        digit3 (4^(25 + 3^3 * (K / 27))) 3 = digit3 (4^25) 3 :=
          pow4_digit_period 3 25 (K / 27)
        _ = 2 := by norm_num [digit3]
    · rw [hK1]
      calc
        digit3 (4^(26 + 3^3 * (K / 27))) 3 = digit3 (4^26) 3 :=
          pow4_digit_period 3 26 (K / 27)
        _ = 2 := by norm_num [digit3]

/-- A trace with no common digit-two row cannot occupy any of the four exact
row-three overlap classes modulo 27. -/
theorem no_common_two_forbids_mod27_classes
    (K : Nat)
    (hNo : ¬ ∃ q : Nat, 1 ≤ q ∧
      digit3 (4^K) q = 2 ∧ digit3 (4^(K+1)) q = 2) :
    K % 27 ≠ 14 ∧ K % 27 ≠ 18 ∧ K % 27 ≠ 19 ∧ K % 27 ≠ 25 := by
  constructor
  · intro h
    apply hNo
    exact ⟨3, by norm_num, row_three_overlap_of_mod27_classes K (Or.inl h) |>.1,
      row_three_overlap_of_mod27_classes K (Or.inl h) |>.2⟩
  constructor
  · intro h
    apply hNo
    have hr := row_three_overlap_of_mod27_classes K (Or.inr (Or.inl h))
    exact ⟨3, by norm_num, hr.1, hr.2⟩
  constructor
  · intro h
    apply hNo
    have hr := row_three_overlap_of_mod27_classes K (Or.inr (Or.inr (Or.inl h)))
    exact ⟨3, by norm_num, hr.1, hr.2⟩
  · intro h
    apply hNo
    have hr := row_three_overlap_of_mod27_classes K (Or.inr (Or.inr (Or.inr h)))
    exact ⟨3, by norm_num, hr.1, hr.2⟩

#check row_three_overlap_of_mod27_classes
#check no_common_two_forbids_mod27_classes
#print axioms row_three_overlap_of_mod27_classes
#print axioms no_common_two_forbids_mod27_classes

end GSTFourPowerDirectResidue27
