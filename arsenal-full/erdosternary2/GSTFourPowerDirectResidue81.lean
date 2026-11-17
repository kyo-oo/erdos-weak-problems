import GSTFourPowerDirectResidue

set_option maxRecDepth 1000000
set_option maxHeartbeats 20000000

namespace GSTFourPowerDirectResidue81

open GSTFourPowerDirectResidue

/-- The exact residue classes modulo `81 = 3^4` where row four is simultaneously
`2` in two consecutive powers of four.  This is a pure arithmetic classifier;
it has no navigation or witness-transport content. -/
def RowFourClass (r : Nat) : Prop :=
  r = 8 ∨ r = 20 ∨ r = 41 ∨ r = 42 ∨ r = 51 ∨ r = 52 ∨ r = 53 ∨
  r = 54 ∨ r = 55 ∨ r = 56 ∨ r = 57 ∨ r = 58 ∨ r = 66 ∨ r = 76

/-- A single residue representative lifts to every exponent in the same class
modulo 81, by the already-kernel-verified period theorem at row four. -/
theorem row_four_overlap_of_mod81_residue
    (K r : Nat) (hr : K % 81 = r)
    (h0 : digit3 (4^r) 4 = 2)
    (h1 : digit3 (4^(r+1)) 4 = 2) :
    digit3 (4^K) 4 = 2 ∧ digit3 (4^(K+1)) 4 = 2 := by
  have hm := Nat.mod_add_div K 81
  rw [hr] at hm
  have hK : K = r + 3^4 * (K / 81) := by
    norm_num at hm ⊢
    omega
  have hK1 : K + 1 = (r+1) + 3^4 * (K / 81) := by omega
  constructor
  · rw [hK]
    calc
      digit3 (4^(r + 3^4 * (K / 81))) 4 = digit3 (4^r) 4 :=
        pow4_digit_period 4 r (K / 81)
      _ = 2 := h0
  · rw [hK1]
    calc
      digit3 (4^((r+1) + 3^4 * (K / 81))) 4 = digit3 (4^(r+1)) 4 :=
        pow4_digit_period 4 (r+1) (K / 81)
      _ = 2 := h1

/-- Exact row-four common-two classifier for the fourteen overlap classes
modulo 81.  Ten of these classes are new beyond the current row-two/mod-nine
and row-three/mod-twenty-seven production coverage. -/
theorem row_four_overlap_of_mod81_classes
    (K : Nat) (hres : RowFourClass (K % 81)) :
    digit3 (4^K) 4 = 2 ∧ digit3 (4^(K+1)) 4 = 2 := by
  unfold RowFourClass at hres
  rcases hres with h | h | h | h | h | h | h | h | h | h | h | h | h | h
  · exact row_four_overlap_of_mod81_residue K 8 h (by norm_num [digit3]) (by norm_num [digit3])
  · exact row_four_overlap_of_mod81_residue K 20 h (by norm_num [digit3]) (by norm_num [digit3])
  · exact row_four_overlap_of_mod81_residue K 41 h (by norm_num [digit3]) (by norm_num [digit3])
  · exact row_four_overlap_of_mod81_residue K 42 h (by norm_num [digit3]) (by norm_num [digit3])
  · exact row_four_overlap_of_mod81_residue K 51 h (by norm_num [digit3]) (by norm_num [digit3])
  · exact row_four_overlap_of_mod81_residue K 52 h (by norm_num [digit3]) (by norm_num [digit3])
  · exact row_four_overlap_of_mod81_residue K 53 h (by norm_num [digit3]) (by norm_num [digit3])
  · exact row_four_overlap_of_mod81_residue K 54 h (by norm_num [digit3]) (by norm_num [digit3])
  · exact row_four_overlap_of_mod81_residue K 55 h (by norm_num [digit3]) (by norm_num [digit3])
  · exact row_four_overlap_of_mod81_residue K 56 h (by norm_num [digit3]) (by norm_num [digit3])
  · exact row_four_overlap_of_mod81_residue K 57 h (by norm_num [digit3]) (by norm_num [digit3])
  · exact row_four_overlap_of_mod81_residue K 58 h (by norm_num [digit3]) (by norm_num [digit3])
  · exact row_four_overlap_of_mod81_residue K 66 h (by norm_num [digit3]) (by norm_num [digit3])
  · exact row_four_overlap_of_mod81_residue K 76 h (by norm_num [digit3]) (by norm_num [digit3])

/-- A global no-common-two exponent avoids every row-four overlap class. -/
theorem no_common_two_forbids_mod81_classes
    (K : Nat)
    (hNo : ¬ ∃ q : Nat, 1 ≤ q ∧
      digit3 (4^K) q = 2 ∧ digit3 (4^(K+1)) q = 2) :
    ¬ RowFourClass (K % 81) := by
  intro hres
  have hr := row_four_overlap_of_mod81_classes K hres
  apply hNo
  exact ⟨4, by norm_num, hr.1, hr.2⟩

#check RowFourClass
#check row_four_overlap_of_mod81_residue
#check row_four_overlap_of_mod81_classes
#check no_common_two_forbids_mod81_classes
#print axioms row_four_overlap_of_mod81_residue
#print axioms row_four_overlap_of_mod81_classes
#print axioms no_common_two_forbids_mod81_classes

end GSTFourPowerDirectResidue81
