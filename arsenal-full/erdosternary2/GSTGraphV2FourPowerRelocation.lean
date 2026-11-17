import GSTGraphV2NonlocalCascade
import GSTGraphV2CanonicalEscape
import GSTGraphV2CanonicalInfiniteCycle
import GSTGraphV2CanonicalTerminalExtinctionProbe
import GSTFinalPurePowerResidueTransplant

set_option maxRecDepth 1000000
set_option maxHeartbeats 20000000

namespace GSTGraphV2FourPowerRelocation

open GST2DMixedEmergence
open GSTU2DEventTransport
open GSTGraphV2InfiniteControl
open GSTGraphV2NonlocalCascade

/-- Exact universal induction edge to be proved without weakening.

A physical Happy cell on the `4^K` unit sheet must force the existence of
some physical Happy cell on the `4^(K+1)` sheet.  The relocated row is not
assumed to be local to the input row. -/
def FourPowerHappyPropagation : Prop :=
  ∀ K p : Nat, 8 ≤ K → 1 ≤ p →
    HappyCell (graph 1 K p).seven.carry (graph 1 K p).seven.digit →
    ∃ q : Nat, 1 ≤ q ∧
      HappyCell (graph 1 (K+1) q).seven.carry
        (graph 1 (K+1) q).seven.digit

/-- A physical Graph-V2 cell is Happy exactly when information digit two is
present at the cell and survives the horizontal x4 step at the same row. -/
theorem graph_happy_iff_consecutive_digit_two
    (E t p : Nat) :
    HappyCell
        (graph E t p).seven.carry
        (graph E t p).seven.digit ↔
      (graph E t p).seven.digit = 2 ∧
        (graph E (t+1) p).seven.digit = 2 := by
  constructor
  · intro hHappy
    rcases hHappy with ⟨hd, hcarry⟩
    refine ⟨hd, ?_⟩
    have hHappy' : HappyCell
        (graph E t p).seven.carry
        (graph E t p).seven.digit := ⟨hd, hcarry⟩
    have hout :=
      (happyCell_positive_and_preserves_big2
        (graph E t p).seven.carry
        (graph E t p).seven.digit hHappy').2
    rw [← (graph_cell_exact E t p).1]
    exact hout
  · rintro ⟨hd, hnext⟩
    refine ⟨hd, ?_⟩
    have hout :
        outDigit
          (graph E t p).seven.carry
          (graph E t p).seven.digit = 2 := by
      rw [(graph_cell_exact E t p).1]
      exact hnext
    have hcarryLt := graph_carry_lt_four E t p
    have hcases :
        (graph E t p).seven.carry = 0 ∨
        (graph E t p).seven.carry = 1 ∨
        (graph E t p).seven.carry = 2 ∨
        (graph E t p).seven.carry = 3 := by
      omega
    rcases hcases with h0 | h1 | h2 | h3
    · exact Or.inl h0
    · rw [h1, hd] at hout
      norm_num [outDigit] at hout
    · rw [h2, hd] at hout
      norm_num [outDigit] at hout
    · exact Or.inr h3

/-- Arithmetic form of the same physical law on a pure four-power sheet.
The carry condition has disappeared completely: a Happy witness is exactly a
shared ternary digit-two position of two consecutive powers of four. -/
theorem four_power_happy_iff_consecutive_digit_two
    (K p : Nat) :
    GSTCanonicalTailStateIso.HappyCell
        (GSTCanonicalTailStateIso.carry4 (4^K) p)
        (GSTCanonicalTailStateIso.digit3 (4^K) p) ↔
      GSTCanonicalTailStateIso.digit3 (4^K) p = 2 ∧
        GSTCanonicalTailStateIso.digit3 (4^(K+1)) p = 2 := by
  simpa [GSTGraphV2InfiniteControl.graph,
    GSTGraphV2InfiniteControl.cell,
    GSTCanonicalSevenAxisBridge.vertex,
    GSTCanonicalSevenAxisBridge.carry4,
    GSTCanonicalSevenAxisBridge.digit3,
    GSTU2DEventTransport.HappyCell,
    GSTCanonicalTailStateIso.HappyCell,
    GSTCanonicalTailStateIso.carry4,
    GSTCanonicalTailStateIso.digit3] using
      (graph_happy_iff_consecutive_digit_two 1 K p)

/-- The original universal four-power target, isolated from the monolith. -/
def FourPowerCanonicalHappyTarget : Prop :=
  ∀ K : Nat, 5 ≤ K → K ≠ 7 →
    ∃ p : Nat, 1 ≤ p ∧
      GSTCanonicalTailStateIso.HappyCell
        (GSTCanonicalTailStateIso.carry4 (4^K) p)
        (GSTCanonicalTailStateIso.digit3 (4^K) p)

/-- Pure arithmetic form of the exact same target. -/
def FourPowerDigitOverlap : Prop :=
  ∀ K : Nat, 5 ≤ K → K ≠ 7 →
    ∃ p : Nat, 1 ≤ p ∧
      GSTCanonicalTailStateIso.digit3 (4^K) p = 2 ∧
      GSTCanonicalTailStateIso.digit3 (4^(K+1)) p = 2

/-- No weakening is hidden in the digit-overlap reformulation. -/
theorem four_power_canonical_target_iff_digit_overlap :
    FourPowerCanonicalHappyTarget ↔ FourPowerDigitOverlap := by
  constructor
  · intro h K hK5 hK7
    rcases h K hK5 hK7 with ⟨p, hp, hHappy⟩
    exact ⟨p, hp, (four_power_happy_iff_consecutive_digit_two K p).mp hHappy⟩
  · intro h K hK5 hK7
    rcases h K hK5 hK7 with ⟨p, hp, hOverlap⟩
    exact ⟨p, hp, (four_power_happy_iff_consecutive_digit_two K p).mpr hOverlap⟩

/-- Exact base witness at K=5. -/
theorem four_power_digit_overlap_base_5 :
    ∃ p : Nat, 1 ≤ p ∧
      GSTCanonicalTailStateIso.digit3 (4^5) p = 2 ∧
      GSTCanonicalTailStateIso.digit3 (4^(5+1)) p = 2 := by
  refine ⟨2, by norm_num, ?_, ?_⟩
  · norm_num [GSTCanonicalTailStateIso.digit3]
  · norm_num [GSTCanonicalTailStateIso.digit3]

/-- Exact base witness at K=6. -/
theorem four_power_digit_overlap_base_6 :
    ∃ p : Nat, 1 ≤ p ∧
      GSTCanonicalTailStateIso.digit3 (4^6) p = 2 ∧
      GSTCanonicalTailStateIso.digit3 (4^(6+1)) p = 2 := by
  refine ⟨2, by norm_num, ?_, ?_⟩
  · norm_num [GSTCanonicalTailStateIso.digit3]
  · norm_num [GSTCanonicalTailStateIso.digit3]

/-- Exact induction base witness at K=8. -/
theorem four_power_digit_overlap_base_8 :
    ∃ p : Nat, 1 ≤ p ∧
      GSTCanonicalTailStateIso.digit3 (4^8) p = 2 ∧
      GSTCanonicalTailStateIso.digit3 (4^(8+1)) p = 2 := by
  refine ⟨4, by norm_num, ?_, ?_⟩
  · norm_num [GSTCanonicalTailStateIso.digit3]
  · norm_num [GSTCanonicalTailStateIso.digit3]

/-- LTE-specialized exponent-trit transport with no free coefficient
hypothesis.  This is the exact arithmetic bridge used for the power-specific
part of the latent-future analysis. -/
theorem four_power_exponent_trit_lift
    (p m a : Nat) (ha : a < 3) :
    GSTCanonicalSevenAxisBridge.digit3 (4^(m + a*3^p)) (p+1) =
      (GSTCanonicalSevenAxisBridge.digit3 (4^m) (p+1) + a) % 3 := by
  exact GSTFinalPurePowerResidueTransplant.pow4_exponent_trit_lift_digit
    p m (GSTGraphV2HandwrittenExponentialLTE.lteCoeff p) a ha
    (GSTGraphV2HandwrittenExponentialLTE.pow4_three_power_lte_exact p)
    (GSTGraphV2HandwrittenExponentialLTE.lteCoeff_mod3_one p)

/-- A deliberately loose but fully symbolic support cutoff.  It depends only
on `K`; no computational cutoff is baked into the universal argument. -/
def fourPowerSupportCutoff (K : Nat) : Nat := 4^(K+2) + 1

private theorem index_le_three_pow_local (r : Nat) :
    r ≤ 3^r := by
  induction r with
  | zero => simp
  | succ r ih =>
      rw [Nat.pow_succ]
      have hp : 0 < 3^r := by positivity
      omega

/-- The cutoff is high enough to dominate the entire `4^(K+1)` physical cell,
including the extra factor four used by the carry observable. -/
theorem four_power_support_cutoff_pow_lt
    (K : Nat) :
    4^((K+1)+1) < 3^(fourPowerSupportCutoff K) := by
  have hlt : 4^((K+1)+1) < fourPowerSupportCutoff K := by
    simp [fourPowerSupportCutoff, show (K+1)+1 = K+2 by omega]
  have hle : fourPowerSupportCutoff K ≤ 3^(fourPowerSupportCutoff K) :=
    index_le_three_pow_local (fourPowerSupportCutoff K)
  omega

/-- Exact pure-power digit extinction at the symbolic cutoff. -/
theorem four_power_digit_zero_at_support_cutoff
    (K : Nat) :
    GSTCanonicalTailStateIso.digit3
      (4^(K+1)) (fourPowerSupportCutoff K) = 0 := by
  have hpow := four_power_support_cutoff_pow_lt K
  have hmono : 4^(K+1) ≤ 4^((K+1)+1) := by
    rw [Nat.pow_succ]
    omega
  have ht : 4^(K+1) < 3^(fourPowerSupportCutoff K) :=
    lt_of_le_of_lt hmono hpow
  simp [GSTCanonicalTailStateIso.digit3, Nat.div_eq_of_lt ht]

/-- Exact physical Graph-V2 neutralization at the same symbolic cutoff. -/
theorem four_power_graph_neutral_at_support_cutoff
    (K : Nat) :
    (graph 1 (K+1) (fourPowerSupportCutoff K)).seven.carry = 0 ∧
      (graph 1 (K+1) (fourPowerSupportCutoff K)).seven.digit = 0 := by
  exact
    GSTGraphV2CanonicalTerminalExtinctionProbe.unit_graph_cell_neutral_of_pow_lt
      (K+1) (fourPowerSupportCutoff K)
      (four_power_support_cutoff_pow_lt K)

/-- Exact vertical future packet beginning one row above a latent x4 cascade.
Nothing is projected away: carry and digit stay on the physical Graph-V2
sheet, carries remain physical, digits remain ternary, and the vertical
recurrence is the literal cell law at every future row. -/
theorem latent_vertical_future_packet
    (K p : Nat)
    (hNext : (graph 1 (K+1) (p+1)).seven.carry = 3) :
    let C : Nat → Nat := fun r =>
      (graph 1 (K+1) (p+1+r)).seven.carry
    let d : Nat → Nat := fun r =>
      (graph 1 (K+1) (p+1+r)).seven.digit
    C 0 = 3 ∧
      (∀ r, C r < 4) ∧
      (∀ r, d r < 3) ∧
      (∀ r,
        GST2DMixedEmergence.nextCarry (C r) (d r) = C (r+1)) := by
  dsimp
  refine ⟨?_, ?_, ?_, ?_⟩
  · simpa using hNext
  · intro r
    exact graph_carry_lt_four 1 (K+1) (p+1+r)
  · intro r
    exact graph_digit_lt_three 1 (K+1) (p+1+r)
  · intro r
    simpa [Nat.add_assoc] using
      (graph_cell_exact 1 (K+1) (p+1+r)).2

/-- If no relocated Happy witness exists anywhere above row zero, then every
row in the vertical future of a latent packet is physically bad.  This is an
internal contradiction-language adapter only; it does not assume the desired
propagation theorem as a parameter. -/
theorem future_bad_of_no_relocated_happy
    (K p : Nat)
    (hNoRelocated : ¬ ∃ q : Nat, 1 ≤ q ∧
      HappyCell (graph 1 (K+1) q).seven.carry
        (graph 1 (K+1) q).seven.digit) :
    ∀ r : Nat,
      ¬ HappyCell
        (graph 1 (K+1) (p+1+r)).seven.carry
        (graph 1 (K+1) (p+1+r)).seven.digit := by
  intro r hHappy
  apply hNoRelocated
  exact ⟨p+1+r, by omega, hHappy⟩

#check FourPowerHappyPropagation
#check FourPowerCanonicalHappyTarget
#check FourPowerDigitOverlap
#check graph_happy_iff_consecutive_digit_two
#check four_power_happy_iff_consecutive_digit_two
#check four_power_canonical_target_iff_digit_overlap
#check four_power_digit_overlap_base_5
#check four_power_digit_overlap_base_6
#check four_power_digit_overlap_base_8
#check four_power_exponent_trit_lift
#check fourPowerSupportCutoff
#check four_power_support_cutoff_pow_lt
#check four_power_digit_zero_at_support_cutoff
#check four_power_graph_neutral_at_support_cutoff
#check latent_vertical_future_packet
#check future_bad_of_no_relocated_happy
#print axioms graph_happy_iff_consecutive_digit_two
#print axioms four_power_happy_iff_consecutive_digit_two
#print axioms four_power_canonical_target_iff_digit_overlap
#print axioms four_power_digit_overlap_base_5
#print axioms four_power_digit_overlap_base_6
#print axioms four_power_digit_overlap_base_8
#print axioms four_power_exponent_trit_lift
#print axioms four_power_support_cutoff_pow_lt
#print axioms four_power_digit_zero_at_support_cutoff
#print axioms four_power_graph_neutral_at_support_cutoff
#print axioms latent_vertical_future_packet
#print axioms future_bad_of_no_relocated_happy

end GSTGraphV2FourPowerRelocation
