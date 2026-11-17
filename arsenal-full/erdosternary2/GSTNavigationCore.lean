import CanonicalOriginModulusScratch
import GSTGraphV2HandwrittenExponentialLTE

set_option maxRecDepth 1000000
set_option maxHeartbeats 10000000

/-- The three spaces of the canonical GST carry graph. -/
inductive GSTSpace where
  | gstPlus
  | altMinus
  | null
  deriving DecidableEq, Repr

/-- Carry coordinate at ternary position `p`. -/
def gstCarry (R p : Nat) : Nat := (4 * (R % 3^p)) / 3^p

/-- Ternary digit coordinate at position `p`. -/
def gstDigit (R p : Nat) : Nat := R / 3^p % 3

/-- Exact physical space classifier. -/
def gstSpaceAt (R p : Nat) : GSTSpace :=
  if gstCarry R p = 0 then .null
  else if gstCarry R p = 3 then .gstPlus
  else .altMinus

/-- Exact ternary tail after the forced `s+1` low digits of `4^(3^s*b)`. -/
def gstNavigationConstant (s b : Nat) : Nat :=
  4^(3^s * b) / 3^(s+1)

/-- A canonical Navigation value has a physical digit-two Happy gate. -/
def GSTNavigationWitness (R : Nat) : Prop :=
  ∃ j, gstDigit R j = 2 ∧
    (gstSpaceAt R j = .gstPlus ∨ gstSpaceAt R j = .null)

/-- Cycle-safe concrete perfect-power decomposition for Navigation. -/
theorem gst_navigation_core_decompositionS
    (s b : Nat) (hs : 1 ≤ s) :
    4^(3^s * b) = 1 + 3^(s+1) * gstNavigationConstant s b := by
  have hmod : 4^(3^s * b) % 3^(s+1) = 1 :=
    GSTGraphV2HandwrittenExponentialLTE.pow4_scaled_mod_next s b
  have hsplit := Nat.mod_add_div (4^(3^s * b)) (3^(s+1))
  rw [hmod] at hsplit
  exact hsplit.symm

/-- The concrete Navigation map satisfies the generic canonical-energy API. -/
theorem gst_navigation_core_origin_energyS :
    GSTCanonicalOriginEnergyS gstNavigationConstant := by
  intro s b hs
  exact gst_navigation_core_decompositionS s b hs

/-- Exact removal of one ternary origin factor. -/
theorem gst_navigation_core_mul3S
    (s m : Nat) (hs : 1 ≤ s) :
    gstNavigationConstant s (3*m) =
      3 * gstNavigationConstant (s+1) m := by
  have hrec := gst_canonical_prefix_recurrenceS
    gstNavigationConstant gst_navigation_core_origin_energyS
    s 0 1 m hs
  have hzero := gst_canonical_origin_zeroS
    gstNavigationConstant gst_navigation_core_origin_energyS s hs
  rw [hzero] at hrec
  norm_num at hrec ⊢
  simpa [Nat.mul_assoc] using hrec

/-- The level-s unit Navigation quotient is the exact LTE coefficient. -/
theorem gst_navigation_core_unit_eq_lteCoeffS
    (s : Nat) (hs : 1 ≤ s) :
    gstNavigationConstant s 1 =
      GSTGraphV2HandwrittenExponentialLTE.lteCoeff s := by
  have hQ := gst_navigation_core_decompositionS s 1 hs
  have hLTE :=
    GSTGraphV2HandwrittenExponentialLTE.pow4_three_power_lte_exact s
  norm_num at hQ
  have heq :
      1 + 3^(s+1) * gstNavigationConstant s 1 =
        1 + 3^(s+1) * GSTGraphV2HandwrittenExponentialLTE.lteCoeff s :=
    hQ.symm.trans hLTE
  have hmul := Nat.add_left_cancel heq
  exact Nat.mul_left_cancel (Nat.pow_pos (by decide : 0 < 3)) hmul

/-- Navigation retains the least origin trit at every positive level. -/
theorem gst_navigation_core_mod3_allS
    (s b : Nat) (hs : 1 ≤ s) :
    gstNavigationConstant s b % 3 = b % 3 := by
  induction b with
  | zero =>
      have hzero := gst_canonical_origin_zeroS
        gstNavigationConstant gst_navigation_core_origin_energyS s hs
      rw [hzero]
  | succ b ih =>
      have hadd := gst_canonical_origin_addS
        gstNavigationConstant gst_navigation_core_origin_energyS s b 1 hs
      have hA : 4^(3^s * b) % 3 = 1 := by
        rw [Nat.pow_mod]
        norm_num
      have hunit : gstNavigationConstant s 1 % 3 = 1 := by
        rw [gst_navigation_core_unit_eq_lteCoeffS s hs]
        exact GSTGraphV2HandwrittenExponentialLTE.lteCoeff_mod3_one s
      rw [hadd, Nat.add_mod, Nat.mul_mod, ih, hA, hunit]
      simp [Nat.add_mod]

/-- Build a Navigation witness from a literal digit-two / carry-zero gate. -/
theorem gst_navigation_core_witness_of_digit_carry_zeroS
    (R j : Nat) (hd : gstDigit R j = 2) (hC : gstCarry R j = 0) :
    GSTNavigationWitness R := by
  refine ⟨j, hd, Or.inr ?_⟩
  simp [gstSpaceAt, hC]

/-- Build a Navigation witness from a literal digit-two / carry-three gate. -/
theorem gst_navigation_core_witness_of_digit_carry_threeS
    (R j : Nat) (hd : gstDigit R j = 2) (hC : gstCarry R j = 3) :
    GSTNavigationWitness R := by
  refine ⟨j, hd, Or.inl ?_⟩
  simp [gstSpaceAt, hC]
