import Mathlib
import GST2DMixedEmergence

/-!
# GST 2D MIXED EMERGENCE — universal micro/macro upgrade

The original physical layer proves several identities by enumerating the
twelve cells `C < 4, d < 3`.  This upgrade extracts the stronger laws
which do not actually require those bounds.

The microscopic x2 composition and its seven-kernel telescope are native
identities on all natural carry/digit inputs.
-/

set_option maxHeartbeats 10000000
set_option maxRecDepth 1000000

namespace GST2DMixedEmergenceUpgrade

open GST2DMixedEmergence

/-- **UNIVERSAL MICRO→MACRO OUTPUT LAW.**  The two microscopic x2 layers
reproduce the x4/base-3 output for every natural carry and digit, not only
for the twelve physical cells. -/
theorem finalMicroDigit_eq_outDigit_universal (C d : Nat) :
    finalMicroDigit C d = outDigit C d := by
  unfold finalMicroDigit midDigit microOutput highBit lowBit outDigit
  omega

/-- **UNIVERSAL CELL BALANCE.**  Every x4/base-3 transition has exact
carry/output conservation, without physical bounds. -/
theorem cell_transition_exact_universal (C d : Nat) :
    3 * nextCarry C d + outDigit C d = C + 4 * d := by
  simpa [nextCarry, outDigit, Nat.mul_comm] using Nat.div_add_mod (C + 4 * d) 3

/-- **UNIVERSAL MICROSCOPIC SEVEN-KERNEL TELESCOPE.**  The hidden midpoint
cancels symbolically on every natural input.  The old bounded theorem is
therefore a physical specialization of an unrestricted GST identity. -/
theorem sevenKernel_micro_telescope_universal (C d : Nat) :
    sevenKernel C d =
      14 * (twoI (outDigit C d) - twoI d) + 7 * surviveI C d := by
  change
    (14 * (twoI (midDigit C d) - twoI d) +
        7 * (twoI d * twoI (midDigit C d))) +
      (14 * (twoI (finalMicroDigit C d) - twoI (midDigit C d)) +
        7 * (twoI (midDigit C d) * twoI (finalMicroDigit C d))) =
      14 * (twoI (outDigit C d) - twoI d) +
        7 * (twoI d * twoI (midDigit C d) +
          twoI (midDigit C d) * twoI (finalMicroDigit C d))
  rw [finalMicroDigit_eq_outDigit_universal]
  ring

/-- The old bounded output theorem is recovered immediately from the
universal identity; its bounds carry no mathematical load. -/
theorem finalMicroDigit_physical_absorbed
    (C d : Nat) (hC : C < 4) (hd : d < 3) :
    finalMicroDigit C d = outDigit C d :=
  finalMicroDigit_eq_outDigit_universal C d

/-- The old bounded telescope is likewise absorbed by the universal law. -/
theorem sevenKernel_physical_absorbed
    (C d : Nat) (hC : C < 4) (hd : d < 3) :
    sevenKernel C d =
      14 * (twoI (outDigit C d) - twoI d) + 7 * surviveI C d :=
  sevenKernel_micro_telescope_universal C d

/-- One receipt for the strengthened microscopic foundation. -/
theorem universal_micro_macro_receipt :
    (∀ C d : Nat, finalMicroDigit C d = outDigit C d)
    ∧ (∀ C d : Nat,
      3 * nextCarry C d + outDigit C d = C + 4 * d)
    ∧ (∀ C d : Nat,
      sevenKernel C d =
        14 * (twoI (outDigit C d) - twoI d) + 7 * surviveI C d) :=
  ⟨finalMicroDigit_eq_outDigit_universal,
    cell_transition_exact_universal,
    sevenKernel_micro_telescope_universal⟩

#check finalMicroDigit_eq_outDigit_universal
#check cell_transition_exact_universal
#check sevenKernel_micro_telescope_universal
#check finalMicroDigit_physical_absorbed
#check sevenKernel_physical_absorbed
#check universal_micro_macro_receipt

#print axioms finalMicroDigit_eq_outDigit_universal
#print axioms cell_transition_exact_universal
#print axioms sevenKernel_micro_telescope_universal
#print axioms universal_micro_macro_receipt

end GST2DMixedEmergenceUpgrade
