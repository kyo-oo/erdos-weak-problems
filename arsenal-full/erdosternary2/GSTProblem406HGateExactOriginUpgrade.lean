import GSTProblem406PrefixOneDyadicNoGo
import GSTProblem406TightPhysicalCut
import GSTFourPowerThirdWave
import Mathlib

set_option maxRecDepth 1000000
set_option maxHeartbeats 20000000

/-!
# Exact-origin correction of the candidate hGate induction

The verified source E=4339*4^12 refutes a general GST three-step
propagation law, not the original pure-four-power hGate.
The exact odd cofactor 1 is essential to the original input domain.

This file proves the false-law counterexample is OUTSIDE the
quantified source domain, and isolates the original source-specific
gate with a true exact finite 24/19 row cap.

NO unconditional hGate is asserted or manufactured.
-/

namespace GSTProblem406HGateExactOriginUpgrade

open GSTProblem406PrefixOneDyadicNoGo
open GSTProblem406TightPhysicalCut
open GSTFourPowerDirectResidue
open GSTFourPowerDirectExistence
open GSTFourPowerThirdWave

/-- A valid input to the exact four-power gate has odd binary
cofactor one by construction. -/
def ExactFourPowerOrigin (E : Nat) : Prop :=
  ∃ K : Nat, E = 4^K

/-- The new high-v2 BAD countermodel is NOT a pure four-power
source, regardless of exponent. The proof distinguishes the
bounded powers by exact computation and the higher powers by
their forced 4^13 divisibility. -/
theorem countermodel_not_a_four_power (K : Nat) :
    sourceE ≠ 4^K := by
  intro h
  by_cases hsmall : K < 13
  · interval_cases K <;> norm_num [sourceE] at h
  · have hmod : sourceE % 4^13 ≠ 0 := by decide
    apply hmod
    have hK : K = 13 + (K-13) := by omega
    rw [h, hK, pow_add]
    simp [Nat.mul_mod]

theorem countermodel_outside_exact_origin :
    ¬ ExactFourPowerOrigin sourceE := by
  rintro ⟨K,hK⟩
  exact countermodel_not_a_four_power K hK

/-- A true K-indexed physical wave is exactly the hGate target:
no quantification over arbitrary seeded or synthetic BAD sources. -/
def ExactOriginHGate : Prop :=
  ∀ K : Nat, 5 ≤ K → K ≠ 7 → thirdWave K

/-- The canonical GST third-wave predicate is equivalent to the
unconditional pure-power CommonTwo target. This does not assert
that either predicate is universally true. -/
theorem exact_origin_hGate_iff_original :
    ExactOriginHGate ↔ FourPowerDirectExistence := by
  simpa only [ExactOriginHGate] using
    GSTFourPowerThirdWave.fourPowerDirectExistence_iff_thirdWave.symm

/-- After the verified low-exponent base, the only unresolved hGate
parameter region is K>=13, and each witness is provably below the
sharper exact physical origin cut. -/
def StrictPhysicalOriginHGate : Prop :=
  ∀ K : Nat, 13 ≤ K →
    ∃ p : Nat, 1 ≤ p ∧ p < tighterPhysicalCut K ∧
      digit3 (4^K) p = 2 ∧
      digit3 (4^(K+1)) p = 2

/-- The low original hGate exponents are discharged directly,
with the ONLY excluded exponent K=7. No propagation principle
is used here. -/
private theorem all_low_physical_exponents
    (K : Nat) (hK : 5 ≤ K) (h13 : K < 13) (h7 : K ≠ 7) :
    CommonTwo K := by
  interval_cases K <;> first
    | omega
    | exact ⟨2, by decide, by decide, by decide⟩
    | exact ⟨4, by decide, by decide, by decide⟩
    | exact ⟨7, by decide, by decide, by decide⟩
    | exact ⟨10, by decide, by decide, by decide⟩

/-- This is the corrected formal hGate contract. The original
universal target is EQUIVALENT to the exact power-only physical
gate with bounded rows, after the kernel-checked base cases.
Importantly the countermodel for generic E cannot refute this
equivalence, because its source is not 4^K. -/
theorem exact_origin_hGate_iff_strict_physical_cut :
    ExactOriginHGate ↔ StrictPhysicalOriginHGate := by
  constructor
  · intro h K hK
    have hCommon : CommonTwo K :=
      (thirdWave_iff_commonTwo K).mp
        (h K (by omega) (by omega))
    exact (original_commonTwo_iff_tighter_cut K hK).mp hCommon
  · intro h K hK h7
    apply (thirdWave_iff_commonTwo K).mpr
    by_cases h13 : 13 ≤ K
    · exact (original_commonTwo_iff_tighter_cut K h13).mpr
        (h K h13)
    · exact all_low_physical_exponents K hK (by omega) h7

/-- Complete exact proof-scope correction: refuting the seed-class
three-step propagation theorem cannot instantiate a refutation of
the pure-power hGate. This is a proven separation, not an
assumption of hGate truth. -/
theorem corrected_scope_certificate :
    (¬ ExactFourPowerOrigin sourceE) ∧
    (ExactOriginHGate ↔ StrictPhysicalOriginHGate) :=
  ⟨countermodel_outside_exact_origin,
   exact_origin_hGate_iff_strict_physical_cut⟩

#print axioms countermodel_not_a_four_power
#print axioms countermodel_outside_exact_origin
#print axioms all_low_physical_exponents
#print axioms exact_origin_hGate_iff_original
#print axioms exact_origin_hGate_iff_strict_physical_cut
#print axioms corrected_scope_certificate

end GSTProblem406HGateExactOriginUpgrade
