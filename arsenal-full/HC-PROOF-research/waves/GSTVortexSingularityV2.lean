import Mathlib
import waves.GSTVortexSingularity
import waves.GSTNCohomologyV2

/-!
# GVSM V2 — EXACT ORBITS, SHEET INVARIANCE, AND CUT WITNESSES

This upgrade strengthens the vortex/cascade layer by replacing selected
examples with exact classifications and replacing adjacent-sheet stability
with arbitrary deep-sheet invariance.
-/

set_option maxHeartbeats 10000000
set_option maxRecDepth 1000000

namespace GSTVortexSingularityV2

open GST2DMixedEmergence
open GSTCanonicalSevenAxisBridge
open GSTU2DEventTransport
open GSTVortexSingularity

/-- The two axial cells are exactly the fixed points of the vortex core. -/
theorem core_rotation_fixed_iff (C d : Nat) (hC : C < 4) (hd : d < 3) :
    coreRotate (C,d) = (C,d) ↔
      (C = 0 ∧ d = 0) ∨ (C = 3 ∧ d = 2) := by
  interval_cases C <;> interval_cases d <;> decide

/-- Every non-axis legal cell lies in the rotating sector. -/
theorem core_rotation_nonaxis_moves (C d : Nat)
    (hC : C < 4) (hd : d < 3)
    (haxis : ¬ ((C = 0 ∧ d = 0) ∨ (C = 3 ∧ d = 2))) :
    coreRotate (C,d) ≠ (C,d) := by
  intro hfix
  exact haxis ((core_rotation_fixed_iff C d hC hd).mp hfix)

/-- BIG2 spiral behavior is exact: NULL maps to carry two and every
non-NULL legal carry maps to carry three. -/
theorem spiral_big2_exact (C : Nat) (hC : C < 4) :
    spiralStep C 2 = if C = 0 then 2 else 3 := by
  interval_cases C <;> decide

theorem spiral_big2_two_iff (C : Nat) (hC : C < 4) :
    spiralStep C 2 = 2 ↔ C = 0 := by
  interval_cases C <;> decide

theorem spiral_big2_three_iff (C : Nat) (hC : C < 4) :
    spiralStep C 2 = 3 ↔ C ≠ 0 := by
  interval_cases C <;> decide

/-- **ARBITRARY-SHEET STABILITY.**  Any two sheets at or above the
primitive depth agree on the complete window modulo 3^k. -/
theorem cascade_pairwise_stable
    (core k S T : Nat)
    (hS : k-1 ≤ S) (hT : k-1 ≤ T) :
    (GSTGraphV2OmegaWaveLaw.omegaCutWord S 1 * core) % 3^k =
      (GSTGraphV2OmegaWaveLaw.omegaCutWord T 1 * core) % 3^k := by
  calc
    (GSTGraphV2OmegaWaveLaw.omegaCutWord S 1 * core) % 3^k
        = (GSTGraphV2OmegaWaveLaw.omegaCutWord (k-1) 1 * core) % 3^k :=
          GSTTailFFourthDimension.omega_tower_word_mod_chain core k S hS
    _ = (GSTGraphV2OmegaWaveLaw.omegaCutWord T 1 * core) % 3^k :=
          (GSTTailFFourthDimension.omega_tower_word_mod_chain core k T hT).symm

/-- The value of every stabilized window is independent of the chosen
sufficiently deep sheet. -/
theorem cascade_window_canonical
    (core k S : Nat) (hS : k-1 ≤ S) :
    (GSTGraphV2OmegaWaveLaw.omegaCutWord S 1 * core) % 3^k =
      (GSTGraphV2OmegaWaveLaw.omegaCutWord (k-1) 1 * core) % 3^k :=
  GSTTailFFourthDimension.omega_tower_word_mod_chain core k S hS

/-- **EXACT IGNITION WITNESS.**  The vortex does not merely contradict an
all-bad tail; it fires at the explicit LTE cut row a+1. -/
theorem vortex_ignition_exact
    (a core : Nat) (ha : 1 ≤ a) (hcore : core % 3 = 2) :
    HappyCell
      (carry4 (4^(3^a * core)) (a+1))
      (digit3 (4^(3^a * core)) (a+1)) :=
  GSTGraphV2OmegaWaveLaw.omega_cut_happy_gate a core ha hcore

/-- The old singularity theorem is absorbed by the exact witness. -/
theorem vortex_singularity_forms_absorbed
    (a core : Nat) (ha : 2 ≤ a) (hcore : core % 3 = 2) :
    ¬ (∀ p : Nat, 3 ≤ p →
        ¬ HappyCell (carry4 (4^(3^a * core)) p)
          (digit3 (4^(3^a * core)) p)) := by
  intro hbad
  exact hbad (a+1) (by omega)
    (vortex_ignition_exact a core (by omega) hcore)

/-- Every ignited N-shape channel has an exact structural cut witness,
including its sheet and core, rather than only an unspecified row. -/
theorem gvsm_exact_cut_signature (s : GSTNCohomology.NShape)
    (hign : ∀ i : Fin s.holes, ignitionCondition (s.channel i)) :
    ∀ i : Fin s.holes,
      ∃ a core : Nat,
        2 ≤ a ∧ core % 3 = 2 ∧
        s.channel i = 3^a * core ∧
        HappyCell
          (carry4 (4^(s.channel i)) (a+1))
          (digit3 (4^(s.channel i)) (a+1)) := by
  intro i
  rcases hign i with ⟨a, core, ha, hcore, hchan⟩
  refine ⟨a, core, ha, hcore, hchan, ?_⟩
  rw [hchan]
  exact vortex_ignition_exact a core (by omega) hcore

/-- Every ignited shape admits a global cut-row selector, one explicit
firing row for every hole simultaneously. -/
theorem gvsm_global_cut_selector (s : GSTNCohomology.NShape)
    (hign : ∀ i : Fin s.holes, ignitionCondition (s.channel i)) :
    ∃ cut : Fin s.holes → Nat,
      ∀ i : Fin s.holes,
        3 ≤ cut i ∧
        HappyCell
          (carry4 (4^(s.channel i)) (cut i))
          (digit3 (4^(s.channel i)) (cut i)) := by
  classical
  let witness : ∀ i : Fin s.holes, ∃ p : Nat,
      3 ≤ p ∧ HappyCell
        (carry4 (4^(s.channel i)) p)
        (digit3 (4^(s.channel i)) p) := by
    intro i
    rcases gvsm_exact_cut_signature s hign i with
      ⟨a, core, ha, hcore, hchan, hhappy⟩
    exact ⟨a+1, by omega, hhappy⟩
  let cut : Fin s.holes → Nat := fun i => Classical.choose (witness i)
  refine ⟨cut, ?_⟩
  intro i
  exact Classical.choose_spec (witness i)

/-- Capstone of the strengthened vortex layer. -/
theorem gvsm_v2_crown :
    (∀ C d, C < 4 → d < 3 →
      (coreRotate (C,d) = (C,d) ↔
        (C = 0 ∧ d = 0) ∨ (C = 3 ∧ d = 2)))
    ∧ (∀ core k S T, k-1 ≤ S → k-1 ≤ T →
      (GSTGraphV2OmegaWaveLaw.omegaCutWord S 1 * core) % 3^k =
        (GSTGraphV2OmegaWaveLaw.omegaCutWord T 1 * core) % 3^k)
    ∧ (∀ a core, 1 ≤ a → core % 3 = 2 →
      HappyCell
        (carry4 (4^(3^a * core)) (a+1))
        (digit3 (4^(3^a * core)) (a+1))) := by
  refine ⟨?_, ?_, vortex_ignition_exact⟩
  · intro C d hC hd
    exact core_rotation_fixed_iff C d hC hd
  · intro core k S T hS hT
    exact cascade_pairwise_stable core k S T hS hT

#check core_rotation_fixed_iff
#check core_rotation_nonaxis_moves
#check spiral_big2_exact
#check cascade_pairwise_stable
#check vortex_ignition_exact
#check gvsm_exact_cut_signature
#check gvsm_global_cut_selector
#check gvsm_v2_crown

#print axioms core_rotation_fixed_iff
#print axioms cascade_pairwise_stable
#print axioms vortex_ignition_exact
#print axioms gvsm_exact_cut_signature
#print axioms gvsm_v2_crown

end GSTVortexSingularityV2
