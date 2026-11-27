import Mathlib
import HCUniverse.GSTClayOfficial
import HCUniverse.GSTHodgeAssaultV2

/-!
# RATIONAL HODGE LAYER V2 — ALL-WEIGHT FINITE GST CLASSIFICATION

This layer strengthens the rationalized internal GST statement.
It classifies every natural weight of the finite lattice and records
uniqueness on the three live diagonal weights.
-/

set_option maxHeartbeats 10000000
set_option maxRecDepth 1000000

namespace GSTClayOfficialV2

open GSTWaveCohomology
open GSTLefschetzCrown
open GSTHodgeAssault
open GSTHodgeAssaultV2
open GSTClayOfficial

/-- Above weight two the rational cycle class is identically zero. -/
theorem ratCycleClass_zero_of_three_le (p : Nat) (hp : 3 ≤ p) :
    ratCycleClass p = fun _ => 0 := by
  funext c
  unfold ratCycleClass
  rw [cycleClass_zero_of_three_le p hp]
  norm_num

/-- **ALL-WEIGHT RATIONAL CLASSIFICATION.**  Every integral GST Hodge class,
after rationalization, is a rational multiple of its weight cycle class for
every p : Nat.  Above weight two this is the zero-sector statement. -/
theorem rational_hodge_all_weights
    (p : Nat) (f : WaveCoef) (hf : isHodgeClass p f) :
    ∃ q : ℚ, ∀ c : WaveCell,
      rat f c = q * ratCycleClass p c := by
  obtain ⟨z,hz⟩ := (hodge_class_all_weights p f).mp hf
  refine ⟨(z:ℚ), ?_⟩
  intro c
  unfold rat ratCycleClass
  exact_mod_cast hz c

/-- On live weights the rational coefficient is exactly the diagonal
coordinate, without existential ambiguity. -/
theorem rational_hodge_coefficient_exact
    (p : Nat) (hp : p < 3) (f : WaveCoef)
    (hf : isHodgeClass p f) :
    ∀ c : WaveCell,
      rat f c =
        ((gev f (4*p) : ℤ) : ℚ) * ratCycleClass p c := by
  obtain ⟨z,hz⟩ := hodge_conjecture p hp f hf
  have hzc := hodge_coefficient_eq_coordinate p hp f hf z hz
  intro c
  unfold rat ratCycleClass
  rw [← hzc]
  exact_mod_cast hz c

/-- The live rational coefficient is unique. -/
theorem rational_hodge_coefficient_unique
    (p : Nat) (hp : p < 3) (f : WaveCoef)
    (q r : ℚ)
    (hq : ∀ c : WaveCell, rat f c = q * ratCycleClass p c)
    (hr : ∀ c : WaveCell, rat f c = r * ratCycleClass p c) :
    q = r := by
  have hp4 : p < 4 := by omega
  let c : WaveCell := ⟨p,p,hp4,hp⟩
  have hc : ratCycleClass p c = 1 := by
    unfold ratCycleClass c
    rw [cycle_at_diagonal p p p hp4 hp rfl rfl]
    norm_num
  have h1 := hq c
  have h2 := hr c
  rw [hc, mul_one] at h1 h2
  linarith

/-- Above weight two every rationalized Hodge class is zero. -/
theorem rational_hodge_zero_of_three_le
    (p : Nat) (hp : 3 ≤ p) (f : WaveCoef)
    (hf : isHodgeClass p f) :
    rat f = fun _ => 0 := by
  have hz := hodge_class_zero_of_three_le p hp f hf
  funext c
  unfold rat
  rw [hz]
  norm_num

theorem rational_v2_crown :
    (∀ p f, isHodgeClass p f →
      ∃ q : ℚ, ∀ c : WaveCell,
        rat f c = q * ratCycleClass p c)
    ∧ (∀ p, p < 3 → ∀ f, isHodgeClass p f →
      ∀ c : WaveCell,
        rat f c =
          ((gev f (4*p) : ℤ) : ℚ) * ratCycleClass p c)
    ∧ (∀ p, 3 ≤ p → ∀ f, isHodgeClass p f →
      rat f = fun _ => 0) := by
  exact ⟨rational_hodge_all_weights,
    rational_hodge_coefficient_exact,
    rational_hodge_zero_of_three_le⟩

#check ratCycleClass_zero_of_three_le
#check rational_hodge_all_weights
#check rational_hodge_coefficient_exact
#check rational_hodge_coefficient_unique
#check rational_hodge_zero_of_three_le
#check rational_v2_crown

#print axioms rational_hodge_all_weights
#print axioms rational_hodge_coefficient_exact
#print axioms rational_hodge_coefficient_unique
#print axioms rational_v2_crown

end GSTClayOfficialV2
