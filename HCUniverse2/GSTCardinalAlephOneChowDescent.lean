import HCUniverse2.GSTCardinalWorldHodgeStarPart1
import Mathlib

/-!
# Owner's GST aleph-one input / uncountable Chow specialization gate

Companion ACTUAL original-X geometric proof:
research/derivations/GST_owner_aleph1_Chow_specialization_originalX_source_birth_20261111.tex

Main independent set-theoretic leaf:
If an UNCOUNTABLE collection of distinct original GST geometry world
inputs is labelled by only COUNTABLY many profiles, some single
profile occurs UNCOUNTABLY often.

Apply to the profile (positive denominator, positive effective
cycle degree, negative effective cycle degree) in N x N x N.
Relative Chow parameter spaces for a fixed profile are projective
over a smooth projective family base; their finitely many connected
components have locally constant rational Betti cycle class.
On an irreducible algebraic CURVE, a proper closed subset is finite,
so an uncountably populated good component must dominate the curve
and has a true cycle on the prescribed original fiber.

The actual relative Chow properness and specialization are proven
geometrically in the companion source derivation. This file formalizes
the load-bearing cardinal pigeonhole theorem; it is NOT a formal
claim that Mathlib has constructed the relative Chow scheme or that
arbitrary prescribed alpha has nearby algebraic source fibers.
-/

set_option maxHeartbeats 2500000
noncomputable section

namespace GSTCardinalAlephOneChowDescent

universe u v

variable {I : Type u} {J : Type v}

/-- The core user's aleph-one law: an uncountable set of genuinely
distinct source worlds cannot be exhausted by countably many
countable degree/denominator profiles. -/
theorem uncountable_source_worlds_have_uncountable_profile
    [Countable J] (sourceWorlds : Set I) (profile : I → J)
    (hSources : ¬ sourceWorlds.Countable) :
    ∃ j : J,
      ¬ (sourceWorlds ∩ profile ⁻¹' {j}).Countable := by
  classical
  by_contra h
  push_neg at h
  have hUnion :
      (⋃ j : J, sourceWorlds ∩ profile ⁻¹' {j}).Countable :=
    Set.countable_iUnion h
  have hCover :
      sourceWorlds ⊆ ⋃ j : J, sourceWorlds ∩ profile ⁻¹' {j} := by
    intro i hi
    apply Set.mem_iUnion.mpr
    refine ⟨profile i, ?_⟩
    exact ⟨hi, rfl⟩
  exact hSources (hUnion.mono hCover)

/-- Apply the exact owner's aleph-one stage to integer denominator
and TWO effective Chow degrees. These profiles are countable,
without assuming ANY uniform bound on their input values. -/
theorem uncountably_many_inputs_share_unbounded_Chow_profile
    (sourceWorlds : Set I)
    (denominator degreePositive degreeNegative : I → ℕ)
    (hSources : ¬ sourceWorlds.Countable) :
    ∃ m dPlus dMinus : ℕ,
      ¬ (sourceWorlds ∩
        {i | denominator i = m ∧
          degreePositive i = dPlus ∧
          degreeNegative i = dMinus}).Countable := by
  let profile : I → ℕ × ℕ × ℕ :=
    fun i => (denominator i, degreePositive i, degreeNegative i)
  obtain ⟨⟨m, dPlus, dMinus⟩, h⟩ :=
    uncountable_source_worlds_have_uncountable_profile
      sourceWorlds profile hSources
  refine ⟨m, dPlus, dMinus, ?_⟩
  simpa [profile, Set.preimage, Set.mem_setOf_eq,
    Prod.mk.injEq] using h

#check uncountable_source_worlds_have_uncountable_profile
#check uncountably_many_inputs_share_unbounded_Chow_profile
#print axioms uncountable_source_worlds_have_uncountable_profile
#print axioms uncountably_many_inputs_share_unbounded_Chow_profile

end GSTCardinalAlephOneChowDescent
