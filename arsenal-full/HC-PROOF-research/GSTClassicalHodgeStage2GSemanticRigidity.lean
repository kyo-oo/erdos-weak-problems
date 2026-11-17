import GSTGeometricRealizationStage2G
import GSTClassicalHodgeAtomicDefectDuality

/-!
# GST CLASSICAL HODGE — STAGE-2G SEMANTIC RIGIDITY

`HodgeBigradedBettiData` currently stores the cycle-class map as an arbitrary
rational-linear map.  None of the other fields constrain that map.  Therefore
one can keep the same analytification and Hodge bigrading and replace the
cycle-class map by zero.

This module proves inside Lean that, whenever a rational `(p,p)` Hodge fiber is
nonzero, the zero-cycle-class version of the same semantic package fails the
Stage-2G Hodge statement.  Consequently no theorem quantified over *arbitrary*
`HodgeBigradedBettiData` can be the classical Hodge theorem unless the semantic
type is strengthened so that its cycle-class field is the genuine geometric
cycle-class construction.

This is a formal target-correction theorem, not a statement against the
limitless GST cosmology.  It tells the classical landing exactly which semantic
freedom must be removed before the geometric/native GST proof can close.
-/

set_option maxHeartbeats 30000000
set_option maxRecDepth 1000000

noncomputable section

open AlgebraicGeometry

namespace GSTClassicalHodgeStage2GSemanticRigidity

open GSTProjectiveOverC
open GSTGeometricRealizationStage2D
open GSTGeometricRealizationStage2F
open GSTGeometricRealizationStage2G

variable {V : SmoothProjectiveComplexScheme}

/-- Keep the genuine analytification and Hodge bigrading but erase all cycle
classes.  This is accepted by the current Stage-2G structure definition. -/
noncomputable def zeroCycleClassData
    (H : HodgeBigradedBettiData V) : HodgeBigradedBettiData V where
  analytification := H.analytification
  hodgeBigrading := H.hodgeBigrading
  cycleClass := fun _ => 0

@[simp]
theorem zeroCycleClassData_cycleClass
    (H : HodgeBigradedBettiData V) (p : Nat) :
    (zeroCycleClassData H).cycleClass p = 0 := rfl

@[simp]
theorem zeroCycleClassData_rationalHodgeSubspace
    (H : HodgeBigradedBettiData V) (p : Nat) :
    rationalHodgeSubspace ((zeroCycleClassData H).hodgeBigrading p) =
      rationalHodgeSubspace (H.hodgeBigrading p) := rfl

/-- A nonzero rational Hodge class cannot lie in the range of the zero cycle
class map. -/
theorem nonzero_hodge_not_in_zero_cycleClass_range
    (H : HodgeBigradedBettiData V)
    (p : Nat)
    (alpha : RationalSingularCohomology H.analytification (2 * p))
    (halpha0 : alpha ≠ 0) :
    alpha ∉ LinearMap.range ((zeroCycleClassData H).cycleClass p) := by
  rintro ⟨Z, hZ⟩
  simpa using halpha0 hZ.symm

/-- **ZERO-MAP COUNTERMODEL INSIDE THE CURRENT STAGE-2G TYPE.**
If one rational `(p,p)` fiber contains a nonzero class, replacing the arbitrary
cycle-class field by zero makes the exact Stage-2G Hodge statement false. -/
theorem not_bigradedBettiHodge_zeroCycleClass
    (H : HodgeBigradedBettiData V)
    (p : Nat)
    (alpha : RationalSingularCohomology H.analytification (2 * p))
    (halpha : alpha ∈ rationalHodgeSubspace (H.hodgeBigrading p))
    (halpha0 : alpha ≠ 0) :
    ¬ BigradedBettiHodgeStatement V (zeroCycleClassData H) := by
  intro h
  have hrange :
      alpha ∈ LinearMap.range ((zeroCycleClassData H).cycleClass p) := by
    exact h p halpha
  exact nonzero_hodge_not_in_zero_cycleClass_range H p alpha halpha0 hrange

/-- Submodule form: any nontrivial Hodge fiber produces a Stage-2G package with
identical Hodge theory and false Hodge conclusion simply by zeroing the
unconstrained cycle-class field. -/
theorem exists_semantic_countermodel_of_nontrivial_hodge
    (H : HodgeBigradedBettiData V)
    (p : Nat)
    (hH : rationalHodgeSubspace (H.hodgeBigrading p) ≠ ⊥) :
    ∃ H0 : HodgeBigradedBettiData V,
      H0 = zeroCycleClassData H ∧
      ¬ BigradedBettiHodgeStatement V H0 := by
  have hex : ∃ alpha : RationalSingularCohomology H.analytification (2 * p),
      alpha ∈ rationalHodgeSubspace (H.hodgeBigrading p) ∧ alpha ≠ 0 := by
    by_contra h
    push_neg at h
    apply hH
    ext alpha
    constructor
    · intro ha
      have hz := h alpha ha
      simpa [hz]
    · intro ha
      have h0 : alpha = 0 := by simpa using ha
      rw [h0]
      exact Submodule.zero_mem _
  obtain ⟨alpha, halpha, halpha0⟩ := hex
  exact ⟨zeroCycleClassData H, rfl,
    not_bigradedBettiHodge_zeroCycleClass H p alpha halpha halpha0⟩

/-- The semantic correction demanded by the classical landing: an
unconditional result must quantify over a type in which the cycle-class map is
geometrically fixed/constrained, not over the current arbitrary-map package. -/
theorem arbitrary_cycleClass_semantics_cannot_be_final_target
    (H : HodgeBigradedBettiData V)
    (p : Nat)
    (hH : rationalHodgeSubspace (H.hodgeBigrading p) ≠ ⊥) :
    ¬ (∀ H' : HodgeBigradedBettiData V,
      BigradedBettiHodgeStatement V H') := by
  intro hall
  obtain ⟨H0, _, hnot⟩ :=
    exists_semantic_countermodel_of_nontrivial_hodge H p hH
  exact hnot (hall H0)

#check zeroCycleClassData
#check nonzero_hodge_not_in_zero_cycleClass_range
#check not_bigradedBettiHodge_zeroCycleClass
#check exists_semantic_countermodel_of_nontrivial_hodge
#check arbitrary_cycleClass_semantics_cannot_be_final_target

#print axioms not_bigradedBettiHodge_zeroCycleClass
#print axioms exists_semantic_countermodel_of_nontrivial_hodge
#print axioms arbitrary_cycleClass_semantics_cannot_be_final_target

end GSTClassicalHodgeStage2GSemanticRigidity
