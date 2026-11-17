import GSTClassicalHodgeGradedGeometricProgramOrbit

/-!
# GST CLASSICAL HODGE — GRADED GEOMETRIC ORBIT ALGEBRA

The mixed program language already contains rational scaling and addition.
Consequently the set of states reachable from the canonical geometric origin
is itself a rational submodule; taking a separate linear span is unnecessary.

This file upgrades the orbit accordingly and proves a stronger graded module
law: **every** geometric program `p -> q` sends the reachable module at weight
`p` into the reachable module at weight `q`, simply by post-composition of
programs.

Hence the upgraded geometry cosmology is not merely a collection of reachable
states.  It is a genuine graded module over the whole mixed noncommutative
program algebra.
-/

set_option maxHeartbeats 90000000
set_option maxRecDepth 1000000

noncomputable section

open AlgebraicGeometry

namespace GSTClassicalHodgeGradedGeometricOrbitAlgebra

open GSTProjectiveOverC
open GSTGeometricRealizationStage2D
open GSTGeometricRealizationStage2F
open GSTGeometricRealizationStage2G
open GSTClassicalHodgeGeometricCycleClassSpine
open GSTClassicalHodgeLimitlessSpinePropagation
open GSTClassicalHodgeGradedGeometricProgramOrbit

variable {V : SmoothProjectiveComplexScheme}
variable {H : HodgeBigradedBettiData V}

/-- The program orbit is already linearly closed because addition and rational
scaling are constructors of the program algebra itself. -/
noncomputable def geometricProgramOrbitModule
    (G : GeometricCycleClassSpine V H)
    (q : Nat) :
    Submodule ℚ (RationalSingularCohomology H.analytification (2 * q)) where
  carrier := geometricProgramOrbitSet G q
  zero_mem' := by
    change ∃ P : GradedGeometricProgram V 0 q,
      (0 : RationalSingularCohomology H.analytification (2 * q)) =
        P.cohomologyEval G (geometricOriginClass V H)
    refine ⟨.smul 0 (normalizedSpineProgram V q), ?_⟩
    simp [GradedGeometricProgram.cohomologyEval,
      GradedGeometricProgram.toPair,
      GradedCycleClassOperatorPair.smulPair]
  add_mem' := by
    intro a b ha hb
    rcases ha with ⟨A, rfl⟩
    rcases hb with ⟨B, rfl⟩
    refine ⟨.add A B, ?_⟩
    simp [GradedGeometricProgram.cohomologyEval,
      GradedGeometricProgram.toPair,
      GradedCycleClassOperatorPair.addPair]
  smul_mem' := by
    intro c a ha
    rcases ha with ⟨A, rfl⟩
    refine ⟨.smul c A, ?_⟩
    simp [GradedGeometricProgram.cohomologyEval,
      GradedGeometricProgram.toPair,
      GradedCycleClassOperatorPair.smulPair]

/-- The original span-based orbit is exactly the intrinsic reachable module. -/
theorem geometricProgramOrbitSubspace_eq_module
    (G : GeometricCycleClassSpine V H)
    (q : Nat) :
    geometricProgramOrbitSubspace G q = geometricProgramOrbitModule G q := by
  apply le_antisymm
  · apply Submodule.span_le.2
    intro alpha halpha
    exact halpha
  · intro alpha halpha
    exact Submodule.subset_span halpha

/-- **GRADED ORBIT MODULE LAW.**
Any mixed geometric program sends a reachable state to another reachable
state.  At the syntax level this is just program composition. -/
theorem program_maps_geometricProgramOrbitModule
    (G : GeometricCycleClassSpine V H)
    {p q : Nat}
    (P : GradedGeometricProgram V p q)
    {alpha : RationalSingularCohomology H.analytification (2 * p)}
    (halpha : alpha ∈ geometricProgramOrbitModule G p) :
    P.cohomologyEval G alpha ∈ geometricProgramOrbitModule G q := by
  rcases halpha with ⟨A, hA⟩
  subst alpha
  refine ⟨.comp A P, ?_⟩
  rfl

/-- Submodule-map form of the graded orbit law. -/
theorem map_geometricProgramOrbitModule_le
    (G : GeometricCycleClassSpine V H)
    {p q : Nat}
    (P : GradedGeometricProgram V p q) :
    Submodule.map (P.cohomologyEval G) (geometricProgramOrbitModule G p) ≤
      geometricProgramOrbitModule G q := by
  rintro beta ⟨alpha, halpha, rfl⟩
  exact program_maps_geometricProgramOrbitModule G P halpha

/-- The intrinsic reachable module remains contained in the genuine cycle-class
range. -/
theorem geometricProgramOrbitModule_le_cycleClass_range
    (G : GeometricCycleClassSpine V H)
    (q : Nat) :
    geometricProgramOrbitModule G q ≤
      LinearMap.range (H.cycleClass q) := by
  rw [← geometricProgramOrbitSubspace_eq_module G q]
  exact geometricProgramOrbitSubspace_le_cycleClass_range G q

/-- The intrinsic reachable module remains contained in the true Hodge sector. -/
theorem geometricProgramOrbitModule_le_hodge
    (G : GeometricCycleClassSpine V H)
    (q : Nat) :
    geometricProgramOrbitModule G q ≤
      rationalHodgeSubspace (H.hodgeBigrading q) := by
  rw [← geometricProgramOrbitSubspace_eq_module G q]
  exact geometricProgramOrbitSubspace_le_hodge G q

/-- The canonical normalized spine seed is an element of the intrinsic orbit
module at every weight, not merely of an auxiliary span. -/
theorem spineHodgeSeed_mem_geometricProgramOrbitModule
    (G : GeometricCycleClassSpine V H)
    (q : Nat) :
    (spineHodgeSeed G q).1 ∈ geometricProgramOrbitModule G q := by
  exact spineHodgeSeed_mem_geometricProgramOrbitSet G q

/-- Intrinsic cyclicity formulation. -/
def GradedGeometricOrbitModuleCyclic
    (G : GeometricCycleClassSpine V H) : Prop :=
  ∀ q : Nat,
    rationalHodgeSubspace (H.hodgeBigrading q) ≤
      geometricProgramOrbitModule G q

/-- The intrinsic module formulation is equivalent to the earlier span
formulation. -/
theorem gradedGeometricOrbitModuleCyclic_iff
    (G : GeometricCycleClassSpine V H) :
    GradedGeometricOrbitModuleCyclic G ↔ GradedGeometricOrbitCyclic G := by
  constructor
  · intro h q alpha halpha
    rw [geometricProgramOrbitSubspace_eq_module G q]
    exact h q halpha
  · intro h q alpha halpha
    rw [← geometricProgramOrbitSubspace_eq_module G q]
    exact h q halpha

/-- Hodge landing directly from intrinsic graded-module cyclicity. -/
theorem bigradedBettiHodge_of_gradedGeometricOrbitModuleCyclic
    (G : GeometricCycleClassSpine V H)
    (hcyclic : GradedGeometricOrbitModuleCyclic G) :
    BigradedBettiHodgeStatement V H := by
  exact bigradedBettiHodge_of_gradedGeometricOrbitCyclic G
    ((gradedGeometricOrbitModuleCyclic_iff G).mp hcyclic)

#check geometricProgramOrbitModule
#check geometricProgramOrbitSubspace_eq_module
#check program_maps_geometricProgramOrbitModule
#check map_geometricProgramOrbitModule_le
#check geometricProgramOrbitModule_le_cycleClass_range
#check geometricProgramOrbitModule_le_hodge
#check GradedGeometricOrbitModuleCyclic
#check gradedGeometricOrbitModuleCyclic_iff
#check bigradedBettiHodge_of_gradedGeometricOrbitModuleCyclic

#print axioms geometricProgramOrbitSubspace_eq_module
#print axioms program_maps_geometricProgramOrbitModule
#print axioms geometricProgramOrbitModule_le_cycleClass_range
#print axioms bigradedBettiHodge_of_gradedGeometricOrbitModuleCyclic

end GSTClassicalHodgeGradedGeometricOrbitAlgebra