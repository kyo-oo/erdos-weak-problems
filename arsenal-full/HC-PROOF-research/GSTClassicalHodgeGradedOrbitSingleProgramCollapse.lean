import GSTClassicalHodgeGradedCorrespondenceProgramOrbit

/-!
# GST CLASSICAL HODGE — GRADED ORBIT SINGLE-PROGRAM COLLAPSE

`fullCorrespondenceOrbitSubspace` was defined as the rational span of the set
of outputs of graded correspondence programs.  But the graded program language
itself already contains rational scaling and addition.

Therefore the orbit set is already a rational submodule: every finite rational
linear combination of program outputs is the output of ONE larger program.
The span construction is mathematically redundant.

This matters for the ontological-graph interpretation.  A Hodge class does not
need to be described as an external finite linear combination of many unrelated
causal histories.  Those histories can be compiled into one graded GST program
from the geometric origin.  The remaining generation statement may therefore
be stated pointwise:

  every Hodge class = cohomologyEval(P)(origin)

for one actual graded correspondence program `P`.
-/

set_option maxHeartbeats 140000000
set_option maxRecDepth 1000000

noncomputable section

open AlgebraicGeometry

namespace GSTClassicalHodgeGradedOrbitSingleProgramCollapse

open GSTProjectiveOverC
open GSTGeometricRealizationStage2D
open GSTGeometricRealizationStage2F
open GSTGeometricRealizationStage2G
open GSTClassicalHodgeGeometricCycleClassSpine
open GSTClassicalHodgeGradedCorrespondenceProgramOrbit
open GSTClassicalHodgeGradedCorrespondenceProgramOrbit.GradedCorrespondenceProgram
open GSTClassicalHodgeCrossWeightNativePropagation
open GSTClassicalHodgeExactClayStatement

variable {V : SmoothProjectiveComplexScheme}
variable {H : HodgeBigradedBettiData V}

/-- Canonical graded route from weight zero to weight `q`, obtained by repeated
genuine principal cuts.  It is used only to witness that the orbit contains
zero in every target weight. -/
noncomputable def originToWeightProgram
    (V : SmoothProjectiveComplexScheme)
    (H : HodgeBigradedBettiData V) :
    (q : Nat) → GradedCorrespondenceProgram V H 0 q
  | 0 => .id 0
  | q + 1 => .comp (originToWeightProgram V H q) (.cut q)

/-- The zero-output program in target weight `q`. -/
noncomputable def zeroOutputProgram
    (V : SmoothProjectiveComplexScheme)
    (H : HodgeBigradedBettiData V)
    (q : Nat) : GradedCorrespondenceProgram V H 0 q :=
  .smul 0 (originToWeightProgram V H q)

/-- Evaluation of a program sum is the sum of evaluations. -/
theorem cohomologyEval_add
    (G : GeometricCycleClassSpine V H)
    {p q : Nat}
    (A B : GradedCorrespondenceProgram V H p q)
    (alpha : RationalSingularCohomology H.analytification (2 * p)) :
    (.add A B : GradedCorrespondenceProgram V H p q).cohomologyEval G alpha =
      A.cohomologyEval G alpha + B.cohomologyEval G alpha := by
  rfl

/-- Evaluation of a rationally scaled program is the scaled evaluation. -/
theorem cohomologyEval_smul
    (G : GeometricCycleClassSpine V H)
    {p q : Nat}
    (a : ℚ)
    (A : GradedCorrespondenceProgram V H p q)
    (alpha : RationalSingularCohomology H.analytification (2 * p)) :
    (.smul a A : GradedCorrespondenceProgram V H p q).cohomologyEval G alpha =
      a • A.cohomologyEval G alpha := by
  rfl

/-- The explicit zero-output program evaluates to zero in every target weight. -/
theorem zeroOutputProgram_eval
    (G : GeometricCycleClassSpine V H)
    (q : Nat) :
    (zeroOutputProgram V H q).cohomologyEval G
      (correspondenceGeometricOriginClass V H) = 0 := by
  rw [zeroOutputProgram, cohomologyEval_smul]
  simp

/-- The verified graded correspondence orbit is already a rational submodule;
no external span closure is needed. -/
noncomputable def fullCorrespondenceOrbitModule
    (G : GeometricCycleClassSpine V H)
    (q : Nat) :
    Submodule ℚ (RationalSingularCohomology H.analytification (2 * q)) where
  carrier := fullCorrespondenceOrbitSet G q
  zero_mem' := by
    refine ⟨zeroOutputProgram V H q, ?_⟩
    symm
    exact zeroOutputProgram_eval G q
  add_mem' := by
    intro alpha beta halpha hbeta
    rcases halpha with ⟨A, rfl⟩
    rcases hbeta with ⟨B, rfl⟩
    refine ⟨.add A B, ?_⟩
    symm
    exact cohomologyEval_add G A B
      (correspondenceGeometricOriginClass V H)
  smul_mem' := by
    intro a alpha halpha
    rcases halpha with ⟨A, rfl⟩
    refine ⟨.smul a A, ?_⟩
    symm
    exact cohomologyEval_smul G a A
      (correspondenceGeometricOriginClass V H)

/-- The old span-based orbit subspace equals the orbit itself, viewed as the
submodule above. -/
theorem fullCorrespondenceOrbitSubspace_eq_module
    (G : GeometricCycleClassSpine V H)
    (q : Nat) :
    fullCorrespondenceOrbitSubspace G q =
      fullCorrespondenceOrbitModule G q := by
  apply le_antisymm
  · apply Submodule.span_le.2
    intro alpha halpha
    exact halpha
  · intro alpha halpha
    exact Submodule.subset_span halpha

/-- Membership in the full graded orbit subspace is exactly existence of ONE
graded correspondence program from weight zero. -/
theorem mem_fullCorrespondenceOrbitSubspace_iff_singleProgram
    (G : GeometricCycleClassSpine V H)
    (q : Nat)
    (alpha : RationalSingularCohomology H.analytification (2 * q)) :
    alpha ∈ fullCorrespondenceOrbitSubspace G q ↔
      ∃ P : GradedCorrespondenceProgram V H 0 q,
        alpha = P.cohomologyEval G
          (correspondenceGeometricOriginClass V H) := by
  rw [fullCorrespondenceOrbitSubspace_eq_module]
  rfl

/-- The current orbit-cyclicity condition is equivalent to direct
single-program generation of every rational Hodge class. -/
theorem fullCorrespondenceOrbitCyclic_iff_singleProgramGeneration
    (G : GeometricCycleClassSpine V H) :
    FullCorrespondenceOrbitCyclic G ↔
      ∀ q : Nat,
      ∀ alpha : RationalSingularCohomology H.analytification (2 * q),
        alpha ∈ rationalHodgeSubspace (H.hodgeBigrading q) →
        ∃ P : GradedCorrespondenceProgram V H 0 q,
          alpha = P.cohomologyEval G
            (correspondenceGeometricOriginClass V H) := by
  constructor
  · intro hcyc q alpha halpha
    exact (mem_fullCorrespondenceOrbitSubspace_iff_singleProgram
      G q alpha).1 (hcyc q halpha)
  · intro hgen q alpha halpha
    exact (mem_fullCorrespondenceOrbitSubspace_iff_singleProgram
      G q alpha).2 (hgen q alpha halpha)

/-- **SINGLE-PROGRAM EXACT HODGE FINALE.**
If every rational Hodge class is the output of one actual graded correspondence
program from the geometric origin, the literal rational Hodge conjecture
follows. -/
theorem exactHodge_of_singleProgramGeneration
    (G : GeometricCycleClassSpine V H)
    (hgen :
      ∀ q : Nat,
      ∀ alpha : RationalSingularCohomology H.analytification (2 * q),
        alpha ∈ rationalHodgeSubspace (H.hodgeBigrading q) →
        ∃ P : GradedCorrespondenceProgram V H 0 q,
          alpha = P.cohomologyEval G
            (correspondenceGeometricOriginClass V H)) :
    EveryHodgeClassIsRationalAlgebraic H :=
  exactHodge_of_fullCorrespondenceOrbitCyclic G
    ((fullCorrespondenceOrbitCyclic_iff_singleProgramGeneration G).2 hgen)

#check originToWeightProgram
#check zeroOutputProgram
#check cohomologyEval_add
#check cohomologyEval_smul
#check fullCorrespondenceOrbitModule
#check fullCorrespondenceOrbitSubspace_eq_module
#check mem_fullCorrespondenceOrbitSubspace_iff_singleProgram
#check fullCorrespondenceOrbitCyclic_iff_singleProgramGeneration
#check exactHodge_of_singleProgramGeneration

#print axioms cohomologyEval_add
#print axioms cohomologyEval_smul
#print axioms fullCorrespondenceOrbitSubspace_eq_module
#print axioms fullCorrespondenceOrbitCyclic_iff_singleProgramGeneration
#print axioms exactHodge_of_singleProgramGeneration

end GSTClassicalHodgeGradedOrbitSingleProgramCollapse
