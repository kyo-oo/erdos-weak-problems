import GSTClassicalHodgeHandwrittenPiEquationDerivation
import GSTClassicalHodgeGradedCorrespondenceProgramOrbit
import GSTClassicalHodgePiStrictOmniverseCompiler

/-!
# GST CLASSICAL HODGE — HANDWRITTEN PI / FULL CORRESPONDENCE PROGRAM LANDING

The projective-word splice proves the handwritten Pi collapse through actual
projective self-maps.  The live branch, however, sits on the correspondence-
fusion lineage, whose verified geometric language is strictly larger.

This file therefore drives the SAME handwritten equations through the full
`GradedCorrespondenceProgram` algebra:

* start at the genuine codimension-zero fundamental cycle;
* run one actual mixed full-correspondence program `P0 : 0 -> p`;
* assume only that its resulting class is nonzero;
* choose the canonical nonzero source coordinate `c` of that derived state;
* for every target sheet `j`, use one genuine realized-correspondence
  expression whose independently defined cohomological action on that ONE
  source is `c * e_j`;
* compose that expression after `P0`, so `c * e_j` is literally an element of
  the full correspondence orbit;
* divide by `c`, obtaining `e_j` in the verified orbit;
* rewrite every handwritten GST branch as `alpha_i * e_j`;
* apply the exact finite branch-collapse identity to recover `alpha` inside the
  same verified orbit;
* use full-program cycle-class naturality to obtain an actual native cycle.

The second half removes even the realized-expression source-hit as an abstract
input.  A source-specific `StrictlyMaterializedBranch` already contains an
actual bi-finite scheme correspondence, cup/Gysin/incidence primitives, and the
computed equality with the GST target branch.  The existing strict compiler
turns precisely those branches into the expressions consumed here.

Crucially, we require strict materialization ONLY for the one derived source to
the requested target sheets.  No global `every omniverse event is materialized`
premise is used.
-/

set_option maxHeartbeats 140000000
set_option maxRecDepth 1000000

noncomputable section

open scoped BigOperators
open AlgebraicGeometry

namespace GSTClassicalHodgeHandwrittenPiCorrespondenceProgramLanding

open GSTProjectiveOverC
open GSTGeometricRealizationStage2D
open GSTGeometricRealizationStage2F
open GSTGeometricRealizationStage2G
open GSTClassicalHodgeFiberedCosmology
open GSTClassicalHodgeRankFreeArsenalIrreducibility
open GSTClassicalHodgeGeometricCycleClassSpine
open GSTClassicalHodgeCodimensionZeroFundamentalCycle
open GSTClassicalHodgeSynchronizedDefectOrbit
open GSTClassicalHodgeHandwrittenPiEquationDerivation
open GSTClassicalHodgeGradedCorrespondenceProgramOrbit
open GSTClassicalHodgeGradedCorrespondenceProgramOrbit.GradedCorrespondenceProgram
open GSTClassicalHodgeRealizedCorrespondenceExpressionAlgebra
open GSTClassicalHodgeRealizedCorrespondenceExpressionAlgebra.RealizedCorrespondenceExpr
open GSTClassicalHodgeOmniverseCausalBranchPacket
open GSTClassicalHodgePiOmniverseBranchSynthesis
open GSTClassicalHodgeOmniverseStrictEventStability
open GSTClassicalHodgePiStrictOmniverseCompiler

variable {V : SmoothProjectiveComplexScheme}
variable {H : HodgeBigradedBettiData V}
variable {p : Nat}

/-- A nonzero same-weight synchronized algebraic source derived from ONE
verified full correspondence program starting at the canonical codimension-zero
fundamental cycle.  No same-weight source is independently postulated. -/
noncomputable def fullOrbitSeedOfProgram
    (G : GeometricCycleClassSpine V H)
    (P0 : GradedCorrespondenceProgram V H 0 p)
    (hne : P0.cohomologyEval G (correspondenceGeometricOriginClass V H) ≠ 0) :
    NativeHodgeOrbitSeed (V := V) (H := H) (p := p) := by
  let Z0 : codimensionCycles V.X p :=
    P0.cycleEval G (codimensionZeroFundamentalCycle V)
  let a0 : RationalSingularCohomology H.analytification (2 * p) :=
    P0.cohomologyEval G (correspondenceGeometricOriginClass V H)
  have hclass : H.cycleClass p Z0 = a0 := by
    simpa [Z0, a0, correspondenceGeometricOriginClass] using
      P0.cycleClass_cycleEval G (codimensionZeroFundamentalCycle V)
  have hHodge : a0 ∈ rationalHodgeSubspace (H.hodgeBigrading p) := by
    rw [← hclass]
    exact G.algebraic_is_hodge p Z0
  let a : ClassicalHodgeFiber V H p := ⟨a0, hHodge⟩
  refine {
    cycle := Z0
    hodge := a
    hodge_ne_zero := ?_
    class_eq := ?_
  }
  · intro ha
    apply hne
    exact congrArg Subtype.val ha
  · simpa [a] using hclass

/-- The derived source is a literal generator of the full correspondence orbit,
not merely an element inferred later from cycle-class range membership. -/
theorem fullOrbitSeedOfProgram_mem_orbit
    (G : GeometricCycleClassSpine V H)
    (P0 : GradedCorrespondenceProgram V H 0 p)
    (hne : P0.cohomologyEval G (correspondenceGeometricOriginClass V H) ≠ 0) :
    (fullOrbitSeedOfProgram G P0 hne).hodge.1 ∈
      fullCorrespondenceOrbitSubspace G p := by
  apply Submodule.subset_span
  refine ⟨P0, ?_⟩
  rfl

/-- Source-specific realized-correspondence expression data.  This is not an
arbitrary ambient linear operator: `E j` is syntax built only from genuinely
realized finite closed correspondences, rational scaling, addition and ordered
composition. -/
structure SourceTargetCorrespondenceExpressions
    (G : GeometricCycleClassSpine V H)
    (P0 : GradedCorrespondenceProgram V H 0 p)
    (hne : P0.cohomologyEval G (correspondenceGeometricOriginClass V H) ≠ 0) where
  expr : ∀ j : ClassicalHodgeBasisIndex V H p,
    RealizedCorrespondenceExpr V H p
  source_action : ∀ j : ClassicalHodgeBasisIndex V H p,
    (expr j).cohomologyOperator (fullOrbitSeedOfProgram G P0 hne).hodge.1 =
      (classicalHodgeBasis V H p).repr
          (fullOrbitSeedOfProgram G P0 hne).hodge
          (fullOrbitSeedOfProgram G P0 hne).sourceIndex •
        (classicalHodgeBasis V H p j).1

namespace SourceTargetCorrespondenceExpressions

/-- Compose the actual source program with the actual realized correspondence
expression for target `j`. -/
noncomputable def targetProgram
    (R : SourceTargetCorrespondenceExpressions G P0 hne)
    (j : ClassicalHodgeBasisIndex V H p) :
    GradedCorrespondenceProgram V H 0 p :=
  .comp P0 (.correspondence (R.expr j))

/-- Exact output of the composed full program on the geometric origin. -/
theorem targetProgram_origin_action
    (R : SourceTargetCorrespondenceExpressions G P0 hne)
    (j : ClassicalHodgeBasisIndex V H p) :
    (R.targetProgram j).cohomologyEval G
        (correspondenceGeometricOriginClass V H) =
      (classicalHodgeBasis V H p).repr
          (fullOrbitSeedOfProgram G P0 hne).hodge
          (fullOrbitSeedOfProgram G P0 hne).sourceIndex •
        (classicalHodgeBasis V H p j).1 := by
  change
    (R.expr j).cohomologyOperator
        (P0.cohomologyEval G (correspondenceGeometricOriginClass V H)) = _
  simpa [fullOrbitSeedOfProgram] using R.source_action j

/-- **FULL CORRESPONDENCE ORIGIN -> ONE BASIS SHEET.**
The composed program puts `c * e_j` in the actual full-program orbit.  The
selected source coefficient `c` is nonzero, so rational scaling isolates
`e_j` itself inside the verified orbit subspace. -/
theorem basis_mem_fullCorrespondenceOrbit
    (R : SourceTargetCorrespondenceExpressions G P0 hne)
    (j : ClassicalHodgeBasisIndex V H p) :
    (classicalHodgeBasis V H p j).1 ∈
      fullCorrespondenceOrbitSubspace G p := by
  let S := fullOrbitSeedOfProgram G P0 hne
  let c : ℚ := (classicalHodgeBasis V H p).repr S.hodge S.sourceIndex
  have hc : c ≠ 0 := S.sourceCoefficient_ne_zero
  have hgen :
      c • (classicalHodgeBasis V H p j).1 ∈
        fullCorrespondenceOrbitSubspace G p := by
    apply Submodule.subset_span
    refine ⟨R.targetProgram j, ?_⟩
    simpa [S, c] using (R.targetProgram_origin_action j).symm
  have hscaled :=
    (fullCorrespondenceOrbitSubspace G p).smul_mem c⁻¹ hgen
  simpa [smul_smul, hc] using hscaled

/-- Every unrestricted Hodge basis direction is in the actual full
correspondence orbit once the source-specific realized expressions are known. -/
theorem every_basis_mem_fullCorrespondenceOrbit
    (R : SourceTargetCorrespondenceExpressions G P0 hne) :
    ∀ j : ClassicalHodgeBasisIndex V H p,
      (classicalHodgeBasis V H p j).1 ∈
        fullCorrespondenceOrbitSubspace G p :=
  fun j => R.basis_mem_fullCorrespondenceOrbit j

/-- **THE HANDWRITTEN GST BRANCHES ARE NOW GEOMETRIC.**
For an arbitrary requested Hodge class `alpha`, the exact GST equation gives

  E_ij(alpha) = alpha_i * e_j.

Since the correspondence program argument has already put `e_j` in the
verified geometric orbit, every live localized-L2 branch appearing in the
handwritten finite sum lies in that same orbit. -/
theorem localizedL2_branch_mem_fullCorrespondenceOrbit
    (R : SourceTargetCorrespondenceExpressions G P0 hne)
    (alpha : ClassicalHodgeFiber V H p)
    (i j : ClassicalHodgeBasisIndex V H p) :
    (localizedNormalizedL2 (V := V) (H := H) i j alpha).1 ∈
      fullCorrespondenceOrbitSubspace G p := by
  have hbasis := R.basis_mem_fullCorrespondenceOrbit j
  have hscaled :=
    (fullCorrespondenceOrbitSubspace G p).smul_mem
      (hodgeCoordinate i alpha) hbasis
  simpa [localizedNormalizedL2_apply, hodgeMatrixUnit_apply] using hscaled

/-- **HANDWRITTEN FINITE BRANCH COLLAPSE INSIDE THE FULL CORRESPONDENCE ORBIT.**
This is the requested page-two derivation with every step now living in the
strongest verified correspondence-fusion geometry language. -/
theorem class_mem_fullCorrespondenceOrbit_of_handwritten_collapse
    (R : SourceTargetCorrespondenceExpressions G P0 hne)
    (alpha : ClassicalHodgeFiber V H p) :
    alpha.1 ∈ fullCorrespondenceOrbitSubspace G p := by
  by_cases halpha : alpha = 0
  · subst alpha
    exact (fullCorrespondenceOrbitSubspace G p).zero_mem
  · obtain ⟨i, hi, hcollapse⟩ := branch_collapse_localizedL2 alpha halpha
    have hcollapseVal := congrArg Subtype.val hcollapse
    rw [hcollapseVal]
    simp only [Submodule.coe_sum, Submodule.coe_smul_of_tower]
    apply Submodule.sum_mem
    intro j hj
    exact (fullCorrespondenceOrbitSubspace G p).smul_mem
      (((classicalHodgeBasis V H p).repr alpha j) *
        (hodgeCoordinate i.1 alpha)⁻¹)
      (R.localizedL2_branch_mem_fullCorrespondenceOrbit alpha i.1 j)

/-- Exact native algebraic cycle obtained from the full correspondence orbit. -/
theorem native_cycle_of_handwritten_fullCorrespondence_collapse
    (R : SourceTargetCorrespondenceExpressions G P0 hne)
    (alpha : ClassicalHodgeFiber V H p) :
    ∃ Z : codimensionCycles V.X p,
      H.cycleClass p Z = alpha.1 := by
  exact fullCorrespondenceOrbitSubspace_le_cycleClass_range G p
    (R.class_mem_fullCorrespondenceOrbit_of_handwritten_collapse alpha)

end SourceTargetCorrespondenceExpressions

/-! ## Strict low-level specialization -/

/-- Omniverse node carried by the derived algebraic source. -/
noncomputable def derivedSourceNode
    (G : GeometricCycleClassSpine V H)
    (P0 : GradedCorrespondenceProgram V H 0 p)
    (hne : P0.cohomologyEval G (correspondenceGeometricOriginClass V H) ≠ 0) :
    HodgeBranchNode (V := V) (H := H) (p := p) :=
  ⟨GSTGraphV2OmniversalCore.Sector.gstPlus,
    (fullOrbitSeedOfProgram G P0 hne).hodge⟩

/-- Exact target node predicted by the GST matrix-unit equation. -/
noncomputable def derivedTargetNode
    (G : GeometricCycleClassSpine V H)
    (P0 : GradedCorrespondenceProgram V H 0 p)
    (hne : P0.cohomologyEval G (correspondenceGeometricOriginClass V H) ≠ 0)
    (j : ClassicalHodgeBasisIndex V H p) :
    HodgeBranchNode (V := V) (H := H) (p := p) :=
  let S := fullOrbitSeedOfProgram G P0 hne
  ⟨GSTGraphV2OmniversalCore.Sector.gstPlus,
    hodgeMatrixUnit S.sourceIndex j S.hodge⟩

/-- A strict materialization only for the source-to-`j` branch is enough to
construct the realized expression required above. -/
noncomputable def sourceTargetExpressionsOfStrictBranches
    (G : GeometricCycleClassSpine V H)
    (P0 : GradedCorrespondenceProgram V H 0 p)
    (hne : P0.cohomologyEval G (correspondenceGeometricOriginClass V H) ≠ 0)
    (hstrict : ∀ j : ClassicalHodgeBasisIndex V H p,
      StrictlyMaterializedBranch
        (derivedSourceNode G P0 hne)
        (derivedTargetNode G P0 hne j)) :
    SourceTargetCorrespondenceExpressions G P0 hne := by
  let S := fullOrbitSeedOfProgram G P0 hne
  choose E hE using fun j =>
    strictBranch_has_realizedExpression (hstrict j)
  refine {
    expr := E
    source_action := ?_
  }
  intro j
  have hmat := hE j
  change
    (derivedTargetNode G P0 hne j).state.1 =
      (E j).cohomologyOperator (derivedSourceNode G P0 hne).state.1 at hmat
  have heq := hmat.symm
  change
    (E j).cohomologyOperator S.hodge.1 =
      (hodgeMatrixUnit S.sourceIndex j S.hodge).1 at heq
  rw [hodgeMatrixUnit_apply] at heq
  simpa [S, hodgeCoordinate] using heq

/-- **SOURCE-SPECIFIC STRICT HANDWRITTEN LANDING.**
No global omniverse materialization law is needed.  Actual strict scheme
correspondences for precisely the branches fired from the one derived source
are enough to reconstruct any requested Hodge class by the handwritten finite
collapse. -/
theorem native_cycle_of_sourceSpecific_strict_branches
    (G : GeometricCycleClassSpine V H)
    (P0 : GradedCorrespondenceProgram V H 0 p)
    (hne : P0.cohomologyEval G (correspondenceGeometricOriginClass V H) ≠ 0)
    (hstrict : ∀ j : ClassicalHodgeBasisIndex V H p,
      StrictlyMaterializedBranch
        (derivedSourceNode G P0 hne)
        (derivedTargetNode G P0 hne j))
    (alpha : ClassicalHodgeFiber V H p) :
    ∃ Z : codimensionCycles V.X p,
      H.cycleClass p Z = alpha.1 := by
  let R := sourceTargetExpressionsOfStrictBranches G P0 hne hstrict
  exact R.native_cycle_of_handwritten_fullCorrespondence_collapse alpha

/-- Global Stage-2G crown using the exact same handwritten equation in every
weight, with one nonzero origin program and only source-specific strict branch
materializations. -/
theorem bigradedBettiHodge_of_sourceSpecific_strict_handwritten_programs
    (G : GeometricCycleClassSpine V H)
    (P0 : ∀ q : Nat, GradedCorrespondenceProgram V H 0 q)
    (hne : ∀ q : Nat,
      (P0 q).cohomologyEval G (correspondenceGeometricOriginClass V H) ≠ 0)
    (hstrict : ∀ q : Nat,
      ∀ j : ClassicalHodgeBasisIndex V H q,
        StrictlyMaterializedBranch
          (derivedSourceNode G (P0 q) (hne q))
          (derivedTargetNode G (P0 q) (hne q) j)) :
    BigradedBettiHodgeStatement V H := by
  intro q alpha halpha
  let alphaH : ClassicalHodgeFiber V H q := ⟨alpha, halpha⟩
  exact native_cycle_of_sourceSpecific_strict_branches
    G (P0 q) (hne q) (hstrict q) alphaH

#check fullOrbitSeedOfProgram
#check SourceTargetCorrespondenceExpressions
#check SourceTargetCorrespondenceExpressions.targetProgram
#check SourceTargetCorrespondenceExpressions.basis_mem_fullCorrespondenceOrbit
#check SourceTargetCorrespondenceExpressions.localizedL2_branch_mem_fullCorrespondenceOrbit
#check SourceTargetCorrespondenceExpressions.class_mem_fullCorrespondenceOrbit_of_handwritten_collapse
#check SourceTargetCorrespondenceExpressions.native_cycle_of_handwritten_fullCorrespondence_collapse
#check sourceTargetExpressionsOfStrictBranches
#check native_cycle_of_sourceSpecific_strict_branches
#check bigradedBettiHodge_of_sourceSpecific_strict_handwritten_programs

#print axioms SourceTargetCorrespondenceExpressions.basis_mem_fullCorrespondenceOrbit
#print axioms SourceTargetCorrespondenceExpressions.class_mem_fullCorrespondenceOrbit_of_handwritten_collapse
#print axioms SourceTargetCorrespondenceExpressions.native_cycle_of_handwritten_fullCorrespondence_collapse
#print axioms sourceTargetExpressionsOfStrictBranches
#print axioms native_cycle_of_sourceSpecific_strict_branches
#print axioms bigradedBettiHodge_of_sourceSpecific_strict_handwritten_programs

end GSTClassicalHodgeHandwrittenPiCorrespondenceProgramLanding
