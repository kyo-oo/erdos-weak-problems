import GSTClassicalHodgeHandwrittenPiCorrespondenceProgramLanding

/-!
# GST CLASSICAL HODGE — HANDWRITTEN PI EXPLICIT NATIVE COLLAPSE

This file removes the final orbit-membership abstraction from the handwritten
Pi derivation.  Starting from the actual composed full-correspondence programs
already constructed in `GSTClassicalHodgeHandwrittenPiCorrespondenceProgramLanding`,
we write the native cycle itself.

Let `S` be the nonzero algebraic source obtained from one genuine program
`P0 : 0 -> p`, and let

  c = coordinate_S(sourceIndex) != 0.

For each Hodge basis direction `j`, the source-target correspondence expression
produces an actual composed program whose cohomological value on the geometric
origin is

  c * e_j.

Apply the native side of that same program to the codimension-zero fundamental
cycle and divide by `c`.  This gives a concrete codimension-p cycle `Z_j` with

  cl(Z_j) = e_j.

For an arbitrary nonzero Hodge class `alpha`, choose the live index `i` from
the exact GST handwritten branch-collapse theorem and define

  B_ij(alpha) = alpha_i * Z_j.

The cycle class of this branch is literally the localized normalized-L^2 GST
branch `E_ij(alpha) = alpha_i e_j`.  Therefore the handwritten finite collapse
can be executed on native cycles themselves:

  Z_alpha = sum_{j in supp(alpha)} (alpha_j / alpha_i) * B_ij(alpha)

and exact linearity gives

  cl(Z_alpha) = alpha.

No new Hodge-surjectivity premise, target cycle, arbitrary ambient endomorphism,
or native-mass bridge is introduced here.  The only geometric input is the
already-explicit source-target realized correspondence expression family.
-/

set_option maxHeartbeats 160000000
set_option maxRecDepth 1000000

noncomputable section

open scoped BigOperators
open AlgebraicGeometry

namespace GSTClassicalHodgeHandwrittenPiExplicitNativeCollapse

open GSTProjectiveOverC
open GSTGeometricRealizationStage2D
open GSTGeometricRealizationStage2G
open GSTClassicalHodgeFiberedCosmology
open GSTClassicalHodgeRankFreeArsenalIrreducibility
open GSTClassicalHodgeCodimensionZeroFundamentalCycle
open GSTClassicalHodgeHandwrittenPiEquationDerivation
open GSTClassicalHodgeHandwrittenPiCorrespondenceProgramLanding
open GSTClassicalHodgeHandwrittenPiCorrespondenceProgramLanding.SourceTargetCorrespondenceExpressions
open GSTClassicalHodgeGradedCorrespondenceProgramOrbit
open GSTClassicalHodgeGradedCorrespondenceProgramOrbit.GradedCorrespondenceProgram
open GSTClassicalHodgeGeometricCycleClassSpine
open GSTClassicalHodgeOmniverseCausalBranchPacket

variable {V : SmoothProjectiveComplexScheme}
variable {H : HodgeBigradedBettiData V}
variable {p : Nat}
variable {G : GeometricCycleClassSpine V H}
variable {P0 : GradedCorrespondenceProgram V H 0 p}
variable {hne : P0.cohomologyEval G (correspondenceGeometricOriginClass V H) ≠ 0}

/-- The nonzero source scalar selected by the actual origin program. -/
noncomputable def sourceScalar
    (R : SourceTargetCorrespondenceExpressions G P0 hne) : ℚ :=
  let S := fullOrbitSeedOfProgram G P0 hne
  (classicalHodgeBasis V H p).repr S.hodge S.sourceIndex

/-- The source scalar is nonzero because the source state itself is nonzero and
`NativeHodgeOrbitSeed.sourceIndex` is chosen from its live support. -/
theorem sourceScalar_ne_zero
    (R : SourceTargetCorrespondenceExpressions G P0 hne) :
    sourceScalar R ≠ 0 := by
  let S := fullOrbitSeedOfProgram G P0 hne
  simpa [sourceScalar, S] using S.sourceCoefficient_ne_zero

/-- Actual native target-basis cycle: execute the genuine composed
correspondence program on the geometric origin and normalize by the nonzero
source coefficient. -/
noncomputable def targetBasisCycle
    (R : SourceTargetCorrespondenceExpressions G P0 hne)
    (j : ClassicalHodgeBasisIndex V H p) :
    codimensionCycles V.X p :=
  (sourceScalar R)⁻¹ •
    (R.targetProgram j).cycleEval G (codimensionZeroFundamentalCycle V)

/-- The normalized native program output is exactly the requested Hodge basis
class.  This is the native/cohomological synchronization equation, not a range
membership shortcut. -/
theorem targetBasisCycle_spec
    (R : SourceTargetCorrespondenceExpressions G P0 hne)
    (j : ClassicalHodgeBasisIndex V H p) :
    H.cycleClass p (targetBasisCycle R j) =
      (classicalHodgeBasis V H p j).1 := by
  let c : ℚ := sourceScalar R
  have hc : c ≠ 0 := by
    simpa [c] using sourceScalar_ne_zero R
  have hnat :=
    (R.targetProgram j).cycleClass_cycleEval G (codimensionZeroFundamentalCycle V)
  have hact := R.targetProgram_origin_action j
  have horigin :
      H.cycleClass 0 (codimensionZeroFundamentalCycle V) =
        correspondenceGeometricOriginClass V H := by
    rfl
  rw [horigin, hact] at hnat
  unfold targetBasisCycle
  rw [LinearMap.map_smul, hnat]
  change c⁻¹ •
      ((classicalHodgeBasis V H p).repr
          (fullOrbitSeedOfProgram G P0 hne).hodge
          (fullOrbitSeedOfProgram G P0 hne).sourceIndex •
        (classicalHodgeBasis V H p j).1) = _
  change c⁻¹ • (c • (classicalHodgeBasis V H p j).1) = _
  simp [hc]

/-- Native realization of the exact handwritten GST branch `E_ij(alpha)`.
The cycle is the source coordinate of `alpha` times the genuine target-basis
cycle produced above. -/
noncomputable def branchCycle
    (R : SourceTargetCorrespondenceExpressions G P0 hne)
    (alpha : ClassicalHodgeFiber V H p)
    (i j : ClassicalHodgeBasisIndex V H p) :
    codimensionCycles V.X p :=
  hodgeCoordinate i alpha • targetBasisCycle R j

/-- **GST BRANCH = NATIVE BRANCH.**  The cycle class of the concrete branch is
literally the localized normalized-L^2 branch from the handwritten equation. -/
theorem branchCycle_spec
    (R : SourceTargetCorrespondenceExpressions G P0 hne)
    (alpha : ClassicalHodgeFiber V H p)
    (i j : ClassicalHodgeBasisIndex V H p) :
    H.cycleClass p (branchCycle R alpha i j) =
      (localizedNormalizedL2 (V := V) (H := H) i j alpha).1 := by
  unfold branchCycle
  rw [LinearMap.map_smul, targetBasisCycle_spec]
  simpa [localizedNormalizedL2_apply, hodgeMatrixUnit_apply]

/-- Choose the exact live source index used by the handwritten branch-collapse
identity.  This is a choice only of an already-proved GST witness. -/
noncomputable def collapseSourceIndex
    (alpha : ClassicalHodgeFiber V H p)
    (halpha : alpha ≠ 0) : HodgeSupportIndex alpha :=
  Classical.choose (branch_collapse_localizedL2 alpha halpha)

/-- The chosen handwritten source coordinate is nonzero. -/
theorem collapseSourceCoefficient_ne_zero
    (alpha : ClassicalHodgeFiber V H p)
    (halpha : alpha ≠ 0) :
    hodgeCoordinate (collapseSourceIndex alpha halpha).1 alpha ≠ 0 := by
  exact (Classical.choose_spec (branch_collapse_localizedL2 alpha halpha)).1

/-- The exact localized-L2 collapse equation associated to the chosen source. -/
theorem collapseSource_equation
    (alpha : ClassicalHodgeFiber V H p)
    (halpha : alpha ≠ 0) :
    alpha =
      ∑ j ∈ ((classicalHodgeBasis V H p).repr alpha).support,
        (((classicalHodgeBasis V H p).repr alpha j) *
            (hodgeCoordinate (collapseSourceIndex alpha halpha).1 alpha)⁻¹) •
          localizedNormalizedL2
            (V := V) (H := H)
            (collapseSourceIndex alpha halpha).1 j alpha := by
  exact (Classical.choose_spec (branch_collapse_localizedL2 alpha halpha)).2

/-- **THE LITERAL HANDWRITTEN NATIVE FINITE SUM.** -/
noncomputable def handwrittenCollapseCycle
    (R : SourceTargetCorrespondenceExpressions G P0 hne)
    (alpha : ClassicalHodgeFiber V H p)
    (halpha : alpha ≠ 0) :
    codimensionCycles V.X p :=
  let i := collapseSourceIndex alpha halpha
  ∑ j ∈ ((classicalHodgeBasis V H p).repr alpha).support,
    (((classicalHodgeBasis V H p).repr alpha j) *
        (hodgeCoordinate i.1 alpha)⁻¹) •
      branchCycle R alpha i.1 j

/-- **HANDWRITTEN PI NATIVE COLLAPSE IDENTITY.**
The native sum constructed with the same coefficients and same GST branches as
page two has cycle class exactly equal to the requested Hodge class. -/
theorem handwrittenCollapseCycle_spec
    (R : SourceTargetCorrespondenceExpressions G P0 hne)
    (alpha : ClassicalHodgeFiber V H p)
    (halpha : alpha ≠ 0) :
    H.cycleClass p (handwrittenCollapseCycle R alpha halpha) = alpha.1 := by
  let i := collapseSourceIndex alpha halpha
  have hcollapse := collapseSource_equation alpha halpha
  have hcollapseVal := congrArg Subtype.val hcollapse
  unfold handwrittenCollapseCycle
  rw [map_sum]
  simp only [LinearMap.map_smul]
  rw [hcollapseVal]
  simp only [Submodule.coe_sum, Submodule.coe_smul_of_tower]
  apply Finset.sum_congr rfl
  intro j hj
  rw [branchCycle_spec R alpha i.1 j]

/-- Zero-inclusive constructive form: every target state receives an explicit
native cycle rather than merely an existential range witness. -/
noncomputable def handwrittenCycle
    (R : SourceTargetCorrespondenceExpressions G P0 hne)
    (alpha : ClassicalHodgeFiber V H p) :
    codimensionCycles V.X p :=
  if halpha : alpha = 0 then 0
  else handwrittenCollapseCycle R alpha halpha

/-- Exact specification for the explicit native representative in all cases. -/
theorem handwrittenCycle_spec
    (R : SourceTargetCorrespondenceExpressions G P0 hne)
    (alpha : ClassicalHodgeFiber V H p) :
    H.cycleClass p (handwrittenCycle R alpha) = alpha.1 := by
  by_cases halpha : alpha = 0
  · subst alpha
    simp [handwrittenCycle]
  · simp [handwrittenCycle, halpha,
      handwrittenCollapseCycle_spec R alpha halpha]

#check sourceScalar
#check targetBasisCycle
#check targetBasisCycle_spec
#check branchCycle
#check branchCycle_spec
#check collapseSourceIndex
#check handwrittenCollapseCycle
#check handwrittenCollapseCycle_spec
#check handwrittenCycle
#check handwrittenCycle_spec

#print axioms targetBasisCycle_spec
#print axioms branchCycle_spec
#print axioms handwrittenCollapseCycle_spec
#print axioms handwrittenCycle_spec

end GSTClassicalHodgeHandwrittenPiExplicitNativeCollapse
