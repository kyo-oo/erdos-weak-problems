import GSTClassicalHodgeGeneralSpaceRealization
import GSTClassicalHodgeGeometryFirstNativeWord
import GSTClassicalHodgeNativeWordFromArbitrarySeed

set_option maxHeartbeats 100000000
set_option maxRecDepth 1000000

noncomputable section

open AlgebraicGeometry

namespace GSTClassicalHodgeGeneralSpaceOperatorCosmos

open GSTGeneralSpace
open GSTProjectiveOverC
open GSTGeometricRealizationStage2D
open GSTGeometricRealizationStage2F
open GSTGeometricRealizationStage2G
open GSTClassicalHodgeGeometricCycleClassSpine
open GSTClassicalHodgeGradedGeometricProgramOrbit
open GSTClassicalHodgeCrossWeightNativePropagation
open GSTClassicalHodgeGeneralSpaceRealization
open GSTClassicalHodgeFiberedCosmology
open GSTClassicalHodgeRankFreeArsenalIrreducibility
open GSTClassicalHodgeGeometryFirstTwoGenerator
open GSTClassicalHodgeGeometryFirstNativeWord
open GSTClassicalHodgeNativeWordFromArbitrarySeed

variable {V : SmoothProjectiveComplexScheme}
variable {H : HodgeBigradedBettiData V}

/-- A full GST geometric path is any already-constructed graded native/Betti
operator pair whose two faces commute with the genuine cycle-class map and
whose cohomological face carries the source state to the target state.

This strictly contains the earlier `GradedGeometricProgram` path language:
projective words and principal cuts embed, but so do genuine correspondence
operators and geometry-first GST native words once their commuting square has
been proved. -/
def OperatorReachability
    (x y : EvenBettiPoint V H) : Prop :=
  ∃ A : GradedCycleClassOperatorPair V H x.1 y.1,
    A.cohomologyOperator x.2 = y.2

/-- The full Hodge/Betti General Space operator cosmos. -/
def operatorGeneralSpace
    (V : SmoothProjectiveComplexScheme)
    (H : HodgeBigradedBettiData V) : GeneralSpace where
  Point := EvenBettiPoint V H
  Path := OperatorReachability
  idPath := by
    intro x
    refine ⟨GradedCycleClassOperatorPair.idPair V H x.1, rfl⟩
  compPath := by
    intro x y z hxy hyz
    rcases hxy with ⟨A, hA⟩
    rcases hyz with ⟨B, hB⟩
    refine ⟨GradedCycleClassOperatorPair.compPair A B, ?_⟩
    change B.cohomologyOperator (A.cohomologyOperator x.2) = z.2
    rw [hA, hB]
  comp_id_left := by intros; apply Subsingleton.elim
  comp_id_right := by intros; apply Subsingleton.elim
  comp_assoc := by intros; apply Subsingleton.elim

/-- Native locus in the full operator cosmos. -/
def OperatorNativeLocus
    (x : (operatorGeneralSpace V H).Point) : Prop :=
  x.2 ∈ LinearMap.range (H.cycleClass x.1)

/-- Hodge locus in the full operator cosmos. -/
def OperatorHodgeLocus
    (x : (operatorGeneralSpace V H).Point) : Prop :=
  x.2 ∈ rationalHodgeSubspace (H.hodgeBigrading x.1)

/-- **FULL COSMIC NATIVE CLOSURE.**
Every admissible path of the operator cosmos preserves genuine algebraic
realizability.  This is not an assumption: it is exactly the commuting square
stored in the path witness. -/
theorem operatorNativeLocus_pathClosed
    {x y : (operatorGeneralSpace V H).Point}
    (γ : (operatorGeneralSpace V H).Path x y)
    (hx : OperatorNativeLocus x) :
    OperatorNativeLocus y := by
  rcases γ with ⟨A, hA⟩
  rcases hx with ⟨Z, hZ⟩
  refine ⟨A.cycleOperator Z, ?_⟩
  rw [A.cycleClass_natural, hZ, hA]

/-- Every old mixed projective/cut program embeds into the full operator
cosmos, so this is an extension of the previous General Space rather than a
replacement of its genuine paths. -/
theorem gradedProgram_path
    (G : GeometricCycleClassSpine V H)
    {p q : Nat}
    (P : GradedGeometricProgram V p q)
    (alpha : RationalSingularCohomology H.analytification (2 * p)) :
    (operatorGeneralSpace V H).Path
      ⟨p, alpha⟩ ⟨q, P.cohomologyEval G alpha⟩ := by
  refine ⟨P.toPair G, rfl⟩

/-- Every geometry-first realization yields the correct native matrix-unit
pair: the code operator on the diagonal, the full GST word off-diagonal. -/
noncomputable def geometryFirstPair
    {p : Nat} {i j : ClassicalHodgeBasisIndex V H p}
    (R : GeometryFirstTwoGenerator (V := V) (H := H) i j) :
    GradedCycleClassOperatorPair V H p p := by
  classical
  exact if hij : i = j then
    { cycleOperator := R.code.cycleOperator
      cohomologyOperator := R.ambientCode
      cycleClass_natural := by
        intro Z
        exact R.code.cycleClass_natural Z }
  else
    { cycleOperator := nativeWord R
      cohomologyOperator := R.ambientWord
      cycleClass_natural := by
        intro Z
        exact cycleClass_nativeWord R Z }

/-- Both diagonal and off-diagonal geometry-first operators supply a genuine
path to the corresponding classical Hodge matrix-unit image. -/
theorem geometryFirst_path
    {p : Nat} {i j : ClassicalHodgeBasisIndex V H p}
    (R : GeometryFirstTwoGenerator (V := V) (H := H) i j)
    (alpha : ClassicalHodgeFiber V H p) :
    (operatorGeneralSpace V H).Path
      ⟨p, alpha.1⟩
      ⟨p, (hodgeMatrixUnit i j alpha).1⟩ := by
  refine ⟨geometryFirstPair R, ?_⟩
  by_cases hij : i = j
  · simpa [geometryFirstPair, hij] using
      (R.ambientCode_on_hodge_of_eq hij alpha)
  · simpa [geometryFirstPair, hij] using
      (R.ambientWord_on_hodge hij alpha)

/-- A nonzero arbitrary native Hodge seed gives a canonical source point of
the operator cosmos. -/
def seedPoint
    {p : Nat}
    (S : NativeHodgeSeed (V := V) (H := H) (p := p)) :
    EvenBettiPoint V H :=
  ⟨p, S.hodgeClass.1⟩

/-- The seed point lies in the native locus by construction. -/
theorem seedPoint_native
    {p : Nat}
    (S : NativeHodgeSeed (V := V) (H := H) (p := p)) :
    OperatorNativeLocus (seedPoint S) := by
  exact ⟨S.cycle, rfl⟩

/-- Normalize the geometry-first pair by the seed's nonzero live source
coordinate. -/
noncomputable def normalizedSeedPair
    {p : Nat}
    (S : NativeHodgeSeed (V := V) (H := H) (p := p))
    (j : ClassicalHodgeBasisIndex V H p)
    (R : GeometryFirstTwoGenerator
      (V := V) (H := H) S.sourceIndex j) :
    GradedCycleClassOperatorPair V H p p :=
  GradedCycleClassOperatorPair.smulPair S.sourceCoefficient⁻¹
    (geometryFirstPair R)

/-- The normalized GST word carries the arbitrary nonzero algebraic seed to
the exact target Hodge basis state. -/
theorem normalizedSeedPair_source
    {p : Nat}
    (S : NativeHodgeSeed (V := V) (H := H) (p := p))
    (j : ClassicalHodgeBasisIndex V H p)
    (R : GeometryFirstTwoGenerator
      (V := V) (H := H) S.sourceIndex j) :
    (normalizedSeedPair S j R).cohomologyOperator S.hodgeClass.1 =
      (classicalHodgeBasis V H p j).1 := by
  change S.sourceCoefficient⁻¹ •
      (geometryFirstPair R).cohomologyOperator S.hodgeClass.1 = _
  have hmatrix :
      (geometryFirstPair R).cohomologyOperator S.hodgeClass.1 =
        (hodgeMatrixUnit S.sourceIndex j S.hodgeClass).1 := by
    by_cases hij : S.sourceIndex = j
    · simpa [geometryFirstPair, hij] using
        (R.ambientCode_on_hodge_of_eq hij S.hodgeClass)
    · simpa [geometryFirstPair, hij] using
        (R.ambientWord_on_hodge hij S.hodgeClass)
  rw [hmatrix]
  rw [hodgeMatrixUnit_apply]
  change S.sourceCoefficient⁻¹ •
      (S.sourceCoefficient • (classicalHodgeBasis V H p j).1) = _
  simp [S.sourceCoefficient_ne_zero]

/-- **ARBITRARY NATIVE SEED -> EXACT HODGE SHEET GENERAL-SPACE PATH.** -/
theorem seed_to_basis_path
    {p : Nat}
    (S : NativeHodgeSeed (V := V) (H := H) (p := p))
    (j : ClassicalHodgeBasisIndex V H p)
    (R : GeometryFirstTwoGenerator
      (V := V) (H := H) S.sourceIndex j) :
    (operatorGeneralSpace V H).Path
      (seedPoint S)
      ⟨p, (classicalHodgeBasis V H p j).1⟩ := by
  refine ⟨normalizedSeedPair S j R, ?_⟩
  exact normalizedSeedPair_source S j R

/-- Consequently every target basis sheet reached by the full GST word is in
the actual native cycle-class locus. -/
theorem basis_native_of_geometryFirst
    {p : Nat}
    (S : NativeHodgeSeed (V := V) (H := H) (p := p))
    (j : ClassicalHodgeBasisIndex V H p)
    (R : GeometryFirstTwoGenerator
      (V := V) (H := H) S.sourceIndex j) :
    OperatorNativeLocus
      (⟨p, (classicalHodgeBasis V H p j).1⟩ : EvenBettiPoint V H) :=
  operatorNativeLocus_pathClosed (seed_to_basis_path S j R) (seedPoint_native S)

#check OperatorReachability
#check operatorGeneralSpace
#check operatorNativeLocus_pathClosed
#check gradedProgram_path
#check geometryFirstPair
#check geometryFirst_path
#check seedPoint
#check seed_to_basis_path
#check basis_native_of_geometryFirst

#print axioms operatorNativeLocus_pathClosed
#print axioms geometryFirst_path
#print axioms normalizedSeedPair_source
#print axioms seed_to_basis_path
#print axioms basis_native_of_geometryFirst

end GSTClassicalHodgeGeneralSpaceOperatorCosmos
