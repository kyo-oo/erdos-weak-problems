import GSTClassicalHodgeGradedCorrespondenceProgramOrbit
import GSTNativeCodimensionCyclePresentation
import GSTClassicalHodgeGradedNativeCohomologyRealization
import GSTClassicalHodgePrincipalCutSuccessorOperator
import GSTClassicalHodgeAtomicSpan
import GSTClassicalHodgeExactClayStatement
import GSTClassicalHodgeNativeExecutablePlane
import GSTClassicalHodgeCodimensionZeroFundamentalCycle

/-!
# GST CLASSICAL HODGE — MINIMAL NATIVE GEOMETRIC CORE

The historical geometric spine stored cohomological operators and Hodge
preservation data. For the actual correspondence-program proof these are
stronger than necessary.

The minimal native core below stores only:

* Hodge type of genuine codimension-point cycle classes;
* kernel stability of the geometry-built principal-cut successor.

All whole-cycle Hodge typing follows from the point-atomic normal form.
All principal-cut cohomological operators and commuting squares are generated
from kernel stability. Realized closed-correspondence atoms already carry
their own exact native/cohomological square.

Thus the complete full-correspondence GST program algebra can be interpreted
without a GeometricCycleClassSpine and without a principal-cut Hodge field.
-/

set_option maxHeartbeats 180000000
set_option maxRecDepth 1000000

noncomputable section

open scoped BigOperators
open AlgebraicGeometry

namespace GSTClassicalHodgeMinimalNativeGeometricCore

open GSTProjectiveOverC
open GSTGeometricRealizationStage2D
open GSTNativeCodimensionCyclePresentation
open GSTGeometricRealizationStage2F
open GSTGeometricRealizationStage2G
open GSTClassicalHodgeAtomicSpan
open GSTClassicalHodgeFiberedCosmology
open GSTClassicalHodgeRankFreeArsenalIrreducibility
open GSTClassicalHodgePrincipalCutSuccessorOperator
open GSTClassicalHodgeCrossWeightNativePropagation
open GSTClassicalHodgeGradedNativeCohomologyRealization
open GSTClassicalHodgeGradedGeometricProgramOrbit
open GSTClassicalHodgeGradedCorrespondenceProgramOrbit
open GSTClassicalHodgeGradedCorrespondenceProgramOrbit.GradedCorrespondenceProgram
open GSTClassicalHodgeRealizedCorrespondenceExpressionAlgebra
open GSTClassicalHodgeExactClayStatement

variable {V : SmoothProjectiveComplexScheme}
variable {H : HodgeBigradedBettiData V}

/-- The irreducible semantic core consumed by the full native GST program
route. No whole-cycle Hodge axiom, no pushforward cohomology operator, and no
principal-cut Hodge-preservation field is stored. -/
structure MinimalNativeGeometricCore
    (V : SmoothProjectiveComplexScheme)
    (H : HodgeBigradedBettiData V) where
  pointClass_is_hodge :
    ∀ p : Nat, ∀ x : CodimensionPoint V.X p,
      H.cycleClass p (codimensionPointCycle V.X p x) ∈
        rationalHodgeSubspace (H.hodgeBigrading p)
  principalCut_kernelStable :
    ∀ p : Nat,
      GradedKernelStable (H := H) (successorNativeOperator V p)

namespace MinimalNativeGeometricCore

/-- Pointwise Hodge typing forces Hodge type for every native cycle class. -/
theorem algebraic_is_hodge
    (C : MinimalNativeGeometricCore (V := V) (H := H))
    (p : Nat)
    (Z : codimensionCycles V.X p) :
    H.cycleClass p Z ∈ rationalHodgeSubspace (H.hodgeBigrading p) := by
  have hspan :
      pointCycleClassSpan p (H.cycleClass p) ≤
        rationalHodgeSubspace (H.hodgeBigrading p) := by
    apply Submodule.span_le.mpr
    rintro y ⟨x, rfl⟩
    exact C.pointClass_is_hodge p x
  apply hspan
  rw [← smoothProjective_cycleClass_range_eq_atomic_span V H p]
  exact ⟨Z, rfl⟩

/-- Kernel stability canonically manufactures the principal-cut operator pair.
The ambient cohomology action is not input data. -/
noncomputable def principalCutPair
    (C : MinimalNativeGeometricCore (V := V) (H := H))
    (p : Nat) :
    GradedCycleClassOperatorPair V H p (p + 1) :=
  toGradedCycleClassOperatorPair
    (successorNativeOperator V p)
    (C.principalCut_kernelStable p)

@[simp] theorem principalCutPair_cycleOperator
    (C : MinimalNativeGeometricCore (V := V) (H := H))
    (p : Nat) :
    (C.principalCutPair p).cycleOperator = successorNativeOperator V p := by
  rfl

/-- Exact principal-cut cycle-class naturality is generated from the kernel
law rather than stored. -/
theorem principalCut_naturality
    (C : MinimalNativeGeometricCore (V := V) (H := H))
    (p : Nat)
    (Z : codimensionCycles V.X p) :
    H.cycleClass (p + 1) (successorNativeOperator V p Z) =
      (C.principalCutPair p).cohomologyOperator (H.cycleClass p Z) := by
  exact (C.principalCutPair p).cycleClass_natural Z

/-- Interpret the complete correspondence/cut syntax using only the minimal
native core. -/
noncomputable def programPair
    (C : MinimalNativeGeometricCore (V := V) (H := H)) :
    {p q : Nat} → GradedCorrespondenceProgram V H p q →
      GradedCycleClassOperatorPair V H p q
  | _, _, .id p => GradedCycleClassOperatorPair.idPair V H p
  | _, _, .correspondence E =>
      { cycleOperator := E.cycleOperator
        cohomologyOperator := E.cohomologyOperator
        cycleClass_natural := fun Z => E.cycleClass_natural Z }
  | _, _, .cut p => C.principalCutPair p
  | _, _, .add A B =>
      GradedCycleClassOperatorPair.addPair (programPair C A) (programPair C B)
  | _, _, .smul a A =>
      GradedCycleClassOperatorPair.smulPair a (programPair C A)
  | _, _, .comp A B =>
      GradedCycleClassOperatorPair.compPair (programPair C A) (programPair C B)

noncomputable def cycleEval
    (C : MinimalNativeGeometricCore (V := V) (H := H))
    {p q : Nat}
    (P : GradedCorrespondenceProgram V H p q) :
    codimensionCycles V.X p →ₗ[ℚ] codimensionCycles V.X q :=
  (programPair C P).cycleOperator

noncomputable def cohomologyEval
    (C : MinimalNativeGeometricCore (V := V) (H := H))
    {p q : Nat}
    (P : GradedCorrespondenceProgram V H p q) :
    RationalSingularCohomology H.analytification (2 * p) →ₗ[ℚ]
      RationalSingularCohomology H.analytification (2 * q) :=
  (programPair C P).cohomologyOperator

/-- Master naturality theorem over the reduced core. -/
theorem cycleClass_cycleEval
    (C : MinimalNativeGeometricCore (V := V) (H := H))
    {p q : Nat}
    (P : GradedCorrespondenceProgram V H p q)
    (Z : codimensionCycles V.X p) :
    H.cycleClass q (cycleEval C P Z) =
      cohomologyEval C P (H.cycleClass p Z) :=
  (programPair C P).cycleClass_natural Z

/-- Every program output on a native source has true target Hodge type, derived
only after native execution. No operator Hodge-preservation field is used. -/
theorem program_output_is_hodge
    (C : MinimalNativeGeometricCore (V := V) (H := H))
    {p q : Nat}
    (P : GradedCorrespondenceProgram V H p q)
    (Z : codimensionCycles V.X p) :
    cohomologyEval C P (H.cycleClass p Z) ∈
      rationalHodgeSubspace (H.hodgeBigrading q) := by
  rw [← cycleClass_cycleEval C P Z]
  exact C.algebraic_is_hodge q (cycleEval C P Z)

/-- Canonical cohomological origin of the reduced program universe. -/
noncomputable def originClass
    (C : MinimalNativeGeometricCore (V := V) (H := H)) :
    RationalSingularCohomology H.analytification 0 :=
  H.cycleClass 0
    (GSTClassicalHodgeCodimensionZeroFundamentalCycle.codimensionZeroFundamentalCycle V)

/-- GEOMETRIC PLANE COMPLETENESS OVER THE MINIMAL NATIVE CORE.
Every Hodge basis sheet is reached by one executable full correspondence/cut
program. -/
def FullGSTPlaneCompleteness
    (C : MinimalNativeGeometricCore (V := V) (H := H)) : Prop :=
  ∀ q : Nat, ∀ j : ClassicalHodgeBasisIndex V H q,
    ∃ P : GradedCorrespondenceProgram V H 0 q,
      cohomologyEval C P (originClass C) =
        (classicalHodgeBasis V H q j).1

/-- Execute one geometric plane edge natively to obtain its target basis
cycle. -/
noncomputable def basisCycle
    (C : MinimalNativeGeometricCore (V := V) (H := H))
    (hplane : FullGSTPlaneCompleteness C)
    (q : Nat)
    (j : ClassicalHodgeBasisIndex V H q) :
    codimensionCycles V.X q :=
  let P := Classical.choose (hplane q j)
  cycleEval C P
    (GSTClassicalHodgeCodimensionZeroFundamentalCycle.codimensionZeroFundamentalCycle V)

/-- Every geometric plane edge is literally the class of the native cycle
obtained by executing the same program. -/
theorem basisCycle_spec
    (C : MinimalNativeGeometricCore (V := V) (H := H))
    (hplane : FullGSTPlaneCompleteness C)
    (q : Nat)
    (j : ClassicalHodgeBasisIndex V H q) :
    H.cycleClass q (basisCycle C hplane q j) =
      (classicalHodgeBasis V H q j).1 := by
  let P := Classical.choose (hplane q j)
  have hP := Classical.choose_spec (hplane q j)
  have hnat := cycleClass_cycleEval C P
    (GSTClassicalHodgeCodimensionZeroFundamentalCycle.codimensionZeroFundamentalCycle V)
  have hP' : (C.cohomologyEval P)
      ((H.cycleClass 0)
        (GSTClassicalHodgeCodimensionZeroFundamentalCycle.codimensionZeroFundamentalCycle V)) =
      (classicalHodgeBasis V H q j).1 := hP
  rw [hP'] at hnat
  simpa [basisCycle, P, originClass] using hnat

/-- Native execution is definitionally the cycle-side interpretation of the
minimal-core program pair. -/
theorem cycleEval_eq_nativeEval
    (C : MinimalNativeGeometricCore (V := V) (H := H))
    {p q : Nat}
    (P : GradedCorrespondenceProgram V H p q) :
    cycleEval C P =
      GSTClassicalHodgeNativeExecutablePlane.nativeEval P := by
  induction P <;>
    simp_all [cycleEval, programPair,
      GSTClassicalHodgeNativeExecutablePlane.nativeEval,
      GradedCycleClassOperatorPair.idPair,
      GradedCycleClassOperatorPair.addPair,
      GradedCycleClassOperatorPair.smulPair,
      GradedCycleClassOperatorPair.compPair]

/-- Minimal-core cohomological plane completeness therefore compiles to the
unique native-only terminal plane. -/
theorem nativeExecutablePlane_of_fullGSTPlane
    (C : MinimalNativeGeometricCore (V := V) (H := H))
    (hplane : FullGSTPlaneCompleteness C) :
    GSTClassicalHodgeNativeExecutablePlane.NativeExecutableGSTPlaneCompleteness
      (V := V) (H := H) := by
  intro q j
  obtain ⟨P,hP⟩ := hplane q j
  refine ⟨P, ?_⟩
  have hnat := cycleClass_cycleEval C P
    (GSTClassicalHodgeCodimensionZeroFundamentalCycle.codimensionZeroFundamentalCycle V)
  have hcycle := congrArg
    (fun A : codimensionCycles V.X 0 →ₗ[ℚ] codimensionCycles V.X q =>
      A (GSTClassicalHodgeCodimensionZeroFundamentalCycle.codimensionZeroFundamentalCycle V))
    (cycleEval_eq_nativeEval C P)
  change H.cycleClass q
      (GSTClassicalHodgeNativeExecutablePlane.nativeEval P
        (GSTClassicalHodgeCodimensionZeroFundamentalCycle.codimensionZeroFundamentalCycle V)) =
        (classicalHodgeBasis V H q j).1
  rw [← hcycle]
  exact hnat.trans hP

/-- MINIMAL-CORE FULL GST PLANE ⇒ EXACT HODGE.
No GeometricCycleClassSpine, no cut-Hodge preservation field, no native-mass
bridge, no ghost closure, and no Hodge-surjectivity premise occurs here. -/
theorem hodge_of_fullGSTPlane
    (C : MinimalNativeGeometricCore (V := V) (H := H))
    (hplane : FullGSTPlaneCompleteness C) :
    BigradedBettiHodgeStatement V H := by
  intro q alpha halpha
  let alphaH : ClassicalHodgeFiber V H q := ⟨alpha, halpha⟩
  rw [show alpha = ↑(Finsupp.linearCombination ℚ (classicalHodgeBasis V H q)
        ((classicalHodgeBasis V H q).repr alphaH)) from
      (congrArg Subtype.val
        ((classicalHodgeBasis V H q).linearCombination_repr alphaH)).symm,
    Finsupp.linearCombination_apply, Finsupp.sum,
    AddSubmonoidClass.coe_finsetSum]
  simp only [Submodule.coe_smul_of_tower, smul_eq_mul]
  exact Submodule.sum_mem _ fun j _ =>
    (LinearMap.range (H.cycleClass q)).smul_mem
      ((classicalHodgeBasis V H q).repr alphaH j)
      ⟨basisCycle C hplane q j, basisCycle_spec C hplane q j⟩

/-- Explicit native-cycle witness under the reduced geometric plane. -/
theorem nativeCycle_of_fullGSTPlane
    (C : MinimalNativeGeometricCore (V := V) (H := H))
    (hplane : FullGSTPlaneCompleteness C)
    (q : Nat)
    (alpha : RationalSingularCohomology H.analytification (2 * q))
    (halpha : alpha ∈ rationalHodgeSubspace (H.hodgeBigrading q)) :
    ∃ Z : codimensionCycles V.X q, H.cycleClass q Z = alpha :=
  hodge_of_fullGSTPlane C hplane q halpha

#check MinimalNativeGeometricCore
#check MinimalNativeGeometricCore.algebraic_is_hodge
#check MinimalNativeGeometricCore.principalCutPair
#check MinimalNativeGeometricCore.programPair
#check MinimalNativeGeometricCore.cycleClass_cycleEval
#check MinimalNativeGeometricCore.program_output_is_hodge
#check MinimalNativeGeometricCore.FullGSTPlaneCompleteness
#check MinimalNativeGeometricCore.cycleEval_eq_nativeEval
#check MinimalNativeGeometricCore.nativeExecutablePlane_of_fullGSTPlane
#check MinimalNativeGeometricCore.basisCycle_spec
#check MinimalNativeGeometricCore.hodge_of_fullGSTPlane
#check MinimalNativeGeometricCore.nativeCycle_of_fullGSTPlane

#print axioms MinimalNativeGeometricCore.algebraic_is_hodge
#print axioms MinimalNativeGeometricCore.cycleClass_cycleEval
#print axioms MinimalNativeGeometricCore.program_output_is_hodge
#print axioms MinimalNativeGeometricCore.cycleEval_eq_nativeEval
#print axioms MinimalNativeGeometricCore.nativeExecutablePlane_of_fullGSTPlane
#print axioms MinimalNativeGeometricCore.basisCycle_spec
#print axioms MinimalNativeGeometricCore.hodge_of_fullGSTPlane

end MinimalNativeGeometricCore
end GSTClassicalHodgeMinimalNativeGeometricCore
