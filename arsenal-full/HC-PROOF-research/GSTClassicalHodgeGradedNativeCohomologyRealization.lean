import Mathlib.Algebra.Module.Projective
import GSTClassicalHodgeCrossWeightNativePropagation

/-!
# GST CLASSICAL HODGE — GRADED NATIVE COHOMOLOGY REALIZATION

Cross-weight geometry should start on native algebraic cycles, not from an
independently postulated Betti operator.  This module is the graded analogue
of `GSTClassicalHodgeNativeOperatorCohomologyRealization`.

A rational-linear native transport

    codimension-p cycles -> codimension-q cycles

has a well-defined action on cycle classes precisely when it sends the kernel
of the source cycle-class map into the kernel of the target cycle-class map.
Under that single congruence condition it descends to the actual source
cycle-class range.  Linear extension then produces an operator on the genuine
ambient rational singular cohomology groups in degrees `2p` and `2q`.

Thus the graded cycle-class naturality square is proved from native geometry;
it is not separately stored as data.
-/

set_option maxHeartbeats 30000000
set_option maxRecDepth 1000000

noncomputable section

open AlgebraicGeometry
open GSTProjectiveOverC
open GSTGeometricRealizationStage2D
open GSTGeometricRealizationStage2F
open GSTGeometricRealizationStage2G
open GSTClassicalHodgeCrossWeightNativePropagation

namespace GSTClassicalHodgeGradedNativeCohomologyRealization

variable {V : SmoothProjectiveComplexScheme}
variable {H : HodgeBigradedBettiData V}
variable {p q : Nat}

abbrev SourceCycles (V : SmoothProjectiveComplexScheme) (p : Nat) :=
  codimensionCycles V.X p
abbrev TargetCycles (V : SmoothProjectiveComplexScheme) (q : Nat) :=
  codimensionCycles V.X q
abbrev SourceCoh (H : HodgeBigradedBettiData V) (p : Nat) :=
  RationalSingularCohomology H.analytification (2 * p)
abbrev TargetCoh (H : HodgeBigradedBettiData V) (q : Nat) :=
  RationalSingularCohomology H.analytification (2 * q)

/-- A graded native operator respects source cycle-class equivalence. -/
def GradedKernelStable
    (A : SourceCycles V p →ₗ[ℚ] TargetCycles V q) : Prop :=
  ∀ Z : SourceCycles V p,
    H.cycleClass p Z = 0 → H.cycleClass q (A Z) = 0

/-- Equal source cycle classes have equal transformed target cycle classes. -/
theorem class_congr_of_gradedKernelStable
    (A : SourceCycles V p →ₗ[ℚ] TargetCycles V q)
    (hA : GradedKernelStable (H := H) A)
    {Z W : SourceCycles V p}
    (hZW : H.cycleClass p Z = H.cycleClass p W) :
    H.cycleClass q (A Z) = H.cycleClass q (A W) := by
  have hker : H.cycleClass p (Z - W) = 0 := by
    simp [hZW]
  have himage := hA (Z - W) hker
  simp only [map_sub] at himage
  exact sub_eq_zero.mp himage

/-- Chosen native representative of one source cycle class. -/
noncomputable def sourceRangeRepresentative
    (x : LinearMap.range (H.cycleClass p)) : SourceCycles V p :=
  Classical.choose x.2

@[simp]
theorem sourceRangeRepresentative_spec
    (x : LinearMap.range (H.cycleClass p)) :
    H.cycleClass p (sourceRangeRepresentative x) = x.1 :=
  Classical.choose_spec x.2

/-- Descend the graded native transport to the actual source cycle-class
range, landing in ambient target cohomology. -/
noncomputable def gradedRangeOperatorIntoAmbient
    (A : SourceCycles V p →ₗ[ℚ] TargetCycles V q)
    (hA : GradedKernelStable (H := H) A) :
    LinearMap.range (H.cycleClass p) →ₗ[ℚ] TargetCoh H q where
  toFun := fun x => H.cycleClass q (A (sourceRangeRepresentative x))
  map_add' := by
    intro x y
    have hrep :
        H.cycleClass p (sourceRangeRepresentative (x + y)) =
          H.cycleClass p
            (sourceRangeRepresentative x + sourceRangeRepresentative y) := by
      simp [sourceRangeRepresentative_spec]
    rw [class_congr_of_gradedKernelStable A hA hrep]
    simp
  map_smul' := by
    intro c x
    have hrep :
        H.cycleClass p (sourceRangeRepresentative (c • x)) =
          H.cycleClass p (c • sourceRangeRepresentative x) := by
      simp [sourceRangeRepresentative_spec]
    rw [class_congr_of_gradedKernelStable A hA hrep]
    simp

/-- Extend the descended graded action from the actual source cycle-class
range to the whole source rational singular cohomology group. -/
noncomputable def gradedAmbientOperator
    (A : SourceCycles V p →ₗ[ℚ] TargetCycles V q)
    (hA : GradedKernelStable (H := H) A) :
    SourceCoh H p →ₗ[ℚ] TargetCoh H q :=
  Classical.choose
    (LinearMap.exists_extend (gradedRangeOperatorIntoAmbient A hA))

/-- The chosen extension agrees with the descended native action on the actual
cycle-class range. -/
theorem gradedAmbientOperator_comp_rangeSubtype
    (A : SourceCycles V p →ₗ[ℚ] TargetCycles V q)
    (hA : GradedKernelStable (H := H) A) :
    (gradedAmbientOperator A hA).comp
        (LinearMap.range (H.cycleClass p)).subtype =
      gradedRangeOperatorIntoAmbient A hA :=
  Classical.choose_spec
    (LinearMap.exists_extend (gradedRangeOperatorIntoAmbient A hA))

/-- **AUTOMATIC GRADED CYCLE-CLASS NATURALITY.** -/
theorem cycleClass_gradedAmbientOperator
    (A : SourceCycles V p →ₗ[ℚ] TargetCycles V q)
    (hA : GradedKernelStable (H := H) A)
    (Z : SourceCycles V p) :
    gradedAmbientOperator A hA (H.cycleClass p Z) =
      H.cycleClass q (A Z) := by
  have hcomp := LinearMap.congr_fun
    (gradedAmbientOperator_comp_rangeSubtype A hA)
    ((H.cycleClass p).rangeRestrict Z)
  change
    gradedAmbientOperator A hA (H.cycleClass p Z) =
      gradedRangeOperatorIntoAmbient A hA
        ((H.cycleClass p).rangeRestrict Z) at hcomp
  rw [hcomp]
  apply class_congr_of_gradedKernelStable A hA
  exact sourceRangeRepresentative_spec _

/-- Every graded kernel-stable native cycle operator canonically produces the
complete graded cycle/cohomology operator pair used by the cross-weight
Lefschetz machinery. -/
noncomputable def toGradedCycleClassOperatorPair
    (A : SourceCycles V p →ₗ[ℚ] TargetCycles V q)
    (hA : GradedKernelStable (H := H) A) :
    GradedCycleClassOperatorPair V H p q where
  cycleOperator := A
  cohomologyOperator := gradedAmbientOperator A hA
  cycleClass_natural := by
    intro Z
    symm
    exact cycleClass_gradedAmbientOperator A hA Z

/-- A native graded transport therefore sends every actual source cycle class
to an actual target cycle class under its automatically generated Betti
operator. -/
theorem gradedAmbient_image_has_native_class
    (A : SourceCycles V p →ₗ[ℚ] TargetCycles V q)
    (hA : GradedKernelStable (H := H) A)
    (Z : SourceCycles V p) :
    ∃ W : TargetCycles V q,
      H.cycleClass q W =
        gradedAmbientOperator A hA (H.cycleClass p Z) := by
  exact ⟨A Z, (cycleClass_gradedAmbientOperator A hA Z).symm⟩

#check GradedKernelStable
#check class_congr_of_gradedKernelStable
#check gradedRangeOperatorIntoAmbient
#check gradedAmbientOperator
#check cycleClass_gradedAmbientOperator
#check toGradedCycleClassOperatorPair
#check gradedAmbient_image_has_native_class

#print axioms class_congr_of_gradedKernelStable
#print axioms gradedAmbientOperator_comp_rangeSubtype
#print axioms cycleClass_gradedAmbientOperator
#print axioms toGradedCycleClassOperatorPair
#print axioms gradedAmbient_image_has_native_class

end GSTClassicalHodgeGradedNativeCohomologyRealization
