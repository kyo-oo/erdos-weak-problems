import GSTClassicalHodgePolynomialTransitionClosure
import GSTClassicalHodgePointNormalForm

/-!
# GST CLASSICAL HODGE — NATIVE GENERATOR NATURALITY

The finite point-transition interface can be weakened further on compact
carriers — in particular on every smooth projective complex scheme.

To prove atomic stability of a rational cohomological observable T, it is
enough to show that for every genuine codimension-p point x, the transformed
class T(cl[x]) is the cycle class of some native codimension-p algebraic cycle.
Compactness then converts that native cycle automatically to a finite rational
point presentation.

Conversely, atomic stability itself supplies such a native witness because the
atomic span is contained in the full cycle-class range.

Hence on smooth projective carriers the following are equivalent:

* global invariance of the atomic cycle-class span;
* generatorwise finite point transitions;
* generatorwise native algebraic-cycle lifts.

This gives the operator attack both a geometric and a combinatorial interface.
-/

set_option maxHeartbeats 10000000
set_option maxRecDepth 1000000

noncomputable section

open AlgebraicGeometry
open GSTProjectiveOverC
open GSTGeometricRealizationStage2D
open GSTGeometricRealizationStage2F
open GSTGeometricRealizationStage2G
open GSTNativeCodimensionCyclePresentation
open GSTCompactNativeCyclePresentation
open GSTClassicalHodgeAtomicSpan
open GSTClassicalHodgeGeneratorwiseAtomicStability
open GSTClassicalHodgePointNormalForm

namespace GSTClassicalHodgeNativeGeneratorNaturality

universe u v

variable {X : Scheme.{u}}
variable {Coh : Type v} [AddCommGroup Coh] [Module ℚ Coh]
variable {p : Nat}
variable {cl : codimensionCycles X p →ₗ[ℚ] Coh}

/-- Generatorwise geometric naturality: each transformed genuine point class
is represented by some native codimension-p algebraic cycle. -/
def HasNativePointLifts (T : Coh →ₗ[ℚ] Coh) : Prop :=
  ∀ x : CodimensionPoint X p,
    ∃ Z : codimensionCycles X p,
      cl Z = T (cl (codimensionPointCycle X p x))

/-- Native point lifts are closed under rational scaling. -/
theorem HasNativePointLifts.smul
    (q : ℚ)
    (hT : HasNativePointLifts (p := p) (cl := cl) T) :
    HasNativePointLifts (p := p) (cl := cl) (q • T) := by
  intro x
  obtain ⟨Z, hZ⟩ := hT x
  refine ⟨q • Z, ?_⟩
  rw [map_smul, hZ, LinearMap.smul_apply]

/-- Atomic stability always yields native point lifts; compactness is not
needed in this direction because the atomic span is already contained in the
full cycle-class range. -/
theorem nativePointLifts_of_atomicSpanStable
    (T : Coh →ₗ[ℚ] Coh)
    (hT : AtomicSpanStable (p := p) (cl := cl) T) :
    HasNativePointLifts (p := p) (cl := cl) T := by
  intro x
  have hgen :
      cl (codimensionPointCycle X p x) ∈ pointCycleClassSpan p cl := by
    apply Submodule.subset_span
    exact ⟨x, rfl⟩
  have himage := hT _ hgen
  have hrange :
      T (cl (codimensionPointCycle X p x)) ∈ LinearMap.range cl :=
    pointCycleClassSpan_le_cycleClass_range p cl himage
  exact hrange

/-- On a compact carrier, a native point lift automatically becomes a finite
point transition by taking the canonical finite presentation of the witness
cycle. -/
theorem finitePointTransitions_of_nativePointLifts
    [CompactSpace X]
    (T : Coh →ₗ[ℚ] Coh)
    (hT : HasNativePointLifts (p := p) (cl := cl) T) :
    HasFinitePointTransitions (p := p) (cl := cl) T := by
  intro x
  rcases hT x with ⟨Z, hZ⟩
  let φ := presentationOfNativeCycle X p Z
  refine ⟨φ, ?_⟩
  rw [finitePointCycleClassMap_eq_cycleClass_realize]
  rw [realize_presentationOfNativeCycle X p Z]
  exact hZ

/-- **COMPACT NATIVE-LIFT NORMAL FORM.**  On a compact scheme, global atomic
stability is equivalent to native generatorwise algebraic lifts. -/
theorem atomicSpanStable_iff_nativePointLifts
    [CompactSpace X]
    (T : Coh →ₗ[ℚ] Coh) :
    AtomicSpanStable (p := p) (cl := cl) T ↔
      HasNativePointLifts (p := p) (cl := cl) T := by
  constructor
  · exact nativePointLifts_of_atomicSpanStable T
  · intro hnative
    apply (atomicSpanStable_iff_finitePointTransitions
      (p := p) (cl := cl) T).mpr
    exact finitePointTransitions_of_nativePointLifts T hnative

/-- Chosen native generator transition. -/
structure NativePointTransition
    (T : Coh →ₗ[ℚ] Coh) where
  imageCycle : CodimensionPoint X p → codimensionCycles X p
  imageCycle_spec : ∀ x,
    cl (imageCycle x) = T (cl (codimensionPointCycle X p x))

namespace NativePointTransition

/-- A chosen native transition gives the existential native-lift law. -/
theorem hasNativePointLifts
    {T : Coh →ₗ[ℚ] Coh}
    (K : NativePointTransition (p := p) (cl := cl) T) :
    HasNativePointLifts (p := p) (cl := cl) T := by
  intro x
  exact ⟨K.imageCycle x, K.imageCycle_spec x⟩

/-- On a compact carrier, convert a native transition into the canonical
finite point-transition kernel. -/
noncomputable def toPointClassTransitionKernel
    [CompactSpace X]
    {T : Coh →ₗ[ℚ] Coh}
    (K : NativePointTransition (p := p) (cl := cl) T) :
    PointClassTransitionKernel (p := p) (cl := cl) T where
  transition x := presentationOfNativeCycle X p (K.imageCycle x)
  transition_spec x := by
    rw [finitePointCycleClassMap_eq_cycleClass_realize]
    rw [realize_presentationOfNativeCycle X p (K.imageCycle x)]
    exact K.imageCycle_spec x

/-- Native point transitions therefore force global atomic stability on compact
carriers. -/
theorem atomicSpanStable
    [CompactSpace X]
    {T : Coh →ₗ[ℚ] Coh}
    (K : NativePointTransition (p := p) (cl := cl) T) :
    AtomicSpanStable (p := p) (cl := cl) T :=
  K.toPointClassTransitionKernel.atomicSpanStable

end NativePointTransition

/-! ## Smooth-projective classical specialization -/

variable {V : SmoothProjectiveComplexScheme}
variable {H : HodgeBigradedBettiData V}

/-- On every smooth projective complex carrier, atomic stability is exactly
native generatorwise naturality. -/
theorem smoothProjective_atomicStable_iff_nativePointLifts
    (T : RationalSingularCohomology H.analytification (2 * p) →ₗ[ℚ]
      RationalSingularCohomology H.analytification (2 * p)) :
    AtomicSpanStable (p := p) (cl := H.cycleClass p) T ↔
      HasNativePointLifts (p := p) (cl := H.cycleClass p) T := by
  letI : CompactSpace V.X := smoothProjectiveCompactSpace V
  exact atomicSpanStable_iff_nativePointLifts T

#check HasNativePointLifts
#check nativePointLifts_of_atomicSpanStable
#check finitePointTransitions_of_nativePointLifts
#check atomicSpanStable_iff_nativePointLifts
#check NativePointTransition
#check NativePointTransition.toPointClassTransitionKernel
#check NativePointTransition.atomicSpanStable
#check smoothProjective_atomicStable_iff_nativePointLifts

#print axioms nativePointLifts_of_atomicSpanStable
#print axioms finitePointTransitions_of_nativePointLifts
#print axioms atomicSpanStable_iff_nativePointLifts
#print axioms NativePointTransition.toPointClassTransitionKernel
#print axioms NativePointTransition.atomicSpanStable
#print axioms smoothProjective_atomicStable_iff_nativePointLifts

end GSTClassicalHodgeNativeGeneratorNaturality
