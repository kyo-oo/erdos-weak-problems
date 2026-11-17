import GSTClassicalHodgeGeometricCycleClassSpine
import GSTClassicalHodgeGradedNativeCohomologyRealization
import GSTClassicalHodgeNativeOperatorCohomologyRealization
import GSTClassicalHodgePointNormalForm

/-!
# GST CLASSICAL HODGE — GEOMETRIC SPINE KERNEL REDUCTION

The geometric spine should not store full ambient operator pairs whenever those
pairs are forced by native geometry.

For a native operator, the precise obstruction to a well-defined cohomological
action is kernel preservation with respect to the genuine cycle-class map.
The repository already constructs the ambient action and commuting square from
that condition.  This file turns that observation into exact iff theorems and
then builds a reduced spine constructor.

Consequences:

* primitive projective pushforward naturality exists iff the genuine native
  pushforward preserves the cycle-class kernel;
* a principal-cut graded operator pair with the already-constructed native
  successor exists iff that successor preserves the graded cycle-class kernel;
* the full `GeometricCycleClassSpine` can therefore be manufactured from
  algebraic-Hodge typing, kernel laws, and Hodge preservation of the canonical
  generated principal-cut action.

Thus the commuting squares and the native-operator identities are theorems,
not independent axioms.
-/

set_option maxHeartbeats 120000000
set_option maxRecDepth 1000000

noncomputable section

open CategoryTheory
open AlgebraicGeometry

namespace GSTClassicalHodgeGeometricSpineKernelReduction

open GSTProjectiveOverC
open GSTGeometricRealizationStage2D
open GSTGeometricRealizationStage2F
open GSTGeometricRealizationStage2G
open GSTClassicalHodgePrimitivePushforwardNaturality
open GSTClassicalHodgeProjectivePointTransport
open GSTClassicalHodgePrincipalCutSuccessorOperator
open GSTClassicalHodgeCrossWeightNativePropagation
open GSTClassicalHodgeNativeOperatorCohomologyRealization
open GSTClassicalHodgeGradedNativeCohomologyRealization
open GSTClassicalHodgeGeometricCycleClassSpine
open GSTNativeCodimensionCyclePresentation
open GSTCompactNativeCyclePresentation
open GSTClassicalHodgePointNormalForm

variable {V : SmoothProjectiveComplexScheme}
variable {H : HodgeBigradedBettiData V}

/-!
## Geometry-first finite-relation descent

The native point normal form exposes the exact obstruction to a projective
pushforward acting on algebraic Betti classes.  Rather than *inputting* a
cohomology endomorphism, we ask whether every finite rational relation among
actual point classes survives the residue-weighted point transport.
-/

/-- Every transported native cycle, evaluated through any supplied cycle-class
map, has a completely explicit finite point formula.  No cohomological
pushforward or Hodge surjectivity is assumed. -/
theorem nativePushforward_class_finitePointFormula
    (p : Nat) (f : V.X ⟶ V.X)
    (φ : FiniteCodimensionPresentation V.X p) :
    H.cycleClass p
        (smoothProjectiveNativePushforward V f p
          (realizeFiniteCodimensionPresentation V.X p φ)) =
      φ.sum (fun x q =>
        q • H.cycleClass p (nativePointPushforward f p x)) := by
  let F :
      codimensionCycles V.X p →ₗ[ℚ]
        RationalSingularCohomology H.analytification (2 * p) :=
    (H.cycleClass p).comp (smoothProjectiveNativePushforward V f p)
  have h := linearMap_realizeFiniteCodimensionPresentation V.X p F φ
  simpa only [F, LinearMap.comp_apply,
    smoothProjectiveNativePushforward_point] using h

/-- Concrete geometry-first constraint: finite relations among actual
codimension-p point fundamental classes remain relations when the genuine
scheme map transports those points with their residue-degree coefficients. -/
def FinitePointClassRelationsPreserved
    (p : Nat) (f : V.X ⟶ V.X) : Prop :=
  ∀ φ : FiniteCodimensionPresentation V.X p,
    (φ.sum (fun x q =>
      q • H.cycleClass p (codimensionPointCycle V.X p x)) = 0) →
    φ.sum (fun x q =>
      q • H.cycleClass p (nativePointPushforward f p x)) = 0

/-- **EXACT POINT-RELATION DESCENT LAW.**  A genuine scheme pushforward has a
well-defined action on the algebraic class range exactly when it respects
all finite linear relations among genuine point-cycle classes.  The criterion
requires neither an arbitrary ambient cohomology map nor any target-cycle
witness, and it makes the obstruction geometrically explicit. -/
theorem finitePointRelationsPreserved_iff_kernelStable
    (p : Nat) (f : V.X ⟶ V.X) :
    FinitePointClassRelationsPreserved (H := H) p f ↔
      KernelStable (H := H) (smoothProjectiveNativePushforward V f p) := by
  letI : CompactSpace V.X := smoothProjectiveCompactSpace V
  constructor
  · intro hrelations Z hZ
    let φ := presentationOfNativeCycle V.X p Z
    have hsource :
        φ.sum (fun x q =>
          q • H.cycleClass p (codimensionPointCycle V.X p x)) =
          H.cycleClass p Z := by
      calc
        _ = H.cycleClass p
              (realizeFiniteCodimensionPresentation V.X p φ) :=
          (linearMap_realizeFiniteCodimensionPresentation
            V.X p (H.cycleClass p) φ).symm
        _ = H.cycleClass p Z := by
          simp only [φ, realize_presentationOfNativeCycle]
    have htarget :
        H.cycleClass p (smoothProjectiveNativePushforward V f p Z) =
          φ.sum (fun x q =>
            q • H.cycleClass p (nativePointPushforward f p x)) := by
      calc
        _ = H.cycleClass p
              (smoothProjectiveNativePushforward V f p
                (realizeFiniteCodimensionPresentation V.X p φ)) := by
          simp only [φ, realize_presentationOfNativeCycle]
        _ = _ := nativePushforward_class_finitePointFormula
          (H := H) p f φ
    rw [htarget]
    exact hrelations φ (hsource.trans hZ)
  · intro hkernel φ hrelation
    have hsource :
        H.cycleClass p
          (realizeFiniteCodimensionPresentation V.X p φ) = 0 := by
      rw [linearMap_realizeFiniteCodimensionPresentation]
      exact hrelation
    have htarget := hkernel
      (realizeFiniteCodimensionPresentation V.X p φ) hsource
    rw [nativePushforward_class_finitePointFormula
      (H := H) p f φ] at htarget
    exact htarget


/-- **PRIMITIVE PUSHFORWARD UNIVERSAL PROPERTY.**
A genuine projective native pushforward admits a cohomological naturality square
iff it preserves the kernel of cycle class. -/
theorem geometricPushforwardNaturality_nonempty_iff_kernelStable
    (p : Nat)
    (f : V.X ⟶ V.X) :
    Nonempty (GeometricPushforwardNaturality V H p f) ↔
      KernelStable (H := H) (smoothProjectiveNativePushforward V f p) := by
  constructor
  · rintro ⟨N⟩
    exact N.kernelStable
  · intro hK
    refine ⟨{
      cohomologyPushforward :=
        ambientOperator (smoothProjectiveNativePushforward V f p) hK
      naturality := ?_
    }⟩
    intro Z
    exact (cycleClass_ambientOperator
      (smoothProjectiveNativePushforward V f p) hK Z).symm


/-- The existence of a cohomology action for a genuine scheme pushforward
is equivalent to preservation of all finite geometric point relations,
without supplying the action as an independent premise. -/
theorem geometricPushforwardNaturality_nonempty_iff_finitePointRelations
    (p : Nat) (f : V.X ⟶ V.X) :
    Nonempty (GeometricPushforwardNaturality V H p f) ↔
      FinitePointClassRelationsPreserved (H := H) p f := by
  exact (geometricPushforwardNaturality_nonempty_iff_kernelStable
    (H := H) p f).trans
      (finitePointRelationsPreserved_iff_kernelStable
        (H := H) p f).symm

/-- Any graded cycle-class operator pair whose native side is the actual
principal-cut successor necessarily forces graded kernel stability of that
successor. -/
theorem principalCut_kernelStable_of_pair
    (p : Nat)
    (T : GradedCycleClassOperatorPair V H p (p + 1))
    (hNative : T.cycleOperator = successorNativeOperator V p) :
    GradedKernelStable (H := H) (successorNativeOperator V p) := by
  intro Z hZ
  have hnat := T.cycleClass_natural Z
  rw [hNative] at hnat
  rw [hZ] at hnat
  simpa using hnat

/-- Conversely graded kernel stability manufactures the complete principal-cut
operator pair with the correct native side. -/
noncomputable def principalCutPairOfKernelStable
    (p : Nat)
    (hK : GradedKernelStable (H := H) (successorNativeOperator V p)) :
    GradedCycleClassOperatorPair V H p (p + 1) :=
  toGradedCycleClassOperatorPair (successorNativeOperator V p) hK

@[simp]
theorem principalCutPairOfKernelStable_native
    (p : Nat)
    (hK : GradedKernelStable (H := H) (successorNativeOperator V p)) :
    (principalCutPairOfKernelStable p hK).cycleOperator =
      successorNativeOperator V p := by
  rfl

/-- **PRINCIPAL-CUT UNIVERSAL PROPERTY.**
The actual native principal-cut successor admits some exact graded
cycle/cohomology pair with that native action iff it is graded-kernel-stable. -/
theorem principalCutPair_nonempty_iff_kernelStable
    (p : Nat) :
    (∃ T : GradedCycleClassOperatorPair V H p (p + 1),
      T.cycleOperator = successorNativeOperator V p) ↔
      GradedKernelStable (H := H) (successorNativeOperator V p) := by
  constructor
  · rintro ⟨T, hT⟩
    exact principalCut_kernelStable_of_pair p T hT
  · intro hK
    exact ⟨principalCutPairOfKernelStable p hK, rfl⟩

/-- Canonical kernel-level principal-cut realization.  Its ambient operator is
not supplied independently: it is generated from the native successor. -/
structure PrincipalCutKernelRealization where
  kernelStable :
    ∀ p : Nat,
      GradedKernelStable (H := H) (successorNativeOperator V p)
  hodge :
    ∀ p : Nat,
    ∀ alpha : RationalSingularCohomology H.analytification (2 * p),
      alpha ∈ rationalHodgeSubspace (H.hodgeBigrading p) →
      gradedAmbientOperator
          (successorNativeOperator V p)
          (kernelStable p) alpha ∈
        rationalHodgeSubspace (H.hodgeBigrading (p + 1))

namespace PrincipalCutKernelRealization

/-- The full graded pair is derived, not stored. -/
noncomputable def pair
    (R : PrincipalCutKernelRealization (V := V) (H := H))
    (p : Nat) :
    GradedCycleClassOperatorPair V H p (p + 1) :=
  principalCutPairOfKernelStable p (R.kernelStable p)

@[simp]
theorem pair_native
    (R : PrincipalCutKernelRealization (V := V) (H := H))
    (p : Nat) :
    (R.pair p).cycleOperator = successorNativeOperator V p := by
  rfl

/-- Exact cycle-class naturality of the canonical principal-cut action. -/
theorem pair_naturality
    (R : PrincipalCutKernelRealization (V := V) (H := H))
    (p : Nat)
    (Z : codimensionCycles V.X p) :
    H.cycleClass (p + 1) (successorNativeOperator V p Z) =
      (R.pair p).cohomologyOperator (H.cycleClass p Z) := by
  exact (R.pair p).cycleClass_natural Z

end PrincipalCutKernelRealization

/-- A reduced genuine cycle-class spine.  It stores only the semantic facts
that are not automatically generated by the native-operator descent machinery.
In particular no pushforward cohomology operator, no principal-cut operator
pair, and no native-side identity are fields. -/
structure KernelReducedGeometricCycleClassSpine where
  algebraic_is_hodge :
    ∀ p : Nat, ∀ Z : codimensionCycles V.X p,
      H.cycleClass p Z ∈ rationalHodgeSubspace (H.hodgeBigrading p)
  pushforward_kernelStable :
    ∀ p : Nat, ∀ f : V.X ⟶ V.X,
      KernelStable (H := H) (smoothProjectiveNativePushforward V f p)
  principalCut : PrincipalCutKernelRealization (V := V) (H := H)

namespace KernelReducedGeometricCycleClassSpine

/-- Manufacture the original full geometric spine from the reduced kernel
semantics.  All operator pairs and commuting squares are generated theorems. -/
noncomputable def toGeometricCycleClassSpine
    (R : KernelReducedGeometricCycleClassSpine (V := V) (H := H)) :
    GeometricCycleClassSpine V H where
  algebraic_is_hodge := R.algebraic_is_hodge
  pushforward_naturality := by
    intro p f
    let hK := R.pushforward_kernelStable p f
    exact {
      cohomologyPushforward :=
        ambientOperator (smoothProjectiveNativePushforward V f p) hK
      naturality := by
        intro Z
        exact (cycleClass_ambientOperator
          (smoothProjectiveNativePushforward V f p) hK Z).symm
    }
  principalCutPair := fun p => R.principalCut.pair p
  principalCutPair_native := by
    intro p
    rfl
  principalCut_hodge := by
    intro p alpha halpha
    exact R.principalCut.hodge p alpha halpha

/-- The reduced spine therefore exports all the old geometric consequences
without re-assuming their operator-pair packaging. -/
theorem principalCut_maps_algebraic_hodge
    (R : KernelReducedGeometricCycleClassSpine (V := V) (H := H))
    (p : Nat)
    (alpha : GSTClassicalHodgeFiberedCosmology.ClassicalHodgeFiber V H p)
    (halg : alpha ∈
      GSTClassicalHodgeRankFreeArsenalIrreducibility.AlgebraicHodgeSubspace V H p) :
    (⟨((R.toGeometricCycleClassSpine.principalCutPair p).cohomologyOperator alpha.1),
        R.toGeometricCycleClassSpine.principalCut_hodge p alpha.1 alpha.2⟩ :
      GSTClassicalHodgeFiberedCosmology.ClassicalHodgeFiber V H (p + 1)) ∈
      GSTClassicalHodgeRankFreeArsenalIrreducibility.AlgebraicHodgeSubspace
        V H (p + 1) := by
  exact R.toGeometricCycleClassSpine.principalCut_maps_algebraic_hodge
    p alpha halg

end KernelReducedGeometricCycleClassSpine

#check geometricPushforwardNaturality_nonempty_iff_kernelStable
#check principalCut_kernelStable_of_pair
#check principalCutPairOfKernelStable
#check principalCutPair_nonempty_iff_kernelStable
#check PrincipalCutKernelRealization
#check PrincipalCutKernelRealization.pair
#check KernelReducedGeometricCycleClassSpine
#check KernelReducedGeometricCycleClassSpine.toGeometricCycleClassSpine

#print axioms geometricPushforwardNaturality_nonempty_iff_kernelStable
#print axioms principalCutPair_nonempty_iff_kernelStable
#print axioms PrincipalCutKernelRealization.pair_naturality
#print axioms KernelReducedGeometricCycleClassSpine.toGeometricCycleClassSpine

end GSTClassicalHodgeGeometricSpineKernelReduction
