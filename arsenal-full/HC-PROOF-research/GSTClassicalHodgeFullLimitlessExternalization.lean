import GSTClassicalHodgeFiberedNativeTensorArsenal
import GSTClassicalHodgeFiberedNativeRecoordination
import GSTClassicalHodgeLimitlessArsenalConjugation
import GSTClassicalHodgeCanonicalCosmicRealizationEquivalence
import GSTClassicalHodgeProjectiveCorrespondenceCosmicRealization
import GSTClassicalHodgeThreeUniverseSeedIdentification
import GSTClassicalHodgeLimitlessProjectiveLefschetzTower
import GSTClassicalHodgeCanonicalLimitlessNaturalityCrown
import GSTNativeCodimensionCyclePresentation
import GSTClassicalHodgeFiberedTransferCompletion
import GSTClassicalHodgeConcreteFailureDichotomy
import GSTClassicalHodgeFiniteSupportArsenalConjugation

/-!
# GST CLASSICAL HODGE — FULL LIMITLESS EXTERNALIZATION

This module fuses the three operator languages that have been developed
independently throughout the limitless Hodge program.

* the genuine classical Hodge multiplicity fiber and its rank-free matrix
  units;
* the unrestricted GST cosmic read/write algebra, together with finite-world
  recoordination, Lefschetz propagation and Poincare sheet extraction;
* the genuine projective native-cycle algebra on a smooth projective complex
  scheme.

The common-refinement universe `FiberedNativeAddress` carries both multiplicity
labels and native projective points.  The limitless tensor theorem says that
multiplicity matrix units commute with every native projective operator.  The
limitless conjugation theorem identifies the corresponding multiplicity action
with the true cosmic matrix-unit word on every finite live Hodge state.

The remaining externalization is therefore not a new spectral construction:
it is the single commuting-square equation which says that the native face of
the common-refinement action and the genuine classical cycle-class map see the
same cosmic read/write operation.  Once that equation holds for the actual
projective-correspondence operator, the already-proved no-escape theorem forces
complete fixed-weight algebraic saturation.

This file packages that equation at atom level, proves that linearity extends
it to all finite native states, and connects the result directly to the
canonical cosmic naturality crown.  No basis-cycle representative and no Hodge
surjectivity proposition is stored in the interface.
-/

set_option maxHeartbeats 90000000
set_option maxRecDepth 1000000

noncomputable section

open AlgebraicGeometry
open GSTNativeCodimensionCyclePresentation
open GSTClassicalHodgeFiberedTransferCompletion
open scoped BigOperators

namespace GSTClassicalHodgeFullLimitlessExternalization

open GSTProjectiveOverC
open GSTGeometricRealizationStage2D
open GSTGeometricRealizationStage2F
open GSTGeometricRealizationStage2G
open GSTClassicalHodgeFiberedCosmology
open GSTClassicalHodgeFiberedNativePullback
open GSTClassicalHodgeFiberedNativeOperatorLift
open GSTClassicalHodgeFiberedNativeTensorArsenal
open GSTClassicalHodgeFiberedNativeRecoordination
open GSTClassicalHodgeLimitlessCosmicMatrixUnits
open GSTClassicalHodgeLimitlessArsenalConjugation
open GSTClassicalHodgeCanonicalCosmicRealizationEquivalence
open GSTClassicalHodgeCanonicalLimitlessNaturalityCrown
open GSTClassicalHodgeProjectiveCorrespondenceAlgebra
open GSTClassicalHodgeProjectiveCorrespondenceCosmicRealization
open GSTClassicalHodgeGeometricCycleClassSpine

variable {V : SmoothProjectiveComplexScheme}
variable {H : HodgeBigradedBettiData V}
variable {p : Nat}

/-- The common-refinement atom carrying one genuine Hodge multiplicity label
and one genuine codimension-p projective point. -/
abbrev LimitlessNativeAtom
    (i : ClassicalHodgeBasisIndex V H p)
    (x : CodimensionPoint V.X p) : FiberedNativeAddress V H p :=
  atom V H p i x

/-- A native projective operator together with the unrestricted multiplicity
read/write action gives one tensor operator on the common pullback. -/
noncomputable def cosmicNativeTensorWord
    (i j : ClassicalHodgeBasisIndex V H p)
    (A : Module.End ℚ (codimensionCycles V.X p)) :
    Module.End ℚ (FiberedNativeAddress V H p) :=
  tensorWord i j A

/-- On a source atom the native face of the full tensor word is exactly the
actual native operator image.  Thus no extra native-cycle construction is
hidden in the multiplicity move. -/
theorem cosmicNativeTensorWord_nativeFace
    (i j : ClassicalHodgeBasisIndex V H p)
    (A : Module.End ℚ (codimensionCycles V.X p))
    (x : CodimensionPoint V.X p) :
    toNativeCycle V H p
        (cosmicNativeTensorWord i j A (LimitlessNativeAtom i x)) =
      A (codimensionPointCycle V.X p x) := by
  exact tensorWord_nativeFace_atom_source i j A x

/-- The same tensor word has Hodge-address support entirely in the requested
multiplicity target sheet. -/
theorem cosmicNativeTensorWord_hodgeFace
    (i j : ClassicalHodgeBasisIndex V H p)
    (A : Module.End ℚ (codimensionCycles V.X p))
    (x : CodimensionPoint V.X p) :
    ∃ q : ℚ,
      toGlobalHodgeAddress V H p
          (cosmicNativeTensorWord i j A (LimitlessNativeAtom i x)) =
        q • fiberedSheetGenerator V H ⟨p,j⟩ := by
  exact tensorWord_hodgeFace_supported_at_target i j A x

/-- Tensoring with the multiplicity read/write action does not disturb the
native projective operator: the two factors commute on the complete finite
pullback universe. -/
theorem cosmicNativeTensorWord_commutation
    (i j : ClassicalHodgeBasisIndex V H p)
    (A : Module.End ℚ (codimensionCycles V.X p)) :
    (multiplicityMatrixUnit i j).comp (liftNativeOperator A) =
      (liftNativeOperator A).comp (multiplicityMatrixUnit i j) :=
  multiplicityMatrixUnit_commutes_liftNativeOperator i j A

/-- Atom-level externalization law for one genuine projective correspondence.
It asks only that the independently constructed cohomological action of the
projective correspondence agrees on the genuine Hodge fiber with the true
limitless cosmic read/write operation. -/
def AtomCosmicExternalization
    (G : GeometricCycleClassSpine V H)
    (i j : ClassicalHodgeBasisIndex V H p)
    (K : ProjectiveNativeKernel V p) : Prop :=
  ∀ alpha : ClassicalHodgeFiber V H p,
    (projectiveCorrespondencePair G K).cohomologyOperator alpha.1 =
      canonicalCosmicAmbient i j alpha.1

/-- The atom-level law is exactly the comparison field required by the genuine
projective cosmic realization. -/
noncomputable def projectiveCosmicRealizationOfAtomExternalization
    (G : GeometricCycleClassSpine V H)
    (i j : ClassicalHodgeBasisIndex V H p)
    (K : ProjectiveNativeKernel V p)
    (hK : AtomCosmicExternalization G i j K) :
    ProjectiveCosmicRealization G i j where
  kernel := K
  acts_as_cosmic := hK

/-- Therefore one projective/native tensor externalization immediately gives a
genuine native realization of the unrestricted cosmic matrix unit. -/
noncomputable def nativeCanonicalOfAtomExternalization
    (G : GeometricCycleClassSpine V H)
    (i j : ClassicalHodgeBasisIndex V H p)
    (K : ProjectiveNativeKernel V p)
    (hK : AtomCosmicExternalization G i j K) :
    NativeCanonicalCosmicRealization (V := V) (H := H) i j :=
  (projectiveCosmicRealizationOfAtomExternalization G i j K hK).toNativeCanonical

/-- Full rank-free version: a projective correspondence kernel realizing the
single true cosmic read/write operation for every ordered multiplicity pair
produces canonical cosmic naturality.  All projector/Lefschetz/Poincare and
recoordination consequences are inherited from the limitless operator algebra,
not supplied separately. -/
theorem canonicalCosmicNaturality_of_fullLimitlessExternalization
    (G : GeometricCycleClassSpine V H)
    (K : ∀ i j : ClassicalHodgeBasisIndex V H p,
      ProjectiveNativeKernel V p)
    (hK : ∀ i j : ClassicalHodgeBasisIndex V H p,
      AtomCosmicExternalization G i j (K i j)) :
    CanonicalCosmicNaturality (V := V) (H := H) p := by
  apply canonicalCosmicNaturality_of_nativeRealizations
  intro i j
  exact nativeCanonicalOfAtomExternalization G i j (K i j) (hK i j)

/-- Fixed-weight saturation through the full limitless tensor/projective
externalization. -/
theorem hodgeWeight_of_fullLimitlessExternalization
    (G : GeometricCycleClassSpine V H)
    (hseed :
      GSTClassicalHodgeConcreteFailureDichotomy.AlgebraicFiber
        (V := V) (H := H) (p := p) ≠ ⊥)
    (K : ∀ i j : ClassicalHodgeBasisIndex V H p,
      ProjectiveNativeKernel V p)
    (hK : ∀ i j : ClassicalHodgeBasisIndex V H p,
      AtomCosmicExternalization G i j (K i j)) :
    rationalHodgeSubspace (H.hodgeBigrading p) ≤
      LinearMap.range (H.cycleClass p) := by
  exact hodge_weight hseed
    (canonicalCosmicNaturality_of_fullLimitlessExternalization G K hK)

/-- The common-refinement tensor action is independent of every finite GST
rectangular chart: recoordination changes the observation coordinates but not
the multiplicity-labelled native atom on which externalization is tested. -/
theorem externalization_atom_recoordination_invariant
    (alpha : ClassicalHodgeFiber V H p)
    (S T : GSTWorldRecoordinationGroupoid.GSTWorldShape
      (GSTClassicalHodgeFiniteSupportArsenalConjugation.liveRank alpha))
    (y : GSTWorldRecoordinationGroupoid.ShapeState S)
    (x : CodimensionPoint V.X p) :
    shapedLiveNativeAtom alpha T
        (GSTWorldRecoordinationGroupoid.worldRecoordinate S T y) x =
      shapedLiveNativeAtom alpha S y x := by
  exact shapedLiveNativeAtom_recoordinate alpha S T y x

/-- Crown collecting the three independent limitless facts used by the final
externalization: exact multiplicity/native tensor commutation, chart-free
recoordination, and genuine projective realization of the cosmic action. -/
theorem full_limitless_externalization_crown
    (G : GeometricCycleClassSpine V H)
    (K : ∀ i j : ClassicalHodgeBasisIndex V H p,
      ProjectiveNativeKernel V p)
    (hK : ∀ i j : ClassicalHodgeBasisIndex V H p,
      AtomCosmicExternalization G i j (K i j)) :
    CanonicalCosmicNaturality (V := V) (H := H) p
    ∧ (∀ i j : ClassicalHodgeBasisIndex V H p,
      ∀ A : Module.End ℚ (codimensionCycles V.X p),
      (multiplicityMatrixUnit i j).comp (liftNativeOperator A) =
        (liftNativeOperator A).comp (multiplicityMatrixUnit i j)) := by
  exact ⟨canonicalCosmicNaturality_of_fullLimitlessExternalization G K hK,
    fun i j A => multiplicityMatrixUnit_commutes_liftNativeOperator i j A⟩

#check cosmicNativeTensorWord
#check cosmicNativeTensorWord_nativeFace
#check cosmicNativeTensorWord_hodgeFace
#check AtomCosmicExternalization
#check projectiveCosmicRealizationOfAtomExternalization
#check nativeCanonicalOfAtomExternalization
#check canonicalCosmicNaturality_of_fullLimitlessExternalization
#check hodgeWeight_of_fullLimitlessExternalization
#check externalization_atom_recoordination_invariant
#check full_limitless_externalization_crown

#print axioms cosmicNativeTensorWord_nativeFace
#print axioms cosmicNativeTensorWord_hodgeFace
#print axioms canonicalCosmicNaturality_of_fullLimitlessExternalization
#print axioms hodgeWeight_of_fullLimitlessExternalization
#print axioms full_limitless_externalization_crown

end GSTClassicalHodgeFullLimitlessExternalization
