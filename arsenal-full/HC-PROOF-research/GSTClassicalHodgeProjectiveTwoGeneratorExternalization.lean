import GSTClassicalHodgePrimitivePushforwardNaturality
import GSTClassicalHodgeGeometryFirstTwoGenerator
import GSTClassicalHodgeExplicitArsenalGeneration
import GSTClassicalHodgeLimitlessTowerOrbitCrown
import GSTClassicalHodgeLimitlessSpinePropagation
import GSTClassicalHodgeProjectiveSelfCorrespondences
import GSTClassicalHodgeTwoGeneratorNativeArsenal
import GSTClassicalHodgeUniversalTwoSlotNativeClosure
import GSTClassicalHodgeRankFreeArsenalIrreducibility

/-!
# GST CLASSICAL HODGE — PROJECTIVE TWO-GENERATOR EXTERNALIZATION

The rank-free GST Hodge engine needs only two noncommuting primitive actions in
one ordered two-slot sector: the code observable and the two-step Lefschetz
operator.  This module removes arbitrary native operators from that interface.

A primitive is now realized by an actual algebraic endomorphism of the smooth
projective carrier.  Its native action is the genuine pushforward on algebraic
cycles.  The standard cycle-class functoriality square supplies kernel
stability automatically, and the induced ambient action is required only to
restrict to the corresponding GST primitive on the genuine Hodge fiber.

From those two actual projective transports we construct
`GeometryFirstTwoGenerator`, so all projector, Lefschetz, Poincare,
recoordination, polynomial and rank-free matrix-unit consequences already
proved in the limitless universe become available without another operator
hypothesis.

The strongest route below does not ask for projective generators for every
ordered basis pair.  The canonical nonzero spine seed selects one live source
coordinate in each weight.  Synchronized-defect orbit extraction then needs
only source-to-target words from that single source.  The native-mass bridge
can manufacture the conserved charge itself, leaving only the point/native
mass geometry and these source-to-target projective primitives.
-/

set_option maxHeartbeats 70000000
set_option maxRecDepth 1000000

noncomputable section

open CategoryTheory
open GSTClassicalHodgeTwoGeneratorNativeArsenal
open GSTClassicalHodgeUniversalTwoSlotNativeClosure
open GSTClassicalHodgeRankFreeArsenalIrreducibility
open GSTClassicalHodgeExplicitArsenalGeneration
open AlgebraicGeometry

namespace GSTClassicalHodgeProjectiveTwoGeneratorExternalization

open GSTProjectiveOverC
open GSTGeometricRealizationStage2F
open GSTGeometricRealizationStage2G
open GSTClassicalHodgeFiberedCosmology
open GSTClassicalHodgeNativeOperatorCohomologyRealization
open GSTClassicalHodgePrimitivePushforwardNaturality
open GSTClassicalHodgeProjectivePointTransport
open GSTClassicalHodgeGeometryFirstTwoGenerator
open GSTClassicalHodgeRankFreePrimitiveGeneration
open GSTClassicalHodgeLimitlessTowerOrbitCrown
open GSTClassicalHodgeLimitlessSpinePropagation
open GSTClassicalHodgeGeometricCycleClassSpine
open GSTClassicalHodgeSynchronizedDefectOrbit

variable {V : SmoothProjectiveComplexScheme}
variable {H : HodgeBigradedBettiData V}
variable {p : Nat}

/-- An actual projective endomorphism realizing one prescribed Hodge-fiber
operator.  Its genuine Betti action is obtained from geometric functoriality,
not by projecting arbitrary Betti classes onto the algebraic cycle-class range.
Only the restriction of that actual action to the Hodge fiber is compared
with the requested GST primitive. -/
structure ProjectivePrimitiveRealization
    (T : Module.End ℚ (ClassicalHodgeFiber V H p)) where
  map : V.X ⟶ V.X
  naturality : GeometricPushforwardNaturality V H p map
  restricts_to_hodge :
    ∀ alpha : ClassicalHodgeFiber V H p,
      naturality.cohomologyPushforward alpha.1 = (T alpha).1

namespace ProjectivePrimitiveRealization

/-- Genuine native-cycle/cohomology primitive from a projective endomorphism.
The commuting square follows from actual geometric naturality. -/
noncomputable def toNativeHodgePrimitive
    {T : Module.End ℚ (ClassicalHodgeFiber V H p)}
    (R : ProjectivePrimitiveRealization (V := V) (H := H) T) :
    NativeHodgePrimitive (V := V) (H := H) T where
  cycleOperator := smoothProjectiveNativePushforward V R.map p
  cohomologyOperator := R.naturality.cohomologyPushforward
  cycleClass_natural := R.naturality.naturality
  restricts_to_hodge := R.restricts_to_hodge

/-- The geometric cohomology action is exactly the primitive's ambient action.
No assertion that a geometric map kills transcendental cohomology is needed. -/
theorem ambient_eq_geometric
    {T : Module.End ℚ (ClassicalHodgeFiber V H p)}
    (R : ProjectivePrimitiveRealization (V := V) (H := H) T) :
    (R.toNativeHodgePrimitive).ambient =
      R.naturality.cohomologyPushforward := by
  rfl

end ProjectivePrimitiveRealization

/-- Exactly two genuine projective primitives for one ordered Hodge-basis pair. -/
structure ProjectiveTwoGenerator
    (i j : ClassicalHodgeBasisIndex V H p) where
  code : ProjectivePrimitiveRealization
    (V := V) (H := H) (twoSlotCodeHodge i j)
  lefschetz : ProjectivePrimitiveRealization
    (V := V) (H := H)
    (twoSlotHodgeOperator i j (diagonalLefschetzQ 2 2))

namespace ProjectiveTwoGenerator

/-- Projective two-generator data instantiate the already-proved
geometry-first two-generator GST machine. -/
noncomputable def toGeometryFirst
    {i j : ClassicalHodgeBasisIndex V H p}
    (R : ProjectiveTwoGenerator (V := V) (H := H) i j) :
    GeometryFirstTwoGenerator (V := V) (H := H) i j where
  code := R.code.toNativeHodgePrimitive
  lefschetz := R.lefschetz.toNativeHodgePrimitive

/-- Therefore the normalized finite GST word built from the two actual
projective maps acts as the rank-one matrix unit `i -> j` on every genuine
Hodge state. -/
theorem normalized_word_on_hodge
    {i j : ClassicalHodgeBasisIndex V H p}
    (R : ProjectiveTwoGenerator (V := V) (H := H) i j)
    (hij : i ≠ j)
    (alpha : ClassicalHodgeFiber V H p) :
    (R.toGeometryFirst).ambientWord alpha.1 =
      (GSTClassicalHodgeRankFreeArsenalIrreducibility.hodgeMatrixUnit i j alpha).1 :=
  (R.toGeometryFirst).ambientWord_on_hodge hij alpha

end ProjectiveTwoGenerator

/-- A projective realization of the two primitive generators for every target
of the selected live source automatically provides the fixed-weight input to
the limitless synchronized orbit theorem. -/
noncomputable def projectiveTargetFamily_to_geometryFirst
    (S : NativeHodgeOrbitSeed (V := V) (H := H) (p := p))
    (R : ∀ j : ClassicalHodgeBasisIndex V H p,
      ProjectiveTwoGenerator (V := V) (H := H) S.sourceIndex j) :
    ∀ j : ClassicalHodgeBasisIndex V H p,
      GeometryFirstTwoGenerator
        (V := V) (H := H) S.sourceIndex j :=
  fun j => (R j).toGeometryFirst

/-- Weight-wise projective externalization crown. -/
theorem hodge_weight_of_projective_two_generators
    (S : NativeHodgeOrbitSeed (V := V) (H := H) (p := p))
    (R : ∀ j : ClassicalHodgeBasisIndex V H p,
      ProjectiveTwoGenerator (V := V) (H := H) S.sourceIndex j) :
    rationalHodgeSubspace (H.hodgeBigrading p) ≤
      LinearMap.range (H.cycleClass p) :=
  S.hodge_weight (projectiveTargetFamily_to_geometryFirst S R)

/-- **PROJECTIVE + LIMITLESS GLOBAL CROWN.** -/
theorem bigradedBettiHodge_of_projective_limitless_arsenal
    (C : ProjectiveTowerHodgeIntertwining (V := V) (H := H))
    (R : ∀ p : Nat,
      ∀ j : ClassicalHodgeBasisIndex V H p,
        ProjectiveTwoGenerator
          (V := V) (H := H) (C.orbitSeed p).sourceIndex j) :
    BigradedBettiHodgeStatement V H := by
  apply C.bigradedBettiHodge
  intro p j
  exact (R p j).toGeometryFirst

/-- Compatibility theorem retaining the earlier all-pairs conserved-spine
interface. -/
theorem bigradedBettiHodge_of_conserved_spine_and_projective_two_generators
    (G : GeometricCycleClassSpine V H)
    (D : SpineTowerConservedCharge G)
    (R : ∀ q : Nat,
      ∀ i j : ClassicalHodgeBasisIndex V H q,
        ProjectiveTwoGenerator (V := V) (H := H) i j) :
    BigradedBettiHodgeStatement V H := by
  intro q alpha halpha
  let alphaH : ClassicalHodgeFiber V H q := ⟨alpha, halpha⟩
  have hne : AlgebraicHodgeSubspace V H q ≠ ⊥ :=
    D.algebraicHodgeSubspace_ne_bot q
  have htop : AlgebraicHodgeSubspace V H q = ⊤ :=
    algebraicHodgeSubspace_eq_top_of_geometryFirstTwoGenerators
      (fun i j => (R q i j).toGeometryFirst) hne
  have halg : alphaH ∈ AlgebraicHodgeSubspace V H q := by
    rw [htop]
    trivial
  have hatomic :
      alpha ∈ GSTClassicalHodgeAtomicSpan.pointCycleClassSpan q
        (H.cycleClass q) := halg
  rw [← GSTClassicalHodgeAtomicSpan.smoothProjective_cycleClass_range_eq_atomic_span
    V H q] at hatomic
  exact hatomic

/-- Canonical synchronized orbit seed generated by the nonzero normalized
projective spine in one weight. -/
noncomputable def conservedSpineOrbitSeed
    (G : GeometricCycleClassSpine V H)
    (D : SpineTowerConservedCharge G)
    (q : Nat) :
    NativeHodgeOrbitSeed (V := V) (H := H) (p := q) where
  cycle := spineNativeTower G q
  hodge := spineHodgeSeed G q
  hodge_ne_zero := D.spineHodgeSeed_ne_zero q
  class_eq := spineNativeTower_cycleClass G q

/-- **ONE-LIVE-SOURCE PROJECTIVE CROWN.**

The all-pairs projective requirement is unnecessary.  In each weight the
canonical nonzero spine seed chooses one live source coordinate.  Genuine
projective two-generator realizations are required only from that selected
source to each target basis direction.  Synchronized-defect orbit extraction
then constructs every target basis cycle and hence every rational Hodge class. -/
theorem bigradedBettiHodge_of_conserved_spine_source_projective_generators
    (G : GeometricCycleClassSpine V H)
    (D : SpineTowerConservedCharge G)
    (R : ∀ q : Nat,
      ∀ j : ClassicalHodgeBasisIndex V H q,
        ProjectiveTwoGenerator (V := V) (H := H)
          (conservedSpineOrbitSeed G D q).sourceIndex j) :
    BigradedBettiHodgeStatement V H := by
  intro q alpha halpha
  exact hodge_weight_of_projective_two_generators
    (conservedSpineOrbitSeed G D q) (R q) halpha

/-- Native-mass version of the canonical orbit seed.  The conserved charge is
manufactured from the native mass bridge rather than supplied separately. -/
noncomputable def nativeMassSpineOrbitSeed
    (G : GeometricCycleClassSpine V H)
    (M : NativeMassCycleClassBridge V H)
    (q : Nat) :
    NativeHodgeOrbitSeed (V := V) (H := H) (p := q) :=
  conservedSpineOrbitSeed G (M.toConservedCharge G) q

/-- **NATIVE-MASS + ONE-LIVE-SOURCE PROJECTIVE CROWN.**

This is the strongest composition in this module.  The infinite nonvanishing
family, the ambient cohomological detector, the all-native successor law, the
full projective matrix-unit family, and the all-ordered-pairs two-generator
family are all derived internally.  Inputs are reduced to the native mass
bridge and two actual projective primitives from the one canonical live source
to each requested target direction. -/
theorem bigradedBettiHodge_of_native_mass_source_projective_generators
    (G : GeometricCycleClassSpine V H)
    (M : NativeMassCycleClassBridge V H)
    (R : ∀ q : Nat,
      ∀ j : ClassicalHodgeBasisIndex V H q,
        ProjectiveTwoGenerator (V := V) (H := H)
          (nativeMassSpineOrbitSeed G M q).sourceIndex j) :
    BigradedBettiHodgeStatement V H :=
  bigradedBettiHodge_of_conserved_spine_source_projective_generators
    G (M.toConservedCharge G) R

/-- Elementwise native-cycle form of the earlier all-pairs route. -/
theorem every_hodge_class_has_native_cycle_of_conserved_spine_and_projective_two_generators
    (G : GeometricCycleClassSpine V H)
    (D : SpineTowerConservedCharge G)
    (R : ∀ q : Nat,
      ∀ i j : ClassicalHodgeBasisIndex V H q,
        ProjectiveTwoGenerator (V := V) (H := H) i j)
    (q : Nat)
    (alpha : RationalSingularCohomology H.analytification (2 * q))
    (halpha : alpha ∈ rationalHodgeSubspace (H.hodgeBigrading q)) :
    ∃ Z : GSTGeometricRealizationStage2D.codimensionCycles V.X q,
      H.cycleClass q Z = alpha := by
  exact LinearMap.mem_range.mp
    (bigradedBettiHodge_of_conserved_spine_and_projective_two_generators G D R q halpha)

/-- Elementwise native-cycle form of the strongest native-mass/live-source
route. -/
theorem every_hodge_class_has_native_cycle_of_native_mass_source_projective_generators
    (G : GeometricCycleClassSpine V H)
    (M : NativeMassCycleClassBridge V H)
    (R : ∀ q : Nat,
      ∀ j : ClassicalHodgeBasisIndex V H q,
        ProjectiveTwoGenerator (V := V) (H := H)
          (nativeMassSpineOrbitSeed G M q).sourceIndex j)
    (q : Nat)
    (alpha : RationalSingularCohomology H.analytification (2 * q))
    (halpha : alpha ∈ rationalHodgeSubspace (H.hodgeBigrading q)) :
    ∃ Z : GSTGeometricRealizationStage2D.codimensionCycles V.X q,
      H.cycleClass q Z = alpha := by
  exact LinearMap.mem_range.mp
    (bigradedBettiHodge_of_native_mass_source_projective_generators G M R q halpha)

#check ProjectivePrimitiveRealization
#check ProjectivePrimitiveRealization.toNativeHodgePrimitive
#check ProjectiveTwoGenerator
#check ProjectiveTwoGenerator.toGeometryFirst
#check ProjectiveTwoGenerator.normalized_word_on_hodge
#check hodge_weight_of_projective_two_generators
#check bigradedBettiHodge_of_projective_limitless_arsenal
#check bigradedBettiHodge_of_conserved_spine_and_projective_two_generators
#check conservedSpineOrbitSeed
#check bigradedBettiHodge_of_conserved_spine_source_projective_generators
#check nativeMassSpineOrbitSeed
#check bigradedBettiHodge_of_native_mass_source_projective_generators
#check every_hodge_class_has_native_cycle_of_conserved_spine_and_projective_two_generators
#check every_hodge_class_has_native_cycle_of_native_mass_source_projective_generators

#print axioms ProjectivePrimitiveRealization.toNativeHodgePrimitive
#print axioms ProjectiveTwoGenerator.normalized_word_on_hodge
#print axioms hodge_weight_of_projective_two_generators
#print axioms bigradedBettiHodge_of_projective_limitless_arsenal
#print axioms bigradedBettiHodge_of_conserved_spine_and_projective_two_generators
#print axioms conservedSpineOrbitSeed
#print axioms bigradedBettiHodge_of_conserved_spine_source_projective_generators
#print axioms nativeMassSpineOrbitSeed
#print axioms bigradedBettiHodge_of_native_mass_source_projective_generators
#print axioms every_hodge_class_has_native_cycle_of_native_mass_source_projective_generators

end GSTClassicalHodgeProjectiveTwoGeneratorExternalization
