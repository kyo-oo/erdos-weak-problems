import GSTClassicalHodgeCanonicalLimitlessNaturalityCrown
import GSTClassicalHodgeRangeLiftedSpectralOperator
import GSTClassicalHodgeCycleOperatorNaturality
import GSTClassicalHodgeLimitlessTwoSlotFailureDichotomy
import GSTClassicalHodgeUniversalTwoSlotNativeClosure

/-!
# GST CLASSICAL HODGE — CANONICAL COSMIC REALIZATION EQUIVALENCE

The final fixed-weight limitless operation is the true cosmic read/write
matrix unit observed in an arbitrary two-sheet Hodge chart.  Its naturality is
best attacked geometrically, not as an abstract subspace-stability statement.

Over Q the native cycle space is projective enough that any cohomology
endomorphism preserving the actual cycle-class range admits a native linear
lift.  Conversely, a genuine native operator commuting with the cycle-class
map automatically preserves the cycle-class range.

Therefore canonical cosmic naturality is equivalent to existence, for each
ordered two-sheet observation, of one actual native codimension-p cycle
operator whose cycle class is the canonical limitless cosmic action on every
algebraic Hodge input.  This is the precise operator-construction target for
the projective correspondence / fibered-native machinery.

No Hodge basis cycle is assumed and no surjectivity statement is stored in the
realization object.
-/

set_option maxHeartbeats 60000000
set_option maxRecDepth 1000000

noncomputable section

open AlgebraicGeometry

namespace GSTClassicalHodgeCanonicalCosmicRealizationEquivalence

open GSTProjectiveOverC
open GSTGeometricRealizationStage2D
open GSTGeometricRealizationStage2F
open GSTGeometricRealizationStage2G
open GSTClassicalHodgeFiberedCosmology
open GSTClassicalHodgeAtomicSpan
open GSTClassicalHodgeCanonicalLimitlessNaturalityCrown
open GSTClassicalHodgeLimitlessTwoSlotFailureDichotomy
open GSTClassicalHodgeLimitlessCosmicMatrixUnits
open GSTClassicalHodgeCycleOperatorNaturality
open GSTClassicalHodgeRangeLiftedSpectralOperator
open GSTClassicalHodgeRankFreePrimitiveGeneration
open GSTClassicalHodgeRankFreeArsenalIrreducibility
open GSTClassicalHodgeUniversalTwoSlotNativeClosure

variable {V : SmoothProjectiveComplexScheme}
variable {H : HodgeBigradedBettiData V}
variable {p : Nat}

/-- Ambient canonical limitless matrix-unit operator attached to one ordered
pair of genuine Hodge-basis directions. -/
noncomputable def canonicalCosmicAmbient
    (i j : ClassicalHodgeBasisIndex V H p) :
    Module.End ℚ (RationalSingularCohomology H.analytification (2 * p)) :=
  GSTClassicalHodgeUniversalTwoSlotNativeClosure.extendHodgeEndomorphism
    (V := V) (H := H)
    (GSTClassicalHodgeRankFreeArsenalIrreducibility.hodgeMatrixUnit i j)

/-- On the genuine Hodge fiber this ambient extension is exactly the observed
true limitless cosmic read/write action. -/
theorem canonicalCosmicAmbient_on_hodge
    (i j : ClassicalHodgeBasisIndex V H p)
    (alpha : ClassicalHodgeFiber V H p) :
    canonicalCosmicAmbient i j alpha.1 =
      liftCosmicWindowOperator (pairBasisIndex i j)
        (rationalCosmicMatrixUnit sourceSlot.1 targetSlot.1) alpha := by
  rw [canonicalCosmicAmbient]
  rw [GSTClassicalHodgeUniversalTwoSlotNativeClosure.extendHodgeEndomorphism_on_hodge]
  rw [hodgeMatrixUnit_eq_lift_limitless_cosmic]

/-- A genuine native realization of the canonical cosmic read/write action.
The commuting-square law is required on all native cycles; the cohomological
operator itself is fixed, not supplied as data. -/
structure NativeCanonicalCosmicRealization
    (i j : ClassicalHodgeBasisIndex V H p) where
  native : Module.End ℚ (codimensionCycles V.X p)
  naturality :
    ∀ Z : codimensionCycles V.X p,
      H.cycleClass p (native Z) =
        canonicalCosmicAmbient i j (H.cycleClass p Z)

namespace NativeCanonicalCosmicRealization

/-- A native canonical realization is automatically a complete
cycle-class-natural operator pair. -/
noncomputable def operatorPair
    {i j : ClassicalHodgeBasisIndex V H p}
    (R : NativeCanonicalCosmicRealization (V := V) (H := H) i j) :
    CycleClassOperatorPair V H p where
  cycleOperator := R.native
  cohomologyOperator := canonicalCosmicAmbient i j
  cycleClass_natural := by
    ext Z
    exact R.naturality Z

/-- Hence the actual cycle-class range is stable under the canonical cosmic
ambient action. -/
theorem range_stable
    {i j : ClassicalHodgeBasisIndex V H p}
    (R : NativeCanonicalCosmicRealization (V := V) (H := H) i j) :
    LinearMap.range (H.cycleClass p) ≤
      (LinearMap.range (H.cycleClass p)).comap (canonicalCosmicAmbient i j) := by
  intro alpha halpha
  rcases halpha with ⟨Z, rfl⟩
  exact ⟨R.native Z, R.naturality Z⟩

/-- In particular the canonical limitless read/write action preserves the
algebraic Hodge fiber. -/
theorem preserves_algebraicFiber
    {i j : ClassicalHodgeBasisIndex V H p}
    (R : NativeCanonicalCosmicRealization (V := V) (H := H) i j)
    (alpha : ClassicalHodgeFiber V H p)
    (halg : alpha ∈ AlgebraicHodgeSubspace V H p) :
    liftCosmicWindowOperator (pairBasisIndex i j)
        (rationalCosmicMatrixUnit sourceSlot.1 targetSlot.1) alpha ∈
      AlgebraicHodgeSubspace V H p := by
  have hrange : alpha.1 ∈ LinearMap.range (H.cycleClass p) := by
    rw [smoothProjective_cycleClass_range_eq_atomic_span V H p]
    exact (mem_AlgebraicHodgeSubspace_iff alpha).mp halg
  rcases hrange with ⟨Z, hZ⟩
  have hnat := R.naturality Z
  rw [hZ, canonicalCosmicAmbient_on_hodge i j alpha] at hnat
  have hout :
      (liftCosmicWindowOperator (pairBasisIndex i j)
          (rationalCosmicMatrixUnit sourceSlot.1 targetSlot.1) alpha).1 ∈
        LinearMap.range (H.cycleClass p) :=
    ⟨R.native Z, hnat⟩
  rw [smoothProjective_cycleClass_range_eq_atomic_span V H p] at hout
  exact (mem_AlgebraicHodgeSubspace_iff
    (liftCosmicWindowOperator (pairBasisIndex i j)
      (rationalCosmicMatrixUnit sourceSlot.1 targetSlot.1) alpha)).mpr hout

end NativeCanonicalCosmicRealization

/-- A family of genuine native realizations immediately gives the single
canonical limitless naturality law used by the no-escape crown. -/
theorem canonicalCosmicNaturality_of_nativeRealizations
    (R : ∀ i j : ClassicalHodgeBasisIndex V H p,
      NativeCanonicalCosmicRealization (V := V) (H := H) i j) :
    CanonicalCosmicNaturality (V := V) (H := H) p := by
  intro i j alpha halg
  exact NativeCanonicalCosmicRealization.preserves_algebraicFiber (R i j)
    alpha halg

/-- Conversely, canonical cosmic naturality gives cycle-class-range stability
on every Hodge class already known to be algebraic.  The range-lift machinery
then turns the corresponding ambient operator into a native operator. -/
theorem nativeRealization_of_range_stable
    (i j : ClassicalHodgeBasisIndex V H p)
    (hstable :
      ∀ alpha ∈ LinearMap.range (H.cycleClass p),
        canonicalCosmicAmbient i j alpha ∈ LinearMap.range (H.cycleClass p)) :
    Nonempty (NativeCanonicalCosmicRealization (V := V) (H := H) i j) := by
  have hT :
      ∀ x : RationalSingularCohomology H.analytification (2 * p),
        x ∈ LinearMap.range (H.cycleClass p) →
        (canonicalCosmicAmbient i j) x ∈ LinearMap.range (H.cycleClass p) :=
    fun x hx => hstable x hx
  refine ⟨{
    native := liftedCycleOperator (canonicalCosmicAmbient i j) hT
    naturality := ?_ }⟩
  intro Z
  exact cycleClass_liftedCycleOperator (canonicalCosmicAmbient i j) hT Z

/-- Exact realization form of the canonical fixed-weight target. -/
theorem nativeCanonicalRealizations_imply_hodgeWeight
    (hseed : AlgebraicHodgeSubspace V H p ≠ ⊥)
    (R : ∀ i j : ClassicalHodgeBasisIndex V H p,
      NativeCanonicalCosmicRealization (V := V) (H := H) i j) :
    rationalHodgeSubspace (H.hodgeBigrading p) ≤
      LinearMap.range (H.cycleClass p) := by
  exact hodge_weight hseed (canonicalCosmicNaturality_of_nativeRealizations R)

/-- With one nonzero algebraic seed, constructing genuine native realizations
of the canonical limitless cosmic matrix units is sufficient for complete
fixed-weight Hodge saturation. -/
theorem algebraicFiber_eq_top_of_nativeCanonicalRealizations
    (hseed : AlgebraicHodgeSubspace V H p ≠ ⊥)
    (R : ∀ i j : ClassicalHodgeBasisIndex V H p,
      NativeCanonicalCosmicRealization (V := V) (H := H) i j) :
    AlgebraicHodgeSubspace V H p = ⊤ := by
  exact algebraicFiber_eq_top hseed
    (canonicalCosmicNaturality_of_nativeRealizations R)

#check canonicalCosmicAmbient
#check canonicalCosmicAmbient_on_hodge
#check NativeCanonicalCosmicRealization
#check NativeCanonicalCosmicRealization.operatorPair
#check NativeCanonicalCosmicRealization.preserves_algebraicFiber
#check canonicalCosmicNaturality_of_nativeRealizations
#check nativeRealization_of_range_stable
#check nativeCanonicalRealizations_imply_hodgeWeight
#check algebraicFiber_eq_top_of_nativeCanonicalRealizations

#print axioms NativeCanonicalCosmicRealization.preserves_algebraicFiber
#print axioms nativeRealization_of_range_stable
#print axioms nativeCanonicalRealizations_imply_hodgeWeight
#print axioms algebraicFiber_eq_top_of_nativeCanonicalRealizations

end GSTClassicalHodgeCanonicalCosmicRealizationEquivalence
