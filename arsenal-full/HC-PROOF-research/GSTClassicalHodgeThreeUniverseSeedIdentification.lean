import GSTClassicalHodgeFiberedTransferCompletion
import GSTClassicalHodgeNativeTransferAddressIdentification
import GSTClassicalHodgeTransferSeedUniverse
import GSTNativeCodimensionCyclePresentation

/-!
# GST CLASSICAL HODGE — THREE-UNIVERSE SEED IDENTIFICATION

The same weight-p limitless generator appears independently in three parts of
the repository:

1. the genuine classical Hodge multiplicity sheet after forgetting its fiber;
2. the universal cosmic shadow of an actual native codimension-p point cycle;
3. the established limitless transfer generator `compactClMono p`.

This file proves these are not merely analogous objects.  After the canonical
rational universal-address identification, they are literally equal.

Thus the classical fibered Hodge universe, the genuine projective cycle
universe, and the original limitless GST transfer universe share one common
base-weight artery.  Multiplicity remains fully visible before the final
forgetful projection, exactly as required for arbitrary classical Hodge rank.
-/

set_option maxHeartbeats 40000000
set_option maxRecDepth 1000000

noncomputable section

open AlgebraicGeometry

namespace GSTClassicalHodgeThreeUniverseSeedIdentification

open GSTProjectiveOverC
open GSTGeometricRealizationStage2D
open GSTGeometricRealizationStage2G
open GSTClassicalHodgeFiberedCosmology
open GSTClassicalHodgeFiberedTransferCompletion
open GSTClassicalHodgeTransferSeedUniverse
open GSTClassicalHodgeNativeCycleCosmicShadow
open GSTClassicalHodgeNativeTransferAddressIdentification
open GSTNativeCodimensionCyclePresentation
open GSTTransferBridgeV2

/-- **THREE-UNIVERSE BASIS-SEED IDENTITY.**
For every genuine Hodge basis sheet and every genuine native codimension-p
point, forgetting multiplicity on the classical side gives exactly the same
rational universal cosmic address as the native point shadow and the original
limitless transfer generator. -/
theorem classicalSheet_eq_nativePoint_eq_transfer
    (V : SmoothProjectiveComplexScheme)
    (H : HodgeBigradedBettiData V)
    (p : Nat)
    (i : ClassicalHodgeBasisIndex V H p)
    (x : CodimensionPoint V.X p) :
    forgetMultiplicityToGST (fiberedSheetGenerator V H ⟨p,i⟩) =
      pureWeightToUniversalAddress
        (nativeCycleCosmicShadow V p (codimensionPointCycle V.X p x))
    ∧ pureWeightToUniversalAddress
        (nativeCycleCosmicShadow V p (codimensionPointCycle V.X p x)) =
      rationalizeCompactAddress (compactClMono p) := by
  constructor
  · rw [fiberedSheet_projects_to_cosmicGenerator]
    rw [nativeCycleCosmicShadow_point]
    rw [pureWeightToUniversalAddress_basis]
    rfl
  · exact nativePoint_shadow_eq_rationalized_transfer V p x

/-- Direct classical-sheet/transfer identity, now obtained through the native
projective-cycle artery as well as the historical internal transfer theorem. -/
theorem classicalSheet_eq_rationalized_transfer
    (V : SmoothProjectiveComplexScheme)
    (H : HodgeBigradedBettiData V)
    (p : Nat)
    (i : ClassicalHodgeBasisIndex V H p) :
    forgetMultiplicityToGST (fiberedSheetGenerator V H ⟨p,i⟩) =
      rationalizeCompactAddress (compactClMono p) := by
  rw [fiberedSheet_projects_to_cosmicGenerator]
  rw [rationalize_compactClMono]
  rfl

/-- Every genuine classical basis vector therefore has the same base limitless
address as every unit native cycle in the corresponding codimension. -/
theorem classicalBasis_baseAddress_eq_nativePoint
    (V : SmoothProjectiveComplexScheme)
    (H : HodgeBigradedBettiData V)
    (p : Nat)
    (i : ClassicalHodgeBasisIndex V H p)
    (x : CodimensionPoint V.X p) :
    forgetMultiplicityToGST
        (fiberedWeightCoordinates V H p (classicalHodgeBasis V H p i)) =
      pureWeightToUniversalAddress
        (nativeCycleCosmicShadow V p (codimensionPointCycle V.X p x)) := by
  rw [classicalBasis_eq_fiberedSheetGenerator]
  exact (classicalSheet_eq_nativePoint_eq_transfer V H p i x).1

/-- Total classical coefficient mass of one Hodge class. -/
noncomputable def classicalHodgeMass
    (V : SmoothProjectiveComplexScheme)
    (H : HodgeBigradedBettiData V)
    (p : Nat) : ClassicalHodgeFiber V H p →ₗ[ℚ] ℚ where
  toFun alpha :=
    ((classicalHodgeBasis V H p).repr alpha).sum fun _ q => q
  map_add' := by
    intro a b
    classical
    simp [LinearMap.map_add, Finsupp.sum_add_index']
  map_smul' := by
    intro q a
    classical
    have hrepr : ((classicalHodgeBasis V H p).repr (q • a))
        = q • ((classicalHodgeBasis V H p).repr a) :=
      LinearMap.map_smul _ _ _
    rw [hrepr, Finsupp.sum_smul_index' (fun _ => rfl)]
    simp [smul_eq_mul, Finsupp.sum, Finset.mul_sum]

/-- Forgetting multiplicity from an arbitrary genuine Hodge class gives its
finite total basis mass times the common limitless transfer direction. -/
theorem classicalHodge_forgetMultiplicity_eq_mass_transfer
    (V : SmoothProjectiveComplexScheme)
    (H : HodgeBigradedBettiData V)
    (p : Nat)
    (alpha : ClassicalHodgeFiber V H p) :
    forgetMultiplicityToGST (fiberedWeightCoordinates V H p alpha) =
      classicalHodgeMass V H p alpha •
        rationalizeCompactAddress (compactClMono p) := by
  rw [forgetMultiplicity_fiberedWeightCoordinates]
  rw [rationalize_compactClMono]
  ext n
  simp [classicalHodgeMass, smul_eq_mul, pureWeightAddress]

/-- If a native cycle and a classical Hodge class have the same total rational
mass, then their multiplicity-forgotten limitless cosmic addresses coincide
exactly. -/
theorem native_and_classical_same_mass_same_limitless_address
    (V : SmoothProjectiveComplexScheme)
    (H : HodgeBigradedBettiData V)
    (p : Nat)
    (Z : codimensionCycles V.X p)
    (alpha : ClassicalHodgeFiber V H p)
    (hmass : nativeCycleMass V p Z = classicalHodgeMass V H p alpha) :
    pureWeightToUniversalAddress (nativeCycleCosmicShadow V p Z) =
      forgetMultiplicityToGST (fiberedWeightCoordinates V H p alpha) := by
  rw [nativeCycle_shadow_eq_mass_transfer]
  rw [classicalHodge_forgetMultiplicity_eq_mass_transfer]
  rw [hmass]

/-- Every nonzero genuine Hodge class has a live multiplicity sheet sitting
over the exact same nonzero limitless transfer seed as every unit native point
cycle of that codimension. -/
theorem nonzeroHodge_liveSheet_native_transfer_tether
    (V : SmoothProjectiveComplexScheme)
    (H : HodgeBigradedBettiData V)
    (p : Nat)
    (alpha : ClassicalHodgeFiber V H p)
    (halpha : alpha ≠ 0)
    (x : CodimensionPoint V.X p) :
    ∃ i : ClassicalHodgeBasisIndex V H p,
      (classicalHodgeBasis V H p).repr alpha i ≠ 0
      ∧ forgetMultiplicityToGST (fiberedSheetGenerator V H ⟨p,i⟩) =
          pureWeightToUniversalAddress
            (nativeCycleCosmicShadow V p (codimensionPointCycle V.X p x))
      ∧ pureWeightToUniversalAddress
            (nativeCycleCosmicShadow V p (codimensionPointCycle V.X p x)) =
          rationalizeCompactAddress (compactClMono p) := by
  obtain ⟨i,hi,htransfer⟩ :=
    nonzero_hodge_has_transfer_seed_sheet (V:=V) (H:=H) alpha halpha
  refine ⟨i,hi,?_,nativePoint_shadow_eq_rationalized_transfer V p x⟩
  rw [htransfer, nativeCycleCosmicShadow_point,
    pureWeightToUniversalAddress_basis]
  rfl

/-- Grand seed identity across all three mathematical universes. -/
theorem three_universe_seed_crown
    (V : SmoothProjectiveComplexScheme)
    (H : HodgeBigradedBettiData V) :
    ∀ p : Nat,
    ∀ i : ClassicalHodgeBasisIndex V H p,
    ∀ x : CodimensionPoint V.X p,
      forgetMultiplicityToGST (fiberedSheetGenerator V H ⟨p,i⟩) =
        pureWeightToUniversalAddress
          (nativeCycleCosmicShadow V p (codimensionPointCycle V.X p x))
      ∧ pureWeightToUniversalAddress
          (nativeCycleCosmicShadow V p (codimensionPointCycle V.X p x)) =
        rationalizeCompactAddress (compactClMono p) := by
  intro p i x
  exact classicalSheet_eq_nativePoint_eq_transfer V H p i x

#check classicalSheet_eq_nativePoint_eq_transfer
#check classicalSheet_eq_rationalized_transfer
#check classicalHodgeMass
#check classicalHodge_forgetMultiplicity_eq_mass_transfer
#check native_and_classical_same_mass_same_limitless_address
#check nonzeroHodge_liveSheet_native_transfer_tether
#check three_universe_seed_crown

#print axioms classicalSheet_eq_nativePoint_eq_transfer
#print axioms classicalHodge_forgetMultiplicity_eq_mass_transfer
#print axioms native_and_classical_same_mass_same_limitless_address
#print axioms nonzeroHodge_liveSheet_native_transfer_tether
#print axioms three_universe_seed_crown

end GSTClassicalHodgeThreeUniverseSeedIdentification
