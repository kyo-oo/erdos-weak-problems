import GSTClassicalHodgeNativeCycleCosmicShadow
import GSTTransferBridgeV2
import GSTUniversalAddressBridge

/-!
# GST CLASSICAL HODGE — NATIVE / TRANSFER ADDRESS IDENTIFICATION

The native-cycle shadow uses the natural Hodge-weight index `p`, whereas the
original limitless transfer bridge uses the universal cosmic-cell address of
`(p,p)`.  These are not competing coordinate systems: the diagonal weight map

  p |-> cosmicAddressEquiv (p,p)

is injective, so it embeds the pure-Hodge weight universe into the universal
cosmic address universe.

This file proves that after this canonical reindexing and rationalization, the
shadow of every genuine codimension-p point cycle is exactly the established
limitless transfer generator `compactClMono p`.
-/

set_option maxHeartbeats 40000000
set_option maxRecDepth 1000000

noncomputable section

open AlgebraicGeometry

namespace GSTClassicalHodgeNativeTransferAddressIdentification

open GSTProjectiveOverC
open GSTGeometricRealizationStage2D
open GSTUniversalAddressBridge
open GSTTransferBridgeV2
open GSTClassicalHodgeLimitlessCosmicMatrixUnits
open GSTClassicalHodgeNativeCycleCosmicShadow
open GSTNativeCodimensionCyclePresentation

/-- Universal cosmic address of the diagonal cell at Hodge weight `p`. -/
def pureWeightAddress (p : Nat) : Nat :=
  cosmicAddressEquiv (p,p)

/-- Distinct Hodge weights have distinct universal cosmic addresses. -/
theorem pureWeightAddress_injective : Function.Injective pureWeightAddress := by
  intro p q h
  have hpq : (p,p) = (q,q) := cosmicAddressEquiv.injective h
  exact congrArg Prod.fst hpq

/-- Embedding of the pure Hodge weight axis into the full cosmic address line. -/
def pureWeightAddressEmbedding : Nat ↪ Nat :=
  ⟨pureWeightAddress, pureWeightAddress_injective⟩

/-- Rational universal-address ring. -/
abbrev RationalCosmicAddress := Nat →₀ ℚ

/-- Reindex a pure-weight cosmic state into the universal cell-address system. -/
noncomputable def pureWeightToUniversalAddress :
    RationalPureCosmos →ₗ[ℚ] RationalCosmicAddress where
  toFun φ := Finsupp.embDomain pureWeightAddressEmbedding φ
  map_add' := by intro φ ψ; simp
  map_smul' := by
    intro q φ
    ext n
    simp [Finsupp.embDomain_apply]

/-- A pure weight basis becomes the universal address basis of its diagonal
cosmic cell. -/
@[simp]
theorem pureWeightToUniversalAddress_basis
    (p : Nat) :
    pureWeightToUniversalAddress (rationalCosmicBasis p) =
      Finsupp.single (pureWeightAddress p) 1 := by
  ext n
  simp [pureWeightToUniversalAddress, rationalCosmicBasis,
    pureWeightAddressEmbedding, pureWeightAddress]

/-- Rationalize the original integral universal compact address ring. -/
noncomputable def rationalizeCompactAddress :
    CompactClRing →ₗ[ℤ] RationalCosmicAddress where
  toFun φ := φ.sum fun n z => Finsupp.single n (z : ℚ)
  map_add' := by
    intro φ ψ
    classical
    simp [Finsupp.sum_add_index']
  map_smul' := by
    intro z φ
    classical
    ext n
    rw [Finsupp.sum_smul_index' (fun i => by simp)]
    simp [Finsupp.sum, Finset.mul_sum]
    refine Finset.sum_congr rfl fun i _ => ?_
    simp only [Finsupp.single_apply]
    by_cases h : n = i
    · simp [h]
    · simp [h]
      intro h1 h2
      exact absurd h2 h1

/-- Rationalization of one integral address basis vector. -/
@[simp]
theorem rationalizeCompactAddress_single
    (n : Nat) (z : ℤ) :
    rationalizeCompactAddress (Finsupp.single n z) =
      Finsupp.single n (z : ℚ) := by
  classical
  ext m
  simp [rationalizeCompactAddress]

/-- The established limitless transfer generator rationalizes to the universal
address basis of the diagonal cosmic cell. -/
theorem rationalize_compactClMono
    (p : Nat) :
    rationalizeCompactAddress (compactClMono p) =
      Finsupp.single (pureWeightAddress p) 1 := by
  ext n
  simp [rationalizeCompactAddress, compactClMono, compactClCode,
    pureWeightAddress, cosmicAddressEquiv]

/-- **NATIVE POINT = LIMITLESS TRANSFER GENERATOR.**
Every genuine codimension-p point cycle has exactly the same rational universal
cosmic address as the pre-existing limitless GST transfer generator. -/
theorem nativePoint_shadow_eq_rationalized_transfer
    (V : SmoothProjectiveComplexScheme)
    (p : Nat) (x : CodimensionPoint V.X p) :
    pureWeightToUniversalAddress
        (nativeCycleCosmicShadow V p (codimensionPointCycle V.X p x)) =
      rationalizeCompactAddress (compactClMono p) := by
  rw [nativeCycleCosmicShadow_point]
  rw [pureWeightToUniversalAddress_basis]
  rw [rationalize_compactClMono]

/-- The same identification for an arbitrary native codimension-p cycle: its
universal transfer address is its total rational point mass times the canonical
limitless transfer direction. -/
theorem nativeCycle_shadow_eq_mass_transfer
    (V : SmoothProjectiveComplexScheme)
    (p : Nat) (Z : codimensionCycles V.X p) :
    pureWeightToUniversalAddress (nativeCycleCosmicShadow V p Z) =
      nativeCycleMass V p Z •
        rationalizeCompactAddress (compactClMono p) := by
  rw [nativeCycleCosmicShadow_eq_mass_smul]
  rw [map_smul]
  rw [pureWeightToUniversalAddress_basis]
  rw [rationalize_compactClMono]

/-- Projective cut tower levels therefore lie exactly on the existing limitless
transfer ray at their codimension weight. -/
theorem projectiveTower_shadow_is_transfer_ray
    (V : SmoothProjectiveComplexScheme)
    (p : Nat) :
    pureWeightToUniversalAddress (projectiveTowerCosmicShadow V p) =
      nativeCycleMass V p
          (GSTClassicalHodgeLimitlessProjectiveLefschetzTower.projectiveCutTower V p) •
        rationalizeCompactAddress (compactClMono p) := by
  unfold projectiveTowerCosmicShadow
  exact nativeCycle_shadow_eq_mass_transfer V p _

/-- Crown identifying actual projective cycle atoms, native-cycle shadows,
universal cosmic addresses, and the established limitless transfer generator. -/
theorem native_transfer_address_crown
    (V : SmoothProjectiveComplexScheme) :
    ∀ p : Nat, ∀ x : CodimensionPoint V.X p,
      pureWeightToUniversalAddress
          (nativeCycleCosmicShadow V p (codimensionPointCycle V.X p x)) =
        rationalizeCompactAddress (compactClMono p) := by
  intro p x
  exact nativePoint_shadow_eq_rationalized_transfer V p x

#check pureWeightAddress
#check pureWeightAddressEmbedding
#check pureWeightToUniversalAddress
#check rationalizeCompactAddress
#check rationalize_compactClMono
#check nativePoint_shadow_eq_rationalized_transfer
#check nativeCycle_shadow_eq_mass_transfer
#check projectiveTower_shadow_is_transfer_ray
#check native_transfer_address_crown

#print axioms pureWeightAddress_injective
#print axioms rationalize_compactClMono
#print axioms nativePoint_shadow_eq_rationalized_transfer
#print axioms nativeCycle_shadow_eq_mass_transfer
#print axioms native_transfer_address_crown

end GSTClassicalHodgeNativeTransferAddressIdentification
