import GSTClassicalHodgeFullLimitlessExternalization
import GSTClassicalHodgeConcreteFailureDichotomy
import GSTClassicalHodgeLimitlessSpinePropagation
import GSTClassicalHodgeCanonicalLimitlessNaturalityCrown

/-!
# GST CLASSICAL HODGE — FULL LIMITLESS CROWN

This is the final composition layer of the current limitless derivation.

All internal algebra has already been discharged upstream:

* unrestricted classical Hodge multiplicity coordinates;
* finite-support localization and arbitrary world recoordination;
* exact sheet projectors and spectral extraction;
* true limitless cosmic Poincare read/write matrix units;
* Lefschetz propagation with nonzero central-binomial coefficients;
* genuine projective native-cycle normal form and principal-cut operators;
* native/cosmic transfer-address identification;
* tensor commutation of multiplicity and projective actions;
* rank-free irreducibility/no-escape saturation.

The geometric cycle-class spine generates the cross-weight algebraic tower
itself.  Two nonvanishing interfaces are retained below.  The older conserved
charge gives a stronger all-weight invariant.  The newer live-mass survival
interface is deliberately weaker and closer to the geometry actually needed by
the Hodge target: only a live `(p,p)` weight must have a nonzero native tower
mass, and zero cycle class must force zero native mass.  No equality between a
geometric successor count and the cosmic normalization coefficient is required.

This module deliberately lands in `BigradedBettiHodgeStatement` directly and
has no dependency on the public `HodgeConjecture` entry face.  That keeps the
final dependency direction acyclic: this crown is geometry/mathematics below,
while `HodgeConjecture.lean` imports this crown and exposes the final theorem.
-/

set_option maxHeartbeats 100000000
set_option maxRecDepth 1000000

noncomputable section

open AlgebraicGeometry

namespace GSTClassicalHodgeFullLimitlessCrown

open GSTProjectiveOverC
open GSTGeometricRealizationStage2D
open GSTGeometricRealizationStage2F
open GSTClassicalHodgeConcreteFailureDichotomy
open GSTGeometricRealizationStage2G
open GSTClassicalHodgeFiberedCosmology
open GSTClassicalHodgeRankFreeArsenalIrreducibility
open GSTClassicalHodgeLimitlessTwoSlotFailureDichotomy
open GSTClassicalHodgeGeometricCycleClassSpine
open GSTClassicalHodgeProjectiveCorrespondenceAlgebra
open GSTClassicalHodgeFullLimitlessExternalization
open GSTClassicalHodgeLimitlessSpinePropagation
open GSTClassicalHodgeNativeCycleCosmicShadow
open GSTClassicalHodgeCanonicalLimitlessNaturalityCrown

variable {V : SmoothProjectiveComplexScheme}
variable {H : HodgeBigradedBettiData V}

/-- The canonical projective/Hodge spine tower does not vanish in a live Hodge
weight.  This is retained as the compatibility interface consumed by the
older crown. -/
def SpineTowerNonvanishing
    (G : GeometricCycleClassSpine V H) : Prop :=
  ∀ p : Nat,
    rationalHodgeSubspace (H.hodgeBigrading p) ≠ ⊥ →
      spineHodgeSeed G p ≠ 0

/-- **NONVANISHING FROM ONE CONSERVED CHARGE.** -/
theorem spineTowerNonvanishing_of_conservedCharge
    (G : GeometricCycleClassSpine V H)
    (D : SpineTowerConservedCharge G) :
    SpineTowerNonvanishing G := by
  intro p _hH
  exact D.spineHodgeSeed_ne_zero p

/-! ## Live-weight native survival

The Hodge target never asks for a nonzero algebraic seed in a weight whose
rational `(p,p)` fiber is zero.  Requiring a nonzero native tower at every
natural-number weight is therefore stronger than necessary and can conflict
with finite geometric dimension.  The following interface isolates exactly the
remaining geometry:

1. native mass descends through the genuine cycle-class map at zero;
2. whenever the Hodge fiber is live, the geometry-built tower has nonzero
   native mass.

The second clause is the exact-stratum exhaustion/survival theorem that the
principal-cut geometry must ultimately provide.  It contains no cosmic scalar
and no arbitrary cohomological detector. -/

/-- Minimal live-weight semantic/geometric survival package. -/
structure LiveSpineMassSurvival
    (G : GeometricCycleClassSpine V H) where
  kernel_mass_zero :
    ∀ p : Nat, ∀ Z : codimensionCycles V.X p,
      H.cycleClass p Z = 0 → nativeCycleMass V p Z = 0
  live_tower_mass_ne_zero :
    ∀ p : Nat,
      rationalHodgeSubspace (H.hodgeBigrading p) ≠ ⊥ →
      nativeCycleMass V p (spineNativeTower G p) ≠ 0

namespace LiveSpineMassSurvival

/-- In a live Hodge weight, nonzero native mass forces the actual cycle class
of the canonical spine cycle to be nonzero. -/
theorem cycleClass_spineNativeTower_ne_zero
    (S : LiveSpineMassSurvival (V := V) (H := H) G)
    (p : Nat)
    (hH : rationalHodgeSubspace (H.hodgeBigrading p) ≠ ⊥) :
    H.cycleClass p (spineNativeTower G p) ≠ 0 := by
  intro hzero
  have hmzero := S.kernel_mass_zero p (spineNativeTower G p) hzero
  exact S.live_tower_mass_ne_zero p hH hmzero

/-- The exact zero-map countermodel is excluded precisely in every live Hodge
weight; no assertion is made in geometrically dead weights. -/
theorem cycleClass_ne_zero_of_live
    (S : LiveSpineMassSurvival (V := V) (H := H) G)
    (p : Nat)
    (hH : rationalHodgeSubspace (H.hodgeBigrading p) ≠ ⊥) :
    H.cycleClass p ≠ 0 := by
  intro hzero
  apply S.cycleClass_spineNativeTower_ne_zero p hH
  rw [hzero]
  rfl

/-- Live native survival is already enough to recover the old tower
nonvanishing interface. -/
theorem spineHodgeSeed_ne_zero_of_live
    (S : LiveSpineMassSurvival (V := V) (H := H) G)
    (p : Nat)
    (hH : rationalHodgeSubspace (H.hodgeBigrading p) ≠ ⊥) :
    spineHodgeSeed G p ≠ 0 :=
  (spineHodgeSeed_ne_zero_iff_cycleClass_ne_zero G p).2
    (S.cycleClass_spineNativeTower_ne_zero p hH)

/-- Compatibility bridge to the legacy crown. -/
theorem spineTowerNonvanishing
    (S : LiveSpineMassSurvival (V := V) (H := H) G) :
    SpineTowerNonvanishing G := by
  intro p hH
  exact S.spineHodgeSeed_ne_zero_of_live p hH

end LiveSpineMassSurvival

/-- The native-mass conserved-charge package already built in the lower spine
layer implies the weaker live-mass interface.  Unlike an arbitrary conserved
detector, this conversion is valid because `NativeMassCycleClassBridge`
constructs its detector from `nativeCycleMass` itself. -/
noncomputable def liveSpineMassSurvival_of_nativeMassBridge
    (G : GeometricCycleClassSpine V H)
    (M : NativeMassCycleClassBridge V H) :
    LiveSpineMassSurvival G where
  kernel_mass_zero := M.kernel_mass_zero
  live_tower_mass_ne_zero := by
    intro p _hH
    exact (M.toConservedCharge G).nativeRead_spineNativeTower_ne_zero p

/-- Genuine projective realization of the one true limitless cosmic read/write
operator in every weight and every ordered multiplicity pair.  The operator is
not an abstract Hodge matrix unit: it must come from the actual projective
correspondence sector constructed from scheme geometry. -/
def FullProjectiveCosmicExternalization
    (G : GeometricCycleClassSpine V H) : Prop :=
  ∀ p : Nat,
  ∀ i j : ClassicalHodgeBasisIndex V H p,
    ∃ K : ProjectiveNativeKernel V p,
      AtomCosmicExternalization G i j K

/-- A full projective externalization gives canonical cosmic naturality in every
weight. -/
theorem canonicalCosmicNaturality_of_fullProjectiveExternalization
    (G : GeometricCycleClassSpine V H)
    (R : FullProjectiveCosmicExternalization G) :
    ∀ p : Nat, CanonicalCosmicNaturality (V := V) (H := H) p := by
  intro p
  let K : ∀ i j : ClassicalHodgeBasisIndex V H p,
      ProjectiveNativeKernel V p :=
    fun i j => Classical.choose (R p i j)
  have hK : ∀ i j : ClassicalHodgeBasisIndex V H p,
      AtomCosmicExternalization G i j (K i j) := by
    intro i j
    exact Classical.choose_spec (R p i j)
  exact canonicalCosmicNaturality_of_fullLimitlessExternalization G K hK

/-- Nonvanishing of the canonical spine tower supplies the one algebraic seed
required by the rank-free no-escape theorem in every live weight. -/
theorem algebraicFiber_ne_bot_of_spineTower
    (G : GeometricCycleClassSpine V H)
    (hNV : SpineTowerNonvanishing G)
    (p : Nat)
    (hH : rationalHodgeSubspace (H.hodgeBigrading p) ≠ ⊥) :
    AlgebraicFiber (V := V) (H := H) (p := p) ≠ ⊥ := by
  have hseed : spineHodgeSeed G p ≠ 0 := hNV p hH
  have halg : spineHodgeSeed G p ∈ AlgebraicHodgeSubspace V H p :=
    spineHodgeSeed_algebraic G p
  intro hbot
  have hz : spineHodgeSeed G p = 0 := by
    have hm : spineHodgeSeed G p ∈
        (⊥ : Submodule ℚ (ClassicalHodgeFiber V H p)) := by
      rw [← hbot]
      exact halg
    simpa using hm
  exact hseed hz

/-- **FULL LIMITLESS CLASSICAL HODGE CROWN.** -/
theorem bigradedBettiHodge
    (G : GeometricCycleClassSpine V H)
    (hNV : SpineTowerNonvanishing G)
    (R : FullProjectiveCosmicExternalization G) :
    BigradedBettiHodgeStatement V H := by
  intro p alpha halpha
  by_cases hH : rationalHodgeSubspace (H.hodgeBigrading p) = ⊥
  · have hz : alpha = 0 := by
      have : alpha ∈ (⊥ : Submodule ℚ
          (RationalSingularCohomology H.analytification (2 * p))) := by
        simpa [hH] using halpha
      simpa using this
    subst alpha
    exact ⟨0, by simp⟩
  · exact hodge_weight
      (algebraicFiber_ne_bot_of_spineTower G hNV p hH)
      (canonicalCosmicNaturality_of_fullProjectiveExternalization G R p)
      halpha

/-- **CONSERVED-CHARGE LIMITLESS CROWN.** -/
theorem bigradedBettiHodge_of_conservedCharge
    (G : GeometricCycleClassSpine V H)
    (D : SpineTowerConservedCharge G)
    (R : FullProjectiveCosmicExternalization G) :
    BigradedBettiHodgeStatement V H :=
  bigradedBettiHodge G
    (spineTowerNonvanishing_of_conservedCharge G D) R

/-- **LIVE-MASS SURVIVAL LIMITLESS CROWN.**
Exact cosmic/native coefficient matching is not needed for the nonvanishing
artery. -/
theorem bigradedBettiHodge_of_liveMassSurvival
    (G : GeometricCycleClassSpine V H)
    (S : LiveSpineMassSurvival G)
    (R : FullProjectiveCosmicExternalization G) :
    BigradedBettiHodgeStatement V H :=
  bigradedBettiHodge G S.spineTowerNonvanishing R

/-- Public-name compatibility receipt for the exact Stage-2G target. -/
theorem classicalHodgeTarget
    (G : GeometricCycleClassSpine V H)
    (hNV : SpineTowerNonvanishing G)
    (R : FullProjectiveCosmicExternalization G) :
    BigradedBettiHodgeStatement V H :=
  bigradedBettiHodge G hNV R

/-- Conserved-charge public-name compatibility receipt. -/
theorem classicalHodgeTarget_of_conservedCharge
    (G : GeometricCycleClassSpine V H)
    (D : SpineTowerConservedCharge G)
    (R : FullProjectiveCosmicExternalization G) :
    BigradedBettiHodgeStatement V H :=
  bigradedBettiHodge_of_conservedCharge G D R

/-- Live-mass public-name compatibility receipt. -/
theorem classicalHodgeTarget_of_liveMassSurvival
    (G : GeometricCycleClassSpine V H)
    (S : LiveSpineMassSurvival G)
    (R : FullProjectiveCosmicExternalization G) :
    BigradedBettiHodgeStatement V H :=
  bigradedBettiHodge_of_liveMassSurvival G S R

/-- Elementwise form: every genuine rational `(p,p)` class receives an actual
native codimension-p algebraic cycle. -/
theorem every_hodge_class_has_native_cycle
    (G : GeometricCycleClassSpine V H)
    (hNV : SpineTowerNonvanishing G)
    (R : FullProjectiveCosmicExternalization G)
    (p : Nat)
    (alpha : RationalSingularCohomology H.analytification (2 * p))
    (halpha : alpha ∈ rationalHodgeSubspace (H.hodgeBigrading p)) :
    ∃ Z : codimensionCycles V.X p,
      H.cycleClass p Z = alpha := by
  exact ((bigradedBettiHodgeStatement_iff_explicit_witness V H).1
      (bigradedBettiHodge G hNV R)) p alpha
      ((mem_rationalHodgeSubspace_iff (H.hodgeBigrading p) alpha).1 halpha)

/-- Elementwise conserved-charge landing. -/
theorem every_hodge_class_has_native_cycle_of_conservedCharge
    (G : GeometricCycleClassSpine V H)
    (D : SpineTowerConservedCharge G)
    (R : FullProjectiveCosmicExternalization G)
    (p : Nat)
    (alpha : RationalSingularCohomology H.analytification (2 * p))
    (halpha : alpha ∈ rationalHodgeSubspace (H.hodgeBigrading p)) :
    ∃ Z : codimensionCycles V.X p,
      H.cycleClass p Z = alpha := by
  exact ((bigradedBettiHodgeStatement_iff_explicit_witness V H).1
      (bigradedBettiHodge_of_conservedCharge G D R)) p alpha
      ((mem_rationalHodgeSubspace_iff (H.hodgeBigrading p) alpha).1 halpha)

/-- Elementwise live-mass landing. -/
theorem every_hodge_class_has_native_cycle_of_liveMassSurvival
    (G : GeometricCycleClassSpine V H)
    (S : LiveSpineMassSurvival G)
    (R : FullProjectiveCosmicExternalization G)
    (p : Nat)
    (alpha : RationalSingularCohomology H.analytification (2 * p))
    (halpha : alpha ∈ rationalHodgeSubspace (H.hodgeBigrading p)) :
    ∃ Z : codimensionCycles V.X p,
      H.cycleClass p Z = alpha := by
  exact ((bigradedBettiHodgeStatement_iff_explicit_witness V H).1
      (bigradedBettiHodge_of_liveMassSurvival G S R)) p alpha
      ((mem_rationalHodgeSubspace_iff (H.hodgeBigrading p) alpha).1 halpha)

/-- There is no remaining finite-rank/countability restriction in the final
crown. -/
theorem full_limitless_rank_free_crown
    (G : GeometricCycleClassSpine V H)
    (hNV : SpineTowerNonvanishing G)
    (R : FullProjectiveCosmicExternalization G) :
    (∀ p : Nat,
      rationalHodgeSubspace (H.hodgeBigrading p) ≤
        LinearMap.range (H.cycleClass p))
    ∧ BigradedBettiHodgeStatement V H := by
  have h := bigradedBettiHodge G hNV R
  exact ⟨h, h⟩

/-- Rank-free crown with nonvanishing generated internally from the conserved
geometric charge. -/
theorem full_limitless_rank_free_crown_of_conservedCharge
    (G : GeometricCycleClassSpine V H)
    (D : SpineTowerConservedCharge G)
    (R : FullProjectiveCosmicExternalization G) :
    (∀ p : Nat,
      rationalHodgeSubspace (H.hodgeBigrading p) ≤
        LinearMap.range (H.cycleClass p))
    ∧ BigradedBettiHodgeStatement V H := by
  have h := bigradedBettiHodge_of_conservedCharge G D R
  exact ⟨h, h⟩

/-- Rank-free crown from the weaker live-mass geometry. -/
theorem full_limitless_rank_free_crown_of_liveMassSurvival
    (G : GeometricCycleClassSpine V H)
    (S : LiveSpineMassSurvival G)
    (R : FullProjectiveCosmicExternalization G) :
    (∀ p : Nat,
      rationalHodgeSubspace (H.hodgeBigrading p) ≤
        LinearMap.range (H.cycleClass p))
    ∧ BigradedBettiHodgeStatement V H := by
  have h := bigradedBettiHodge_of_liveMassSurvival G S R
  exact ⟨h, h⟩

#check SpineTowerNonvanishing
#check spineTowerNonvanishing_of_conservedCharge
#check LiveSpineMassSurvival
#check LiveSpineMassSurvival.cycleClass_spineNativeTower_ne_zero
#check LiveSpineMassSurvival.cycleClass_ne_zero_of_live
#check LiveSpineMassSurvival.spineHodgeSeed_ne_zero_of_live
#check LiveSpineMassSurvival.spineTowerNonvanishing
#check liveSpineMassSurvival_of_nativeMassBridge
#check FullProjectiveCosmicExternalization
#check canonicalCosmicNaturality_of_fullProjectiveExternalization
#check algebraicFiber_ne_bot_of_spineTower
#check bigradedBettiHodge
#check bigradedBettiHodge_of_conservedCharge
#check bigradedBettiHodge_of_liveMassSurvival
#check classicalHodgeTarget
#check classicalHodgeTarget_of_conservedCharge
#check classicalHodgeTarget_of_liveMassSurvival
#check every_hodge_class_has_native_cycle
#check every_hodge_class_has_native_cycle_of_conservedCharge
#check every_hodge_class_has_native_cycle_of_liveMassSurvival
#check full_limitless_rank_free_crown
#check full_limitless_rank_free_crown_of_conservedCharge
#check full_limitless_rank_free_crown_of_liveMassSurvival

#print axioms spineTowerNonvanishing_of_conservedCharge
#print axioms LiveSpineMassSurvival.cycleClass_spineNativeTower_ne_zero
#print axioms LiveSpineMassSurvival.cycleClass_ne_zero_of_live
#print axioms LiveSpineMassSurvival.spineTowerNonvanishing
#print axioms liveSpineMassSurvival_of_nativeMassBridge
#print axioms canonicalCosmicNaturality_of_fullProjectiveExternalization
#print axioms algebraicFiber_ne_bot_of_spineTower
#print axioms bigradedBettiHodge
#print axioms bigradedBettiHodge_of_conservedCharge
#print axioms bigradedBettiHodge_of_liveMassSurvival
#print axioms classicalHodgeTarget
#print axioms classicalHodgeTarget_of_liveMassSurvival
#print axioms every_hodge_class_has_native_cycle_of_liveMassSurvival
#print axioms full_limitless_rank_free_crown
#print axioms full_limitless_rank_free_crown_of_liveMassSurvival

end GSTClassicalHodgeFullLimitlessCrown
