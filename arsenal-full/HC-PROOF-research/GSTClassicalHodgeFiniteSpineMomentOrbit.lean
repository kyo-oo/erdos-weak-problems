import GSTClassicalHodgeLimitlessSpinePropagation
import GSTClassicalHodgeProjectiveCorrespondenceCosmicRealization
import GSTClassicalHodgeSynchronizedDefectOrbit
import GSTClassicalHodgeBasisCycleBridge

/-!
# GST CLASSICAL HODGE — FINITE SPINE MOMENT / PROJECTIVE ORBIT CROWN

The previous geometry-first crowns reduced the classical Hodge landing to two
large semantic interfaces:

* a tower charge strong enough to keep the normalized projective spine nonzero
  in every natural weight;
* projective realizations of complete Hodge-fiber operators.

Both interfaces are stronger than the orbit argument actually uses.

First, an actual smooth projective carrier is finite-dimensional.  There is no
reason to demand a nonzero projective spine in weights whose genuine `(p,p)`
Hodge fiber is already zero.  For one requested weight `top`, only the finite
prefix from weight zero through `top` matters.  We therefore introduce a
finite spine-moment chain.  It carries a rational cohomological readout and the
exact limitless successor recursion only below `top`.  One nonzero base moment
then proves the canonical normalized spine seed at `top` is nonzero.  No
all-weight nonvanishing package and no total point-mass functional occurs.

Second, synchronized-defect extraction never needs a projective operator to
agree with a prescribed matrix unit on the whole Hodge fiber.  Once one live
algebraic source state is known, it only needs the action on that one state.
We therefore use one genuine projective-correspondence kernel per target basis
direction and require only its cohomological image of the selected live source.
The exact cycle-class commuting square is supplied by the existing genuine
projective-correspondence algebra.

This produces a strictly smaller geometry interface:

  finite relevant spine moment
    + one projective-correspondence source action per target
      -> one nonzero algebraic orbit seed
      -> every Hodge basis direction
      -> exact Stage-2G Hodge landing.

No arbitrary cycle operator, no all-Hodge operator agreement, no coefficient
mass bridge, and no nonzero tower beyond the requested weight is used.
-/

set_option maxHeartbeats 90000000
set_option maxRecDepth 1000000

noncomputable section

open AlgebraicGeometry

namespace GSTClassicalHodgeFiniteSpineMomentOrbit

open GSTProjectiveOverC
open GSTGeometricRealizationStage2D
open GSTGeometricRealizationStage2F
open GSTGeometricRealizationStage2G
open GSTClassicalHodgeFiberedCosmology
open GSTClassicalHodgeRankFreeArsenalIrreducibility
open GSTClassicalHodgeGeometricCycleClassSpine
open GSTClassicalHodgeLimitlessSpinePropagation
open GSTClassicalHodgeLimitlessTowerOrbitCrown
open GSTClassicalHodgeSynchronizedDefectOrbit
open GSTClassicalHodgeProjectiveCorrespondenceAlgebra
open GSTClassicalHodgeProjectiveCorrespondenceCosmicRealization

variable {V : SmoothProjectiveComplexScheme}
variable {H : HodgeBigradedBettiData V}

/-- A finite cohomological detector for the canonical normalized projective
spine up to one requested weight.

Only the prefix `0,...,top` is constrained.  In particular this structure does
not assert that the projective spine remains nonzero in irrelevant weights
above the geometric dimension. -/
structure FiniteSpineMomentChain
    (G : GeometricCycleClassSpine V H)
    (top : Nat) where
  read :
    ∀ q : Nat,
      RationalSingularCohomology H.analytification (2 * q) →ₗ[ℚ] ℚ
  base_ne_zero :
    read 0 (spineHodgeSeed G 0).1 ≠ 0
  successor_read :
    ∀ q : Nat, q < top →
      read (q + 1)
          ((G.principalCutPair q).cohomologyOperator
            (spineHodgeSeed G q).1) =
        successorScalar q * read q (spineHodgeSeed G q).1

namespace FiniteSpineMomentChain

/-- The normalized spine has constant finite moment throughout every level of
the requested prefix. -/
theorem read_spineHodgeSeed_eq_base
    {G : GeometricCycleClassSpine V H}
    {top : Nat}
    (D : FiniteSpineMomentChain G top) :
    ∀ q : Nat, q ≤ top →
      D.read q (spineHodgeSeed G q).1 =
        D.read 0 (spineHodgeSeed G 0).1 := by
  intro q hq
  induction q with
  | zero => rfl
  | succ q ih =>
      have hlt : q < top := by omega
      have hqle : q ≤ top := by omega
      change
        D.read (q + 1)
            ((successorScalar q)⁻¹ •
              (G.principalCutPair q).cohomologyOperator
                (spineHodgeSeed G q).1) =
          D.read 0 (spineHodgeSeed G 0).1
      rw [LinearMap.map_smul]
      rw [D.successor_read q hlt]
      rw [ih hqle]
      simp [successorScalar_ne_zero]

/-- The requested top-weight spine seed is nonzero.  This is the exact amount
of nonvanishing needed by the synchronized orbit argument. -/
theorem top_spineHodgeSeed_ne_zero
    {G : GeometricCycleClassSpine V H}
    {top : Nat}
    (D : FiniteSpineMomentChain G top) :
    spineHodgeSeed G top ≠ 0 := by
  intro hz
  have hconst := D.read_spineHodgeSeed_eq_base top (le_refl top)
  rw [hz] at hconst
  have hzero : D.read top
      (0 : RationalSingularCohomology H.analytification (2 * top)) = 0 :=
    map_zero _
  exact D.base_ne_zero (hconst.symm.trans hzero)

/-- The geometry-built native spine and its now-proved nonzero Hodge class give
one synchronized live orbit seed at the requested weight. -/
noncomputable def topOrbitSeed
    {G : GeometricCycleClassSpine V H}
    {top : Nat}
    (D : FiniteSpineMomentChain G top) :
    NativeHodgeOrbitSeed (V := V) (H := H) (p := top) where
  cycle := spineNativeTower G top
  hodge := spineHodgeSeed G top
  hodge_ne_zero := D.top_spineHodgeSeed_ne_zero
  class_eq := spineNativeTower_cycleClass G top

/-- The requested weight already has a nonzero algebraic Hodge direction. -/
theorem top_algebraicHodgeSubspace_ne_bot
    {G : GeometricCycleClassSpine V H}
    {top : Nat}
    (D : FiniteSpineMomentChain G top) :
    AlgebraicHodgeSubspace V H top ≠ ⊥ :=
  algebraicHodgeSubspace_ne_bot_of_spineSeed G top
    D.top_spineHodgeSeed_ne_zero

end FiniteSpineMomentChain

/-! ## One-source projective-correspondence extraction -/

variable {p : Nat}

/-- One genuine projective-correspondence operator whose cohomological action
is prescribed only on the selected live source state.

This is strictly weaker than realizing a complete rank-one matrix unit, or two
primitive generators, on the entire Hodge fiber.  The native operator remains
a member of the actual projective-correspondence span. -/
structure ProjectiveLiveSourceTarget
    (G : GeometricCycleClassSpine V H)
    (S : NativeHodgeOrbitSeed (V := V) (H := H) (p := p))
    (j : ClassicalHodgeBasisIndex V H p) where
  kernel : ProjectiveNativeKernel V p
  source_action :
    (projectiveCorrespondencePair G kernel).cohomologyOperator S.hodge.1 =
      (classicalHodgeBasis V H p).repr S.hodge S.sourceIndex •
        (classicalHodgeBasis V H p j).1

namespace ProjectiveLiveSourceTarget

/-- Normalize the genuine projective-correspondence image of the live native
source by its nonzero selected coordinate. -/
noncomputable def targetCycle
    {G : GeometricCycleClassSpine V H}
    {S : NativeHodgeOrbitSeed (V := V) (H := H) (p := p)}
    {j : ClassicalHodgeBasisIndex V H p}
    (R : ProjectiveLiveSourceTarget G S j) :
    codimensionCycles V.X p :=
  let c := (classicalHodgeBasis V H p).repr S.hodge S.sourceIndex
  c⁻¹ • (projectiveCorrespondencePair G R.kernel).cycleOperator S.cycle

/-- **ONE-SOURCE PROJECTIVE ORBIT EXTRACTION.**
The normalized projective-correspondence image is an actual native cycle whose
cycle class is exactly the requested Hodge basis vector. -/
theorem targetCycle_spec
    {G : GeometricCycleClassSpine V H}
    {S : NativeHodgeOrbitSeed (V := V) (H := H) (p := p)}
    {j : ClassicalHodgeBasisIndex V H p}
    (R : ProjectiveLiveSourceTarget G S j) :
    H.cycleClass p R.targetCycle =
      (classicalHodgeBasis V H p j).1 := by
  let c := (classicalHodgeBasis V H p).repr S.hodge S.sourceIndex
  have hc : c ≠ 0 := S.sourceCoefficient_ne_zero
  have hpair :=
    (projectiveCorrespondencePair G R.kernel).cycleClass_cycleOperator S.cycle
  rw [S.class_eq, R.source_action] at hpair
  unfold targetCycle
  rw [LinearMap.map_smul, hpair]
  simp [c, hc]

end ProjectiveLiveSourceTarget

/-- A one-source projective realization for every target basis direction gives
an explicit basis-cycle bridge. -/
noncomputable def projectiveLiveSourceBasisBridge
    (G : GeometricCycleClassSpine V H)
    (S : NativeHodgeOrbitSeed (V := V) (H := H) (p := p))
    (R : ∀ j : ClassicalHodgeBasisIndex V H p,
      ProjectiveLiveSourceTarget G S j) :
    HodgeConjecture.HodgeBasisCycleBridge V H p where
  basisCycle j := (R j).targetCycle
  basisCycle_spec j := (R j).targetCycle_spec

/-- Fixed-weight Hodge landing from one nonzero algebraic spine seed and one
projective-correspondence source action per target basis direction. -/
theorem hodge_weight_of_projective_live_source
    (G : GeometricCycleClassSpine V H)
    (S : NativeHodgeOrbitSeed (V := V) (H := H) (p := p))
    (R : ∀ j : ClassicalHodgeBasisIndex V H p,
      ProjectiveLiveSourceTarget G S j) :
    rationalHodgeSubspace (H.hodgeBigrading p) ≤
      LinearMap.range (H.cycleClass p) := by
  intro alpha halpha
  exact HodgeConjecture.hodge_class_has_cycle_of_basis_bridge
    V H (projectiveLiveSourceBasisBridge G S R) alpha halpha

/-- **FINITE RELEVANT-SPINE + ONE-SOURCE PROJECTIVE CROWN.**

For each weight whose genuine rational `(p,p)` Hodge fiber is nonzero, use only
a finite detector prefix ending at that weight.  The resulting canonical live
spine seed is then spread across that weight by genuine projective
correspondences whose action is constrained only on the selected source.

Zero Hodge fibers require neither a moment chain nor projective data. -/
theorem bigradedBettiHodge_of_finite_spine_moments_and_projective_live_source
    (G : GeometricCycleClassSpine V H)
    (D : ∀ p : Nat,
      rationalHodgeSubspace (H.hodgeBigrading p) ≠ ⊥ →
        FiniteSpineMomentChain G p)
    (R : ∀ p : Nat,
      ∀ hp : rationalHodgeSubspace (H.hodgeBigrading p) ≠ ⊥,
      ∀ j : ClassicalHodgeBasisIndex V H p,
        ProjectiveLiveSourceTarget G (D p hp).topOrbitSeed j) :
    BigradedBettiHodgeStatement V H := by
  intro p alpha halpha
  by_cases hp : rationalHodgeSubspace (H.hodgeBigrading p) = ⊥
  · have hzero : alpha = 0 := by
      have hz : alpha ∈
          (⊥ : Submodule ℚ
            (RationalSingularCohomology H.analytification (2 * p))) := by
        simpa [hp] using halpha
      simpa using hz
    subst alpha
    exact ⟨0, by simp⟩
  · exact hodge_weight_of_projective_live_source
      G (D p hp).topOrbitSeed (R p hp) halpha

/-- Elementwise witness form of the finite-spine/projective-live-source crown. -/
theorem every_hodge_class_has_native_cycle_of_finite_spine_moments
    (G : GeometricCycleClassSpine V H)
    (D : ∀ p : Nat,
      rationalHodgeSubspace (H.hodgeBigrading p) ≠ ⊥ →
        FiniteSpineMomentChain G p)
    (R : ∀ p : Nat,
      ∀ hp : rationalHodgeSubspace (H.hodgeBigrading p) ≠ ⊥,
      ∀ j : ClassicalHodgeBasisIndex V H p,
        ProjectiveLiveSourceTarget G (D p hp).topOrbitSeed j)
    (p : Nat)
    (alpha : RationalSingularCohomology H.analytification (2 * p))
    (halpha : alpha ∈ rationalHodgeSubspace (H.hodgeBigrading p)) :
    ∃ Z : codimensionCycles V.X p,
      H.cycleClass p Z = alpha := by
  exact bigradedBettiHodge_of_finite_spine_moments_and_projective_live_source
    G D R p halpha

#check FiniteSpineMomentChain
#check FiniteSpineMomentChain.read_spineHodgeSeed_eq_base
#check FiniteSpineMomentChain.top_spineHodgeSeed_ne_zero
#check FiniteSpineMomentChain.topOrbitSeed
#check FiniteSpineMomentChain.top_algebraicHodgeSubspace_ne_bot
#check ProjectiveLiveSourceTarget
#check ProjectiveLiveSourceTarget.targetCycle
#check ProjectiveLiveSourceTarget.targetCycle_spec
#check projectiveLiveSourceBasisBridge
#check hodge_weight_of_projective_live_source
#check bigradedBettiHodge_of_finite_spine_moments_and_projective_live_source
#check every_hodge_class_has_native_cycle_of_finite_spine_moments

#print axioms FiniteSpineMomentChain.read_spineHodgeSeed_eq_base
#print axioms FiniteSpineMomentChain.top_spineHodgeSeed_ne_zero
#print axioms FiniteSpineMomentChain.topOrbitSeed
#print axioms ProjectiveLiveSourceTarget.targetCycle_spec
#print axioms hodge_weight_of_projective_live_source
#print axioms bigradedBettiHodge_of_finite_spine_moments_and_projective_live_source
#print axioms every_hodge_class_has_native_cycle_of_finite_spine_moments

end GSTClassicalHodgeFiniteSpineMomentOrbit