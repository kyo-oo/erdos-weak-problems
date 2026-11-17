import GSTClassicalHodgePiOneWordCyclicSeedOmniverseFinale
import GSTClassicalHodgeStrictCorrespondenceBettiTracePushPull
import GSTClassicalHodgePrincipalCutSpectralFusion

/-!
# GST CLASSICAL HODGE — PI STRICT-TRACE CYCLIC OMNIVERSE FINALE

This file removes the free projective-word language from the class-local
spectral attack.  The unique observable is built directly from one genuine
scheme-bi-finite closed correspondence

    K -> X x_C X.

Its intrinsic analytic span gives the two honest Betti pullbacks.  A nonzero
finite Betti trace on the right leg constructs the total whole-Betti push-pull

    T_K = deg(r)^(-1) Tr_r o l^*.

Point compatibility identifies this whole-Betti action with the actual native
finite-incidence action on point cycles; point normal form globalizes the
commuting square to every native cycle.  Hence algebraic-cycle classes are
stable under `T_K` as a theorem.

If `T_K` has pairwise-distinct eigenvalues on the exact finite live support of
one target Hodge state and one actual native cyclic source has a nonzero
coordinate in every selected eigendirection, GST polynomial interpolation
extracts every live Hodge sheet and the finite support sum reconstructs the
target class.

The operator is therefore not an arbitrary linear extension: it is generated
by one actual closed correspondence carrier, its intrinsic analytification,
its finite trace and its genuine point-incidence geometry.
-/

set_option maxHeartbeats 200000000
set_option maxRecDepth 1000000

noncomputable section

open scoped BigOperators
open AlgebraicGeometry

namespace GSTClassicalHodgePiStrictTraceCyclicOmniverseFinale

open GSTProjectiveOverC
open GSTGeometricRealizationStage2D
open GSTGeometricRealizationStage2F
open GSTGeometricRealizationStage2G
open GSTClassicalHodgeFiberedCosmology
open GSTClassicalHodgeAtomicSpan
open GSTClassicalHodgeFiniteSupportArsenalConjugation
open GSTClassicalHodgePiOmniverseCanonicalSupportSpectral
open GSTClassicalHodgePrincipalCutSpectralFusion
open GSTClassicalHodgeProjectiveSpectralCover
open GSTClassicalHodgeCyclicSpectralGeneration
open GSTClassicalHodgeSchemeFiniteCorrespondenceFirewall
open GSTClassicalHodgeStrictCorrespondenceAnalyticSpan
open GSTClassicalHodgeStrictCorrespondenceBettiTracePushPull
open GSTClassicalHodgeGradedFiniteClosedCorrespondence
open GSTClassicalHodgeNativeCycleCosmicShadow
open GSTClassicalHodgeNativeTransferAddressIdentification
open GSTClassicalHodgeTransferSeedUniverse
open GSTTransferBridgeV2

variable {V : SmoothProjectiveComplexScheme}
variable {H : HodgeBigradedBettiData V}
variable {p : Nat}

/-- **ONE STRICT CORRESPONDENCE / ONE CYCLIC NATIVE SOURCE.**

Everything geometric is attached to one actual bi-finite closed
correspondence.  The observable is its normalized finite-trace push-pull. -/
structure StrictTraceCyclicPacket
    (alpha : ClassicalHodgeFiber V H p) where
  correspondence : SchemeBiFiniteClosedCorrespondence V
  trace : RightFiniteBettiTrace
    H.analytification correspondence (2 * p)
  pointCompatibility :
    PointCycleCompatibility (n := p) correspondence trace
  eigenvalue : Fin (liveRank alpha) → ℚ
  eigenvalue_injective : Function.Injective eigenvalue
  eigenvector : ∀ i : Fin (liveRank alpha),
    trace.pushPull
        (classicalHodgeBasis V H p (liveBasisIndex alpha i)).1 =
      eigenvalue i •
        (classicalHodgeBasis V H p (liveBasisIndex alpha i)).1
  coefficient : Fin (liveRank alpha) → ℚ
  coefficient_ne_zero : ∀ i, coefficient i ≠ 0
  seedCycle : codimensionCycles V.X p
  seed_class :
    H.cycleClass p seedCycle =
      ∑ i : Fin (liveRank alpha),
        coefficient i •
          (classicalHodgeBasis V H p (liveBasisIndex alpha i)).1

namespace StrictTraceCyclicPacket

variable {alpha : ClassicalHodgeFiber V H p}

/-- The strict traced correspondence preserves the genuine cycle-class range.
This follows from point compatibility plus the globalized native-incidence
commuting square; it is not a field of the packet. -/
theorem pushPull_range_stable
    (P : StrictTraceCyclicPacket (V := V) (H := H) alpha) :
    ∀ x,
      x ∈ LinearMap.range (H.cycleClass p) →
        P.trace.pushPull x ∈ LinearMap.range (H.cycleClass p) := by
  intro x hx
  rcases hx with ⟨Z, rfl⟩
  let K := P.correspondence.toBiFiniteClosedCorrespondence.toFiniteClosedCorrespondence
  refine ⟨K.gradedNativeCycleOperator p p Z, ?_⟩
  exact P.pointCompatibility.cycleClass_natural Z

/-- Therefore the same actual push-pull preserves the atomic algebraic span. -/
theorem pushPull_atomic_stable
    (P : StrictTraceCyclicPacket (V := V) (H := H) alpha) :
    ∀ x,
      x ∈ pointCycleClassSpan p (H.cycleClass p) →
        P.trace.pushPull x ∈ pointCycleClassSpan p (H.cycleClass p) := by
  intro x hx
  have hrange : x ∈ LinearMap.range (H.cycleClass p) := by
    rwa [smoothProjective_cycleClass_range_eq_atomic_span V H p]
  have hout := P.pushPull_range_stable x hrange
  rwa [smoothProjective_cycleClass_range_eq_atomic_span V H p] at hout

/-- The genuine strict push-pull is a geometry-ready classical Hodge spectral
operator on the exact live packet. -/
noncomputable def spectralOperator
    (P : StrictTraceCyclicPacket (V := V) (H := H) alpha) :
    ClassicalHodgeSpectralOperator V H p (Fin (liveRank alpha)) where
  basisIndex := liveBasisIndex alpha
  basisIndex_injective := (canonicalLiveWindow alpha).basisIndex_injective
  observable := P.trace.pushPull
  eigenvalue := P.eigenvalue
  eigenvalue_injective := P.eigenvalue_injective
  eigenvector := P.eigenvector
  atomic_stable := P.pushPull_atomic_stable

/-- The one native source is an actual algebraic cyclic vector for the strict
correspondence spectral action. -/
theorem cyclic_seed_atomic
    (P : StrictTraceCyclicPacket (V := V) (H := H) alpha) :
    (∑ i : Fin (liveRank alpha),
      P.coefficient i •
        (classicalHodgeBasis V H p (liveBasisIndex alpha i)).1) ∈
      pointCycleClassSpan p (H.cycleClass p) := by
  have hrange :
      (∑ i : Fin (liveRank alpha),
        P.coefficient i •
          (classicalHodgeBasis V H p (liveBasisIndex alpha i)).1) ∈
        LinearMap.range (H.cycleClass p) :=
    ⟨P.seedCycle, P.seed_class⟩
  rwa [smoothProjective_cycleClass_range_eq_atomic_span V H p] at hrange

/-- **STRICT TRACE + ONE CYCLIC SOURCE ALGEBRAIZES EVERY LIVE SHEET.** -/
theorem live_basis_algebraic
    (P : StrictTraceCyclicPacket (V := V) (H := H) alpha)
    (i : Fin (liveRank alpha)) :
    (classicalHodgeBasis V H p (liveBasisIndex alpha i)).1 ∈
      pointCycleClassSpan p (H.cycleClass p) := by
  exact P.spectralOperator.selected_basis_algebraic_of_cyclic_seed
    P.coefficient P.coefficient_ne_zero P.cyclic_seed_atomic i

/-- Every basis direction actually occurring in the target is algebraic. -/
theorem support_basis_algebraic
    (P : StrictTraceCyclicPacket (V := V) (H := H) alpha)
    (i : HodgeSupportIndex alpha) :
    (classicalHodgeBasis V H p i.1).1 ∈
      pointCycleClassSpan p (H.cycleClass p) := by
  obtain ⟨r, hr⟩ := supportIndex_has_canonicalSlot alpha i
  have h := P.live_basis_algebraic r
  have hr' : liveBasisIndex alpha r = i.1 := hr
  simpa [hr'] using h

/-- **STRICT-SCHEME TARGET COLLAPSE.**  The target Hodge state is represented
by one genuine native cycle on the original projective scheme. -/
theorem target_cycle
    (P : StrictTraceCyclicPacket (V := V) (H := H) alpha) :
    ∃ Z : codimensionCycles V.X p,
      H.cycleClass p Z = alpha.1 := by
  have hmem :
      alpha.1 ∈ pointCycleClassSpan p (H.cycleClass p) := by
    rw [hodgeClass_eq_support_sum alpha]
    apply Submodule.sum_mem
    intro i hi
    exact (pointCycleClassSpan p (H.cycleClass p)).smul_mem
      ((classicalHodgeBasis V H p).repr alpha i.1)
      (P.support_basis_algebraic i)
  exact pointCycleClassSpan_le_cycleClass_range
    p (H.cycleClass p) hmem

/-- The one cyclic source remains tethered to the original limitless transfer
ray, so the strict scheme correspondence acts inside the same Pi/GST common
base rather than in a detached classical universe. -/
theorem seed_limitless_address
    (P : StrictTraceCyclicPacket (V := V) (H := H) alpha) :
    pureWeightToUniversalAddress
        (nativeCycleCosmicShadow V p P.seedCycle) =
      nativeCycleMass V p P.seedCycle •
        rationalizeCompactAddress (compactClMono p) := by
  exact nativeCycle_shadow_eq_mass_transfer V p P.seedCycle

end StrictTraceCyclicPacket

/-- Pi-wide exact rational Hodge landing from one genuine strict traced
correspondence and one native cyclic source for every nonzero target state. -/
theorem bigradedBettiHodge_of_strictTraceCyclicPackets
    (packet :
      ∀ q : Nat, ∀ alpha : ClassicalHodgeFiber V H q,
        alpha ≠ 0 →
          Nonempty
            (StrictTraceCyclicPacket
              (V := V) (H := H) (p := q) alpha)) :
    BigradedBettiHodgeStatement V H := by
  intro q x hx
  let alpha : ClassicalHodgeFiber V H q := ⟨x, hx⟩
  by_cases halpha : alpha = 0
  · have hx0 : x = 0 := congrArg Subtype.val halpha
    subst x
    exact LinearMap.zero_mem _
  · exact (Classical.choice (packet q alpha halpha)).target_cycle

#check StrictTraceCyclicPacket
#check StrictTraceCyclicPacket.pushPull_range_stable
#check StrictTraceCyclicPacket.pushPull_atomic_stable
#check StrictTraceCyclicPacket.spectralOperator
#check StrictTraceCyclicPacket.live_basis_algebraic
#check StrictTraceCyclicPacket.target_cycle
#check StrictTraceCyclicPacket.seed_limitless_address
#check bigradedBettiHodge_of_strictTraceCyclicPackets

#print axioms StrictTraceCyclicPacket.pushPull_range_stable
#print axioms StrictTraceCyclicPacket.live_basis_algebraic
#print axioms StrictTraceCyclicPacket.target_cycle
#print axioms bigradedBettiHodge_of_strictTraceCyclicPackets

end GSTClassicalHodgePiStrictTraceCyclicOmniverseFinale
