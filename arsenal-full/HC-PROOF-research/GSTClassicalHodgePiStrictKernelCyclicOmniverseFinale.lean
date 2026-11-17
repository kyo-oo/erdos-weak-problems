import GSTClassicalHodgePiOneWordCyclicSeedOmniverseFinale
import GSTClassicalHodgeStrictCorrespondenceTransferFromPrimitives
import GSTClassicalHodgePrincipalCutSpectralFusion

/-!
# GST CLASSICAL HODGE — PI STRICT KERNEL CYCLIC OMNIVERSE FINALE

This is the geometry-first version of the one-observable Pi/GST attack.
No arbitrary ambient endomorphism, no projective-word algebra, and no finite
trace operator is supplied.

One actual strict bi-finite closed correspondence `K -> X x_C X` carries its
middle Betti class `[K]`.  Ordinary rational cup product and projection Gysin
construct the whole-Betti kernel action

    alpha |-> (p2)_* ([K] cup p1^* alpha).

The genuine point-cylinder/intersection/proper-pushforward packet proves that
this same action is the cycle class of the native finite-incidence operator on
all algebraic cycles.  Therefore preservation of the algebraic cycle-class
range is derived from low-level geometry.

If this forced kernel action has simple spectrum on the exact finite live
support of a target Hodge state, a single native cyclic source is enough for
GST Lagrange interpolation to isolate every live sheet.  Finite support then
collapses back to one genuine codimension-p cycle on the original projective
carrier.
-/

set_option maxHeartbeats 200000000
set_option maxRecDepth 1000000

noncomputable section

open scoped BigOperators
open AlgebraicGeometry

namespace GSTClassicalHodgePiStrictKernelCyclicOmniverseFinale

open GSTProjectiveOverC
open GSTGeometricRealizationStage2D
open GSTGeometricRealizationStage2F
open GSTGeometricRealizationStage2G
open GSTClassicalHodgeFiberedCosmology
open GSTClassicalHodgeAtomicSpan
open GSTClassicalHodgeFiniteSupportArsenalConjugation
open GSTClassicalHodgePiOmniverseCanonicalSupportSpectral
open GSTClassicalHodgeCyclicSpectralGeneration
open GSTClassicalHodgePrincipalCutSpectralFusion
open GSTClassicalHodgeBettiCupGysinPrimitives
open GSTClassicalHodgeAmbientCorrespondenceKernelAction
open GSTClassicalHodgeAmbientIntersectionFromPrimitives
open GSTClassicalHodgeSchemeFiniteCorrespondenceFirewall
open GSTClassicalHodgeGeometricCycleClassPointRigidity
open GSTClassicalHodgeCycleClassIntersectionPrimitives
open GSTClassicalHodgeStrictCorrespondenceTransferFromPrimitives
open GSTClassicalHodgeNativeCycleCosmicShadow
open GSTClassicalHodgeNativeTransferAddressIdentification
open GSTClassicalHodgeTransferSeedUniverse
open GSTTransferBridgeV2

variable {V : SmoothProjectiveComplexScheme}
variable {H : HodgeBigradedBettiData V}
variable {p : Nat}

/-- **LOWEST-LEVEL STRICT KERNEL SPECTRAL PACKET.**

The observable is definitionally forced from an actual closed correspondence
class and ordinary cup/Gysin topology.  `incidence` is the genuine geometric
point-fiber intersection packet which proves native/Betti synchronization. -/
structure StrictKernelCyclicPacket
    (alpha : ClassicalHodgeFiber V H p) where
  dimension : Nat
  topology : RationalBettiIntersectionPrimitives H.analytification dimension
  correspondence : SchemeBiFiniteClosedCorrespondence V
  kernel : MiddleBettiCorrespondenceKernel
    H.analytification dimension correspondence
  pointClass : PointBettiClass (V := V) p H.analytification
  pointClass_eq : ∀ x : CodimensionPoint V.X p,
    H.cycleClass p (codimensionPointCycle V.X p x) = pointClass x
  incidence : GeometricIncidencePrimitives
    (V := V) (H := H) (d := dimension) (p := p)
    topology correspondence kernel pointClass
  eigenvalue : Fin (liveRank alpha) → ℚ
  eigenvalue_injective : Function.Injective eigenvalue
  eigenvector : ∀ i : Fin (liveRank alpha),
    kernelAction H.analytification topology kernel (2 * p)
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

namespace StrictKernelCyclicPacket

variable {alpha : ClassicalHodgeFiber V H p}

/-- The forced kernel action preserves the genuine cycle-class range. -/
theorem kernelAction_range_stable
    (P : StrictKernelCyclicPacket (V := V) (H := H) alpha) :
    ∀ x,
      x ∈ LinearMap.range (H.cycleClass p) →
        kernelAction H.analytification P.topology P.kernel (2 * p) x ∈
          LinearMap.range (H.cycleClass p) := by
  intro x hx
  rcases hx with ⟨Z, rfl⟩
  let K := P.correspondence.toBiFiniteClosedCorrespondence.toFiniteClosedCorrespondence
  refine ⟨K.nativeOperator p Z, ?_⟩
  exact supplied_cycleClass_nativeOperator
    (V := V) (H := H) (d := P.dimension) (p := p)
    P.topology P.correspondence P.kernel P.pointClass
    P.pointClass_eq P.incidence Z

/-- Hence the forced geometric kernel action preserves the atomic algebraic
span. -/
theorem kernelAction_atomic_stable
    (P : StrictKernelCyclicPacket (V := V) (H := H) alpha) :
    ∀ x,
      x ∈ pointCycleClassSpan p (H.cycleClass p) →
        kernelAction H.analytification P.topology P.kernel (2 * p) x ∈
          pointCycleClassSpan p (H.cycleClass p) := by
  intro x hx
  have hrange : x ∈ LinearMap.range (H.cycleClass p) := by
    rwa [smoothProjective_cycleClass_range_eq_atomic_span V H p]
  have hout := P.kernelAction_range_stable x hrange
  rwa [smoothProjective_cycleClass_range_eq_atomic_span V H p] at hout

/-- The actual correspondence kernel therefore supplies the exact spectral
operator consumed by GST cyclic generation. -/
noncomputable def spectralOperator
    (P : StrictKernelCyclicPacket (V := V) (H := H) alpha) :
    ClassicalHodgeSpectralOperator V H p (Fin (liveRank alpha)) where
  basisIndex := liveBasisIndex alpha
  basisIndex_injective := (canonicalLiveWindow alpha).basisIndex_injective
  observable := kernelAction H.analytification P.topology P.kernel (2 * p)
  eigenvalue := P.eigenvalue
  eigenvalue_injective := P.eigenvalue_injective
  eigenvector := P.eigenvector
  atomic_stable := P.kernelAction_atomic_stable

/-- One actual native cycle supplies the cyclic spectral source. -/
theorem cyclic_seed_atomic
    (P : StrictKernelCyclicPacket (V := V) (H := H) alpha) :
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

/-- **KERNEL GEOMETRY + ONE CYCLIC SOURCE ALGEBRAIZES EVERY LIVE SHEET.** -/
theorem live_basis_algebraic
    (P : StrictKernelCyclicPacket (V := V) (H := H) alpha)
    (i : Fin (liveRank alpha)) :
    (classicalHodgeBasis V H p (liveBasisIndex alpha i)).1 ∈
      pointCycleClassSpan p (H.cycleClass p) := by
  exact P.spectralOperator.selected_basis_algebraic_of_cyclic_seed
    P.coefficient P.coefficient_ne_zero P.cyclic_seed_atomic i

/-- Every basis direction in the target support is algebraic. -/
theorem support_basis_algebraic
    (P : StrictKernelCyclicPacket (V := V) (H := H) alpha)
    (i : HodgeSupportIndex alpha) :
    (classicalHodgeBasis V H p i.1).1 ∈
      pointCycleClassSpan p (H.cycleClass p) := by
  obtain ⟨r, hr⟩ := supportIndex_has_canonicalSlot alpha i
  have h := P.live_basis_algebraic r
  have hr' : liveBasisIndex alpha r = i.1 := hr
  simpa [hr'] using h

/-- **PI TARGET COLLAPSE FROM LOW-LEVEL CORRESPONDENCE GEOMETRY.** -/
theorem target_cycle
    (P : StrictKernelCyclicPacket (V := V) (H := H) alpha) :
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

/-- The native cyclic source and the correspondence action live over the same
limitless weight-p transfer ray. -/
theorem seed_limitless_address
    (P : StrictKernelCyclicPacket (V := V) (H := H) alpha) :
    pureWeightToUniversalAddress
        (nativeCycleCosmicShadow V p P.seedCycle) =
      nativeCycleMass V p P.seedCycle •
        rationalizeCompactAddress (compactClMono p) := by
  exact nativeCycle_shadow_eq_mass_transfer V p P.seedCycle

end StrictKernelCyclicPacket

/-- Pi-wide exact Hodge landing when every nonzero target admits one
geometry-built strict kernel spectral packet. -/
theorem bigradedBettiHodge_of_strictKernelCyclicPackets
    (packet :
      ∀ q : Nat, ∀ alpha : ClassicalHodgeFiber V H q,
        alpha ≠ 0 →
          Nonempty
            (StrictKernelCyclicPacket
              (V := V) (H := H) (p := q) alpha)) :
    BigradedBettiHodgeStatement V H := by
  intro q x hx
  let alpha : ClassicalHodgeFiber V H q := ⟨x, hx⟩
  by_cases halpha : alpha = 0
  · have hx0 : x = 0 := congrArg Subtype.val halpha
    subst x
    exact LinearMap.zero_mem _
  · exact (Classical.choice (packet q alpha halpha)).target_cycle

#check StrictKernelCyclicPacket
#check StrictKernelCyclicPacket.kernelAction_range_stable
#check StrictKernelCyclicPacket.kernelAction_atomic_stable
#check StrictKernelCyclicPacket.spectralOperator
#check StrictKernelCyclicPacket.live_basis_algebraic
#check StrictKernelCyclicPacket.target_cycle
#check StrictKernelCyclicPacket.seed_limitless_address
#check bigradedBettiHodge_of_strictKernelCyclicPackets

#print axioms StrictKernelCyclicPacket.kernelAction_range_stable
#print axioms StrictKernelCyclicPacket.live_basis_algebraic
#print axioms StrictKernelCyclicPacket.target_cycle
#print axioms bigradedBettiHodge_of_strictKernelCyclicPackets

end GSTClassicalHodgePiStrictKernelCyclicOmniverseFinale
