import GSTClassicalHodgeProjectiveSpectralCover
import GSTClassicalHodgePiOmniverseCanonicalSupportSpectral
import GSTClassicalHodgePiUnboundedOmniverseCrown

/-!
# GST CLASSICAL HODGE — PI PROJECTIVE-SPECTRAL OMNIVERSE FINALE

This is the class-local form of the handwritten Pi/GST construction with the
geometric burden compressed as far as the current projective word machinery
allows without identifying Hodge labels with native cycles.

For one nonzero Hodge state `alpha` we use exactly its finite live support.
On that support it is enough to have ONE genuine finite projective operator
word with distinct rational eigenvalues.  The word automatically preserves the
actual algebraic cycle-class span because its primitives are genuine
projective transports.  Different live coordinates may be witnessed by
different algebraic combinations; finite hyperplane avoidance over Q then
assembles one cyclic algebraic seed touching every active coordinate.

The same support is simultaneously:

* the exact support in the finite rational branch-collapse identity;
* the exact GST N-cohomology packet;
* the finite spectral packet of the genuine projective word;
* embedded in the three-sector branch omniverse whose worlds persist through
  every finite level of the unbounded higher-causal tower.

Polynomial spectral extraction produces each live Hodge basis sheet as an
actual native codimension-p cycle, and the finite support sum reconstructs the
original class on the same projective carrier.

No all-events strict materialization, matrix-unit correspondence family,
projective point visible in every coordinate, native-mass bridge, global finite
rank, saturation principle, or defect-extinction assumption occurs here.
-/

set_option maxHeartbeats 180000000
set_option maxRecDepth 1000000

noncomputable section

open scoped BigOperators
open AlgebraicGeometry

namespace GSTClassicalHodgePiProjectiveSpectralOmniverseFinale

open GSTProjectiveOverC
open GSTGeometricRealizationStage2D
open GSTGeometricRealizationStage2F
open GSTGeometricRealizationStage2G
open GSTClassicalHodgeFiberedCosmology
open GSTClassicalHodgeRankFreeArsenalIrreducibility
open GSTClassicalHodgeGeometricCycleClassSpine
open GSTClassicalHodgeProjectiveSpectralCover
open GSTClassicalHodgePiOmniverseCanonicalSupportSpectral
open GSTClassicalHodgeOmniverseCausalBranchPacket
open GSTClassicalHodgePiUnboundedOmniverseCrown
open GSTGraphV2OmniversalCore

variable {V : SmoothProjectiveComplexScheme}
variable {H : HodgeBigradedBettiData V}
variable {p : Nat}

/-- A single projective word diagonalized on exactly the live support of one
requested Hodge state.  Coordinate visibility is deliberately weak and
coordinatewise: different coordinates may use different algebraic witnesses.
The infinite-field assembly theorem turns them into one simultaneous cyclic
seed internally. -/
structure CanonicalProjectiveSpectralPacket
    (G : GeometricCycleClassSpine V H)
    (alpha : ClassicalHodgeFiber V H p) where
  spectral :
    ProjectiveWordSpectralFamily
      (V := V) (H := H) (p := p) G (Fin (liveRank alpha))
  basisIndex_eq : spectral.basisIndex = liveBasisIndex alpha
  visible : ∀ i : Fin (liveRank alpha), spectral.CoordinateVisible i

namespace CanonicalProjectiveSpectralPacket

variable {G : GeometricCycleClassSpine V H}
variable {alpha : ClassicalHodgeFiber V H p}

/-- The canonical packet is literally a finite projective spectral cover of
`alpha`; no larger auxiliary cover is introduced. -/
noncomputable def toFiniteProjectiveSpectralCover
    (P : CanonicalProjectiveSpectralPacket G alpha) :
    FiniteProjectiveSpectralCover G alpha where
  rank := liveRank alpha
  spectral := P.spectral
  covers_live_support := by
    intro i
    obtain ⟨r, hr⟩ := supportIndex_has_canonicalSlot alpha i
    refine ⟨r, ?_⟩
    rw [P.basisIndex_eq]
    exact hr
  visible := P.visible

/-- **ONE PROJECTIVE WORD / CANONICAL SUPPORT LANDING.**
The packet constructs an actual native codimension-p cycle representing the
whole requested Hodge class. -/
theorem target_cycle
    (P : CanonicalProjectiveSpectralPacket G alpha) :
    ∃ Z : codimensionCycles V.X p,
      H.cycleClass p Z = alpha.1 := by
  exact P.toFiniteProjectiveSpectralCover.exists_native_cycle

/-- Every live basis direction is individually algebraic after the one-word
spectral extraction. -/
theorem live_basis_algebraic
    (P : CanonicalProjectiveSpectralPacket G alpha)
    (i : HodgeSupportIndex alpha) :
    (classicalHodgeBasis V H p i.1).1 ∈
      GSTClassicalHodgeAtomicSpan.pointCycleClassSpan p (H.cycleClass p) := by
  exact P.toFiniteProjectiveSpectralCover.live_basis_algebraic i

/-- The coordinatewise witnesses are assembled internally into one algebraic
cyclic seed whose coefficient on every live slot is nonzero. -/
theorem exists_cyclic_atomic_seed
    (P : CanonicalProjectiveSpectralPacket G alpha) :
    ∃ a : Fin (liveRank alpha) → ℚ,
      (∀ i, a i ≠ 0) ∧
      (∑ i : Fin (liveRank alpha),
        a i • (classicalHodgeBasis V H p
          (liveBasisIndex alpha i)).1) ∈
        GSTClassicalHodgeAtomicSpan.pointCycleClassSpan p (H.cycleClass p) := by
  obtain ⟨a, hne, halg⟩ := P.spectral.exists_cyclic_atomic_seed P.visible
  refine ⟨a, hne, ?_⟩
  simpa [P.basisIndex_eq] using halg

end CanonicalProjectiveSpectralPacket

/-- The canonical projective spectral packet and the N-cohomology branch packet
have the same finite index universe. -/
theorem packet_has_exact_ncohomology
    (depth : Nat)
    (alpha : ClassicalHodgeFiber V H p) :
    ∃ basis : Fin (liveRank alpha) →
        GSTNCohomology.nCohoClasses depth (liveSupportNShape alpha) 1,
      ∀ i : Fin (liveRank alpha),
        (basis i).1 i =
          GSTNCohomology.towerWindow depth
            ((liveSupportNShape alpha).channel i) 1 := by
  simpa using canonicalWindow_has_ncohomology_packet
    (V := V) (H := H) (p := p) depth alpha

/-- Every target basis branch selected by the finite support lives in the full
three-sector GST graph and persists through every finite higher-causal level.
This statement is pure omniverse geometry and does not smuggle in algebraicity. -/
theorem supportBranch_has_unbounded_causal_certificate
    (alpha : ClassicalHodgeFiber V H p)
    (halpha : alpha ≠ 0)
    (s : Sector)
    (j : ClassicalHodgeBasisIndex V H p) :
    ∃ i : HodgeSupportIndex alpha,
      hodgeCoordinate i.1 alpha ≠ 0 ∧
      (hodgeBranchGraph (V := V) (H := H) (p := p)).Event
        ⟨Sector.gstPlus, alpha⟩
        ⟨s, hodgeMatrixUnit i.1 j alpha⟩
      ∧ ∀ n : Nat,
        ∃ c : (hodgeHigherCausalCosmos
          (V := V) (H := H) (p := p)).Cell n,
          c = ⟨s, hodgeMatrixUnit i.1 j alpha⟩ := by
  obtain ⟨i, hevent, hi⟩ :=
    event_to_arbitrary_target
      (V := V) (H := H) alpha halpha s j
  refine ⟨i, hi, hevent, ?_⟩
  exact branchWorld_has_unbounded_higher_tower
    (V := V) (H := H) (p := p)
    ⟨s, hodgeMatrixUnit i.1 j alpha⟩

/-- **FULL CLASS-LOCAL PI / PROJECTIVE WORD / GST OMNIVERSE CROWN.**
One projective spectral packet on the exact live support simultaneously gives
finite branch collapse, the N-cohomology packet, unbounded higher-causal branch
certificates, one algebraic cyclic seed and an actual native cycle representing
`alpha`. -/
theorem canonicalProjectiveSpectral_pi_omniverse_crown
    (G : GeometricCycleClassSpine V H)
    (depth : Nat)
    (alpha : ClassicalHodgeFiber V H p)
    (halpha : alpha ≠ 0)
    (P : CanonicalProjectiveSpectralPacket G alpha) :
    (∃ i : HodgeSupportIndex alpha,
      hodgeCoordinate i.1 alpha ≠ 0 ∧
      alpha =
        ∑ j ∈ ((classicalHodgeBasis V H p).repr alpha).support,
          (((classicalHodgeBasis V H p).repr alpha j) *
              (hodgeCoordinate i.1 alpha)⁻¹) •
            hodgeMatrixUnit i.1 j alpha)
    ∧
    (∃ basis : Fin (liveRank alpha) →
        GSTNCohomology.nCohoClasses depth (liveSupportNShape alpha) 1,
      ∀ i : Fin (liveRank alpha),
        (basis i).1 i =
          GSTNCohomology.towerWindow depth
            ((liveSupportNShape alpha).channel i) 1)
    ∧
    (∀ s : Sector, ∀ j : ClassicalHodgeBasisIndex V H p,
      ∃ i : HodgeSupportIndex alpha,
        hodgeCoordinate i.1 alpha ≠ 0 ∧
        (hodgeBranchGraph (V := V) (H := H) (p := p)).Event
          ⟨Sector.gstPlus, alpha⟩
          ⟨s, hodgeMatrixUnit i.1 j alpha⟩
        ∧ ∀ n : Nat,
          ∃ c : (hodgeHigherCausalCosmos
            (V := V) (H := H) (p := p)).Cell n,
            c = ⟨s, hodgeMatrixUnit i.1 j alpha⟩)
    ∧
    (∃ a : Fin (liveRank alpha) → ℚ,
      (∀ i, a i ≠ 0) ∧
      (∑ i : Fin (liveRank alpha),
        a i • (classicalHodgeBasis V H p
          (liveBasisIndex alpha i)).1) ∈
        GSTClassicalHodgeAtomicSpan.pointCycleClassSpan p (H.cycleClass p))
    ∧
    (∃ Z : codimensionCycles V.X p,
      H.cycleClass p Z = alpha.1) := by
  refine ⟨branch_collapse_identity alpha halpha,
    packet_has_exact_ncohomology depth alpha, ?_,
    P.exists_cyclic_atomic_seed, P.target_cycle⟩
  intro s j
  exact supportBranch_has_unbounded_causal_certificate alpha halpha s j

/-- **PI-WIDE ONE-PROJECTIVE-WORD LANDING.**
If every nonzero rational Hodge state admits one canonical-support projective
spectral packet, the exact Stage-2G rational Hodge statement follows.  The
packet is finite because the individual class is finite-support; the ambient
Hodge basis and GST omniverse remain unrestricted. -/
theorem bigradedBettiHodge_of_canonicalProjectiveSpectralPackets
    (G : GeometricCycleClassSpine V H)
    (packet :
      ∀ q : Nat, ∀ alpha : ClassicalHodgeFiber V H q,
        alpha ≠ 0 →
          Nonempty
            (CanonicalProjectiveSpectralPacket
              (V := V) (H := H) (p := q) G alpha)) :
    BigradedBettiHodgeStatement V H := by
  intro q x hx
  let alpha : ClassicalHodgeFiber V H q := ⟨x, hx⟩
  by_cases halpha : alpha = 0
  · have hx0 : x = 0 := congrArg Subtype.val halpha
    subst x
    exact LinearMap.zero_mem _
  · exact (Classical.choice (packet q alpha halpha)).target_cycle

#check CanonicalProjectiveSpectralPacket
#check CanonicalProjectiveSpectralPacket.toFiniteProjectiveSpectralCover
#check CanonicalProjectiveSpectralPacket.target_cycle
#check CanonicalProjectiveSpectralPacket.exists_cyclic_atomic_seed
#check packet_has_exact_ncohomology
#check supportBranch_has_unbounded_causal_certificate
#check canonicalProjectiveSpectral_pi_omniverse_crown
#check bigradedBettiHodge_of_canonicalProjectiveSpectralPackets

#print axioms CanonicalProjectiveSpectralPacket.target_cycle
#print axioms CanonicalProjectiveSpectralPacket.exists_cyclic_atomic_seed
#print axioms supportBranch_has_unbounded_causal_certificate
#print axioms canonicalProjectiveSpectral_pi_omniverse_crown
#print axioms bigradedBettiHodge_of_canonicalProjectiveSpectralPackets

end GSTClassicalHodgePiProjectiveSpectralOmniverseFinale
