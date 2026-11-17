import GSTClassicalHodgePiOmniverseBranchSynthesis
import GSTClassicalHodgePrincipalCutSpectralFusion
import GSTClassicalHodgeFiniteSupportArsenalConjugation

/-!
# GST CLASSICAL HODGE — CANONICAL OMNIVERSE SUPPORT / ONE SPECTRAL COLLAPSE

The handwritten Pi/omniverse construction does not choose an arbitrary finite
spectral cover.  The requested rational Hodge state already carries its own
finite live support inside the unrestricted Hodge basis, and the omniverse
causal packet already interprets exactly those live coordinates as the active
N-cohomology branch packet.

This file makes that identification literal.

For a concrete Hodge state `alpha` we construct the canonical finite Hodge
window by enumerating `HodgeSupportIndex alpha`.  Therefore:

* every slot of the window is genuinely live;
* every live coordinate of `alpha` occurs in the window;
* no global finite-rank assumption is introduced;
* the window is the same finite packet that underlies the GST/N-cohomology
  branching construction.

The existing closed-correspondence spectral amplifier then needs no separately
supplied support-cover map.  One genuinely realized spectral correspondence
observable, together with one synchronized algebraic seed visible in every
active branch, extracts all live basis sheets and reconstructs `alpha` as an
actual native algebraic cycle.

Thus the handwritten many-branch collapse is compressed geometrically to ONE
same-weight realized correspondence observable on the canonical active packet.
The ambient Pi/GST universe remains unbounded; only the active packet of the
particular class is finite.
-/

set_option maxHeartbeats 120000000
set_option maxRecDepth 1000000

noncomputable section

open scoped BigOperators
open AlgebraicGeometry

namespace GSTClassicalHodgePiOmniverseCanonicalSupportSpectral

open GSTProjectiveOverC
open GSTGeometricRealizationStage2D
open GSTGeometricRealizationStage2F
open GSTGeometricRealizationStage2G
open GSTClassicalHodgeFiberedCosmology
open GSTClassicalHodgeRankFreeArsenalIrreducibility
open GSTClassicalHodgeFiniteSupportArsenalConjugation
open GSTClassicalHodgeCanonicalSpectralObservable
open GSTClassicalHodgeClosedCorrespondenceSpectralAmplifier
open GSTClassicalHodgePrincipalCutSpectralFusion
open GSTClassicalHodgeSynchronizedDefectOrbit
open GSTClassicalHodgeGeometricCycleClassSpine
open GSTClassicalHodgeOmniverseCausalBranchPacket
open GSTClassicalHodgePiOmniverseBranchSynthesis

variable {V : SmoothProjectiveComplexScheme}
variable {H : HodgeBigradedBettiData V}
variable {p : Nat}

/-- The canonical spectral window of one Hodge state is exactly its live
basis-support enumeration. -/
noncomputable def canonicalLiveWindow
    (alpha : ClassicalHodgeFiber V H p) :
    FiniteHodgeBasisWindow V H p where
  N := liveRank alpha
  basisIndex := liveBasisIndex alpha
  basisIndex_injective := by
    intro r s hrs
    apply (liveEquivFin alpha).symm.injective
    apply Subtype.ext
    simpa [liveBasisIndex] using hrs

@[simp]
theorem canonicalLiveWindow_N
    (alpha : ClassicalHodgeFiber V H p) :
    (canonicalLiveWindow alpha).N = liveRank alpha := rfl

@[simp]
theorem canonicalLiveWindow_basisIndex
    (alpha : ClassicalHodgeFiber V H p)
    (r : Fin (liveRank alpha)) :
    (canonicalLiveWindow alpha).basisIndex r = liveBasisIndex alpha r := rfl

/-- Every actual support index occurs in the canonical live window. -/
theorem supportIndex_has_canonicalSlot
    (alpha : ClassicalHodgeFiber V H p)
    (i : HodgeSupportIndex alpha) :
    ∃ r : Fin (canonicalLiveWindow alpha).N,
      (canonicalLiveWindow alpha).basisIndex r = i.1 := by
  let r : Fin (liveRank alpha) := liveEquivFin alpha i
  refine ⟨r, ?_⟩
  change liveBasisIndex alpha r = i.1
  unfold liveBasisIndex r
  have h := (liveEquivFin alpha).symm_apply_apply i
  exact congrArg Subtype.val h

/-- Conversely every canonical slot is genuinely live in `alpha`. -/
theorem canonicalSlot_is_live
    (alpha : ClassicalHodgeFiber V H p)
    (r : Fin (canonicalLiveWindow alpha).N) :
    (classicalHodgeBasis V H p).repr alpha
      ((canonicalLiveWindow alpha).basisIndex r) ≠ 0 := by
  change (classicalHodgeBasis V H p).repr alpha
      (liveBasisIndex alpha r) ≠ 0
  exact liveCoordinateVector_ne_zero_at alpha r

/-- The canonical Hodge window and the handwritten N-cohomology packet have
exactly the same finite cardinality. -/
theorem canonicalWindow_rank_eq_ncohomology_holes
    (alpha : ClassicalHodgeFiber V H p) :
    (canonicalLiveWindow alpha).N = (liveSupportNShape alpha).holes := by
  rfl

/-- Hence the N-cohomology readout exists on precisely the slots of the
canonical spectral window. -/
theorem canonicalWindow_has_ncohomology_packet
    (R : Nat)
    (alpha : ClassicalHodgeFiber V H p) :
    ∃ basis : Fin (canonicalLiveWindow alpha).N →
        GSTNCohomology.nCohoClasses R (liveSupportNShape alpha) 1,
      ∀ i : Fin (canonicalLiveWindow alpha).N,
        (basis i).1 i =
          GSTNCohomology.towerWindow R
            ((liveSupportNShape alpha).channel i) 1 := by
  simpa [canonicalWindow_rank_eq_ncohomology_holes alpha] using
    (liveSupport_ncohomology_rank R alpha)

/-- **CANONICAL-SUPPORT SPECTRAL COLLAPSE.**
No finite support cover is supplied.  It is derived from `alpha` itself.
One realized correspondence observable on this exact active packet, and one
synchronized algebraic seed visible in every active slot, manufacture an
actual native cycle representing `alpha`. -/
theorem target_cycle_of_canonical_omniverse_spectral_packet
    (G : GeometricCycleClassSpine V H)
    (alpha : ClassicalHodgeFiber V H p)
    (R : ClosedCorrespondenceWindowRealization G (canonicalLiveWindow alpha))
    (S : NativeHodgeOrbitSeed (V := V) (H := H) (p := p))
    (hvisible : ∀ r : Fin (canonicalLiveWindow alpha).N,
      SeedVisible R S r) :
    ∃ Z : codimensionCycles V.X p,
      H.cycleClass p Z = alpha.1 := by
  apply target_cycle_of_seed_spectral_coverage R S alpha
  intro j hj
  have hjmem : j ∈ ((classicalHodgeBasis V H p).repr alpha).support :=
    Finsupp.mem_support_iff.mpr hj
  let i : HodgeSupportIndex alpha := ⟨j, hjmem⟩
  obtain ⟨r, hr⟩ := supportIndex_has_canonicalSlot alpha i
  exact ⟨r, hr, hvisible r⟩

/-- Elementwise form using the exact finite rational branch-collapse identity
from the Pi/omniverse packet.  The GST branch packet and the geometric spectral
collapse are simultaneously available for every nonzero target state. -/
theorem pi_branch_packet_and_native_cycle
    (G : GeometricCycleClassSpine V H)
    (alpha : ClassicalHodgeFiber V H p)
    (halpha : alpha ≠ 0)
    (R : ClosedCorrespondenceWindowRealization G (canonicalLiveWindow alpha))
    (S : NativeHodgeOrbitSeed (V := V) (H := H) (p := p))
    (hvisible : ∀ r : Fin (canonicalLiveWindow alpha).N,
      SeedVisible R S r) :
    (∃ i : HodgeSupportIndex alpha,
      hodgeCoordinate i.1 alpha ≠ 0 ∧
      alpha =
        ∑ j ∈ ((classicalHodgeBasis V H p).repr alpha).support,
          (((classicalHodgeBasis V H p).repr alpha j) *
              (hodgeCoordinate i.1 alpha)⁻¹) •
            hodgeMatrixUnit i.1 j alpha)
    ∧ (∃ Z : codimensionCycles V.X p,
      H.cycleClass p Z = alpha.1) := by
  exact ⟨branch_collapse_identity alpha halpha,
    target_cycle_of_canonical_omniverse_spectral_packet
      G alpha R S hvisible⟩

#check canonicalLiveWindow
#check supportIndex_has_canonicalSlot
#check canonicalSlot_is_live
#check canonicalWindow_rank_eq_ncohomology_holes
#check canonicalWindow_has_ncohomology_packet
#check target_cycle_of_canonical_omniverse_spectral_packet
#check pi_branch_packet_and_native_cycle

#print axioms supportIndex_has_canonicalSlot
#print axioms canonicalSlot_is_live
#print axioms canonicalWindow_has_ncohomology_packet
#print axioms target_cycle_of_canonical_omniverse_spectral_packet
#print axioms pi_branch_packet_and_native_cycle

end GSTClassicalHodgePiOmniverseCanonicalSupportSpectral
