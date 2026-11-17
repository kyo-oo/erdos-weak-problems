import GSTClassicalHodgeClosedCorrespondenceGhostExtinction
import GSTClassicalHodgeOmniversalSeparatorGhostCrown

/-!
# GST CLASSICAL HODGE — UNREACHABLE COSMIC CORRESPONDENCE FAILURE PACKET

The previous layers now meet at one exact frontier.

* The single-sheet crown says a classical Hodge failure yields one genuine
  Hodge basis sheet with an atomic separator.
* The limitless fibered cosmology identifies that sheet with one exact cosmic
  diagonal generator after forgetting multiplicity.
* The realized closed-correspondence algebra proves that any sheet hit from a
  genuine point by an actual rational word of realized correspondences is
  algebraic, hence cannot carry a separator.

Therefore every genuine Stage-2G failure forces an **unreachable cosmic
sheet**: an exact limitless GST diagonal generator whose classical
multiplicity sheet cannot be reached from ANY genuine codimension-p point by
ANY finite rational word of actual realized closed correspondences.

This is substantially sharper than an unspecified missing algebraic cycle and
substantially safer than postulating matrix-unit naturality.  The remaining
cosmology task is now precise: rule out such an unreachable cosmic generator by
constructing enough genuine geometric correspondence dynamics.
-/

set_option maxHeartbeats 80000000
set_option maxRecDepth 1000000

noncomputable section

open AlgebraicGeometry

namespace GSTClassicalHodgeClosedCorrespondenceFailurePacket

open GSTProjectiveOverC
open GSTGeometricRealizationStage2G
open GSTClassicalHodgeFiberedCosmology
open GSTClassicalHodgeSingleSheetCrown
open GSTClassicalHodgeClosedCorrespondenceGhostExtinction

variable {V : SmoothProjectiveComplexScheme}
variable {H : HodgeBigradedBettiData V}

/-- A separator sheet is necessarily unreachable by genuine realized closed
correspondence words from genuine point atoms. -/
theorem basisSeparator_forbids_closedCorrespondenceHit
    {p : Nat}
    {j : ClassicalHodgeBasisIndex V H p}
    (S : BasisAtomicSeparator V H p j) :
    ¬ ClosedCorrespondenceHitsSheet (V := V) (H := H) j := by
  intro hHit
  have hnone :=
    isEmpty_basisAtomicSeparator_of_closedCorrespondenceHit j hHit
  exact isEmpty_iff.mp hnone S

/-- Exact failure packet: one microscopic separator, one unreachable classical
sheet, and one exact limitless GST cosmic diagonal address are the same
obstruction. -/
structure UnreachableCosmicSheet where
  weight : Nat
  sheet : ClassicalHodgeBasisIndex V H weight
  separator : BasisAtomicSeparator V H weight sheet
  unreachable :
    ¬ ClosedCorrespondenceHitsSheet (V := V) (H := H) sheet
  cosmic_exact :
    GSTClassicalHodgeFiberedCosmology.forgetMultiplicityToGST
      (fiberedWeightCoordinates V H weight
        (classicalHodgeBasis V H weight sheet)) =
      Finsupp.single
        (GSTUniversalAddressBridge.cosmicAddressEquiv (weight,weight)) 1

/-- Every genuine failure produces an unreachable exact cosmic generator. -/
noncomputable def unreachableCosmicSheetOfSeparator
    {p : Nat}
    {j : ClassicalHodgeBasisIndex V H p}
    (S : BasisAtomicSeparator V H p j) :
    UnreachableCosmicSheet (V := V) (H := H) where
  weight := p
  sheet := j
  separator := S
  unreachable := basisSeparator_forbids_closedCorrespondenceHit S
  cosmic_exact := classical_basis_projects_to_cosmic_diagonal V H p j

/-- **CLASSICAL FAILURE -> UNREACHABLE LIMITLESS COSMIC SHEET.** -/
theorem not_hodge_yields_unreachableCosmicSheet
    (hnot : ¬ BigradedBettiHodgeStatement V H) :
    Nonempty (UnreachableCosmicSheet (V := V) (H := H)) := by
  rw [not_bigradedBettiHodgeStatement_iff_exists_basis_separator V H] at hnot
  rcases hnot with ⟨p,j,⟨S⟩⟩
  exact ⟨unreachableCosmicSheetOfSeparator S⟩

/-- Conversely, eliminating unreachable cosmic sheets suffices for the full
Stage-2G Hodge statement. -/
theorem hodge_of_no_unreachableCosmicSheet
    (hno : IsEmpty (UnreachableCosmicSheet (V := V) (H := H))) :
    BigradedBettiHodgeStatement V H := by
  by_contra hnot
  exact isEmpty_iff.mp hno
    (Classical.choice (not_hodge_yields_unreachableCosmicSheet hnot))

/-- Exact equivalence at the new geometry/cosmology frontier. -/
theorem hodge_iff_no_unreachableCosmicSheet :
    BigradedBettiHodgeStatement V H ↔
      IsEmpty (UnreachableCosmicSheet (V := V) (H := H)) := by
  constructor
  · intro h
    refine ⟨?_⟩
    intro U
    have hnone :=
      (bigradedBettiHodgeStatement_iff_no_basis_separator V H).mp
        h U.weight U.sheet
    exact isEmpty_iff.mp hnone U.separator
  · exact hodge_of_no_unreachableCosmicSheet

#check UnreachableCosmicSheet
#check basisSeparator_forbids_closedCorrespondenceHit
#check unreachableCosmicSheetOfSeparator
#check not_hodge_yields_unreachableCosmicSheet
#check hodge_of_no_unreachableCosmicSheet
#check hodge_iff_no_unreachableCosmicSheet

#print axioms basisSeparator_forbids_closedCorrespondenceHit
#print axioms not_hodge_yields_unreachableCosmicSheet
#print axioms hodge_iff_no_unreachableCosmicSheet

end GSTClassicalHodgeClosedCorrespondenceFailurePacket
