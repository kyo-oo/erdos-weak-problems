import GSTClassicalHodgeClosedCorrespondenceSpectralAmplifier
import GSTClassicalHodgeFiniteSupportArsenalConjugation

/-!
# GST CLASSICAL HODGE — LIVE-SUPPORT CLOSED-CORRESPONDENCE SPECTRAL CROWN

Every individual rational Hodge class has finite support in the unrestricted
classical Hodge basis.  The previous module shows that one realized closed-
correspondence observable can algebraize any finite window once each selected
sheet is visible from one genuine point class.

This file chooses the window canonically: exactly the live support of the
requested Hodge class.

Thus a nonzero class alpha requires only:

1. ONE finite rational word of genuine realized closed correspondences whose
   Hodge action is the canonical GST code observable on alpha's live support;
2. for each live slot, ONE genuine codimension-p point whose class has nonzero
   coordinate in that slot.

The zero-complement GST polynomial calculus extracts an exact native cycle for
each live basis sheet, and the original finite-support coefficients reassemble
alpha itself.

This is strictly weaker than all-pairs matrix-unit externalization and strictly
more geometric than an abstract range-stability or native-lift interface.
-/

set_option maxHeartbeats 100000000
set_option maxRecDepth 1000000

noncomputable section

open scoped BigOperators
open AlgebraicGeometry

namespace GSTClassicalHodgeLiveSupportCorrespondenceSpectralCrown

open GSTProjectiveOverC
open GSTGeometricRealizationStage2D
open GSTGeometricRealizationStage2G
open GSTClassicalHodgeFiberedCosmology
open GSTClassicalHodgeRankFreeArsenalIrreducibility
open GSTClassicalHodgeCanonicalSpectralObservable
open GSTClassicalHodgeFiniteSupportArsenalConjugation
open GSTClassicalHodgeLocalCyclicCriterion
open GSTClassicalHodgeClosedCorrespondenceSpectralAmplifier
open GSTClassicalHodgeGeometricCycleClassSpine

variable {V : SmoothProjectiveComplexScheme}
variable {H : HodgeBigradedBettiData V}
variable {p : Nat}

/-- Canonical finite Hodge-basis window consisting of exactly the live support
of one concrete Hodge class. -/
noncomputable def liveSupportWindow
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
theorem liveSupportWindow_basisIndex
    (alpha : ClassicalHodgeFiber V H p)
    (r : Fin (liveRank alpha)) :
    (liveSupportWindow alpha).basisIndex r = liveBasisIndex alpha r :=
  rfl

/-- One class-local geometry certificate: a realized correspondence observable
on the exact live support together with one visible genuine point per live
slot. -/
structure LiveSupportCorrespondenceSpectralCertificate
    (G : GeometricCycleClassSpine V H)
    (alpha : ClassicalHodgeFiber V H p) where
  realization :
    ClosedCorrespondenceWindowRealization G (liveSupportWindow alpha)
  visible : ∀ r : Fin (liveRank alpha), realization.PointVisible r

namespace LiveSupportCorrespondenceSpectralCertificate

variable {G : GeometricCycleClassSpine V H}
variable {alpha : ClassicalHodgeFiber V H p}

/-- Exact native algebraic cycle for one live basis slot. -/
noncomputable def liveBasisCycle
    (C : LiveSupportCorrespondenceSpectralCertificate G alpha)
    (r : Fin (liveRank alpha)) :
    codimensionCycles V.X p :=
  C.realization.extractedBasisCycle r (C.visible r)

@[simp]
theorem liveBasisCycle_spec
    (C : LiveSupportCorrespondenceSpectralCertificate G alpha)
    (r : Fin (liveRank alpha)) :
    H.cycleClass p (C.liveBasisCycle r) =
      (classicalHodgeBasis V H p (liveBasisIndex alpha r)).1 := by
  simpa [liveBasisCycle, liveSupportWindow] using
    C.realization.extractedBasisCycle_spec r (C.visible r)

/-- Reassemble alpha using its original finite live coordinates. -/
noncomputable def reconstructedCycle
    (C : LiveSupportCorrespondenceSpectralCertificate G alpha) :
    codimensionCycles V.X p :=
  ∑ r : Fin (liveRank alpha),
    (liveCoordinateVector alpha r) • C.liveBasisCycle r

/-- The reconstructed native cycle has exactly the requested Hodge class. -/
theorem reconstructedCycle_spec
    (C : LiveSupportCorrespondenceSpectralCertificate G alpha) :
    H.cycleClass p C.reconstructedCycle = alpha.1 := by
  unfold reconstructedCycle
  rw [map_sum]
  simp_rw [LinearMap.map_smul, C.liveBasisCycle_spec]
  calc
    (∑ r : Fin (liveRank alpha),
        (liveCoordinateVector alpha r) •
          (classicalHodgeBasis V H p (liveBasisIndex alpha r)).1)
        = ∑ i : HodgeSupportIndex alpha,
          ((classicalHodgeBasis V H p).repr alpha i.1) •
            (classicalHodgeBasis V H p i.1).1 := by
              classical
              exact Fintype.sum_equiv
                (liveEquivFin alpha).symm
                (fun r : Fin (liveRank alpha) =>
                  (liveCoordinateVector alpha r) •
                    (classicalHodgeBasis V H p (liveBasisIndex alpha r)).1)
                (fun i : HodgeSupportIndex alpha =>
                  ((classicalHodgeBasis V H p).repr alpha i.1) •
                    (classicalHodgeBasis V H p i.1).1)
                (fun r => by simp [liveCoordinateVector, liveBasisIndex])
    _ = alpha.1 := (hodgeClass_eq_support_sum alpha).symm

/-- Constructive native-cycle witness for the requested Hodge class. -/
theorem exists_native_cycle
    (C : LiveSupportCorrespondenceSpectralCertificate G alpha) :
    ∃ Z : codimensionCycles V.X p,
      H.cycleClass p Z = alpha.1 :=
  ⟨C.reconstructedCycle, C.reconstructedCycle_spec⟩

end LiveSupportCorrespondenceSpectralCertificate

/-- **LIVE-SUPPORT CLOSED-CORRESPONDENCE STAGE-2G CROWN.**
Every nonzero Hodge class is algebraic once its exact finite support admits one
realized correspondence code observable and live point visibility.  Zero
classes require no certificate. -/
theorem bigradedBettiHodge_of_liveSupportCorrespondenceSpectralCertificates
    (G : GeometricCycleClassSpine V H)
    (C : ∀ q : Nat,
      ∀ alpha : ClassicalHodgeFiber V H q,
        alpha ≠ 0 →
          Nonempty (LiveSupportCorrespondenceSpectralCertificate G alpha)) :
    BigradedBettiHodgeStatement V H := by
  intro q x hx
  let alpha : ClassicalHodgeFiber V H q := ⟨x,hx⟩
  by_cases hzero : alpha = 0
  · have hx0 : x = 0 := congrArg Subtype.val hzero
    subst x
    exact ⟨0, by simp⟩
  · exact (Classical.choice (C q alpha hzero)).exists_native_cycle

/-- Elementwise constructive form. -/
theorem every_hodge_class_has_native_cycle_of_liveSupportCorrespondenceSpectralCertificates
    (G : GeometricCycleClassSpine V H)
    (C : ∀ q : Nat,
      ∀ beta : ClassicalHodgeFiber V H q,
        beta ≠ 0 →
          Nonempty (LiveSupportCorrespondenceSpectralCertificate G beta))
    (alpha : ClassicalHodgeFiber V H p) :
    ∃ Z : codimensionCycles V.X p,
      H.cycleClass p Z = alpha.1 := by
  by_cases hzero : alpha = 0
  · refine ⟨0, ?_⟩
    rw [hzero]
    simp
  · exact (Classical.choice (C p alpha hzero)).exists_native_cycle

#check liveSupportWindow
#check LiveSupportCorrespondenceSpectralCertificate
#check LiveSupportCorrespondenceSpectralCertificate.liveBasisCycle
#check LiveSupportCorrespondenceSpectralCertificate.reconstructedCycle
#check LiveSupportCorrespondenceSpectralCertificate.reconstructedCycle_spec
#check LiveSupportCorrespondenceSpectralCertificate.exists_native_cycle
#check bigradedBettiHodge_of_liveSupportCorrespondenceSpectralCertificates

#print axioms LiveSupportCorrespondenceSpectralCertificate.liveBasisCycle_spec
#print axioms LiveSupportCorrespondenceSpectralCertificate.reconstructedCycle_spec
#print axioms bigradedBettiHodge_of_liveSupportCorrespondenceSpectralCertificates

end GSTClassicalHodgeLiveSupportCorrespondenceSpectralCrown
