import GSTClassicalHodgeSeparatorProbe
import GSTWorldRecoordinationGroupoid
import GSTUniversalAddressBridge
import GSTWorldPoincareDuality
import GSTGeometricRealizationStage2G
import GSTWorldCosmology
import GSTClassicalHodgeFiberedCosmology

/-!
# GST CLASSICAL HODGE — FINITE-SUPPORT LOCAL GST CHARTS

The total classical Hodge multiplicity universe need not be globally finite or
countable.  No such hypothesis is needed.  Every individual Hodge class has a
finite-support basis representation.  Its live support can therefore be
recoordinated exactly into one finite GST world.

This module constructs that local chart.  It also dualizes an arbitrary
completed Hodge probe across the native GST Poincare involution so that the
fibered coordinate pairing becomes literally the finite-world top pairing.

Hence any nonzero atomic separator probe has a finite GST observation witness.
This is the exact local-to-global interface needed for applying the existing
finite Lefschetz/Poincare/reciprocity laws without collapsing unrestricted
classical multiplicity.
-/

set_option maxHeartbeats 10000000
set_option maxRecDepth 1000000

noncomputable section

open scoped BigOperators
open GSTProjectiveOverC
open GSTClassicalHodgeFiberedCosmology
open GSTClassicalHodgeAtomicDefectDuality
open GSTClassicalHodgeSeparatorProbe
open GSTWorldRecoordinationGroupoid
open GSTWorldPoincareDuality
open GSTGeometricRealizationStage2G
open GSTWorldCosmology

namespace GSTClassicalHodgeFiniteSupportChart

/-- The genuinely live fibered addresses of one compact Hodge state. -/
abbrev LiveFiberedAddress
    {V : SmoothProjectiveComplexScheme}
    {H : HodgeBigradedBettiData V}
    (f : FiberedHodgeAddress V H) :=
  {s : FiberedHodgeIndex V H // s ∈ f.support}

/-- Number of live coordinates of one Hodge state. -/
def fiberedSupportSize
    {V : SmoothProjectiveComplexScheme}
    {H : HodgeBigradedBettiData V}
    (f : FiberedHodgeAddress V H) : Nat :=
  Fintype.card (LiveFiberedAddress f)

/-- Canonical finite code of the live support. -/
noncomputable def fiberedSupportEquivFin
    {V : SmoothProjectiveComplexScheme}
    {H : HodgeBigradedBettiData V}
    (f : FiberedHodgeAddress V H) :
    LiveFiberedAddress f ≃ Fin (fiberedSupportSize f) :=
  Fintype.equivFin (LiveFiberedAddress f)

/-- Standard local GST chart for a finite support: an N x 1 world. -/
def fiberedSupportShape
    {V : SmoothProjectiveComplexScheme}
    {H : HodgeBigradedBettiData V}
    (f : FiberedHodgeAddress V H) :
    GSTWorldShape (fiberedSupportSize f) where
  rows := fiberedSupportSize f
  cols := 1
  area_eq := by simp

/-- Embed one live fibered address into the finite GST support chart. -/
noncomputable def liveAddressToSupportState
    {V : SmoothProjectiveComplexScheme}
    {H : HodgeBigradedBettiData V}
    (f : FiberedHodgeAddress V H) :
    LiveFiberedAddress f ≃ ShapeState (fiberedSupportShape f) :=
  (fiberedSupportEquivFin f).trans
    (shapeCodeEquiv (fiberedSupportShape f)).symm

/-- Rational coefficient field on the finite support chart. -/
def fiberedSupportWorld
    {V : SmoothProjectiveComplexScheme}
    {H : HodgeBigradedBettiData V}
    (f : FiberedHodgeAddress V H) :
    ShapeState (fiberedSupportShape f) → ℚ :=
  fun c =>
    f (((liveAddressToSupportState f).symm c).1)

@[simp]
theorem fiberedSupportWorld_live
    {V : SmoothProjectiveComplexScheme}
    {H : HodgeBigradedBettiData V}
    (f : FiberedHodgeAddress V H)
    (s : LiveFiberedAddress f) :
    fiberedSupportWorld f (liveAddressToSupportState f s) = f s.1 := by
  simp [fiberedSupportWorld]

/-- Rational version of the native finite GST Poincare top pairing.  It uses
exactly the same world complement as the integral world theory. -/
def rationalWorldTopPairing
    {A B : Nat}
    (a b : WorldCell A B → ℚ) : ℚ :=
  ∑ c : WorldCell A B, a c * b (worldDual c)

/-- Pull a completed Hodge probe into the finite support chart, with the
Poincare involution inserted so that the world top pairing becomes the
ordinary coordinate pairing. -/
def dualizedSupportProbe
    {V : SmoothProjectiveComplexScheme}
    {H : HodgeBigradedBettiData V}
    (f : FiberedHodgeAddress V H)
    (g : FiberedCompletedAddress V H) :
    ShapeState (fiberedSupportShape f) → ℚ :=
  fun c =>
    g (((liveAddressToSupportState f).symm
      (worldDual c)).1)

/-- Sum over the finite GST chart is exactly sum over the live Finsupp support. -/
theorem supportWorld_sum_equiv_support
    {V : SmoothProjectiveComplexScheme}
    {H : HodgeBigradedBettiData V}
    (f : FiberedHodgeAddress V H)
    (g : FiberedCompletedAddress V H) :
    (∑ c : ShapeState (fiberedSupportShape f),
      fiberedSupportWorld f c *
        g (((liveAddressToSupportState f).symm c).1)) =
      ∑ s : LiveFiberedAddress f, f s.1 * g s.1 := by
  exact Fintype.sum_equiv
    (liveAddressToSupportState f).symm
    (fun c =>
      fiberedSupportWorld f c *
        g (((liveAddressToSupportState f).symm c).1))
    (fun s => f s.1 * g s.1)
    (fun c => by simp [fiberedSupportWorld])

/-- The subtype sum over live support is the original compact/completed
fibered pairing. -/
theorem supportSubtype_sum_eq_fiberedPairing
    {V : SmoothProjectiveComplexScheme}
    {H : HodgeBigradedBettiData V}
    (f : FiberedHodgeAddress V H)
    (g : FiberedCompletedAddress V H) :
    (∑ s : LiveFiberedAddress f, f s.1 * g s.1) =
      fiberedPairing f g := by
  classical
  rw [fiberedPairing]
  rw [Finsupp.sum]
  rw [← Finset.sum_subtype (s := f.support)
    (p := fun s => s ∈ f.support)
    (f := fun s => f s * g s)
    (by intro s; simp)]

/-- **FINITE-SUPPORT POINCARE IDENTIFICATION.**

The limitless fibered compact/completed pairing of one Hodge state is exactly
the native finite GST Poincare pairing on its support chart. -/
theorem fiberedPairing_eq_finiteGSTPoincare
    {V : SmoothProjectiveComplexScheme}
    {H : HodgeBigradedBettiData V}
    (f : FiberedHodgeAddress V H)
    (g : FiberedCompletedAddress V H) :
    fiberedPairing f g =
      rationalWorldTopPairing
        (fiberedSupportWorld f)
        (dualizedSupportProbe f g) := by
  rw [rationalWorldTopPairing]
  have hdual :
      ∀ c : ShapeState (fiberedSupportShape f),
        dualizedSupportProbe f g (worldDual c) =
          g (((liveAddressToSupportState f).symm c).1) := by
    intro c
    simp [dualizedSupportProbe]
  simp_rw [hdual]
  rw [supportWorld_sum_equiv_support f g]
  exact (supportSubtype_sum_eq_fiberedPairing f g).symm

/-- Rational top pairing is left-nondegenerate on every finite GST world,
by the same complementary-basis extraction mechanism as the integral theory. -/
theorem rationalWorldTopPairing_nondegenerate_left
    {A B : Nat}
    (a : WorldCell A B → ℚ)
    (h : ∀ b : WorldCell A B → ℚ,
      rationalWorldTopPairing a b = 0) :
    a = 0 := by
  funext c
  let b : WorldCell A B → ℚ :=
    fun x => if x = worldDual c then 1 else 0
  have hc := h b
  classical
  have hpick : rationalWorldTopPairing a b = a c := by
    unfold rationalWorldTopPairing b
    rw [Finset.sum_eq_single c]
    · simp
    · intro d hd hdc
      have hne : worldDual d ≠ worldDual c := by
        intro heq
        exact hdc (worldDual_injective heq)
      simp [hne]
    · simp
  rw [hpick] at hc
  exact hc

/-- Every nonzero compact fibered Hodge address therefore has a finite GST
Poincare probe detecting it. -/
theorem nonzero_fiberedAddress_has_finiteGST_probe
    {V : SmoothProjectiveComplexScheme}
    {H : HodgeBigradedBettiData V}
    (f : FiberedHodgeAddress V H)
    (hf : f ≠ 0) :
    ∃ b : ShapeState (fiberedSupportShape f) → ℚ,
      rationalWorldTopPairing (fiberedSupportWorld f) b ≠ 0 := by
  by_contra hnone
  push_neg at hnone
  have hzero : fiberedSupportWorld f = 0 :=
    rationalWorldTopPairing_nondegenerate_left
      (fiberedSupportWorld f) hnone
  apply hf
  apply Finsupp.ext
  intro s
  by_cases hs : s ∈ f.support
  · let slive : LiveFiberedAddress f := ⟨s, hs⟩
    have hz := congrFun hzero (liveAddressToSupportState f slive)
    simpa [slive] using hz
  · have h0 : f s = 0 := by
      by_contra hne
      exact hs (Finsupp.mem_support_iff.mpr hne)
    exact h0

/-- A nonzero atomic separator probe produces an honest finite GST world in
which its Hodge state has a nonzero Poincare pairing. -/
theorem atomicSeparatorProbe_has_finiteGST_witness
    (V : SmoothProjectiveComplexScheme)
    (H : HodgeBigradedBettiData V)
    (p : Nat)
    (S : AtomicSeparatorProbe V H p) :
    rationalWorldTopPairing
      (fiberedSupportWorld
        (fiberedWeightCoordinates V H p S.alpha))
      (dualizedSupportProbe
        (fiberedWeightCoordinates V H p S.alpha)
        (fun s =>
          if hp : s.1 = p then
            match hp ▸ s.2 with
            | i => functionalHodgeProbe V H p S.detector i
          else 0)) ≠ 0 := by
  let f := fiberedWeightCoordinates V H p S.alpha
  let g : FiberedCompletedAddress V H :=
    fun s =>
      if hp : s.1 = p then
        match hp ▸ s.2 with
        | i => functionalHodgeProbe V H p S.detector i
      else 0
  have hpair : fiberedPairing f g ≠ 0 := by
    have hcoords :
        fiberedPairing f g =
          hodgeFiberPairing
            ((classicalHodgeBasis V H p).repr S.alpha)
            (functionalHodgeProbe V H p S.detector) := by
      classical
      unfold f g fiberedPairing hodgeFiberPairing fiberedWeightCoordinates
      simp [weightFiberEmbedding, Finsupp.sum_embDomain]
      rfl
    rw [hcoords]
    exact S.pairing_nonzero
  rw [fiberedPairing_eq_finiteGSTPoincare f g] at hpair
  exact hpair

/-- **FINITE OBSERVATION REDUCTION OF HODGE FAILURE.**  If the classical
Stage-2G target fails, then one concrete finite GST support chart carries a
nonzero rational Poincare pairing witnessing that failure.  No global
countability or finite-rank hypothesis on the classical Hodge fiber appears. -/
theorem not_hodge_yields_finiteGST_poincare_witness
    (V : SmoothProjectiveComplexScheme)
    (H : HodgeBigradedBettiData V)
    (hnot : ¬ BigradedBettiHodgeStatement V H) :
    ∃ p : Nat, ∃ S : AtomicSeparatorProbe V H p,
      rationalWorldTopPairing
        (fiberedSupportWorld
          (fiberedWeightCoordinates V H p S.alpha))
        (dualizedSupportProbe
          (fiberedWeightCoordinates V H p S.alpha)
          (fun s =>
            if hp : s.1 = p then
              match hp ▸ s.2 with
              | i => functionalHodgeProbe V H p S.detector i
            else 0)) ≠ 0 := by
  obtain ⟨p, hS⟩ :=
    (not_bigradedBettiHodgeStatement_iff_exists_separatorProbe V H).mp hnot
  let S := Classical.choice hS
  exact ⟨p, S, atomicSeparatorProbe_has_finiteGST_witness V H p S⟩

#check LiveFiberedAddress
#check fiberedSupportSize
#check fiberedSupportEquivFin
#check fiberedSupportShape
#check liveAddressToSupportState
#check fiberedSupportWorld
#check rationalWorldTopPairing
#check dualizedSupportProbe
#check fiberedPairing_eq_finiteGSTPoincare
#check rationalWorldTopPairing_nondegenerate_left
#check nonzero_fiberedAddress_has_finiteGST_probe
#check atomicSeparatorProbe_has_finiteGST_witness
#check not_hodge_yields_finiteGST_poincare_witness

#print axioms fiberedPairing_eq_finiteGSTPoincare
#print axioms rationalWorldTopPairing_nondegenerate_left
#print axioms nonzero_fiberedAddress_has_finiteGST_probe
#print axioms atomicSeparatorProbe_has_finiteGST_witness
#print axioms not_hodge_yields_finiteGST_poincare_witness

end GSTClassicalHodgeFiniteSupportChart
