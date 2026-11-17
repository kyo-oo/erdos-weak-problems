import GSTClassicalHodgeLimitlessCosmicMatrixUnits
import GSTClassicalHodgeConcreteFailureDichotomy
import GSTClassicalHodgeRankFreePrimitiveGeneration

/-!
# GST CLASSICAL HODGE — LIMITLESS TWO-SLOT FAILURE DICHOTOMY

The finite two-slot word is only an observation chart.  This file embeds every
finite rational pure-Hodge window into the genuine limitless rational compact
cosmos `Nat ->₀ Q`, proves exact readback, and intertwines finite matrix units
with the unrestricted cosmic matrix units.

Consequently the single concrete failure mode isolated by
`GSTClassicalHodgeConcreteFailureDichotomy` is rewritten as failure of one true
limitless cosmic Poincare read/write operator after a two-coordinate
recoordination.  The classical obstruction is therefore no longer attached to
a finite surrogate.
-/

set_option maxHeartbeats 50000000
set_option maxRecDepth 1000000

noncomputable section

open scoped BigOperators
open AlgebraicGeometry

namespace GSTClassicalHodgeLimitlessTwoSlotFailureDichotomy

open GSTProjectiveOverC
open GSTGeometricRealizationStage2G
open GSTClassicalHodgeFullArsenalIrreducibility
open GSTClassicalHodgeRankFreeArsenalIrreducibility
open GSTClassicalHodgeRankFreePrimitiveGeneration
open GSTClassicalHodgeConcreteFailureDichotomy
open GSTClassicalHodgeLimitlessCosmicMatrixUnits
open GSTClassicalHodgeExplicitArsenalGeneration
open GSTClassicalHodgeFiberedCosmology

/-- Embed a finite rational pure-Hodge window into the unrestricted rational
compact cosmos at the corresponding natural weights. -/
noncomputable def embedWindow
    {N : Nat} : RationalPureWindow N →ₗ[ℚ] RationalPureCosmos where
  toFun a := ∑ r : Fin N, Finsupp.single r.1 (a r)
  map_add' := by
    intro a b
    ext n
    simp [Finset.sum_add_distrib]
  map_smul' := by
    intro q a
    ext n
    simp [Finset.smul_sum]

/-- Read the first `N` limitless weights back as one finite pure window. -/
def readWindow
    {N : Nat} : RationalPureCosmos →ₗ[ℚ] RationalPureWindow N where
  toFun f := fun r => f r.1
  map_add' := by intro f g; funext r; simp
  map_smul' := by intro q f; funext r; simp

@[simp]
theorem embedWindow_apply_fin
    {N : Nat} (a : RationalPureWindow N) (r : Fin N) :
    embedWindow a r.1 = a r := by
  classical
  have key : (Finsupp.lapply r.1 : (ℕ →₀ ℚ) →ₗ[ℚ] ℚ)
      (∑ s : Fin N, Finsupp.single s.1 (a s)) = a r := by
    rw [map_sum, Finset.sum_eq_single r]
    · show (Finsupp.single r.1 (a r)) r.1 = a r
      rw [Finsupp.single_apply, if_pos rfl]
    · intro s _ hsr
      show (Finsupp.single s.1 (a s)) r.1 = (0 : ℚ)
      have hval : s.1 ≠ r.1 := by
        intro h
        exact hsr (Fin.ext h)
      rw [Finsupp.single_apply, if_neg hval]
    · simp
  exact key

/-- Exact finite observation: embedding and reading back loses nothing. -/
@[simp]
theorem readWindow_embedWindow
    {N : Nat} (a : RationalPureWindow N) :
    readWindow (embedWindow a) = a := by
  funext r
  exact embedWindow_apply_fin a r

/-- Finite basis sheets are literally the observations of unrestricted cosmic
basis vectors. -/
theorem embedWindow_basis
    {N : Nat} (r : Fin N) :
    embedWindow (rationalPureBasis r) = rationalCosmicBasis r.1 := by
  ext n
  by_cases hn : n = r.1
  · subst n
    simp [rationalCosmicBasis, rationalPureBasis,
      embedWindow_apply_fin]
  · classical
    have hrcb : rationalCosmicBasis r.1 n = 0 := by
      show (Finsupp.single r.1 (1 : ℚ)) n = 0
      rw [Finsupp.single_apply, if_neg (Ne.symm hn)]
    have key : (Finsupp.lapply n : (ℕ →₀ ℚ) →ₗ[ℚ] ℚ)
        (∑ s : Fin N, Finsupp.single s.1 (rationalPureBasis r s))
        = rationalCosmicBasis r.1 n := by
      rw [map_sum, hrcb]
      apply Finset.sum_eq_zero
      intro s _
      show (Finsupp.single s.1 (rationalPureBasis r s)) n = (0 : ℚ)
      rw [Finsupp.single_apply]
      by_cases hsn : s.1 = n
      · rw [if_pos hsn]
        have hsr : s ≠ r := by
          intro h
          apply hn
          rw [← hsn, h]
        simp only [rationalPureBasis, if_neg hsr]
      · rw [if_neg hsn]
    exact key

/-- A limitless matrix unit acting between two visible finite weights stays in
that observation window and reads back as the usual finite matrix unit. -/
theorem readWindow_cosmicMatrixUnit_embedWindow
    {N : Nat} (r s : Fin N) (a : RationalPureWindow N) :
    readWindow
        (rationalCosmicMatrixUnit r.1 s.1 (embedWindow a)) =
      pureMatrixUnit r s a := by
  funext q
  rw [rationalCosmicMatrixUnit_apply]
  rw [embedWindow_apply_fin]
  by_cases hqs : q = s
  · subst q
    simp [readWindow, pureMatrixUnit, rationalPureBasis]
  · have hval : q.1 ≠ s.1 := by
      intro h
      exact hqs (Fin.ext h)
    simp [readWindow, pureMatrixUnit, rationalPureBasis, hqs, hval]

/-- Operator form of the finite/limitless matrix-unit intertwining. -/
theorem finiteMatrixUnit_is_cosmic_observation
    {N : Nat} (r s : Fin N) :
    pureMatrixUnit r s =
      (readWindow (N:=N)).comp
        ((rationalCosmicMatrixUnit r.1 s.1).comp embedWindow) := by
  apply LinearMap.ext
  intro a
  symm
  exact readWindow_cosmicMatrixUnit_embedWindow r s a

/-- The fixed two-slot GST word used by rank-free generation is exactly a
finite observation of the true limitless cosmic matrix unit `E_01`. -/
theorem forwardArsenalWord_is_limitless_cosmic_observation :
    forwardArsenalWord sourceSlot targetSlot =
      (readWindow (N:=2)).comp
        ((rationalCosmicMatrixUnit sourceSlot.1 targetSlot.1).comp embedWindow) := by
  rw [← twoSlot_matrixUnit_eq_forwardArsenalWord]
  exact finiteMatrixUnit_is_cosmic_observation sourceSlot targetSlot

variable {V : SmoothProjectiveComplexScheme}
variable {H : HodgeBigradedBettiData V}
variable {p : Nat}

/-- Lift one limitless cosmic operator through an arbitrary finite classical
Hodge recoordination chart. -/
noncomputable def liftCosmicWindowOperator
    {N : Nat}
    (e : Fin N → ClassicalHodgeBasisIndex V H p)
    (T : Module.End ℚ RationalPureCosmos) :
    Module.End ℚ (ClassicalHodgeFiber V H p) :=
  (finiteHodgeWrite e).comp
    ((readWindow (N:=N)).comp
      (T.comp (embedWindow.comp (finiteHodgeRead e))))

/-- Every classical matrix unit is the lift of one unrestricted cosmic matrix
unit after finite recoordination of its two participating basis directions. -/
theorem hodgeMatrixUnit_eq_lift_limitless_cosmic
    (i j : ClassicalHodgeBasisIndex V H p) :
    hodgeMatrixUnit i j =
      liftCosmicWindowOperator (pairBasisIndex i j)
        (rationalCosmicMatrixUnit sourceSlot.1 targetSlot.1) := by
  rw [rankFreeMatrixUnit_eq_lifted_GST_word]
  rw [forwardArsenalWord_is_limitless_cosmic_observation]
  rfl

/-- The concrete two-slot word and the limitless cosmic lift agree pointwise on
the genuine classical Hodge fiber. -/
theorem twoSlotWord_apply_eq_limitless_cosmic
    (i j : ClassicalHodgeBasisIndex V H p)
    (alpha : ClassicalHodgeFiber V H p) :
    liftFiniteHodgeOperator (pairBasisIndex i j)
        (forwardArsenalWord sourceSlot targetSlot) alpha =
      liftCosmicWindowOperator (pairBasisIndex i j)
        (rationalCosmicMatrixUnit sourceSlot.1 targetSlot.1) alpha := by
  rw [twoSlotWord_apply_eq_matrixUnit]
  rw [hodgeMatrixUnit_eq_lift_limitless_cosmic]

/-- A failure witness expressed directly by the unrestricted cosmic matrix-unit
operator, not by a finite GST surrogate. -/
structure LimitlessCosmicEscape where
  source : ClassicalHodgeBasisIndex V H p
  target : ClassicalHodgeBasisIndex V H p
  alpha : ClassicalHodgeFiber V H p
  alpha_algebraic : alpha ∈ AlgebraicFiber (V:=V) (H:=H) (p:=p)
  escapes :
    liftCosmicWindowOperator (pairBasisIndex source target)
        (rationalCosmicMatrixUnit sourceSlot.1 targetSlot.1) alpha ∉
      AlgebraicFiber (V:=V) (H:=H) (p:=p)

end GSTClassicalHodgeLimitlessTwoSlotFailureDichotomy

namespace GSTClassicalHodgeConcreteFailureDichotomy

/-- Every old two-slot escape is exactly a limitless cosmic escape. -/
noncomputable def TwoSlotEscape.toLimitlessCosmicEscape
    (E : TwoSlotEscape (V:=V) (H:=H) (p:=p)) :
    GSTClassicalHodgeLimitlessTwoSlotFailureDichotomy.LimitlessCosmicEscape
      (V:=V) (H:=H) (p:=p) where
  source := E.source
  target := E.target
  alpha := E.alpha
  alpha_algebraic := E.alpha_algebraic
  escapes := by
    rw [← GSTClassicalHodgeLimitlessTwoSlotFailureDichotomy.twoSlotWord_apply_eq_limitless_cosmic
      E.source E.target E.alpha]
    exact E.escapes

end GSTClassicalHodgeConcreteFailureDichotomy

namespace GSTClassicalHodgeLimitlessTwoSlotFailureDichotomy

open GSTProjectiveOverC
open GSTGeometricRealizationStage2G
open GSTClassicalHodgeFullArsenalIrreducibility
open GSTClassicalHodgeRankFreeArsenalIrreducibility
open GSTClassicalHodgeRankFreePrimitiveGeneration
open GSTClassicalHodgeConcreteFailureDichotomy
open GSTClassicalHodgeLimitlessCosmicMatrixUnits
open GSTClassicalHodgeExplicitArsenalGeneration
open GSTClassicalHodgeFiberedCosmology

variable {V : SmoothProjectiveComplexScheme}
variable {H : HodgeBigradedBettiData V}
variable {p : Nat}

/-- **LIMITLESS FAILURE DICHOTOMY.** If the genuine algebraic Hodge fiber is
proper, then either it contains no nonzero seed or the actual unrestricted
cosmic matrix unit `E_01`, after recoordination, ejects an algebraic Hodge
state from the cycle-class range. -/
theorem proper_algebraicFiber_zero_or_limitlessCosmicEscape
    (hproper : AlgebraicFiber (V:=V) (H:=H) (p:=p) ≠ ⊤) :
    AlgebraicFiber (V:=V) (H:=H) (p:=p) = ⊥ ∨
      Nonempty (LimitlessCosmicEscape (V:=V) (H:=H) (p:=p)) := by
  rcases proper_algebraicFiber_zero_or_twoSlotEscape
      (V:=V) (H:=H) (p:=p) hproper with hzero | hescape
  · exact Or.inl hzero
  · exact Or.inr ⟨hescape.some.toLimitlessCosmicEscape⟩

/-- Conversely, stability under the one true cosmic `E_01` in every two-sheet
recoordination gives full rank-free arsenal invariance. -/
theorem rankFreeInvariant_of_limitlessCosmicStable
    (hstable :
      ∀ i j : ClassicalHodgeBasisIndex V H p,
      ∀ alpha ∈ AlgebraicFiber (V:=V) (H:=H) (p:=p),
        liftCosmicWindowOperator (pairBasisIndex i j)
            (rationalCosmicMatrixUnit sourceSlot.1 targetSlot.1) alpha ∈
          AlgebraicFiber (V:=V) (H:=H) (p:=p)) :
    RankFreeArsenalInvariant
      (AlgebraicFiber (V:=V) (H:=H) (p:=p)) := by
  intro i j alpha halpha
  rw [hodgeMatrixUnit_eq_lift_limitless_cosmic]
  exact hstable i j alpha halpha

/-- One nonzero algebraic seed plus stability under the single limitless cosmic
read/write matrix unit in all two-sheet recoordination charts saturates the
entire genuine Hodge fiber. -/
theorem algebraicFiber_eq_top_of_seed_and_limitlessCosmicStable
    (hseed : AlgebraicFiber (V:=V) (H:=H) (p:=p) ≠ ⊥)
    (hstable :
      ∀ i j : ClassicalHodgeBasisIndex V H p,
      ∀ alpha ∈ AlgebraicFiber (V:=V) (H:=H) (p:=p),
        liftCosmicWindowOperator (pairBasisIndex i j)
            (rationalCosmicMatrixUnit sourceSlot.1 targetSlot.1) alpha ∈
          AlgebraicFiber (V:=V) (H:=H) (p:=p)) :
    AlgebraicFiber (V:=V) (H:=H) (p:=p) = ⊤ := by
  exact rankFreeArsenalInvariant_eq_top _
    (rankFreeInvariant_of_limitlessCosmicStable hstable) hseed

#check embedWindow
#check readWindow
#check readWindow_embedWindow
#check finiteMatrixUnit_is_cosmic_observation
#check forwardArsenalWord_is_limitless_cosmic_observation
#check liftCosmicWindowOperator
#check hodgeMatrixUnit_eq_lift_limitless_cosmic
#check LimitlessCosmicEscape
#check proper_algebraicFiber_zero_or_limitlessCosmicEscape
#check algebraicFiber_eq_top_of_seed_and_limitlessCosmicStable

#print axioms readWindow_embedWindow
#print axioms finiteMatrixUnit_is_cosmic_observation
#print axioms forwardArsenalWord_is_limitless_cosmic_observation
#print axioms hodgeMatrixUnit_eq_lift_limitless_cosmic
#print axioms proper_algebraicFiber_zero_or_limitlessCosmicEscape
#print axioms algebraicFiber_eq_top_of_seed_and_limitlessCosmicStable

end GSTClassicalHodgeLimitlessTwoSlotFailureDichotomy
