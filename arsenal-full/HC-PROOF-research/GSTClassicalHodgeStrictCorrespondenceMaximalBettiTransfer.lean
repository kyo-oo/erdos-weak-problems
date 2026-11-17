import GSTClassicalHodgeStrictCorrespondenceBettiObstruction

/-!
# GST CLASSICAL HODGE — MAXIMAL CANONICAL BETTI TRANSFER

For a strict scheme-bi-finite correspondence the intrinsic analytic span gives

    l^*, r^* : H^n(X,Q) -> H^n(C_an,Q)

and the transfer obstruction

    Omega_K(alpha) = [l^* alpha] mod range(r^*).

Even before one proves `Omega_K = 0` or injectivity of `r^*`, there is already
a completely canonical, choice-free correspondence action on the largest
possible source and with the smallest unavoidable target ambiguity:

    ker(Omega_K)  --->  H^n(X,Q) / ker(r^*).

Indeed `alpha in ker Omega_K` says `l^* alpha` belongs to `range(r^*)`; the
first isomorphism theorem then identifies that range canonically with the
quotient by `ker(r^*)`.  This file constructs exactly that map.

It is the maximal operator determined by the strict analytic correspondence
relation itself.  No Hodge basis, algebraic cycle selector, arbitrary linear
extension, or choice of target representative occurs.
-/

set_option maxHeartbeats 100000000
set_option maxRecDepth 1000000

noncomputable section

open CategoryTheory
open AlgebraicGeometry

namespace GSTClassicalHodgeStrictCorrespondenceMaximalBettiTransfer

open GSTProjectiveOverC
open GSTGeometricRealizationStage2F
open GSTClassicalHodgeSchemeFiniteCorrespondenceFirewall
open GSTClassicalHodgeStrictCorrespondenceAnalyticSpan
open GSTClassicalHodgeStrictCorrespondenceBettiObstruction

variable {V : SmoothProjectiveComplexScheme}
variable (A : AnalytificationData V)
variable (K : SchemeBiFiniteClosedCorrespondence V)
variable (n : Nat)

abbrev XCoh := RationalSingularCohomology A n
abbrev CCoh := CarrierCohomology A K n

/-- Largest subspace of ambient Betti cohomology on which the strict
correspondence relation has at least one target. -/
def transferableSubspace : Submodule ℚ (XCoh A n) :=
  LinearMap.ker (transferObstruction A K n)

/-- Unavoidable target ambiguity: two targets define the same relation iff
they differ by an element killed by the right pullback. -/
def targetAmbiguity : Submodule ℚ (XCoh A n) :=
  LinearMap.ker (rightCohomologyPullback A K n)

/-- Every transferable class has left pullback in the exact right-pullback
range. -/
theorem transferable_left_mem_rightRange
    (alpha : transferableSubspace A K n) :
    leftCohomologyPullback A K n alpha.1 ∈ rightPullbackRange A K n := by
  have hzero : transferObstruction A K n alpha.1 = 0 := by
    exact alpha.2
  exact (transferObstruction_apply_eq_zero_iff A K n alpha.1).1 hzero

/-- Left pullback regarded as an element of the actual right-pullback range. -/
noncomputable def transferableRangeMap :
    transferableSubspace A K n →ₗ[ℚ]
      LinearMap.range (rightCohomologyPullback A K n) where
  toFun := fun alpha =>
    ⟨leftCohomologyPullback A K n alpha.1,
      transferable_left_mem_rightRange A K n alpha⟩
  map_add' := by
    intro a b
    apply Subtype.ext
    simp
  map_smul' := by
    intro q a
    apply Subtype.ext
    simp

/-- **MAXIMAL CANONICAL STRICT-CORRESPONDENCE TRANSFER.**
Use the inverse first-isomorphism equivalence for `r^*` to turn the left
pullback of a transferable class into a canonical target modulo the exact
kernel ambiguity. -/
noncomputable def maximalBettiTransfer :
    transferableSubspace A K n →ₗ[ℚ]
      (XCoh A n ⧸ targetAmbiguity A K n) :=
  (rightCohomologyPullback A K n).quotKerEquivRange.symm.toLinearMap.comp
    (transferableRangeMap A K n)

/-- The quotient target reconstructed by `maximalBettiTransfer` maps under the
first-isomorphism equivalence to exactly the genuine left pullback. -/
theorem maximalBettiTransfer_spec
    (alpha : transferableSubspace A K n) :
    (rightCohomologyPullback A K n).quotKerEquivRange
      (maximalBettiTransfer A K n alpha) =
        transferableRangeMap A K n alpha := by
  exact (rightCohomologyPullback A K n).quotKerEquivRange.apply_symm_apply
    (transferableRangeMap A K n alpha)

/-- Representative form: every representative of the canonical quotient
transfer is related to the source precisely when its quotient class is the
canonical transfer value. -/
theorem quotient_eq_maximalTransfer_iff_related
    (alpha : transferableSubspace A K n)
    (beta : XCoh A n) :
    Submodule.Quotient.mk beta = maximalBettiTransfer A K n alpha ↔
      BettiRelated A K n alpha.1 beta := by
  constructor
  · intro hq
    have hrange := congrArg
      (rightCohomologyPullback A K n).quotKerEquivRange hq
    rw [maximalBettiTransfer_spec] at hrange
    have hval : rightCohomologyPullback A K n beta =
        leftCohomologyPullback A K n alpha.1 :=
      congrArg Subtype.val hrange
    exact hval.symm
  · intro hrel
    apply (rightCohomologyPullback A K n).quotKerEquivRange.injective
    rw [maximalBettiTransfer_spec]
    apply Subtype.ext
    exact hrel.symm

/-- The maximal transfer is uniquely characterized by the strict analytic
relation modulo target ambiguity. -/
theorem maximalBettiTransfer_unique
    (T : transferableSubspace A K n →ₗ[ℚ]
      (XCoh A n ⧸ targetAmbiguity A K n))
    (hT : ∀ alpha : transferableSubspace A K n,
      (rightCohomologyPullback A K n).quotKerEquivRange (T alpha) =
        transferableRangeMap A K n alpha) :
    T = maximalBettiTransfer A K n := by
  apply LinearMap.ext
  intro alpha
  apply (rightCohomologyPullback A K n).quotKerEquivRange.injective
  rw [hT, maximalBettiTransfer_spec]

/-- If the obstruction vanishes globally, the transferable subspace is the
whole Betti carrier. -/
theorem transferableSubspace_eq_top
    (htotal : transferObstruction A K n = 0) :
    transferableSubspace A K n = ⊤ := by
  rw [transferableSubspace, htotal]
  exact LinearMap.ker_zero

/-- If `r^*` is injective, the target ambiguity vanishes. -/
theorem targetAmbiguity_eq_bot
    (hright : Function.Injective (rightCohomologyPullback A K n)) :
    targetAmbiguity A K n = ⊥ := by
  exact LinearMap.ker_eq_bot.mpr hright

#check transferableSubspace
#check targetAmbiguity
#check transferableRangeMap
#check maximalBettiTransfer
#check maximalBettiTransfer_spec
#check quotient_eq_maximalTransfer_iff_related
#check maximalBettiTransfer_unique
#check transferableSubspace_eq_top
#check targetAmbiguity_eq_bot

end GSTClassicalHodgeStrictCorrespondenceMaximalBettiTransfer
