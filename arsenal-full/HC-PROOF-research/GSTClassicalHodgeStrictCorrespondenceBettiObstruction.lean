import GSTClassicalHodgeStrictCorrespondenceAnalyticSpan

/-!
# GST CLASSICAL HODGE — STRICT CORRESPONDENCE BETTI TRANSFER OBSTRUCTION

The intrinsic analytic span of a strict scheme-bi-finite correspondence gives
canonical pullbacks

  l^*, r^* : H^n(X,Q) -> H^n(C_an,Q)

on the COMPLETE rational singular cohomology carrier.  Turning this span into
a single-valued correspondence operator means solving

  r^*(beta) = l^*(alpha)

for beta, for every alpha.  This file isolates that problem exactly as one
quotient-valued linear obstruction.

No arbitrary extension is chosen.  No Hodge algebraicity is assumed.  The
obstruction vanishes on a class precisely when the strict correspondence
relation has a target for that class; it vanishes identically precisely when
the relation is total.  If r^* is injective, the target is automatically
unique, hence the geometric relation becomes a canonical full-Betti operator.

This is the precise algebraic-topology interface required by the final
push-pull construction.
-/

set_option maxHeartbeats 100000000
set_option maxRecDepth 1000000

noncomputable section

open CategoryTheory
open AlgebraicGeometry

namespace GSTClassicalHodgeStrictCorrespondenceBettiObstruction

open GSTProjectiveOverC
open GSTGeometricRealizationStage2F
open GSTClassicalHodgeSchemeFiniteCorrespondenceFirewall
open GSTClassicalHodgeStrictCorrespondenceAnalyticSpan

variable {V : SmoothProjectiveComplexScheme}
variable (A : AnalytificationData V)
variable (K : SchemeBiFiniteClosedCorrespondence V)
variable (n : Nat)

abbrev XCoh := RationalSingularCohomology A n
abbrev CCoh := CarrierCohomology A K n

/-- Range of the right Betti pullback.  A left-pulled class is transferable
exactly when it belongs to this range. -/
def rightPullbackRange : Submodule ℚ (CCoh A K n) :=
  LinearMap.range (rightCohomologyPullback A K n)

/-- **CANONICAL FULL-BETTI TRANSFER OBSTRUCTION.**
Quotient the carrier cohomology by the genuine right-pullback range and send an
ambient class through the left pullback.  No choices occur. -/
noncomputable def transferObstruction :
    XCoh A n →ₗ[ℚ] (CCoh A K n ⧸ rightPullbackRange A K n) :=
  (Submodule.mkQ (rightPullbackRange A K n)).comp
    (leftCohomologyPullback A K n)

/-- Vanishing of the obstruction on one class is exactly membership of its
left pullback in the right-pullback range. -/
theorem transferObstruction_apply_eq_zero_iff
    (alpha : XCoh A n) :
    transferObstruction A K n alpha = 0 ↔
      leftCohomologyPullback A K n alpha ∈ rightPullbackRange A K n := by
  rw [transferObstruction, LinearMap.comp_apply]
  exact Submodule.Quotient.mk_eq_zero _

/-- Range form expanded to the actual target class: obstruction zero iff there
exists beta with the exact intrinsic correspondence relation. -/
theorem transferObstruction_apply_eq_zero_iff_exists_related
    (alpha : XCoh A n) :
    transferObstruction A K n alpha = 0 ↔
      ∃ beta : XCoh A n, BettiRelated A K n alpha beta := by
  rw [transferObstruction_apply_eq_zero_iff]
  constructor
  · rintro ⟨beta, hbeta⟩
    exact ⟨beta, hbeta.symm⟩
  · rintro ⟨beta, hbeta⟩
    exact ⟨beta, hbeta.symm⟩

/-- The strict analytic relation is total on the complete Betti carrier iff the
single quotient-valued obstruction map vanishes identically. -/
theorem transferObstruction_eq_zero_iff_total :
    transferObstruction A K n = 0 ↔
      ∀ alpha : XCoh A n,
        ∃ beta : XCoh A n, BettiRelated A K n alpha beta := by
  constructor
  · intro h alpha
    have ha : transferObstruction A K n alpha = 0 := by rw [h]; rfl
    exact (transferObstruction_apply_eq_zero_iff_exists_related A K n alpha).1 ha
  · intro h
    apply LinearMap.ext
    intro alpha
    exact (transferObstruction_apply_eq_zero_iff_exists_related A K n alpha).2
      (h alpha)

/-- Injectivity of the right pullback makes correspondence targets unique. -/
theorem related_target_unique
    (hright : Function.Injective (rightCohomologyPullback A K n))
    {alpha beta gamma : XCoh A n}
    (hbeta : BettiRelated A K n alpha beta)
    (hgamma : BettiRelated A K n alpha gamma) :
    beta = gamma := by
  apply hright
  exact hbeta.symm.trans hgamma

/-- Once totality and right-pullback injectivity are proved, the relation itself
constructs a canonical linear operator on the entire Betti carrier. -/
noncomputable def canonicalBettiOperator
    (htotal : transferObstruction A K n = 0)
    (hright : Function.Injective (rightCohomologyPullback A K n)) :
    XCoh A n →ₗ[ℚ] XCoh A n where
  toFun := fun alpha =>
    Classical.choose
      ((transferObstruction_apply_eq_zero_iff_exists_related A K n alpha).1
        (by rw [htotal]; rfl))
  map_add' := by
    intro alpha beta
    apply hright
    let wa := Classical.choose
      ((transferObstruction_apply_eq_zero_iff_exists_related A K n alpha).1
        (by rw [htotal]; rfl))
    let wb := Classical.choose
      ((transferObstruction_apply_eq_zero_iff_exists_related A K n beta).1
        (by rw [htotal]; rfl))
    let wab := Classical.choose
      ((transferObstruction_apply_eq_zero_iff_exists_related A K n (alpha + beta)).1
        (by rw [htotal]; rfl))
    have ha := Classical.choose_spec
      ((transferObstruction_apply_eq_zero_iff_exists_related A K n alpha).1
        (by rw [htotal]; rfl))
    have hb := Classical.choose_spec
      ((transferObstruction_apply_eq_zero_iff_exists_related A K n beta).1
        (by rw [htotal]; rfl))
    have hab := Classical.choose_spec
      ((transferObstruction_apply_eq_zero_iff_exists_related A K n (alpha + beta)).1
        (by rw [htotal]; rfl))
    dsimp [BettiRelated] at ha hb hab ⊢
    simp only [map_add, ha, hb]
    rw [hab.symm, map_add, ← ha, ← hb]
  map_smul' := by
    intro q alpha
    apply hright
    let wa := Classical.choose
      ((transferObstruction_apply_eq_zero_iff_exists_related A K n alpha).1
        (by rw [htotal]; rfl))
    let wqa := Classical.choose
      ((transferObstruction_apply_eq_zero_iff_exists_related A K n (q • alpha)).1
        (by rw [htotal]; rfl))
    have ha := Classical.choose_spec
      ((transferObstruction_apply_eq_zero_iff_exists_related A K n alpha).1
        (by rw [htotal]; rfl))
    have hqa := Classical.choose_spec
      ((transferObstruction_apply_eq_zero_iff_exists_related A K n (q • alpha)).1
        (by rw [htotal]; rfl))
    dsimp [BettiRelated] at ha hqa ⊢
    simp only [map_smul, ha]
    rw [hqa.symm, map_smul, ← ha]

/-- The constructed operator satisfies the defining strict correspondence
pullback square on every rational singular cohomology class. -/
theorem canonicalBettiOperator_spec
    (htotal : transferObstruction A K n = 0)
    (hright : Function.Injective (rightCohomologyPullback A K n))
    (alpha : XCoh A n) :
    BettiRelated A K n alpha
      (canonicalBettiOperator A K n htotal hright alpha) := by
  exact Classical.choose_spec
    ((transferObstruction_apply_eq_zero_iff_exists_related A K n alpha).1
      (by rw [htotal]; rfl))

/-- Uniqueness: there is at most one full-Betti linear operator satisfying the
strict analytic correspondence equation once the right pullback is injective. -/
theorem canonicalBettiOperator_unique
    (hright : Function.Injective (rightCohomologyPullback A K n))
    (T U : XCoh A n →ₗ[ℚ] XCoh A n)
    (hT : ∀ alpha, BettiRelated A K n alpha (T alpha))
    (hU : ∀ alpha, BettiRelated A K n alpha (U alpha)) :
    T = U := by
  apply LinearMap.ext
  intro alpha
  exact related_target_unique A K n hright (hT alpha) (hU alpha)

#check rightPullbackRange
#check transferObstruction
#check transferObstruction_apply_eq_zero_iff_exists_related
#check transferObstruction_eq_zero_iff_total
#check related_target_unique
#check canonicalBettiOperator
#check canonicalBettiOperator_spec
#check canonicalBettiOperator_unique

end GSTClassicalHodgeStrictCorrespondenceBettiObstruction
