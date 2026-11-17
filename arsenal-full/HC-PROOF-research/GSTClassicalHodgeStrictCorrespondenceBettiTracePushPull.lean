import GSTClassicalHodgeStrictCorrespondenceMaximalBettiTransfer
import GSTClassicalHodgeStrictCorrespondenceChainTranspose
import GSTClassicalHodgeGradedFiniteClosedCorrespondence
import GSTGeometricRealizationStage2D

set_option maxHeartbeats 100000000
set_option maxRecDepth 1000000

noncomputable section

open CategoryTheory
open AlgebraicGeometry

namespace GSTClassicalHodgeStrictCorrespondenceBettiTracePushPull

open GSTProjectiveOverC
open GSTGeometricRealizationStage2F
open GSTGeometricRealizationStage2G
open GSTGeometricRealizationStage2D
open GSTNativeCodimensionCyclePresentation
open GSTClassicalHodgeSchemeFiniteCorrespondenceFirewall
open GSTClassicalHodgeStrictCorrespondenceAnalyticSpan
open GSTClassicalHodgeStrictCorrespondenceBettiObstruction
open GSTClassicalHodgeStrictCorrespondenceMaximalBettiTransfer
open GSTClassicalHodgeFiniteClosedCorrespondence
open GSTClassicalHodgeGradedFiniteClosedCorrespondence

variable {V : SmoothProjectiveComplexScheme}
variable (A : AnalytificationData V)
variable (K : SchemeBiFiniteClosedCorrespondence V)
variable (n : Nat)

abbrev XCoh := RationalSingularCohomology A n
abbrev CCoh := CarrierCohomology A K n

/-- Finite-map Betti trace for the right projection.  This is the geometric
covariant leg missing from the intrinsic pullback span. -/
structure RightFiniteBettiTrace where
  trace : CCoh A K n →ₗ[ℚ] XCoh A n
  degree : ℚ
  degree_ne_zero : degree ≠ 0
  trace_rightPullback :
    trace.comp (rightCohomologyPullback A K n) =
      degree • LinearMap.id

namespace RightFiniteBettiTrace

noncomputable def normalizedTrace
    (T : RightFiniteBettiTrace A K n) :
    CCoh A K n →ₗ[ℚ] XCoh A n :=
  T.degree⁻¹ • T.trace

/-- The normalized trace is an exact left inverse of the right pullback. -/
theorem normalizedTrace_rightPullback
    (T : RightFiniteBettiTrace A K n) :
    T.normalizedTrace.comp (rightCohomologyPullback A K n) = LinearMap.id := by
  ext alpha
  have h := LinearMap.congr_fun T.trace_rightPullback alpha
  simp only [LinearMap.comp_apply, LinearMap.smul_apply, LinearMap.id_apply,
    RightFiniteBettiTrace.normalizedTrace] at h ⊢
  rw [h, smul_smul, inv_mul_cancel₀ T.degree_ne_zero, one_smul]

/-- **TOTAL WHOLE-BETTI PUSH-PULL.** `Tr_r ∘ l^*`, defined on every rational
singular cohomology class, including nonalgebraic Hodge classes. -/
noncomputable def pushPull
    (T : RightFiniteBettiTrace A K n) : XCoh A n →ₗ[ℚ] XCoh A n :=
  T.normalizedTrace.comp (leftCohomologyPullback A K n)

@[simp]
theorem pushPull_apply
    (T : RightFiniteBettiTrace A K n)
    (alpha : XCoh A n) :
    (pushPull A K n T) alpha =
      (normalizedTrace A K n T) (leftCohomologyPullback A K n alpha) := rfl

/-- Pointwise form of the trace's proved left-inverse law. -/
@[simp]
theorem normalizedTrace_rightPullback_apply
    (T : RightFiniteBettiTrace A K n) (alpha : XCoh A n) :
    (normalizedTrace A K n T) (rightCohomologyPullback A K n alpha) = alpha := by
  have h := LinearMap.congr_fun T.normalizedTrace_rightPullback alpha
  simpa only [LinearMap.comp_apply, LinearMap.id_apply] using h

/-- Nonzero finite degree forces injectivity of right pullback. -/
theorem rightPullback_injective
    (T : RightFiniteBettiTrace A K n) :
    Function.Injective (rightCohomologyPullback A K n) := by
  intro alpha beta h
  have h' := congrArg T.normalizedTrace h
  simpa [T.normalizedTrace_rightPullback_apply] using h'


/-- Direct elimination of a strict relation, using only the left-inverse law.
No totality of the relation or choice of a second related target is needed. -/
theorem pushPull_eq_of_bettiRelated
    (T : RightFiniteBettiTrace A K n)
    {alpha beta : XCoh A n} (h : BettiRelated A K n alpha beta) :
    (pushPull A K n T) alpha = beta := by
  rw [pushPull_apply, show leftCohomologyPullback A K n alpha =
    rightCohomologyPullback A K n beta from h]
  exact normalizedTrace_rightPullback_apply A K n T beta

/-- The carrier's right-pullback projection supplied by the trace. -/
noncomputable def carrierProjection
    (T : RightFiniteBettiTrace A K n) : CCoh A K n →ₗ[ℚ] CCoh A K n :=
  (rightCohomologyPullback A K n).comp T.normalizedTrace

/-- The carrier component discarded by normalized trace push-pull. -/
noncomputable def carrierResidual
    (T : RightFiniteBettiTrace A K n) : CCoh A K n →ₗ[ℚ] CCoh A K n :=
  LinearMap.id - T.carrierProjection

/-- Exact reconstruction of any intrinsic carrier class. -/
theorem carrier_decomposition
    (T : RightFiniteBettiTrace A K n) (omega : CCoh A K n) :
    omega = rightCohomologyPullback A K n ((normalizedTrace A K n T) omega) +
      (carrierResidual A K n T) omega := by
  change omega = rightCohomologyPullback A K n ((normalizedTrace A K n T) omega) +
    (omega - rightCohomologyPullback A K n ((normalizedTrace A K n T) omega))
  abel

/-- The residual is invisible to the trace, by a proved cancellation. -/
@[simp]
theorem normalizedTrace_carrierResidual
    (T : RightFiniteBettiTrace A K n) (omega : CCoh A K n) :
    (normalizedTrace A K n T) ((carrierResidual A K n T) omega) = 0 := by
  change (normalizedTrace A K n T)
    (omega - rightCohomologyPullback A K n ((normalizedTrace A K n T) omega)) = 0
  rw [map_sub, normalizedTrace_rightPullback_apply A K n T, sub_self]

/-- Projection onto the actual right-pullback range is idempotent. -/
theorem carrierProjection_idempotent
    (T : RightFiniteBettiTrace A K n) :
    T.carrierProjection.comp T.carrierProjection = T.carrierProjection := by
  ext omega
  change rightCohomologyPullback A K n
    ((normalizedTrace A K n T) (rightCohomologyPullback A K n
      ((normalizedTrace A K n T) omega))) =
    rightCohomologyPullback A K n ((normalizedTrace A K n T) omega)
  rw [normalizedTrace_rightPullback_apply A K n T]

/-- The residual vanishes exactly on the genuine right-pullback range. -/
theorem carrierResidual_eq_zero_iff
    (T : RightFiniteBettiTrace A K n) (omega : CCoh A K n) :
    (carrierResidual A K n T) omega = 0 ↔
      omega ∈ LinearMap.range (rightCohomologyPullback A K n) := by
  change omega - rightCohomologyPullback A K n ((normalizedTrace A K n T) omega) = 0 ↔ _
  rw [sub_eq_zero]
  constructor
  · intro h
    exact ⟨(normalizedTrace A K n T) omega, h.symm⟩
  · rintro ⟨beta, rfl⟩
    rw [T.normalizedTrace_rightPullback_apply]

/-- Uniqueness for the decomposition associated with this fixed trace:
right-pulled target plus a trace-zero carrier residual. -/
theorem carrier_decomposition_unique
    (T : RightFiniteBettiTrace A K n)
    (omega : CCoh A K n) (beta : XCoh A n) (eta : CCoh A K n)
    (heq : omega = rightCohomologyPullback A K n beta + eta)
    (hzero : (normalizedTrace A K n T) eta = 0) :
    beta = (normalizedTrace A K n T) omega ∧ eta = (carrierResidual A K n T) omega := by
  have hb : (normalizedTrace A K n T) omega = beta := by
    rw [heq, map_add, normalizedTrace_rightPullback_apply A K n T, hzero, add_zero]
  refine ⟨hb.symm, ?_⟩
  change eta = omega - rightCohomologyPullback A K n ((normalizedTrace A K n T) omega)
  rw [hb, heq]
  abel

/-- Intrinsic source defect retained on the correspondence carrier. -/
noncomputable def sourceResidual
    (T : RightFiniteBettiTrace A K n) : XCoh A n →ₗ[ℚ] CCoh A K n :=
  T.carrierResidual.comp (leftCohomologyPullback A K n)

/-- A strict common plane needs BOTH a zero carrier defect and the prescribed
target.  Merely defining a total push-pull map does not prove either condition. -/
theorem bettiRelated_iff_residual_and_target
    (T : RightFiniteBettiTrace A K n) (alpha beta : XCoh A n) :
    BettiRelated A K n alpha beta ↔
      (sourceResidual A K n T) alpha = 0 ∧ (pushPull A K n T) alpha = beta := by
  have hres : (sourceResidual A K n T) alpha = 0 ↔
      leftCohomologyPullback A K n alpha =
        rightCohomologyPullback A K n ((pushPull A K n T) alpha) := by
    change leftCohomologyPullback A K n alpha -
      rightCohomologyPullback A K n ((pushPull A K n T) alpha) = 0 ↔ _
    exact sub_eq_zero
  constructor
  · intro h
    have ht := pushPull_eq_of_bettiRelated A K n T h
    refine ⟨hres.2 ?_, ht⟩
    rw [ht]
    exact h
  · rintro ⟨hr, ht⟩
    have h := hres.1 hr
    rw [ht] at h
    exact h

/-- The carrier defect is an explicit representative of the existing quotient
obstruction: its zero locus is the exact transferable subspace. -/
theorem sourceResidual_eq_zero_iff_transferObstruction
    (T : RightFiniteBettiTrace A K n) (alpha : XCoh A n) :
    (sourceResidual A K n T) alpha = 0 ↔ transferObstruction A K n alpha = 0 := by
  change (carrierResidual A K n T) (leftCohomologyPullback A K n alpha) = 0 ↔ _
  rw [T.carrierResidual_eq_zero_iff]
  exact (transferObstruction_apply_eq_zero_iff A K n alpha).symm

/-- Different valid finite traces agree on every intrinsically transferable
source, even if their extensions away from that locus differ. -/
theorem pushPull_independent_on_transferable
    (T U : RightFiniteBettiTrace A K n) (alpha : XCoh A n)
    (h : transferObstruction A K n alpha = 0) :
    (pushPull A K n T) alpha = (pushPull A K n U) alpha := by
  obtain ⟨beta, hb⟩ :=
    (transferObstruction_apply_eq_zero_iff_exists_related A K n alpha).1 h
  exact (pushPull_eq_of_bettiRelated A K n T hb).trans
    (pushPull_eq_of_bettiRelated A K n U hb).symm

#print axioms carrier_decomposition
#print axioms carrier_decomposition_unique
#print axioms carrierProjection_idempotent
#print axioms bettiRelated_iff_residual_and_target
#print axioms sourceResidual_eq_zero_iff_transferObstruction
#print axioms pushPull_independent_on_transferable

/-- Finite trace removes the target ambiguity in GLM's maximal transfer. -/
theorem targetAmbiguity_eq_bot
    (T : RightFiniteBettiTrace A K n) :
    GSTClassicalHodgeStrictCorrespondenceMaximalBettiTransfer.targetAmbiguity A K n = ⊥ := by
  exact GSTClassicalHodgeStrictCorrespondenceMaximalBettiTransfer.targetAmbiguity_eq_bot
    A K n T.rightPullback_injective

/-- On every class on which the relation transfer is defined, trace push-pull
satisfies exactly the original strict Betti relation. -/
theorem pushPull_related_of_transferable
    (T : RightFiniteBettiTrace A K n)
    (alpha : GSTClassicalHodgeStrictCorrespondenceMaximalBettiTransfer.transferableSubspace A K n) :
    BettiRelated A K n alpha.1 ((pushPull A K n T) alpha.1) := by
  have hmem := GSTClassicalHodgeStrictCorrespondenceMaximalBettiTransfer.transferable_left_mem_rightRange
    A K n alpha
  rcases hmem with ⟨beta, hbeta⟩
  have hrel : leftCohomologyPullback A K n alpha.1 =
      rightCohomologyPullback A K n beta := hbeta.symm
  have hpush : (pushPull A K n T) alpha.1 = beta := by
    rw [pushPull_apply A K n T alpha.1, hrel]
    have hs := LinearMap.congr_fun T.normalizedTrace_rightPullback beta
    simpa [LinearMap.comp_apply] using hs
  rw [hpush]
  exact hrel

/-- **MAXIMAL-TRANSFER FUSION.** GLM's canonical partial quotient transfer is
exactly the quotient class of the independently constructed total trace
push-pull. -/
theorem maximalBettiTransfer_eq_pushPull_mod_ambiguity
    (T : RightFiniteBettiTrace A K n)
    (alpha : GSTClassicalHodgeStrictCorrespondenceMaximalBettiTransfer.transferableSubspace A K n) :
    GSTClassicalHodgeStrictCorrespondenceMaximalBettiTransfer.maximalBettiTransfer A K n alpha =
      Submodule.Quotient.mk ((pushPull A K n T) alpha.1) := by
  symm
  exact (GSTClassicalHodgeStrictCorrespondenceMaximalBettiTransfer.quotient_eq_maximalTransfer_iff_related
    A K n alpha ((pushPull A K n T) alpha.1)).2
      (pushPull_related_of_transferable A K n T alpha)

end RightFiniteBettiTrace

/-- Forward and actual algebraic-transpose traces. -/
structure BiFiniteBettiTrace where
  forward : RightFiniteBettiTrace A K n
  transpose : RightFiniteBettiTrace A K.transpose n

namespace BiFiniteBettiTrace

noncomputable def forwardAction
    (T : BiFiniteBettiTrace A K n) : XCoh A n →ₗ[ℚ] XCoh A n :=
  T.forward.pushPull

noncomputable def transposeAction
    (T : BiFiniteBettiTrace A K n) : XCoh A n →ₗ[ℚ] XCoh A n :=
  T.transpose.pushPull

end BiFiniteBettiTrace

/-- Compare the independently constructed push-pull with the native finite
incidence action only on point cycles; compact point normal form then globalizes
this to every native cycle. -/
structure PointCycleCompatibility
    {H : HodgeBigradedBettiData V}
    (K : SchemeBiFiniteClosedCorrespondence V)
    (T : RightFiniteBettiTrace H.analytification K (2 * n)) where
  point_natural :
    ∀ x : CodimensionPoint V.X n,
      H.cycleClass n
          (K.toBiFiniteClosedCorrespondence.toFiniteClosedCorrespondence
            |>.gradedNativePointImage n x) =
        (RightFiniteBettiTrace.pushPull H.analytification K (2 * n) T)
          (H.cycleClass n (codimensionPointCycle V.X n x))

namespace PointCycleCompatibility

noncomputable def toGradedCorrespondencePointNaturality
    {H : HodgeBigradedBettiData V}
    {K : SchemeBiFiniteClosedCorrespondence V}
    {T : RightFiniteBettiTrace H.analytification K (2 * n)}
    (C : PointCycleCompatibility (n := n) K T) :
    GradedCorrespondencePointNaturality
      K.toBiFiniteClosedCorrespondence.toFiniteClosedCorrespondence H n n where
  cohomologyOperator :=
    RightFiniteBettiTrace.pushPull H.analytification K (2 * n) T
  point_natural := C.point_natural

/-- **PROJECTIVE-INCIDENCE NATURALITY CROWN.** -/
theorem cycleClass_natural
    {H : HodgeBigradedBettiData V}
    {K : SchemeBiFiniteClosedCorrespondence V}
    {T : RightFiniteBettiTrace H.analytification K (2 * n)}
    (C : PointCycleCompatibility (n := n) K T)
    (Z : codimensionCycles V.X n) :
    H.cycleClass n
        (K.toBiFiniteClosedCorrespondence.toFiniteClosedCorrespondence
          |>.gradedNativeCycleOperator n n Z) =
      (RightFiniteBettiTrace.pushPull H.analytification K (2 * n) T)
        (H.cycleClass n Z) := by
  exact C.toGradedCorrespondencePointNaturality.cycleClass_natural Z

end PointCycleCompatibility

#check RightFiniteBettiTrace
#check RightFiniteBettiTrace.normalizedTrace_rightPullback
#check RightFiniteBettiTrace.rightPullback_injective
#check RightFiniteBettiTrace.pushPull
#check RightFiniteBettiTrace.maximalBettiTransfer_eq_pushPull_mod_ambiguity
#check BiFiniteBettiTrace
#check PointCycleCompatibility.cycleClass_natural

#print axioms RightFiniteBettiTrace.normalizedTrace_rightPullback
#print axioms RightFiniteBettiTrace.maximalBettiTransfer_eq_pushPull_mod_ambiguity
#print axioms PointCycleCompatibility.cycleClass_natural

end GSTClassicalHodgeStrictCorrespondenceBettiTracePushPull
