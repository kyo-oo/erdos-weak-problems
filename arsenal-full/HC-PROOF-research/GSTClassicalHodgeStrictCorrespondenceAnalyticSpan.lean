import GSTClassicalHodgeSchemeFiniteCorrespondenceFirewall
import GSTClassicalHodgeSingularCohomologyFunctoriality
import Mathlib.Algebra.Homology.ShortComplex.HomologicalComplex

/-!
# GST CLASSICAL HODGE — INTRINSIC ANALYTIC SPAN OF A STRICT CORRESPONDENCE

A strict correspondence `C -> X ×_C X` already contains enough information to
construct the analytic *span* needed by Betti functoriality.  No independently
supplied topology on `C` is necessary for this step.

We take actual complex points of the carrier over the left projection to the
complex base, send each carrier point to its pair of left/right complex points
of `X`, and topologize the image as the corresponding subspace of
`X^an × X^an`.  The two coordinate projections are then continuous by
construction.  Mathlib's singular-chain functor gives the corresponding chain
maps, dual cochain pullbacks, and induced maps on the full rational singular
cohomology carrier.

This is intentionally stronger than point-cycle naturality: the two pullbacks
are defined on every Betti class, including classes outside the algebraic
cycle-class range.  No Hodge algebraicity statement enters the construction.

The remaining covariant leg of classical push-pull is isolated after this
module; it is no longer entangled with analytification or point-kernel
semantics.
-/

set_option maxHeartbeats 100000000
set_option maxRecDepth 1000000

noncomputable section

open CategoryTheory
open CategoryTheory.Limits
open AlgebraicGeometry
open AlgebraicTopology

namespace GSTClassicalHodgeStrictCorrespondenceAnalyticSpan

open GSTProjectiveOverC
open GSTGeometricRealizationStage2F
open GSTClassicalHodgeProjectiveSelfCorrespondences
open GSTClassicalHodgeSchemeFiniteCorrespondenceFirewall

variable {V : SmoothProjectiveComplexScheme}
variable (A : AnalytificationData V)

/-- Actual complex points of the strict carrier, using the left projection to
supply its map to `Spec C`. -/
abbrev CarrierComplexPoint
    (K : SchemeBiFiniteClosedCorrespondence V) :=
  { z : complexBase ⟶ K.carrier //
      (z ≫ K.toSchemeFiniteClosedCorrespondence.left) ≫ V.structureMap =
        𝟙 complexBase }

/-- Left projection of a carrier complex point. -/
def leftComplexPoint
    (K : SchemeBiFiniteClosedCorrespondence V)
    (z : CarrierComplexPoint K) : ComplexPoint V := by
  refine ⟨z.1 ≫ K.toSchemeFiniteClosedCorrespondence.left, ?_⟩
  simpa using z.2

/-- The two strict carrier projections have the same map to the complex base. -/
theorem left_toBase_eq_right_toBase
    (K : SchemeBiFiniteClosedCorrespondence V) :
    K.toSchemeFiniteClosedCorrespondence.left ≫ V.structureMap =
      K.right ≫ V.structureMap := by
  change (K.intoProduct ≫ fst V) ≫ V.structureMap =
    (K.intoProduct ≫ snd V) ≫ V.structureMap
  simp only [Category.assoc]
  rw [fst_toBase_eq_snd_toBase]

/-- Right projection of the same carrier complex point. -/
def rightComplexPoint
    (K : SchemeBiFiniteClosedCorrespondence V)
    (z : CarrierComplexPoint K) : ComplexPoint V := by
  refine ⟨z.1 ≫ K.right, ?_⟩
  calc
    (z.1 ≫ K.right) ≫ V.structureMap =
        z.1 ≫ (K.right ≫ V.structureMap) := by simp [Category.assoc]
    _ = z.1 ≫
        (K.toSchemeFiniteClosedCorrespondence.left ≫ V.structureMap) := by
          rw [← left_toBase_eq_right_toBase K]
    _ = 𝟙 complexBase := by simpa [Category.assoc] using z.2

/-- Pair of analytic `X`-points carried by one genuine point of `C`. -/
def carrierPointPair
    (K : SchemeBiFiniteClosedCorrespondence V) :
    CarrierComplexPoint K → A.space × A.space :=
  fun z =>
    (A.pointsEquiv (leftComplexPoint K z),
      A.pointsEquiv (rightComplexPoint K z))

/-- Intrinsic analytic locus of the correspondence inside `X^an × X^an`. -/
def analyticLocus
    (K : SchemeBiFiniteClosedCorrespondence V) : Set (A.space × A.space) :=
  Set.range (carrierPointPair A K)

/-- The analytic carrier used for singular (co)homology: the actual image of
carrier complex points inside the product analytification.  It inherits the
subspace topology and therefore needs no independent topology field. -/
noncomputable def analyticCarrier
    (K : SchemeBiFiniteClosedCorrespondence V) : TopCat :=
  TopCat.of (analyticLocus A K)

/-- Continuous left analytic projection. -/
noncomputable def analyticLeft
    (K : SchemeBiFiniteClosedCorrespondence V) :
    analyticCarrier A K ⟶ A.space :=
  ConcreteCategory.ofHom (C := TopCat)
    ⟨(fun z => z.1.1), continuous_fst.comp continuous_subtype_val⟩

/-- Continuous right analytic projection. -/
noncomputable def analyticRight
    (K : SchemeBiFiniteClosedCorrespondence V) :
    analyticCarrier A K ⟶ A.space :=
  ConcreteCategory.ofHom (C := TopCat)
    ⟨(fun z => z.1.2), continuous_snd.comp continuous_subtype_val⟩

/-- Genuine rational singular chains of the intrinsic analytic carrier. -/
noncomputable def carrierSingularChains
    (K : SchemeBiFiniteClosedCorrespondence V) :
    ChainComplex (ModuleCat ℚ) ℕ :=
  ((singularChainComplexFunctor (ModuleCat ℚ)).obj rationalCoefficient).obj
    (analyticCarrier A K)

/-- Genuine rational singular cochains of the intrinsic analytic carrier. -/
noncomputable def carrierSingularCochains
    (K : SchemeBiFiniteClosedCorrespondence V) :
    CochainComplex (ModuleCat ℚ) ℕ :=
  (carrierSingularChains A K).linearYonedaObj ℚ rationalCoefficient

/-- Native rational singular cohomology of the intrinsic carrier. -/
noncomputable def carrierCohomologyObj
    (K : SchemeBiFiniteClosedCorrespondence V)
    (n : Nat) : ModuleCat ℚ :=
  (carrierSingularCochains A K).homology n

abbrev CarrierCohomology
    (K : SchemeBiFiniteClosedCorrespondence V)
    (n : Nat) : Type :=
  carrierCohomologyObj A K n

/-- Covariant singular-chain map induced by the left projection. -/
noncomputable def leftChainMap
    (K : SchemeBiFiniteClosedCorrespondence V) :
    carrierSingularChains A K ⟶ rationalSingularChains A :=
  ((singularChainComplexFunctor (ModuleCat ℚ)).obj rationalCoefficient).map
    (analyticLeft A K)

/-- Covariant singular-chain map induced by the right projection. -/
noncomputable def rightChainMap
    (K : SchemeBiFiniteClosedCorrespondence V) :
    carrierSingularChains A K ⟶ rationalSingularChains A :=
  ((singularChainComplexFunctor (ModuleCat ℚ)).obj rationalCoefficient).map
    (analyticRight A K)

/-- Contravariant cochain pullback along the left projection. -/
noncomputable def leftCochainPullback
    (K : SchemeBiFiniteClosedCorrespondence V) :
    rationalSingularCochains A ⟶ carrierSingularCochains A K := by
  unfold rationalSingularCochains carrierSingularCochains
  exact (HomologicalComplex.unopFunctor (ModuleCat ℚ) (ComplexShape.down ℕ)).map
    (Quiver.Hom.op
      ((((CategoryTheory.linearYoneda ℚ (ModuleCat ℚ)).obj rationalCoefficient).rightOp
        |>.mapHomologicalComplex (ComplexShape.down ℕ)).map
        (leftChainMap A K)))

/-- Contravariant cochain pullback along the right projection. -/
noncomputable def rightCochainPullback
    (K : SchemeBiFiniteClosedCorrespondence V) :
    rationalSingularCochains A ⟶ carrierSingularCochains A K := by
  unfold rationalSingularCochains carrierSingularCochains
  exact (HomologicalComplex.unopFunctor (ModuleCat ℚ) (ComplexShape.down ℕ)).map
    (Quiver.Hom.op
      ((((CategoryTheory.linearYoneda ℚ (ModuleCat ℚ)).obj rationalCoefficient).rightOp
        |>.mapHomologicalComplex (ComplexShape.down ℕ)).map
        (rightChainMap A K)))

/-- Full Betti pullback along the left leg. -/
noncomputable def leftCohomologyPullbackObj
    (K : SchemeBiFiniteClosedCorrespondence V)
    (n : Nat) :
    rationalSingularCohomologyObj A n ⟶ carrierCohomologyObj A K n :=
  HomologicalComplex.homologyMap (leftCochainPullback A K) n

/-- Full Betti pullback along the right leg. -/
noncomputable def rightCohomologyPullbackObj
    (K : SchemeBiFiniteClosedCorrespondence V)
    (n : Nat) :
    rationalSingularCohomologyObj A n ⟶ carrierCohomologyObj A K n :=
  HomologicalComplex.homologyMap (rightCochainPullback A K) n

/-- Underlying rational-linear left pullback on every Betti class. -/
noncomputable def leftCohomologyPullback
    (K : SchemeBiFiniteClosedCorrespondence V)
    (n : Nat) :
    RationalSingularCohomology A n →ₗ[ℚ] CarrierCohomology A K n :=
  (leftCohomologyPullbackObj A K n).hom

/-- Underlying rational-linear right pullback on every Betti class. -/
noncomputable def rightCohomologyPullback
    (K : SchemeBiFiniteClosedCorrespondence V)
    (n : Nat) :
    RationalSingularCohomology A n →ₗ[ℚ] CarrierCohomology A K n :=
  (rightCohomologyPullbackObj A K n).hom

/-- Canonical full-Betti relation cut out by the analytic correspondence span.
Unlike a freely extended operator, this relation is determined on every class
by the actual closed carrier and its two projections. -/
def BettiRelated
    (K : SchemeBiFiniteClosedCorrespondence V)
    (n : Nat)
    (alpha beta : RationalSingularCohomology A n) : Prop :=
  leftCohomologyPullback A K n alpha = rightCohomologyPullback A K n beta

/-- The first genuinely gauge-free cohomological object attached to a strict
closed correspondence: two native pullbacks into one intrinsic carrier
cohomology. -/
structure IntrinsicBettiSpan
    (K : SchemeBiFiniteClosedCorrespondence V)
    (n : Nat) where
  carrier : Type := CarrierCohomology A K n
  addCommGroup : AddCommGroup carrier
  moduleQ : Module ℚ carrier
  left : RationalSingularCohomology A n →ₗ[ℚ] carrier
  right : RationalSingularCohomology A n →ₗ[ℚ] carrier

/-- Canonical intrinsic span of a strict scheme correspondence. -/
noncomputable def intrinsicBettiSpan
    (K : SchemeBiFiniteClosedCorrespondence V)
    (n : Nat) : IntrinsicBettiSpan A K n where
  carrier := CarrierCohomology A K n
  addCommGroup := inferInstance
  moduleQ := inferInstance
  left := leftCohomologyPullback A K n
  right := rightCohomologyPullback A K n

#check CarrierComplexPoint
#check analyticLocus
#check analyticCarrier
#check analyticLeft
#check analyticRight
#check carrierSingularChains
#check leftCohomologyPullback
#check rightCohomologyPullback
#check BettiRelated
#check IntrinsicBettiSpan
#check intrinsicBettiSpan

#print axioms left_toBase_eq_right_toBase

end GSTClassicalHodgeStrictCorrespondenceAnalyticSpan
