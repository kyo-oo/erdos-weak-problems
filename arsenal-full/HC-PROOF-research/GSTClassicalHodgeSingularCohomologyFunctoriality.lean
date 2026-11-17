import GSTClassicalHodgeAnalytificationFunctoriality
import Mathlib.Algebra.Homology.ShortComplex.HomologicalComplex

/-!
# GST CLASSICAL HODGE — NATIVE SINGULAR-COHOMOLOGY FUNCTORIALITY

A continuous endomorphism of the supplied analytification acts covariantly on
Mathlib's genuine rational singular chain complex.  Linear Yoneda duality
reverses that map on cochains, and `HomologicalComplex.homologyMap` then gives
the induced pullback on the actual rational Betti cohomology object used by
Stage 2F/2G.

This removes the arbitrary "cohomology operator" from the externalization
step: once a projective algebraic transport is analytically continuous, its
Betti action is constructed by the native singular complex.
-/

set_option maxHeartbeats 10000000
set_option maxRecDepth 1000000

noncomputable section

open CategoryTheory
open AlgebraicTopology
open GSTProjectiveOverC
open GSTGeometricRealizationStage2F
open GSTClassicalHodgeAnalytificationFunctoriality

namespace GSTClassicalHodgeSingularCohomologyFunctoriality

variable {V : SmoothProjectiveComplexScheme}
variable (A : AnalytificationData V)

/-- Covariant singular-chain map of one analytic endomorphism. -/
noncomputable def singularChainMap
    (f : AnalyticEndomorphism A) :
    rationalSingularChains A ⟶ rationalSingularChains A :=
  ((singularChainComplexFunctor (ModuleCat ℚ)).obj rationalCoefficient).map
    f.toTopCatHom

/-- Contravariant singular-cochain map obtained from the chain map by the
linear-Yoneda duality used definitionally in Stage 2F. -/
noncomputable def singularCochainPullback
    (f : AnalyticEndomorphism A) :
    rationalSingularCochains A ⟶ rationalSingularCochains A := by
  unfold rationalSingularCochains
  exact (HomologicalComplex.unopFunctor (ModuleCat ℚ) (ComplexShape.down ℕ)).map
    (Quiver.Hom.op
      ((((CategoryTheory.linearYoneda ℚ (ModuleCat ℚ)).obj rationalCoefficient).rightOp
        |>.mapHomologicalComplex (ComplexShape.down ℕ)).map
        (singularChainMap A f)))

/-- Induced map on the genuine rational singular cohomology object. -/
noncomputable def rationalCohomologyPullbackObj
    (f : AnalyticEndomorphism A)
    (n : Nat) :
    rationalSingularCohomologyObj A n ⟶
      rationalSingularCohomologyObj A n :=
  HomologicalComplex.homologyMap (singularCochainPullback A f) n

/-- Underlying rational-linear endomorphism used by the Hodge attack. -/
noncomputable def rationalCohomologyPullback
    (f : AnalyticEndomorphism A)
    (n : Nat) :
    RationalSingularCohomology A n →ₗ[ℚ]
      RationalSingularCohomology A n :=
  (rationalCohomologyPullbackObj A f n).hom

/-- Chain functoriality sends the analytic identity to the identity chain map. -/
theorem singularChainMap_id :
    singularChainMap A (AnalyticEndomorphism.id (A := A)) =
      𝟙 (rationalSingularChains A) := by
  simp [singularChainMap, rationalSingularChains]

/-- Chain maps respect composition. -/
theorem singularChainMap_comp
    (f g : AnalyticEndomorphism A) :
    singularChainMap A (AnalyticEndomorphism.comp (A := A) f g) =
      singularChainMap A f ≫ singularChainMap A g := by
  simp [singularChainMap]
  rfl

/-- Cohomology pullback is contravariantly functorial. -/
theorem rationalCohomologyPullback_comp
    (f g : AnalyticEndomorphism A)
    (n : Nat) :
    rationalCohomologyPullback A (AnalyticEndomorphism.comp (A := A) f g) n =
      (rationalCohomologyPullback A f n).comp
        (rationalCohomologyPullback A g n) := by
  ext x
  unfold rationalCohomologyPullback rationalCohomologyPullbackObj
  have hcochain :
    singularCochainPullback A (AnalyticEndomorphism.comp (A := A) f g) =
      (singularCochainPullback A g) ≫ (singularCochainPullback A f) := by
    simp [singularCochainPullback, singularChainMap_comp]
    rfl
  have hcomp :
    HomologicalComplex.homologyMap
        (singularCochainPullback A (AnalyticEndomorphism.comp (A := A) f g)) n =
      (HomologicalComplex.homologyMap (singularCochainPullback A g) n) ≫
        (HomologicalComplex.homologyMap (singularCochainPullback A f) n) := by
    rw [hcochain, HomologicalComplex.homologyMap_comp]
  show (ModuleCat.Hom.hom
      (HomologicalComplex.homologyMap
        (singularCochainPullback A (AnalyticEndomorphism.comp (A := A) f g)) n)) x =
    ((ModuleCat.Hom.hom
      (HomologicalComplex.homologyMap (singularCochainPullback A f) n)).comp
      (ModuleCat.Hom.hom
        (HomologicalComplex.homologyMap (singularCochainPullback A g) n))) x
  rw [hcomp]
  simp

/-- Identity acts identically on rational Betti cohomology. -/
theorem rationalCohomologyPullback_id
    (n : Nat) :
    rationalCohomologyPullback A (AnalyticEndomorphism.id (A := A)) n =
      LinearMap.id := by
  ext x
  unfold rationalCohomologyPullback rationalCohomologyPullbackObj
  have hcochain :
    singularCochainPullback A (AnalyticEndomorphism.id (A := A)) =
      𝟙 (rationalSingularCochains A) := by
    simp [singularCochainPullback, singularChainMap_id]
    rfl
  show (ModuleCat.Hom.hom
      (HomologicalComplex.homologyMap
        (singularCochainPullback A (AnalyticEndomorphism.id (A := A))) n)) x =
    LinearMap.id x
  rw [hcochain, HomologicalComplex.homologyMap_id]
  simp
  rfl

/-- A morphism-level analytification package therefore yields a genuine
contravariant Betti representation of every algebraic C-scheme endomorphism. -/
noncomputable def algebraicEndomorphismBettiPullback
    (E : EndomorphismAnalytification A)
    (f : ComplexSchemeEndomorphism V)
    (n : Nat) :
    RationalSingularCohomology A n →ₗ[ℚ]
      RationalSingularCohomology A n :=
  rationalCohomologyPullback A (E.lift f) n

#check singularChainMap
#check singularCochainPullback
#check rationalCohomologyPullbackObj
#check rationalCohomologyPullback
#check algebraicEndomorphismBettiPullback

#print axioms singularChainMap_id
#print axioms singularChainMap_comp
#print axioms rationalCohomologyPullback_comp
#print axioms rationalCohomologyPullback_id

end GSTClassicalHodgeSingularCohomologyFunctoriality
