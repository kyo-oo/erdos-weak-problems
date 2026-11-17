import GSTGeometricRealizationStage2F
import GSTClassicalHodgeSingularCohomologyFunctoriality
import Mathlib.Algebra.Homology.ShortComplex.HomologicalComplex

/-!
# GST CLASSICAL HODGE — NATIVE BETTI SELF-PRODUCT

This is the ambient topological carrier needed for a genuine algebraic
correspondence action.  It is constructed directly from the supplied
analytification `A.space`:

  X_an × X_an

with the product topology.  No correspondence operator, cycle selector,
Hodge algebraicity statement, or extension off the algebraic range is supplied.

The two coordinate projections and the factor-swap homeomorphism are actual
continuous maps.  Mathlib's singular-chain functor, linear Yoneda duality, and
homology therefore construct their actions on the complete rational singular
cohomology carrier.  In particular the transpose geometry already acts on
all Betti classes before any cycle class is mentioned.
-/

set_option maxHeartbeats 100000000
set_option maxRecDepth 1000000

noncomputable section

open CategoryTheory
open AlgebraicTopology
open GSTProjectiveOverC
open GSTGeometricRealizationStage2F

namespace GSTClassicalHodgeAmbientBettiSelfProduct

variable {V : SmoothProjectiveComplexScheme}
variable (A : AnalytificationData V)

/-- The actual topological self-product of the analytification. -/
noncomputable def bettiSelfProductSpace : TopCat :=
  TopCat.of (A.space × A.space)

/-- First continuous projection from the Betti self-product. -/
noncomputable def bettiFst : bettiSelfProductSpace A ⟶ A.space :=
  ConcreteCategory.ofHom (C := TopCat)
    ⟨Prod.fst, continuous_fst⟩

/-- Second continuous projection from the Betti self-product. -/
noncomputable def bettiSnd : bettiSelfProductSpace A ⟶ A.space :=
  ConcreteCategory.ofHom (C := TopCat)
    ⟨Prod.snd, continuous_snd⟩

/-- Coordinate swap on the actual Betti self-product. -/
noncomputable def bettiSwap :
    bettiSelfProductSpace A ⟶ bettiSelfProductSpace A :=
  ConcreteCategory.ofHom (C := TopCat)
    ⟨(fun q => (q.2, q.1)), continuous_snd.prodMk continuous_fst⟩

/-- Factor swap is its own inverse as a genuine TopCat isomorphism. -/
noncomputable def bettiSwapIso :
    bettiSelfProductSpace A ≅ bettiSelfProductSpace A where
  hom := bettiSwap A
  inv := bettiSwap A
  hom_inv_id := by
    ext q <;> rfl
  inv_hom_id := by
    ext q <;> rfl

@[simp]
theorem bettiSwap_fst :
    bettiSwap A ≫ bettiFst A = bettiSnd A := by
  ext q
  rfl

@[simp]
theorem bettiSwap_snd :
    bettiSwap A ≫ bettiSnd A = bettiFst A := by
  ext q
  rfl

@[simp]
theorem bettiSwap_swap :
    bettiSwap A ≫ bettiSwap A = 𝟙 (bettiSelfProductSpace A) := by
  ext q
  rfl

/-- Genuine rational singular chains of `X_an × X_an`. -/
noncomputable def productSingularChains :
    ChainComplex (ModuleCat ℚ) ℕ :=
  ((singularChainComplexFunctor (ModuleCat ℚ)).obj rationalCoefficient).obj
    (bettiSelfProductSpace A)

/-- Rational singular cochains of `X_an × X_an`. -/
noncomputable def productSingularCochains :
    CochainComplex (ModuleCat ℚ) ℕ :=
  (productSingularChains A).linearYonedaObj ℚ rationalCoefficient

/-- Rational singular cohomology object of the actual Betti self-product. -/
noncomputable def productCohomologyObj (n : Nat) : ModuleCat ℚ :=
  (productSingularCochains A).homology n

abbrev ProductCohomology (n : Nat) : Type :=
  productCohomologyObj A n

/-- Chain map induced by the first projection. -/
noncomputable def fstChainMap :
    productSingularChains A ⟶ rationalSingularChains A :=
  ((singularChainComplexFunctor (ModuleCat ℚ)).obj rationalCoefficient).map
    (bettiFst A)

/-- Chain map induced by the second projection. -/
noncomputable def sndChainMap :
    productSingularChains A ⟶ rationalSingularChains A :=
  ((singularChainComplexFunctor (ModuleCat ℚ)).obj rationalCoefficient).map
    (bettiSnd A)

/-- Chain automorphism induced by factor swap. -/
noncomputable def swapChainMap :
    productSingularChains A ⟶ productSingularChains A :=
  ((singularChainComplexFunctor (ModuleCat ℚ)).obj rationalCoefficient).map
    (bettiSwap A)

/-- Contravariant cochain pullback along the first projection. -/
noncomputable def fstCochainPullback :
    rationalSingularCochains A ⟶ productSingularCochains A := by
  unfold rationalSingularCochains
  exact (HomologicalComplex.unopFunctor (ModuleCat ℚ) (ComplexShape.down ℕ)).map
    (Quiver.Hom.op
      ((((CategoryTheory.linearYoneda ℚ (ModuleCat ℚ)).obj rationalCoefficient).rightOp
        |>.mapHomologicalComplex (ComplexShape.down ℕ)).map
        (fstChainMap A)))

/-- Contravariant cochain pullback along the second projection. -/
noncomputable def sndCochainPullback :
    rationalSingularCochains A ⟶ productSingularCochains A := by
  unfold rationalSingularCochains
  exact (HomologicalComplex.unopFunctor (ModuleCat ℚ) (ComplexShape.down ℕ)).map
    (Quiver.Hom.op
      ((((CategoryTheory.linearYoneda ℚ (ModuleCat ℚ)).obj rationalCoefficient).rightOp
        |>.mapHomologicalComplex (ComplexShape.down ℕ)).map
        (sndChainMap A)))

/-- Contravariant cochain pullback along the factor swap. -/
noncomputable def swapCochainPullback :
    productSingularCochains A ⟶ productSingularCochains A := by
  unfold productSingularCochains
  exact (HomologicalComplex.unopFunctor (ModuleCat ℚ) (ComplexShape.down ℕ)).map
    (Quiver.Hom.op
      ((((CategoryTheory.linearYoneda ℚ (ModuleCat ℚ)).obj rationalCoefficient).rightOp
        |>.mapHomologicalComplex (ComplexShape.down ℕ)).map
        (swapChainMap A)))

/-- Complete rational Betti pullback through the first projection. -/
noncomputable def fstCohomologyPullback (n : Nat) :
    RationalSingularCohomology A n →ₗ[ℚ] ProductCohomology A n :=
  (HomologicalComplex.homologyMap (fstCochainPullback A) n).hom

/-- Complete rational Betti pullback through the second projection. -/
noncomputable def sndCohomologyPullback (n : Nat) :
    RationalSingularCohomology A n →ₗ[ℚ] ProductCohomology A n :=
  (HomologicalComplex.homologyMap (sndCochainPullback A) n).hom

/-- Complete rational Betti pullback through factor swap. -/
noncomputable def swapCohomologyPullback (n : Nat) :
    ProductCohomology A n →ₗ[ℚ] ProductCohomology A n :=
  (HomologicalComplex.homologyMap (swapCochainPullback A) n).hom

/-- On singular chains the genuine factor swap exchanges the two projections. -/
theorem swapChain_fst :
    swapChainMap A ≫ fstChainMap A = sndChainMap A := by
  let F := (singularChainComplexFunctor (ModuleCat ℚ)).obj rationalCoefficient
  change F.map (bettiSwap A) ≫ F.map (bettiFst A) = F.map (bettiSnd A)
  rw [← F.map_comp, bettiSwap_fst]

/-- Dual chain identity for the second projection. -/
theorem swapChain_snd :
    swapChainMap A ≫ sndChainMap A = fstChainMap A := by
  let F := (singularChainComplexFunctor (ModuleCat ℚ)).obj rationalCoefficient
  change F.map (bettiSwap A) ≫ F.map (bettiSnd A) = F.map (bettiFst A)
  rw [← F.map_comp, bettiSwap_snd]

/-- The singular-chain factor swap is involutive. -/
theorem swapChain_involutive :
    swapChainMap A ≫ swapChainMap A = 𝟙 (productSingularChains A) := by
  let F := (singularChainComplexFunctor (ModuleCat ℚ)).obj rationalCoefficient
  change F.map (bettiSwap A) ≫ F.map (bettiSwap A) = 𝟙 _
  rw [← F.map_comp, bettiSwap_swap, F.map_id]

/-- **FULL-BETTI TRANSPOSE OF THE FIRST PROJECTION.**
Pulling a class through the original second projection is the same as first
pulling through the first projection and then through factor swap. -/
theorem sndPullback_eq_swap_fstPullback
    (n : Nat) :
    sndCohomologyPullback A n =
      (swapCohomologyPullback A n).comp (fstCohomologyPullback A n) := by
  ext alpha
  unfold sndCohomologyPullback swapCohomologyPullback fstCohomologyPullback
  have hcochain :
    sndCochainPullback A =
      (fstCochainPullback A) ≫ (swapCochainPullback A) := by
    unfold sndCochainPullback fstCochainPullback swapCochainPullback
    rw [← swapChain_fst]
    simp
    rfl
  have hcomp :
    HomologicalComplex.homologyMap (sndCochainPullback A) n =
      (HomologicalComplex.homologyMap (fstCochainPullback A) n) ≫
        (HomologicalComplex.homologyMap (swapCochainPullback A) n) := by
    rw [hcochain, HomologicalComplex.homologyMap_comp]
  show (ModuleCat.Hom.hom
      (HomologicalComplex.homologyMap (sndCochainPullback A) n)) alpha =
    ((ModuleCat.Hom.hom
      (HomologicalComplex.homologyMap (swapCochainPullback A) n)).comp
      (ModuleCat.Hom.hom
        (HomologicalComplex.homologyMap (fstCochainPullback A) n))) alpha
  rw [hcomp]
  simp

/-- Symmetric full-Betti projection law. -/
theorem fstPullback_eq_swap_sndPullback
    (n : Nat) :
    fstCohomologyPullback A n =
      (swapCohomologyPullback A n).comp (sndCohomologyPullback A n) := by
  ext alpha
  unfold fstCohomologyPullback swapCohomologyPullback sndCohomologyPullback
  have hcochain :
    fstCochainPullback A =
      (sndCochainPullback A) ≫ (swapCochainPullback A) := by
    unfold fstCochainPullback sndCochainPullback swapCochainPullback
    rw [← swapChain_snd]
    simp
    rfl
  have hcomp :
    HomologicalComplex.homologyMap (fstCochainPullback A) n =
      (HomologicalComplex.homologyMap (sndCochainPullback A) n) ≫
        (HomologicalComplex.homologyMap (swapCochainPullback A) n) := by
    rw [hcochain, HomologicalComplex.homologyMap_comp]
  show (ModuleCat.Hom.hom
      (HomologicalComplex.homologyMap (fstCochainPullback A) n)) alpha =
    ((ModuleCat.Hom.hom
      (HomologicalComplex.homologyMap (swapCochainPullback A) n)).comp
      (ModuleCat.Hom.hom
        (HomologicalComplex.homologyMap (sndCochainPullback A) n))) alpha
  rw [hcomp]
  simp

/-- **FULL-BETTI FACTOR-SWAP INVOLUTION.** -/
theorem swapCohomology_involutive
    (n : Nat) :
    (swapCohomologyPullback A n).comp (swapCohomologyPullback A n) =
      LinearMap.id := by
  ext alpha
  unfold swapCohomologyPullback
  have hinner : (swapCochainPullback A) ≫ (swapCochainPullback A) = 𝟙 _ := by
    unfold swapCochainPullback
    let F := (HomologicalComplex.unopFunctor (ModuleCat ℚ) (ComplexShape.down ℕ))
    let G := (((CategoryTheory.linearYoneda ℚ (ModuleCat ℚ)).obj rationalCoefficient).rightOp
      |>.mapHomologicalComplex (ComplexShape.down ℕ))
    change F.map (Quiver.Hom.op (G.map (swapChainMap A))) ≫
      F.map (Quiver.Hom.op (G.map (swapChainMap A))) = 𝟙 _
    rw [← F.map_comp,
      show (G.map (swapChainMap A)).op ≫ (G.map (swapChainMap A)).op
          = (G.map (swapChainMap A) ≫ G.map (swapChainMap A)).op from rfl,
      ← G.map_comp, swapChain_involutive, G.map_id,
      show (𝟙 (G.obj (productSingularChains A))).op
          = 𝟙 (Opposite.op (G.obj (productSingularChains A))) from rfl,
      F.map_id]
  have hcomp :
    (HomologicalComplex.homologyMap (swapCochainPullback A) n) ≫
      (HomologicalComplex.homologyMap (swapCochainPullback A) n) = 𝟙 _ := by
    rw [← HomologicalComplex.homologyMap_comp, hinner,
      HomologicalComplex.homologyMap_id]
  show (ModuleCat.Hom.hom
      (HomologicalComplex.homologyMap (swapCochainPullback A) n))
      ((ModuleCat.Hom.hom
        (HomologicalComplex.homologyMap (swapCochainPullback A) n)) alpha) =
    alpha
  rw [show (ModuleCat.Hom.hom
      (HomologicalComplex.homologyMap (swapCochainPullback A) n))
      ((ModuleCat.Hom.hom
        (HomologicalComplex.homologyMap (swapCochainPullback A) n)) alpha) =
    (ModuleCat.Hom.hom
      ((HomologicalComplex.homologyMap (swapCochainPullback A) n) ≫
      (HomologicalComplex.homologyMap (swapCochainPullback A) n))) alpha from by
    simp
    rfl]
  rw [hcomp]
  simp
  rfl

#check bettiSelfProductSpace
#check bettiFst
#check bettiSnd
#check bettiSwapIso
#check ProductCohomology
#check fstCohomologyPullback
#check sndCohomologyPullback
#check swapCohomologyPullback
#check sndPullback_eq_swap_fstPullback
#check fstPullback_eq_swap_sndPullback
#check swapCohomology_involutive

#print axioms bettiSwap_fst
#print axioms swapChain_fst
#print axioms sndPullback_eq_swap_fstPullback
#print axioms swapCohomology_involutive

end GSTClassicalHodgeAmbientBettiSelfProduct
