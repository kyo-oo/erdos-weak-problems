import GSTClassicalHodgeStrictCorrespondenceAnalyticTranspose

/-!
# GST CLASSICAL HODGE — STRICT CORRESPONDENCE CHAIN TRANSPOSE

The previous analytic-transpose layer proves that the actual algebraic factor
swap sends the intrinsic analytic locus of `K` to the intrinsic analytic locus
of `K^t`.  Here we upgrade that pointwise statement to a genuine TopCat
isomorphism and then through Mathlib's singular-chain functor.

Thus transpose compatibility is established before any Hodge class,
cycle-class representative, transfer choice, or Gysin enhancement is used:

* the carrier of `K^t` is the coordinate-swapped carrier of `K`;
* its left projection is the original right projection;
* its right projection is the original left projection;
* the corresponding singular-chain maps satisfy the same identities.

Any eventual full Betti push-pull construction therefore has a fixed geometric
transpose; a formal coefficient adjoint cannot be substituted for it.
-/

set_option maxHeartbeats 100000000
set_option maxRecDepth 1000000

noncomputable section

open CategoryTheory
open AlgebraicGeometry
open AlgebraicTopology

namespace GSTClassicalHodgeStrictCorrespondenceChainTranspose

open GSTProjectiveOverC
open GSTGeometricRealizationStage2F
open GSTClassicalHodgeSchemeFiniteCorrespondenceFirewall
open GSTClassicalHodgeStrictCorrespondenceAnalyticSpan
open GSTClassicalHodgeStrictCorrespondenceAnalyticTranspose

variable {V : SmoothProjectiveComplexScheme}
variable (A : AnalytificationData V)

/-- Coordinate swap maps the intrinsic carrier of `K` continuously to that of
its genuine algebraic transpose. -/
noncomputable def analyticCarrierSwapHom
    (K : SchemeBiFiniteClosedCorrespondence V) :
    analyticCarrier A K ⟶ analyticCarrier A K.transpose :=
  ConcreteCategory.ofHom (C := TopCat) ⟨
    (fun q => ⟨(q.1.2, q.1.1),
      (mem_analyticLocus_transpose_iff A K (q.1.2, q.1.1)).2 q.2⟩),
    by
      exact Continuous.subtype_mk
        ((continuous_snd.comp continuous_subtype_val).prodMk
          (continuous_fst.comp continuous_subtype_val)) _⟩

/-- The same coordinate swap is the inverse map. -/
noncomputable def analyticCarrierSwapInv
    (K : SchemeBiFiniteClosedCorrespondence V) :
    analyticCarrier A K.transpose ⟶ analyticCarrier A K :=
  ConcreteCategory.ofHom (C := TopCat) ⟨
    (fun q => ⟨(q.1.2, q.1.1),
      (mem_analyticLocus_transpose_iff A K q.1).1 q.2⟩),
    by
      exact Continuous.subtype_mk
        ((continuous_snd.comp continuous_subtype_val).prodMk
          (continuous_fst.comp continuous_subtype_val)) _⟩

/-- The intrinsic analytic carriers of `K` and `K^t` are genuinely isomorphic. -/
noncomputable def analyticCarrierTransposeIso
    (K : SchemeBiFiniteClosedCorrespondence V) :
    analyticCarrier A K ≅ analyticCarrier A K.transpose where
  hom := analyticCarrierSwapHom A K
  inv := analyticCarrierSwapInv A K
  hom_inv_id := by
    ext q
    apply Subtype.ext
    rfl
  inv_hom_id := by
    ext q
    apply Subtype.ext
    rfl

/-- **ANALYTIC LEFT/RIGHT TRANSPOSE LAW.** -/
theorem swapHom_left
    (K : SchemeBiFiniteClosedCorrespondence V) :
    analyticCarrierSwapHom A K ≫ analyticLeft A K.transpose =
      analyticRight A K := by
  ext q
  rfl

/-- Dual analytic transpose law. -/
theorem swapHom_right
    (K : SchemeBiFiniteClosedCorrespondence V) :
    analyticCarrierSwapHom A K ≫ analyticRight A K.transpose =
      analyticLeft A K := by
  ext q
  rfl

/-- Singular-chain image of the actual analytic factor swap. -/
noncomputable def transposeChainIso
    (K : SchemeBiFiniteClosedCorrespondence V) :
    carrierSingularChains A K ≅ carrierSingularChains A K.transpose :=
  ((singularChainComplexFunctor (ModuleCat ℚ)).obj rationalCoefficient).mapIso
    (analyticCarrierTransposeIso A K)

/-- **CHAIN-LEVEL TRANSPOSE COMPATIBILITY.**
After the genuine carrier swap, the left chain projection of `K^t` is exactly
the right chain projection of `K`. -/
theorem transposeChain_left
    (K : SchemeBiFiniteClosedCorrespondence V) :
    (transposeChainIso A K).hom ≫ leftChainMap A K.transpose =
      rightChainMap A K := by
  let F := (singularChainComplexFunctor (ModuleCat ℚ)).obj rationalCoefficient
  change F.map (analyticCarrierSwapHom A K) ≫ F.map (analyticLeft A K.transpose) =
    F.map (analyticRight A K)
  rw [← F.map_comp, swapHom_left A K]

/-- Right chain projection of `K^t` becomes the original left projection. -/
theorem transposeChain_right
    (K : SchemeBiFiniteClosedCorrespondence V) :
    (transposeChainIso A K).hom ≫ rightChainMap A K.transpose =
      leftChainMap A K := by
  let F := (singularChainComplexFunctor (ModuleCat ℚ)).obj rationalCoefficient
  change F.map (analyticCarrierSwapHom A K) ≫ F.map (analyticRight A K.transpose) =
    F.map (analyticLeft A K)
  rw [← F.map_comp, swapHom_right A K]

#check analyticCarrierSwapHom
#check analyticCarrierTransposeIso
#check swapHom_left
#check swapHom_right
#check transposeChainIso
#check transposeChain_left
#check transposeChain_right

#print axioms swapHom_left
#print axioms transposeChain_left
#print axioms transposeChain_right

end GSTClassicalHodgeStrictCorrespondenceChainTranspose
