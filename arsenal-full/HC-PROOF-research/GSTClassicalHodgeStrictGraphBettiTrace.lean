import GSTClassicalHodgeStrictGraphCorrespondence
import GSTClassicalHodgeStrictCorrespondenceBettiTracePushPull

/-!
# GST CLASSICAL HODGE — TRANSPOSED GRAPH BETTI TRACE WITHOUT A TRACE AXIOM

For the transpose of a finite graph correspondence, the right algebraic leg is
literally the identity.  Its intrinsic analytic carrier is therefore the graph
locus `(f(x),x)`.  Projection to the second coordinate has a canonical
continuous section obtained from analytification of `f`.

Pullback along that section is an exact left inverse to right pullback on
rational singular cohomology.  Hence the degree-one `RightFiniteBettiTrace`
used by the strict-relation compiler is constructed rather than supplied.

No Hodge class, target state, cycle-class surjectivity, or desired operator
action occurs in the construction.
-/

set_option maxHeartbeats 180000000
set_option maxRecDepth 1000000

noncomputable section

open CategoryTheory
open AlgebraicGeometry
open AlgebraicTopology

namespace GSTClassicalHodgeStrictGraphBettiTrace

open GSTProjectiveOverC
open GSTGeometricRealizationStage2F
open GSTClassicalHodgeAnalytificationFunctoriality
open GSTClassicalHodgeSingularCohomologyFunctoriality
open GSTClassicalHodgeStrictGraphCorrespondence
open GSTClassicalHodgeStrictCorrespondenceAnalyticSpan
open GSTClassicalHodgeStrictCorrespondenceBettiObstruction
open GSTClassicalHodgeStrictCorrespondenceBettiTracePushPull

variable {V : SmoothProjectiveComplexScheme}
variable (A : AnalytificationData V)

/-- A genuine complex point of `X` canonically determines a carrier point of
the transposed graph. -/
noncomputable def transposeGraphCarrierPoint
    (f : ComplexSchemeEndomorphism V)
    (hf : IsFinite f.hom)
    (x : ComplexPoint V) :
    CarrierComplexPoint ((strictGraph f hf).transpose) := by
  refine ⟨x.1, ?_⟩
  calc
    (x.1 ≫ ((strictGraph f hf).transpose.toSchemeFiniteClosedCorrespondence.left)) ≫
        V.structureMap =
      (x.1 ≫ f.hom) ≫ V.structureMap := by
        rw [strictGraph_transpose_left]
    _ = x.1 ≫ (f.hom ≫ V.structureMap) := by simp [Category.assoc]
    _ = x.1 ≫ V.structureMap := by rw [f.over_base]
    _ = 𝟙 complexBase := x.2

/-- The intrinsic analytic point of the transposed graph is exactly
`(f^an(x),x)`. -/
theorem transposeGraphCarrierPoint_pair
    (f : ComplexSchemeEndomorphism V)
    (hf : IsFinite f.hom)
    (x : ComplexPoint V) :
    carrierPointPair A ((strictGraph f hf).transpose)
        (transposeGraphCarrierPoint f hf x) =
      (A.pointsEquiv (ComplexSchemeEndomorphism.complexPointMap f x),
        A.pointsEquiv x) := by
  apply Prod.ext
  · simp [carrierPointPair, leftComplexPoint, transposeGraphCarrierPoint,
      strictGraph_transpose_left,
      ComplexSchemeEndomorphism.complexPointMap]
    rfl
  · apply congrArg A.pointsEquiv
    apply Subtype.ext
    simp [rightComplexPoint, transposeGraphCarrierPoint,
      strictGraph_transpose_right]
    exact Category.comp_id _

/-- Canonical section of the analytic right projection of a transposed finite
graph.  Continuity is exactly the morphism-level analytification law already
present in the GST geometry. -/
noncomputable def transposeGraphAnalyticSection
    (F : AnalyticEndomorphism A)
    (hf : IsFinite F.algebraic.hom) :
    A.space ⟶ analyticCarrier A ((strictGraph F.algebraic hf).transpose) := by
  let s : A.space → analyticCarrier A ((strictGraph F.algebraic hf).transpose) :=
    fun x => ⟨(transportedPointMap A F.algebraic x, x), by
      let z := transposeGraphCarrierPoint F.algebraic hf (A.pointsEquiv.symm x)
      refine ⟨z, ?_⟩
      have hz := transposeGraphCarrierPoint_pair A F.algebraic hf
        (A.pointsEquiv.symm x)
      simpa [transportedPointMap] using hz⟩
  refine ConcreteCategory.ofHom (C := TopCat)
    ⟨s, ?_⟩
  apply continuous_induced_rng.2
  exact F.continuous_toFun.prodMk continuous_id

/-- The right projection followed after the canonical graph section is
literally identity. -/
@[simp]
theorem transposeGraphAnalyticSection_right
    (F : AnalyticEndomorphism A)
    (hf : IsFinite F.algebraic.hom) :
    transposeGraphAnalyticSection A F hf ≫
      analyticRight A ((strictGraph F.algebraic hf).transpose) = 𝟙 A.space := by
  apply TopCat.ext
  intro x
  rfl

/-- Covariant singular-chain map of the canonical graph section. -/
noncomputable def transposeGraphSectionChainMap
    (F : AnalyticEndomorphism A)
    (hf : IsFinite F.algebraic.hom) :
    rationalSingularChains A ⟶
      carrierSingularChains A ((strictGraph F.algebraic hf).transpose) :=
  ((singularChainComplexFunctor (ModuleCat ℚ)).obj rationalCoefficient).map
    (transposeGraphAnalyticSection A F hf)

/-- Contravariant cochain pullback along the canonical graph section. -/
noncomputable def transposeGraphSectionCochainPullback
    (F : AnalyticEndomorphism A)
    (hf : IsFinite F.algebraic.hom) :
    carrierSingularCochains A ((strictGraph F.algebraic hf).transpose) ⟶
      rationalSingularCochains A := by
  let D :=
    ((CategoryTheory.linearYoneda ℚ (ModuleCat ℚ)).obj rationalCoefficient).rightOp
      |>.mapHomologicalComplex (ComplexShape.down ℕ)
  unfold carrierSingularCochains rationalSingularCochains
  exact (HomologicalComplex.unopFunctor (ModuleCat ℚ) (ComplexShape.down ℕ)).map
    (Quiver.Hom.op (D.map (transposeGraphSectionChainMap A F hf)))

/-- The section-induced map on carrier cohomology. -/
noncomputable def transposeGraphSectionCohomologyPullback
    (F : AnalyticEndomorphism A)
    (hf : IsFinite F.algebraic.hom)
    (n : Nat) :
    CarrierCohomology A ((strictGraph F.algebraic hf).transpose) n →ₗ[ℚ]
      RationalSingularCohomology A n :=
  (HomologicalComplex.homologyMap
    (transposeGraphSectionCochainPullback A F hf) n).hom

/-- At chain level, section followed by the right projection is identity. -/
theorem transposeGraphSectionChainMap_right
    (F : AnalyticEndomorphism A)
    (hf : IsFinite F.algebraic.hom) :
    transposeGraphSectionChainMap A F hf ≫
      rightChainMap A ((strictGraph F.algebraic hf).transpose) =
        𝟙 (rationalSingularChains A) := by
  let C := (singularChainComplexFunctor (ModuleCat ℚ)).obj rationalCoefficient
  change C.map (transposeGraphAnalyticSection A F hf) ≫
    C.map (analyticRight A ((strictGraph F.algebraic hf).transpose)) = 𝟙 _
  rw [← C.map_comp, transposeGraphAnalyticSection_right, C.map_id]

/-- Contravariance turns the preceding retraction into a cochain retraction. -/
theorem rightCochainPullback_transposeGraphSection
    (F : AnalyticEndomorphism A)
    (hf : IsFinite F.algebraic.hom) :
    rightCochainPullback A ((strictGraph F.algebraic hf).transpose) ≫
      transposeGraphSectionCochainPullback A F hf =
        𝟙 (rationalSingularCochains A) := by
  have h1 : (HomologicalComplex.unopFunctor (ModuleCat ℚ) (ComplexShape.down ℕ)).map
      (Quiver.Hom.op ((((CategoryTheory.linearYoneda ℚ (ModuleCat ℚ)).obj rationalCoefficient).rightOp
        |>.mapHomologicalComplex (ComplexShape.down ℕ)).map
        (rightChainMap A ((strictGraph F.algebraic hf).transpose)))) ≫
    (HomologicalComplex.unopFunctor (ModuleCat ℚ) (ComplexShape.down ℕ)).map
      (Quiver.Hom.op ((((CategoryTheory.linearYoneda ℚ (ModuleCat ℚ)).obj rationalCoefficient).rightOp
        |>.mapHomologicalComplex (ComplexShape.down ℕ)).map
        (transposeGraphSectionChainMap A F hf))) =
    𝟙 (rationalSingularCochains A) := by
    rw [← CategoryTheory.Functor.map_comp, ← CategoryTheory.op_comp,
      ← CategoryTheory.Functor.map_comp, transposeGraphSectionChainMap_right,
      CategoryTheory.Functor.map_id, CategoryTheory.op_id, CategoryTheory.Functor.map_id]
    rfl
  exact h1

/-- **GRAPH-RETRACTION COHOMOLOGY LAW.**
Pullback along the canonical section is an exact left inverse of the right
cohomology pullback. -/
theorem transposeGraphSectionCohomologyPullback_right
    (F : AnalyticEndomorphism A)
    (hf : IsFinite F.algebraic.hom)
    (n : Nat) :
    (transposeGraphSectionCohomologyPullback A F hf n).comp
      (rightCohomologyPullback A ((strictGraph F.algebraic hf).transpose) n) =
        LinearMap.id := by
  ext alpha
  unfold transposeGraphSectionCohomologyPullback rightCohomologyPullback
    rightCohomologyPullbackObj
  have hcochain := rightCochainPullback_transposeGraphSection A F hf
  have hcomp : (HomologicalComplex.homologyMap
      (rightCochainPullback A ((strictGraph F.algebraic hf).transpose) ≫
        transposeGraphSectionCochainPullback A F hf) n).hom alpha =
    (HomologicalComplex.homologyMap (transposeGraphSectionCochainPullback A F hf) n).hom
      ((HomologicalComplex.homologyMap
        (rightCochainPullback A ((strictGraph F.algebraic hf).transpose)) n).hom alpha) := by
    rw [HomologicalComplex.homologyMap_comp]
    rfl
  rw [hcochain, HomologicalComplex.homologyMap_id] at hcomp
  exact hcomp.symm

/-- **DEGREE-ONE TRACE FROM STRICT GRAPH GEOMETRY.**
The finite right trace of a transposed graph is no longer an input. -/
noncomputable def transposedStrictGraphRightTrace
    (F : AnalyticEndomorphism A)
    (hf : IsFinite F.algebraic.hom)
    (n : Nat) :
    RightFiniteBettiTrace A ((strictGraph F.algebraic hf).transpose) n where
  trace := transposeGraphSectionCohomologyPullback A F hf n
  degree := 1
  degree_ne_zero := one_ne_zero
  trace_rightPullback := by
    simpa using transposeGraphSectionCohomologyPullback_right A F hf n

/-- The normalized trace is definitionally the graph-section pullback because
the constructed finite degree is one. -/
theorem transposedStrictGraph_normalizedTrace_eq_section
    (F : AnalyticEndomorphism A)
    (hf : IsFinite F.algebraic.hom)
    (n : Nat) :
    (transposedStrictGraphRightTrace A F hf n).normalizedTrace =
      transposeGraphSectionCohomologyPullback A F hf n := by
  ext alpha
  simp [transposedStrictGraphRightTrace,
    RightFiniteBettiTrace.normalizedTrace]

/-- Consequently the transposed graph right pullback is injective with no
separate trace/injectivity hypothesis. -/
theorem transposedStrictGraph_rightPullback_injective
    (F : AnalyticEndomorphism A)
    (hf : IsFinite F.algebraic.hom)
    (n : Nat) :
    Function.Injective
      (rightCohomologyPullback A ((strictGraph F.algebraic hf).transpose) n) :=
  (transposedStrictGraphRightTrace A F hf n).rightPullback_injective

/-! ## The graph section is an inverse, not merely a retraction

These constructions depend only on the actual finite native map and its
analytification.  No target Hodge sheet or algebraic representative is used.
They remove the carrier-defect premise for this geometric family.  They do
not assert that a prescribed matrix-unit branch is the action of such a map.
-/

/-- Every carrier point of the transposed native graph lies on the graph of
the transported point map.  This direction uses the actual carrier witness;
it is stronger than merely constructing a section into that carrier. -/
theorem transposeGraphCarrierPoint_on_graph
    (f : ComplexSchemeEndomorphism V)
    (hf : IsFinite f.hom)
    (z : CarrierComplexPoint ((strictGraph f hf).transpose)) :
    (carrierPointPair A ((strictGraph f hf).transpose) z).1 =
      transportedPointMap A f
        (carrierPointPair A ((strictGraph f hf).transpose) z).2 := by
  change A.pointsEquiv (leftComplexPoint ((strictGraph f hf).transpose) z) = _
  simp only [transportedPointMap, carrierPointPair, Equiv.symm_apply_apply]
  apply congrArg A.pointsEquiv
  apply Subtype.ext
  simp [leftComplexPoint, rightComplexPoint,
    ComplexSchemeEndomorphism.complexPointMap,
    strictGraph_transpose_left, strictGraph_transpose_right]
  exact (congrArg (fun m => m ≫ f.hom) (Category.comp_id _)).symm

/-- The previously constructed graph section is also a right inverse.
Both inverse laws are now geometric theorems, with no carrier-coherence axiom. -/
@[simp]
theorem transposeGraphAnalyticRight_section
    (F : AnalyticEndomorphism A)
    (hf : IsFinite F.algebraic.hom) :
    analyticRight A ((strictGraph F.algebraic hf).transpose) ≫
      transposeGraphAnalyticSection A F hf =
        𝟙 (analyticCarrier A ((strictGraph F.algebraic hf).transpose)) := by
  apply TopCat.ext
  intro x
  apply Subtype.ext
  change (transportedPointMap A F.algebraic x.1.2, x.1.2) = x.1
  rcases x.2 with ⟨z, hz⟩
  rw [← hz]
  apply Prod.ext
  · exact (transposeGraphCarrierPoint_on_graph A F.algebraic hf z).symm
  · rfl

/-- The intrinsic carrier of a transposed finite graph is canonically
isomorphic to the source analytification.  The finite map supplies the other
face of this same observation carrier. -/
noncomputable def transposeGraphCarrierIso
    (F : AnalyticEndomorphism A)
    (hf : IsFinite F.algebraic.hom) :
    analyticCarrier A ((strictGraph F.algebraic hf).transpose) ≅ A.space where
  hom := analyticRight A ((strictGraph F.algebraic hf).transpose)
  inv := transposeGraphAnalyticSection A F hf
  hom_inv_id := transposeGraphAnalyticRight_section A F hf
  inv_hom_id := transposeGraphAnalyticSection_right A F hf

/-- The second inverse identity survives the native singular-chain functor. -/
theorem transposeGraphRightChainMap_section
    (F : AnalyticEndomorphism A)
    (hf : IsFinite F.algebraic.hom) :
    rightChainMap A ((strictGraph F.algebraic hf).transpose) ≫
      transposeGraphSectionChainMap A F hf =
        𝟙 (carrierSingularChains A ((strictGraph F.algebraic hf).transpose)) := by
  let C := (singularChainComplexFunctor (ModuleCat ℚ)).obj rationalCoefficient
  change C.map (analyticRight A ((strictGraph F.algebraic hf).transpose)) ≫
    C.map (transposeGraphAnalyticSection A F hf) = 𝟙 _
  rw [← C.map_comp, transposeGraphAnalyticRight_section, C.map_id]

/-- Dual inverse identity on the actual carrier cochains. -/
theorem transposeGraphSectionCochainPullback_right
    (F : AnalyticEndomorphism A)
    (hf : IsFinite F.algebraic.hom) :
    transposeGraphSectionCochainPullback A F hf ≫
      rightCochainPullback A ((strictGraph F.algebraic hf).transpose) =
        𝟙 (carrierSingularCochains A ((strictGraph F.algebraic hf).transpose)) := by
  have h1 : (HomologicalComplex.unopFunctor (ModuleCat ℚ) (ComplexShape.down ℕ)).map
      (Quiver.Hom.op ((((CategoryTheory.linearYoneda ℚ (ModuleCat ℚ)).obj rationalCoefficient).rightOp
        |>.mapHomologicalComplex (ComplexShape.down ℕ)).map
        (transposeGraphSectionChainMap A F hf))) ≫
    (HomologicalComplex.unopFunctor (ModuleCat ℚ) (ComplexShape.down ℕ)).map
      (Quiver.Hom.op ((((CategoryTheory.linearYoneda ℚ (ModuleCat ℚ)).obj rationalCoefficient).rightOp
        |>.mapHomologicalComplex (ComplexShape.down ℕ)).map
        (rightChainMap A ((strictGraph F.algebraic hf).transpose)))) =
    𝟙 (carrierSingularCochains A ((strictGraph F.algebraic hf).transpose)) := by
    rw [← CategoryTheory.Functor.map_comp, ← CategoryTheory.op_comp,
      ← CategoryTheory.Functor.map_comp, transposeGraphRightChainMap_section,
      CategoryTheory.Functor.map_id, CategoryTheory.op_id, CategoryTheory.Functor.map_id]
    rfl
  exact h1

/-- Right pullback and section pullback are inverse on the WHOLE carrier
cohomology, not just on algebraic source classes. -/
theorem transposeGraphRightCohomologyPullback_section
    (F : AnalyticEndomorphism A)
    (hf : IsFinite F.algebraic.hom)
    (n : Nat) :
    (rightCohomologyPullback A ((strictGraph F.algebraic hf).transpose) n).comp
      (transposeGraphSectionCohomologyPullback A F hf n) = LinearMap.id := by
  ext omega
  unfold rightCohomologyPullback rightCohomologyPullbackObj
    transposeGraphSectionCohomologyPullback
  have hcochain := transposeGraphSectionCochainPullback_right A F hf
  have hcomp : (HomologicalComplex.homologyMap
      (transposeGraphSectionCochainPullback A F hf ≫
        rightCochainPullback A ((strictGraph F.algebraic hf).transpose)) n).hom omega =
    (HomologicalComplex.homologyMap
      (rightCochainPullback A ((strictGraph F.algebraic hf).transpose)) n).hom
      ((HomologicalComplex.homologyMap (transposeGraphSectionCochainPullback A F hf) n).hom omega) := by
    rw [HomologicalComplex.homologyMap_comp]
    rfl
  rw [hcochain, HomologicalComplex.homologyMap_id] at hcomp
  exact hcomp.symm

/-- **GEOMETRY PROVES ZERO CARRIER DEFECT.**
There is no supplied residual-vanishing or transfer-totality hypothesis. -/
theorem transposedStrictGraph_carrierResidual_eq_zero
    (F : AnalyticEndomorphism A)
    (hf : IsFinite F.algebraic.hom)
    (n : Nat) :
    (transposedStrictGraphRightTrace A F hf n).carrierResidual = 0 := by
  ext omega
  change omega -
    rightCohomologyPullback A ((strictGraph F.algebraic hf).transpose) n
      (RightFiniteBettiTrace.normalizedTrace A _ n
        (transposedStrictGraphRightTrace A F hf n) omega) = 0
  rw [transposedStrictGraph_normalizedTrace_eq_section]
  have h := LinearMap.congr_fun
    (transposeGraphRightCohomologyPullback_section A F hf n) omega
  simp only [LinearMap.comp_apply, LinearMap.id_apply] at h
  rw [h, sub_self]

/-- Source defects vanish for all Betti classes on this constructed carrier. -/
theorem transposedStrictGraph_sourceResidual_eq_zero
    (F : AnalyticEndomorphism A)
    (hf : IsFinite F.algebraic.hom)
    (n : Nat) :
    (transposedStrictGraphRightTrace A F hf n).sourceResidual = 0 := by
  ext alpha
  change (RightFiniteBettiTrace.carrierResidual A _ n
    (transposedStrictGraphRightTrace A F hf n))
      (leftCohomologyPullback A ((strictGraph F.algebraic hf).transpose) n alpha) = 0
  rw [transposedStrictGraph_carrierResidual_eq_zero]
  rfl

/-- The quotient obstruction vanishes as a consequence of the native graph
geometry.  Totality is proved for this carrier, not postulated globally. -/
theorem transposedStrictGraph_transferObstruction_eq_zero
    (F : AnalyticEndomorphism A)
    (hf : IsFinite F.algebraic.hom)
    (n : Nat) :
    transferObstruction A ((strictGraph F.algebraic hf).transpose) n = 0 := by
  ext alpha
  apply (RightFiniteBettiTrace.sourceResidual_eq_zero_iff_transferObstruction
    A _ n (transposedStrictGraphRightTrace A F hf n) alpha).1
  rw [transposedStrictGraph_sourceResidual_eq_zero]
  rfl

/-- The left face of the carrier is the actual analytified native map. -/
@[simp]
theorem transposeGraphAnalyticSection_left
    (F : AnalyticEndomorphism A)
    (hf : IsFinite F.algebraic.hom) :
    transposeGraphAnalyticSection A F hf ≫
      analyticLeft A ((strictGraph F.algebraic hf).transpose) = F.toTopCatHom := by
  apply TopCat.ext
  intro x
  rfl

/-- The source-to-left-face chain map is exactly native functoriality. -/
theorem transposeGraphSectionChainMap_left
    (F : AnalyticEndomorphism A)
    (hf : IsFinite F.algebraic.hom) :
    transposeGraphSectionChainMap A F hf ≫
      leftChainMap A ((strictGraph F.algebraic hf).transpose) =
        singularChainMap A F := by
  let C := (singularChainComplexFunctor (ModuleCat ℚ)).obj rationalCoefficient
  change C.map (transposeGraphAnalyticSection A F hf) ≫
    C.map (analyticLeft A ((strictGraph F.algebraic hf).transpose)) =
      C.map F.toTopCatHom
  rw [← C.map_comp, transposeGraphAnalyticSection_left]

/-- The cochain action is derived from the native left face. -/
theorem leftCochainPullback_transposeGraphSection
    (F : AnalyticEndomorphism A)
    (hf : IsFinite F.algebraic.hom) :
    leftCochainPullback A ((strictGraph F.algebraic hf).transpose) ≫
      transposeGraphSectionCochainPullback A F hf = singularCochainPullback A F := by
  have h1 : (HomologicalComplex.unopFunctor (ModuleCat ℚ) (ComplexShape.down ℕ)).map
      (Quiver.Hom.op ((((CategoryTheory.linearYoneda ℚ (ModuleCat ℚ)).obj rationalCoefficient).rightOp
        |>.mapHomologicalComplex (ComplexShape.down ℕ)).map
        (leftChainMap A ((strictGraph F.algebraic hf).transpose)))) ≫
    (HomologicalComplex.unopFunctor (ModuleCat ℚ) (ComplexShape.down ℕ)).map
      (Quiver.Hom.op ((((CategoryTheory.linearYoneda ℚ (ModuleCat ℚ)).obj rationalCoefficient).rightOp
        |>.mapHomologicalComplex (ComplexShape.down ℕ)).map
        (transposeGraphSectionChainMap A F hf))) =
    (HomologicalComplex.unopFunctor (ModuleCat ℚ) (ComplexShape.down ℕ)).map
      (Quiver.Hom.op ((((CategoryTheory.linearYoneda ℚ (ModuleCat ℚ)).obj rationalCoefficient).rightOp
        |>.mapHomologicalComplex (ComplexShape.down ℕ)).map
        (singularChainMap A F))) := by
    rw [← CategoryTheory.Functor.map_comp, ← CategoryTheory.op_comp,
      ← CategoryTheory.Functor.map_comp, transposeGraphSectionChainMap_left]
  exact h1

/-- **EXACT NATIVE GRAPH ACTION.**
The carrier and its trace determine the actual map's Betti pullback.  No
source-action equation or target representative is an input. -/
theorem transposedStrictGraph_pushPull_eq_nativePullback
    (F : AnalyticEndomorphism A)
    (hf : IsFinite F.algebraic.hom)
    (n : Nat) :
    (transposedStrictGraphRightTrace A F hf n).pushPull =
      rationalCohomologyPullback A F n := by
  rw [RightFiniteBettiTrace.pushPull,
    transposedStrictGraph_normalizedTrace_eq_section]
  ext alpha
  unfold transposeGraphSectionCohomologyPullback
    leftCohomologyPullback leftCohomologyPullbackObj
    rationalCohomologyPullback rationalCohomologyPullbackObj
  have hcochain := leftCochainPullback_transposeGraphSection A F hf
  have hcomp : (HomologicalComplex.homologyMap
      (leftCochainPullback A ((strictGraph F.algebraic hf).transpose) ≫
        transposeGraphSectionCochainPullback A F hf) n).hom alpha =
    (HomologicalComplex.homologyMap (transposeGraphSectionCochainPullback A F hf) n).hom
      ((HomologicalComplex.homologyMap
        (leftCochainPullback A ((strictGraph F.algebraic hf).transpose)) n).hom alpha) := by
    rw [HomologicalComplex.homologyMap_comp]
    rfl
  rw [hcochain] at hcomp
  exact hcomp.symm

/-- Every source has its exact, geometrically determined common-carrier
target.  This statement does not identify that target with an arbitrary GST
matrix-unit sheet. -/
theorem transposedStrictGraph_related_nativePullback
    (F : AnalyticEndomorphism A)
    (hf : IsFinite F.algebraic.hom)
    (n : Nat)
    (alpha : RationalSingularCohomology A n) :
    BettiRelated A ((strictGraph F.algebraic hf).transpose) n alpha
      (rationalCohomologyPullback A F n alpha) := by
  apply (RightFiniteBettiTrace.bettiRelated_iff_residual_and_target
    A _ n (transposedStrictGraphRightTrace A F hf n) alpha _).2
  constructor
  · rw [transposedStrictGraph_sourceResidual_eq_zero]
    rfl
  · rw [transposedStrictGraph_pushPull_eq_nativePullback]

/-- Exact target test for this source-independent geometric construction.
The carrier-defect condition has been eliminated by proof; matching the
prescribed target remains a concrete native-map computation. -/
theorem transposedStrictGraph_related_iff_nativePullback
    (F : AnalyticEndomorphism A)
    (hf : IsFinite F.algebraic.hom)
    (n : Nat)
    (alpha beta : RationalSingularCohomology A n) :
    BettiRelated A ((strictGraph F.algebraic hf).transpose) n alpha beta ↔
      rationalCohomologyPullback A F n alpha = beta := by
  constructor
  · intro h
    have ht := RightFiniteBettiTrace.pushPull_eq_of_bettiRelated
      A _ n (transposedStrictGraphRightTrace A F hf n) h
    simpa only [transposedStrictGraph_pushPull_eq_nativePullback] using ht
  · intro h
    rw [← h]
    exact transposedStrictGraph_related_nativePullback A F hf n alpha

#check transposeGraphAnalyticSection
#check transposeGraphAnalyticSection_right
#check transposeGraphSectionCohomologyPullback_right
#check transposedStrictGraphRightTrace
#check transposedStrictGraph_rightPullback_injective

#print axioms transposeGraphAnalyticSection_right
#print axioms transposeGraphSectionCohomologyPullback_right
#print axioms transposedStrictGraphRightTrace
#print axioms transposedStrictGraph_rightPullback_injective

#check transposeGraphCarrierIso
#check transposedStrictGraph_related_iff_nativePullback
#print axioms transposeGraphCarrierIso
#print axioms transposedStrictGraph_carrierResidual_eq_zero
#print axioms transposedStrictGraph_sourceResidual_eq_zero
#print axioms transposedStrictGraph_transferObstruction_eq_zero
#print axioms transposedStrictGraph_pushPull_eq_nativePullback
#print axioms transposedStrictGraph_related_nativePullback
#print axioms transposedStrictGraph_related_iff_nativePullback

end GSTClassicalHodgeStrictGraphBettiTrace
