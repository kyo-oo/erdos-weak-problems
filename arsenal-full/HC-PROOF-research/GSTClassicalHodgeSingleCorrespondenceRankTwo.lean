import GSTClassicalHodgeActualCommutatorRankGain

/-!
# GST single-correspondence, weight-local charge-wedge rank gain

Fix ONE weight p and its actual native projective spine Z with Hodge class s.
Choose one rational Hodge-fiber functional ell with ell(s) != 0, and one
genuinely realized finite-closed geometric correspondence expression T.

Define the NATIVE ALGEBRAIC cycle
  Delta = ell(s) • T_native(Z) - ell(T_Betti(s)) • Z.

Geometric cycle-class naturality gives its exact Betti class. A two-term
cancellation makes this class charge-orthogonal to s for *every* T. If
its class is nonzero, the two are linearly independent; in a rank-two Hodge
fiber, this closes every Hodge class at that weight.

Crucial semantic refinement: ell is a functional of ONLY this Hodge fiber.
We do NOT require a nonzero conserved charge in every natural-number weight;
such a global hypothesis is incompatible with genuine bounded cohomological
degree support. This is an honest conditional geometric rank-gain criterion,
not a universal geometric nonvanishing theorem.
-/

set_option maxHeartbeats 20000000

noncomputable section

open scoped BigOperators
open AlgebraicGeometry
open GSTProjectiveOverC
open GSTGeometricRealizationStage2D
open GSTGeometricRealizationStage2F
open GSTGeometricRealizationStage2G
open GSTClassicalHodgeFiberedCosmology
open GSTClassicalHodgeGeometricCycleClassSpine
open GSTClassicalHodgeLimitlessSpinePropagation
open GSTClassicalHodgeRealizedCorrespondenceExpressionAlgebra
open GSTClassicalHodgeRankFreeArsenalIrreducibility
open GSTClassicalHodgeAtomicSpan

namespace GSTClassicalHodgeSingleCorrespondenceRankTwo

variable {V : SmoothProjectiveComplexScheme}
variable {H : HodgeBigradedBettiData V}
variable {p : Nat}

/-- A REALIZED geometric correspondence carries the native spine to another
genuine algebraic Hodge vector. No preservation of arbitrary Hodge states is
assumed or needed. -/
noncomputable def movedSpine
    (G : GeometricCycleClassSpine V H)
    (E : RealizedCorrespondenceExpr V H p) :
    ClassicalHodgeFiber V H p :=
  ⟨E.cohomologyOperator (spineHodgeSeed G p).1, by
    have h :=
      G.algebraic_is_hodge p (E.cycleOperator (spineNativeTower G p))
    rw [E.cycleClass_natural, spineNativeTower_cycleClass] at h
    exact h⟩

/-- Native charge wedge from ONE correspondence and ONE local readout. -/
noncomputable def nativeChargeWedge
    (G : GeometricCycleClassSpine V H)
    (ell : ClassicalHodgeFiber V H p →ₗ[ℚ] ℚ)
    (E : RealizedCorrespondenceExpr V H p) :
    codimensionCycles V.X p :=
  (ell (spineHodgeSeed G p)) •
      E.cycleOperator (spineNativeTower G p) -
    (ell (movedSpine G E)) • spineNativeTower G p

/-- The same charge wedge constructed directly inside the Hodge fiber. -/
noncomputable def hodgeChargeWedge
    (G : GeometricCycleClassSpine V H)
    (ell : ClassicalHodgeFiber V H p →ₗ[ℚ] ℚ)
    (E : RealizedCorrespondenceExpr V H p) :
    ClassicalHodgeFiber V H p :=
  (ell (spineHodgeSeed G p)) • movedSpine G E -
    (ell (movedSpine G E)) • spineHodgeSeed G p

/-- The wedge really comes from an ACTUAL native algebraic cycle, by the
natural cycle/cohomology commuting square of the geometric correspondence. -/
theorem nativeChargeWedge_cycleClass
    (G : GeometricCycleClassSpine V H)
    (ell : ClassicalHodgeFiber V H p →ₗ[ℚ] ℚ)
    (E : RealizedCorrespondenceExpr V H p) :
    H.cycleClass p (nativeChargeWedge G ell E) =
      (hodgeChargeWedge G ell E).1 := by
  simp only [nativeChargeWedge, hodgeChargeWedge, map_sub,
    map_smul, Submodule.coe_sub, Submodule.coe_smul_of_tower,
    E.cycleClass_natural, spineNativeTower_cycleClass]
  rfl

/-- THE WEIGHT-LOCAL CHARGE IDENTITY: no global conserved-charge structure
and no charge-eigenoperator hypothesis appear in the theorem. -/
theorem hodgeChargeWedge_charge_zero
    (G : GeometricCycleClassSpine V H)
    (ell : ClassicalHodgeFiber V H p →ₗ[ℚ] ℚ)
    (E : RealizedCorrespondenceExpr V H p) :
    ell (hodgeChargeWedge G ell E) = 0 := by
  unfold hodgeChargeWedge
  rw [map_sub, map_smul, map_smul]
  simp only [smul_eq_mul]
  ring

/-- If the geometric wedge is nonzero, it is rigorously independent of the
nonzero-charge native spine, without a second geometric correspondence. -/
theorem spine_chargeWedge_linearIndependent
    (G : GeometricCycleClassSpine V H)
    (ell : ClassicalHodgeFiber V H p →ₗ[ℚ] ℚ)
    (hlive : ell (spineHodgeSeed G p) ≠ 0)
    (E : RealizedCorrespondenceExpr V H p)
    (htransverse : hodgeChargeWedge G ell E ≠ 0) :
    LinearIndependent ℚ
      ![spineHodgeSeed G p, hodgeChargeWedge G ell E] := by
  apply (LinearIndependent.pair_iff).2
  intro a b hab
  have hread :
      a * ell (spineHodgeSeed G p) +
        b * ell (hodgeChargeWedge G ell E) = 0 := by
    have h := congrArg ell hab
    simpa only [map_add, map_smul, map_zero, smul_eq_mul] using h
  have haMul : a * ell (spineHodgeSeed G p) = 0 := by
    simpa [hodgeChargeWedge_charge_zero G ell E] using hread
  have ha : a = 0 := (mul_eq_zero.mp haMul).resolve_right hlive
  subst a
  have hbSmul : b • hodgeChargeWedge G ell E = 0 := by
    simpa using hab
  have hb : b = 0 := (smul_eq_zero.mp hbSmul).resolve_right htransverse
  exact ⟨rfl, hb⟩

/-- Exact rank-two Hodge conclusion from ONE transverse actual geometric
correspondence. The required nonzero transverse wedge remains an explicit
geometric input; there is no target preimage or Hodge-surjectivity premise. -/
theorem every_rank_two_hodge_class_of_one_transverse_correspondence
    (G : GeometricCycleClassSpine V H)
    (ell : ClassicalHodgeFiber V H p →ₗ[ℚ] ℚ)
    (hlive : ell (spineHodgeSeed G p) ≠ 0)
    (E : RealizedCorrespondenceExpr V H p)
    (htransverse : hodgeChargeWedge G ell E ≠ 0)
    [FiniteDimensional ℚ (ClassicalHodgeFiber V H p)]
    (hrank : Module.finrank ℚ (ClassicalHodgeFiber V H p) = 2)
    (alpha : RationalSingularCohomology H.analytification (2 * p))
    (halpha : alpha ∈ rationalHodgeSubspace (H.hodgeBigrading p)) :
    ∃ Z : codimensionCycles V.X p, H.cycleClass p Z = alpha := by
  have hLI :
      LinearIndependent ℚ
        ![spineHodgeSeed G p, hodgeChargeWedge G ell E] :=
    spine_chargeWedge_linearIndependent G ell hlive E htransverse
  have hspan :
      Submodule.span ℚ
        (Set.range (![spineHodgeSeed G p, hodgeChargeWedge G ell E] :
          Fin 2 → ClassicalHodgeFiber V H p)) = ⊤ :=
    hLI.span_eq_top_of_card_eq_finrank' (by simpa [hrank])
  let S := AlgebraicHodgeSubspace V H p
  have hseed : spineHodgeSeed G p ∈ S :=
    spineHodgeSeed_algebraic G p
  have htarget : hodgeChargeWedge G ell E ∈ S := by
    change (hodgeChargeWedge G ell E).1 ∈
      pointCycleClassSpan p (H.cycleClass p)
    rw [← smoothProjective_cycleClass_range_eq_atomic_span V H p]
    exact ⟨nativeChargeWedge G ell E,
      nativeChargeWedge_cycleClass G ell E⟩
  have hS : S = ⊤ := by
    apply top_unique
    rw [← hspan]
    apply Submodule.span_le.mpr
    rintro x ⟨i, rfl⟩
    fin_cases i
    · simpa using hseed
    · simpa using htarget
  have hmem : (⟨alpha, halpha⟩ :
      ClassicalHodgeFiber V H p) ∈ S := by
    rw [hS]
    trivial
  change alpha ∈ pointCycleClassSpan p (H.cycleClass p) at hmem
  rw [← smoothProjective_cycleClass_range_eq_atomic_span V H p] at hmem
  exact hmem

/-- A scalar action on the actual native spine cannot create a new
geometric Hodge direction. This is an explicit no-go certificate. -/
theorem hodgeChargeWedge_eq_zero_of_scalar_spine_action
    (G : GeometricCycleClassSpine V H)
    (ell : ClassicalHodgeFiber V H p →ₗ[ℚ] ℚ)
    (E : RealizedCorrespondenceExpr V H p)
    (c : ℚ)
    (hscalar : movedSpine G E = c • spineHodgeSeed G p) :
    hodgeChargeWedge G ell E = 0 := by
  simp [hodgeChargeWedge, hscalar, smul_smul, mul_comm]

/-- Any verified transverse geometric action escapes the projective spine
line. The geometric hypothesis is an independently checkable statement about
ONE realized closed correspondence rather than an assumed rank-full basis. -/
theorem hodgeChargeWedge_ne_zero_of_no_scalar_spine_action
    (G : GeometricCycleClassSpine V H)
    (ell : ClassicalHodgeFiber V H p →ₗ[ℚ] ℚ)
    (hlive : ell (spineHodgeSeed G p) ≠ 0)
    (E : RealizedCorrespondenceExpr V H p)
    (hnot : ∀ c : ℚ, movedSpine G E ≠ c • spineHodgeSeed G p) :
    hodgeChargeWedge G ell E ≠ 0 := by
  intro hz
  let d := ell (spineHodgeSeed G p)
  let q := ell (movedSpine G E)
  have heq : d • movedSpine G E = q • spineHodgeSeed G p := by
    have h := hz
    change d • movedSpine G E - q • spineHodgeSeed G p = 0 at h
    exact sub_eq_zero.mp h
  have hrepr :
      movedSpine G E = (d⁻¹ * q) • spineHodgeSeed G p := by
    calc
      movedSpine G E = (d⁻¹ * d) • movedSpine G E := by simp [d, hlive]
      _ = d⁻¹ • (d • movedSpine G E) := by rw [smul_smul]
      _ = d⁻¹ • (q • spineHodgeSeed G p) := by rw [heq]
      _ = (d⁻¹ * q) • spineHodgeSeed G p := by rw [smul_smul]
  exact hnot (d⁻¹ * q) hrepr

/-- The one-operator rank-two Hodge result can be triggered by a purely
geometric *nonproportionality* observation; no precomputed wedge determinant
or per-target algebraic-cycle preimage is required. -/
theorem every_rank_two_hodge_class_of_nonproportional_geometric_action
    (G : GeometricCycleClassSpine V H)
    (ell : ClassicalHodgeFiber V H p →ₗ[ℚ] ℚ)
    (hlive : ell (spineHodgeSeed G p) ≠ 0)
    (E : RealizedCorrespondenceExpr V H p)
    (hnot : ∀ c : ℚ, movedSpine G E ≠ c • spineHodgeSeed G p)
    [FiniteDimensional ℚ (ClassicalHodgeFiber V H p)]
    (hrank : Module.finrank ℚ (ClassicalHodgeFiber V H p) = 2)
    (alpha : RationalSingularCohomology H.analytification (2 * p))
    (halpha : alpha ∈ rationalHodgeSubspace (H.hodgeBigrading p)) :
    ∃ Z : codimensionCycles V.X p, H.cycleClass p Z = alpha :=
  every_rank_two_hodge_class_of_one_transverse_correspondence
    G ell hlive E
    (hodgeChargeWedge_ne_zero_of_no_scalar_spine_action G ell hlive E hnot)
    hrank alpha halpha

#check movedSpine
#check nativeChargeWedge
#check nativeChargeWedge_cycleClass
#check hodgeChargeWedge_charge_zero
#check spine_chargeWedge_linearIndependent
#check hodgeChargeWedge_eq_zero_of_scalar_spine_action
#check hodgeChargeWedge_ne_zero_of_no_scalar_spine_action
#check every_rank_two_hodge_class_of_nonproportional_geometric_action
#check every_rank_two_hodge_class_of_one_transverse_correspondence

#print axioms nativeChargeWedge_cycleClass
#print axioms hodgeChargeWedge_charge_zero
#print axioms spine_chargeWedge_linearIndependent
#print axioms hodgeChargeWedge_ne_zero_of_no_scalar_spine_action
#print axioms every_rank_two_hodge_class_of_nonproportional_geometric_action
#print axioms every_rank_two_hodge_class_of_one_transverse_correspondence

end GSTClassicalHodgeSingleCorrespondenceRankTwo
