import GSTClassicalHodgeStrictCorrespondenceAnalyticSpan

/-!
# GST CLASSICAL HODGE — STRICT CORRESPONDENCE ANALYTIC TRANSPOSE

The algebraic factor-swap transpose of a strict scheme-bi-finite
correspondence has the same carrier scheme and exchanges its two projections.
The intrinsic analytic-span construction therefore has an exact transpose law
already at the level of actual complex points: the analytic pair of `Kᵗ` is the
coordinate swap of the analytic pair of `K`.

This theorem is independent of any transfer, Gysin map, Hodge class, or
cycle-class range.  It fixes the orientation of the eventual push-pull action
and prevents a formal coefficient transpose from being substituted for the
actual algebraic factor swap.
-/

set_option maxHeartbeats 100000000
set_option maxRecDepth 1000000

noncomputable section

open CategoryTheory
open AlgebraicGeometry

namespace GSTClassicalHodgeStrictCorrespondenceAnalyticTranspose

open GSTProjectiveOverC
open GSTGeometricRealizationStage2F
open GSTClassicalHodgeSchemeFiniteCorrespondenceFirewall
open GSTClassicalHodgeStrictCorrespondenceAnalyticSpan

variable {V : SmoothProjectiveComplexScheme}
variable (A : AnalytificationData V)

/-- The carrier complex-point types of `K` and its genuine factor-swap
transpose are canonically equivalent: both use the same carrier scheme, and
the two possible structure maps to `Spec C` agree. -/
noncomputable def transposeCarrierPointEquiv
    (K : SchemeBiFiniteClosedCorrespondence V) :
    CarrierComplexPoint K.transpose ≃ CarrierComplexPoint K where
  toFun z := by
    refine ⟨z.1, ?_⟩
    calc
      (z.1 ≫ K.toSchemeFiniteClosedCorrespondence.left) ≫ V.structureMap =
          z.1 ≫
            (K.toSchemeFiniteClosedCorrespondence.left ≫ V.structureMap) := by
              exact Category.assoc _ _ _
      _ = z.1 ≫ (K.right ≫ V.structureMap) := by
            exact congrArg (fun g => z.1 ≫ g) (left_toBase_eq_right_toBase K)
      _ = (z.1 ≫ K.transpose.toSchemeFiniteClosedCorrespondence.left) ≫
            V.structureMap := by
              exact (congrArg (fun g => z.1 ≫ g ≫ V.structureMap)
                (K.transpose_left).symm).trans (Category.assoc _ _ _).symm
      _ = 𝟙 complexBase := z.2
  invFun z := by
    refine ⟨z.1, ?_⟩
    calc
      (z.1 ≫ K.transpose.toSchemeFiniteClosedCorrespondence.left) ≫
          V.structureMap = (z.1 ≫ K.right) ≫ V.structureMap := by
            rw [K.transpose_left]
      _ = z.1 ≫ (K.right ≫ V.structureMap) := by simp [Category.assoc]
      _ = z.1 ≫
          (K.toSchemeFiniteClosedCorrespondence.left ≫ V.structureMap) := by
            rw [← left_toBase_eq_right_toBase K]
      _ = 𝟙 complexBase := by simpa [Category.assoc] using z.2
  left_inv z := by
    apply Subtype.ext
    rfl
  right_inv z := by
    apply Subtype.ext
    rfl

/-- Under transpose, the left analytic point is the original right point. -/
theorem transpose_leftComplexPoint
    (K : SchemeBiFiniteClosedCorrespondence V)
    (z : CarrierComplexPoint K.transpose) :
    leftComplexPoint K.transpose z =
      rightComplexPoint K (transposeCarrierPointEquiv K z) := by
  apply Subtype.ext
  simp [leftComplexPoint, rightComplexPoint,
    SchemeBiFiniteClosedCorrespondence.transpose_left]
  rfl

/-- Under transpose, the right analytic point is the original left point. -/
theorem transpose_rightComplexPoint
    (K : SchemeBiFiniteClosedCorrespondence V)
    (z : CarrierComplexPoint K.transpose) :
    rightComplexPoint K.transpose z =
      leftComplexPoint K (transposeCarrierPointEquiv K z) := by
  apply Subtype.ext
  simp [leftComplexPoint, rightComplexPoint,
    SchemeBiFiniteClosedCorrespondence.transpose_right]
  rfl

/-- **POINTWISE ANALYTIC TRANSPOSE LAW.** -/
theorem transpose_carrierPointPair
    (K : SchemeBiFiniteClosedCorrespondence V)
    (z : CarrierComplexPoint K.transpose) :
    carrierPointPair A K.transpose z =
      ( (carrierPointPair A K (transposeCarrierPointEquiv K z)).2,
        (carrierPointPair A K (transposeCarrierPointEquiv K z)).1 ) := by
  ext <;>
    simp [carrierPointPair, transpose_leftComplexPoint,
      transpose_rightComplexPoint]

/-- The analytic locus of the genuine algebraic transpose is exactly the
coordinate swap of the original analytic locus. -/
theorem mem_analyticLocus_transpose_iff
    (K : SchemeBiFiniteClosedCorrespondence V)
    (q : A.space × A.space) :
    q ∈ analyticLocus A K.transpose ↔
      (q.2, q.1) ∈ analyticLocus A K := by
  constructor
  · rintro ⟨z, rfl⟩
    refine ⟨transposeCarrierPointEquiv K z, ?_⟩
    rw [transpose_carrierPointPair]
  · rintro ⟨z, hz⟩
    let zt : CarrierComplexPoint K.transpose :=
      (transposeCarrierPointEquiv K).symm z
    refine ⟨zt, ?_⟩
    have hpair := transpose_carrierPointPair A K zt
    have he : transposeCarrierPointEquiv K zt = z := by simp [zt]
    rw [he] at hpair
    rw [hz] at hpair
    simpa using hpair

/-- Set-level factor-swap form of the same result. -/
theorem analyticLocus_transpose
    (K : SchemeBiFiniteClosedCorrespondence V) :
    analyticLocus A K.transpose =
      {q : A.space × A.space | (q.2,q.1) ∈ analyticLocus A K} := by
  ext q
  exact mem_analyticLocus_transpose_iff A K q

#check transposeCarrierPointEquiv
#check transpose_carrierPointPair
#check mem_analyticLocus_transpose_iff
#check analyticLocus_transpose

#print axioms transpose_carrierPointPair
#print axioms analyticLocus_transpose

end GSTClassicalHodgeStrictCorrespondenceAnalyticTranspose
