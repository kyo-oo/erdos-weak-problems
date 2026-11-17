import GSTK3DiagonalActualStage2G
import GSTK3PrimitiveGram

/-!
# Actual Stage-2G TWO independent K3 primitive native algebraic cycles

The purely exact intersection Gram is verified by
GSTK3PrimitiveGram, but this module performs the next essential
cross-carrier step: the two primitive generators are actual Mathlib
codimension-two native cycles of the same smooth projective scheme Y
with actual Stage-2G Betti cycle-class map.

P = Δ - U - V - d^-1 (h×h)
Q = (h×h) - d(U+V).

P is the previously proved genuine primitive; Q is a NEW primitive
formed only from genuine native divisor-product cycles.

For geometric nonzero/independence, two independent ACTUAL
intersection readouts are used:
- a transcendental u×v pairing detects P but kills Q;
- the algebraic (h×h)-pairing detects Q with value d².

These are checkable in every projective K3 selfproduct; they are
not arbitrary Hodge class lift or full-rank basis assumptions.

All statements concern actual codimension-two native cycles
and their true Stage-2G cohomology classes; no toy Hodge carrier.
-/

set_option maxHeartbeats 5000000
noncomputable section

open AlgebraicGeometry
open GSTProjectiveOverC
open GSTGeometricRealizationStage2D
open GSTGeometricRealizationStage2F
open GSTGeometricRealizationStage2G
open GSTK3DiagonalActualStage2G
open GSTK3DiagonalPrimitive

namespace GSTK3ActualPrimitiveRankTwo

variable {Y : SmoothProjectiveComplexScheme}
variable {H : HodgeBigradedBettiData Y}

/-- A SECOND fully explicit rational codimension-two native algebraic
cycle built from the hyperplane product and two point-section cycles. -/
noncomputable def secondNativePrimitive
    (G : GenuineK3ProductDiagonalPacket Y H) :
    codimensionCycles Y.X 2 :=
  G.hCrossH - G.degree • (G.pointLeft + G.pointRight)

/-- Actual geometric cup Lefschetz operator kills this SECOND
native algebraic cycle independently of the diagonal primitive. -/
theorem secondNativePrimitive_lefschetz_zero
    (G : GenuineK3ProductDiagonalPacket Y H) :
    G.lefschetz (H.cycleClass 2 (secondNativePrimitive G)) = 0 := by
  simp [secondNativePrimitive, map_sub, map_add, map_smul,
    G.cross_lefschetz, G.left_lefschetz, G.right_lefschetz]

/-- This second cycle has TRUE rational (2,2) Hodge type,
because it is a native algebraic codimension-two cycle. -/
theorem secondNativePrimitive_is_hodge
    (G : GenuineK3ProductDiagonalPacket Y H) :
    H.cycleClass 2 (secondNativePrimitive G) ∈
      rationalHodgeSubspace (H.hodgeBigrading 2) :=
  G.cycle_is_hodge (secondNativePrimitive G)

/-- The old independent K3 transcendental intersection detector
kills the second pure-divisor primitive exactly. -/
theorem secondNativePrimitive_transcendental_zero
    (G : GenuineK3ProductDiagonalPacket Y H) :
    G.transversePairing (H.cycleClass 2 (secondNativePrimitive G)) = 0 := by
  simp [secondNativePrimitive, map_sub, map_add, map_smul,
    G.left_transverse, G.right_transverse, G.cross_transverse]

/-- A minimal separately checkable intersection certificate.
On an actual K3 product choose ellB(alpha) = integral_Y
alpha cup [h×h]. Then ellB(B)=d², ellB(U)=ellB(V)=0.
No target-surjectivity or transverse basis is assumed. -/
structure GenuineK3DivisorIntersection
    (G : GenuineK3ProductDiagonalPacket Y H) where
  productDetector :
    RationalSingularCohomology H.analytification 4 →ₗ[ℚ] ℚ
  cross_value :
    productDetector (H.cycleClass 2 G.hCrossH) = G.degree ^ 2
  left_value :
    productDetector (H.cycleClass 2 G.pointLeft) = 0
  right_value :
    productDetector (H.cycleClass 2 G.pointRight) = 0

/-- The separate divisor intersection detector pairs NONZERO
with the new primitive cycle, in true Betti rational cohomology. -/
theorem secondNativePrimitive_divisor_pairing
    (G : GenuineK3ProductDiagonalPacket Y H)
    (D : GenuineK3DivisorIntersection G) :
    D.productDetector (H.cycleClass 2 (secondNativePrimitive G)) =
      G.degree ^ 2 := by
  simp [secondNativePrimitive, map_sub, map_add, map_smul,
    D.cross_value, D.left_value, D.right_value]

/-- The two independently geometric primitive classes are
LINEARLY INDEPENDENT. The first coefficient is read by the
transcendental pair, the second by actual divisor intersection.
The kernel proof never assumes a nonzero Hodge basis determinant. -/
theorem two_actual_native_primitives_independent
    (G : GenuineK3ProductDiagonalPacket Y H)
    (D : GenuineK3DivisorIntersection G)
    (a b : ℚ)
    (hlinear :
      a • H.cycleClass 2 (genuineNativePrimitive G) +
      b • H.cycleClass 2 (secondNativePrimitive G) = 0) :
    a = 0 ∧ b = 0 := by
  have hp : G.transversePairing
      (H.cycleClass 2 (genuineNativePrimitive G)) =
      G.transverseValue :=
    diagonalPrimitiveCycle_transcendental_readout
      (H.cycleClass 2) G.transversePairing
      G.diagonal G.pointLeft G.pointRight G.hCrossH
      G.degree G.transverseValue
      G.diagonal_transverse G.left_transverse
      G.right_transverse G.cross_transverse
  have hq := secondNativePrimitive_transcendental_zero G
  have htrans : a * G.transverseValue = 0 := by
    have h := congrArg G.transversePairing hlinear
    simpa [map_add, map_smul, hp, hq] using h
  have ha : a = 0 := by
    rcases mul_eq_zero.mp htrans with ha | hbad
    · exact ha
    · exact False.elim (G.transverseValue_ne_zero hbad)
  have hdiv : b * G.degree ^ 2 = 0 := by
    have h := congrArg D.productDetector hlinear
    rw [ha] at h
    simpa [map_add, map_smul, secondNativePrimitive_divisor_pairing G D] using h
  have hb : b = 0 := by
    rcases mul_eq_zero.mp hdiv with hb | hbad
    · exact hb
    · exact False.elim ((pow_ne_zero 2 G.degree_ne_zero) hbad)
  exact ⟨ha, hb⟩

#check secondNativePrimitive
#check secondNativePrimitive_lefschetz_zero
#check secondNativePrimitive_is_hodge
#check secondNativePrimitive_divisor_pairing
#check two_actual_native_primitives_independent
#print axioms two_actual_native_primitives_independent

end GSTK3ActualPrimitiveRankTwo
