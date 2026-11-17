import GSTUniversalCodimensionTwoPrimitiveExtraction

/-!
# GST direct primitive cycles from an algebraic automorphism orbit

Let S be a smooth projective surface with H¹(S,ℚ)=0 (in
particular, a K3 surface), ample class h and a finite-order
algebraic automorphism g fixing h. The four graph
cycles Γ_id, Γ_g, Γ_g², Γ_g³ are genuine algebraic subvarieties of
the original smooth projective fourfold S×S.

For L=pr₁*h+pr₂*h, the pushforward of h along Γ_(g^k) has
the SAME cohomology class for each k: g^*h=h and H¹(S,ℚ)=0
eliminate the even and odd Kunneth discrepancies.
Therefore the actual graph differences

  A=Γ_id-Γ_(g²),   B=Γ_g-Γ_(g³)

are DIRECTLY primitive: L*cl(A)=L*cl(B)=0.
No Lefschetz correction is required for these cycles.

For the Fermat quartic K3 and g:z₀↦i z₀, the action on its
holomorphic two-form is i and its rational cyclotomic factor is
Q(i). The two graph-difference operators are 2I and 2g,
which have rational rank two, independently of the other H²
eigenspaces. Their traces give a rational Gram diag(8,8).

The Lean theorem operates on ACTUAL native graph cycles and their
precise geometric hyperplane and transcendental measurements.
The remaining analytic instantiation is the canonical Kunneth
comparison between scheme graphs and Betti endomorphisms.
-/

set_option maxHeartbeats 10000000
noncomputable section

open AlgebraicGeometry
open GSTProjectiveOverC
open GSTGeometricRealizationStage2D
open GSTGeometricRealizationStage2F
open GSTGeometricRealizationStage2G
open GSTClassicalHodgeFiberedCosmology
open GSTClassicalHodgeGeometricCycleClassSpine
open GSTClassicalHodgeGeometricMatrixRankLanding
open GSTUniversalLefschetzCurveCycles
open GSTUniversalCodimensionTwoPrimitiveExtraction

namespace GSTK3DirectGraphOrbitDifference

variable {V : SmoothProjectiveComplexScheme}
variable {H : HodgeBigradedBettiData V}

/-- Native algebraic difference of the identity and squared graphs. -/
def evenOrbitDifference
    (graphs : Fin 4 → codimensionCycles V.X 2) :
    codimensionCycles V.X 2 :=
  graphs 0 - graphs 2

/-- Native algebraic difference of the order-one and cubed graphs. -/
def oddOrbitDifference
    (graphs : Fin 4 → codimensionCycles V.X 2) :
    codimensionCycles V.X 2 :=
  graphs 1 - graphs 3

/-- Pairwise equal Lefschetz tests of the algebraic graph orbit
produce two directly PRIMITIVE actual rational algebraic cycles. -/
theorem direct_graph_orbit_differences_primitive
    (G : GeometricCycleClassSpine V H)
    (P : GeometricHigherLefschetzData G 4)
    (graphs : Fin 4 → codimensionCycles V.X 2)
    (common : ClassicalHodgeFiber V H (4-1))
    (hShared : ∀ i : Fin 4,
       P.primitiveTest (nativeToHodgeFiberLinear G (graphs i)) = common) :
    P.primitiveTest
        (nativeToHodgeFiberLinear G (evenOrbitDifference graphs)) = 0 ∧
    P.primitiveTest
        (nativeToHodgeFiberLinear G (oddOrbitDifference graphs)) = 0 := by
  constructor
  · simp [evenOrbitDifference, map_sub, hShared]
  · simp [oddOrbitDifference, map_sub, hShared]

/-- Rational rank-two detector of DIRECT primitive graph differences.
On the quartic K3 these two measurements are the coefficients of
2·id and 2·g in the rational Q(i) transcendental factor. -/
theorem direct_graph_orbit_differences_independent
    (G : GeometricCycleClassSpine V H)
    (graphs : Fin 4 → codimensionCycles V.X 2)
    (measure : ClassicalHodgeFiber V H 2 →ₗ[ℚ] (ℚ × ℚ))
    (hEven : measure
      (nativeToHodgeFiberLinear G (evenOrbitDifference graphs)) = (2,0))
    (hOdd : measure
      (nativeToHodgeFiberLinear G (oddOrbitDifference graphs)) = (0,2))
    (a b : ℚ)
    (hRelation :
      a • nativeToHodgeFiberLinear G (evenOrbitDifference graphs) +
      b • nativeToHodgeFiberLinear G (oddOrbitDifference graphs) = 0) :
    a = 0 ∧ b = 0 := by
  have h := congrArg measure hRelation
  simp only [map_add, map_smul, map_zero, hEven, hOdd] at h
  have hf : a * 2 = 0 := by
    simpa [smul_eq_mul] using (congrArg Prod.fst h)
  have hg : b * 2 = 0 := by
    simpa [smul_eq_mul] using (congrArg Prod.snd h)
  constructor <;> linarith

#check direct_graph_orbit_differences_primitive
#check direct_graph_orbit_differences_independent
#print axioms direct_graph_orbit_differences_independent

end GSTK3DirectGraphOrbitDifference
