import GSTClassicalHodgeRealizedCorrespondenceExpressionAlgebra
import GSTClassicalHodgeDiagonalIdentityCorrespondence

/-!
# GST CLASSICAL HODGE — GEOMETRIC CORRESPONDENCE POLYNOMIAL CALCULUS

The full realized-correspondence expression algebra is now noncommutative and
contains a genuine geometric identity: the diagonal of X.

This file builds an explicit polynomial calculus INSIDE that geometry.  A list
of rational coefficients `[c₀,c₁,...,cₙ]` and one genuine realized
correspondence expression `T` are compiled by Horner recursion into

  c₀ I + T (c₁ I + T (...)).

The identity `I` is the actual diagonal correspondence, not an arbitrary
ambient identity.  Hence the resulting polynomial operator has a native cycle
face and an exact cycle-class commuting square automatically.

On an eigenvector `T a = λ a`, the compiled geometric expression acts by the
ordinary scalar polynomial evaluation.  This is the precise geometric socket
needed for spectral isolation without importing abstract Hodge-coordinate
projectors.
-/

set_option maxHeartbeats 100000000
set_option maxRecDepth 1000000

noncomputable section

open AlgebraicGeometry

namespace GSTClassicalHodgeGeometricCorrespondencePolynomialCalculus

open GSTProjectiveOverC
open GSTGeometricRealizationStage2D
open GSTGeometricRealizationStage2F
open GSTGeometricRealizationStage2G
open GSTClassicalHodgeRealizedCorrespondenceExpressionAlgebra
open GSTClassicalHodgeRealizedCorrespondenceExpressionAlgebra.RealizedCorrespondenceExpr
open GSTClassicalHodgeDiagonalIdentityCorrespondence

variable {V : SmoothProjectiveComplexScheme}
variable {H : HodgeBigradedBettiData V}
variable {p : Nat}

/-- The genuine diagonal correspondence as an expression atom. -/
noncomputable def diagonalExpr : RealizedCorrespondenceExpr V H p :=
  .atom (diagonalRealized (V := V) (H := H) (p := p))

@[simp] theorem diagonalExpr_cohomology
    (alpha : RationalSingularCohomology H.analytification (2 * p)) :
    (diagonalExpr (V := V) (H := H) (p := p)).cohomologyOperator alpha = alpha :=
  rfl

/-- Horner compilation of a rational coefficient list into the genuine
correspondence expression algebra.

`[]` is the zero polynomial.  `c :: cs` denotes `c + X * P_cs`. -/
noncomputable def hornerExpr
    (T : RealizedCorrespondenceExpr V H p) :
    List ℚ → RealizedCorrespondenceExpr V H p
  | [] => .zero
  | c :: cs =>
      .add (.smul c (diagonalExpr (V := V) (H := H) (p := p)))
        (.comp T (hornerExpr T cs))

/-- Matching scalar Horner evaluation. -/
def hornerScalar (lambda : ℚ) : List ℚ → ℚ
  | [] => 0
  | c :: cs => c + lambda * hornerScalar lambda cs

@[simp] theorem hornerExpr_nil
    (T : RealizedCorrespondenceExpr V H p) :
    hornerExpr T [] = .zero := rfl

@[simp] theorem hornerExpr_cons
    (T : RealizedCorrespondenceExpr V H p)
    (c : ℚ) (cs : List ℚ) :
    hornerExpr T (c :: cs) =
      .add (.smul c (diagonalExpr (V := V) (H := H) (p := p)))
        (.comp T (hornerExpr T cs)) := rfl

/-- **GEOMETRIC HORNER EIGENVECTOR LAW.**
If a genuine correspondence expression has eigenvalue lambda on alpha, every
compiled polynomial expression acts by the ordinary scalar Horner value. -/
theorem hornerExpr_on_eigenvector
    (T : RealizedCorrespondenceExpr V H p)
    (alpha : RationalSingularCohomology H.analytification (2 * p))
    (lambda : ℚ)
    (hT : T.cohomologyOperator alpha = lambda • alpha) :
    ∀ cs : List ℚ,
      (hornerExpr T cs).cohomologyOperator alpha =
        hornerScalar lambda cs • alpha := by
  intro cs
  induction cs with
  | nil =>
      simp [hornerExpr, hornerScalar, RealizedCorrespondenceExpr.cohomologyOperator,
        RealizedCorrespondenceExpr.operatorPair,
        GSTClassicalHodgeRealizedClosedCorrespondenceAlgebra.CycleClassOperatorPair.zero,
        LinearMap.zero_apply]
  | cons c cs ih =>
      change
        c • alpha +
          T.cohomologyOperator ((hornerExpr T cs).cohomologyOperator alpha) =
        (c + lambda * hornerScalar lambda cs) • alpha
      rw [ih, map_smul, hT]
      rw [add_smul, smul_smul, mul_comm (hornerScalar lambda cs) lambda]

/-- Every compiled polynomial expression satisfies exact native cycle-class
naturality because it lives inside the genuine correspondence expression
algebra. -/
theorem hornerExpr_cycleClass_natural
    (T : RealizedCorrespondenceExpr V H p)
    (cs : List ℚ)
    (Z : codimensionCycles V.X p) :
    H.cycleClass p ((hornerExpr T cs).cycleOperator Z) =
      (hornerExpr T cs).cohomologyOperator (H.cycleClass p Z) := by
  exact (hornerExpr T cs).cycleClass_natural Z

/-- Therefore polynomial functional calculus in one genuine correspondence
preserves the actual algebraic cycle-class range. -/
theorem hornerExpr_range_stable
    (T : RealizedCorrespondenceExpr V H p)
    (cs : List ℚ) :
    ∀ alpha,
      alpha ∈ LinearMap.range (H.cycleClass p) →
      (hornerExpr T cs).cohomologyOperator alpha ∈
        LinearMap.range (H.cycleClass p) :=
  (hornerExpr T cs).range_stable

#check diagonalExpr
#check hornerExpr
#check hornerScalar
#check hornerExpr_on_eigenvector
#check hornerExpr_cycleClass_natural
#check hornerExpr_range_stable

#print axioms hornerExpr_on_eigenvector
#print axioms hornerExpr_cycleClass_natural
#print axioms hornerExpr_range_stable

end GSTClassicalHodgeGeometricCorrespondencePolynomialCalculus
