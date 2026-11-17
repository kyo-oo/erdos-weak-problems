import GSTClassicalHodgeRealizedClosedCorrespondenceAlgebra
import GSTClassicalHodgeStage2GSemanticRigidity

/-!
# GST realized correspondence semantic firewall

The current `RealizedFiniteClosedCorrespondence` record contains a true
finite-closed scheme correspondence K and a cohomological operator T, but its
pointwise realization law only constrains T on the image of the cycle-class
map. In a semantic instance whose cycle-class map is zero, EVERY linear
operator T passes that same realization law for exactly the SAME K.

The theorems here prove this ambiguity inside Lean. If rational cohomology
in degree 2p is nonzero, both the ZERO endomorphism and the IDENTITY
endomorphism can be packaged as distinct "realized" Betti actions on the
same native finite-closed correspondence for the zero-cycle-class model.

Thus pointwise compatibility does not pin the off-image cohomology action.
The missing geometric input is a canonical construction of the true
cohomological correspondence action on the FULL Betti space, followed by
a proof of its correct naturality. It cannot be replaced by a free choice
of endomorphism matching already-algebraic point classes.

This is a countermodel to the *formal interface*, not a counterexample to
the actual Hodge conjecture on honest smooth projective varieties.
-/

set_option maxHeartbeats 10000000

noncomputable section

open AlgebraicGeometry
open GSTProjectiveOverC
open GSTGeometricRealizationStage2D
open GSTGeometricRealizationStage2F
open GSTGeometricRealizationStage2G
open GSTClassicalHodgeFiniteClosedCorrespondence
open GSTClassicalHodgeFiniteClosedCorrespondenceOperator
open GSTClassicalHodgeRealizedClosedCorrespondenceAlgebra
open GSTClassicalHodgeStage2GSemanticRigidity

namespace GSTClassicalHodgeCorrespondenceSemanticFirewall

variable {V : SmoothProjectiveComplexScheme}
variable (H : HodgeBigradedBettiData V)
variable (p : Nat)

abbrev BettiAt :=
  RationalSingularCohomology H.analytification (2 * p)

/-- With the ZERO cycle-class map, pointwise realization holds for EVERY
cohomological endomorphism of the identical Betti space and for EVERY
genuine finite-closed correspondence K. -/
theorem every_ambient_operator_realized_on_zero_cycleClass
    (K : FiniteClosedCorrespondence V)
    (T : BettiAt H p →ₗ[ℚ] BettiAt H p) :
    K.RealizesAmbientOnPoints
      (H := zeroCycleClassData H) T := by
  intro x
  change (0 : BettiAt H p) = T (0 : BettiAt H p)
  simp

/-- Package any ambient endomorphism over the exact same true geometric
correspondence when the semantic cycle-class map is zero. -/
noncomputable def zeroClassRealization
    (K : FiniteClosedCorrespondence V)
    (T : BettiAt H p →ₗ[ℚ] BettiAt H p) :
    RealizedFiniteClosedCorrespondence V (zeroCycleClassData H) p where
  geometry := K
  cohomologyOperator := T
  realizes_on_points :=
    every_ambient_operator_realized_on_zero_cycleClass H p K T

/-- A nontrivial Betti fiber yields TWO distinct cohomology actions on the
SAME finite-closed geometric correspondence that both satisfy every existing
pointwise realization rule. The native geometry is literally identical.
Hence the off-image action is not a consequence of those rules. -/
theorem realized_cohomology_operator_not_fixed_by_point_law
    (K : FiniteClosedCorrespondence V)
    (a : BettiAt H p)
    (hne : a ≠ 0) :
    ∃ R S :
      RealizedFiniteClosedCorrespondence V (zeroCycleClassData H) p,
      R.geometry = S.geometry ∧
        R.cohomologyOperator ≠ S.cohomologyOperator := by
  let R := zeroClassRealization H p K (0 : BettiAt H p →ₗ[ℚ] BettiAt H p)
  let S := zeroClassRealization H p K
    (LinearMap.id : BettiAt H p →ₗ[ℚ] BettiAt H p)
  refine ⟨R, S, rfl, ?_⟩
  intro heq
  have hzero : (0 : BettiAt H p) = a := by
    have hval :=
      congrArg (fun T : BettiAt H p →ₗ[ℚ] BettiAt H p => T a) heq
    simpa [R, S, zeroClassRealization] using hval
  exact hne hzero.symm

#check every_ambient_operator_realized_on_zero_cycleClass
#check zeroClassRealization
#check realized_cohomology_operator_not_fixed_by_point_law

#print axioms every_ambient_operator_realized_on_zero_cycleClass
#print axioms realized_cohomology_operator_not_fixed_by_point_law

end GSTClassicalHodgeCorrespondenceSemanticFirewall
