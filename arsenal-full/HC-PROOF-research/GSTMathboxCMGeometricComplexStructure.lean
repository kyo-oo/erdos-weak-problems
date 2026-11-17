import GSTClassicalHodgeSingleCorrespondenceRankTwo
import Mathlib

/-!
# Mathbox GST: independent CM geometry from J^2 = -identity

Instead of POSTULATING nonzero transverse movement of a geometric
correspondence, deduce it from the structural CM/quadratic law.

Pure rational algebraic theorem:
If J is a rational-linear endomorphism of W and J(J z)=-z for
every z, no nonzero z has J z = c*z for rational c, because this
would force c^2 = -1 in Q.

Actual geometric application:
If a truly REALIZED correspondence E on a rank-two rational Hodge
fiber is the spine action of such a rational complex-structure J,
its moved spine is necessarily nonproportional to the native
algebraic spine. A separating rational readout is obtained from
an existing Hodge-basis coordinate, NOT passed as an extra hypothesis.
The previous GST rank-two theorem then explicitly constructs
a rational native algebraic cycle for every rational Hodge class.

The quadratic CM relation on the actual geometric correspondence is
a mathematical geometric construction obligation. The proof does
NOT assert that such a J/E exists on every smooth projective
complex variety; an odd-dimensional rational Hodge fiber cannot
carry any J with J^2 = -I at all.
-/

set_option maxHeartbeats 20000000

noncomputable section

open AlgebraicGeometry
open GSTProjectiveOverC
open GSTGeometricRealizationStage2D
open GSTGeometricRealizationStage2F
open GSTGeometricRealizationStage2G
open GSTClassicalHodgeFiberedCosmology
open GSTClassicalHodgeGeometricCycleClassSpine
open GSTClassicalHodgeLimitlessSpinePropagation
open GSTClassicalHodgeRealizedCorrespondenceExpressionAlgebra
open GSTClassicalHodgeSingleCorrespondenceRankTwo
open GSTClassicalHodgeRankFreeArsenalIrreducibility

namespace GSTMathboxCMGeometricComplexStructure

variable {W : Type*} [AddCommGroup W] [Module ℚ W]

/-- A rational J with J² = -identity forces every nonzero state
to move off its OWN rational line. There are no rational roots of
X²+1; the geometric direction is nonzero without assuming it. -/
theorem complex_structure_moves_nonzero_off_line
    (J : Module.End ℚ W)
    (hJ2 : ∀ z : W, J (J z) = -z)
    (z : W) (hz : z ≠ 0)
    (c : ℚ) (hc : J z = c • z) : False := by
  have hquad : c • (c • z) = -z := by
    calc
      c • (c • z) = c • J z := by rw [hc]
      _ = J (c • z) := by rw [map_smul]
      _ = J (J z) := by rw [hc]
      _ = -z := hJ2 z
  have hzero : (c ^ 2 + 1) • z = 0 := by
    calc
      (c ^ 2 + 1) • z = c • (c • z) + z := by
        simp [add_smul, pow_two, smul_smul]
      _ = -z + z := by rw [hquad]
      _ = 0 := neg_add_cancel z
  have hscalar : (c ^ 2 + 1 : ℚ) = 0 :=
    (smul_eq_zero.mp hzero).resolve_right hz
  nlinarith [sq_nonneg c]

variable {V : SmoothProjectiveComplexScheme}
variable {H : HodgeBigradedBettiData V}
variable {p : Nat}

/-- A truly realized correspondence whose action on the spine is
certified to come from a rational CM complex structure J must move
a nonzero algebraic spine off its own rational line. -/
theorem geometric_CM_action_forces_transversality
    (G : GeometricCycleClassSpine V H)
    (hnz : spineHodgeSeed G p ≠ 0)
    (E : RealizedCorrespondenceExpr V H p)
    (J : Module.End ℚ (ClassicalHodgeFiber V H p))
    (hJ2 : ∀ z : ClassicalHodgeFiber V H p, J (J z) = -z)
    (hgeom : J (spineHodgeSeed G p) = movedSpine G E) :
    ∀ c : ℚ, movedSpine G E ≠ c • spineHodgeSeed G p := by
  intro c hc
  exact complex_structure_moves_nonzero_off_line
    J hJ2 (spineHodgeSeed G p) hnz c (hgeom.trans hc)

/-- An existing genuine rational Hodge-basis coordinate detects ANY
nonzero spine. The required conserved/readout functional is thus
CONSTRUCTED from a true Hodge basis rather than independently assumed. -/
theorem exists_nonzero_spine_readout
    (G : GeometricCycleClassSpine V H)
    (hnz : spineHodgeSeed G p ≠ 0) :
    ∃ ell : ClassicalHodgeFiber V H p →ₗ[ℚ] ℚ,
      ell (spineHodgeSeed G p) ≠ 0 := by
  obtain ⟨i, hi⟩ :=
    exists_nonzero_hodgeCoordinate (V := V) (H := H) (p := p) hnz
  exact ⟨hodgeCoordinate i, hi⟩

/-- GST/CM RANK-TWO GEOMETRIC CLOSURE FROM A QUADRATIC LAW.
No independent nonzero commutator or transverse coordinate input
is needed: J²=-id derives the nonzero direction and the rational
basis provides the charged readout. Every target receives an
explicit genuine rational native algebraic cycle under those
geometric hypotheses. -/
theorem rank_two_hodge_of_actual_CM_complex_structure
    (G : GeometricCycleClassSpine V H)
    (hnz : spineHodgeSeed G p ≠ 0)
    (E : RealizedCorrespondenceExpr V H p)
    (J : Module.End ℚ (ClassicalHodgeFiber V H p))
    (hJ2 : ∀ z : ClassicalHodgeFiber V H p, J (J z) = -z)
    (hgeom : J (spineHodgeSeed G p) = movedSpine G E)
    [FiniteDimensional ℚ (ClassicalHodgeFiber V H p)]
    (hrank : Module.finrank ℚ (ClassicalHodgeFiber V H p) = 2)
    (alpha : RationalSingularCohomology H.analytification (2 * p))
    (halpha : alpha ∈ rationalHodgeSubspace (H.hodgeBigrading p)) :
    ∃ Z : codimensionCycles V.X p, H.cycleClass p Z = alpha := by
  obtain ⟨ell, hlive⟩ := exists_nonzero_spine_readout G hnz
  exact every_rank_two_hodge_class_of_nonproportional_geometric_action
    G ell hlive E
    (geometric_CM_action_forces_transversality G hnz E J hJ2 hgeom)
    hrank alpha halpha

#check complex_structure_moves_nonzero_off_line
#check geometric_CM_action_forces_transversality
#check exists_nonzero_spine_readout
#check rank_two_hodge_of_actual_CM_complex_structure

#print axioms complex_structure_moves_nonzero_off_line
#print axioms geometric_CM_action_forces_transversality
#print axioms exists_nonzero_spine_readout
#print axioms rank_two_hodge_of_actual_CM_complex_structure

end GSTMathboxCMGeometricComplexStructure
