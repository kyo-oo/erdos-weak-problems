import GSTResearchFiniteWeightGeometricDegree
import GSTResearchUniversalOrbitClosureLaw

/-!
# GST dimension-corrected geometric Hodge synthesis

Final combination of two genuinely geometric laws in the right domain:

1. A dimension-bounded BETTI-DEGREE charge on the genuine native
projective successor tower, proving a nonzero algebraic Hodge seed
at each p<=d. Unlike the raw coefficient-mass bridge, this
charge is assumed to factor through actual cycle class.
2. LOCAL actual-geometric cyclicity for each nonzero native cycle
in the same finite weight range, which forces the explicit orbit
of the constructed spine seed to span its entire Hodge fiber.

Weights p>d must have zero rational Hodge fiber (an explicit
geometric vanishing property). No nonzero source is demanded
outside the geometric dimension. This avoids the old unlimited
mass-bridge inconsistency.

Lean proves the exact all-weight rational Hodge target FROM these
three independent geometric premises, constructing an actual native
representative for every requested class.

Crucial distinction: this theorem does NOT prove that all projective
varieties satisfy the bounded degree and cyclicity premises. Their
uniform independent geometric constructions remain the Hodge task.
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
open GSTClassicalHodgeGeometricMatrixRankLanding
open GSTClassicalHodgeLimitlessSpinePropagation
open GSTResearchFiniteWeightGeometricDegree
open GSTResearchUniversalOrbitClosureLaw

namespace GSTResearchDimensionCorrectedHodgeSynthesis

variable {V : SmoothProjectiveComplexScheme}
variable {H : HodgeBigradedBettiData V}

/-- The actual geometry condition needed for the orbit engine:
every nonzero genuine native algebraic class in the certified
degree range is cyclic under actual Hodge-compatible
finite-closed correspondences. This is local to native classes,
not global irreducibility of the entire rational representation. -/
def NativeGeometricCyclicityInWindow
    (G : GeometricCycleClassSpine V H) (d : Nat) : Prop :=
  ∀ p : Nat, p ≤ d →
    ∀ Z : codimensionCycles V.X p,
      geometricHodgeClass G Z ≠ 0 →
      SeedCyclicForActualGeometry G Z

/-- DIMENSION-CORRECTED HODGE LANDING.
An actual degree-conserving native source and locally cyclic genuine
correspondence actions in every active finite codimension yield
all rational Hodge algebraicity, with no out-of-dimension source
required. The source is built from the projective spine, not
chosen as a preimage of a target class. -/
theorem hodge_of_bounded_degree_and_native_geometric_cyclicity
    (G : GeometricCycleClassSpine V H)
    (d : Nat)
    (D : BoundedGeometricDegreeCharge G d)
    (hvanish : ∀ p : Nat, d < p →
      ∀ a : ClassicalHodgeFiber V H p, a = 0)
    (hcyclic : NativeGeometricCyclicityInWindow G d) :
    BigradedBettiHodgeStatement V H := by
  intro p alpha halpha
  by_cases hp : p ≤ d
  · have hnonzero :
        geometricHodgeClass G (spineNativeTower G p) ≠ 0 := by
      have hEq :
          geometricHodgeClass G (spineNativeTower G p) =
            spineHodgeSeed G p := by
        apply Subtype.ext
        exact spineNativeTower_cycleClass G p
      rw [hEq]
      exact D.hodge_spine_nonzero p hp
    exact hodge_cycles_from_one_geometrically_cyclic_native_seed
      G (spineNativeTower G p)
      (hcyclic p hp (spineNativeTower G p) hnonzero)
      alpha halpha
  · have hpgt : d < p := by omega
    have ha0 : alpha = 0 := by
      have hz := hvanish p hpgt
        (⟨alpha, halpha⟩ : ClassicalHodgeFiber V H p)
      simpa using congrArg Subtype.val hz
    exact ⟨0, by simp [ha0]⟩

#check NativeGeometricCyclicityInWindow
#check hodge_of_bounded_degree_and_native_geometric_cyclicity

#print axioms hodge_of_bounded_degree_and_native_geometric_cyclicity

end GSTResearchDimensionCorrectedHodgeSynthesis
