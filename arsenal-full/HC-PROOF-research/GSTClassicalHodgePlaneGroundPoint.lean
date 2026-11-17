import GSTClassicalHodgeGeometricCycleClassPointRigidity
import GSTClassicalHodgePlaneSemanticIndependence
import GSTClassicalHodgeStrictPlaneCircularityAudit
import GSTClassicalHodgeStrictGraphBettiTrace

/-!
# GST CLASSICAL HODGE — THE PLANE GROUND POINT

This file fixes the endpoint of the GST-plane audit.

There are no more anonymous "plane completeness" assumptions to descend into.
The intrinsic GST plane is already a theorem.  Mechanical strict-graph trace
and injectivity are constructed from geometry.  Ghost-adaptive plane packages
are conclusion-equivalent and therefore barred as premises.

The only semantic datum not determined by the intrinsic GST plane is the
Stage-2G cycle-class map itself.  The compact native-cycle normal form proves
that this datum has an exact generator presentation: linear cycle-class maps
and assignments of Betti classes to genuine codimension-p points are mutually
inverse descriptions of the same object.

Therefore a point assignment is NOT an additional completeness axiom.  It is
exactly the coordinate presentation of the Stage-2G semantic map.  If a
geometric point assignment is independently constructed, the only semantic
identification needed is generatorwise equality with that assignment; compact
normal form then forces the entire map.  Conversely full map equality forces
those point equations.

The zero-cycle-class counterworld proves that bare intrinsic GST plane algebra
cannot choose the geometric semantic coordinate: it keeps the full unbounded
plane while violating every nonzero geometric point assignment.
-/

set_option maxHeartbeats 180000000
set_option maxRecDepth 1000000

noncomputable section

open AlgebraicGeometry

namespace GSTClassicalHodgePlaneGroundPoint

open GSTProjectiveOverC
open GSTGeometricRealizationStage2G
open GSTClassicalHodgeGeometricCycleClassPointRigidity
open GSTClassicalHodgeStage2GSemanticRigidity
open GSTClassicalHodgePlaneSemanticIndependence
open GSTClassicalHodgeStrictPlaneCircularityAudit
open GSTClassicalHodgeGeometricCycleClassSpine
open GSTClassicalHodgeCommonClassPlaneRealization
open GSTClassicalHodgeOmniversalGhostPlaneStrike

variable {V : SmoothProjectiveComplexScheme}

/-- Read a linear native cycle-class map only on the genuine codimension-p
point generators.  This is canonical and contains no extra choice. -/
noncomputable def pointAssignmentOfCycleClass
    (p : Nat)
    (A : AnalytificationData V)
    (F : codimensionCycles V.X p →ₗ[ℚ]
      RationalSingularCohomology A (2 * p)) :
    PointBettiClass (V := V) p A :=
  fun x => F (codimensionPointCycle V.X p x)

/-- Extending the point values of an arbitrary linear cycle-class map through
the exact compact native-cycle presentation reconstructs the original map.
There is no semantic information away from the point generators. -/
theorem cycleClassFromPointGeometry_pointAssignment
    (p : Nat)
    (A : AnalytificationData V)
    (F : codimensionCycles V.X p →ₗ[ℚ]
      RationalSingularCohomology A (2 * p)) :
    cycleClassFromPointGeometry (V := V) p A
      (pointAssignmentOfCycleClass (V := V) p A F) = F := by
  apply cycleClass_ext_points (V := V) p
  intro x
  simp [pointAssignmentOfCycleClass]

/-- Conversely, reading the point values of a map generated from point geometry
returns the original point assignment exactly. -/
theorem pointAssignment_cycleClassFromPointGeometry
    (p : Nat)
    (A : AnalytificationData V)
    (pt : PointBettiClass (V := V) p A) :
    pointAssignmentOfCycleClass (V := V) p A
      (cycleClassFromPointGeometry (V := V) p A pt) = pt := by
  funext x
  simp [pointAssignmentOfCycleClass]

/-- **SEMANTIC PARAMETERIZATION THEOREM.**
For compact smooth-projective GST native cycles, a point-class assignment and
a rational linear cycle-class map are EXACTLY equivalent data.  This is the
stable semantic ground: there is no hidden larger cycle-class compatibility
package above or below it. -/
noncomputable def pointGeometryCycleClassEquiv
    (p : Nat)
    (A : AnalytificationData V) :
    PointBettiClass (V := V) p A ≃
      (codimensionCycles V.X p →ₗ[ℚ]
        RationalSingularCohomology A (2 * p)) where
  toFun := cycleClassFromPointGeometry (V := V) p A
  invFun := pointAssignmentOfCycleClass (V := V) p A
  left_inv := pointAssignment_cycleClassFromPointGeometry (V := V) p A
  right_inv := cycleClassFromPointGeometry_pointAssignment (V := V) p A

/-- The point-extension construction is injective: two different point
assignments cannot secretly define the same global semantic map. -/
theorem cycleClassFromPointGeometry_injective
    (p : Nat)
    (A : AnalytificationData V) :
    Function.Injective
      (cycleClassFromPointGeometry (V := V) p A) := by
  intro pt₁ pt₂ h
  have h' := congrArg
    (pointAssignmentOfCycleClass (V := V) p A) h
  simpa [pointAssignment_cycleClassFromPointGeometry] using h'

/-- Reading point coordinates is also injective on linear cycle maps because
the compact point presentation has no invisible directions. -/
theorem pointAssignmentOfCycleClass_injective
    (p : Nat)
    (A : AnalytificationData V) :
    Function.Injective
      (pointAssignmentOfCycleClass (V := V) p A) := by
  intro F G h
  calc
    F = cycleClassFromPointGeometry (V := V) p A
        (pointAssignmentOfCycleClass (V := V) p A F) :=
      (cycleClassFromPointGeometry_pointAssignment (V := V) p A F).symm
    _ = cycleClassFromPointGeometry (V := V) p A
        (pointAssignmentOfCycleClass (V := V) p A G) := by rw [h]
    _ = G := cycleClassFromPointGeometry_pointAssignment (V := V) p A G

/-- Every Stage-2G cycle-class map is unconditionally reconstructed from its own
point coordinates.  This theorem uses no geometric correctness assumption. -/
theorem stage2G_cycleClass_reconstructs_from_own_points
    (H : HodgeBigradedBettiData V)
    (p : Nat) :
    cycleClassFromPointGeometry (V := V) p H.analytification
      (pointAssignmentOfCycleClass (V := V) p H.analytification
        (H.cycleClass p)) = H.cycleClass p :=
  cycleClassFromPointGeometry_pointAssignment
    (V := V) p H.analytification (H.cycleClass p)

/-- **THE EXACT GEOMETRIC SEMANTIC GROUND.**
No global surjectivity or Hodge conclusion occurs here.  This says only that a
genuine codimension-p point cycle lands on the independently specified
geometric Betti class assigned to that same point. -/
def PointSemanticGround
    (H : HodgeBigradedBettiData V)
    (p : Nat)
    (pt : PointBettiClass (V := V) p H.analytification) : Prop :=
  ∀ x : CodimensionPoint V.X p,
    H.cycleClass p (codimensionPointCycle V.X p x) = pt x

/-- The semantic ground is simply equality between the Stage-2G map's canonical
point coordinates and the independently specified geometric coordinates. -/
theorem pointSemanticGround_iff_pointAssignment_eq
    (H : HodgeBigradedBettiData V)
    (p : Nat)
    (pt : PointBettiClass (V := V) p H.analytification) :
    PointSemanticGround H p pt ↔
      pointAssignmentOfCycleClass (V := V) p H.analytification
        (H.cycleClass p) = pt := by
  constructor
  · intro h
    funext x
    exact h x
  · intro h x
    exact congrFun h x

/-- **GROUND-POINT EXACTNESS.**
The local point law is equivalent to equality of the ENTIRE Stage-2G cycle
class map with the map generated from point geometry.  Hence no further
cycle-class compatibility law can appear later without being redundant. -/
theorem pointSemanticGround_iff_full_geometric_cycleClass
    (H : HodgeBigradedBettiData V)
    (p : Nat)
    (pt : PointBettiClass (V := V) p H.analytification) :
    PointSemanticGround H p pt ↔
      H.cycleClass p =
        cycleClassFromPointGeometry (V := V) p H.analytification pt := by
  constructor
  · intro hground
    exact suppliedCycleClass_eq_geometric (V := V) p H pt hground
  · intro hmap x
    rw [hmap]
    exact cycleClassFromPointGeometry_point
      (V := V) p H.analytification pt x

/-- The local ground has a unique global extension.  This is the formal reason
that no second independent semantic bridge can legitimately be introduced
above it. -/
theorem pointSemanticGround_unique_extension
    (H : HodgeBigradedBettiData V)
    (p : Nat)
    (pt : PointBettiClass (V := V) p H.analytification)
    (F : codimensionCycles V.X p →ₗ[ℚ]
      RationalSingularCohomology H.analytification (2 * p))
    (hF : ∀ x : CodimensionPoint V.X p,
      F (codimensionPointCycle V.X p x) = pt x) :
    F = cycleClassFromPointGeometry (V := V) p H.analytification pt := by
  apply cycleClass_ext_points (V := V) p
  intro x
  rw [hF x]
  exact (cycleClassFromPointGeometry_point
    (V := V) p H.analytification pt x).symm

/-- Point-ground equality is therefore extensional: any two linear cycle-class
realizations with the same genuine point values are identical everywhere. -/
theorem cycleClass_realizations_unique_from_ground
    (H : HodgeBigradedBettiData V)
    (p : Nat)
    (pt : PointBettiClass (V := V) p H.analytification)
    (F G : codimensionCycles V.X p →ₗ[ℚ]
      RationalSingularCohomology H.analytification (2 * p))
    (hF : ∀ x : CodimensionPoint V.X p,
      F (codimensionPointCycle V.X p x) = pt x)
    (hG : ∀ x : CodimensionPoint V.X p,
      G (codimensionPointCycle V.X p x) = pt x) :
    F = G := by
  exact cycleClass_ext_points (V := V) p F G (fun x => (hF x).trans (hG x).symm)

/-- **ZERO-WORLD EXCLUSION AT ONE POINT.**
If even one geometric point class is nonzero, the arbitrary zero-cycle-class
copy of Stage 2G cannot satisfy the semantic ground. -/
theorem zeroCycleClass_violates_nonzero_point_ground
    (H : HodgeBigradedBettiData V)
    (p : Nat)
    (pt : PointBettiClass (V := V) p H.analytification)
    (x : CodimensionPoint V.X p)
    (hx : pt x ≠ 0) :
    ¬ PointSemanticGround (zeroCycleClassData H) p pt := by
  intro hground
  have hz := hground x
  have hz' : (0 : RationalSingularCohomology H.analytification (2 * p)) = pt x := by
    simpa [zeroCycleClassData] using hz
  exact hx hz'.symm

/-- **FULL INTRINSIC PLANE DOES NOT SYNTHESIZE SEMANTIC GROUND.**
The same explicit zero-cycle world simultaneously has a live fixed-source GST
plane and violates any nonzero geometric point assignment.  This prevents a
future proof from silently replacing semantic geometry by stronger intrinsic
plane algebra. -/
theorem full_GST_plane_can_coexist_with_ground_failure
    (H : HodgeBigradedBettiData V)
    (p : Nat)
    (alpha : ClassicalHodgeFiber V H p)
    (halpha : alpha ≠ 0)
    (pt : PointBettiClass (V := V) p H.analytification)
    (x : CodimensionPoint V.X p)
    (hx : pt x ≠ 0) :
    (Nonempty
      { i : HodgeSupportIndex (zeroCycleClassHodgeState H alpha) //
        hodgeCoordinate i.1 (zeroCycleClassHodgeState H alpha) ≠ 0 })
      ∧ ¬ PointSemanticGround (zeroCycleClassData H) p pt := by
  constructor
  · obtain ⟨i, hi, _hevent, _hreach, _htower, _hL2, _hcollapse⟩ :=
      zeroCycleClass_full_GST_plane H alpha halpha
    exact ⟨⟨i, hi⟩⟩
  · exact zeroCycleClass_violates_nonzero_point_ground H p pt x hx

/-- **NO CONCLUSION-SHAPED PLANE PREMISE.**
The two historical ghost-adaptive plane packages are exactly Hodge itself, so
neither belongs below the ground point. -/
theorem ghostAdaptive_plane_packages_are_not_ground_axioms
    {H : HodgeBigradedBettiData V}
    (G : GeometricCycleClassSpine V H) :
    (GhostAdaptiveStrictPlaneCompleteness G ↔
      BigradedBettiHodgeStatement V H)
      ∧
    (GhostAdaptiveCommonClassPlaneCompleteness G ↔
      BigradedBettiHodgeStatement V H) :=
  all_ghostAdaptive_plane_packages_iff_hodge G

/-- **GROUND-POINT ENDPOINT.**
For a fixed geometric point assignment, the local semantic law, the complete
cycle-class equality, and uniqueness of the global extension are one and the
same mathematical datum.  Together with `pointGeometryCycleClassEquiv`, this
closes the semantic descent: intrinsic plane algebra is theorem-level;
mechanical graph trace is constructed; ghost-adaptive completeness is circular;
and raw Stage 2G semantic freedom is exactly, and only, its point coordinates. -/
theorem plane_ground_point_endpoint
    (H : HodgeBigradedBettiData V)
    (p : Nat)
    (pt : PointBettiClass (V := V) p H.analytification) :
    PointSemanticGround H p pt ↔
      H.cycleClass p =
        cycleClassFromPointGeometry (V := V) p H.analytification pt :=
  pointSemanticGround_iff_full_geometric_cycleClass H p pt

#check pointAssignmentOfCycleClass
#check cycleClassFromPointGeometry_pointAssignment
#check pointAssignment_cycleClassFromPointGeometry
#check pointGeometryCycleClassEquiv
#check cycleClassFromPointGeometry_injective
#check pointAssignmentOfCycleClass_injective
#check stage2G_cycleClass_reconstructs_from_own_points
#check PointSemanticGround
#check pointSemanticGround_iff_pointAssignment_eq
#check pointSemanticGround_iff_full_geometric_cycleClass
#check pointSemanticGround_unique_extension
#check cycleClass_realizations_unique_from_ground
#check zeroCycleClass_violates_nonzero_point_ground
#check full_GST_plane_can_coexist_with_ground_failure
#check ghostAdaptive_plane_packages_are_not_ground_axioms
#check plane_ground_point_endpoint

#print axioms cycleClassFromPointGeometry_pointAssignment
#print axioms pointAssignment_cycleClassFromPointGeometry
#print axioms pointGeometryCycleClassEquiv
#print axioms stage2G_cycleClass_reconstructs_from_own_points
#print axioms pointSemanticGround_iff_pointAssignment_eq
#print axioms pointSemanticGround_iff_full_geometric_cycleClass
#print axioms pointSemanticGround_unique_extension
#print axioms zeroCycleClass_violates_nonzero_point_ground
#print axioms full_GST_plane_can_coexist_with_ground_failure
#print axioms ghostAdaptive_plane_packages_are_not_ground_axioms
#print axioms plane_ground_point_endpoint

end GSTClassicalHodgePlaneGroundPoint
