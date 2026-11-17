import GSTClassicalHodgeCrossCarrierGeometricTransfer
import GSTClassicalHodgeGeometricCycleClassPointRigidity
import GSTCompactNativeCyclePresentation

/-!
# Cross-carrier correspondence naturality from actual point incidence

This is the key constructive upgrade beyond an abstract naturality interface.

For a cycle map `N` and Betti map `B` between DIFFERENT smooth projective
varieties, it suffices to prove their commuting square ON EACH ACTUAL
codimension-p irreducible point cycle.  Compact native-cycle presentation
then upgrades that exact point law to full cycle-class naturality, for
every finite rational combination automatically.

The resulting `CrossCarrierTransfer` is a fully constructed object:
- native := the supplied native incidence/correspondence operator;
- betti  := the supplied geometric cohomological action;
- naturality := the theorem proved here FROM the point incidence law.

There is no universal existence claim for either operator.  For an actual
surface switch, Kuga--Satake correspondence or Gale incidence, the substantive
task is to construct these maps and prove its geometric point equation.
This file eliminates the need for a separate global naturality axiom.

NEEDS CI RUN LATER.
-/

set_option maxHeartbeats 18000000
set_option maxRecDepth 800000

noncomputable section

open AlgebraicGeometry
open GSTProjectiveOverC
open GSTGeometricRealizationStage2D
open GSTGeometricRealizationStage2F
open GSTGeometricRealizationStage2G
open GSTNativeCodimensionCyclePresentation
open GSTCompactNativeCyclePresentation
open GSTClassicalHodgeGeometricCycleClassPointRigidity
open GSTClassicalHodgeCrossCarrierGeometricTransfer

namespace GSTClassicalHodgeCrossCarrierPointIncidence

variable {V W : SmoothProjectiveComplexScheme}
variable {H : HodgeBigradedBettiData V}
variable {J : HodgeBigradedBettiData W}
variable {p q : Nat}

/-- Exact geometric incidence law on genuine source codimension-p points.
This equation does not pretend that a Betti action is geometric: the two
operators are separately specified and their pointwise compatibility
must be proved from the chosen correspondence's geometry. -/
def HasCrossCarrierPointIncidence
    (N : codimensionCycles V.X p →ₗ[ℚ] codimensionCycles W.X q)
    (B : RationalSingularCohomology H.analytification (2 * p) →ₗ[ℚ]
      RationalSingularCohomology J.analytification (2 * q)) : Prop :=
  ∀ x : CodimensionPoint V.X p,
    J.cycleClass q (N (codimensionPointCycle V.X p x)) =
      B (H.cycleClass p (codimensionPointCycle V.X p x))

/-- Pointwise incidence on genuine irreducible cycles forces global
naturality of the native and Betti maps on the entire rational cycle space.
The proof is unique linear extension from native point generators. -/
theorem global_naturality_of_point_incidence
    (N : codimensionCycles V.X p →ₗ[ℚ] codimensionCycles W.X q)
    (B : RationalSingularCohomology H.analytification (2 * p) →ₗ[ℚ]
      RationalSingularCohomology J.analytification (2 * q))
    (h : HasCrossCarrierPointIncidence (V := V) (W := W)
      (H := H) (J := J) N B)
    (Z : codimensionCycles V.X p) :
    J.cycleClass q (N Z) = B (H.cycleClass p Z) := by
  have hlinear :
      (J.cycleClass q).comp N =
        B.comp (H.cycleClass p) := by
    apply cycleClass_ext_points (V := V) p
    intro x
    exact h x
  exact congrArg (fun F => F Z) hlinear

/-- Manufacture a REAL multicarrier correspondence from the point incidence
equation: the entire naturality square is now a derived theorem rather
than an independent input field. -/
noncomputable def crossCarrierOfPointIncidence
    (N : codimensionCycles V.X p →ₗ[ℚ] codimensionCycles W.X q)
    (B : RationalSingularCohomology H.analytification (2 * p) →ₗ[ℚ]
      RationalSingularCohomology J.analytification (2 * q))
    (h : HasCrossCarrierPointIncidence (V := V) (W := W)
      (H := H) (J := J) N B) :
    CrossCarrierTransfer V W H J p q where
  native := N
  betti := B
  naturality := global_naturality_of_point_incidence N B h

/-- From ONE geometric point incidence law, every cohomological image of a
source algebraic cycle has an ACTUAL target native-cycle witness. -/
theorem sourceCycle_image_from_point_incidence
    (N : codimensionCycles V.X p →ₗ[ℚ] codimensionCycles W.X q)
    (B : RationalSingularCohomology H.analytification (2 * p) →ₗ[ℚ]
      RationalSingularCohomology J.analytification (2 * q))
    (h : HasCrossCarrierPointIncidence (V := V) (W := W)
      (H := H) (J := J) N B)
    (Z : codimensionCycles V.X p) :
    ∃ targetCycle : codimensionCycles W.X q,
      J.cycleClass q targetCycle = B (H.cycleClass p Z) := by
  exact ⟨N Z, global_naturality_of_point_incidence N B h Z⟩

/-- Geometric incidence and a nonzero rational period construct the normalized
target cycle.  The only geometric assumption is the explicitly stated
pointwise cycle-class law, plus the independent period calculation. -/
theorem normalized_target_from_point_incidence
    (N : codimensionCycles V.X p →ₗ[ℚ] codimensionCycles W.X q)
    (B : RationalSingularCohomology H.analytification (2 * p) →ₗ[ℚ]
      RationalSingularCohomology J.analytification (2 * q))
    (h : HasCrossCarrierPointIncidence (V := V) (W := W)
      (H := H) (J := J) N B)
    (Z : codimensionCycles V.X p)
    (target : GSTClassicalHodgeFiberedCosmology.ClassicalHodgeFiber W J q)
    (k : ℚ) (hk : k ≠ 0)
    (hperiod : B (H.cycleClass p Z) = k • target.1) :
    J.cycleClass q (k⁻¹ • N Z) = target.1 := by
  rw [map_smul, global_naturality_of_point_incidence N B h Z,
    hperiod, smul_smul]
  simp [hk]

#check HasCrossCarrierPointIncidence
#check global_naturality_of_point_incidence
#check crossCarrierOfPointIncidence
#check normalized_target_from_point_incidence
#print axioms normalized_target_from_point_incidence

end GSTClassicalHodgeCrossCarrierPointIncidence
