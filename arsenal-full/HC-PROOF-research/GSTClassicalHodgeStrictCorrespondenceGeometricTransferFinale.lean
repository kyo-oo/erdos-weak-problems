import GSTClassicalHodgeAmbientCorrespondenceIncidenceNaturality
import GSTClassicalHodgeGeometricCycleClassPointRigidity
import GSTNativeCodimensionCyclePresentation

/-!
# GST CLASSICAL HODGE — STRICT CORRESPONDENCE GEOMETRIC TRANSFER FINALE

This file removes the last logical circularity between the Stage-2G supplied
cycle-class map and correspondence naturality.

The proof order is now geometry-first:

1. assign the genuine Betti fundamental class `pt x` to every irreducible
   codimension-p point;
2. extend those point classes uniquely to ALL native cycles using the already
   proved compact point normal form (`cycleClassFromPointGeometry`);
3. compute the strict correspondence action by the ambient formula

       T_C(alpha) = p₂_! ( [C] ∪ p₁^* alpha );

4. identify the scheme-theoretic fiber intersection with the native finite
   incidence cycle;
5. only after that calculation, identify the historical Stage-2G supplied
   `H.cycleClass` with the constructed geometric cycle class by point rigidity.

Thus the final commuting square is a theorem, not a field of the geometric
input packet.
-/

set_option maxHeartbeats 100000000
set_option maxRecDepth 1000000

noncomputable section

open CategoryTheory
open AlgebraicGeometry

namespace GSTClassicalHodgeStrictCorrespondenceGeometricTransferFinale

open GSTProjectiveOverC
open GSTGeometricRealizationStage2D
open GSTGeometricRealizationStage2F
open GSTGeometricRealizationStage2G
open GSTNativeCodimensionCyclePresentation
open GSTClassicalHodgeAmbientBettiSelfProduct
open GSTClassicalHodgeAmbientCorrespondenceKernelAction
open GSTClassicalHodgeSchemeFiniteCorrespondenceFirewall
open GSTClassicalHodgeFiniteClosedCorrespondence
open GSTClassicalHodgeFiniteClosedCorrespondenceOperator
open GSTClassicalHodgeGeometricCycleClassPointRigidity

variable {V : SmoothProjectiveComplexScheme}
variable {H : HodgeBigradedBettiData V}
variable {d p : Nat}

abbrev GeometricCycleClass
    (pt : PointBettiClass (V := V) p H.analytification) :=
  cycleClassFromPointGeometry (V := V) p H.analytification pt

/-- The genuinely lower-level scheme/topology calculation, stated without
using the Stage-2G supplied cycle-class map.

The two fields are precisely:
* the class of the scheme-theoretic intersection `C ∩ ({x}×X)`;
* proper projection of that class equals the geometrically generated class of
  the finite residue-degree-weighted incidence cycle.

There is no cohomology endomorphism and no final naturality square here. -/
structure GeometricPointFiberLaw
    (P : AmbientBettiIntersectionCalculus H.analytification d)
    (K : SchemeBiFiniteClosedCorrespondence V)
    (κ : MiddleBettiCorrespondenceKernel H.analytification d K)
    (pt : PointBettiClass (V := V) p H.analytification) where
  fiberIntersectionClass :
    CodimensionPoint V.X p →
      ProductCohomology H.analytification (2 * d + 2 * p)

  kernel_cup_pointFundamental :
    ∀ x : CodimensionPoint V.X p,
      P.cup (2 * d) (2 * p) κ.kernelClass
          (fstCohomologyPullback H.analytification (2 * p) (pt x)) =
        fiberIntersectionClass x

  gysin_fiberIntersection :
    ∀ x : CodimensionPoint V.X p,
      P.sndGysin (2 * p) (fiberIntersectionClass x) =
        GeometricCycleClass (H := H) pt
          (K.toBiFiniteClosedCorrespondence.toFiniteClosedCorrespondence
            |>.nativePointImage p x)

namespace GeometricPointFiberLaw

variable
    {P : AmbientBettiIntersectionCalculus H.analytification d}
    {K : SchemeBiFiniteClosedCorrespondence V}
    {κ : MiddleBettiCorrespondenceKernel H.analytification d K}
    {pt : PointBettiClass (V := V) p H.analytification}

/-- **PURE GEOMETRIC POINT TRANSFER.**
Before referring to the Stage-2G supplied map at all, the ambient kernel action
sends the point fundamental class to the geometrically generated class of the
actual finite incidence image. -/
theorem geometric_action_on_point
    (I : GeometricPointFiberLaw (H := H) (p := p) P K κ pt)
    (x : CodimensionPoint V.X p) :
    κ.action H.analytification P (2 * p) (pt x) =
      GeometricCycleClass (H := H) pt
        (K.toBiFiniteClosedCorrespondence.toFiniteClosedCorrespondence
          |>.nativePointImage p x) := by
  rw [MiddleBettiCorrespondenceKernel.action_apply]
  rw [I.kernel_cup_pointFundamental x]
  exact I.gysin_fiberIntersection x

/-- The geometrically generated cycle class itself satisfies point incidence
naturality. -/
theorem geometric_cycleClass_point_natural
    (I : GeometricPointFiberLaw (H := H) (p := p) P K κ pt)
    (x : CodimensionPoint V.X p) :
    GeometricCycleClass (H := H) pt
        (K.toBiFiniteClosedCorrespondence.toFiniteClosedCorrespondence
          |>.nativePointImage p x) =
      κ.action H.analytification P (2 * p)
        (GeometricCycleClass (H := H) pt
          (codimensionPointCycle V.X p x)) := by
  rw [cycleClassFromPointGeometry_point]
  exact (I.geometric_action_on_point x).symm

/-- **PURE GEOMETRIC GLOBAL TRANSFER LAW.**
Because native cycles are exact finite point sums, the point calculation already
forces naturality on every algebraic cycle. -/
theorem geometric_cycleClass_nativeOperator
    (I : GeometricPointFiberLaw (H := H) (p := p) P K κ pt)
    (Z : codimensionCycles V.X p) :
    GeometricCycleClass (H := H) pt
        (K.toBiFiniteClosedCorrespondence.toFiniteClosedCorrespondence
          |>.nativeOperator p Z) =
      κ.action H.analytification P (2 * p) (GeometricCycleClass (H := H) pt Z) := by
  let clGeo := GeometricCycleClass (H := H) pt
  let F : codimensionCycles V.X p →ₗ[ℚ]
      RationalSingularCohomology H.analytification (2 * p) :=
    clGeo.comp
      (K.toBiFiniteClosedCorrespondence.toFiniteClosedCorrespondence
        |>.nativeOperator p)
      - (κ.action H.analytification P (2 * p)).comp clGeo
  have hF : F = 0 := by
    apply GSTClassicalHodgePointNormalForm.nativeLinearMap_eq_zero_of_points V p
    intro x
    dsimp [F]
    rw [K.toBiFiniteClosedCorrespondence.toFiniteClosedCorrespondence
      |>.nativeOperator_point p x]
    exact sub_eq_zero.mpr (I.geometric_cycleClass_point_natural x)
  have hZ := LinearMap.congr_fun hF Z
  simpa [F, clGeo] using sub_eq_zero.mp hZ

/-- If the historical Stage-2G map has the correct point fundamental classes,
point rigidity identifies it with the constructed geometric cycle class. -/
theorem supplied_cycleClass_eq_geometric
    (hpoint : ∀ x : CodimensionPoint V.X p,
      H.cycleClass p (codimensionPointCycle V.X p x) = pt x) :
    H.cycleClass p = GeometricCycleClass (H := H) pt :=
  GSTClassicalHodgeGeometricCycleClassPointRigidity.suppliedCycleClass_eq_geometric
    (V := V) p H pt hpoint

/-- **FINAL STRICT CORRESPONDENCE TRANSFER LAW.**
The Stage-2G cycle class commutes with the actual strict scheme correspondence,
where the cohomological action is the ambient kernel formula on the ENTIRE
rational singular cohomology carrier. -/
theorem supplied_cycleClass_nativeOperator
    (I : GeometricPointFiberLaw (H := H) (p := p) P K κ pt)
    (hpoint : ∀ x : CodimensionPoint V.X p,
      H.cycleClass p (codimensionPointCycle V.X p x) = pt x)
    (Z : codimensionCycles V.X p) :
    H.cycleClass p
        (K.toBiFiniteClosedCorrespondence.toFiniteClosedCorrespondence
          |>.nativeOperator p Z) =
      κ.action H.analytification P (2 * p) (H.cycleClass p Z) := by
  rw [supplied_cycleClass_eq_geometric hpoint]
  exact I.geometric_cycleClass_nativeOperator Z

/-- The preceding theorem immediately packages into the repository's exact
cycle/cohomology operator-pair interface, with a cohomology operator that was
constructed independently on all Betti classes. -/
noncomputable def suppliedCycleClassOperatorPair
    (I : GeometricPointFiberLaw (H := H) (p := p) P K κ pt)
    (hpoint : ∀ x : CodimensionPoint V.X p,
      H.cycleClass p (codimensionPointCycle V.X p x) = pt x) :=
  K.toBiFiniteClosedCorrespondence.toFiniteClosedCorrespondence
    |>.toCycleClassOperatorPair
      (κ.action H.analytification P (2 * p))
      (by
        intro x
        have hx := I.supplied_cycleClass_nativeOperator hpoint
          (codimensionPointCycle V.X p x)
        rw [K.toBiFiniteClosedCorrespondence.toFiniteClosedCorrespondence
          |>.nativeOperator_point p x] at hx
        exact hx)

#check geometric_action_on_point
#check geometric_cycleClass_nativeOperator
#check supplied_cycleClass_eq_geometric
#check supplied_cycleClass_nativeOperator
#check suppliedCycleClassOperatorPair

#print axioms geometric_cycleClass_nativeOperator
#print axioms supplied_cycleClass_eq_geometric
#print axioms supplied_cycleClass_nativeOperator

end GeometricPointFiberLaw

/-- Simultaneous forward/transpose geometric fiber laws. -/
structure BiGeometricPointFiberLaw
    (P : AmbientBettiIntersectionCalculus H.analytification d)
    (K : SchemeBiFiniteClosedCorrespondence V)
    (κ : MiddleBettiCorrespondenceKernel H.analytification d K)
    (pt : PointBettiClass (V := V) p H.analytification) where
  forward : GeometricPointFiberLaw (H := H) (p := p) P K κ pt
  transpose :
    GeometricPointFiberLaw (H := H) (p := p)
      P K.transpose κ.transposeKernel pt

namespace BiGeometricPointFiberLaw

variable
    {P : AmbientBettiIntersectionCalculus H.analytification d}
    {K : SchemeBiFiniteClosedCorrespondence V}
    {κ : MiddleBettiCorrespondenceKernel H.analytification d K}
    {pt : PointBettiClass (V := V) p H.analytification}

/-- **FORWARD + GENUINE TRANSPOSE FINALE.**
With the actual point fundamental classes identified, both the strict
correspondence and its algebraic factor-swap transpose satisfy the exact global
cycle-class transfer law. -/
theorem supplied_forward_and_transpose_transfer
    (I : BiGeometricPointFiberLaw (H := H) (p := p) P K κ pt)
    (hpoint : ∀ x : CodimensionPoint V.X p,
      H.cycleClass p (codimensionPointCycle V.X p x) = pt x) :
    (∀ Z : codimensionCycles V.X p,
      H.cycleClass p
          (K.toBiFiniteClosedCorrespondence.toFiniteClosedCorrespondence
            |>.nativeOperator p Z) =
        κ.action H.analytification P (2 * p) (H.cycleClass p Z))
    ∧
    (∀ Z : codimensionCycles V.X p,
      H.cycleClass p
          (K.transpose.toBiFiniteClosedCorrespondence.toFiniteClosedCorrespondence
            |>.nativeOperator p Z) =
        κ.transposeKernel.action H.analytification P (2 * p) (H.cycleClass p Z)) := by
  constructor
  · exact I.forward.supplied_cycleClass_nativeOperator hpoint
  · exact I.transpose.supplied_cycleClass_nativeOperator hpoint

/-- The transpose operator in the finale is the actual factor-swapped
projective-incidence formula. -/
theorem transpose_is_factor_swap_incidence
    (I : BiGeometricPointFiberLaw (H := H) (p := p) P K κ pt)
    (alpha : RationalSingularCohomology H.analytification (2 * p)) :
    κ.transposeKernel.action H.analytification P (2 * p) alpha =
      P.fstGysin (2 * p)
        (P.cup (2 * d) (2 * p) κ.kernelClass
          (sndCohomologyPullback H.analytification (2 * p) alpha)) := by
  exact κ.transpose_action_apply H.analytification P (2 * p) alpha

#check supplied_forward_and_transpose_transfer
#check transpose_is_factor_swap_incidence

#print axioms supplied_forward_and_transpose_transfer
#print axioms transpose_is_factor_swap_incidence

end BiGeometricPointFiberLaw

end GSTClassicalHodgeStrictCorrespondenceGeometricTransferFinale
