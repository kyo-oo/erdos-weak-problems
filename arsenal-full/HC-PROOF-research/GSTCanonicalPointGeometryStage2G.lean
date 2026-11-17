import GSTClassicalHodgeGeometricCycleClassPointRigidity
import GSTClassicalHodgeExactClayStatement
import GSTActualXHodgeResidualProjection

/-!
# Stage2G with point-generated geometric cycle classes in EVERY codimension

Construct a unique rational-linear cycleClass across every codimension
from geometric fundamental Betti classes of irreducible subvarieties.

This module builds the algebraic extension and establishes its exact image.
The next geometric integration supplies analytic fundamental classes; the
universal research target establishes their rational Hodge spanning.
-/

set_option maxHeartbeats 10000000
noncomputable section

open AlgebraicGeometry
open GSTProjectiveOverC
open GSTGeometricRealizationStage2D
open GSTGeometricRealizationStage2F
open GSTGeometricRealizationStage2G
open GSTNativeCodimensionCyclePresentation
open GSTClassicalHodgeGeometricCycleClassPointRigidity

namespace GSTCanonicalPointGeometryStage2G

variable {V : SmoothProjectiveComplexScheme}

/-- A coherent family of rational Betti point fundamental classes
in all codimensions on the ORIGINAL variety V. -/
abbrev AllCodimensionPointBettiClasses
    (H : HodgeBigradedBettiData V) : Type :=
  ∀ p : Nat, PointBettiClass (V := V) p H.analytification

/-- Actual all-codimension cycle-class map derived from
irreducible subvariety point data rather than a supplied arbitrary
linear map, determined entirely by point fundamental-class data. -/
noncomputable def pointGeneratedHodgeData
    (H : HodgeBigradedBettiData V)
    (pt : AllCodimensionPointBettiClasses H) :
    HodgeBigradedBettiData V where
  analytification := H.analytification
  hodgeBigrading := H.hodgeBigrading
  cycleClass := fun p =>
    cycleClassFromPointGeometry (V := V) p H.analytification (pt p)

/-- The new geometry-generated cycleClass maps every actual
codimension-p point cycle to its stated Betti fundamental class. -/
theorem pointGeneratedHodgeData_point
    (H : HodgeBigradedBettiData V)
    (pt : AllCodimensionPointBettiClasses H)
    (p : Nat) (x : CodimensionPoint V.X p) :
    (pointGeneratedHodgeData H pt).cycleClass p
      (codimensionPointCycle V.X p x) = pt p x := by
  exact cycleClassFromPointGeometry_point
    (V := V) p H.analytification (pt p) x

/-- The exact range of the derived all-codimension class map
is the rational span of genuine irreducible point fundamental
classes. The next spanning theorem compares this image with the
rational Hodge subspace. -/
theorem pointGeneratedHodgeData_range
    (H : HodgeBigradedBettiData V)
    (pt : AllCodimensionPointBettiClasses H)
    (p : Nat) :
    LinearMap.range ((pointGeneratedHodgeData H pt).cycleClass p) =
      Submodule.span ℚ (Set.range (pt p)) := by
  exact cycleClassFromPointGeometry_range_eq_pointSpan
    (V := V) p H.analytification (pt p)

/-- Pin the classical Hodge conjecture in point-geometric
semantics: the conjecture is exactly the statement that, in
EVERY codimension, the rational Hodge subspace lies in the
span of actual point fundamental classes. The equality is an
exact algebraic reduction used by the universal construction program. -/
theorem pointGeneratedHodgeStatement_iff_actual_point_span
    (H : HodgeBigradedBettiData V)
    (pt : AllCodimensionPointBettiClasses H) :
    BigradedBettiHodgeStatement V (pointGeneratedHodgeData H pt) ↔
      ∀ p : Nat,
        rationalHodgeSubspace (H.hodgeBigrading p) ≤
          Submodule.span ℚ (Set.range (pt p)) := by
  unfold BigradedBettiHodgeStatement
  constructor
  · intro h p
    have hp := h p
    change rationalHodgeSubspace (H.hodgeBigrading p) ≤
      LinearMap.range
        (cycleClassFromPointGeometry (V := V) p H.analytification (pt p)) at hp
    rwa [cycleClassFromPointGeometry_range_eq_pointSpan] at hp
  · intro h p
    change rationalHodgeSubspace (H.hodgeBigrading p) ≤
      LinearMap.range
        (cycleClassFromPointGeometry (V := V) p H.analytification (pt p))
    rw [cycleClassFromPointGeometry_range_eq_pointSpan]
    exact h p

/-! ## Actual-X GST Euler / point-fundamental-class semantic integration

The GST actual-X projector and Euler compiler can now be run with a
cycleClass GENERATED from irreducible point fundamental-class data,
not with a separately unconstrained Stage-2G map.

The first theorem constructs a GENUINE finite rational algebraic
cycle on the original scheme from every prescribed Hodge target.
It computes exactly the residual on the same true Betti carrier;
it does not falsely assert its vanishing.

The second theorem computes the complete point-fundamental-class
expansion of the Euler-certified exact output, provided actual
algebraic source columns have been independently constructed
and their measured determinant proved nonzero.
Neither the point fundamental-class assignment nor the full-rank
source is manufactured by a formal identity: the first is a
separate geometric comparison datum and the latter is the
source-generation problem audited in ActualXHodgeResidualProjection.
-/

open GSTActualXHodgeResidualProjection
open GSTCompactNativeCyclePresentation
open GSTClassicalHodgePointNormalForm

/-- Every point-generated GST projection is literally an original-X
finite rational sum of irreducible-subvariety Betti classes, plus
the exactly measured Hodge residual. No Hodge-to-Chow selector
and no arbitrary unconnected cycleClass map appears here. -/
theorem pointGeneratedNativeProjection_finite_source_and_residual
    (H : HodgeBigradedBettiData V)
    (pt : AllCodimensionPointBettiClasses H)
    (p : Nat)
    {ι : Type*} [Fintype ι] [DecidableEq ι]
    (P : ActualXCycleProjectionData V (pointGeneratedHodgeData H pt) p ι)
    (alpha : HodgeSpace V (pointGeneratedHodgeData H pt) p) :
    ∃ phi : FiniteCodimensionPresentation V.X p,
      phi.sum (fun x q =>
        q • (pointGeneratedHodgeData H pt).cycleClass p
          (codimensionPointCycle V.X p x)) +
        (P.primitiveResidual alpha).1 = alpha.1 := by
  letI : CompactSpace V.X := smoothProjectiveCompactSpace V
  let Z := P.projectNative alpha
  refine ⟨presentationOfNativeCycle V.X p Z, ?_⟩
  have hcycle :=
    linearMap_realizeFiniteCodimensionPresentation V.X p
      ((pointGeneratedHodgeData H pt).cycleClass p)
      (presentationOfNativeCycle V.X p Z)
  have hreal : realizeFiniteCodimensionPresentation V.X p
      (presentationOfNativeCycle V.X p Z) = Z :=
    realize_presentationOfNativeCycle V.X p Z
  rw [hreal] at hcycle
  have hdecomp := P.algebraic_part_plus_residual alpha
  have hvalues := congrArg Subtype.val hdecomp
  change (pointGeneratedHodgeData H pt).cycleClass p Z +
    (P.primitiveResidual alpha).1 = alpha.1 at hvalues
  exact hcycle.symm ▸ hvalues

/-- With an INDEPENDENTLY constructed full-rank family of actual
Chow columns, the same Euler reconstruction gives a finite
original-X scheme-point cycle whose class is the target.
Every point term is forced by pointGeneratedHodgeData_point. -/
theorem pointGeneratedNativeEuler_exact_finite_source
    (H : HodgeBigradedBettiData V)
    (pt : AllCodimensionPointBettiClasses H)
    (p : Nat)
    {ι : Type*} [Fintype ι] [DecidableEq ι]
    (P : ActualXCycleProjectionData V (pointGeneratedHodgeData H pt) p ι)
    {n : Nat}
    (readout : HodgeSpace V (pointGeneratedHodgeData H pt) p ≃ₗ[ℚ]
      (Fin n → ℚ))
    (sources : Fin n → codimensionCycles V.X p)
    (hDet : (P.eulerSourceMatrix readout sources).det ≠ 0)
    (alpha : HodgeSpace V (pointGeneratedHodgeData H pt) p) :
    ∃ phi : FiniteCodimensionPresentation V.X p,
      phi.sum (fun x q =>
        q • (pointGeneratedHodgeData H pt).cycleClass p
          (codimensionPointCycle V.X p x)) = alpha.1 := by
  letI : CompactSpace V.X := smoothProjectiveCompactSpace V
  let Z := P.eulerCertifiedCycle readout sources
    (P.eulerSourceMatrix readout sources)⁻¹ alpha
  refine ⟨presentationOfNativeCycle V.X p Z, ?_⟩
  have hc := P.eulerCertifiedCycle_of_det_ne_zero
    readout sources hDet alpha
  change (pointGeneratedHodgeData H pt).cycleClass p Z = alpha.1 at hc
  have hcycle :=
    linearMap_realizeFiniteCodimensionPresentation V.X p
      ((pointGeneratedHodgeData H pt).cycleClass p)
      (presentationOfNativeCycle V.X p Z)
  have hreal : realizeFiniteCodimensionPresentation V.X p
      (presentationOfNativeCycle V.X p Z) = Z :=
    realize_presentationOfNativeCycle V.X p Z
  rw [hreal] at hcycle
  exact hcycle.symm.trans hc

#check pointGeneratedNativeProjection_finite_source_and_residual
#check pointGeneratedNativeEuler_exact_finite_source
#print axioms pointGeneratedNativeProjection_finite_source_and_residual
#print axioms pointGeneratedNativeEuler_exact_finite_source

#check pointGeneratedHodgeData
#check pointGeneratedHodgeData_point
#check pointGeneratedHodgeData_range
#check pointGeneratedHodgeStatement_iff_actual_point_span
#print axioms pointGeneratedHodgeStatement_iff_actual_point_span

end GSTCanonicalPointGeometryStage2G
