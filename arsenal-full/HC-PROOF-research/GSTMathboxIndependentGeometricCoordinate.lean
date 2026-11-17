import GSTClassicalHodgeSingleCorrespondenceRankTwo
import GSTClassicalHodgeGeometricMatrixRankLanding

/-!
# Mathbox GST: the THIRD INDEPENDENT GEOMETRIC COORDINATE

Interpret the user's (a*x^4)_3 and (b*y^4)_3 as the THIRD
INDEPENDENT GEOMETRIC COORDINATE (third axis, index 2 of Fin 3).
Do NOT treat the subscript 3 as a base-three digit, a derivative,
or an arbitrary unrelated scalar.

The formal mathematical content has two levels:

(1) Geometry of coordinates: the third readout kills the first TWO
coordinate axes, and detects the independent third axis. We rewrite
the photographed 99*x radical using the actual coordinate-3 projection
and derive the exact nonvanishing criterion for its real domain.

(2) True native algebraic geometry: if a rational cohomological
coordinate functional kills EVERY old native cycle class and detects
a newly constructed native cycle class, that actual cycle lies outside
the span of all old classes. The proof works for arbitrarily many
old directions, without dimension or rank cutoffs. The new cycle can
be any output of the true geometric correspondence-cycle operator.

The novel universal existence claim - a geometric construction of such
a detected new cycle for EVERY missing Hodge direction - is NOT
smuggled in as a new law/axiom. It remains a distinct target.
-/

set_option maxHeartbeats 20000000

noncomputable section

open scoped BigOperators
open AlgebraicGeometry
open GSTProjectiveOverC
open GSTGeometricRealizationStage2D
open GSTGeometricRealizationStage2F
open GSTGeometricRealizationStage2G
open GSTClassicalHodgeFiberedCosmology
open GSTClassicalHodgeGeometricCycleClassSpine
open GSTClassicalHodgeLimitlessSpinePropagation
open GSTClassicalHodgeGeometricMatrixRankLanding
open GSTClassicalHodgeSingleCorrespondenceRankTwo
open GSTClassicalHodgeRealizedCorrespondenceExpressionAlgebra

namespace GSTMathboxIndependentGeometricCoordinate

/-- Third independent coordinate of a genuine THREE-coordinate vector.
Lean Fin indices 0,1,2 correspond to geometric coordinates 1,2,3. -/
def coordinate3 (v : Fin 3 → ℝ) : ℝ := v 2

/-- The third coordinate as a rational linear functional. -/
def thirdCoordinateRead : (Fin 3 → ℚ) →ₗ[ℚ] ℚ where
  toFun v := v 2
  map_add' := by intros; rfl
  map_smul' := by intros; rfl

/-- Exact GST x^4 operation on the THIRD geometric axis. -/
def thirdPowerCoordinate (a : ℝ) (v : Fin 3 → ℝ) : ℝ :=
  a * (coordinate3 v) ^ 4

/-- Literal index-3 numerator of the photographed GST law. -/
def thirdGeometricNumerator (a b : ℝ)
    (x y : Fin 3 → ℝ) : ℝ :=
  thirdPowerCoordinate a x - thirdPowerCoordinate b y

/-- The photographed equation with index 3 interpreted correctly. -/
noncomputable def independentThirdConversion
    (factor a b psi xi : ℝ) (x y : Fin 3 → ℝ) : ℝ :=
  99 * factor * Real.sqrt
    (thirdGeometricNumerator a b x y / (psi ^ 2 * xi))

/-- The radical is squared on the exact geometric third-coordinate
numerator. Nothing from coordinates 1 or 2 was silently substituted. -/
theorem independentThirdConversion_sq
    (factor a b psi xi : ℝ) (x y : Fin 3 → ℝ)
    (h : 0 ≤ thirdGeometricNumerator a b x y / (psi ^ 2 * xi)) :
    independentThirdConversion factor a b psi xi x y ^ 2 =
      ((99 : ℝ) * factor) ^ 2 *
        (thirdGeometricNumerator a b x y / (psi ^ 2 * xi)) := by
  unfold independentThirdConversion
  rw [mul_pow, Real.sq_sqrt h]

/-- A nonzero third-coordinate differential makes the EXACT radical
nonzero provided its real radicand is positive and the prefactor lives. -/
theorem independentThirdConversion_ne_zero
    (factor a b psi xi : ℝ) (x y : Fin 3 → ℝ)
    (hfactor : factor ≠ 0)
    (hrad : 0 < thirdGeometricNumerator a b x y / (psi ^ 2 * xi)) :
    independentThirdConversion factor a b psi xi x y ≠ 0 := by
  unfold independentThirdConversion
  exact mul_ne_zero
    (mul_ne_zero (by norm_num : (99 : ℝ) ≠ 0) hfactor)
    (ne_of_gt (Real.sqrt_pos.2 hrad))

/-- The third coordinate of geometric axis 3 is nonzero. -/
theorem coordinate3_detects_axis3 :
    thirdCoordinateRead (fun i : Fin 3 => if i = 2 then 1 else 0) = 1 := by
  simp [thirdCoordinateRead]

/-- The third coordinate vanishes on geometric axis 1. -/
theorem coordinate3_kills_axis1 :
    thirdCoordinateRead (fun i : Fin 3 => if i = 0 then 1 else 0) = 0 := by
  simp [thirdCoordinateRead]

/-- The third coordinate vanishes on geometric axis 2. -/
theorem coordinate3_kills_axis2 :
    thirdCoordinateRead (fun i : Fin 3 => if i = 1 then 1 else 0) = 0 := by
  simp [thirdCoordinateRead]

/-- An independent third geometric axis cannot be obtained as a linear
combination of the first two axes. This proves independent-coordinates
semantics, rather than merely naming a third scalar. -/
theorem independent_geometric_third_axis
    (a b : ℚ) :
    (fun i : Fin 3 => if i = 2 then (1 : ℚ) else 0) ≠
      a • (fun i : Fin 3 => if i = 0 then (1 : ℚ) else 0) +
      b • (fun i : Fin 3 => if i = 1 then (1 : ℚ) else 0) := by
  intro h
  have hc := congrArg (fun v : Fin 3 → ℚ => v 2) h
  have hfalse : (1 : ℚ) = 0 := by simpa using hc
  norm_num at hfalse

variable {V : SmoothProjectiveComplexScheme}
variable {H : HodgeBigradedBettiData V}
variable {p : Nat}
variable {ι : Type*}

/-- THE ARBITRARY-RANK GEOMETRIC EXTENSION LEMMA.
An independent geometric coordinate that vanishes on every old
ACTUAL NATIVE algebraic cycle class but detects a new ACTUAL
NATIVE algebraic cycle class proves the new direction is not in
the old class-span. No restriction to rank 2 or to a specific basis. -/
theorem detected_native_cycle_outside_old_span
    (G : GeometricCycleClassSpine V H)
    (old : ι → codimensionCycles V.X p)
    (fresh : codimensionCycles V.X p)
    (thirdRead : ClassicalHodgeFiber V H p →ₗ[ℚ] ℚ)
    (hOld : ∀ i : ι,
      thirdRead (geometricHodgeClass G (old i)) = 0)
    (hFresh : thirdRead (geometricHodgeClass G fresh) ≠ 0) :
    geometricHodgeClass G fresh ∉
      Submodule.span ℚ
        (Set.range (fun i : ι => geometricHodgeClass G (old i))) := by
  intro hspan
  have hker :
      Submodule.span ℚ
        (Set.range (fun i : ι => geometricHodgeClass G (old i))) ≤
      LinearMap.ker thirdRead := by
    apply Submodule.span_le.mpr
    rintro x ⟨i, rfl⟩
    exact LinearMap.mem_ker.mpr (hOld i)
  exact hFresh (LinearMap.mem_ker.mp (hker hspan))


/-- An independently DETECTED genuine cycle causes a STRICT increase
in the actual algebraic Hodge span, at any finite or infinite source-index
type. No Hodge witness is chosen as a premise: the inputs are old native
cycles, a newly constructed native cycle, and the checked rational period. -/
theorem detected_native_cycle_strict_rank_gain
    (G : GeometricCycleClassSpine V H)
    (old : ι → codimensionCycles V.X p)
    (fresh : codimensionCycles V.X p)
    (readout : ClassicalHodgeFiber V H p →ₗ[ℚ] ℚ)
    (hOld : ∀ i : ι,
      readout (geometricHodgeClass G (old i)) = 0)
    (hFresh : readout (geometricHodgeClass G fresh) ≠ 0) :
    Submodule.span ℚ
        (Set.range (fun i : ι => geometricHodgeClass G (old i))) <
      Submodule.span ℚ
        (Set.insert (geometricHodgeClass G fresh)
          (Set.range (fun i : ι => geometricHodgeClass G (old i)))) := by
  apply lt_of_le_of_ne
  · exact Submodule.span_mono (Set.subset_insert _ _)
  · intro heq
    have hnew :
        geometricHodgeClass G fresh ∈
          Submodule.span ℚ
            (Set.insert (geometricHodgeClass G fresh)
              (Set.range (fun i : ι => geometricHodgeClass G (old i)))) :=
      Submodule.subset_span (Set.mem_insert _ _)
    rw [← heq] at hnew
    exact detected_native_cycle_outside_old_span
      G old fresh readout hOld hFresh hnew

#print axioms detected_native_cycle_strict_rank_gain

/-- Stronger GST interpretation of the user-created third coordinate:
for a genuine REALIZED correspondence E, the actual native image of the
projective spine supplies a new independent algebraic Hodge direction
whenever the third geometric coordinate reads zero on the previous
native cycles and nonzero on this explicitly generated output.

The readout property needs a mathematical geometric construction;
it is NOT an axiom or an assumed algebraic preimage of an arbitrary
target Hodge class. -/
theorem realized_correspondence_fresh_native_direction
    (G : GeometricCycleClassSpine V H)
    (old : ι → codimensionCycles V.X p)
    (E : RealizedCorrespondenceExpr V H p)
    (thirdRead : ClassicalHodgeFiber V H p →ₗ[ℚ] ℚ)
    (hOld : ∀ i : ι,
      thirdRead (geometricHodgeClass G (old i)) = 0)
    (hFresh :
      thirdRead
        (geometricHodgeClass G
          (E.cycleOperator (spineNativeTower G p))) ≠ 0) :
    geometricHodgeClass G
        (E.cycleOperator (spineNativeTower G p)) ∉
      Submodule.span ℚ
        (Set.range (fun i : ι => geometricHodgeClass G (old i))) :=
  detected_native_cycle_outside_old_span G old
    (E.cycleOperator (spineNativeTower G p)) thirdRead hOld hFresh

/-! ## Numerical third-coordinate detector wired to ACTUAL native cycles

This is the direct mathematical bridge from the user's photographed
99*x sqrt((a*x^4)_3-(b*y^4)_3) expression to the newly proved
arbitrary-rank native-cycle extension theorem. The bridge is valid
for genuine rational-cycle classes, and can take any number of old
directions. The needed numerical/geometric correspondence equality
remains an independently checkable construction obligation. -/

/-- A nonzero value of the literal photographed radical proves that
the *third-coordinate geometric numerator itself* is nonzero.
No positivity/denominator hypothesis is silently inferred in reverse. -/
theorem nonzero_conversion_forces_third_numerator
    (factor a b psi xi : ℝ) (x y : Fin 3 → ℝ)
    (h : independentThirdConversion factor a b psi xi x y ≠ 0) :
    thirdGeometricNumerator a b x y ≠ 0 := by
  intro hzero
  apply h
  simp [independentThirdConversion, hzero]

/-- Concrete, rank-unrestricted GST conversion-to-geometry theorem:
if the index-3 real expression is nonzero and its numerator is ACTUALLY
the real image of a rational geometric coordinate applied to the
cohomology class of a native correspondence output, that output lies
outside the span of every old genuine native class.

This proves exactly the mathematical implication missing from the
handwritten formula. The identity hGeom is a geometric comparison
equation that must be proved from the scheme's correspondence geometry;
it is not a target-cycle preimage or an arbitrary assumed Hodge
surjectivity statement. -/
theorem photographed_third_coordinate_certifies_fresh_native_cycle
    (G : GeometricCycleClassSpine V H)
    (old : ι → codimensionCycles V.X p)
    (E : RealizedCorrespondenceExpr V H p)
    (thirdRead : ClassicalHodgeFiber V H p →ₗ[ℚ] ℚ)
    (hOld : ∀ i : ι,
      thirdRead (geometricHodgeClass G (old i)) = 0)
    (factor a b psi xi : ℝ)
    (x y : Fin 3 → ℝ)
    (hConversion :
      independentThirdConversion factor a b psi xi x y ≠ 0)
    (hGeom :
      ((thirdRead
        (geometricHodgeClass G
          (E.cycleOperator (spineNativeTower G p))) : ℚ) : ℝ) =
        thirdGeometricNumerator a b x y) :
    geometricHodgeClass G
        (E.cycleOperator (spineNativeTower G p)) ∉
      Submodule.span ℚ
        (Set.range (fun i : ι => geometricHodgeClass G (old i))) := by
  have hNumerator :
      thirdGeometricNumerator a b x y ≠ 0 :=
    nonzero_conversion_forces_third_numerator
      factor a b psi xi x y hConversion
  have hFresh :
      thirdRead
        (geometricHodgeClass G
          (E.cycleOperator (spineNativeTower G p))) ≠ 0 := by
    intro hz
    apply hNumerator
    calc
      thirdGeometricNumerator a b x y =
          ((thirdRead
            (geometricHodgeClass G
              (E.cycleOperator (spineNativeTower G p))) : ℚ) : ℝ) :=
        hGeom.symm
      _ = 0 := by simp [hz]
  exact realized_correspondence_fresh_native_direction
    G old E thirdRead hOld hFresh

#check coordinate3
#check thirdCoordinateRead
#check independentThirdConversion_sq
#check independentThirdConversion_ne_zero
#check coordinate3_detects_axis3
#check coordinate3_kills_axis1
#check coordinate3_kills_axis2
#check independent_geometric_third_axis
#check detected_native_cycle_outside_old_span
#check realized_correspondence_fresh_native_direction
#check nonzero_conversion_forces_third_numerator
#check photographed_third_coordinate_certifies_fresh_native_cycle

#print axioms independent_geometric_third_axis
#print axioms detected_native_cycle_outside_old_span
#print axioms realized_correspondence_fresh_native_direction
#print axioms photographed_third_coordinate_certifies_fresh_native_cycle

end GSTMathboxIndependentGeometricCoordinate
