import GSTUniversalCodimensionTwoPrimitiveExtraction

/-!
# GST genuine primitive cycle extraction from non-Lefschetz algebraic geometry

The existing all-dimensional codimension-two theorem constructs a
primitive remainder of an arbitrary rational Hodge class and the
native codimension-two cycle realizing its nonprimitive correction.

This module closes a mathematical weakness in that formulation:
real Hard Lefschetz is an ISOMORPHISM, but the earlier structural
interface demanded only surjectivity. Adding its standard
injectivity gives a canonical primitive projector:
  P(alpha) = alpha - h cup (L^(d-2))^(-1)(L^(d-3) alpha).

PROVEN NEW THEOREM: for any actual native algebraic codimension-two
cycle Z, its corrected native cycle P_native(Z) is a NONZERO
ALGEBRAIC PRIMITIVE class if and only if cl(Z) lies outside
the h-cup image of rational Hodge divisors.

This produces nonzero algebraic primitive classes from explicit
geometric incidence cycles *without assuming any primitive
class is already algebraic*. It does not imply that ALL primitive
rational Hodge classes are represented by such Z. The latter
universal surjectivity remains the Hodge conjecture problem.
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
open GSTUniversalLefschetzCurveCycles
open GSTUniversalCodimensionTwoPrimitiveExtraction

namespace GSTPrimitiveTransverseCycleExtraction

variable {V : SmoothProjectiveComplexScheme}
variable {H : HodgeBigradedBettiData V}
variable {d : Nat}

/-- The algebraic correction always belongs to the genuine
hyperplane-times-divisor Hodge image, with its exact Lefschetz
test value prescribed by alpha. -/
theorem correction_is_cup_of_real_divisor
    (G : GeometricCycleClassSpine V H)
    (P : GeometricHigherLefschetzData G d)
    (h11 : DivisorsRepresentHodge11 H)
    (alpha : ClassicalHodgeFiber V H 2) :
    ∃ beta : ClassicalHodgeFiber V H 1,
      nativeToHodgeFiberLinear G
        (algebraicLefschetzCorrection G P h11 alpha) =
        P.cupH beta ∧
      P.cupH2 beta = P.primitiveTest alpha := by
  let beta : ClassicalHodgeFiber V H 1 :=
    Classical.choose (P.hardLefschetz (P.primitiveTest alpha))
  let D : codimensionCycles V.X 1 :=
    Classical.choose (h11 beta)
  have hD : nativeToHodgeFiberLinear G D = beta := by
    apply Subtype.ext
    exact Classical.choose_spec (h11 beta)
  refine ⟨beta, ?_, Classical.choose_spec (P.hardLefschetz (P.primitiveTest alpha))⟩
  change nativeToHodgeFiberLinear G (P.nativeCupH D) = P.cupH beta
  rw [P.nativeNaturality D, hD]

/-- Hard Lefschetz INJECTIVITY forces the primitive projection to
vanish on EVERY h-times-divisor Hodge class. The previous data
required only surjectivity, which was not enough for this fact. -/
theorem primitive_remainder_vanishes_on_cupH
    (G : GeometricCycleClassSpine V H)
    (P : GeometricHigherLefschetzData G d)
    (h11 : DivisorsRepresentHodge11 H)
    (hInject : Function.Injective P.cupH2)
    (beta : ClassicalHodgeFiber V H 1) :
    primitiveHodgeRemainder G P h11 (P.cupH beta) = 0 := by
  obtain ⟨gamma, hc, hg⟩ :=
    correction_is_cup_of_real_divisor G P h11 (P.cupH beta)
  have heq : gamma = beta := by
    apply hInject
    calc
      P.cupH2 gamma = P.primitiveTest (P.cupH beta) := hg
      _ = P.cupH2 beta := P.twoStepCompatibility beta
  unfold primitiveHodgeRemainder
  rw [hc, heq]
  exact sub_self _

/-- Exact equality between the true rational Hodge primitive
projection and the class of the native algebraic corrected cycle. -/
theorem native_primitive_projection_cycleClass
    (G : GeometricCycleClassSpine V H)
    (P : GeometricHigherLefschetzData G d)
    (h11 : DivisorsRepresentHodge11 H)
    (Z : codimensionCycles V.X 2) :
    nativeToHodgeFiberLinear G
      (primitiveizeNativeMiddleCycle G P h11 Z) =
      primitiveHodgeRemainder G P h11
        (nativeToHodgeFiberLinear G Z) := by
  simp [primitiveizeNativeMiddleCycle, primitiveHodgeRemainder, map_sub]

/-- A truly primitive rational class from a native algebraic cycle
is NONZERO exactly when the original cycle is not in the
divisor-times-ample subspace. This detects genuine geometric
primitive directions, not just a nonzero zeta/CM scalar. -/
theorem native_primitive_nonzero_iff_outside_divisor_cup
    (G : GeometricCycleClassSpine V H)
    (P : GeometricHigherLefschetzData G d)
    (h11 : DivisorsRepresentHodge11 H)
    (hInject : Function.Injective P.cupH2)
    (Z : codimensionCycles V.X 2) :
    (nativeToHodgeFiberLinear G
      (primitiveizeNativeMiddleCycle G P h11 Z) ≠ 0) ↔
      (∀ beta : ClassicalHodgeFiber V H 1,
        nativeToHodgeFiberLinear G Z ≠ P.cupH beta) := by
  rw [native_primitive_projection_cycleClass]
  constructor
  · intro hnonzero beta hZ
    rw [hZ] at hnonzero
    exact hnonzero
      (primitive_remainder_vanishes_on_cupH G P h11 hInject beta)
  · intro houtside hzero
    obtain ⟨beta, hc, _⟩ :=
      correction_is_cup_of_real_divisor G P h11
        (nativeToHodgeFiberLinear G Z)
    have hZ : nativeToHodgeFiberLinear G Z = P.cupH beta := by
      have heq :
          nativeToHodgeFiberLinear G Z =
          nativeToHodgeFiberLinear G
            (algebraicLefschetzCorrection G P h11
              (nativeToHodgeFiberLinear G Z)) := by
        exact sub_eq_zero.mp hzero
      exact heq.trans hc
    exact houtside beta hZ

/-- A TRUE new construction: given an actual codimension-two
algebraic cycle with an independently testable class outside
h times divisors, return an actual nonzero primitive algebraic
cycle. Its Hodge class is forced to be primitive by geometry,
and forced nonzero by Hard Lefschetz injectivity. No algebraic
preimage of an arbitrary primitive target class is assumed. -/
theorem exists_actual_nonzero_algebraic_primitive_of_transverse_cycle
    (G : GeometricCycleClassSpine V H)
    (P : GeometricHigherLefschetzData G d)
    (h11 : DivisorsRepresentHodge11 H)
    (hInject : Function.Injective P.cupH2)
    (Z : codimensionCycles V.X 2)
    (houtside : ∀ beta : ClassicalHodgeFiber V H 1,
      nativeToHodgeFiberLinear G Z ≠ P.cupH beta) :
    ∃ W : codimensionCycles V.X 2,
      nativeToHodgeFiberLinear G W ≠ 0 ∧
      P.primitiveTest (nativeToHodgeFiberLinear G W) = 0 := by
  refine ⟨primitiveizeNativeMiddleCycle G P h11 Z, ?_, ?_⟩
  · exact (native_primitive_nonzero_iff_outside_divisor_cup
        G P h11 hInject Z).2 houtside
  · exact primitiveizeNativeMiddleCycle_primitive G P h11 Z

/-- A certified rational period or intersection measurement that
vanishes on EVERY hyperplane-times-divisor class is conserved by
the actual primitive-cycle correction.

This provides an exact interface for the GST CM/NM programme:
construct ONE true geometrically defined measurement of a
genuine codimension-two native algebraic cycle, prove it is zero
on the Lefschetz divisor image and nonzero on that actual cycle.
The already-built native primitive projection will then output
a nonzero primitive algebraic class while preserving its detected
measurement. No arbitrary primitive target preimage is inserted. -/
theorem geometrically_measured_native_primitive_cycle
    (G : GeometricCycleClassSpine V H)
    (P : GeometricHigherLefschetzData G d)
    (h11 : DivisorsRepresentHodge11 H)
    (hInject : Function.Injective P.cupH2)
    (measure : ClassicalHodgeFiber V H 2 →ₗ[ℚ] ℚ)
    (annihilatesLefschetz :
      ∀ beta : ClassicalHodgeFiber V H 1,
        measure (P.cupH beta) = 0)
    (Z : codimensionCycles V.X 2)
    (hnonzero : measure (nativeToHodgeFiberLinear G Z) ≠ 0) :
    ∃ W : codimensionCycles V.X 2,
      nativeToHodgeFiberLinear G W ≠ 0 ∧
      P.primitiveTest (nativeToHodgeFiberLinear G W) = 0 ∧
      measure (nativeToHodgeFiberLinear G W) =
        measure (nativeToHodgeFiberLinear G Z) := by
  have houtside : ∀ beta : ClassicalHodgeFiber V H 1,
      nativeToHodgeFiberLinear G Z ≠ P.cupH beta := by
    intro beta hEq
    apply hnonzero
    rw [hEq]
    exact annihilatesLefschetz beta
  refine ⟨primitiveizeNativeMiddleCycle G P h11 Z, ?_, ?_, ?_⟩
  · exact (native_primitive_nonzero_iff_outside_divisor_cup
        G P h11 hInject Z).2 houtside
  · exact primitiveizeNativeMiddleCycle_primitive G P h11 Z
  · rw [native_primitive_projection_cycleClass]
    change measure
      (nativeToHodgeFiberLinear G Z -
        nativeToHodgeFiberLinear G
          (algebraicLefschetzCorrection G P h11
            (nativeToHodgeFiberLinear G Z))) =
        measure (nativeToHodgeFiberLinear G Z)
    rw [map_sub]
    obtain ⟨beta, hCorr, _⟩ :=
      correction_is_cup_of_real_divisor G P h11
        (nativeToHodgeFiberLinear G Z)
    rw [hCorr, annihilatesLefschetz beta]
    exact sub_zero _

/-- The resulting projection onto the primitive part is IDEMPOTENT
once genuine Hard Lefschetz is an isomorphism, rather than merely
surjective. Thus the correction cannot keep changing an already
primitive class under repeated application. -/
theorem geometric_primitive_projection_idempotent
    (G : GeometricCycleClassSpine V H)
    (P : GeometricHigherLefschetzData G d)
    (h11 : DivisorsRepresentHodge11 H)
    (hInject : Function.Injective P.cupH2)
    (alpha : ClassicalHodgeFiber V H 2) :
    primitiveHodgeRemainder G P h11
      (primitiveHodgeRemainder G P h11 alpha) =
        primitiveHodgeRemainder G P h11 alpha := by
  let a := primitiveHodgeRemainder G P h11 alpha
  have ha : P.primitiveTest a = 0 :=
    primitiveHodgeRemainder_primitive G P h11 alpha
  obtain ⟨beta,hCorr,hbeta⟩ :=
    correction_is_cup_of_real_divisor G P h11 a
  have hzero : beta = 0 := by
    apply hInject
    rw [hbeta,ha]
    exact (map_zero P.cupH2).symm
  change a - nativeToHodgeFiberLinear G
    (algebraicLefschetzCorrection G P h11 a) = a
  rw [hCorr,hzero]
  simp


/-! ## GST all-center rational-blowup PRIMITIVE native cycle birth

The exact actual blowup cohomology formula for Y=Bl_X(P^N) at
codimension two gives the independent sectors
  (ambient hyperplane squared, first exceptional center divisor,
   second exceptional fundamental class)
whenever X is positive-dimensional and center codimension >= 3.

For a rational ample polarization L=A-t*E with t != 0, the
cup-product image of a rational divisor x*A+y*E has coordinates
  (x, y-t*x, -t*y).
The native first exceptional class A*E has coordinates (0,1,0).
The equations x=0 and -t*y=0 force y=0, contradicting
its middle coordinate 1. Therefore this actual algebraic
cycle lies STRICTLY outside the Lefschetz divisor image.

The earlier GST primitive projection then constructs an ACTUAL
NONZERO rational algebraic PRIMITIVE codimension-two cycle
on the rational blowup for every such smooth center X.

The geometric coordinate-readout packet below must be realized
by the true projective blowup Chow/Betti decomposition. The
Lean result does NOT claim the theorem for a freely chosen
zero cycle-class map or manufacture the cohomology splitting.
-/

/-- Scheme-native exceptional codimension-two cycle, with
independently geometric three-sector Hodge coordinate readouts
and the exact polarized hyperplane cup law. These conditions
are cohomological and do NOT assert the primitive conclusion. -/
structure GenuineBlowupThreeSectorPrimitivePacket
    (G : GeometricCycleClassSpine V H)
    (P : GeometricHigherLefschetzData G d) where
  exceptionalNative : codimensionCycles V.X 2
  polarizationSlope : ℚ
  slope_ne_zero : polarizationSlope ≠ 0
  ambientCoordinate : ClassicalHodgeFiber V H 2 →ₗ[ℚ] ℚ
  firstExceptionalCoordinate : ClassicalHodgeFiber V H 2 →ₗ[ℚ] ℚ
  secondExceptionalCoordinate : ClassicalHodgeFiber V H 2 →ₗ[ℚ] ℚ
  exceptional_ambient_zero :
    ambientCoordinate (nativeToHodgeFiberLinear G exceptionalNative) = 0
  exceptional_first_one :
    firstExceptionalCoordinate
      (nativeToHodgeFiberLinear G exceptionalNative) = 1
  exceptional_second_zero :
    secondExceptionalCoordinate
      (nativeToHodgeFiberLinear G exceptionalNative) = 0
  divisor_cup_coordinates :
    ∀ beta : ClassicalHodgeFiber V H 1,
      ∃ x y : ℚ,
        ambientCoordinate (P.cupH beta) = x ∧
        firstExceptionalCoordinate (P.cupH beta) =
          y - polarizationSlope*x ∧
        secondExceptionalCoordinate (P.cupH beta) =
          -polarizationSlope*y

/-- EXACT three-coordinate calculation: the native first
exceptional algebraic cycle is transverse to ALL hyperplane
times divisor classes, without assuming target primitive
surjectivity, CM eigendata, or any target cycle preimage. -/
theorem blowup_exceptional_cycle_transverse_to_divisor_cup
    (G : GeometricCycleClassSpine V H)
    (P : GeometricHigherLefschetzData G d)
    (B : GenuineBlowupThreeSectorPrimitivePacket G P) :
    ∀ beta : ClassicalHodgeFiber V H 1,
      nativeToHodgeFiberLinear G B.exceptionalNative ≠
        P.cupH beta := by
  intro beta hEq
  obtain ⟨x, y, hx, hmiddle, hlast⟩ :=
    B.divisor_cup_coordinates beta
  have hx0 : x = 0 := by
    calc
      x = B.ambientCoordinate (P.cupH beta) := hx.symm
      _ = B.ambientCoordinate
          (nativeToHodgeFiberLinear G B.exceptionalNative) := by
            rw [← hEq]
      _ = 0 := B.exceptional_ambient_zero
  have hty : -B.polarizationSlope*y = 0 := by
    calc
      -B.polarizationSlope*y =
          B.secondExceptionalCoordinate (P.cupH beta) := hlast.symm
      _ = B.secondExceptionalCoordinate
          (nativeToHodgeFiberLinear G B.exceptionalNative) := by
            rw [← hEq]
      _ = 0 := B.exceptional_second_zero
  have hy0 : y = 0 := by
    have hmul : B.polarizationSlope * y = 0 := by
      linarith
    exact (mul_eq_zero.mp hmul).resolve_left B.slope_ne_zero
  have hmiddleEq : (1 : ℚ) = y - B.polarizationSlope*x := by
    calc
      1 = B.firstExceptionalCoordinate
          (nativeToHodgeFiberLinear G B.exceptionalNative) :=
            B.exceptional_first_one.symm
      _ = B.firstExceptionalCoordinate (P.cupH beta) := by
            rw [hEq]
      _ = y - B.polarizationSlope*x := hmiddle
  simp [hx0,hy0] at hmiddleEq

/-- Construct a genuine NEW primitive rational algebraic
codimension-two cycle from the first exceptional divisor
direction for an arbitrary smooth center satisfying the
standard, independently certified three-sector blowup geometry.
The cycle is provably NONZERO and primitive, not just a
nonzero Hodge cohomology vector. -/
theorem actual_nonzero_primitive_cycle_of_three_sector_blowup
    (G : GeometricCycleClassSpine V H)
    (P : GeometricHigherLefschetzData G d)
    (h11 : DivisorsRepresentHodge11 H)
    (hInject : Function.Injective P.cupH2)
    (B : GenuineBlowupThreeSectorPrimitivePacket G P) :
    ∃ W : codimensionCycles V.X 2,
      nativeToHodgeFiberLinear G W ≠ 0 ∧
      P.primitiveTest (nativeToHodgeFiberLinear G W) = 0 := by
  exact exists_actual_nonzero_algebraic_primitive_of_transverse_cycle
    G P h11 hInject B.exceptionalNative
      (blowup_exceptional_cycle_transverse_to_divisor_cup G P B)


/-! ## All-rank native exceptional Picard-to-primitive construction

The earlier theorem provided ONE nonzero primitive native cycle. This
strengthening works with an arbitrary rational VECTOR SPACE D of
genuine center divisor classes, of unrestricted rank.

The independent cohomological readouts of a true smooth-center
projective blowup have:
* ambient coordinate of the first exceptional native cycle = 0;
* exceptional center divisor coordinate = the original D-vector;
* second exceptional coordinate = 0.
The whole hyperplane-times-divisor subspace has only ambient and
exceptional divisor parameters x,y. Nonzero exceptional slope t
forces these parameters to vanish if their ambient and second
coordinates vanish. Consequently NO nonzero D-vector from the
first exceptional sector can lie in that Lefschetz cup image.

This is a direct, actual native-cycle construction, not a choice of
an arbitrary primitive Hodge representative. It leaves separately
visible the true scheme blowup/Betti splitting and ample polarizing
cup formulas that must realize the packet.
-/

/-- All-rank geometric three-sector blowup with actual rational
center divisor module D; the output is the genuine Mathlib-native
codimension-two algebraic cycle carrier on the host V. -/
structure GenuineBlowupPicardPrimitivePacket
    (G : GeometricCycleClassSpine V H)
    (P : GeometricHigherLefschetzData G d)
    (D : Type*) [AddCommGroup D] [Module ℚ D] where
  nativeFirstExceptional : D →ₗ[ℚ] codimensionCycles V.X 2
  polarizationSlope : ℚ
  slope_ne_zero : polarizationSlope ≠ 0
  centerHyperplane : D
  centerNormal : D
  ambientReadout : ClassicalHodgeFiber V H 2 →ₗ[ℚ] ℚ
  centerReadout : ClassicalHodgeFiber V H 2 →ₗ[ℚ] D
  secondReadout : ClassicalHodgeFiber V H 2 →ₗ[ℚ] ℚ
  exceptional_ambient_zero : ∀ a : D,
    ambientReadout
      (nativeToHodgeFiberLinear G (nativeFirstExceptional a)) = 0
  exceptional_center_exact : ∀ a : D,
    centerReadout
      (nativeToHodgeFiberLinear G (nativeFirstExceptional a)) = a
  exceptional_second_zero : ∀ a : D,
    secondReadout
      (nativeToHodgeFiberLinear G (nativeFirstExceptional a)) = 0
  divisor_cup_coordinates :
    ∀ beta : ClassicalHodgeFiber V H 1,
      ∃ x y : ℚ,
        ambientReadout (P.cupH beta) = x ∧
        centerReadout (P.cupH beta) =
          (y - polarizationSlope * x) • centerHyperplane +
            y • centerNormal ∧
        secondReadout (P.cupH beta) = -polarizationSlope * y

/-- A true all-rank first-exceptional divisor direction can be
contained in the host's Lefschetz divisor image ONLY IF THE
CENTER DIVISOR DIRECTION IS ZERO. This controls every direction
at once, rather than one lucky ample class. -/
theorem exceptional_picard_class_in_Lefschetz_forces_zero
    {D : Type*} [AddCommGroup D] [Module ℚ D]
    (G : GeometricCycleClassSpine V H)
    (P : GeometricHigherLefschetzData G d)
    (B : GenuineBlowupPicardPrimitivePacket G P D)
    (a : D) (beta : ClassicalHodgeFiber V H 1)
    (hEq : nativeToHodgeFiberLinear G
      (B.nativeFirstExceptional a) = P.cupH beta) :
    a = 0 := by
  obtain ⟨x, y, hx, hcenter, hsecond⟩ :=
    B.divisor_cup_coordinates beta
  have hx0 : x = 0 := by
    calc
      x = B.ambientReadout (P.cupH beta) := hx.symm
      _ = B.ambientReadout
        (nativeToHodgeFiberLinear G (B.nativeFirstExceptional a)) := by
          rw [hEq]
      _ = 0 := B.exceptional_ambient_zero a
  have hty : -B.polarizationSlope * y = 0 := by
    calc
      -B.polarizationSlope * y = B.secondReadout (P.cupH beta) :=
        hsecond.symm
      _ = B.secondReadout
        (nativeToHodgeFiberLinear G (B.nativeFirstExceptional a)) := by
          rw [hEq]
      _ = 0 := B.exceptional_second_zero a
  have hy0 : y = 0 := by
    have hmul : B.polarizationSlope * y = 0 := by linarith
    exact (mul_eq_zero.mp hmul).resolve_left B.slope_ne_zero
  calc
    a = B.centerReadout
      (nativeToHodgeFiberLinear G (B.nativeFirstExceptional a)) :=
        (B.exceptional_center_exact a).symm
    _ = B.centerReadout (P.cupH beta) := by rw [hEq]
    _ = (y - B.polarizationSlope * x) • B.centerHyperplane +
      y • B.centerNormal := hcenter
    _ = 0 := by simp [hx0, hy0]

/-- For EVERY nonzero genuine rational center divisor class, a
nonzero, genuine native algebraic PRIMITIVE codimension-two cycle
is explicitly constructed by GST's native Lefschetz correction.
There is no center Hodge conjecture hypothesis above degree one. -/
theorem nonzero_primitive_cycle_of_any_center_divisor
    {D : Type*} [AddCommGroup D] [Module ℚ D]
    (G : GeometricCycleClassSpine V H)
    (P : GeometricHigherLefschetzData G d)
    (h11 : DivisorsRepresentHodge11 H)
    (hInject : Function.Injective P.cupH2)
    (B : GenuineBlowupPicardPrimitivePacket G P D)
    (a : D) (ha : a ≠ 0) :
    ∃ W : codimensionCycles V.X 2,
      nativeToHodgeFiberLinear G W ≠ 0 ∧
      P.primitiveTest (nativeToHodgeFiberLinear G W) = 0 := by
  apply exists_actual_nonzero_algebraic_primitive_of_transverse_cycle
    G P h11 hInject (B.nativeFirstExceptional a)
  intro beta hEq
  exact ha
    (exceptional_picard_class_in_Lefschetz_forces_zero
      G P B a beta hEq)


/-- Distinct rational center divisor vectors construct DISTINCT
primitive Hodge classes on the rational host. Equal primitive
projections would force their difference into the Lefschetz cup
image, contrary to the exact geometric three-sector readout
unless the two divisor vectors were identical. All center ranks
are permitted and no target primitive surjectivity is assumed. -/
theorem primitive_center_divisor_directions_are_distinct
    {D : Type*} [AddCommGroup D] [Module ℚ D]
    (G : GeometricCycleClassSpine V H)
    (P : GeometricHigherLefschetzData G d)
    (h11 : DivisorsRepresentHodge11 H)
    (B : GenuineBlowupPicardPrimitivePacket G P D)
    (a b : D)
    (hEqual :
      nativeToHodgeFiberLinear G
        (primitiveizeNativeMiddleCycle G P h11
          (B.nativeFirstExceptional a)) =
      nativeToHodgeFiberLinear G
        (primitiveizeNativeMiddleCycle G P h11
          (B.nativeFirstExceptional b))) :
    a = b := by
  let A : ClassicalHodgeFiber V H 2 :=
    nativeToHodgeFiberLinear G (B.nativeFirstExceptional a)
  let C : ClassicalHodgeFiber V H 2 :=
    nativeToHodgeFiberLinear G (B.nativeFirstExceptional b)
  obtain ⟨betaA, hCorrA, _⟩ :=
    correction_is_cup_of_real_divisor G P h11 A
  obtain ⟨betaC, hCorrC, _⟩ :=
    correction_is_cup_of_real_divisor G P h11 C
  have hProjection : A - P.cupH betaA = C - P.cupH betaC := by
    have hh := hEqual
    rw [native_primitive_projection_cycleClass G P h11
          (B.nativeFirstExceptional a),
        native_primitive_projection_cycleClass G P h11
          (B.nativeFirstExceptional b)] at hh
    change A - nativeToHodgeFiberLinear G
        (algebraicLefschetzCorrection G P h11 A) =
      C - nativeToHodgeFiberLinear G
        (algebraicLefschetzCorrection G P h11 C) at hh
    simpa only [hCorrA, hCorrC] using hh
  have hDifference : A - C = P.cupH (betaA - betaC) := by
    calc
      A - C =
          (A - P.cupH betaA) - (C - P.cupH betaC) +
            (P.cupH betaA - P.cupH betaC) := by abel
      _ = P.cupH betaA - P.cupH betaC := by
            rw [hProjection]
            simp
      _ = P.cupH (betaA - betaC) := by rw [map_sub]
  have hNativeDifference :
      nativeToHodgeFiberLinear G
        (B.nativeFirstExceptional (a - b)) =
          P.cupH (betaA - betaC) := by
    calc
      _ = A - C := by simp [A, C, map_sub]
      _ = P.cupH (betaA - betaC) := hDifference
  have hZero : a - b = 0 :=
    exceptional_picard_class_in_Lefschetz_forces_zero
      G P B (a - b) (betaA - betaC) hNativeDifference
  exact sub_eq_zero.mp hZero


/-! ## GST primitive projection is a RATIONAL LINEAR MAP

The previous primitive correction used a noncomputable choice of
Hard Lefschetz inverse and a divisor lifting. Because the Hard
Lefschetz map is injective as well as surjective, the CORRECTED
HODGE CLASS is independent of those choices and is fully linear.
Proving this closes the remaining rank issue: an injective
construction of primitive classes is now an actual linear
embedding of the entire rational center Picard space, not merely
a set-theoretic injection or finitely many sample cycles.
-/

/-- Exact additivity of the previously defined primitive Hodge
remainder, obtained from the uniqueness of the Hard Lefschetz
inverse rather than a presumed linear choice of Chow lifts. -/
theorem primitive_hodge_remainder_add
    (G : GeometricCycleClassSpine V H)
    (P : GeometricHigherLefschetzData G d)
    (h11 : DivisorsRepresentHodge11 H)
    (hInject : Function.Injective P.cupH2)
    (alpha gamma : ClassicalHodgeFiber V H 2) :
    primitiveHodgeRemainder G P h11 (alpha + gamma) =
      primitiveHodgeRemainder G P h11 alpha +
        primitiveHodgeRemainder G P h11 gamma := by
  obtain ⟨u, hu, htu⟩ :=
    correction_is_cup_of_real_divisor G P h11 (alpha + gamma)
  obtain ⟨v, hv, htv⟩ :=
    correction_is_cup_of_real_divisor G P h11 alpha
  obtain ⟨w, hw, htw⟩ :=
    correction_is_cup_of_real_divisor G P h11 gamma
  have hSum : u = v + w := by
    apply hInject
    calc
      P.cupH2 u = P.primitiveTest (alpha + gamma) := htu
      _ = P.primitiveTest alpha + P.primitiveTest gamma := by
            rw [map_add]
      _ = P.cupH2 v + P.cupH2 w := by rw [htv, htw]
      _ = P.cupH2 (v + w) := by rw [map_add]
  unfold primitiveHodgeRemainder
  rw [hu, hv, hw, hSum, map_add]
  abel

/-- Exact rational scalar compatibility of the canonical Hodge
primitive projection. No scalar-linear Chow section is required. -/
theorem primitive_hodge_remainder_smul
    (G : GeometricCycleClassSpine V H)
    (P : GeometricHigherLefschetzData G d)
    (h11 : DivisorsRepresentHodge11 H)
    (hInject : Function.Injective P.cupH2)
    (a : ℚ) (alpha : ClassicalHodgeFiber V H 2) :
    primitiveHodgeRemainder G P h11 (a • alpha) =
      a • primitiveHodgeRemainder G P h11 alpha := by
  obtain ⟨u, hu, htu⟩ :=
    correction_is_cup_of_real_divisor G P h11 (a • alpha)
  obtain ⟨v, hv, htv⟩ :=
    correction_is_cup_of_real_divisor G P h11 alpha
  have hScalar : u = a • v := by
    apply hInject
    calc
      P.cupH2 u = P.primitiveTest (a • alpha) := htu
      _ = a • P.primitiveTest alpha := by rw [map_smul]
      _ = a • P.cupH2 v := by rw [htv]
      _ = P.cupH2 (a • v) := by rw [map_smul]
  unfold primitiveHodgeRemainder
  rw [hu, hv, hScalar, map_smul]
  simp only [smul_sub]

/-- The canonical native GST primitive Hodge projection, now a
genuine ℚ-linear operator despite its originally noncomputable
native Chow-level choice. -/
noncomputable def primitiveHodgeProjectionLinear
    (G : GeometricCycleClassSpine V H)
    (P : GeometricHigherLefschetzData G d)
    (h11 : DivisorsRepresentHodge11 H)
    (hInject : Function.Injective P.cupH2) :
    ClassicalHodgeFiber V H 2 →ₗ[ℚ]
      ClassicalHodgeFiber V H 2 where
  toFun := primitiveHodgeRemainder G P h11
  map_add' := by
    intro a b
    exact primitive_hodge_remainder_add G P h11 hInject a b
  map_smul' := by
    intro a x
    exact primitive_hodge_remainder_smul G P h11 hInject a x

/-- GENUINE LINEAR embedding of the rational center divisor
directions into the rational primitive Hodge classes represented
by native algebraic cycles on a rational blowup host. -/
noncomputable def picardToNativePrimitiveLinear
    {D : Type*} [AddCommGroup D] [Module ℚ D]
    (G : GeometricCycleClassSpine V H)
    (P : GeometricHigherLefschetzData G d)
    (h11 : DivisorsRepresentHodge11 H)
    (hInject : Function.Injective P.cupH2)
    (B : GenuineBlowupPicardPrimitivePacket G P D) :
    D →ₗ[ℚ] ClassicalHodgeFiber V H 2 :=
  (primitiveHodgeProjectionLinear G P h11 hInject).comp
    ((nativeToHodgeFiberLinear G).comp B.nativeFirstExceptional)

/-- FULL RANK: this map is a linear INJECTION, not merely a
different primitive cycle for each individually selected divisor.
Its image consists of actual algebraic primitive Hodge classes,
so the center's entire Picard rank survives as genuine primitive
algebraic directions on the rational blowup host. -/
theorem picardToNativePrimitiveLinear_injective
    {D : Type*} [AddCommGroup D] [Module ℚ D]
    (G : GeometricCycleClassSpine V H)
    (P : GeometricHigherLefschetzData G d)
    (h11 : DivisorsRepresentHodge11 H)
    (hInject : Function.Injective P.cupH2)
    (B : GenuineBlowupPicardPrimitivePacket G P D) :
    Function.Injective (picardToNativePrimitiveLinear G P h11 hInject B) := by
  intro a b hab
  have hProj :
      primitiveHodgeRemainder G P h11
        (nativeToHodgeFiberLinear G (B.nativeFirstExceptional a)) =
      primitiveHodgeRemainder G P h11
        (nativeToHodgeFiberLinear G (B.nativeFirstExceptional b)) := by
    change primitiveHodgeRemainder G P h11
      (nativeToHodgeFiberLinear G (B.nativeFirstExceptional a)) =
      primitiveHodgeRemainder G P h11
      (nativeToHodgeFiberLinear G (B.nativeFirstExceptional b)) at hab
    exact hab
  apply primitive_center_divisor_directions_are_distinct G P h11 B a b
  calc
    nativeToHodgeFiberLinear G
      (primitiveizeNativeMiddleCycle G P h11
        (B.nativeFirstExceptional a)) =
        primitiveHodgeRemainder G P h11
          (nativeToHodgeFiberLinear G
            (B.nativeFirstExceptional a)) :=
          native_primitive_projection_cycleClass G P h11
            (B.nativeFirstExceptional a)
    _ = primitiveHodgeRemainder G P h11
      (nativeToHodgeFiberLinear G
        (B.nativeFirstExceptional b)) := hProj
    _ = nativeToHodgeFiberLinear G
      (primitiveizeNativeMiddleCycle G P h11
        (B.nativeFirstExceptional b)) :=
          (native_primitive_projection_cycleClass G P h11
            (B.nativeFirstExceptional b)).symm

#check primitiveHodgeProjectionLinear

/-! ## Genuine primitive-kernel target, not merely ambient Hodge

The injection above lands in the ACTUAL kernel of the geometric
primitiveTest operator. The refined codomain is a rational
submodule of the genuine Hodge fiber on the smooth projective
blowup host. Every image class is represented by the already
constructed native primitive Chow cycle; no primitive target
preimage is assumed.
-/

/-- Inject the WHOLE rational center Picard module into the
geometric PRIMITIVE rational Hodge subspace, not just full Hdg². -/
noncomputable def picardToNativePrimitiveKernelLinear
    {D : Type*} [AddCommGroup D] [Module ℚ D]
    (G : GeometricCycleClassSpine V H)
    (P : GeometricHigherLefschetzData G d)
    (h11 : DivisorsRepresentHodge11 H)
    (hInject : Function.Injective P.cupH2)
    (B : GenuineBlowupPicardPrimitivePacket G P D) :
    D →ₗ[ℚ] LinearMap.ker P.primitiveTest :=
  (picardToNativePrimitiveLinear G P h11 hInject B).codRestrict
    (LinearMap.ker P.primitiveTest) (by
      intro a
      apply LinearMap.mem_ker.mpr
      change P.primitiveTest
        (primitiveHodgeRemainder G P h11
          (nativeToHodgeFiberLinear G
            (B.nativeFirstExceptional a))) = 0
      exact primitiveHodgeRemainder_primitive G P h11
        (nativeToHodgeFiberLinear G
          (B.nativeFirstExceptional a)))

/-- Native geometric primitive-cycle ranks are preserved:
the Picard-module embedding into the primitive KERNEL is
injective in ALL ranks and all ambient dimensions admitting
the genuine projective blowup and Hard Lefschetz certificates. -/
theorem picardToNativePrimitiveKernelLinear_injective
    {D : Type*} [AddCommGroup D] [Module ℚ D]
    (G : GeometricCycleClassSpine V H)
    (P : GeometricHigherLefschetzData G d)
    (h11 : DivisorsRepresentHodge11 H)
    (hInject : Function.Injective P.cupH2)
    (B : GenuineBlowupPicardPrimitivePacket G P D) :
    Function.Injective
      (picardToNativePrimitiveKernelLinear G P h11 hInject B) := by
  intro a b h
  apply picardToNativePrimitiveLinear_injective G P h11 hInject B
  have hv := congrArg Subtype.val h
  exact hv


/-- EXPLICIT geometric witness for EVERY vector in the Picard-rank
primitive kernel embedding. In addition to proving that the map
is injective, this theorem returns an ACTUAL native rational
codimension-two Chow cycle whose cohomology class is exactly
the embedded primitive vector. This makes its image a genuine
algebraic primitive subspace, not only an abstract Hodge one. -/
theorem every_picard_primitive_vector_has_native_chow_cycle
    {D : Type*} [AddCommGroup D] [Module ℚ D]
    (G : GeometricCycleClassSpine V H)
    (P : GeometricHigherLefschetzData G d)
    (h11 : DivisorsRepresentHodge11 H)
    (hInject : Function.Injective P.cupH2)
    (B : GenuineBlowupPicardPrimitivePacket G P D)
    (a : D) :
    ∃ W : codimensionCycles V.X 2,
      nativeToHodgeFiberLinear G W =
        (picardToNativePrimitiveKernelLinear
          G P h11 hInject B a).val ∧
      P.primitiveTest (nativeToHodgeFiberLinear G W) = 0 := by
  refine ⟨primitiveizeNativeMiddleCycle G P h11
      (B.nativeFirstExceptional a), ?_, ?_⟩
  · change nativeToHodgeFiberLinear G
      (primitiveizeNativeMiddleCycle G P h11
        (B.nativeFirstExceptional a)) =
      primitiveHodgeRemainder G P h11
        (nativeToHodgeFiberLinear G
          (B.nativeFirstExceptional a))
    exact native_primitive_projection_cycleClass G P h11
      (B.nativeFirstExceptional a)
  · exact primitiveizeNativeMiddleCycle_primitive G P h11
      (B.nativeFirstExceptional a)

/-! ## GST intrinsic tangent-Chern primitive source on ANY original X

Previous source constructors depended on choosing a plane or
exceptional divisor. The second Chern class c₂(T_X) of the
ACTUAL tangent bundle is an independently canonical algebraic
codimension-two class on EVERY smooth projective complex X.

The original GST primitive projector sends this true native Chern
cycle to c₂(T_X) - h·D_X, where D_X is a genuine rational divisor
constructed using Hard Lefschetz and Lefschetz (1,1).

The native tangent Chern-cycle argument below represents the
ordinary scheme-theoretic tangent/Chern-class construction.
It does NOT pass an arbitrary Hodge target as an algebraic witness.
The output can be zero on some X. Nonzero means that the real
Chern class lies outside the divisor-cup subspace.
-/

noncomputable def nativeTangentSecondChernPrimitive
    (G : GeometricCycleClassSpine V H)
    (P : GeometricHigherLefschetzData G d)
    (h11 : DivisorsRepresentHodge11 H)
    (nativeTangentSecondChern : codimensionCycles V.X 2) :
    codimensionCycles V.X 2 :=
  primitiveizeNativeMiddleCycle G P h11 nativeTangentSecondChern

theorem nativeTangentSecondChernPrimitive_correct
    (G : GeometricCycleClassSpine V H)
    (P : GeometricHigherLefschetzData G d)
    (h11 : DivisorsRepresentHodge11 H)
    (nativeTangentSecondChern : codimensionCycles V.X 2) :
    P.primitiveTest
      (nativeToHodgeFiberLinear G
        (nativeTangentSecondChernPrimitive G P h11 nativeTangentSecondChern)) =
        0 := by
  exact primitiveizeNativeMiddleCycle_primitive G P h11
    nativeTangentSecondChern

theorem nativeTangentSecondChernPrimitive_cycleClass
    (G : GeometricCycleClassSpine V H)
    (P : GeometricHigherLefschetzData G d)
    (h11 : DivisorsRepresentHodge11 H)
    (nativeTangentSecondChern : codimensionCycles V.X 2) :
    nativeToHodgeFiberLinear G
      (nativeTangentSecondChernPrimitive G P h11 nativeTangentSecondChern) =
      primitiveHodgeRemainder G P h11
        (nativeToHodgeFiberLinear G nativeTangentSecondChern) := by
  exact native_primitive_projection_cycleClass G P h11
    nativeTangentSecondChern

theorem nativeTangentSecondChernPrimitive_nonzero
    (G : GeometricCycleClassSpine V H)
    (P : GeometricHigherLefschetzData G d)
    (h11 : DivisorsRepresentHodge11 H)
    (hInject : Function.Injective P.cupH2)
    (nativeTangentSecondChern : codimensionCycles V.X 2)
    (hOutside : ∀ beta : ClassicalHodgeFiber V H 1,
      nativeToHodgeFiberLinear G nativeTangentSecondChern ≠ P.cupH beta) :
    nativeToHodgeFiberLinear G
      (nativeTangentSecondChernPrimitive G P h11 nativeTangentSecondChern) ≠ 0 := by
  exact (native_primitive_nonzero_iff_outside_divisor_cup
    G P h11 hInject nativeTangentSecondChern).2 hOutside

/-! ## Exact K3×K3 geometric certificate

For polarized K3 surfaces (S,h₁),(T,h₂), with positive squares
a=∫_S h₁², b=∫_T h₂² and X=S×T, put H=h₁+h₂.

In H⁴(X;Q), let A=[pt]×T, C=h₁h₂, B=S×[pt].
Then c₂(T_X)=24(A+B), H²=a A+2 C+b B;
and A·B=1, C·C=a b, other products zero.

The GST rational divisor correction is
 H·((16/a-8/b)h₁+(16/b-8/a)h₂).

The primitive cycle coordinates (A,C,B) are
 (8(a+b)/b, -8(a+b)/(a b), 8(a+b)/a),
and their exact square is 192(a+b)²/(a b).

The Lean ℚ identity audits intersection arithmetic.
Geometric instantiation invokes genuine Künneth and K3 Chern
class comparison; it is not proved merely by numeric coordinates.
-/

def k3ProductTangentPrimitiveCoords (a b : ℚ) : ℚ × ℚ × ℚ :=
  (8*(a+b)/b, -8*(a+b)/(a*b), 8*(a+b)/a)

def k3ProductMiddlePairing (a b : ℚ)
    (u v : ℚ × ℚ × ℚ) : ℚ :=
  u.1*v.2.2 + u.2.2*v.1 + (a*b)*u.2.1*v.2.1

theorem k3ProductTangentPrimitiveNorm
    (a b : ℚ) (ha : a ≠ 0) (hb : b ≠ 0) :
    k3ProductMiddlePairing a b
      (k3ProductTangentPrimitiveCoords a b)
      (k3ProductTangentPrimitiveCoords a b) =
      192*(a+b)^2/(a*b) := by
  dsimp [k3ProductMiddlePairing, k3ProductTangentPrimitiveCoords]
  field_simp
  ring

theorem k3ProductTangentPrimitiveNorm_degreeTwo :
    k3ProductMiddlePairing 2 2
      (k3ProductTangentPrimitiveCoords 2 2)
      (k3ProductTangentPrimitiveCoords 2 2) = 768 := by
  norm_num [k3ProductMiddlePairing, k3ProductTangentPrimitiveCoords]

/-! ## Adversarial GST source-coverage test: ambient tangent Chern vanishes

For a smooth degree-d hypersurface X^n in P^(n+1), its authentic
tangent Euler sequence gives in algebraic K0:
 [T_X]=(n+2)[O_X(1)]-[O_X]-[O_X(d)].

Thus ALL Chern and Adams operations on the sublambda-ring
generated by the tangent bundle and the ambient line bundle
remain in the ambient rational Chow subalgebra Q[h].
In codimension 2, c₂(T_X)=(binom(n+2,2)-(n+2)d+d²)h².
On a fourfold, this is (15-6d+d²)h².
Any h² class lies in h cup Hodge-divisor, so the GST primitive
projection is zero.

This is an exact no-go for trying to solve arbitrary primitive
Hodge by tangent Chern classes alone: on smooth cubic fourfolds
containing a plane, c₂(T_X)=6h² has primitive output zero,
while the genuine plane source 3[P]-h² has square 24.
It is NOT a no-go for GST or other nonambient source channels.
-/

/-- The actual GST primitiveizer erases an ambient tangent-Chern
source rather than manufacturing a false primitive direction. -/
theorem nativeTangentSecondChernPrimitive_ambient_zero
    (G : GeometricCycleClassSpine V H)
    (P : GeometricHigherLefschetzData G d)
    (h11 : DivisorsRepresentHodge11 H)
    (hInject : Function.Injective P.cupH2)
    (nativeTangentSecondChern : codimensionCycles V.X 2)
    (beta : ClassicalHodgeFiber V H 1)
    (hAmbient :
      nativeToHodgeFiberLinear G nativeTangentSecondChern = P.cupH beta) :
    nativeToHodgeFiberLinear G
      (nativeTangentSecondChernPrimitive G P h11 nativeTangentSecondChern) =
        0 := by
  rw [nativeTangentSecondChernPrimitive_cycleClass, hAmbient]
  exact primitive_remainder_vanishes_on_cupH G P h11 hInject beta

/-- Universal fourfold hypersurface tangent c₂ coefficient. -/
def hypersurfaceFourfoldTangentC2Coeff (degree : ℤ) : ℤ :=
  15 - 6*degree + degree^2

theorem cubicFourfoldTangentC2_ambient :
    hypersurfaceFourfoldTangentC2Coeff 3 = 6 := by
  norm_num [hypersurfaceFourfoldTangentC2Coeff]


/-! ## Target-born K-charge surgery: an actual obstruction to naive twisting

For a complex rank-two bundle, the universal discriminant polynomial is
4*c₂-c₁². Tensoring by a line with first Chern class h changes the
Chern coordinates to c₁+2h and c₂+h*c₁+h², but it DOES NOT
change that discriminant. In contrast, adding an independent c₂
hyperplane charge m*h² DOES change it while retaining the target
primitive direction under an explicit algebraic hyperplane correction.

These are universal characteristic-class polynomial identities in an
arbitrary commutative ring, including the rational cohomology ring of any
original smooth projective X. They are NOT a construction of a
holomorphic bundle for every Hodge class: that unproved analytic
integrability step is still required for the full Hodge conjecture.
-/

/-- Rank-two Chern discriminant, in the universal characteristic ring. -/
def rankTwoDiscriminantPoly {R : Type*} [CommRing R]
    (c1 c2 : R) : R :=
  4 * c2 - c1 ^ 2

/-- Twisting a rank-two source by ANY line bundle leaves its Chern
discriminant unchanged. Hence arbitrarily positive twisting cannot
repair a zero-discriminant Hermitian-Einstein obstruction. -/
theorem rankTwoDiscriminant_twist_invariant
    {R : Type*} [CommRing R] (c1 c2 h : R) :
    rankTwoDiscriminantPoly (c1 + 2*h)
      (c2 + h*c1 + h^2) = rankTwoDiscriminantPoly c1 c2 := by
  unfold rankTwoDiscriminantPoly
  ring

/-- Injecting a genuinely independent ambient codimension-two charge,
rather than tensoring the same bundle, changes the discriminant. -/
theorem rankTwoDiscriminant_ambient_charge
    {R : Type*} [CommRing R] (c1 c2 h m : R) :
    rankTwoDiscriminantPoly c1 (c2 + m*h^2) =
      rankTwoDiscriminantPoly c1 c2 + 4*m*h^2 := by
  unfold rankTwoDiscriminantPoly
  ring

/-- Exact GST target packet: a topological rank-two source whose second
Chern coordinate is N*alpha+m*h² retains the requested alpha after
the known algebraic polarization correction. No target cycle selected. -/
theorem rankTwoChargePacket_original_target
    {R : Type*} [CommRing R] (alpha N m h : R) :
    (N*alpha + m*h^2) - m*h^2 = N*alpha := by
  ring

/-- Twisting the CHARGE-AUGMENTED source introduces only the explicit
algebraic ambient term (m+k²)h². This subtraction is valid in the
actual rational cohomology ring of EVERY original projective X. -/
theorem rankTwoChargedTwist_exact_primitive_recovery
    {R : Type*} [CommRing R] (alpha N m k h : R) :
    (N*alpha + m*h^2 + (k*h)^2) - (m+k^2)*h^2 =
      N*alpha := by
  ring

/-- The distinct Chern-charge operation yields a nonzero positive
polarization degree at every positive charge on an ample variety. -/
theorem positive_ambient_charge_discriminant_degree
    (m degree : ℚ) (hm : 0 < m) (hd : 0 < degree) :
    0 < 4*m*degree := by
  positivity


/-! ## Every-rank, every-codimension charged Chern-class protection

The splitting-principle identity for a rank-r vector bundle is
  c_p(E ⊗ L^k) = Σ_{j=0}^{p} choose(r-j,p-j) (k h)^(p-j) c_j(E).
If each lower source c_j(E)=m_j*h^j is ambient and only c_p(E)
has an independent primitive component N*alpha, the formula below
proves the ENTIRE lower Chern contribution is an explicitly known
ambient multiple of h^p. Thus ANY number of independent ambient
K-charges can be introduced to avoid unstable geometric constraints
without changing the desired primitive target after subtraction.

These are the universal cohomology-ring identities; existence of a
HOLomorphic E with the requested Chern coordinates remains open and
cannot be inserted as a hidden surjectivity hypothesis.
-/

/-- One graded-characteristic charge (m_j h^j) contributes only
to the algebraic top-degree hyperplane direction after twisting. -/
theorem allCodimensionChargeTerm_ambient
    {R : Type*} [CommRing R]
    (p j : Nat) (hj : j ≤ p) (m k h : R) :
    (k*h)^(p-j) * (m*h^j) =
      (k^(p-j)*m)*h^p := by
  rw [mul_pow]
  calc
    (k^(p-j)*h^(p-j)) * (m*h^j) =
        (k^(p-j)*m)*(h^(p-j)*h^j) := by ring
    _ = (k^(p-j)*m)*h^p := by
      rw [← pow_add, Nat.sub_add_cancel hj]

/-- Exact universal all-rank GST multicharge formula in a commutative
characteristic-class ring, hence applicable on every original X. -/
theorem allCodimensionMultiCharge_ambient_formula
    {R : Type*} [CommRing R]
    (r p : Nat) (m : Nat → R) (N alpha k h : R) :
    (∑ j ∈ Finset.range p,
      ((r-j).choose (p-j) : R) *
        (k*h)^(p-j) * (m j*h^j)) + N*alpha =
    (∑ j ∈ Finset.range p,
      ((r-j).choose (p-j) : R) *
        k^(p-j) * m j) * h^p + N*alpha := by
  congr 1
  rw [Finset.sum_mul]
  apply Finset.sum_congr rfl
  intro j hj
  have hjle : j ≤ p := Nat.le_of_lt (Finset.mem_range.mp hj)
  have hterm := allCodimensionChargeTerm_ambient p j hjle (m j) k h
  calc
    ((r-j).choose (p-j) : R) * (k*h)^(p-j) * (m j*h^j) =
        ((r-j).choose (p-j) : R) *
          ((k*h)^(p-j) * (m j*h^j)) := by ring
    _ = ((r-j).choose (p-j) : R) * k^(p-j) * m j * h^p := by
      rw [hterm]
      ring

/-- The native primitive cohomology target is recovered exactly
after removing the algebraic multicharge hyperplane packet.
This statement makes NO assertion that a holomorphic source exists. -/
theorem allCodimensionMultiCharge_exact_recovery
    {R : Type*} [CommRing R]
    (r p : Nat) (m : Nat → R) (N alpha k h : R) :
    ((∑ j ∈ Finset.range p,
      ((r-j).choose (p-j) : R) *
        (k*h)^(p-j) * (m j*h^j)) + N*alpha) -
      (∑ j ∈ Finset.range p,
        ((r-j).choose (p-j) : R) *
          k^(p-j) * m j) * h^p = N*alpha := by
  rw [allCodimensionMultiCharge_ambient_formula]
  ring

#check allCodimensionChargeTerm_ambient
#check allCodimensionMultiCharge_ambient_formula
#check allCodimensionMultiCharge_exact_recovery
#print axioms allCodimensionMultiCharge_exact_recovery

#check rankTwoDiscriminant_twist_invariant
#check rankTwoDiscriminant_ambient_charge
#check rankTwoChargePacket_original_target
#check rankTwoChargedTwist_exact_primitive_recovery
#check positive_ambient_charge_discriminant_degree
#print axioms rankTwoDiscriminant_twist_invariant
#print axioms rankTwoChargedTwist_exact_primitive_recovery

#check nativeTangentSecondChernPrimitive_ambient_zero
#check cubicFourfoldTangentC2_ambient
#print axioms nativeTangentSecondChernPrimitive_ambient_zero

#check nativeTangentSecondChernPrimitive_correct
#check nativeTangentSecondChernPrimitive_cycleClass
#check nativeTangentSecondChernPrimitive_nonzero
#check k3ProductTangentPrimitiveNorm
#check k3ProductTangentPrimitiveNorm_degreeTwo
#print axioms k3ProductTangentPrimitiveNorm

#check every_picard_primitive_vector_has_native_chow_cycle
#print axioms every_picard_primitive_vector_has_native_chow_cycle

#check picardToNativePrimitiveKernelLinear
#check picardToNativePrimitiveKernelLinear_injective
#print axioms picardToNativePrimitiveKernelLinear_injective

#check picardToNativePrimitiveLinear
#check picardToNativePrimitiveLinear_injective
#print axioms picardToNativePrimitiveLinear_injective

#check primitive_center_divisor_directions_are_distinct
#print axioms primitive_center_divisor_directions_are_distinct

#check GenuineBlowupPicardPrimitivePacket
#check exceptional_picard_class_in_Lefschetz_forces_zero
#check nonzero_primitive_cycle_of_any_center_divisor
#print axioms nonzero_primitive_cycle_of_any_center_divisor

#check GenuineBlowupThreeSectorPrimitivePacket
#check blowup_exceptional_cycle_transverse_to_divisor_cup
#check actual_nonzero_primitive_cycle_of_three_sector_blowup
#print axioms actual_nonzero_primitive_cycle_of_three_sector_blowup

#check geometrically_measured_native_primitive_cycle
#check geometric_primitive_projection_idempotent
#print axioms geometrically_measured_native_primitive_cycle
#print axioms geometric_primitive_projection_idempotent

#check correction_is_cup_of_real_divisor
#check primitive_remainder_vanishes_on_cupH
#check native_primitive_projection_cycleClass
#check native_primitive_nonzero_iff_outside_divisor_cup
#check exists_actual_nonzero_algebraic_primitive_of_transverse_cycle

#print axioms native_primitive_nonzero_iff_outside_divisor_cup
#print axioms exists_actual_nonzero_algebraic_primitive_of_transverse_cycle

end GSTPrimitiveTransverseCycleExtraction
