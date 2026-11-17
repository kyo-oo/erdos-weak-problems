import GSTGraphV2WaveNShapeCompiler
import GSTGraphV2NativeCurvatureBirth
import GSTUniversalCodimensionTwoPrimitiveExtraction
import GSTGraphV2SelfExpandingCosmology
import GSTHodgeSingleHypothesisConditional

/-!
# GST wave-to-original-X source compiler and primitive curvature birth

This is the missing *typed interface*, not an assumed inverse Hodge cycle map.

The Wave I+CM current and N-hole single fold are already explicit rational
operators on an arbitrarily large information signal.  If an independently
constructed N-hole wave **native algebraic-cycle family** on the ORIGINAL
smooth projective complex X intertwines this operator with a genuinely
realized native/cohomological correspondence, we transport each wave iterate
to an ACTUAL native algebraic-cycle iterate with its exact Betti class.

For the first higher-dimensional challenge, codimension p=2, we join the
existing universal Lefschetz primitive extraction to this source and
the actual original-X commutator curvature cycle. The new statement proves
that any primitive-preserving pair of native folds produces an ACTUAL
primitive algebraic curvature cycle from the corrected wave seed.

No new assertion of wave-to-Hodge surjectivity is inserted in this
interface: that is an independently geometric issue, distinct from
already proved pure-wave cyclicity.
-/

noncomputable section

namespace GSTHodgeGSTWaveGeometricCompiler

open GSTProjectiveOverC
open GSTGeometricRealizationStage2D
open GSTGeometricRealizationStage2F
open GSTGeometricRealizationStage2G
open GSTClassicalHodgeFiberedCosmology
open GSTClassicalHodgeCycleOperatorNaturality
open GSTClassicalHodgeGeometricCycleClassSpine
open GSTClassicalHodgeGeometricMatrixRankLanding
open GSTUniversalLefschetzCurveCycles
open GSTGraphV2CMWaveFusion
open GSTGraphV2WaveNShapeCompiler
open GSTGraphV2NativeCurvatureBirth
open GSTUniversalCodimensionTwoPrimitiveExtraction
open GSTNCohomology

variable {V : SmoothProjectiveComplexScheme}
variable {H : HodgeBigradedBettiData V}
variable {p : Nat}

/-- An actual original-X native realization of the previously constructed
GST single-wave information/CM/N-hole fold.

The nativeFamily must come from independent algebraic construction on X;
no Hodge class is an input parameter of that map. The operatorPair
provides the cycle class commuting square. -/
structure WaveNativeCompiler
    (V : SmoothProjectiveComplexScheme)
    (H : HodgeBigradedBettiData V)
    (p : Nat) (s : NShape) where
  nativeFamily :
    HoleWaveSignals s →ₗ[ℚ] codimensionCycles V.X p
  operatorPair : CycleClassOperatorPair V H p
  intertwine :
    ∀ u : HoleWaveSignals s,
      nativeFamily (shiftedNShapeFold s u) =
        operatorPair.cycleOperator (nativeFamily u)

variable {s : NShape}

/-- One actual algebraic cycle obtained from the original mixed
information/wave source on X. -/
def nativeWaveSeed (C : WaveNativeCompiler V H p s) :
    codimensionCycles V.X p :=
  C.nativeFamily (uniformNShapeSeed s)

/-- The full ORIGINAL-X algebraic-cycle orbit of that one source. -/
def nativeWaveOrbit (C : WaveNativeCompiler V H p s) :
    ℕ → codimensionCycles V.X p
  | 0 => nativeWaveSeed C
  | k + 1 => C.operatorPair.cycleOperator (nativeWaveOrbit C k)

/-- A genuine wave-native transformation is preserved at every order. -/
theorem every_wave_iterate_is_native
    (C : WaveNativeCompiler V H p s) (k : ℕ) :
    C.nativeFamily (nShapeOrbit s k) = nativeWaveOrbit C k := by
  induction k with
  | zero => rfl
  | succ k ih =>
      change C.nativeFamily (shiftedNShapeFold s (nShapeOrbit s k)) =
        C.operatorPair.cycleOperator (nativeWaveOrbit C k)
      rw [C.intertwine, ih]

/-- The exact cohomological shadow of a genuine original-X source orbit. -/
def geometricWaveHodgeOrbit (C : WaveNativeCompiler V H p s) :
    ℕ → RationalSingularCohomology H.analytification (2*p)
  | 0 => H.cycleClass p (nativeWaveSeed C)
  | k + 1 => C.operatorPair.cohomologyOperator
      (geometricWaveHodgeOrbit C k)

/-- The original-X Betti cycle class commutes with every wave-fold iterate.
This is the genuine cycle/Cohomology/graph path from input to output. -/
theorem nativeWaveOrbit_cycleClass
    (C : WaveNativeCompiler V H p s) (k : ℕ) :
    H.cycleClass p (nativeWaveOrbit C k) =
      geometricWaveHodgeOrbit C k := by
  induction k with
  | zero => rfl
  | succ k ih =>
      change H.cycleClass p
        (C.operatorPair.cycleOperator (nativeWaveOrbit C k)) =
        C.operatorPair.cohomologyOperator
          (geometricWaveHodgeOrbit C k)
      rw [C.operatorPair.cycleClass_cycleOperator, ih]

/-- Combine an actual born wave seed with two native correspondence
operators to obtain a new original-X algebraic curvature cycle. -/
def waveBornCurvature
    (C : WaveNativeCompiler V H p s)
    (A B : CycleClassOperatorPair V H p) :
    codimensionCycles V.X p :=
  nativeCurvatureCycle A B (nativeWaveSeed C)

/-- The class of the wave-born curvature cycle is the true commutator
of the ambient Betti actions, on the class of the actual born seed. -/
theorem waveBornCurvature_class
    (C : WaveNativeCompiler V H p s)
    (A B : CycleClassOperatorPair V H p) :
    H.cycleClass p (waveBornCurvature C A B) =
      A.cohomologyOperator
        (B.cohomologyOperator (H.cycleClass p (nativeWaveSeed C))) -
      B.cohomologyOperator
        (A.cohomologyOperator (H.cycleClass p (nativeWaveSeed C))) := by
  exact nativeCurvature_cycleClass A B (nativeWaveSeed C)

/-- The curvature readout actually separates a new algebraic class
from a specified old Betti subspace when its independent geometric
test is nonzero. -/
theorem waveBornCurvature_outside_old
    (C : WaveNativeCompiler V H p s)
    (A B : CycleClassOperatorPair V H p)
    (old : Submodule ℚ
      (RationalSingularCohomology H.analytification (2*p)))
    (read : RationalSingularCohomology H.analytification (2*p)
      →ₗ[ℚ] ℚ)
    (hOld : ∀ x ∈ old, read x = 0)
    (hNew : read (H.cycleClass p (waveBornCurvature C A B)) ≠ 0) :
    H.cycleClass p (waveBornCurvature C A B) ∉ old :=
  nativeCurvature_escapes_old_sector A B (nativeWaveSeed C)
    old read hOld hNew

section PrimitiveDegreeTwo

variable {d : Nat}

/-- Independently construct the native Lefschetz-corrected PRIMITIVE
cycle from the original GST wave seed. -/
def primitiveNativeWaveSeed
    (C : WaveNativeCompiler V H 2 s)
    (G : GeometricCycleClassSpine V H)
    (P : GeometricHigherLefschetzData G d)
    (h11 : DivisorsRepresentHodge11 H) :
    codimensionCycles V.X 2 :=
  primitiveizeNativeMiddleCycle G P h11 (nativeWaveSeed C)

/-- The corrected wave seed has zero true geometric primitive test. -/
theorem primitiveNativeWaveSeed_test
    (C : WaveNativeCompiler V H 2 s)
    (G : GeometricCycleClassSpine V H)
    (P : GeometricHigherLefschetzData G d)
    (h11 : DivisorsRepresentHodge11 H) :
    P.primitiveTest
      (nativeToHodgeFiberLinear G
        (primitiveNativeWaveSeed C G P h11)) = 0 :=
  primitiveizeNativeMiddleCycle_primitive G P h11 (nativeWaveSeed C)

/-- An actual codimension-two algebraic curvature cycle obtained from a
primitiveized original-X GST wave seed. -/
def primitiveBornCurvature
    (C : WaveNativeCompiler V H 2 s)
    (G : GeometricCycleClassSpine V H)
    (P : GeometricHigherLefschetzData G d)
    (h11 : DivisorsRepresentHodge11 H)
    (A B : CycleClassOperatorPair V H 2) :
    codimensionCycles V.X 2 :=
  nativeCurvatureCycle A B (primitiveNativeWaveSeed C G P h11)

/-- Exact HIGHER-CODIMENSION primitive-curvature theorem:
If each real native geometric fold preserves the primitive kernel,
their noncommutative curvature of the freshly corrected wave seed
is still primitive. No arbitrary primitive Hodge representative
is assumed as a cycle. -/
theorem primitiveBornCurvature_test
    (C : WaveNativeCompiler V H 2 s)
    (G : GeometricCycleClassSpine V H)
    (P : GeometricHigherLefschetzData G d)
    (h11 : DivisorsRepresentHodge11 H)
    (A B : CycleClassOperatorPair V H 2)
    (hA : ∀ Z : codimensionCycles V.X 2,
      P.primitiveTest (nativeToHodgeFiberLinear G Z) = 0 →
      P.primitiveTest
        (nativeToHodgeFiberLinear G (A.cycleOperator Z)) = 0)
    (hB : ∀ Z : codimensionCycles V.X 2,
      P.primitiveTest (nativeToHodgeFiberLinear G Z) = 0 →
      P.primitiveTest
        (nativeToHodgeFiberLinear G (B.cycleOperator Z)) = 0) :
    P.primitiveTest
      (nativeToHodgeFiberLinear G
        (primitiveBornCurvature C G P h11 A B)) = 0 := by
  let Z := primitiveNativeWaveSeed C G P h11
  have hz : P.primitiveTest (nativeToHodgeFiberLinear G Z) = 0 :=
    primitiveNativeWaveSeed_test C G P h11
  have hAB := hA (B.cycleOperator Z) (hB Z hz)
  have hBA := hB (A.cycleOperator Z) (hA Z hz)
  change P.primitiveTest
      (nativeToHodgeFiberLinear G
        (A.cycleOperator (B.cycleOperator Z) -
          B.cycleOperator (A.cycleOperator Z))) = 0
  rw [map_sub, map_sub, hAB, hBA, sub_self]

end PrimitiveDegreeTwo

#check GSTGraphV2SelfExpandingCosmology.NativeGeometryBirth.every_world_birth_has_native_realization
#check GSTHodgeSingleHypothesisConditional.exactHodge_of_one_GST_fold_orbit
#check GSTUniversalCodimensionTwoPrimitiveExtraction.Hodge_class_eq_primitive_plus_native_cycle
#check every_wave_iterate_is_native
#check nativeWaveOrbit_cycleClass
#check waveBornCurvature_class
#check primitiveBornCurvature_test
#print axioms primitiveBornCurvature_test
#print axioms nativeWaveOrbit_cycleClass

end GSTHodgeGSTWaveGeometricCompiler
