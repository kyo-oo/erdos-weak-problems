import GSTHodgeWaveAllNHoleReadout
import GSTClassicalHodgeCycleOperatorNaturality
import GSTHodgeGSTWaveGeometricCompiler

/-!
# GST arbitrary-N Wave I/II/CM -> original-X native algebraic cycles

The all-N source eigenfunctional in GSTHodgeWaveAllNHoleReadout is
constructed from the original wave's fixed information cells, with
exact eigenvalues 2 + 10*channel(i).  This file adds a GEOMETRIC
synthesis of its quotient, rather than assuming a WaveNativeCompiler
intertwiner.

Input: actual rational algebraic cycles atom(i) on the ORIGINAL X,
with native dual functionals and compatible rational Betti dual
functionals.  In concrete products of CM elliptic curves, these
are implemented by Chow matrix-unit correspondences and the exact
intersection pairing with complementary divisor cycles.

Output: one actual rational native cycle operator, one compatible
whole-Betti operator, and an original-X native wave source map,
with the EXACT intertwining identity for EVERY full N-hole wave signal.

The frame cycles are separate input geometric data and are not
constructed on arbitrary X merely by information reachability.
-/

namespace GSTHodgeWaveAllNGeometricLanding

open GSTHodgeWaveAllNHoleReadout
open GSTGraphV2WaveNShapeCompiler
open GSTGraphV2CMWaveFusion
open GSTNCohomology

section RationalGeometry

variable {A : Type*} [AddCommGroup A] [Module ℚ A]
variable {B : Type*} [AddCommGroup B] [Module ℚ B]

/-- Independent genuine native cycles and independently geometric
dual intersection readings. No inverse cycle-class map is used. -/
structure GeometricWaveFrame (s : NShape) (cl : A →ₗ[ℚ] B) where
  atom : Fin s.holes → A
  nativeDual : Fin s.holes → (A →ₗ[ℚ] ℚ)
  bettiDual : Fin s.holes → (B →ₗ[ℚ] ℚ)
  dual_atom : ∀ i j, nativeDual i (atom j) = if i = j then 1 else 0
  dual_class : ∀ i (z : A), bettiDual i (cl z) = nativeDual i z

namespace GeometricWaveFrame

variable {s : NShape} {cl : A →ₗ[ℚ] B}

/-- Assemble arbitrary wave quotient coefficients into ACTUAL
native rational cycles, no postulated Hodge target lift. -/
def nativeCombination (F : GeometricWaveFrame s cl) :
    (Fin s.holes → ℚ) →ₗ[ℚ] A where
  toFun x := ∑ i : Fin s.holes, x i • F.atom i
  map_add' := by
    intro x y
    simp only [Pi.add_apply, add_smul, Finset.sum_add_distrib]
  map_smul' := by
    intro r x
    simp [Pi.smul_apply, smul_smul, Finset.smul_sum, smul_eq_mul]

/-- The same geometric sum on canonical rational Betti classes. -/
def bettiCombination (F : GeometricWaveFrame s cl) :
    (Fin s.holes → ℚ) →ₗ[ℚ] B where
  toFun x := ∑ i : Fin s.holes, x i • cl (F.atom i)
  map_add' := by
    intro x y
    simp only [Pi.add_apply, add_smul, Finset.sum_add_distrib]
  map_smul' := by
    intro r x
    simp [Pi.smul_apply, smul_smul, Finset.smul_sum, smul_eq_mul]

def nativeCoordinates (F : GeometricWaveFrame s cl) :
    A →ₗ[ℚ] (Fin s.holes → ℚ) where
  toFun z := fun i => F.nativeDual i z
  map_add' := by
    intro x y
    funext i
    simp [map_add, Pi.add_apply]
  map_smul' := by
    intro r x
    funext i
    simp [map_smul, Pi.smul_apply, smul_eq_mul]

def bettiCoordinates (F : GeometricWaveFrame s cl) :
    B →ₗ[ℚ] (Fin s.holes → ℚ) where
  toFun z := fun i => F.bettiDual i z
  map_add' := by
    intro x y
    funext i
    simp [map_add, Pi.add_apply]
  map_smul' := by
    intro r x
    funext i
    simp [map_smul, Pi.smul_apply, smul_eq_mul]

theorem nativeCoordinates_nativeCombination
    (F : GeometricWaveFrame s cl) (x : Fin s.holes → ℚ) :
    F.nativeCoordinates (F.nativeCombination x) = x := by
  funext j
  change F.nativeDual j (∑ i : Fin s.holes, x i • F.atom i) = x j
  rw [map_sum]
  simp only [map_smul, smul_eq_mul]
  simp [F.dual_atom, Finset.sum_ite_eq']

theorem bettiCoordinates_cl (F : GeometricWaveFrame s cl) (z : A) :
    F.bettiCoordinates (cl z) = F.nativeCoordinates z := by
  funext i
  exact F.dual_class i z

theorem cl_nativeCombination (F : GeometricWaveFrame s cl)
    (x : Fin s.holes → ℚ) :
    cl (F.nativeCombination x) = F.bettiCombination x := by
  simp [nativeCombination, bettiCombination, map_sum, map_smul]

/-- New native source construction from the original FULL N-hole wave. -/
def nativeWaveSource (F : GeometricWaveFrame s cl) :
    HoleWaveSignals s →ₗ[ℚ] A :=
  F.nativeCombination.comp (holeReadout s)

/-- The native original-X operator is a concrete sum of rank-one
cycle-source maps with wave-determined eigenvalues. -/
def nativeFold (F : GeometricWaveFrame s cl) : A →ₗ[ℚ] A :=
  F.nativeCombination.comp ((coefficientFold s).comp F.nativeCoordinates)

/-- The Betti operator is generated from the SAME geometric cycles,
dual pairings and wave spectral coefficients, not postulated freely. -/
def bettiFold (F : GeometricWaveFrame s cl) : B →ₗ[ℚ] B :=
  F.bettiCombination.comp ((coefficientFold s).comp F.bettiCoordinates)

/-- Actual canonical cycle class commutes with the newly synthesized
native fold for EVERY codimension-p cycle. -/
theorem nativeFold_cycleClass (F : GeometricWaveFrame s cl) (z : A) :
    cl (F.nativeFold z) = F.bettiFold (cl z) := by
  change cl (F.nativeCombination (coefficientFold s (F.nativeCoordinates z))) =
    F.bettiCombination (coefficientFold s (F.bettiCoordinates (cl z)))
  rw [F.cl_nativeCombination, F.bettiCoordinates_cl]

theorem nativeFold_cycleClass_square (F : GeometricWaveFrame s cl) :
    cl.comp F.nativeFold = F.bettiFold.comp cl := by
  ext z
  exact F.nativeFold_cycleClass z

/-- The newly constructed native fold intertwines the ENTIRE ORIGINAL
N-hole CM/Wave-I fold, not merely a finite orbit prefix. -/
theorem nativeWaveSource_intertwines
    (F : GeometricWaveFrame s cl) (u : HoleWaveSignals s) :
    F.nativeWaveSource (shiftedNShapeFold s u) =
      F.nativeFold (F.nativeWaveSource u) := by
  change F.nativeCombination (holeReadout s (shiftedNShapeFold s u)) =
    F.nativeCombination
      (coefficientFold s
        (F.nativeCoordinates (F.nativeCombination (holeReadout s u))))
  rw [holeReadout_intertwines, F.nativeCoordinates_nativeCombination]

/-- The original uniform Wave-I SURVIVE seed maps to the sum of
the actual independently constructed native cycles. -/
theorem uniformWaveSource_eq_sum (F : GeometricWaveFrame s cl) :
    F.nativeWaveSource (uniformNShapeSeed s) =
      ∑ i : Fin s.holes, F.atom i := by
  change ∑ i : Fin s.holes,
    (holeReadout s (uniformNShapeSeed s) i) • F.atom i =
    ∑ i : Fin s.holes, F.atom i
  simp only [holeReadout_uniform, one_smul]

theorem nativeFold_atom (F : GeometricWaveFrame s cl)
    (i : Fin s.holes) :
    F.nativeFold (F.atom i) = (2 + channelShift s i) • F.atom i := by
  change F.nativeCombination
    (coefficientFold s (F.nativeCoordinates (F.atom i))) =
    (2 + channelShift s i) • F.atom i
  have hid : F.nativeCoordinates (F.atom i) =
      fun j => if j = i then (1 : ℚ) else 0 := by
    funext j
    exact F.dual_atom j i
  rw [hid]
  change
    ∑ j : Fin s.holes,
      ((2 + channelShift s j) * (if j = i then 1 else 0)) • F.atom j =
      (2 + channelShift s i) • F.atom i
  simp

end GeometricWaveFrame
end RationalGeometry

section OriginalXLanding

open GSTProjectiveOverC
open GSTGeometricRealizationStage2D
open GSTGeometricRealizationStage2F
open GSTGeometricRealizationStage2G
open GSTClassicalHodgeCycleOperatorNaturality

variable {V : SmoothProjectiveComplexScheme}
variable {H : HodgeBigradedBettiData V}
variable {p : Nat} {s : NShape}

/-- The concrete geometric frame on the original smooth projective X,
whose cycle-class map is the supplied Betti interface. -/
abbrev OriginalXFrame :=
  GeometricWaveFrame s (H.cycleClass p)

/-- A single native/Betti correspondence pair derived explicitly from
Wave I+II+CM and independent actual Chow cycles, with no extra
intertwining assumption. -/
noncomputable def OriginalXFrame.toCycleClassOperatorPair
    (F : OriginalXFrame (V := V) (H := H) (p := p) (s := s)) :
    CycleClassOperatorPair V H p where
  cycleOperator := F.nativeFold
  cohomologyOperator := F.bettiFold
  cycleClass_natural := F.nativeFold_cycleClass_square

/-- The existing WaveNativeCompiler can now be built without assuming
its intertwining field: the geometric frame + all-N fixed-cell
eigen-readout PROVES that field. -/
noncomputable def OriginalXFrame.toWaveNativeCompiler
    (F : OriginalXFrame (V := V) (H := H) (p := p) (s := s)) :
    GSTHodgeGSTWaveGeometricCompiler.WaveNativeCompiler V H p s where
  nativeFamily := F.nativeWaveSource
  operatorPair := F.toCycleClassOperatorPair
  intertwine := by
    intro u
    exact F.nativeWaveSource_intertwines u

end OriginalXLanding

#check GeometricWaveFrame.nativeWaveSource_intertwines
#check GeometricWaveFrame.nativeFold_cycleClass
#check OriginalXFrame.toWaveNativeCompiler
#print axioms GeometricWaveFrame.nativeWaveSource_intertwines
#print axioms OriginalXFrame.toWaveNativeCompiler

end GSTHodgeWaveAllNGeometricLanding
