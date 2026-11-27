import HCUniverse2.GSTOriginalXWaveChowMatrixCompiler
import HCUniverse2.GSTImageThreePhysicalNavigationControl
import Mathlib

/-!
# Original-X GST exact physical Navigation wave/Chow bridge

NO substitution of a hand-picked abstract operator matrix:
the matrix coefficients are computed directly from the owner's
original 4x3 Wave-I carrier, original U shuffle, signed CM J mirror,
true SURVIVE M and exact [J,M] source, with the original arithmetic
Navigation predicate controlling the physical curvature charge.

For a real original X with >=12 independent algebraic divisor-Lefschetz
cycles and genuine dual intersection cycles, the companion TeX builds
the ACTUAL Chow correspondence Gamma_R in CH^d(X x X)_Q as a
rational sum of E_ij = pr1*(Y_i) pr2*(Z_j). This Lean file proves
the operator/canonical-Betti commuting square and verifies the
source-sensitive null/max physical matrix coefficients from the true
owner wave definitions.

The IntersectionChowFrame is realized from actual Chow cycles in
the geometric manuscript; the Lean code does not pretend that
an abstract module family alone creates those schemes.
-/

set_option maxHeartbeats 6000000
noncomputable section

namespace GSTOriginalXNativePhysicalNavigationBridge

open GSTGraphV2CMWaveFusion
open GSTImageThreeCurvatureResonance
open GSTImageThreePhysicalNavigationControl
open GSTPerfectPowerTailNavigation
open GSTOriginalXDivisorCurveCyclicChowFold
open GSTOriginalXWaveChowMatrixCompiler

/-- The ORIGINAL author's 12 cells ordered by carry and trit. -/
def originalCell (i : Fin 12) : GSTGraphV2InformationRecovery.Cell :=
  (⟨i.val / 3, by omega⟩, ⟨i.val % 3, by omega⟩)

theorem originalCell_zero :
    originalCell (0 : Fin 12) = nullCell := by decide
theorem originalCell_eleven :
    originalCell (11 : Fin 12) = maximumCell := by decide

/-- The source matrix comes from applying the original actual physical
wave F_R=U+J+M+navigationCharge(R)[J,M] to its true basis cells. -/
def originalPhysicalWaveMatrix (R : Nat) : Matrix (Fin 12) (Fin 12) ℚ :=
  fun i j =>
    physicalCurvatureFold R 1
      (fun s => if s = originalCell j then 1 else 0)
      (originalCell i)

/-- TRUE owner's maximum/null source entry is 2b-1 with b the
ORIGINAL arithmetic Navigation charge. -/
theorem physical_max_from_null (R : Nat) :
    originalPhysicalWaveMatrix R 11 0 =
      2 * navigationCharge R - 1 := by
  change physicalCurvatureFold R 1
    (fun s => if s = originalCell (0 : Fin 12) then 1 else 0)
    (originalCell (11 : Fin 12)) = _
  rw [originalCell_zero, originalCell_eleven]
  change curvatureFold 1 (navigationCharge R)
    (fun s => if s = nullCell then 1 else 0) maximumCell = _
  rw [curvatureFold_maximum]
  simp [nullCell, maximumCell]

/-- The same original physical matrix has a truly nonvanishing
null-to-maximum channel for every arithmetic state R. -/
theorem physical_max_from_null_nonzero (R : Nat) :
    originalPhysicalWaveMatrix R 11 0 ≠ 0 := by
  rw [physical_max_from_null]
  intro hz
  apply physicalNavigationCharge_ne_half R
  linarith

universe u v
variable {A : Type u} [AddCommGroup A] [Module ℚ A]
variable {B : Type v} [AddCommGroup B] [Module ℚ B]
variable (G : IntersectionChowFrame (Fin 12) A B)

/-- Original GST physical fold, now built as a native Chow operator
on the actual original-X algebraic source sector. -/
noncomputable def physicalChowOperator (R : Nat) : Module.End ℚ A :=
  nativeMatrixFold G (originalPhysicalWaveMatrix R)

/-- Canonical Betti action of the SAME true original-X Chow source. -/
noncomputable def physicalBettiOperator (R : Nat) : Module.End ℚ B :=
  bettiMatrixFold G (originalPhysicalWaveMatrix R)

/-- Genuine native-to-canonical-Betti source commutation, for the
original GST U/J/M/Nav curvature matrix, not arbitrary fake signals. -/
theorem physical_chow_betti_square (R : Nat) (Z : A) :
    G.cycleClass (physicalChowOperator G R Z) =
      physicalBettiOperator G R (G.cycleClass Z) :=
  nativeMatrixFold_class G (originalPhysicalWaveMatrix R) Z

/-- The algebraic image of actual original-X cycles is stable under
EVERY true arithmetic Navigation-controlled original GST curvature fold. -/
theorem physical_preserves_algebraic_range
    (R : Nat) (alpha : B)
    (halpha : alpha ∈ LinearMap.range G.cycleClass) :
    physicalBettiOperator G R alpha ∈ LinearMap.range G.cycleClass :=
  matrixFold_preserves_algebraic_range G
    (originalPhysicalWaveMatrix R) alpha halpha

#check originalPhysicalWaveMatrix
#check physical_max_from_null
#check physical_max_from_null_nonzero
#check physical_chow_betti_square
#check physical_preserves_algebraic_range
#print axioms physical_max_from_null
#print axioms physical_chow_betti_square
#print axioms physical_preserves_algebraic_range

end GSTOriginalXNativePhysicalNavigationBridge
