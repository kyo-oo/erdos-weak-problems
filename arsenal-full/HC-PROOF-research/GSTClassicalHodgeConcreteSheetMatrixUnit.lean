import GSTClassicalHodgeIntegralLefschetzTransport
import GSTClassicalHodgeSheetSpectralExtraction
import GSTClassicalHodgeIntegralWorldEmbedding
import GSTGlobalPureHodgeCosmology
import GSTWorldRecoordinationGroupoid

/-!
# GST CLASSICAL HODGE — CONCRETE SHEET MATRIX UNITS

This module constructs the actual finite GST matrix-unit operation from the
primitive limitless arsenal:

1. spectrally project onto one source sheet;
2. apply the unique Lefschetz power carrying that diagonal sheet to a chosen
   forward target;
3. spectrally project the target sheet;
4. rationalize and divide by the nonzero central-binomial coefficient.

On a pure integral square the result is exactly the source coefficient placed
on the target sheet and zero everywhere else.  Thus the abstract rational
matrix units used in the rank-free irreducibility theorem are realized by a
concrete projector/Lefschetz/projector word of the existing GST operator
calculus.
-/

set_option maxHeartbeats 20000000
set_option maxRecDepth 1000000

noncomputable section

open AlgebraicGeometry
open GSTWorldCosmology
open GSTTruncatedWorldCohomologyRing
open GSTUniversalLefschetzCosmology
open GSTClassicalHodgeSheetSpectralExtraction
open GSTClassicalHodgeIntegralLefschetzTransport
open GSTGlobalPureHodgeCosmology
open GSTWorldRecoordinationGroupoid

namespace GSTClassicalHodgeConcreteSheetMatrixUnit

/-- Rational coefficient field on a finite square GST world. -/
abbrev RationalSquareCoef (N : Nat) := WorldCell N N → ℚ

/-- Rationalization of an integer GST world. -/
def rationalizeWorld {N : Nat}
    (f : WorldCoef N N) : RationalSquareCoef N :=
  fun x => (f x : ℚ)

/-- Rationalized target projector. -/
def rationalSheetProjector {N : Nat}
    (s : Fin N) (f : WorldCoef N N) : RationalSquareCoef N :=
  rationalizeWorld (sheetSpectralProj s f)

/-- Forward projector/Lefschetz/projector word before normalization. -/
def forwardSheetWord
    {N : Nat} (r s : Fin N)
    (f : WorldCoef N N) : WorldCoef N N :=
  sheetSpectralProj s
    (worldAct N N ((L N N) ^ (2 * (s.1-r.1)))
      (sheetSpectralProj r f))

/-- Nonzero rational normalizing scalar of the forward matrix-unit word. -/
def forwardNormalizeScalar
    {N : Nat} (r s : Fin N) : ℚ :=
  ((2 * (s.1-r.1)).choose (s.1-r.1) : Nat)

/-- Normalized rational forward matrix unit. -/
def forwardSheetMatrixUnit
    {N : Nat} (r s : Fin N)
    (f : WorldCoef N N) : RationalSquareCoef N :=
  fun x => (forwardNormalizeScalar r s)⁻¹ *
    (forwardSheetWord r s f x : ℚ)

/-- The forward normalization scalar is nonzero. -/
theorem forwardNormalizeScalar_ne_zero
    {N : Nat} (r s : Fin N) :
    forwardNormalizeScalar r s ≠ 0 := by
  unfold forwardNormalizeScalar
  exact_mod_cast Nat.ne_of_gt (Nat.choose_pos (by omega))

/-- On a pure world, source projection is exactly the source diagonal atom. -/
theorem source_projection_pure
    {N : Nat} (r : Fin N)
    (f : WorldCoef N N)
    (hf : isWorldPureHodge f) :
    sheetSpectralProj r f = sheetDiagonalAtom r (f (r,r)) :=
  sheetSpectralProj_pure_eq_atom r f hf

/-- The unnormalized word has exactly central-binomial-scaled source
coefficient at the target diagonal. -/
theorem forwardSheetWord_target
    {N : Nat} (r s : Fin N)
    (hrs : r.1 ≤ s.1)
    (f : WorldCoef N N)
    (hf : isWorldPureHodge f) :
    forwardSheetWord r s f (s,s) =
      f (r,r) *
        ((2 * (s.1-r.1)).choose (s.1-r.1) : ℤ) := by
  unfold forwardSheetWord
  rw [source_projection_pure r f hf]
  have hmove := sheetAtom_lefschetz_forward_exact r s hrs (f (r,r))
  have hcode :
      sheetSpectralProj s
        (worldAct N N ((L N N) ^ (2 * (s.1-r.1)))
          (sheetDiagonalAtom r (f (r,r)))) (s,s) =
      worldAct N N ((L N N) ^ (2 * (s.1-r.1)))
          (sheetDiagonalAtom r (f (r,r))) (s,s) := by
    simp [sheetSpectralProj, codeSectorProj, sheetCode]
    rfl
  exact hcode.trans hmove

/-- After normalization, the target coordinate is exactly the original source
coordinate. -/
theorem forwardSheetMatrixUnit_target
    {N : Nat} (r s : Fin N)
    (hrs : r.1 ≤ s.1)
    (f : WorldCoef N N)
    (hf : isWorldPureHodge f) :
    forwardSheetMatrixUnit r s f (s,s) = (f (r,r) : ℚ) := by
  unfold forwardSheetMatrixUnit
  rw [forwardSheetWord_target r s hrs f hf]
  push_cast
  have hne : (((2 * (s.1 - r.1)).choose (s.1 - r.1) : ℕ) : ℚ) ≠ 0 := by
    have hpos : 0 < ((2 * (s.1 - r.1)).choose (s.1 - r.1) : ℕ) :=
      Nat.choose_pos (by omega)
    intro hzero
    have hnat : ((2 * (s.1 - r.1)).choose (s.1 - r.1) : ℕ) = 0 := by
      simpa using hzero
    omega
  rw [forwardNormalizeScalar, mul_comm ((f (r,r) : ℤ) : ℚ) _, ← mul_assoc,
    inv_mul_cancel₀ hne, one_mul]

/-- The target projector kills every state other than the target diagonal
sheet. -/
theorem forwardSheetMatrixUnit_off_target
    {N : Nat} (r s : Fin N)
    (f : WorldCoef N N)
    (x : WorldCell N N)
    (hx : x ≠ (s,s)) :
    forwardSheetMatrixUnit r s f x = 0 := by
  unfold forwardSheetMatrixUnit forwardSheetWord
  have hcode : worldCode (outputShape N N) x ≠ sheetCode s := by
    intro h
    have hx' : x = (s,s) :=
      worldCode_injective (outputShape N N) h
    exact hx hx'
  simp [sheetSpectralProj, codeSectorProj, hcode]

/-- **CONCRETE FORWARD MATRIX UNIT.** On every pure integral GST square the
normalized projector/Lefschetz/projector word is exactly the rank-one matrix
unit carrying the source diagonal coefficient to the target diagonal sheet. -/
theorem forwardSheetMatrixUnit_exact
    {N : Nat} (r s : Fin N)
    (hrs : r.1 ≤ s.1)
    (f : WorldCoef N N)
    (hf : isWorldPureHodge f) :
    forwardSheetMatrixUnit r s f =
      fun x => if x = (s,s) then (f (r,r) : ℚ) else 0 := by
  funext x
  by_cases hx : x = (s,s)
  · subst x
    simp [forwardSheetMatrixUnit_target r s hrs f hf]
  · simp [hx, forwardSheetMatrixUnit_off_target r s f x hx]

/-- In particular, every nonzero integral source sheet produces the exact
nonzero target sheet after normalization. -/
theorem forwardSheetMatrixUnit_nonzero
    {N : Nat} (r s : Fin N)
    (hrs : r.1 ≤ s.1)
    (f : WorldCoef N N)
    (hf : isWorldPureHodge f)
    (hr : f (r,r) ≠ 0) :
    forwardSheetMatrixUnit r s f ≠ 0 := by
  intro hz
  have hs := congrFun hz ((s,s) : WorldCell N N)
  rw [forwardSheetMatrixUnit_target r s hrs f hf] at hs
  exact hr (by exact_mod_cast (show (f (r,r) : ℚ) = 0 from hs))

#check RationalSquareCoef
#check rationalizeWorld
#check forwardSheetWord
#check forwardNormalizeScalar
#check forwardSheetMatrixUnit
#check forwardSheetWord_target
#check forwardSheetMatrixUnit_target
#check forwardSheetMatrixUnit_off_target
#check forwardSheetMatrixUnit_exact
#check forwardSheetMatrixUnit_nonzero

#print axioms forwardSheetWord_target
#print axioms forwardSheetMatrixUnit_target
#print axioms forwardSheetMatrixUnit_exact
#print axioms forwardSheetMatrixUnit_nonzero

end GSTClassicalHodgeConcreteSheetMatrixUnit
