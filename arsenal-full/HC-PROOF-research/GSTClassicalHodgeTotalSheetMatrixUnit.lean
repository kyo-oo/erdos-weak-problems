import GSTClassicalHodgeConcreteSheetMatrixUnit
import GSTSquarePureHodgeDuality

/-!
# GST CLASSICAL HODGE — TOTAL SHEET MATRIX UNITS

The forward projector/Lefschetz/projector word already realizes every ordered
sheet transfer `r -> s` with `r <= s`.  Square-world Poincare duality turns a
backward request into the forward mirrored request

    mirror(r) <= mirror(s).

After running the forward matrix unit in the dual chart, dualize the rational
output back.  The result is the exact target sheet with the original source
coefficient.  Therefore every pair of live multiplicity sheets admits one
explicit GST matrix-unit word built solely from spectral projectors,
Lefschetz evolution, Poincare reflection and rational normalization.
-/

set_option maxHeartbeats 20000000
set_option maxRecDepth 1000000

noncomputable section

open GSTWorldCosmology
open GSTWorldPoincareDuality
open GSTSquarePureHodgeDuality
open GSTClassicalHodgeConcreteSheetMatrixUnit
open GSTClassicalHodgeSheetSpectralExtraction
open GSTGlobalPureHodgeCosmology
open GSTDimensionFreeHodgeDiagonal
open GSTClassicalHodgeIntegralLefschetzTransport

namespace GSTClassicalHodgeTotalSheetMatrixUnit

/-- Raw integer Poincare dual of a square world coefficient field. -/
def integerSquareDual {N : Nat} (f : WorldCoef N N) : WorldCoef N N :=
  fun x => f (worldDual x)

/-- Rational Poincare dual. -/
def rationalSquareDual {N : Nat}
    (f : RationalSquareCoef N) : RationalSquareCoef N :=
  fun x => f (worldDual x)

@[simp]
theorem integerSquareDual_involutive
    {N : Nat} (f : WorldCoef N N) :
    integerSquareDual (integerSquareDual f) = f := by
  funext x
  simp [integerSquareDual]

@[simp]
theorem rationalSquareDual_involutive
    {N : Nat} (f : RationalSquareCoef N) :
    rationalSquareDual (rationalSquareDual f) = f := by
  funext x
  simp [rationalSquareDual]

/-- Integer Poincare duality preserves pure diagonal support. -/
theorem integerSquareDual_isPure
    {N : Nat} (f : WorldCoef N N)
    (hf : isWorldPureHodge f) :
    isWorldPureHodge (integerSquareDual f) := by
  intro x hx
  unfold integerSquareDual
  apply hf (worldDual x)
  intro hdiag
  apply hx
  have hfin : complementFin x.1 = complementFin x.2 := by
    apply Fin.ext
    exact hdiag
  have hxfin : x.1 = x.2 :=
    (complementFin_involutive x.1).symm.trans
      ((congrArg complementFin hfin).trans
        (complementFin_involutive x.2))
  exact congrArg Fin.val hxfin

/-- Poincare dual reads the mirrored diagonal coefficient. -/
theorem integerSquareDual_diagonal
    {N : Nat} (f : WorldCoef N N) (r : Fin N) :
    integerSquareDual f (sheetMirror r, sheetMirror r) =
      f (r,r) := by
  unfold integerSquareDual
  have hinv : sheetMirror (sheetMirror r) = r :=
    complementFin_involutive r
  rw [worldDual_sheetDiagonal, hinv]

/-- Backward matrix unit via Poincare reflection, forward transport, and dual
return. -/
def backwardSheetMatrixUnit
    {N : Nat} (r s : Fin N)
    (f : WorldCoef N N) : RationalSquareCoef N :=
  let mr : Fin N := sheetMirror r
  let ms : Fin N := sheetMirror s
  rationalSquareDual
    (forwardSheetMatrixUnit mr ms (integerSquareDual f))

/-- Exact backward matrix unit. -/
theorem backwardSheetMatrixUnit_exact
    {N : Nat} (r s : Fin N)
    (hsr : s.1 ≤ r.1)
    (f : WorldCoef N N)
    (hf : isWorldPureHodge f) :
    backwardSheetMatrixUnit r s f =
      fun x => if x = (s,s) then (f (r,r) : ℚ) else 0 := by
  let mr : Fin N := sheetMirror r
  let ms : Fin N := sheetMirror s
  have hmrs : mr.1 ≤ ms.1 := by
    exact backward_request_reflects_forward r s hsr
  have hforward := forwardSheetMatrixUnit_exact
    mr ms hmrs (integerSquareDual f) (integerSquareDual_isPure f hf)
  unfold backwardSheetMatrixUnit
  change rationalSquareDual
      (forwardSheetMatrixUnit mr ms (integerSquareDual f)) = _
  rw [hforward]
  funext x
  unfold rationalSquareDual
  by_cases hx : x = (s,s)
  · subst x
    have hdual : worldDual ((s,s) : WorldCell N N) = (ms,ms) :=
      worldDual_sheetDiagonal s
    rw [hdual]
    simp [integerSquareDual_diagonal, mr]
  · have hdualne : worldDual x ≠ (ms,ms) := by
      intro h
      apply hx
      have h2 := congrArg worldDual h
      rw [worldDual_involutive, worldDual_sheetDiagonal] at h2
      have hinv : sheetMirror ms = s := complementFin_involutive s
      rw [hinv] at h2
      exact h2
    simp [hdualne, hx]

/-- Total concrete GST matrix unit between arbitrary sheets. -/
def totalSheetMatrixUnit
    {N : Nat} (r s : Fin N)
    (f : WorldCoef N N) : RationalSquareCoef N :=
  if h : r.1 ≤ s.1 then
    forwardSheetMatrixUnit r s f
  else
    backwardSheetMatrixUnit r s f

/-- **TOTAL MATRIX-UNIT THEOREM.** Every ordered source/target pair of a pure
integral GST square has an explicit projector/Lefschetz/Poincare word sending
exactly the source coefficient to the target sheet and killing all others. -/
theorem totalSheetMatrixUnit_exact
    {N : Nat} (r s : Fin N)
    (f : WorldCoef N N)
    (hf : isWorldPureHodge f) :
    totalSheetMatrixUnit r s f =
      fun x => if x = (s,s) then (f (r,r) : ℚ) else 0 := by
  unfold totalSheetMatrixUnit
  by_cases h : r.1 ≤ s.1
  · rw [dif_pos h]
    exact forwardSheetMatrixUnit_exact r s h f hf
  · rw [dif_neg h]
    exact backwardSheetMatrixUnit_exact r s (by omega) f hf

/-- Nonzero source sheets remain nonzero under every total matrix-unit
transport. -/
theorem totalSheetMatrixUnit_nonzero
    {N : Nat} (r s : Fin N)
    (f : WorldCoef N N)
    (hf : isWorldPureHodge f)
    (hr : f (r,r) ≠ 0) :
    totalSheetMatrixUnit r s f ≠ 0 := by
  intro hz
  have hs := congrFun hz ((s,s) : WorldCell N N)
  rw [totalSheetMatrixUnit_exact r s f hf] at hs
  simp at hs
  exact hr (by exact_mod_cast hs)

#check integerSquareDual
#check rationalSquareDual
#check integerSquareDual_isPure
#check backwardSheetMatrixUnit
#check backwardSheetMatrixUnit_exact
#check totalSheetMatrixUnit
#check totalSheetMatrixUnit_exact
#check totalSheetMatrixUnit_nonzero

#print axioms integerSquareDual_isPure
#print axioms backwardSheetMatrixUnit_exact
#print axioms totalSheetMatrixUnit_exact
#print axioms totalSheetMatrixUnit_nonzero

end GSTClassicalHodgeTotalSheetMatrixUnit
