import Mathlib
import GSTGlobalPureHodgeCosmology
import GSTWorldPoincareDuality

/-!
# GST SQUARE PURE-HODGE DUALITY

The global pure-Hodge cosmology identifies the full diagonal sector of every
rectangular world with its canonical diagonal-coordinate module.

This file strengthens that structure on square worlds.  The native GST
Poincare involution preserves the diagonal exactly when the two world depths
coincide.  Consequently it restricts to an involutive integer-linear
automorphism of the complete pure-Hodge sector, and under the canonical
pure-Hodge coordinate equivalence it is exactly reversal of the diagonal
coordinate string.

This is an internal GST statement: the duality is constructed entirely from
the existing world complement and global pure-Hodge coordinate laws.
-/

set_option maxHeartbeats 10000000
set_option maxRecDepth 1000000

namespace GSTSquarePureHodgeDuality

open GSTWorldCosmology
open GSTWorldPoincareDuality
open GSTDimensionFreeHodgeDiagonal
open GSTGlobalPureHodgeCosmology

/-- Mirror one canonical pure-Hodge coordinate in an N x N world. -/
def pureMirror
    {N : Nat} (p : Fin (min N N)) : Fin (min N N) :=
  ⟨N - 1 - p.1, by
    have hp : p.1 < N := by
      simpa using p.2
    have hmirror : N - 1 - p.1 < N := by
      omega
    simpa using hmirror⟩

@[simp]
theorem pureMirror_involutive
    {N : Nat} (p : Fin (min N N)) :
    pureMirror (pureMirror p) = p := by
  apply Fin.ext
  unfold pureMirror
  simp only
  omega

/-- The world Poincare complement of a pure diagonal cell is the mirrored
pure diagonal cell in every square GST world. -/
theorem worldDual_pureDiagonalState
    {N : Nat} (p : Fin (min N N)) :
    worldDual (pureDiagonalState p) =
      pureDiagonalState (pureMirror p) := by
  unfold worldDual pureDiagonalState diagonalState pureMirror complementFin
  apply Prod.ext
  · apply Fin.ext
    rfl
  · apply Fin.ext
    rfl

/-- Restriction of the native world duality to the complete pure-Hodge
submodule of a square world. -/
def squarePureDual
    {N : Nat} (f : PureWorldHodge N N) :
    PureWorldHodge N N := by
  refine ⟨fun x => f.1 (worldDual x), ?_⟩
  intro x hx
  apply f.2 (worldDual x)
  intro hdual
  apply hx
  have hfin :
      complementFin x.1 = complementFin x.2 := by
    apply Fin.ext
    exact hdual
  have hxfin : x.1 = x.2 :=
    (complementFin_involutive x.1).symm.trans
      ((congrArg complementFin hfin).trans
        (complementFin_involutive x.2))
  exact congrArg Fin.val hxfin

@[simp]
theorem squarePureDual_involutive
    {N : Nat} (f : PureWorldHodge N N) :
    squarePureDual (squarePureDual f) = f := by
  apply Subtype.ext
  funext x
  simp [squarePureDual]

/-- The restricted pure-Hodge duality is a genuine integer-linear
automorphism, not merely a set-theoretic involution. -/
def squarePureDualLinearEquiv
    (N : Nat) :
    PureWorldHodge N N ≃ₗ[ℤ] PureWorldHodge N N where
  toFun := squarePureDual
  invFun := squarePureDual
  left_inv := squarePureDual_involutive
  right_inv := squarePureDual_involutive
  map_add' := by
    intro f g
    apply Subtype.ext
    funext x
    rfl
  map_smul' := by
    intro z f
    apply Subtype.ext
    funext x
    rfl

/-- Coordinate reversal on the complete square pure-Hodge coordinate module. -/
def pureCoordinateReverse
    {N : Nat} (a : PureHodgeCoordinates N N) :
    PureHodgeCoordinates N N :=
  fun p => a (pureMirror p)

@[simp]
theorem pureCoordinateReverse_involutive
    {N : Nat} (a : PureHodgeCoordinates N N) :
    pureCoordinateReverse (pureCoordinateReverse a) = a := by
  funext p
  simp [pureCoordinateReverse]

/-- **PURE-HODGE DUALITY COORDINATE LAW.**

Under the canonical global pure-Hodge coordinates, native world duality is
exactly reversal of the full diagonal coordinate vector. -/
theorem pureCoordinates_squarePureDual
    {N : Nat} (f : PureWorldHodge N N) :
    pureCoordinates (squarePureDual f).1 =
      pureCoordinateReverse (pureCoordinates f.1) := by
  funext p
  show f.1 (worldDual (pureDiagonalState p))
    = f.1 (pureDiagonalState (pureMirror p))
  rw [worldDual_pureDiagonalState]

/-- The global pure-Hodge linear equivalence conjugates square-world
Poincare duality to coordinate reversal. -/
theorem pureHodgeLinearEquiv_conjugates_duality
    {N : Nat} (f : PureWorldHodge N N) :
    pureHodgeLinearEquiv N N (squarePureDual f) =
      pureCoordinateReverse (pureHodgeLinearEquiv N N f) := by
  exact pureCoordinates_squarePureDual f

/-- Pure-Hodge duality has order two simultaneously in the world and in its
canonical coordinate representation. -/
theorem square_pure_hodge_duality_crown :
    (∀ N (f : PureWorldHodge N N),
      squarePureDual (squarePureDual f) = f)
    ∧ (∀ N (a : PureHodgeCoordinates N N),
      pureCoordinateReverse (pureCoordinateReverse a) = a)
    ∧ (∀ N (f : PureWorldHodge N N),
      pureHodgeLinearEquiv N N (squarePureDual f) =
        pureCoordinateReverse (pureHodgeLinearEquiv N N f)) := by
  exact ⟨
    fun N f => squarePureDual_involutive f,
    fun N a => pureCoordinateReverse_involutive a,
    fun N f => pureHodgeLinearEquiv_conjugates_duality f⟩

#check pureMirror
#check worldDual_pureDiagonalState
#check squarePureDual
#check squarePureDual_involutive
#check squarePureDualLinearEquiv
#check pureCoordinateReverse
#check pureCoordinateReverse_involutive
#check pureCoordinates_squarePureDual
#check pureHodgeLinearEquiv_conjugates_duality
#check square_pure_hodge_duality_crown

#print axioms worldDual_pureDiagonalState
#print axioms squarePureDual_involutive
#print axioms squarePureDualLinearEquiv
#print axioms pureCoordinates_squarePureDual
#print axioms square_pure_hodge_duality_crown

end GSTSquarePureHodgeDuality
