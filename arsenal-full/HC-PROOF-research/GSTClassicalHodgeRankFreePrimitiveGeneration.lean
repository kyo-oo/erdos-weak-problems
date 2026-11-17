import GSTClassicalHodgePrimitiveArsenalRationalization
import GSTClassicalHodgeRankFreeArsenalIrreducibility
import GSTWorldRecoordinationGroupoid

/-!
# GST CLASSICAL HODGE — RANK-FREE PRIMITIVE GENERATION

The genuine classical Hodge fiber may have arbitrary basis cardinality, but
one rank-free matrix unit only involves two basis directions.  Therefore a
2x2 finite GST observation window is enough to realize every global matrix
unit.

We construct finite read/write maps between an arbitrary finite list of
chosen genuine Hodge-basis directions and a rational GST pure window.  Under
this conjugation the finite matrix unit is *definitionally* the rank-free
Hodge matrix unit on the corresponding genuine basis directions.  Combining
this with explicit GST arsenal generation shows that every global Hodge
matrix unit is the lift of a concrete two-slot projector/Lefschetz word.

This is the precise finite-observation/limitless-colimit mechanism: no global
countability and no fixed finite Hodge rank is assumed.
-/

set_option maxHeartbeats 30000000
set_option maxRecDepth 1000000

noncomputable section

open scoped BigOperators
open GSTProjectiveOverC
open GSTGeometricRealizationStage2G
open GSTWorldRecoordinationGroupoid
open GSTClassicalHodgeFiberedCosmology
open GSTClassicalHodgeFullArsenalIrreducibility
open GSTClassicalHodgeExplicitArsenalGeneration
open GSTClassicalHodgePrimitiveArsenalRationalization
open GSTClassicalHodgeRankFreeArsenalIrreducibility

namespace GSTClassicalHodgeRankFreePrimitiveGeneration

variable {V : SmoothProjectiveComplexScheme}
variable {H : HodgeBigradedBettiData V}
variable {p : Nat}

/-- Read the chosen genuine Hodge-basis coordinates into one finite GST pure
window. -/
noncomputable def finiteHodgeRead
    {N : Nat}
    (e : Fin N → ClassicalHodgeBasisIndex V H p) :
    ClassicalHodgeFiber V H p →ₗ[ℚ] RationalPureWindow N where
  toFun alpha := fun r => hodgeCoordinate (e r) alpha
  map_add' := by
    intro a b
    funext r
    simp [hodgeCoordinate]
  map_smul' := by
    intro c a
    funext r
    simp [hodgeCoordinate]

/-- Write a finite GST pure vector back into the selected genuine Hodge-basis
sheets. -/
noncomputable def finiteHodgeWrite
    {N : Nat}
    (e : Fin N → ClassicalHodgeBasisIndex V H p) :
    RationalPureWindow N →ₗ[ℚ] ClassicalHodgeFiber V H p where
  toFun a := ∑ r : Fin N, (a r) • classicalHodgeBasis V H p (e r)
  map_add' := by
    intro a b
    simp [add_smul, Finset.sum_add_distrib]
  map_smul' := by
    intro c a
    simp [mul_smul, Finset.smul_sum]

/-- Lift a finite GST operator into the unrestricted genuine Hodge fiber by
reading the selected coordinates, applying the finite operator, and writing
back into the same selected basis sheets. -/
noncomputable def liftFiniteHodgeOperator
    {N : Nat}
    (e : Fin N → ClassicalHodgeBasisIndex V H p)
    (T : Module.End ℚ (RationalPureWindow N)) :
    Module.End ℚ (ClassicalHodgeFiber V H p) :=
  (finiteHodgeWrite e).comp (T.comp (finiteHodgeRead e))

/-- **FINITE MATRIX UNIT CONJUGATES TO THE GENUINE RANK-FREE MATRIX UNIT.** -/
theorem liftFiniteHodgeOperator_matrixUnit
    {N : Nat}
    (e : Fin N → ClassicalHodgeBasisIndex V H p)
    (r s : Fin N) :
    liftFiniteHodgeOperator e (pureMatrixUnit r s) =
      hodgeMatrixUnit (e r) (e s) := by
  apply LinearMap.ext
  intro alpha
  simp [liftFiniteHodgeOperator, finiteHodgeRead, finiteHodgeWrite,
    pureMatrixUnit, hodgeMatrixUnit_apply, rationalPureBasis]

/-- Two-slot selector containing any ordered pair of genuine Hodge-basis
indices.  World recoordination means the abstract names of the two directions
are irrelevant; only their two local slots matter. -/
def pairBasisIndex
    (i j : ClassicalHodgeBasisIndex V H p) :
    Fin 2 → ClassicalHodgeBasisIndex V H p
  | ⟨0, _⟩ => i
  | ⟨1, _⟩ => j

/-- Source slot of the universal two-slot local world. -/
def sourceSlot : Fin 2 := ⟨0, by omega⟩

/-- Target slot of the universal two-slot local world. -/
def targetSlot : Fin 2 := ⟨1, by omega⟩

@[simp]
theorem pairBasisIndex_source
    (i j : ClassicalHodgeBasisIndex V H p) :
    pairBasisIndex i j sourceSlot = i := rfl

@[simp]
theorem pairBasisIndex_target
    (i j : ClassicalHodgeBasisIndex V H p) :
    pairBasisIndex i j targetSlot = j := rfl

/-- Every rank-free matrix unit is already the lift of the fixed 2x2 finite
matrix unit from local source slot 0 to local target slot 1. -/
theorem rankFreeMatrixUnit_eq_twoSlotLift
    (i j : ClassicalHodgeBasisIndex V H p) :
    hodgeMatrixUnit i j =
      liftFiniteHodgeOperator (pairBasisIndex i j)
        (pureMatrixUnit sourceSlot targetSlot) := by
  symm
  simpa using
    liftFiniteHodgeOperator_matrixUnit
      (pairBasisIndex i j) sourceSlot targetSlot

/-- The two-slot matrix unit is an explicit normalized GST
projector-Lefschetz word. -/
theorem twoSlot_matrixUnit_eq_forwardArsenalWord :
    pureMatrixUnit sourceSlot targetSlot =
      forwardArsenalWord sourceSlot targetSlot := by
  symm
  apply forwardArsenalWord_eq_matrixUnit
  decide

/-- **RANK-FREE MATRIX UNIT = LIFTED ACTUAL GST WORD.**
Every global matrix unit on the genuine classical Hodge basis is the lift of
one fixed 2x2 GST projector/Lefschetz word after recoordination of its two
participating basis sheets. -/
theorem rankFreeMatrixUnit_eq_lifted_GST_word
    (i j : ClassicalHodgeBasisIndex V H p) :
    hodgeMatrixUnit i j =
      liftFiniteHodgeOperator (pairBasisIndex i j)
        (forwardArsenalWord sourceSlot targetSlot) := by
  rw [rankFreeMatrixUnit_eq_twoSlotLift,
    twoSlot_matrixUnit_eq_forwardArsenalWord]

/-- Rank-free generation crown. -/
theorem rank_free_primitive_generation_crown :
    ∀ i j : ClassicalHodgeBasisIndex V H p,
      hodgeMatrixUnit i j =
        liftFiniteHodgeOperator (pairBasisIndex i j)
          (forwardArsenalWord sourceSlot targetSlot) :=
  rankFreeMatrixUnit_eq_lifted_GST_word

#check finiteHodgeRead
#check finiteHodgeWrite
#check liftFiniteHodgeOperator
#check liftFiniteHodgeOperator_matrixUnit
#check pairBasisIndex
#check rankFreeMatrixUnit_eq_twoSlotLift
#check rankFreeMatrixUnit_eq_lifted_GST_word
#check rank_free_primitive_generation_crown

#print axioms liftFiniteHodgeOperator_matrixUnit
#print axioms rankFreeMatrixUnit_eq_twoSlotLift
#print axioms rankFreeMatrixUnit_eq_lifted_GST_word
#print axioms rank_free_primitive_generation_crown

end GSTClassicalHodgeRankFreePrimitiveGeneration
