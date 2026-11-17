import GSTClassicalHodgeFiberedTransferCompletion
import GSTClassicalHodgeRankFreeArsenalIrreducibility
import GSTWorldPoincareDuality

/-!
# GST CLASSICAL HODGE — GLOBAL SHEET COSMOS

The repository already contains the correct total carrier for all rational
Hodge multiplicity sheets:

    FiberedHodgeAddress V H = (Σ p, ClassicalHodgeBasisIndex V H p) →₀ ℚ.

The missing step was to let the limitless GST read/write algebra act directly
on this total carrier rather than repeatedly collapsing to ad-hoc two-slot
windows.

This file installs the global sheet probes and global sheet matrix units.
They are exact Poincare-style coordinate reads followed by writes into another
genuine Hodge sheet.  At one fixed weight they intertwine exactly with the
rank-free `hodgeMatrixUnit` operators on the true rational `(p,p)` Hodge
fiber.  Distinct multiplicity sheets remain independent; forgetting
multiplicity happens only after the global action.
-/

set_option maxHeartbeats 100000000
set_option maxRecDepth 1000000

noncomputable section

open scoped BigOperators
open AlgebraicGeometry

namespace GSTClassicalHodgeGlobalSheetCosmos

open GSTProjectiveOverC
open GSTGeometricRealizationStage2F
open GSTGeometricRealizationStage2G
open GSTClassicalHodgeFiberedCosmology
open GSTClassicalHodgeFiberedTransferCompletion
open GSTClassicalHodgeRankFreeArsenalIrreducibility
open GSTWorldPoincareDuality

variable {V : SmoothProjectiveComplexScheme}
variable {H : HodgeBigradedBettiData V}

/-- Global Poincare-style probe of one genuine `(weight,basis-sheet)` address. -/
noncomputable def sheetProbe
    (s : FiberedHodgeIndex V H) :
    FiberedHodgeAddress V H →ₗ[ℚ] ℚ :=
  Finsupp.lapply s

@[simp]
theorem sheetProbe_apply
    (s : FiberedHodgeIndex V H)
    (phi : FiberedHodgeAddress V H) :
    sheetProbe s phi = phi s :=
  rfl

@[simp]
theorem sheetProbe_generator_self
    (s : FiberedHodgeIndex V H) :
    sheetProbe s (fiberedSheetGenerator V H s) = 1 := by
  simp [sheetProbe, fiberedSheetGenerator]

@[simp]
theorem sheetProbe_generator_other
    (s t : FiberedHodgeIndex V H)
    (hst : s ≠ t) :
    sheetProbe s (fiberedSheetGenerator V H t) = 0 := by
  simp [sheetProbe, fiberedSheetGenerator, hst]

/-- Global limitless sheet matrix unit: read source sheet `s`, write target
sheet `t`.  This is the total-sheet analogue of the cosmic diagonal matrix
unit and of the fixed-weight rank-free Hodge matrix unit. -/
noncomputable def sheetMatrixUnit
    (s t : FiberedHodgeIndex V H) :
    Module.End ℚ (FiberedHodgeAddress V H) :=
  LinearMap.smulRight (sheetProbe s) (fiberedSheetGenerator V H t)

@[simp]
theorem sheetMatrixUnit_apply
    (s t : FiberedHodgeIndex V H)
    (phi : FiberedHodgeAddress V H) :
    sheetMatrixUnit s t phi =
      phi s • fiberedSheetGenerator V H t := by
  rfl

@[simp]
theorem sheetMatrixUnit_generator_source
    (s t : FiberedHodgeIndex V H) :
    sheetMatrixUnit s t (fiberedSheetGenerator V H s) =
      fiberedSheetGenerator V H t := by
  simp [sheetMatrixUnit_apply, fiberedSheetGenerator,
    Finsupp.single_apply, one_smul]

@[simp]
theorem sheetMatrixUnit_generator_other
    (s t u : FiberedHodgeIndex V H)
    (hus : u ≠ s) :
    sheetMatrixUnit s t (fiberedSheetGenerator V H u) = 0 := by
  simp [sheetMatrixUnit_apply, fiberedSheetGenerator, hus]

/-- Exact global matrix-unit composition. -/
theorem sheetMatrixUnit_comp
    (s t u : FiberedHodgeIndex V H) :
    (sheetMatrixUnit t u).comp (sheetMatrixUnit s t) =
      sheetMatrixUnit s u := by
  apply LinearMap.ext
  intro phi
  simp [sheetMatrixUnit_apply, fiberedSheetGenerator,
    Finsupp.single_apply, one_smul, smul_assoc]

/-- Mismatched global sheet matrix units annihilate. -/
theorem sheetMatrixUnit_comp_zero
    (s t u v : FiberedHodgeIndex V H)
    (htu : t ≠ u) :
    (sheetMatrixUnit u v).comp (sheetMatrixUnit s t) = 0 := by
  apply LinearMap.ext
  intro phi
  simp [sheetMatrixUnit_apply, fiberedSheetGenerator, htu]

/-- A write into a weight-`p` target is supported only over weight `p`, no
matter where the scalar was read from. -/
theorem sheetMatrixUnit_target_weight
    (p : Nat)
    (s t : FiberedHodgeIndex V H)
    (ht : t.1 = p)
    (phi : FiberedHodgeAddress V H) :
    IsFiberedTransferHodge p (sheetMatrixUnit s t phi) := by
  intro u hu
  rw [sheetMatrixUnit_apply]
  by_cases htu : t = u
  · subst u
    exact (hu ht).elim
  · simp [fiberedSheetGenerator, htu]

/-- Reading the global sheet `(p,i)` from the embedded true Hodge fiber is
exactly the genuine basis-coordinate functional. -/
@[simp]
theorem sheetProbe_fiberedWeightCoordinates
    (p : Nat)
    (i : ClassicalHodgeBasisIndex V H p)
    (alpha : ClassicalHodgeFiber V H p) :
    sheetProbe (⟨p,i⟩ : FiberedHodgeIndex V H)
        (fiberedWeightCoordinates V H p alpha) =
      hodgeCoordinate i alpha := by
  simp [sheetProbe, fiberedWeightCoordinates, weightFiberEmbedding,
    hodgeCoordinate]
  show (Finsupp.embDomain (Function.Embedding.sigmaMk p)
      ((classicalHodgeBasis V H p).repr alpha)) ((Function.Embedding.sigmaMk p) i) =
    ((classicalHodgeBasis V H p).repr alpha) i
  rw [Finsupp.embDomain_apply_self]

/-- Exact coordinate embedding of a scalar multiple of one genuine Hodge
basis sheet. -/
@[simp]
theorem fiberedWeightCoordinates_smul_basis
    (p : Nat)
    (j : ClassicalHodgeBasisIndex V H p)
    (q : ℚ) :
    fiberedWeightCoordinates V H p
        (q • classicalHodgeBasis V H p j) =
      q • fiberedSheetGenerator V H
        (⟨p,j⟩ : FiberedHodgeIndex V H) := by
  simp [fiberedWeightCoordinates, weightFiberEmbedding,
    fiberedSheetGenerator]

/-- **GLOBAL/FIBER MATRIX-UNIT INTERTWINING.**
The total-sheet read/write operation restricted to one weight is literally the
rank-free Hodge matrix unit already used by the GST irreducibility engine. -/
theorem sheetMatrixUnit_intertwines_hodgeMatrixUnit
    (p : Nat)
    (i j : ClassicalHodgeBasisIndex V H p)
    (alpha : ClassicalHodgeFiber V H p) :
    sheetMatrixUnit
        (⟨p,i⟩ : FiberedHodgeIndex V H)
        (⟨p,j⟩ : FiberedHodgeIndex V H)
        (fiberedWeightCoordinates V H p alpha) =
      fiberedWeightCoordinates V H p (hodgeMatrixUnit i j alpha) := by
  rw [sheetMatrixUnit_apply]
  show (sheetProbe (⟨p,i⟩ : FiberedHodgeIndex V H)
      (fiberedWeightCoordinates V H p alpha)) •
      fiberedSheetGenerator V H (⟨p,j⟩ : FiberedHodgeIndex V H) =
    fiberedWeightCoordinates V H p (hodgeMatrixUnit i j alpha)
  rw [sheetProbe_fiberedWeightCoordinates]
  rw [hodgeMatrixUnit_apply]
  rw [fiberedWeightCoordinates_smul_basis]

/-- The global sheet matrix unit still lies over the established limitless GST
base diagonal after multiplicity is forgotten.  Thus the new global sheet
cosmos refines rather than replaces the original cosmic diagonal universe. -/
theorem forgetMultiplicity_sheetMatrixUnit_basis_source
    (p : Nat)
    (i j : ClassicalHodgeBasisIndex V H p) :
    forgetMultiplicityToGST
      (sheetMatrixUnit
        (⟨p,i⟩ : FiberedHodgeIndex V H)
        (⟨p,j⟩ : FiberedHodgeIndex V H)
        (fiberedSheetGenerator V H ⟨p,i⟩)) =
      Finsupp.single
        (GSTUniversalAddressBridge.cosmicAddressEquiv (p,p)) 1 := by
  rw [sheetMatrixUnit_generator_source]
  exact fiberedSheet_projects_to_cosmicGenerator V H p j

/-- One global crown: exact probes, exact matrix-unit composition, exact
fixed-weight intertwining, and exact projection to the original limitless GST
base all hold in the same total sheet universe. -/
theorem global_sheet_cosmos_crown :
    (∀ s : FiberedHodgeIndex V H,
      sheetProbe s (fiberedSheetGenerator V H s) = 1)
    ∧ (∀ s t u : FiberedHodgeIndex V H,
      (sheetMatrixUnit t u).comp (sheetMatrixUnit s t) =
        sheetMatrixUnit s u)
    ∧ (∀ p (i j : ClassicalHodgeBasisIndex V H p)
        (alpha : ClassicalHodgeFiber V H p),
      sheetMatrixUnit
          (⟨p,i⟩ : FiberedHodgeIndex V H)
          (⟨p,j⟩ : FiberedHodgeIndex V H)
          (fiberedWeightCoordinates V H p alpha) =
        fiberedWeightCoordinates V H p (hodgeMatrixUnit i j alpha)) := by
  exact ⟨sheetProbe_generator_self,
    sheetMatrixUnit_comp,
    sheetMatrixUnit_intertwines_hodgeMatrixUnit⟩

#check sheetProbe
#check sheetMatrixUnit
#check sheetMatrixUnit_comp
#check sheetMatrixUnit_comp_zero
#check sheetMatrixUnit_target_weight
#check sheetProbe_fiberedWeightCoordinates
#check sheetMatrixUnit_intertwines_hodgeMatrixUnit
#check forgetMultiplicity_sheetMatrixUnit_basis_source
#check global_sheet_cosmos_crown

#print axioms sheetMatrixUnit_comp
#print axioms sheetProbe_fiberedWeightCoordinates
#print axioms sheetMatrixUnit_intertwines_hodgeMatrixUnit
#print axioms global_sheet_cosmos_crown

end GSTClassicalHodgeGlobalSheetCosmos
