import GSTClassicalHodgeLocalSeedBareLefschetzExtinction

/-!
# GST CLASSICAL HODGE — BARE L² NONCIRCULARITY AUDIT

The minimal-ghost reduction compresses the entire GST operator arsenal to one
ambient two-slot `L²` operator.  It is tempting to regard native point lifts for
that operator as a new geometric theorem still waiting to be proved.

This file identifies the exact logical content of that premise.

Fix one genuine algebraic Hodge source `a` and one source basis coordinate `i`
with nonzero coefficient.  For any target Hodge basis sheet `j`, the following
are equivalent:

* the ambient two-slot GST `L²` operator from `i` to `j` has native point lifts;
* the target basis sheet `j` itself belongs to the genuine atomic algebraic
  cycle-class span.

The reverse implication uses only the fact that every genuine point-cycle
class is Hodge and the exact two-slot formula

  L²(alpha) = c * coord_i(alpha) * basis_j.

If `basis_j` already has one native representative, scalar multiples of that
representative lift every point image.  The forward implication applies native
atomic stability to the fixed algebraic source; since both the universal
forward scalar and the source coordinate are nonzero, the target basis is
recovered by rational rescaling.

Therefore `HasNativePointLifts` for bare two-slot `L²` is not an independent
replacement for the Hodge problem once a live algebraic source is present.  It
is exactly the missing algebraicity of the target sheet in operator language.
This audit prevents circular closure through a renamed matrix-unit premise.
-/

set_option maxHeartbeats 90000000
set_option maxRecDepth 1000000

noncomputable section

open AlgebraicGeometry

namespace GSTClassicalHodgeBareLefschetzNonCircularity

open GSTProjectiveOverC
open GSTGeometricRealizationStage2D
open GSTGeometricRealizationStage2F
open GSTGeometricRealizationStage2G
open GSTNativeCodimensionCyclePresentation
open GSTClassicalHodgeAtomicSpan
open GSTClassicalHodgeFiberedCosmology
open GSTClassicalHodgeNativeGeneratorNaturality
open GSTClassicalHodgeUniversalTwoSlotNativeClosure
open GSTClassicalHodgeTwoSlotLefschetzCollapse
open GSTClassicalHodgeLocalSeedBareLefschetzExtinction
open GSTClassicalHodgeGeometricCycleClassSpine

variable {V : SmoothProjectiveComplexScheme}
variable {H : HodgeBigradedBettiData V}
variable {p : Nat}

/-- If the target Hodge basis sheet is already algebraic, then bare two-slot
GST `L²` has native lifts on every genuine point generator. -/
theorem nativePointLifts_of_targetBasis_algebraic
    (G : GeometricCycleClassSpine V H)
    (i j : ClassicalHodgeBasisIndex V H p)
    (hj : (classicalHodgeBasis V H p j).1 ∈
      pointCycleClassSpan p (H.cycleClass p)) :
    HasNativePointLifts
      (p := p) (cl := H.cycleClass p)
      (ambientTwoStepLefschetz i j) := by
  have hjRange :
      (classicalHodgeBasis V H p j).1 ∈
        LinearMap.range (H.cycleClass p) :=
    pointCycleClassSpan_le_cycleClass_range p (H.cycleClass p) hj
  rcases hjRange with ⟨Zj, hZj⟩
  intro x
  let ax : ClassicalHodgeFiber V H p :=
    ⟨H.cycleClass p (codimensionPointCycle V.X p x),
      G.algebraic_is_hodge p (codimensionPointCycle V.X p x)⟩
  let c : ℚ :=
    (forwardScalar sourceSlot targetSlot : ℚ) * hodgeCoordinate i ax
  refine ⟨c • Zj, ?_⟩
  rw [LinearMap.map_smul, hZj]
  simpa [c] using
    (ambientTwoStepLefschetz_on_hodge_coordinate
      (V := V) (H := H) i j ax).symm

/-- Conversely, one live algebraic source turns native point lifts for bare
`L²` into algebraicity of the target basis sheet. -/
theorem targetBasis_algebraic_of_nativePointLifts
    (i j : ClassicalHodgeBasisIndex V H p)
    (a : ClassicalHodgeFiber V H p)
    (haAlg : a.1 ∈ pointCycleClassSpan p (H.cycleClass p))
    (hi : hodgeCoordinate i a ≠ 0)
    (hL : HasNativePointLifts
      (p := p) (cl := H.cycleClass p)
      (ambientTwoStepLefschetz i j)) :
    (classicalHodgeBasis V H p j).1 ∈
      pointCycleClassSpan p (H.cycleClass p) := by
  have hstable : AtomicSpanStable
      (p := p) (cl := H.cycleClass p)
      (ambientTwoStepLefschetz i j) :=
    (smoothProjective_atomicStable_iff_nativePointLifts
      (V := V) (H := H) (p := p)
      (ambientTwoStepLefschetz i j)).2 hL
  have himage :
      ambientTwoStepLefschetz i j a.1 ∈
        pointCycleClassSpan p (H.cycleClass p) :=
    hstable a.1 haAlg
  have hformula :=
    ambientTwoStepLefschetz_on_hodge_coordinate
      (V := V) (H := H) i j a
  rw [hformula] at himage
  let c : ℚ :=
    (forwardScalar sourceSlot targetSlot : ℚ) * hodgeCoordinate i a
  have hc : c ≠ 0 :=
    mul_ne_zero twoSlot_forwardScalar_ne_zero hi
  have hscaled :=
    (pointCycleClassSpan p (H.cycleClass p)).smul_mem c⁻¹ himage
  simpa [c, hc, smul_smul] using hscaled

/-- **BARE L² NATIVE NATURALITY = TARGET ALGEBRAICITY.**
With one algebraic source carrying a nonzero source coordinate, native point
lifts for the compressed two-slot GST `L²` operator are exactly equivalent to
algebraicity of the target basis sheet. -/
theorem bareLefschetz_nativePointLifts_iff_targetBasis_algebraic
    (G : GeometricCycleClassSpine V H)
    (i j : ClassicalHodgeBasisIndex V H p)
    (a : ClassicalHodgeFiber V H p)
    (haAlg : a.1 ∈ pointCycleClassSpan p (H.cycleClass p))
    (hi : hodgeCoordinate i a ≠ 0) :
    HasNativePointLifts
        (p := p) (cl := H.cycleClass p)
        (ambientTwoStepLefschetz i j)
      ↔
    (classicalHodgeBasis V H p j).1 ∈
      pointCycleClassSpan p (H.cycleClass p) := by
  constructor
  · exact targetBasis_algebraic_of_nativePointLifts i j a haAlg hi
  · intro hj
    exact nativePointLifts_of_targetBasis_algebraic G i j hj

/-- Minimal-ghost specialization: after the local algebraic source has been
constructed, the remaining bare-L² premise is literally equivalent to saying
that the detected ghost sheet is algebraic. -/
theorem minimalGhost_bareLefschetz_iff_detectedSheet_algebraic
    (G : GeometricCycleClassSpine V H)
    (M : GSTClassicalHodgeMinimalPrimitiveSeparatorGhost.MinimalPrimitiveGhost G)
    (S : MinimalGhostLocalSeed G M) :
    HasNativePointLifts
        (p := M.weight) (cl := H.cycleClass M.weight)
        (ambientTwoStepLefschetz S.sourceIndex M.sheet)
      ↔
    (classicalHodgeBasis V H M.weight M.sheet).1 ∈
      pointCycleClassSpan M.weight (H.cycleClass M.weight) := by
  exact bareLefschetz_nativePointLifts_iff_targetBasis_algebraic
    G S.sourceIndex M.sheet S.source S.source_algebraic
    S.sourceCoefficient_ne_zero

/-- Hence a genuine minimal separator forbids native point lifts for the bare
`L²` crossing to its detected sheet.  This is a consequence of the separator,
not a new geometric contradiction. -/
theorem minimalGhost_bareLefschetz_has_no_nativePointLifts
    (G : GeometricCycleClassSpine V H)
    (M : GSTClassicalHodgeMinimalPrimitiveSeparatorGhost.MinimalPrimitiveGhost G)
    (S : MinimalGhostLocalSeed G M) :
    ¬ HasNativePointLifts
        (p := M.weight) (cl := H.cycleClass M.weight)
        (ambientTwoStepLefschetz S.sourceIndex M.sheet) := by
  intro hL
  have hj :=
    (minimalGhost_bareLefschetz_iff_detectedSheet_algebraic G M S).1 hL
  have hker :
      pointCycleClassSpan M.weight (H.cycleClass M.weight) ≤
        LinearMap.ker M.separator.detector :=
    (GSTClassicalHodgeAtomicAnnihilator.annihilatesPointCycles_iff_atomicSpan_le_ker
      M.weight (H.cycleClass M.weight) M.separator.detector).mp
      M.separator.annihilates_atoms
  exact M.separator.detects_basis (hker hj)

#check nativePointLifts_of_targetBasis_algebraic
#check targetBasis_algebraic_of_nativePointLifts
#check bareLefschetz_nativePointLifts_iff_targetBasis_algebraic
#check minimalGhost_bareLefschetz_iff_detectedSheet_algebraic
#check minimalGhost_bareLefschetz_has_no_nativePointLifts

#print axioms nativePointLifts_of_targetBasis_algebraic
#print axioms targetBasis_algebraic_of_nativePointLifts
#print axioms bareLefschetz_nativePointLifts_iff_targetBasis_algebraic
#print axioms minimalGhost_bareLefschetz_iff_detectedSheet_algebraic
#print axioms minimalGhost_bareLefschetz_has_no_nativePointLifts

end GSTClassicalHodgeBareLefschetzNonCircularity
