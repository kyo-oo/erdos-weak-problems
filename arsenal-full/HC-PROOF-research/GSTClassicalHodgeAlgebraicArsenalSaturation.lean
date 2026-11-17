import GSTClassicalHodgeArsenalOrbitSaturation
import GSTClassicalHodgeRankFreeArsenalIrreducibility
import GSTClassicalHodgeAtomicSpan

/-!
# GST CLASSICAL HODGE — ALGEBRAIC ARSENAL SATURATION

The limitless matrix-unit action reduces algebraicity in one Hodge weight to
one orbit statement.

Let `A_p` be the genuine algebraic Hodge subspace: those rational `(p,p)`
classes whose ambient class lies in the actual point-cycle span.  If one
nonzero class `alpha` belongs to `A_p` and every GST matrix-unit image of
`alpha` remains in `A_p`, then the span of the single arsenal orbit is both
all of the Hodge fiber and contained in `A_p`.  Hence `A_p = top`.

This is strictly stronger than asking separately for one algebraic cycle for
every Hodge basis direction.  The entire weight is forced by one native seed
and closure of its one-step full-arsenal orbit.
-/

set_option maxHeartbeats 20000000
set_option maxRecDepth 1000000

noncomputable section

open AlgebraicGeometry
open GSTProjectiveOverC
open GSTGeometricRealizationStage2D
open GSTGeometricRealizationStage2F
open GSTGeometricRealizationStage2G
open GSTClassicalHodgeAtomicSpan
open GSTClassicalHodgeFiberedCosmology
open GSTClassicalHodgeRankFreeArsenalIrreducibility
open GSTClassicalHodgeArsenalOrbitSaturation
open GSTClassicalHodgeAtomicDefectDuality

namespace GSTClassicalHodgeAlgebraicArsenalSaturation

variable {V : SmoothProjectiveComplexScheme}
variable {H : HodgeBigradedBettiData V}
variable {p : Nat}

/-- One algebraic Hodge seed whose complete one-step matrix-unit orbit remains
algebraic. -/
structure AlgebraicArsenalSeed
    (V : SmoothProjectiveComplexScheme)
    (H : HodgeBigradedBettiData V)
    (p : Nat) where
  seed : ClassicalHodgeFiber V H p
  seed_ne_zero : seed ≠ 0
  seed_algebraic : seed ∈ AlgebraicHodgeSubspace V H p
  orbit_algebraic :
    ∀ i j : ClassicalHodgeBasisIndex V H p,
      hodgeMatrixUnit i j seed ∈ AlgebraicHodgeSubspace V H p

namespace AlgebraicArsenalSeed

/-- The whole linear span of the single full-arsenal orbit is algebraic. -/
theorem orbitSpan_le_algebraic
    (S : AlgebraicArsenalSeed V H p) :
    arsenalOrbitSpan S.seed ≤ AlgebraicHodgeSubspace V H p := by
  apply Submodule.span_le.mpr
  rintro x ⟨ij, rfl⟩
  exact S.orbit_algebraic ij.1 ij.2

/-- **ONE-SEED ALGEBRAIC SATURATION.** The one-step GST orbit of one nonzero
algebraic Hodge seed already forces the complete genuine Hodge fiber into the
actual algebraic cycle-class image. -/
theorem algebraicHodgeSubspace_eq_top
    (S : AlgebraicArsenalSeed V H p) :
    AlgebraicHodgeSubspace V H p = ⊤ := by
  have htop : arsenalOrbitSpan S.seed = ⊤ :=
    arsenalOrbitSpan_eq_top S.seed S.seed_ne_zero
  apply top_unique
  intro alpha _
  have halpha : alpha ∈ arsenalOrbitSpan S.seed := by
    rw [htop]
    trivial
  exact S.orbitSpan_le_algebraic halpha

/-- Every genuine rational `(p,p)` class in this weight is represented by an
actual native codimension-p cycle. -/
theorem every_hodge_class_has_native_cycle
    (S : AlgebraicArsenalSeed V H p)
    (alpha : ClassicalHodgeFiber V H p) :
    ∃ Z : codimensionCycles V.X p,
      H.cycleClass p Z = alpha.1 := by
  have hmem : alpha ∈ AlgebraicHodgeSubspace V H p := by
    rw [S.algebraicHodgeSubspace_eq_top]
    trivial
  have hatomic : alpha.1 ∈ pointCycleClassSpan p (H.cycleClass p) := hmem
  rw [← smoothProjective_cycleClass_range_eq_atomic_span V H p] at hatomic
  exact hatomic

/-- The atomic defect in this weight vanishes completely. -/
theorem atomicDefect_eq_zero
    (S : AlgebraicArsenalSeed V H p) :
    atomicDefectLinearMap V H p = 0 := by
  apply (atomicDefectLinearMap_eq_zero_iff V H p).2
  intro alpha halpha
  let alphaH : ClassicalHodgeFiber V H p := ⟨alpha, halpha⟩
  have hmem : alphaH ∈ AlgebraicHodgeSubspace V H p := by
    rw [S.algebraicHodgeSubspace_eq_top]
    trivial
  exact hmem

end AlgebraicArsenalSeed

/-- A one-seed arsenal certificate in every nonzero weight closes the complete
Stage-2G Hodge statement directly, without any natural-number address chart or
basis-wise projector family. -/
theorem bigradedBettiHodge_of_algebraicArsenalSeeds
    (V : SmoothProjectiveComplexScheme)
    (H : HodgeBigradedBettiData V)
    (hseed : ∀ p : Nat,
      (Nontrivial (ClassicalHodgeFiber V H p)) →
        Nonempty (AlgebraicArsenalSeed V H p)) :
    BigradedBettiHodgeStatement V H := by
  intro p alpha halpha
  let alphaH : ClassicalHodgeFiber V H p := ⟨alpha, halpha⟩
  by_cases hzero : alphaH = 0
  · refine ⟨0, ?_⟩
    have hcoe := congrArg
      (fun x : ClassicalHodgeFiber V H p =>
        (x : RationalSingularCohomology H.analytification (2 * p))) hzero
    simpa [alphaH] using hcoe.symm
  · letI : Nontrivial (ClassicalHodgeFiber V H p) :=
      ⟨⟨0, alphaH, by simpa [Ne.symm hzero]⟩⟩
    let S := Classical.choice (hseed p inferInstance)
    exact S.every_hodge_class_has_native_cycle alphaH

#check AlgebraicArsenalSeed
#check AlgebraicArsenalSeed.orbitSpan_le_algebraic
#check AlgebraicArsenalSeed.algebraicHodgeSubspace_eq_top
#check AlgebraicArsenalSeed.every_hodge_class_has_native_cycle
#check AlgebraicArsenalSeed.atomicDefect_eq_zero
#check bigradedBettiHodge_of_algebraicArsenalSeeds

#print axioms AlgebraicArsenalSeed.algebraicHodgeSubspace_eq_top
#print axioms AlgebraicArsenalSeed.every_hodge_class_has_native_cycle
#print axioms AlgebraicArsenalSeed.atomicDefect_eq_zero
#print axioms bigradedBettiHodge_of_algebraicArsenalSeeds

end GSTClassicalHodgeAlgebraicArsenalSaturation
