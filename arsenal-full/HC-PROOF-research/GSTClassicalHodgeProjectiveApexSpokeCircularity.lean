import GSTClassicalHodgeOmniverseProjectiveApexSpokes
import GSTClassicalHodgeMinimalPrimitiveSeparatorGhost
import GSTClassicalHodgeAtomicSpan
import GSTClassicalHodgeAtomicAnnihilator

/-!
# GST CLASSICAL HODGE — PROJECTIVE APEX SPOKE CIRCULARITY

A target-specific projective apex spoke is a useful geometric reduction, but it
cannot be promoted to an unexplained final axiom.

A basis separator annihilates every point-cycle class.  On a smooth projective
carrier the point-cycle span is exactly the full cycle-class range, so the same
separator annihilates the class of every native algebraic cycle.

Now let `M` be a minimal primitive ghost and let `S` be any synchronized
nonzero algebraic seed in `M.weight`.  A `ProjectiveApexL2Spoke S M.sheet`
would have two incompatible consequences:

* genuine pushforward naturality makes its apex image the cycle class of an
  actual native pushed-forward cycle, hence the separator reads zero;
* the spoke's localized two-slot `L^2` equation identifies that same image
  with a nonzero scalar multiple of the detected basis sheet, hence the
  separator reads nonzero.

Therefore no such projective spoke can coexist with the minimal ghost.  A
ghost-indexed family of target spokes is consequently Hodge-strength, just like
the ghost-indexed bare-L2 closure audit.

No new geometric existence assumption is introduced here.
-/

set_option maxHeartbeats 100000000
set_option maxRecDepth 1000000

noncomputable section

open AlgebraicGeometry

namespace GSTClassicalHodgeProjectiveApexSpokeCircularity

open GSTProjectiveOverC
open GSTGeometricRealizationStage2D
open GSTGeometricRealizationStage2F
open GSTGeometricRealizationStage2G
open GSTClassicalHodgeFiberedCosmology
open GSTClassicalHodgeAtomicSpan
open GSTClassicalHodgeAtomicAnnihilator
open GSTClassicalHodgeSingleSheetCrown
open GSTClassicalHodgeSynchronizedDefectOrbit
open GSTClassicalHodgeMinimalPrimitiveSeparatorGhost
open GSTClassicalHodgeOmniverseProjectiveApexSpokes
open GSTClassicalHodgeGeometricCycleClassSpine

variable {V : SmoothProjectiveComplexScheme}
variable {H : HodgeBigradedBettiData V}

/-- A microscopic basis separator kills the class of every native cycle, not
only the point generators stored in its definition. -/
theorem BasisAtomicSeparator.kills_native_cycle
    {p : Nat}
    {i : ClassicalHodgeBasisIndex V H p}
    (Sep : BasisAtomicSeparator V H p i)
    (Z : codimensionCycles V.X p) :
    Sep.detector (H.cycleClass p Z) = 0 := by
  have hker :
      pointCycleClassSpan p (H.cycleClass p) ≤
        LinearMap.ker Sep.detector :=
    (annihilatesPointCycles_iff_atomicSpan_le_ker
      p (H.cycleClass p) Sep.detector).mp Sep.annihilates_atoms
  apply hker
  rw [← smoothProjective_cycleClass_range_eq_atomic_span V H p]
  exact ⟨Z, rfl⟩

/-- **A MINIMAL GHOST FORBIDS A PROJECTIVE L² SPOKE INTO ITS SHEET.**

The contradiction uses only the spoke's genuine native pushforward naturality,
the exact two-slot L² action already proved in the branch, and the separator's
atomic annihilation law. -/
theorem minimalGhost_forbids_projectiveApexL2Spoke
    (G : GeometricCycleClassSpine V H)
    (M : MinimalPrimitiveGhost G)
    (S : NativeHodgeOrbitSeed (V := V) (H := H) (p := M.weight)) :
    IsEmpty (ProjectiveApexL2Spoke S M.sheet) := by
  refine ⟨?_⟩
  intro R
  have hnat :=
    R.operatorPair.cycleClass_cycleOperator S.cycle
  rw [S.class_eq, R.operatorPair_on_apex] at hnat
  have hread := congrArg M.separator.detector hnat
  have hleft :
      M.separator.detector
        (H.cycleClass M.weight
          (R.operatorPair.cycleOperator S.cycle)) = 0 :=
    M.separator.kills_native_cycle
      (R.operatorPair.cycleOperator S.cycle)
  rw [hleft] at hread
  have hscalar :
      GSTClassicalHodgeOmniverseProjectiveApexSpokes.apexSpokeScalar S ≠ 0 :=
    apexSpokeScalar_ne_zero S
  have hright :
      M.separator.detector
        (GSTClassicalHodgeOmniverseProjectiveApexSpokes.apexSpokeScalar S •
          (classicalHodgeBasis V H M.weight M.sheet).1) ≠ 0 := by
    rw [LinearMap.map_smul]
    exact smul_ne_zero hscalar M.separator.detects_basis
  exact hright hread.symm

/-- Existential form: not even one genuine projective map can realize the
localized-L² transfer from an algebraic apex into the detected minimal-ghost
sheet. -/
theorem no_projectiveApexL2Spoke_to_minimalGhost
    (G : GeometricCycleClassSpine V H)
    (M : MinimalPrimitiveGhost G)
    (S : NativeHodgeOrbitSeed (V := V) (H := H) (p := M.weight)) :
    ¬ Nonempty (ProjectiveApexL2Spoke S M.sheet) := by
  exact not_nonempty_iff.mpr (minimalGhost_forbids_projectiveApexL2Spoke G M S)

/-- A ghost-indexed projective-spoke closure, parameterized by any chosen
algebraic source seed at each hypothetical minimal ghost. -/
def MinimalGhostProjectiveSpokeClosure
    (G : GeometricCycleClassSpine V H)
    (seed : ∀ M : MinimalPrimitiveGhost G,
      NativeHodgeOrbitSeed (V := V) (H := H) (p := M.weight)) : Prop :=
  ∀ M : MinimalPrimitiveGhost G,
    Nonempty (ProjectiveApexL2Spoke (seed M) M.sheet)

/-- Such a ghost-indexed projective-spoke family is impossible in any Hodge
failure world. -/
theorem hodge_of_minimalGhostProjectiveSpokeClosure
    (G : GeometricCycleClassSpine V H)
    (seed : ∀ M : MinimalPrimitiveGhost G,
      NativeHodgeOrbitSeed (V := V) (H := H) (p := M.weight))
    (hclose : MinimalGhostProjectiveSpokeClosure G seed) :
    BigradedBettiHodgeStatement V H := by
  by_contra hnot
  let M : MinimalPrimitiveGhost G :=
    minimalPrimitiveGhostOfFailure G hnot
  exact no_projectiveApexL2Spoke_to_minimalGhost G M (seed M) (hclose M)

/-- **PROJECTIVE-SPOKE CIRCULARITY RECEIPT.**
Once a source-seed selector is fixed on hypothetical minimal ghosts, existence
of projective L² spokes into their detected sheets is exactly Hodge-strength:
the reverse implication is vacuous because Hodge empties the minimal-ghost
type. -/
theorem minimalGhostProjectiveSpokeClosure_iff_hodge
    (G : GeometricCycleClassSpine V H)
    (seed : ∀ M : MinimalPrimitiveGhost G,
      NativeHodgeOrbitSeed (V := V) (H := H) (p := M.weight)) :
    MinimalGhostProjectiveSpokeClosure G seed ↔
      BigradedBettiHodgeStatement V H := by
  constructor
  · exact hodge_of_minimalGhostProjectiveSpokeClosure G seed
  · intro hHodge M
    have hnone :
        IsEmpty (MinimalPrimitiveGhost G) := by
      refine ⟨?_⟩
      intro E
      have hsep :=
        (bigradedBettiHodgeStatement_iff_no_basis_separator V H).mp
          hHodge E.weight E.sheet
      exact isEmpty_iff.mp hsep E.separator
    exact (isEmpty_iff.mp hnone M).elim

#check BasisAtomicSeparator.kills_native_cycle
#check minimalGhost_forbids_projectiveApexL2Spoke
#check no_projectiveApexL2Spoke_to_minimalGhost
#check MinimalGhostProjectiveSpokeClosure
#check hodge_of_minimalGhostProjectiveSpokeClosure
#check minimalGhostProjectiveSpokeClosure_iff_hodge

#print axioms BasisAtomicSeparator.kills_native_cycle
#print axioms minimalGhost_forbids_projectiveApexL2Spoke
#print axioms hodge_of_minimalGhostProjectiveSpokeClosure
#print axioms minimalGhostProjectiveSpokeClosure_iff_hodge

end GSTClassicalHodgeProjectiveApexSpokeCircularity
