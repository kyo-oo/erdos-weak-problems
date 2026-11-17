import GSTClassicalHodgeOmniversalSeparatorGhostCrown
import GSTClassicalHodgePiOneSourceCompositionalCorrespondenceFinale

/-!
# GST CLASSICAL HODGE — OMNIVERSAL NATIVE-ORBIT CLOSURE

This file closes the separator-ghost route against the *full* legitimate
native orbit.  The earlier origin-only pairing interface was unnecessarily
narrow: an omniversal separator already annihilates every genuine native cycle
at every source weight under every verified graded geometric program.

Consequently, once genuine correspondence geometry constructs an exact native
cycle for the separator's detected basis sheet, the identity graded program at
that same weight produces the contradiction immediately.  No return to the
codimension-zero origin, no finite global chart, and no identification of
Hodge multiplicity with native geometry is used.

The geometric input is the sharp one-source compositional correspondence
packet already isolated elsewhere in the repository.  Such a packet contains
one genuine algebraic source and, for each target sheet, one finite expression
in actual realized closed correspondences hitting that sheet by a nonzero
rational scalar.  Its `basisCycle_spec` theorem constructs the exact native
basis cycle.  The omniversal ghost then kills that cycle under `Program.id`,
while its separator field detects the same basis vector nontrivially.
-/

set_option maxHeartbeats 120000000
set_option maxRecDepth 1000000

noncomputable section

open AlgebraicGeometry

namespace GSTClassicalHodgeOmniversalNativeOrbitClosure

open GSTProjectiveOverC
open GSTGeometricRealizationStage2D
open GSTGeometricRealizationStage2F
open GSTGeometricRealizationStage2G
open GSTClassicalHodgeFiberedCosmology
open GSTClassicalHodgeGeometricCycleClassSpine
open GSTClassicalHodgeGradedGeometricProgramOrbit
open GSTClassicalHodgeOmniversalSeparatorGhostCrown
open GSTClassicalHodgePiOneSourceCompositionalCorrespondenceFinale

variable {V : SmoothProjectiveComplexScheme}
variable {H : HodgeBigradedBettiData V}

/-- A detected sheet itself certifies that its Hodge weight is live. -/
theorem hodgeWeightLive_of_omniversalGhost
    {G : GeometricCycleClassSpine V H}
    (E : OmniversalSeparatorGhost G) :
    rationalHodgeSubspace (H.hodgeBigrading E.weight) ≠ ⊥ := by
  intro hbot
  have hmem := (classicalHodgeBasis V H E.weight E.sheet).2
  rw [hbot] at hmem
  have hval :
      (classicalHodgeBasis V H E.weight E.sheet).1 = 0 := by
    simpa using hmem
  have hzero :
      classicalHodgeBasis V H E.weight E.sheet = 0 := by
    apply Subtype.ext
    exact hval
  exact (classicalHodgeBasis V H E.weight).ne_zero E.sheet hzero

/-- **FULL-NATIVE IDENTITY COLLISION.**

If genuine correspondence geometry has constructed an exact native cycle for
the sheet detected by an omniversal separator, then the separator is
impossible.  The contradiction uses the identity graded program at the same
weight, so it exploits the full quantification already present in
`kills_all_native_programs` rather than forcing the sheet through the
codimension-zero origin. -/
theorem false_of_omniversalGhost_and_oneSourceRealization
    {G : GeometricCycleClassSpine V H}
    (E : OmniversalSeparatorGhost G)
    (R : OneSourceCompositionalCorrespondenceRealization
      (V := V) (H := H) E.weight) :
    False := by
  let Z : codimensionCycles V.X E.weight := R.basisCycle E.sheet
  have hZ :
      H.cycleClass E.weight Z =
        (classicalHodgeBasis V H E.weight E.sheet).1 := by
    simpa [Z] using R.basisCycle_spec E.sheet
  have hkill :=
    E.kills_all_native_programs E.weight
      (GradedGeometricProgram.id E.weight) Z
  have hkill' :
      E.separator.detector (H.cycleClass E.weight Z) = 0 := by
    simpa [GradedGeometricProgram.cohomologyEval,
      GradedGeometricProgram.toPair,
      GradedCycleClassOperatorPair.idPair] using hkill
  rw [hZ] at hkill'
  exact E.separator.detects_basis hkill'

/-- A Pi-wide family of sharp one-source compositional correspondence packets
eliminates every omniversal separator ghost. -/
theorem no_omniversalSeparatorGhost_of_piOneSourceCompositionalCorrespondences
    (G : GeometricCycleClassSpine V H)
    (R : PiOneSourceCompositionalCorrespondenceRealization
      (V := V) (H := H)) :
    IsEmpty (OmniversalSeparatorGhost G) := by
  refine ⟨?_⟩
  intro E
  have hlive := hodgeWeightLive_of_omniversalGhost E
  let W : OneSourceCompositionalCorrespondenceRealization
      (V := V) (H := H) E.weight :=
    Classical.choice (R E.weight hlive)
  exact false_of_omniversalGhost_and_oneSourceRealization E W

/-- **OMNIVERSAL NO-GHOST HODGE FINALE.**

The exact Stage-2G Hodge statement follows by contradiction through the
completed limitless separator ghost: a hypothetical failure produces an
omniversal ghost, the live-weight correspondence packet constructs the native
cycle of its detected sheet, and the identity native program simultaneously
forces the separator read to vanish and to be nonzero. -/
theorem hodge_of_piOneSourceCompositionalCorrespondence_noGhost
    (G : GeometricCycleClassSpine V H)
    (R : PiOneSourceCompositionalCorrespondenceRealization
      (V := V) (H := H)) :
    BigradedBettiHodgeStatement V H :=
  (hodge_iff_no_omniversalSeparatorGhost G).2
    (no_omniversalSeparatorGhost_of_piOneSourceCompositionalCorrespondences G R)

/-- Elementwise contradiction form, useful for future geometry constructors:
once a single live-weight packet is available, no ghost can occupy that weight. -/
theorem no_ghost_at_weight_of_oneSourceRealization
    (G : GeometricCycleClassSpine V H)
    (q : Nat)
    (R : OneSourceCompositionalCorrespondenceRealization
      (V := V) (H := H) q) :
    ∀ E : OmniversalSeparatorGhost G, E.weight = q → False := by
  intro E hEq
  subst q
  exact false_of_omniversalGhost_and_oneSourceRealization E R

#check hodgeWeightLive_of_omniversalGhost
#check false_of_omniversalGhost_and_oneSourceRealization
#check no_omniversalSeparatorGhost_of_piOneSourceCompositionalCorrespondences
#check hodge_of_piOneSourceCompositionalCorrespondence_noGhost
#check no_ghost_at_weight_of_oneSourceRealization

#print axioms hodgeWeightLive_of_omniversalGhost
#print axioms false_of_omniversalGhost_and_oneSourceRealization
#print axioms no_omniversalSeparatorGhost_of_piOneSourceCompositionalCorrespondences
#print axioms hodge_of_piOneSourceCompositionalCorrespondence_noGhost

end GSTClassicalHodgeOmniversalNativeOrbitClosure
