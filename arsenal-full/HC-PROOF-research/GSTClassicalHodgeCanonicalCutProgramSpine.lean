import GSTClassicalHodgeGradedCorrespondenceProgramOrbit
import GSTClassicalHodgeLimitlessProjectiveLefschetzTower
import GSTClassicalHodgeHandwrittenPiCorrespondenceProgramLanding

/-!
# GST CLASSICAL HODGE — CANONICAL PRINCIPAL-CUT PROGRAM SPINE

The handwritten Pi correspondence landing previously accepted an arbitrary
full correspondence program `P0 : 0 -> p` and only required its origin image
to be nonzero.  The GST/projective geometry already contains a canonical such
program: repeatedly apply the genuine principal-cut constructor

  cut 0 ; cut 1 ; ... ; cut (p-1).

This file makes that vertical path literal.  Its native execution on the
codimension-zero fundamental cycle is exactly the previously constructed
`projectiveCutTower`.  Consequently its cohomological origin image is exactly
the genuine cycle class of that same tower by the master naturality square.

No free source program remains.  The only vertical nonvanishing statement left
is therefore the concrete equation

  cycleClass p (projectiveCutTower V p) != 0,

which is precisely the point at which the projective tower must be identified
with the nonzero limitless GST/Lefschetz tower.
-/

set_option maxHeartbeats 140000000
set_option maxRecDepth 1000000

noncomputable section

open AlgebraicGeometry

namespace GSTClassicalHodgeCanonicalCutProgramSpine

open GSTProjectiveOverC
open GSTGeometricRealizationStage2D
open GSTGeometricRealizationStage2G
open GSTClassicalHodgeFiberedCosmology
open GSTClassicalHodgeGeometricCycleClassSpine
open GSTClassicalHodgeCodimensionZeroFundamentalCycle
open GSTClassicalHodgePrincipalCutSuccessorOperator
open GSTClassicalHodgeLimitlessProjectiveLefschetzTower
open GSTClassicalHodgeGradedCorrespondenceProgramOrbit
open GSTClassicalHodgeGradedCorrespondenceProgramOrbit.GradedCorrespondenceProgram
open GSTClassicalHodgeHandwrittenPiCorrespondenceProgramLanding
open GSTClassicalHodgeOmniverseStrictEventStability

variable {V : SmoothProjectiveComplexScheme}
variable {H : HodgeBigradedBettiData V}

/-- The canonical verified vertical program from weight zero to weight `p`:
exactly one genuine principal cut at each successive codimension. -/
noncomputable def canonicalCutProgram :
    (p : Nat) -> GradedCorrespondenceProgram V H 0 p
  | 0 => .id 0
  | p + 1 => .comp (canonicalCutProgram p) (.cut p)

/-- The next canonical program step executes natively by the actual
geometry-built successor operator. -/
theorem canonicalCutProgram_cycleEval_succ
    (G : GeometricCycleClassSpine V H)
    (p : Nat)
    (Z : codimensionCycles V.X 0) :
    (canonicalCutProgram (V := V) (H := H) (p + 1)).cycleEval G Z =
      successorNativeOperator V p
        ((canonicalCutProgram (V := V) (H := H) p).cycleEval G Z) := by
  change
    (G.principalCutPair p).cycleOperator
        ((canonicalCutProgram (V := V) (H := H) p).cycleEval G Z) = _
  rw [G.principalCutPair_native p]

/-- **CANONICAL PROGRAM = PROJECTIVE CUT TOWER, NATIVELY.**
There is no arbitrary `P0`: the verified full-program execution is exactly the
existing recursive projective principal-cut tower. -/
theorem canonicalCutProgram_origin_cycle
    (G : GeometricCycleClassSpine V H) :
    forall p : Nat,
      (canonicalCutProgram (V := V) (H := H) p).cycleEval G
          (codimensionZeroFundamentalCycle V) =
        projectiveCutTower V p := by
  intro p
  induction p with
  | zero =>
      simp [canonicalCutProgram, projectiveCutTower]
  | succ p ih =>
      rw [canonicalCutProgram_cycleEval_succ G p]
      rw [ih]
      exact (projectiveCutTower_succ V p).symm

/-- **COHOMOLOGICAL ORIGIN = ACTUAL CUT-TOWER CLASS.**
Master cycle-class naturality identifies the canonical program's cohomological
output with the cycle class of the genuine projective cut tower. -/
theorem canonicalCutProgram_origin_class
    (G : GeometricCycleClassSpine V H)
    (p : Nat) :
    (canonicalCutProgram (V := V) (H := H) p).cohomologyEval G
        (correspondenceGeometricOriginClass V H) =
      H.cycleClass p (projectiveCutTower V p) := by
  have hnat :=
    (canonicalCutProgram (V := V) (H := H) p).cycleClass_cycleEval G
      (codimensionZeroFundamentalCycle V)
  rw [canonicalCutProgram_origin_cycle G p] at hnat
  simpa [correspondenceGeometricOriginClass] using hnat.symm

/-- The former arbitrary-program nonvanishing premise is now literally the
nonvanishing of the canonical projective tower's cycle class. -/
theorem canonicalCutProgram_origin_ne_zero_iff
    (G : GeometricCycleClassSpine V H)
    (p : Nat) :
    (canonicalCutProgram (V := V) (H := H) p).cohomologyEval G
        (correspondenceGeometricOriginClass V H) != 0
      <-> H.cycleClass p (projectiveCutTower V p) != 0 := by
  rw [canonicalCutProgram_origin_class G p]

/-- Canonical same-weight synchronized source extracted from the actual
principal-cut tower.  No arbitrary source program is supplied. -/
noncomputable def canonicalCutOrbitSeed
    (G : GeometricCycleClassSpine V H)
    (p : Nat)
    (hne : H.cycleClass p (projectiveCutTower V p) != 0) :=
  fullOrbitSeedOfProgram G
    (canonicalCutProgram (V := V) (H := H) p)
    ((canonicalCutProgram_origin_ne_zero_iff G p).2 hne)

/-- **HANDWRITTEN LANDING WITH THE FREE `P0` REMOVED.**
Once the concrete tower class is nonzero, source-specific strict materialization
of exactly the GST branches fired from this canonical source reconstructs an
arbitrary target Hodge class by the existing handwritten finite collapse. -/
theorem native_cycle_of_canonicalCut_strict_branches
    (G : GeometricCycleClassSpine V H)
    (p : Nat)
    (hne : H.cycleClass p (projectiveCutTower V p) != 0)
    (hstrict : forall j : ClassicalHodgeBasisIndex V H p,
      StrictlyMaterializedBranch
        (derivedSourceNode G
          (canonicalCutProgram (V := V) (H := H) p)
          ((canonicalCutProgram_origin_ne_zero_iff G p).2 hne))
        (derivedTargetNode G
          (canonicalCutProgram (V := V) (H := H) p)
          ((canonicalCutProgram_origin_ne_zero_iff G p).2 hne) j))
    (alpha : ClassicalHodgeFiber V H p) :
    exists Z : codimensionCycles V.X p,
      H.cycleClass p Z = alpha.1 := by
  exact native_cycle_of_sourceSpecific_strict_branches
    G
    (canonicalCutProgram (V := V) (H := H) p)
    ((canonicalCutProgram_origin_ne_zero_iff G p).2 hne)
    hstrict alpha

#check canonicalCutProgram
#check canonicalCutProgram_cycleEval_succ
#check canonicalCutProgram_origin_cycle
#check canonicalCutProgram_origin_class
#check canonicalCutProgram_origin_ne_zero_iff
#check canonicalCutOrbitSeed
#check native_cycle_of_canonicalCut_strict_branches

#print axioms canonicalCutProgram_origin_cycle
#print axioms canonicalCutProgram_origin_class
#print axioms canonicalCutProgram_origin_ne_zero_iff
#print axioms native_cycle_of_canonicalCut_strict_branches

end GSTClassicalHodgeCanonicalCutProgramSpine
