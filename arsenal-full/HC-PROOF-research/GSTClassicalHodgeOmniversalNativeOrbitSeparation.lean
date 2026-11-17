import GSTClassicalHodgeOmniversalSeparatorGhostCrown
import GSTClassicalHodgeGradedGeometricOrbitAlgebra
import GSTClassicalHodgeExactClayStatement
import GSTClassicalHodgeNativeExecutablePlane

/-!
# GST CLASSICAL HODGE — OMNIVERSAL NATIVE-ORBIT SEPARATION

This file closes an ambiguity in the no-ghost strategy.

The completed fibered pairing is already nondegenerate.  The remaining question
is whether the ACTUAL graded geometric program orbit, starting at the genuine
codimension-zero fundamental cycle, contains enough states to determine every
completed probe.

Because the graded program language itself contains rational addition and
scaling, its reachable set is already a submodule.  Therefore three apparently
different formulations are the same geometric statement:

1. every genuine Hodge basis sheet is the output of one actual graded program;
2. the actual program orbit contains the entire rational Hodge fiber;
3. the actual program addresses are pairing-total against completed probes
   supported at that weight.

No Hodge conclusion, target cycle, native matrix-unit lift, or plane
materialization hypothesis is inserted in these definitions.
-/

set_option maxHeartbeats 180000000
set_option maxRecDepth 1000000

noncomputable section

open scoped BigOperators
open AlgebraicGeometry

namespace GSTClassicalHodgeOmniversalNativeOrbitSeparation

open GSTProjectiveOverC
open GSTGeometricRealizationStage2D
open GSTGeometricRealizationStage2F
open GSTGeometricRealizationStage2G
open GSTClassicalHodgeFiberedCosmology
open GSTClassicalHodgeAtomicDefectDuality
open GSTClassicalHodgeAtomicAnnihilator
open GSTClassicalHodgeLimitlessSeparatorGhost
open GSTClassicalHodgeGeometricCycleClassSpine
open GSTClassicalHodgeRankFreeArsenalIrreducibility
open GSTClassicalHodgeGradedGeometricProgramOrbit
open GSTClassicalHodgeGradedGeometricOrbitAlgebra
open GSTClassicalHodgeOmniversalSeparatorGhostCrown

variable {V : SmoothProjectiveComplexScheme}
variable {H : HodgeBigradedBettiData V}

/-- **GEOMETRIC GST PLANE COMPLETENESS.**

This is the native/program meaning of plane completeness: every genuine Hodge
basis sheet, at every weight, is reached from the canonical geometric origin by
ONE verified graded geometric program.

Unlike the intrinsic Hodge-graph plane theorem, the witness here is executable
on actual native algebraic cycles and carries an exact cycle-class commuting
square by construction. -/
def GeometricGSTPlaneCompleteness
    (G : GeometricCycleClassSpine V H) : Prop :=
  ∀ q : Nat, ∀ j : ClassicalHodgeBasisIndex V H q,
    ∃ P : GradedGeometricProgram V 0 q,
      P.cohomologyEval G (geometricOriginClass V H) =
        (classicalHodgeBasis V H q j).1

/-- Geometric plane completeness puts every basis vector in the intrinsic
reachable module. -/
theorem basis_mem_orbit_of_geometricPlane
    (G : GeometricCycleClassSpine V H)
    (hplane : GeometricGSTPlaneCompleteness G)
    (q : Nat)
    (j : ClassicalHodgeBasisIndex V H q) :
    (classicalHodgeBasis V H q j).1 ∈ geometricProgramOrbitModule G q := by
  change (classicalHodgeBasis V H q j).1 ∈ geometricProgramOrbitSet G q
  obtain ⟨P, hP⟩ := hplane q j
  exact ⟨P, hP.symm⟩

/-- Every genuine Hodge state belongs to the actual graded-program orbit once
all basis sheets are individually program-reachable. -/
theorem orbitCyclic_of_geometricPlane
    (G : GeometricCycleClassSpine V H)
    (hplane : GeometricGSTPlaneCompleteness G) :
    GradedGeometricOrbitModuleCyclic G := by
  intro q alpha halpha
  let alphaH : ClassicalHodgeFiber V H q := ⟨alpha, halpha⟩
  rw [show alpha =
      ∑ j ∈ ((classicalHodgeBasis V H q).repr alphaH).support,
        ((classicalHodgeBasis V H q).repr alphaH j) •
          (classicalHodgeBasis V H q j).1 by
    exact congrArg Subtype.val ((classicalHodgeBasis V H q).sum_repr alphaH)]
  apply Submodule.sum_mem
  intro j hj
  exact (geometricProgramOrbitModule G q).smul_mem
    ((classicalHodgeBasis V H q).repr alphaH j)
    (basis_mem_orbit_of_geometricPlane G hplane q j)

/-- Conversely, orbit cyclicity gives one ACTUAL program for every basis sheet,
because the program orbit is already a submodule rather than merely a span. -/
theorem geometricPlane_of_orbitCyclic
    (G : GeometricCycleClassSpine V H)
    (hcyclic : GradedGeometricOrbitModuleCyclic G) :
    GeometricGSTPlaneCompleteness G := by
  intro q j
  have hmem :
      (classicalHodgeBasis V H q j).1 ∈ geometricProgramOrbitModule G q :=
    hcyclic q (classicalHodgeBasis V H q j).2
  change (classicalHodgeBasis V H q j).1 ∈ geometricProgramOrbitSet G q at hmem
  rcases hmem with ⟨P, hP⟩
  exact ⟨P, hP.symm⟩

/-- **FIRST EXACT IDENTIFICATION.**
Program-level geometric GST plane completeness is exactly graded native-orbit
cyclicity.  Thus these cannot drift into two different future assumptions. -/
theorem geometricPlane_iff_gradedOrbitCyclic
    (G : GeometricCycleClassSpine V H) :
    GeometricGSTPlaneCompleteness G ↔
      GradedGeometricOrbitModuleCyclic G := by
  constructor
  · exact orbitCyclic_of_geometricPlane G
  · exact geometricPlane_of_orbitCyclic G

/-- One program hitting one basis sheet gives its exact fibered address. -/
theorem nativeProgramFiberedAddress_eq_basis
    (G : GeometricCycleClassSpine V H)
    {q : Nat}
    {j : ClassicalHodgeBasisIndex V H q}
    (P : GradedGeometricProgram V 0 q)
    (hP :
      P.cohomologyEval G (geometricOriginClass V H) =
        (classicalHodgeBasis V H q j).1) :
    nativeProgramFiberedAddress G P =
      Finsupp.single
        (⟨q,j⟩ : FiberedHodgeIndex V H) 1 := by
  unfold nativeProgramFiberedAddress nativeProgramHodgeState
  rw [show
      (⟨P.cohomologyEval G (geometricOriginClass V H), by
          unfold geometricOriginClass
          exact P.cohomologyEval_mem_hodge G
            (GSTClassicalHodgeCodimensionZeroFundamentalCycle
              .codimensionZeroFundamentalCycle V)⟩ :
        ClassicalHodgeFiber V H q) =
      classicalHodgeBasis V H q j by
    apply Subtype.ext
    exact hP]
  exact fiberedWeightCoordinates_basis V H q j

/-- **GEOMETRIC PLANE ⇒ PAIRING TOTALITY.**

A completed probe supported at weight q and invisible to every verified native
program must vanish coordinate-by-coordinate: geometric plane completeness
provides a program whose address is each Kronecker basis atom. -/
theorem nativeOrbitPairingTotal_of_geometricPlane
    (G : GeometricCycleClassSpine V H)
    (hplane : GeometricGSTPlaneCompleteness G) :
    OmniversalNativeOrbitPairingTotal G := by
  intro q g hsupp hkill
  funext s
  rcases s with ⟨r,j⟩
  by_cases hr : r = q
  · subst r
    obtain ⟨P, hP⟩ := hplane q j
    have hk := hkill P
    rw [nativeProgramFiberedAddress_eq_basis G P hP] at hk
    simpa [fiberedPairing_single_left] using hk
  · exact hsupp ⟨r,j⟩ hr

/-- The module-cyclicity formulation gives pairing totality through the exact
geometric-plane equivalence. -/
theorem nativeOrbitPairingTotal_of_gradedOrbitCyclic
    (G : GeometricCycleClassSpine V H)
    (hcyclic : GradedGeometricOrbitModuleCyclic G) :
    OmniversalNativeOrbitPairingTotal G :=
  nativeOrbitPairingTotal_of_geometricPlane G
    (geometricPlane_of_orbitCyclic G hcyclic)

/-- **PAIRING TOTALITY ⇒ ACTUAL ORBIT CYCLICITY.**

This is the converse hidden in the old no-ghost proposal.  If the genuine
program orbit missed even one Hodge vector, quotient separation would produce
a nonzero rational functional annihilating the entire orbit.  Its canonical
completed fibered probe is supported at that one weight and pairs to zero with
every native program address, contradicting pairing totality.

Thus pairing totality is not a mysterious additional infinity principle: it is
exactly the dual form of executable geometric orbit completeness. -/
theorem gradedOrbitCyclic_of_nativeOrbitPairingTotal
    (G : GeometricCycleClassSpine V H)
    (htotal : OmniversalNativeOrbitPairingTotal G) :
    GradedGeometricOrbitModuleCyclic G := by
  intro q alpha halpha
  by_contra hnot
  obtain ⟨ell, hell, hdetect⟩ :=
    exists_linearFunctional_separating_submodule
      (geometricProgramOrbitModule G q) alpha hnot
  let g : FiberedCompletedAddress V H :=
    separatorFiberedProbe (V := V) (H := H) q ell
  have hsupp :
      ∀ s : FiberedHodgeIndex V H, s.1 ≠ q → g s = 0 := by
    intro s hs
    rcases s with ⟨r,j⟩
    exact separatorFiberedProbe_at_other_weight
      (V := V) (H := H) q r hs ell j
  have hkill :
      ∀ P : GradedGeometricProgram V 0 q,
        fiberedPairing (nativeProgramFiberedAddress G P) g = 0 := by
    intro P
    have horbit :
        P.cohomologyEval G (geometricOriginClass V H) ∈
          geometricProgramOrbitModule G q := by
      change
        P.cohomologyEval G (geometricOriginClass V H) ∈
          geometricProgramOrbitSet G q
      exact ⟨P, rfl⟩
    have hzero :
        ell (P.cohomologyEval G (geometricOriginClass V H)) = 0 :=
      hell _ horbit
    let a : ClassicalHodgeFiber V H q :=
      nativeProgramHodgeState G P
    have hp :=
      fiberedPairing_separatorProbe
        (V := V) (H := H) q ell a
    simpa [g, a, nativeProgramFiberedAddress, nativeProgramHodgeState]
      using hp.trans hzero
  have hg : g = 0 := htotal q g hsupp hkill
  let alphaH : ClassicalHodgeFiber V H q := ⟨alpha, halpha⟩
  have hp :=
    fiberedPairing_separatorProbe
      (V := V) (H := H) q ell alphaH
  have hz : ell alpha = 0 := by
    rw [hg] at hp
    simpa [g, alphaH, fiberedPairing] using hp
  exact hdetect hz

/-- **SECOND EXACT IDENTIFICATION.**
The old handwritten "native orbit is pairing-determining" law is exactly the
dual statement that the executable geometric orbit fills every Hodge fiber. -/
theorem nativeOrbitPairingTotal_iff_gradedOrbitCyclic
    (G : GeometricCycleClassSpine V H) :
    OmniversalNativeOrbitPairingTotal G ↔
      GradedGeometricOrbitModuleCyclic G := by
  constructor
  · exact gradedOrbitCyclic_of_nativeOrbitPairingTotal G
  · exact nativeOrbitPairingTotal_of_gradedOrbitCyclic G

/-- **FULL THREE-WAY IDENTIFICATION.**
Executable geometric plane completeness, graded native-orbit cyclicity, and
completed-probe pairing totality are three presentations of the same GST
geometric completeness law. -/
theorem geometricPlane_iff_nativeOrbitPairingTotal
    (G : GeometricCycleClassSpine V H) :
    GeometricGSTPlaneCompleteness G ↔
      OmniversalNativeOrbitPairingTotal G :=
  (geometricPlane_iff_gradedOrbitCyclic G).trans
    (nativeOrbitPairingTotal_iff_gradedOrbitCyclic G).symm

/-- **NO-GHOST LANDING FROM GEOMETRIC PLANE COMPLETENESS.** -/
theorem no_omniversalGhost_of_geometricPlane
    (G : GeometricCycleClassSpine V H)
    (hplane : GeometricGSTPlaneCompleteness G) :
    IsEmpty (OmniversalSeparatorGhost G) :=
  no_omniversalSeparatorGhost_of_nativeOrbitPairingTotal G
    (nativeOrbitPairingTotal_of_geometricPlane G hplane)

/-- **GEOMETRIC GST PLANE COMPLETENESS ⇒ EXACT STAGE-2G HODGE.**

This is the completed native version of the plane theorem: because its edges
are actual graded geometric programs, not abstract Hodge graph edges, every
basis sheet is an actual cycle-class value and the no-ghost contradiction
closes. -/
theorem hodge_of_geometricGSTPlaneCompleteness
    (G : GeometricCycleClassSpine V H)
    (hplane : GeometricGSTPlaneCompleteness G) :
    BigradedBettiHodgeStatement V H :=
  hodge_of_nativeOrbitPairingTotal G
    (nativeOrbitPairingTotal_of_geometricPlane G hplane)

/-- Constructive elementwise form: every rational Hodge class receives an
actual native codimension-q cycle once the geometric GST plane is complete. -/
theorem nativeCycle_of_geometricGSTPlaneCompleteness
    (G : GeometricCycleClassSpine V H)
    (hplane : GeometricGSTPlaneCompleteness G)
    (q : Nat)
    (alpha : RationalSingularCohomology H.analytification (2 * q))
    (halpha : alpha ∈ rationalHodgeSubspace (H.hodgeBigrading q)) :
    ∃ Z : codimensionCycles V.X q, H.cycleClass q Z = alpha :=
  hodge_of_geometricGSTPlaneCompleteness G hplane q alpha halpha

#check GeometricGSTPlaneCompleteness
#check basis_mem_orbit_of_geometricPlane
#check geometricPlane_iff_gradedOrbitCyclic
#check nativeProgramFiberedAddress_eq_basis
#check nativeOrbitPairingTotal_of_geometricPlane
#check nativeOrbitPairingTotal_of_gradedOrbitCyclic
#check gradedOrbitCyclic_of_nativeOrbitPairingTotal
#check nativeOrbitPairingTotal_iff_gradedOrbitCyclic
#check geometricPlane_iff_nativeOrbitPairingTotal
#check no_omniversalGhost_of_geometricPlane
#check hodge_of_geometricGSTPlaneCompleteness

/-- Exact Clay-style rational-algebraic landing from executable geometric GST
plane completeness. -/
theorem everyHodgeClassIsRationalAlgebraic_of_geometricGSTPlaneCompleteness
    (G : GeometricCycleClassSpine V H)
    (hplane : GeometricGSTPlaneCompleteness G) :
    GSTClassicalHodgeExactClayStatement.EveryHodgeClassIsRationalAlgebraic H :=
  (GSTClassicalHodgeExactClayStatement.everyHodgeClassIsRationalAlgebraic_iff_stage2G H).2
    (hodge_of_geometricGSTPlaneCompleteness G hplane)

/-- Exact finite-rational-combination wording of the same geometric-plane
landing. -/
theorem everyHodgeClassIsFiniteRationalCombination_of_geometricGSTPlaneCompleteness
    (G : GeometricCycleClassSpine V H)
    (hplane : GeometricGSTPlaneCompleteness G) :
    GSTClassicalHodgeExactClayStatement.EveryHodgeClassIsFiniteRationalCombination H :=
  (GSTClassicalHodgeExactClayStatement.rationalAlgebraic_iff_finiteRationalCombination H).1
    (everyHodgeClassIsRationalAlgebraic_of_geometricGSTPlaneCompleteness G hplane)


/-- Geometric executable plane completeness supplies the exact basis-cycle
normal form, so there is no separate basis-algebraicity premise below it. -/
theorem basisCycleSupply_of_geometricGSTPlaneCompleteness
    (G : GeometricCycleClassSpine V H)
    (hplane : GeometricGSTPlaneCompleteness G) :
    GSTClassicalHodgeNativeExecutablePlane.HodgeBasisCycleSupply
      (V := V) (H := H) := by
  intro q j
  obtain ⟨P, hP⟩ := hplane q j
  let Z : codimensionCycles V.X q := P.cycleEval G
    GSTClassicalHodgeCodimensionZeroFundamentalCycle.codimensionZeroFundamentalCycle V
  refine ⟨Z, ?_⟩
  have hnat :=
    P.cycleClass_cycleEval G
      GSTClassicalHodgeCodimensionZeroFundamentalCycle.codimensionZeroFundamentalCycle V
  simpa [Z, geometricOriginClass] using hnat.trans hP

/-- **COMPLETION HIERARCHY RECEIPT.**
The executable geometric GST plane lands simultaneously in the basis-cycle
normal form, Stage-2G Hodge, and the exact finite-rational Clay formulation.
The middle basis-cycle statement is already proved elsewhere to be equivalent
to Hodge, so it cannot be reused as a lower completeness axiom. -/
theorem geometricGSTPlane_completion_hierarchy
    (G : GeometricCycleClassSpine V H)
    (hplane : GeometricGSTPlaneCompleteness G) :
    GSTClassicalHodgeNativeExecutablePlane.HodgeBasisCycleSupply
        (V := V) (H := H)
    ∧ BigradedBettiHodgeStatement V H
    ∧ GSTClassicalHodgeExactClayStatement.EveryHodgeClassIsFiniteRationalCombination H := by
  refine ⟨basisCycleSupply_of_geometricGSTPlaneCompleteness G hplane,
    hodge_of_geometricGSTPlaneCompleteness G hplane, ?_⟩
  exact
    everyHodgeClassIsFiniteRationalCombination_of_geometricGSTPlaneCompleteness
      G hplane

/-- **WEAK-SPINE TOTALITY NO-GO.**
Native-orbit pairing totality cannot be derived uniformly from the fields of
`GeometricCycleClassSpine` alone.  The repository's zero-cycle-class spine
satisfies those fields while failing Stage-2G whenever a nonzero Hodge class
exists.  If every such spine were pairing-total, the existing no-ghost landing
would force Hodge in that countermodel. -/
theorem weakSpine_cannot_force_nativeOrbitPairingTotal
    (H0 : HodgeBigradedBettiData V)
    (p : Nat)
    (alpha : RationalSingularCohomology H0.analytification (2 * p))
    (halpha : alpha ∈ rationalHodgeSubspace (H0.hodgeBigrading p))
    (halpha0 : alpha ≠ 0) :
    ¬ (∀ G0 : GeometricCycleClassSpine V
          (GSTClassicalHodgeStage2GSemanticRigidity.zeroCycleClassData H0),
        OmniversalNativeOrbitPairingTotal G0) := by
  intro htotal
  let G0 : GeometricCycleClassSpine V
      (GSTClassicalHodgeStage2GSemanticRigidity.zeroCycleClassData H0) :=
    zeroCycleClassSpine H0
  have hhodge :
      BigradedBettiHodgeStatement V
        (GSTClassicalHodgeStage2GSemanticRigidity.zeroCycleClassData H0) :=
    hodge_of_nativeOrbitPairingTotal G0 (htotal G0)
  exact
    (GSTClassicalHodgeStage2GSemanticRigidity.not_bigradedBettiHodge_zeroCycleClass
      H0 p alpha halpha halpha0) hhodge

#check weakSpine_cannot_force_nativeOrbitPairingTotal
#check nativeCycle_of_geometricGSTPlaneCompleteness
#check basisCycleSupply_of_geometricGSTPlaneCompleteness
#check geometricGSTPlane_completion_hierarchy
#check everyHodgeClassIsRationalAlgebraic_of_geometricGSTPlaneCompleteness
#check everyHodgeClassIsFiniteRationalCombination_of_geometricGSTPlaneCompleteness

#print axioms weakSpine_cannot_force_nativeOrbitPairingTotal
#print axioms geometricPlane_iff_gradedOrbitCyclic
#print axioms nativeOrbitPairingTotal_of_geometricPlane
#print axioms gradedOrbitCyclic_of_nativeOrbitPairingTotal
#print axioms nativeOrbitPairingTotal_iff_gradedOrbitCyclic
#print axioms geometricPlane_iff_nativeOrbitPairingTotal
#print axioms hodge_of_geometricGSTPlaneCompleteness
#print axioms basisCycleSupply_of_geometricGSTPlaneCompleteness
#print axioms geometricGSTPlane_completion_hierarchy
#print axioms everyHodgeClassIsRationalAlgebraic_of_geometricGSTPlaneCompleteness
#print axioms everyHodgeClassIsFiniteRationalCombination_of_geometricGSTPlaneCompleteness

end GSTClassicalHodgeOmniversalNativeOrbitSeparation
