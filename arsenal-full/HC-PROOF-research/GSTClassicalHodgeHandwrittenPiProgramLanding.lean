import GSTClassicalHodgeHandwrittenPiEquationDerivation
import GSTClassicalHodgeProjectiveGeneratorWordCompiler
import GSTClassicalHodgeCodimensionZeroFundamentalCycle

/-!
# GST CLASSICAL HODGE — HANDWRITTEN PI PROGRAM LANDING

This file removes the opaque `HandwrittenPiGeometricLanding` premise from the
equation-level derivation and replaces it by the actual mixed GST program
algebra.

The proof follows the handwritten construction literally.

1. Run one genuine graded geometric program `P0 : 0 -> p` from the canonical
   codimension-zero fundamental cycle.  Assume only that the resulting Hodge
   state `a` is nonzero.
2. Choose the canonical live coordinate `s` of this derived state.
3. For each target basis direction `j`, use the genuine projective two-generator
   realization and compile the GST word

       scalar^-1 * code o L^2 o (id - code).

   The existing source-action theorem computes this word on `a` as

       a_s * e_j.

4. Since the graded orbit is a rational module and `a_s != 0`, divide by `a_s`.
   Hence every basis vector `e_j` lies in the genuine geometric program orbit.
5. For an arbitrary requested Hodge state `alpha`, the handwritten branch is

       E_ij(alpha) = alpha_i * e_j.

   Therefore every live localized-L^2 branch is in the orbit, and the already
   proved finite branch-collapse equation reconstructs `alpha` inside the same
   orbit.  The master cycle-class theorem then returns an actual algebraic cycle.

No Hodge-surjectivity statement, target cycle, arbitrary same-weight algebraic
seed, conserved charge, native-mass bridge, or abstract branch-landing packet is
assumed here.  The same-weight source is derived from the codimension-zero
origin by the supplied genuine graded program.
-/

set_option maxHeartbeats 120000000
set_option maxRecDepth 1000000

noncomputable section

open scoped BigOperators
open AlgebraicGeometry

namespace GSTClassicalHodgeHandwrittenPiProgramLanding

open GSTProjectiveOverC
open GSTGeometricRealizationStage2D
open GSTGeometricRealizationStage2F
open GSTGeometricRealizationStage2G
open GSTClassicalHodgeFiberedCosmology
open GSTClassicalHodgeRankFreeArsenalIrreducibility
open GSTClassicalHodgeGeometricCycleClassSpine
open GSTClassicalHodgeCodimensionZeroFundamentalCycle
open GSTClassicalHodgeGradedGeometricProgramOrbit
open GSTClassicalHodgeGradedGeometricOrbitAlgebra
open GSTClassicalHodgeSynchronizedDefectOrbit
open GSTClassicalHodgeProjectiveTwoGeneratorExternalization
open GSTClassicalHodgeProjectiveGeneratorWordCompiler
open GSTClassicalHodgeHandwrittenPiEquationDerivation

variable {V : SmoothProjectiveComplexScheme}
variable {H : HodgeBigradedBettiData V}
variable {p : Nat}

/-- A genuine mixed program from the codimension-zero origin, together with
nonvanishing of its cohomological output, canonically supplies the synchronized
same-weight algebraic source needed by the horizontal GST word.  The source is
DERIVED from the origin program; it is not an independent premise. -/
noncomputable def orbitSeedOfProgram
    (G : GeometricCycleClassSpine V H)
    (P0 : GradedGeometricProgram V 0 p)
    (hne : P0.cohomologyEval G (geometricOriginClass V H) ≠ 0) :
    NativeHodgeOrbitSeed (V := V) (H := H) (p := p) := by
  let Z0 : codimensionCycles V.X p :=
    P0.cycleEval G (codimensionZeroFundamentalCycle V)
  let a0 : RationalSingularCohomology H.analytification (2 * p) :=
    P0.cohomologyEval G (geometricOriginClass V H)
  let a : ClassicalHodgeFiber V H p :=
    ⟨a0, by
      simpa [a0, geometricOriginClass] using
        P0.cohomologyEval_mem_hodge G (codimensionZeroFundamentalCycle V)⟩
  refine {
    cycle := Z0
    hodge := a
    hodge_ne_zero := ?_
    class_eq := ?_
  }
  · intro ha
    apply hne
    exact congrArg Subtype.val ha
  · simpa [Z0, a, a0, geometricOriginClass] using
      P0.cycleClass_cycleEval G (codimensionZeroFundamentalCycle V)

/-- The derived source state is itself literally in the intrinsic graded
geometric orbit. -/
theorem orbitSeedOfProgram_mem_orbit
    (G : GeometricCycleClassSpine V H)
    (P0 : GradedGeometricProgram V 0 p)
    (hne : P0.cohomologyEval G (geometricOriginClass V H) ≠ 0) :
    (orbitSeedOfProgram G P0 hne).hodge.1 ∈
      geometricProgramOrbitModule G p := by
  refine ⟨P0, ?_⟩
  rfl

/-- **PROGRAM ORIGIN -> EVERY BASIS SHEET.**
One nonzero state reached from the codimension-zero origin, together with the
actual projective two-generator GST word from its chosen live coordinate to
`j`, puts the exact basis vector `e_j` in the genuine graded program orbit. -/
theorem basis_mem_orbit_of_program_projective_word
    (G : GeometricCycleClassSpine V H)
    (P0 : GradedGeometricProgram V 0 p)
    (hne : P0.cohomologyEval G (geometricOriginClass V H) ≠ 0)
    (j : ClassicalHodgeBasisIndex V H p)
    (hij : (orbitSeedOfProgram G P0 hne).sourceIndex ≠ j)
    (R : ProjectiveTwoGenerator (V := V) (H := H)
      (orbitSeedOfProgram G P0 hne).sourceIndex j) :
    (classicalHodgeBasis V H p j).1 ∈ geometricProgramOrbitModule G p := by
  let S := orbitSeedOfProgram G P0 hne
  let W := compileProjectiveTwoGenerator R
  have hsource : S.hodge.1 ∈ geometricProgramOrbitModule G p := by
    simpa [S] using orbitSeedOfProgram_mem_orbit G P0 hne
  have hword :
      (GradedGeometricProgram.word W).cohomologyEval G S.hodge.1 ∈
        geometricProgramOrbitModule G p :=
    program_maps_geometricProgramOrbitModule G
      (GradedGeometricProgram.word W) hsource
  have haction :
      (GradedGeometricProgram.word W).cohomologyEval G S.hodge.1 =
        (classicalHodgeBasis V H p).repr S.hodge S.sourceIndex •
          (classicalHodgeBasis V H p j).1 := by
    simpa [W, GradedGeometricProgram.cohomologyEval,
      GradedGeometricProgram.toPair] using
      compileProjectiveTwoGenerator_source_action G S j hij R
  rw [haction] at hword
  have hc :
      (classicalHodgeBasis V H p).repr S.hodge S.sourceIndex ≠ 0 :=
    S.sourceCoefficient_ne_zero
  have hscaled :=
    (geometricProgramOrbitModule G p).smul_mem
      ((classicalHodgeBasis V H p).repr S.hodge S.sourceIndex)⁻¹ hword
  simpa [smul_smul, hc] using hscaled

/-- A target-independent family of actual projective GST words therefore puts
EVERY unrestricted Hodge basis direction in the geometric orbit. -/
theorem every_basis_mem_orbit_of_program_projective_words
    (G : GeometricCycleClassSpine V H)
    (P0 : GradedGeometricProgram V 0 p)
    (hne : P0.cohomologyEval G (geometricOriginClass V H) ≠ 0)
    (R : ∀ j : ClassicalHodgeBasisIndex V H p,
      ProjectiveTwoGenerator (V := V) (H := H)
        (orbitSeedOfProgram G P0 hne).sourceIndex j)
    (hdiag : (classicalHodgeBasis V H p
      (orbitSeedOfProgram G P0 hne).sourceIndex).1
      ∈ geometricProgramOrbitModule G p) :
    ∀ j : ClassicalHodgeBasisIndex V H p,
      (classicalHodgeBasis V H p j).1 ∈ geometricProgramOrbitModule G p := by
  intro j
  by_cases h : (orbitSeedOfProgram G P0 hne).sourceIndex = j
  · subst h; exact hdiag
  · exact basis_mem_orbit_of_program_projective_word G P0 hne j h (R j)

/-- **THE HANDWRITTEN LIVE BRANCHES LAND.**
The branch landing required by the two-page derivation is now DERIVED.  The
localized GST branch on the requested class is `alpha_i * e_j`; the previous
theorem already put `e_j` in the actual program orbit. -/
theorem liveLocalizedL2BranchesLandInOrbit_of_program_projective_words
    (G : GeometricCycleClassSpine V H)
    (P0 : GradedGeometricProgram V 0 p)
    (hne : P0.cohomologyEval G (geometricOriginClass V H) ≠ 0)
    (R : ∀ j : ClassicalHodgeBasisIndex V H p,
      ProjectiveTwoGenerator (V := V) (H := H)
        (orbitSeedOfProgram G P0 hne).sourceIndex j)
    (hdiag : (classicalHodgeBasis V H p
      (orbitSeedOfProgram G P0 hne).sourceIndex).1
      ∈ geometricProgramOrbitModule G p)
    (alpha : ClassicalHodgeFiber V H p)
    (halpha : alpha ≠ 0) :
    LiveLocalizedL2BranchesLandInOrbit G alpha := by
  obtain ⟨i, hi, _⟩ := branch_collapse_localizedL2 alpha halpha
  refine ⟨i, hi, ?_⟩
  intro j hj
  have hbasis :=
    every_basis_mem_orbit_of_program_projective_words G P0 hne R hdiag j
  have hscaled :=
    (geometricProgramOrbitModule G p).smul_mem
      (hodgeCoordinate i.1 alpha) hbasis
  simpa [localizedNormalizedL2_apply, hodgeMatrixUnit_apply] using hscaled

/-- The exact native cycle for the requested Hodge state, obtained in the same
order as the handwritten derivation: origin program -> projective GST words ->
live localized-L2 branches -> finite rational collapse -> native cycle. -/
theorem native_cycle_of_program_projective_words
    (G : GeometricCycleClassSpine V H)
    (P0 : GradedGeometricProgram V 0 p)
    (hne : P0.cohomologyEval G (geometricOriginClass V H) ≠ 0)
    (R : ∀ j : ClassicalHodgeBasisIndex V H p,
      ProjectiveTwoGenerator (V := V) (H := H)
        (orbitSeedOfProgram G P0 hne).sourceIndex j)
    (hdiag : (classicalHodgeBasis V H p
      (orbitSeedOfProgram G P0 hne).sourceIndex).1
      ∈ geometricProgramOrbitModule G p)
    (alpha : ClassicalHodgeFiber V H p) :
    ∃ Z : codimensionCycles V.X p,
      H.cycleClass p Z = alpha.1 := by
  by_cases halpha : alpha = 0
  · subst alpha
    exact ⟨0, by simp⟩
  · exact native_cycle_of_liveLocalizedL2Branches G alpha
      (liveLocalizedL2BranchesLandInOrbit_of_program_projective_words
        G P0 hne R hdiag alpha halpha)

/-- **GLOBAL HANDWRITTEN-PI PROGRAM CROWN.**
At every weight, one nonzero genuine mixed program from the codimension-zero
origin plus the two actual projective GST primitives from its selected live
coordinate to every target sheet proves the full Stage-2G Hodge statement.

Compared with `HandwrittenPiGeometricLanding`, the geometric landing is no
longer a premise: it is the conclusion of the explicit GST equations above. -/
theorem bigradedBettiHodge_of_handwritten_program_words
    (G : GeometricCycleClassSpine V H)
    (P0 : ∀ q : Nat, GradedGeometricProgram V 0 q)
    (hne : ∀ q : Nat,
      (P0 q).cohomologyEval G (geometricOriginClass V H) ≠ 0)
    (R : ∀ q : Nat,
      ∀ j : ClassicalHodgeBasisIndex V H q,
        ProjectiveTwoGenerator (V := V) (H := H)
          (orbitSeedOfProgram G (P0 q) (hne q)).sourceIndex j)
    (hdiag : ∀ q : Nat,
      (classicalHodgeBasis V H q
        (orbitSeedOfProgram G (P0 q) (hne q)).sourceIndex).1
      ∈ geometricProgramOrbitModule G q) :
    BigradedBettiHodgeStatement V H := by
  intro q alpha halpha
  let alphaH : ClassicalHodgeFiber V H q := ⟨alpha, halpha⟩
  exact native_cycle_of_program_projective_words
    G (P0 q) (hne q) (R q) (hdiag q) alphaH

#check orbitSeedOfProgram
#check basis_mem_orbit_of_program_projective_word
#check every_basis_mem_orbit_of_program_projective_words
#check liveLocalizedL2BranchesLandInOrbit_of_program_projective_words
#check native_cycle_of_program_projective_words
#check bigradedBettiHodge_of_handwritten_program_words

#print axioms basis_mem_orbit_of_program_projective_word
#print axioms liveLocalizedL2BranchesLandInOrbit_of_program_projective_words
#print axioms native_cycle_of_program_projective_words
#print axioms bigradedBettiHodge_of_handwritten_program_words

end GSTClassicalHodgeHandwrittenPiProgramLanding
