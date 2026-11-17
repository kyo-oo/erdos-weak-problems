import GSTClassicalHodgeGradedOrbitSingleProgramCollapse
import GSTClassicalHodgeOmniversalSeparatorGhostCrown
import GSTClassicalHodgeNativeExecutablePlane
import GSTClassicalHodgeAtomicDefectDuality
import GSTClassicalHodgeCodimensionZeroFundamentalCycle
import GSTClassicalHodgeGradedGeometricProgramOrbit
import GSTClassicalHodgeCrossWeightNativePropagation

/-!
# GST CLASSICAL HODGE — FULL CORRESPONDENCE GST PLANE COMPLETION

This file fixes the terminal geometric meaning of GST plane completeness in
the strongest verified program language currently present in the repository.

An edge is not an abstract Hodge matrix unit. It is one executable
GradedCorrespondenceProgram built from genuine realized finite closed
correspondences, genuine principal cuts, rational addition/scaling and
ordered composition.
-/

set_option maxHeartbeats 180000000
set_option maxRecDepth 1000000

noncomputable section

open scoped BigOperators
open AlgebraicGeometry

namespace GSTClassicalHodgeFullCorrespondenceGSTPlaneCompletion

open GSTProjectiveOverC
open GSTGeometricRealizationStage2D
open GSTGeometricRealizationStage2F
open GSTGeometricRealizationStage2G
open GSTClassicalHodgeFiberedCosmology
open GSTClassicalHodgeRankFreeArsenalIrreducibility
open GSTClassicalHodgeGeometricCycleClassSpine
open GSTClassicalHodgeGradedCorrespondenceProgramOrbit
open GSTClassicalHodgeGradedCorrespondenceProgramOrbit.GradedCorrespondenceProgram
open GSTClassicalHodgeGradedOrbitSingleProgramCollapse
open GSTClassicalHodgeExactClayStatement
open GSTClassicalHodgeAtomicAnnihilator
open GSTClassicalHodgeAtomicSpan
open GSTClassicalHodgeAtomicDefectDuality
open GSTClassicalHodgeGradedGeometricProgramOrbit
open GSTClassicalHodgeCrossWeightNativePropagation
open GSTClassicalHodgeCodimensionZeroFundamentalCycle
open GSTClassicalHodgeLimitlessSeparatorGhost
open GSTClassicalHodgeOmniversalSeparatorGhostCrown

variable {V : SmoothProjectiveComplexScheme}
variable {H : HodgeBigradedBettiData V}

/-- FULL GEOMETRIC GST PLANE COMPLETENESS.
Every Hodge basis sheet is the exact cohomological output of one actual full
correspondence/cut program from the canonical codimension-zero origin. -/
def FullCorrespondenceGSTPlaneCompleteness
    (G : GeometricCycleClassSpine V H) : Prop :=
  ∀ q : Nat, ∀ j : ClassicalHodgeBasisIndex V H q,
    ∃ P : GradedCorrespondenceProgram V H 0 q,
      P.cohomologyEval G (correspondenceGeometricOriginClass V H) =
        (classicalHodgeBasis V H q j).1

theorem basis_mem_fullOrbit_of_plane
    (G : GeometricCycleClassSpine V H)
    (hplane : FullCorrespondenceGSTPlaneCompleteness G)
    (q : Nat)
    (j : ClassicalHodgeBasisIndex V H q) :
    (classicalHodgeBasis V H q j).1 ∈
      fullCorrespondenceOrbitModule G q := by
  change (classicalHodgeBasis V H q j).1 ∈ fullCorrespondenceOrbitSet G q
  obtain ⟨P,hP⟩ := hplane q j
  exact ⟨P,hP.symm⟩

theorem fullOrbitCyclic_of_plane
    (G : GeometricCycleClassSpine V H)
    (hplane : FullCorrespondenceGSTPlaneCompleteness G) :
    FullCorrespondenceOrbitCyclic G := by
  intro q alpha halpha
  classical
  rw [fullCorrespondenceOrbitSubspace_eq_module G q]
  let alphaH : ClassicalHodgeFiber V H q := ⟨alpha,halpha⟩
  rw [show alpha =
      ((classicalHodgeBasis V H q).repr alphaH).support.sum
        (fun j => ((classicalHodgeBasis V H q).repr alphaH j) •
          (classicalHodgeBasis V H q j).1) by
    have hrepr := (classicalHodgeBasis V H q).linearCombination_repr alphaH
    have hval := congrArg Subtype.val hrepr
    simpa [Finsupp.linearCombination_apply, Finsupp.sum] using hval.symm]
  apply Submodule.sum_mem
  intro j hj
  exact (fullCorrespondenceOrbitModule G q).smul_mem
    ((classicalHodgeBasis V H q).repr alphaH j)
    (basis_mem_fullOrbit_of_plane G hplane q j)

theorem plane_of_fullOrbitCyclic
    (G : GeometricCycleClassSpine V H)
    (hcyclic : FullCorrespondenceOrbitCyclic G) :
    FullCorrespondenceGSTPlaneCompleteness G := by
  intro q j
  have hmem :
      (classicalHodgeBasis V H q j).1 ∈
        fullCorrespondenceOrbitSubspace G q :=
    hcyclic q (classicalHodgeBasis V H q j).2
  obtain ⟨P,hP⟩ :=
    (mem_fullCorrespondenceOrbitSubspace_iff_singleProgram
      G q (classicalHodgeBasis V H q j).1).1 hmem
  exact ⟨P,hP.symm⟩

theorem fullCorrespondencePlane_iff_orbitCyclic
    (G : GeometricCycleClassSpine V H) :
    FullCorrespondenceGSTPlaneCompleteness G ↔
      FullCorrespondenceOrbitCyclic G := by
  constructor
  · exact fullOrbitCyclic_of_plane G
  · exact plane_of_fullOrbitCyclic G

theorem fullCorrespondencePlane_iff_singleProgramGeneration
    (G : GeometricCycleClassSpine V H) :
    FullCorrespondenceGSTPlaneCompleteness G ↔
      (∀ q : Nat,
       ∀ alpha : RationalSingularCohomology H.analytification (2 * q),
         alpha ∈ rationalHodgeSubspace (H.hodgeBigrading q) →
         ∃ P : GradedCorrespondenceProgram V H 0 q,
           alpha =
             P.cohomologyEval G
               (correspondenceGeometricOriginClass V H)) :=
  (fullCorrespondencePlane_iff_orbitCyclic G).trans
    (fullCorrespondenceOrbitCyclic_iff_singleProgramGeneration G)

/-- Hodge state produced by one executable full correspondence/cut program
from the canonical geometric origin.  Hodge type is derived from the native
cycle-class range, not stored in the program. -/
noncomputable def fullProgramHodgeState
    (G : GeometricCycleClassSpine V H)
    {q : Nat}
    (P : GradedCorrespondenceProgram V H 0 q) :
    ClassicalHodgeFiber V H q :=
  ⟨P.cohomologyEval G (correspondenceGeometricOriginClass V H), by
    have hrange :=
      P.cohomologyEval_mem_cycleClass_range G
        (codimensionZeroFundamentalCycle V)
    rcases hrange with ⟨Z, hZ⟩
    have hmem := G.algebraic_is_hodge q Z
    rw [hZ] at hmem
    simpa [correspondenceGeometricOriginClass] using hmem⟩

/-- Exact unrestricted fibered address of one executable full program state. -/
noncomputable def fullProgramFiberedAddress
    (G : GeometricCycleClassSpine V H)
    {q : Nat}
    (P : GradedCorrespondenceProgram V H 0 q) :
    FiberedHodgeAddress V H :=
  fiberedWeightCoordinates V H q (fullProgramHodgeState G P)

/-- Full-correspondence version of the old no-ghost pairing-totality law. -/
def FullCorrespondenceNativeOrbitPairingTotal
    (G : GeometricCycleClassSpine V H) : Prop :=
  ∀ q : Nat,
  ∀ g : FiberedCompletedAddress V H,
    (∀ s : FiberedHodgeIndex V H, s.1 ≠ q → g s = 0) →
    (∀ P : GradedCorrespondenceProgram V H 0 q,
      fiberedPairing (fullProgramFiberedAddress G P) g = 0) →
    g = 0

/-- A full program that hits one basis sheet has exactly the corresponding
Kronecker fibered address. -/
theorem fullProgramFiberedAddress_eq_basis
    (G : GeometricCycleClassSpine V H)
    {q : Nat}
    {j : ClassicalHodgeBasisIndex V H q}
    (P : GradedCorrespondenceProgram V H 0 q)
    (hP :
      P.cohomologyEval G (correspondenceGeometricOriginClass V H) =
        (classicalHodgeBasis V H q j).1) :
    fullProgramFiberedAddress G P =
      Finsupp.single (⟨q,j⟩ : FiberedHodgeIndex V H) 1 := by
  unfold fullProgramFiberedAddress fullProgramHodgeState
  rw [show
      (⟨P.cohomologyEval G (correspondenceGeometricOriginClass V H), by
          have hrange :=
            P.cohomologyEval_mem_cycleClass_range G
              (codimensionZeroFundamentalCycle V)
          rcases hrange with ⟨Z, hZ⟩
          have hmem := G.algebraic_is_hodge q Z
          rw [hZ] at hmem
          simpa [correspondenceGeometricOriginClass] using hmem⟩ :
        ClassicalHodgeFiber V H q) =
      classicalHodgeBasis V H q j by
    apply Subtype.ext
    exact hP]
  exact fiberedWeightCoordinates_basis V H q j

/-- Full geometric plane completeness makes the executable full-program orbit
pairing-total coordinate by coordinate. -/
theorem fullPairingTotal_of_fullCorrespondencePlane
    (G : GeometricCycleClassSpine V H)
    (hplane : FullCorrespondenceGSTPlaneCompleteness G) :
    FullCorrespondenceNativeOrbitPairingTotal G := by
  intro q g hsupp hkill
  funext s
  rcases s with ⟨r,j⟩
  by_cases hr : r = q
  · subst r
    obtain ⟨P, hP⟩ := hplane q j
    have hk := hkill P
    rw [fullProgramFiberedAddress_eq_basis G P hP] at hk
    simpa [fiberedPairing_single_left] using hk
  · exact hsupp ⟨r,j⟩ hr

/-- Pairing-totality forces the full executable orbit to contain the entire
Hodge fiber.  If a Hodge state were missing, a separating functional would
yield a nonzero completed probe invisible to every full program. -/
theorem fullOrbitCyclic_of_fullPairingTotal
    (G : GeometricCycleClassSpine V H)
    (htotal : FullCorrespondenceNativeOrbitPairingTotal G) :
    FullCorrespondenceOrbitCyclic G := by
  intro q alpha halpha
  rw [fullCorrespondenceOrbitSubspace_eq_module G q]
  by_contra hnot
  obtain ⟨ell, hell, hdetect⟩ :=
    exists_linearFunctional_separating_submodule
      (fullCorrespondenceOrbitModule G q) alpha hnot
  let g : FiberedCompletedAddress V H :=
    separatorFiberedProbe (V := V) (H := H) q ell
  have hsupp :
      ∀ s : FiberedHodgeIndex V H, s.1 ≠ q → g s = 0 := by
    intro s hs
    rcases s with ⟨r,j⟩
    exact separatorFiberedProbe_at_other_weight
      (V := V) (H := H) q r hs ell j
  have hkill :
      ∀ P : GradedCorrespondenceProgram V H 0 q,
        fiberedPairing (fullProgramFiberedAddress G P) g = 0 := by
    intro P
    have horbit :
        P.cohomologyEval G (correspondenceGeometricOriginClass V H) ∈
          fullCorrespondenceOrbitModule G q := by
      change
        P.cohomologyEval G (correspondenceGeometricOriginClass V H) ∈
          fullCorrespondenceOrbitSet G q
      exact ⟨P, rfl⟩
    have hzero :
        ell (P.cohomologyEval G (correspondenceGeometricOriginClass V H)) = 0 :=
      hell _ horbit
    let a : ClassicalHodgeFiber V H q := fullProgramHodgeState G P
    have hp :=
      fiberedPairing_separatorProbe
        (V := V) (H := H) q ell a
    simpa [g, a, fullProgramFiberedAddress, fullProgramHodgeState]
      using hp.trans hzero
  have hg : g = 0 := htotal q g hsupp hkill
  let alphaH : ClassicalHodgeFiber V H q := ⟨alpha, halpha⟩
  have hp :=
    fiberedPairing_separatorProbe
      (V := V) (H := H) q ell alphaH
  have hz : ell alpha = 0 := by
    have hpairZero :
        fiberedPairing (fiberedWeightCoordinates V H q alphaH) g = 0 := by
      rw [hg]
      simp [fiberedPairing]
    have hpairExact :
        fiberedPairing (fiberedWeightCoordinates V H q alphaH) g = ell alpha := by
      simpa [g, alphaH] using hp
    exact hpairExact.symm.trans hpairZero
  exact hdetect hz

/-- **EXACT FULL-PROGRAM IDENTIFICATION.**
Executable full-correspondence GST plane completeness is exactly completed-probe
pairing totality for the same executable program orbit. -/
theorem fullCorrespondencePlane_iff_fullPairingTotal
    (G : GeometricCycleClassSpine V H) :
    FullCorrespondenceGSTPlaneCompleteness G ↔
      FullCorrespondenceNativeOrbitPairingTotal G := by
  constructor
  · exact fullPairingTotal_of_fullCorrespondencePlane G
  · intro htotal
    exact plane_of_fullOrbitCyclic G
      (fullOrbitCyclic_of_fullPairingTotal G htotal)

/-- A basis separator kills every executable full-program address because every
such state lies in the actual cycle-class range, hence in the atomic point-cycle
span annihilated by the separator. -/
theorem separatorProbe_kills_fullProgramAddress
    {G : GeometricCycleClassSpine V H}
    (E : OmniversalSeparatorGhost G)
    (P : GradedCorrespondenceProgram V H 0 E.weight) :
    fiberedPairing
      (fullProgramFiberedAddress G P)
      (separatorFiberedProbe
        (V := V) (H := H) E.weight E.separator.detector) = 0 := by
  change fiberedPairing
      (fiberedWeightCoordinates V H E.weight (fullProgramHodgeState G P))
      (separatorFiberedProbe (V := V) (H := H) E.weight E.separator.detector) = 0
  rw [fiberedPairing_separatorProbe]
  have hrange :=
    P.cohomologyEval_mem_cycleClass_range G
      (codimensionZeroFundamentalCycle V)
  rw [smoothProjective_cycleClass_range_eq_atomic_span V H E.weight] at hrange
  have hker :
      pointCycleClassSpan E.weight (H.cycleClass E.weight) ≤
        LinearMap.ker E.separator.detector :=
    (annihilatesPointCycles_iff_atomicSpan_le_ker
      E.weight (H.cycleClass E.weight) E.separator.detector).mp
        E.separator.annihilates_atoms
  exact hker hrange

/-- Full-program pairing totality kills every omniversal separator ghost. -/
theorem noGhost_of_fullCorrespondencePairingTotal
    (G : GeometricCycleClassSpine V H)
    (htotal : FullCorrespondenceNativeOrbitPairingTotal G) :
    IsEmpty (OmniversalSeparatorGhost G) := by
  refine ⟨?_⟩
  intro E
  let g : FiberedCompletedAddress V H :=
    separatorFiberedProbe
      (V := V) (H := H) E.weight E.separator.detector
  have hsupp :
      ∀ s : FiberedHodgeIndex V H, s.1 ≠ E.weight → g s = 0 := by
    simpa [g] using omniversalSeparatorProbe_supported_on_weight E
  have hkill :
      ∀ P : GradedCorrespondenceProgram V H 0 E.weight,
        fiberedPairing (fullProgramFiberedAddress G P) g = 0 := by
    intro P
    simpa [g] using separatorProbe_kills_fullProgramAddress E P
  have hg0 : g = 0 := htotal E.weight g hsupp hkill
  have hgne : g ≠ 0 := by
    simpa [g] using basisSeparator_ghost_ne_zero E.separator
  exact hgne hg0

/-- Full-program pairing totality therefore lands in the exact Stage-2G Hodge
statement without any additional ghost closure package. -/
theorem hodge_of_fullCorrespondencePairingTotal
    (G : GeometricCycleClassSpine V H)
    (htotal : FullCorrespondenceNativeOrbitPairingTotal G) :
    BigradedBettiHodgeStatement V H :=
  (hodge_iff_no_omniversalSeparatorGhost G).2
    (noGhost_of_fullCorrespondencePairingTotal G htotal)

/-- The cycle-side execution of the cohomologically interpreted full program is
exactly the native-only execution.  The geometric spine changes only the
cohomological interpretation, never the native program itself. -/
theorem cycleEval_eq_nativeEval
    (G : GeometricCycleClassSpine V H)
    {p q : Nat}
    (P : GradedCorrespondenceProgram V H p q) :
    P.cycleEval G =
      GSTClassicalHodgeNativeExecutablePlane.nativeEval P := by
  induction P with
  | id p =>
      rfl
  | correspondence E =>
      rfl
  | cut p =>
      exact G.principalCutPair_native p
  | add A B ihA ihB =>
      change A.cycleEval G + B.cycleEval G =
        GSTClassicalHodgeNativeExecutablePlane.nativeEval A +
          GSTClassicalHodgeNativeExecutablePlane.nativeEval B
      rw [ihA, ihB]
  | smul a A ih =>
      change a • A.cycleEval G =
        a • GSTClassicalHodgeNativeExecutablePlane.nativeEval A
      rw [ih]
  | comp A B ihA ihB =>
      change (B.cycleEval G).comp (A.cycleEval G) =
        (GSTClassicalHodgeNativeExecutablePlane.nativeEval B).comp
          (GSTClassicalHodgeNativeExecutablePlane.nativeEval A)
      rw [ihA, ihB]

/-- Every cohomological full-correspondence plane therefore compiles to the
native-only executable plane.  No new realization law is introduced here. -/
theorem nativeExecutablePlane_of_fullCorrespondencePlane
    (G : GeometricCycleClassSpine V H)
    (hplane : FullCorrespondenceGSTPlaneCompleteness G) :
    GSTClassicalHodgeNativeExecutablePlane.NativeExecutableGSTPlaneCompleteness
      (V := V) (H := H) := by
  intro q j
  obtain ⟨P,hP⟩ := hplane q j
  refine ⟨P, ?_⟩
  have hnat :=
    P.cycleClass_cycleEval G
      (codimensionZeroFundamentalCycle V)
  have hcycle := congrArg
    (fun A : codimensionCycles V.X 0 →ₗ[ℚ] codimensionCycles V.X q =>
      A (codimensionZeroFundamentalCycle V))
    (cycleEval_eq_nativeEval G P)
  change H.cycleClass q
      ((GSTClassicalHodgeNativeExecutablePlane.nativeEval P)
        (codimensionZeroFundamentalCycle V)) =
        (classicalHodgeBasis V H q j).1
  rw [← hcycle]
  exact hnat.trans hP

/-- **NATIVE EXECUTABLE PLANE -> FULL COHOMOLOGICAL PLANE.**

The converse compiler is forced by the existing master cycle-class naturality
law.  The native-only plane already supplies, for each sheet, an actual full
correspondence/cut program whose native output has that sheet as cycle class.
Executing the SAME program through the geometric spine and evaluating the
naturality square on the canonical origin shows that its cohomological output
is exactly the requested basis sheet.

Thus the native and full-correspondence notions of completed GST plane cannot
drift apart. -/
theorem fullCorrespondencePlane_of_nativeExecutablePlane
    (G : GeometricCycleClassSpine V H)
    (hplane :
      GSTClassicalHodgeNativeExecutablePlane.NativeExecutableGSTPlaneCompleteness
        (V := V) (H := H)) :
    FullCorrespondenceGSTPlaneCompleteness G := by
  intro q j
  obtain ⟨P, hnative⟩ := hplane q j
  refine ⟨P, ?_⟩
  have hnat :=
    P.cycleClass_cycleEval G
      (codimensionZeroFundamentalCycle V)
  have hcycle := congrArg
    (fun A : codimensionCycles V.X 0 →ₗ[ℚ] codimensionCycles V.X q =>
      A (codimensionZeroFundamentalCycle V))
    (cycleEval_eq_nativeEval G P)
  have hout :
      H.cycleClass q
        (P.cycleEval G
          (codimensionZeroFundamentalCycle V)) =
        (classicalHodgeBasis V H q j).1 := by
    rw [hcycle]
    exact hnative
  exact hnat.symm.trans hout

/-- **EXACT EXECUTABLE-PLANE IDENTIFICATION.**
Once the geometric spine supplies the cohomological interpretation of the
already-native program syntax, native executable plane completeness and full
correspondence GST plane completeness are literally equivalent. -/
theorem nativeExecutablePlane_iff_fullCorrespondencePlane
    (G : GeometricCycleClassSpine V H) :
    GSTClassicalHodgeNativeExecutablePlane.NativeExecutableGSTPlaneCompleteness
        (V := V) (H := H) ↔
      FullCorrespondenceGSTPlaneCompleteness G := by
  constructor
  · exact fullCorrespondencePlane_of_nativeExecutablePlane G
  · exact nativeExecutablePlane_of_fullCorrespondencePlane G

/-- **NATIVE EXECUTABLE PLANE KILLS EVERY OMNIVERSAL GHOST DIRECTLY.**

No pairing-totality hypothesis is needed once the plane already executes
natively.  A hypothetical separator detects one basis sheet, while native
plane completeness constructs an actual native cycle with exactly that class.
The separator's verified identity-program annihilation then evaluates the same
sheet to zero, contradicting detection. -/
theorem noGhost_of_nativeExecutablePlane
    (G : GeometricCycleClassSpine V H)
    (hplane :
      GSTClassicalHodgeNativeExecutablePlane.NativeExecutableGSTPlaneCompleteness
        (V := V) (H := H)) :
    IsEmpty (OmniversalSeparatorGhost G) := by
  refine ⟨?_⟩
  intro E
  obtain ⟨P, hP⟩ := hplane E.weight E.sheet
  let Z : codimensionCycles V.X E.weight :=
    GSTClassicalHodgeNativeExecutablePlane.nativeOutput P
  have hrange :
      H.cycleClass E.weight Z ∈
        pointCycleClassSpan E.weight (H.cycleClass E.weight) := by
    rw [← smoothProjective_cycleClass_range_eq_atomic_span V H E.weight]
    exact ⟨Z, rfl⟩
  have hker :
      pointCycleClassSpan E.weight (H.cycleClass E.weight) ≤
        LinearMap.ker E.separator.detector :=
    (annihilatesPointCycles_iff_atomicSpan_le_ker
      E.weight (H.cycleClass E.weight) E.separator.detector).mp
        E.separator.annihilates_atoms
  have hzero :
      E.separator.detector (H.cycleClass E.weight Z) = 0 := hker hrange
  rw [show H.cycleClass E.weight Z =
      (classicalHodgeBasis V H E.weight E.sheet).1 by
        exact hP] at hzero
  exact E.separator.detects_basis hzero

/-- **THE COMPLETED GST PLANE IS THE NO-GHOST FINALE.**
Native executable plane completeness therefore lands directly in the exact
Stage-2G Hodge statement through the original omniversal contradiction route. -/
theorem hodge_of_nativeExecutablePlane_noGhost
    (G : GeometricCycleClassSpine V H)
    (hplane :
      GSTClassicalHodgeNativeExecutablePlane.NativeExecutableGSTPlaneCompleteness
        (V := V) (H := H)) :
    BigradedBettiHodgeStatement V H :=
  (hodge_iff_no_omniversalSeparatorGhost G).2
    (noGhost_of_nativeExecutablePlane G hplane)

/-- Exact finite-rational Clay wording of the same native-plane theorem. -/
theorem finiteRationalCombination_of_nativeExecutablePlane
    (G : GeometricCycleClassSpine V H)
    (hplane :
      GSTClassicalHodgeNativeExecutablePlane.NativeExecutableGSTPlaneCompleteness
        (V := V) (H := H)) :
    EveryHodgeClassIsFiniteRationalCombination H :=
  (exact_rational_hodge_conjecture_finite_sum H).1
    (hodge_of_nativeExecutablePlane_noGhost G hplane)

/-- One crown recording the now-single completed GST-plane notion:
native execution, full correspondence execution, pairing totality, no ghost,
Stage-2G Hodge, and the exact finite rational algebraic-cycle statement. -/
theorem completedGSTPlane_noGhost_hodge_crown
    (G : GeometricCycleClassSpine V H)
    (hplane :
      GSTClassicalHodgeNativeExecutablePlane.NativeExecutableGSTPlaneCompleteness
        (V := V) (H := H)) :
    FullCorrespondenceGSTPlaneCompleteness G
      ∧ FullCorrespondenceNativeOrbitPairingTotal G
      ∧ IsEmpty (OmniversalSeparatorGhost G)
      ∧ BigradedBettiHodgeStatement V H
      ∧ EveryHodgeClassIsFiniteRationalCombination H := by
  have hfull := fullCorrespondencePlane_of_nativeExecutablePlane G hplane
  have htotal := fullPairingTotal_of_fullCorrespondencePlane G hfull
  have hghost := noGhost_of_nativeExecutablePlane G hplane
  have hhodge := (hodge_iff_no_omniversalSeparatorGhost G).2 hghost
  exact ⟨hfull, htotal, hghost, hhodge,
    (exact_rational_hodge_conjecture_finite_sum H).1 hhodge⟩

/-- **OLD NO-GHOST TARGET = COMPLETED NATIVE GST PLANE.**

This is the exact bridge to the original omniversal proof design.  The native
executable plane is equivalent to completed-probe pairing totality of the full
verified correspondence/cut orbit: neither side is a separate extra law.

So the phrase "GST plane completeness" in the final route can be read
geometrically (native execution) or dually (no nonzero completed probe is
invisible to every executable native branch). -/
theorem nativeExecutablePlane_iff_fullPairingTotal
    (G : GeometricCycleClassSpine V H) :
    GSTClassicalHodgeNativeExecutablePlane.NativeExecutableGSTPlaneCompleteness
        (V := V) (H := H) ↔
      FullCorrespondenceNativeOrbitPairingTotal G :=
  (nativeExecutablePlane_iff_fullCorrespondencePlane G).trans
    (fullCorrespondencePlane_iff_fullPairingTotal G)

/-- Equivalent orbit-cyclicity form of completed native GST plane
completeness. -/
theorem nativeExecutablePlane_iff_fullOrbitCyclic
    (G : GeometricCycleClassSpine V H) :
    GSTClassicalHodgeNativeExecutablePlane.NativeExecutableGSTPlaneCompleteness
        (V := V) (H := H) ↔
      FullCorrespondenceOrbitCyclic G :=
  (nativeExecutablePlane_iff_fullCorrespondencePlane G).trans
    (fullCorrespondencePlane_iff_orbitCyclic G)

/-- **COMPLETED GST PLANE / OMNIVERSAL DUALITY CROWN.**
All three noncircular formulations of the missing geometric plane law coincide:
native execution, verified-program orbit cyclicity, and completed-probe pairing
totality.  Any one of them kills the omniversal ghost and yields the exact
Hodge landing by the theorems below. -/
theorem completedGSTPlane_equivalence_crown
    (G : GeometricCycleClassSpine V H) :
    (GSTClassicalHodgeNativeExecutablePlane.NativeExecutableGSTPlaneCompleteness
        (V := V) (H := H) ↔
      FullCorrespondenceGSTPlaneCompleteness G)
    ∧
    (GSTClassicalHodgeNativeExecutablePlane.NativeExecutableGSTPlaneCompleteness
        (V := V) (H := H) ↔
      FullCorrespondenceOrbitCyclic G)
    ∧
    (GSTClassicalHodgeNativeExecutablePlane.NativeExecutableGSTPlaneCompleteness
        (V := V) (H := H) ↔
      FullCorrespondenceNativeOrbitPairingTotal G) := by
  exact ⟨nativeExecutablePlane_iff_fullCorrespondencePlane G,
    nativeExecutablePlane_iff_fullOrbitCyclic G,
    nativeExecutablePlane_iff_fullPairingTotal G⟩

noncomputable def basisCycle
    (G : GeometricCycleClassSpine V H)
    (hplane : FullCorrespondenceGSTPlaneCompleteness G)
    (q : Nat)
    (j : ClassicalHodgeBasisIndex V H q) :
    codimensionCycles V.X q :=
  let P := Classical.choose (hplane q j)
  P.cycleEval G
    (codimensionZeroFundamentalCycle V)

theorem basisCycle_spec
    (G : GeometricCycleClassSpine V H)
    (hplane : FullCorrespondenceGSTPlaneCompleteness G)
    (q : Nat)
    (j : ClassicalHodgeBasisIndex V H q) :
    H.cycleClass q (basisCycle G hplane q j) =
      (classicalHodgeBasis V H q j).1 := by
  let P := Classical.choose (hplane q j)
  have hP := Classical.choose_spec (hplane q j)
  have hnat :=
    P.cycleClass_cycleEval G
      (codimensionZeroFundamentalCycle V)
  calc
    H.cycleClass q (basisCycle G hplane q j) =
        H.cycleClass q
          (P.cycleEval G
            (codimensionZeroFundamentalCycle V)) := by
          rfl
    _ = P.cohomologyEval G (correspondenceGeometricOriginClass V H) := by
          simpa [correspondenceGeometricOriginClass] using hnat
    _ = (classicalHodgeBasis V H q j).1 := hP

theorem hodge_of_fullCorrespondenceGSTPlane
    (G : GeometricCycleClassSpine V H)
    (hplane : FullCorrespondenceGSTPlaneCompleteness G) :
    BigradedBettiHodgeStatement V H := by
  exact (everyHodgeClassIsRationalAlgebraic_iff_stage2G H).1
    (exactHodge_of_fullCorrespondenceOrbitCyclic G
      (fullOrbitCyclic_of_plane G hplane))

theorem nativeCycle_of_fullCorrespondenceGSTPlane
    (G : GeometricCycleClassSpine V H)
    (hplane : FullCorrespondenceGSTPlaneCompleteness G)
    (q : Nat)
    (alpha : RationalSingularCohomology H.analytification (2 * q))
    (halpha : alpha ∈ rationalHodgeSubspace (H.hodgeBigrading q)) :
    ∃ Z : codimensionCycles V.X q,
      H.cycleClass q Z = alpha :=
  (hodge_of_fullCorrespondenceGSTPlane G hplane) q halpha

#check FullCorrespondenceGSTPlaneCompleteness
#check basis_mem_fullOrbit_of_plane
#check fullCorrespondencePlane_iff_orbitCyclic
#check fullCorrespondencePlane_iff_singleProgramGeneration
#check basisCycle
#check basisCycle_spec
#check fullProgramHodgeState
#check fullProgramFiberedAddress
#check FullCorrespondenceNativeOrbitPairingTotal
#check fullCorrespondencePlane_iff_fullPairingTotal
#check separatorProbe_kills_fullProgramAddress
#check noGhost_of_fullCorrespondencePairingTotal
#check hodge_of_fullCorrespondencePairingTotal
#check nativeExecutablePlane_of_fullCorrespondencePlane
#check fullCorrespondencePlane_of_nativeExecutablePlane
#check nativeExecutablePlane_iff_fullCorrespondencePlane
#check nativeExecutablePlane_iff_fullPairingTotal
#check nativeExecutablePlane_iff_fullOrbitCyclic
#check completedGSTPlane_equivalence_crown
#check noGhost_of_nativeExecutablePlane
#check hodge_of_nativeExecutablePlane_noGhost
#check finiteRationalCombination_of_nativeExecutablePlane
#check completedGSTPlane_noGhost_hodge_crown
#check hodge_of_fullCorrespondenceGSTPlane
#check nativeCycle_of_fullCorrespondenceGSTPlane

#print axioms fullCorrespondencePlane_iff_orbitCyclic
#print axioms fullCorrespondencePlane_iff_singleProgramGeneration
#print axioms basisCycle_spec
#print axioms fullCorrespondencePlane_iff_fullPairingTotal
#print axioms separatorProbe_kills_fullProgramAddress
#print axioms noGhost_of_fullCorrespondencePairingTotal
#print axioms hodge_of_fullCorrespondencePairingTotal
#print axioms nativeExecutablePlane_of_fullCorrespondencePlane
#print axioms fullCorrespondencePlane_of_nativeExecutablePlane
#print axioms nativeExecutablePlane_iff_fullCorrespondencePlane
#print axioms nativeExecutablePlane_iff_fullPairingTotal
#print axioms nativeExecutablePlane_iff_fullOrbitCyclic
#print axioms completedGSTPlane_equivalence_crown
#print axioms noGhost_of_nativeExecutablePlane
#print axioms hodge_of_nativeExecutablePlane_noGhost
#print axioms completedGSTPlane_noGhost_hodge_crown
#print axioms hodge_of_fullCorrespondenceGSTPlane

end GSTClassicalHodgeFullCorrespondenceGSTPlaneCompletion
