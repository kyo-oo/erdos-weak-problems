import GSTClassicalHodgeLimitlessSeparatorGhost
import GSTClassicalHodgeGradedSeparatorBackpropagation
import GSTClassicalHodgeGradedGeometricOrbitAlgebra
import GSTClassicalHodgeSingleSheetCrown

/-!
# GST CLASSICAL HODGE — OMNIVERSAL SEPARATOR-GHOST CROWN

This module packages the strongest obstruction form obtained from the upgraded
limitless/fibered/graded geometry stack.

A genuine Stage-2G failure cannot remain an unspecified missing cycle.  It
forces one basis sheet together with a completed limitless dual probe which is
nonzero on that exact sheet and orthogonal to every algebraic Hodge state.  The
same detector is orthogonal to every state obtained from every native cycle by
every verified graded geometric program.  Pulling it backward through any such
program preserves atomic annihilation.

Thus the obstruction is a coherent ghost cone over the entire independently
verified projective + principal-cut cosmology.
-/

set_option maxHeartbeats 90000000
set_option maxRecDepth 1000000

noncomputable section

open AlgebraicGeometry

namespace GSTClassicalHodgeOmniversalSeparatorGhostCrown

open GSTProjectiveOverC
open GSTGeometricRealizationStage2D
open GSTGeometricRealizationStage2F
open GSTGeometricRealizationStage2G
open GSTClassicalHodgeFiberedCosmology
open GSTClassicalHodgeAtomicAnnihilator
open GSTClassicalHodgeAtomicDefectDuality
open GSTClassicalHodgeSingleSheetCrown
open GSTClassicalHodgeGeometricCycleClassSpine
open GSTClassicalHodgeGradedGeometricProgramOrbit
open GSTClassicalHodgeLimitlessSeparatorGhost
open GSTClassicalHodgeGradedSeparatorBackpropagation

variable {V : SmoothProjectiveComplexScheme}
variable {H : HodgeBigradedBettiData V}

/-- One coherent obstruction packet seen simultaneously in classical
cohomology, the completed limitless fibered dual, and the entire graded
geometric-program cosmology. -/
structure OmniversalSeparatorGhost
    (G : GeometricCycleClassSpine V H) where
  weight : Nat
  sheet : ClassicalHodgeBasisIndex V H weight
  separator : BasisAtomicSeparator V H weight sheet
  ghost : FiberedCompletedAddress V H :=
    separatorFiberedProbe (V := V) (H := H) weight separator.detector
  ghost_ne_zero : ghost ≠ 0
  ghost_detects_sheet :
    fiberedPairing
      (fiberedWeightCoordinates V H weight
        (classicalHodgeBasis V H weight sheet)) ghost ≠ 0
  kills_all_native_programs :
    ∀ p : Nat,
    ∀ P : GradedGeometricProgram V p weight,
    ∀ Z : codimensionCycles V.X p,
      separator.detector
        (P.cohomologyEval G (H.cycleClass p Z)) = 0
  backward_atomic :
    ∀ p : Nat,
    ∀ P : GradedGeometricProgram V p weight,
      AnnihilatesPointCycleClasses p (H.cycleClass p)
        (pullbackDetector G P separator.detector)

/-- Every microscopic separator canonically upgrades to the omniversal ghost
packet. -/
noncomputable def BasisAtomicSeparator.toOmniversalGhost
    (G : GeometricCycleClassSpine V H)
    {p : Nat}
    {i : ClassicalHodgeBasisIndex V H p}
    (S : BasisAtomicSeparator V H p i) :
    OmniversalSeparatorGhost G where
  weight := p
  sheet := i
  separator := S
  ghost := separatorFiberedProbe (V := V) (H := H) p S.detector
  ghost_ne_zero := basisSeparator_ghost_ne_zero S
  ghost_detects_sheet := basisSeparator_ghost_detects_sheet S
  kills_all_native_programs := by
    intro q P Z
    exact basisSeparator_kills_every_program_cycle G P S Z
  backward_atomic := by
    intro q P
    exact basisSeparator_pullback_annihilates_atoms G P S

/-- **FAILURE = EXISTENCE OF AN OMNIVERSAL GEOMETRIC-ORBIT GHOST.**
The forward implication constructs the full obstruction packet.  Conversely,
its stored basis separator is already a witness that Stage-2G fails. -/
theorem not_hodge_iff_nonempty_omniversalSeparatorGhost
    (G : GeometricCycleClassSpine V H) :
    ¬ BigradedBettiHodgeStatement V H ↔
      Nonempty (OmniversalSeparatorGhost G) := by
  constructor
  · intro hnot
    rw [not_bigradedBettiHodgeStatement_iff_exists_basis_separator V H] at hnot
    rcases hnot with ⟨p,i,⟨S⟩⟩
    exact ⟨BasisAtomicSeparator.toOmniversalGhost G S⟩
  · rintro ⟨E⟩ hHodge
    have hnone :=
      (bigradedBettiHodgeStatement_iff_no_basis_separator V H).mp
        hHodge E.weight E.sheet
    exact isEmpty_iff.mp hnone E.separator

/-- Exact positive form: eliminating these omniversal ghosts is equivalent to
closing the genuine Stage-2G Hodge statement. -/
theorem hodge_iff_no_omniversalSeparatorGhost
    (G : GeometricCycleClassSpine V H) :
    BigradedBettiHodgeStatement V H ↔
      IsEmpty (OmniversalSeparatorGhost G) := by
  constructor
  · intro h
    refine ⟨?_⟩
    intro E
    have hnone :=
      (bigradedBettiHodgeStatement_iff_no_basis_separator V H).mp
        h E.weight E.sheet
    exact isEmpty_iff.mp hnone E.separator
  · intro hnone
    by_contra hnot
    have hne := (not_hodge_iff_nonempty_omniversalSeparatorGhost G).mp hnot
    exact isEmpty_iff.mp hnone (Classical.choice hne)

/-- Origin form of the ghost law: the obstruction is orthogonal to every
canonical-origin program state. -/
theorem omniversalGhost_kills_origin_orbit
    {G : GeometricCycleClassSpine V H}
    (E : OmniversalSeparatorGhost G)
    (P : GradedGeometricProgram V 0 E.weight) :
    E.separator.detector
      (P.cohomologyEval G (geometricOriginClass V H)) = 0 := by
  exact E.kills_all_native_programs 0 P
    (GSTClassicalHodgeCodimensionZeroFundamentalCycle.codimensionZeroFundamentalCycle V)

/-! ## Limitless native-orbit pairing totality

This is the exact no-ghost target of the unbounded/fibered proof.  It is stated
on the unrestricted sigma-indexed Hodge address universe; no finite rank,
`4 x 3` chart, or twelve-sheet specialization occurs here.

A verified graded geometric program starts at the genuine codimension-zero
fundamental cycle and therefore produces a genuine Hodge state.  We embed that
state into its exact fibered address.  Pairing-totality says that a completed
probe supported on one weight and invisible to every such verified native
program address must vanish globally.

The theorem below proves that this pure GST totality statement is exactly strong
enough to eliminate every omniversal separator ghost.  No Hodge conclusion is
used in its proof. -/

/-- The Hodge state produced by one verified mixed native/projective/cut
program from the canonical geometric origin. -/
noncomputable def nativeProgramHodgeState
    (G : GeometricCycleClassSpine V H)
    {q : Nat}
    (P : GradedGeometricProgram V 0 q) :
    ClassicalHodgeFiber V H q :=
  ⟨P.cohomologyEval G (geometricOriginClass V H), by
    unfold geometricOriginClass
    exact P.cohomologyEval_mem_hodge G
      (GSTClassicalHodgeCodimensionZeroFundamentalCycle.codimensionZeroFundamentalCycle V)⟩

/-- Exact unrestricted fibered address of one verified native program state. -/
noncomputable def nativeProgramFiberedAddress
    (G : GeometricCycleClassSpine V H)
    {q : Nat}
    (P : GradedGeometricProgram V 0 q) :
    FiberedHodgeAddress V H :=
  fiberedWeightCoordinates V H q (nativeProgramHodgeState G P)

/-- **OMNIVERSAL NATIVE-ORBIT PAIRING TOTALITY.**
At every Hodge weight, the verified native-program states form a determining
family for completed limitless probes supported on that weight. -/
def OmniversalNativeOrbitPairingTotal
    (G : GeometricCycleClassSpine V H) : Prop :=
  ∀ q : Nat,
  ∀ g : FiberedCompletedAddress V H,
    (∀ s : FiberedHodgeIndex V H, s.1 ≠ q → g s = 0) →
    (∀ P : GradedGeometricProgram V 0 q,
      fiberedPairing (nativeProgramFiberedAddress G P) g = 0) →
    g = 0

/-- **VERIFIED PROGRAM-ORBIT CYCLICITY IMPLIES LIMITLESS PAIRING TOTALITY.**

This is the missing algebraic bridge in the no-ghost route.  If the actual
graded geometric-program orbit already contains the whole rational Hodge
subspace at every weight, then every completed probe supported on one weight
and invisible to all verified native-program addresses is zero.

The proof is coordinatewise and uses no separator or Hodge conclusion:
each genuine Hodge basis sheet belongs to the verified orbit, hence is exactly
the output of some genuine program from the geometric origin.  The probe kills
that program address, so it kills the corresponding basis atom.  Off the chosen
weight it vanishes by support.  Therefore every fibered coordinate vanishes. -/
theorem nativeOrbitPairingTotal_of_gradedGeometricOrbitModuleCyclic
    (G : GeometricCycleClassSpine V H)
    (hcyclic :
      GSTClassicalHodgeGradedGeometricOrbitAlgebra.GradedGeometricOrbitModuleCyclic G) :
    OmniversalNativeOrbitPairingTotal G := by
  intro q g hsupp hkill
  funext s
  rcases s with ⟨r, i⟩
  by_cases hrq : r = q
  · subst r
    have hbasisMem :
        (classicalHodgeBasis V H q i).1 ∈
          GSTClassicalHodgeGradedGeometricOrbitAlgebra.geometricProgramOrbitModule G q := by
      exact hcyclic q (classicalHodgeBasis V H q i).2
    change (classicalHodgeBasis V H q i).1 ∈
      GSTClassicalHodgeGradedGeometricProgramOrbit.geometricProgramOrbitSet G q at hbasisMem
    rcases hbasisMem with ⟨P, hP⟩
    have hsub :
        nativeProgramHodgeState G P =
          classicalHodgeBasis V H q i := by
      apply Subtype.ext
      simpa [nativeProgramHodgeState] using hP.symm
    have hpair := hkill P
    rw [nativeProgramFiberedAddress, hsub,
      fiberedWeightCoordinates_basis,
      GSTClassicalHodgeAtomicDefectDuality.fiberedPairing_single_left] at hpair
    exact hpair
  · exact hsupp ⟨r, i⟩ hrq

/-- The canonical probe attached to an omniversal separator is genuinely
supported on the separator's single Hodge weight. -/
theorem omniversalSeparatorProbe_supported_on_weight
    {G : GeometricCycleClassSpine V H}
    (E : OmniversalSeparatorGhost G) :
    ∀ s : FiberedHodgeIndex V H,
      s.1 ≠ E.weight →
        separatorFiberedProbe
          (V := V) (H := H) E.weight E.separator.detector s = 0 := by
  intro s hs
  rcases s with ⟨q, j⟩
  exact separatorFiberedProbe_at_other_weight
    (V := V) (H := H) E.weight q hs E.separator.detector j

/-- Every verified native-program address is invisible to the canonical
completed probe of an omniversal separator. -/
theorem omniversalSeparatorProbe_kills_nativeProgramAddress
    {G : GeometricCycleClassSpine V H}
    (E : OmniversalSeparatorGhost G)
    (P : GradedGeometricProgram V 0 E.weight) :
    fiberedPairing
        (nativeProgramFiberedAddress G P)
        (separatorFiberedProbe
          (V := V) (H := H) E.weight E.separator.detector) = 0 := by
  change fiberedPairing
      (fiberedWeightCoordinates V H E.weight (nativeProgramHodgeState G P))
      (separatorFiberedProbe (V := V) (H := H) E.weight E.separator.detector) = 0
  rw [fiberedPairing_separatorProbe]
  simpa [nativeProgramHodgeState] using
    omniversalGhost_kills_origin_orbit E P

/-- **PAIRING TOTALITY KILLS EVERY OMNIVERSAL GHOST.**
This is the exact contradiction step requested by the no-ghost route: the
separator supplies a nonzero completed probe; verified geometry makes that
probe invisible to the entire native program orbit; limitless pairing totality
therefore forces the same probe to be zero. -/
theorem no_omniversalSeparatorGhost_of_nativeOrbitPairingTotal
    (G : GeometricCycleClassSpine V H)
    (htotal : OmniversalNativeOrbitPairingTotal G) :
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
      ∀ P : GradedGeometricProgram V 0 E.weight,
        fiberedPairing (nativeProgramFiberedAddress G P) g = 0 := by
    intro P
    simpa [g] using omniversalSeparatorProbe_kills_nativeProgramAddress E P
  have hg0 : g = 0 := htotal E.weight g hsupp hkill
  have hgne : g ≠ 0 := by
    simpa [g] using basisSeparator_ghost_ne_zero E.separator
  exact hgne hg0

/-- Cyclicity of the actual verified geometric-program orbit therefore kills
every omniversal separator ghost without any target-indexed correspondence
packet. -/
theorem no_omniversalSeparatorGhost_of_gradedGeometricOrbitModuleCyclic
    (G : GeometricCycleClassSpine V H)
    (hcyclic :
      GSTClassicalHodgeGradedGeometricOrbitAlgebra.GradedGeometricOrbitModuleCyclic G) :
    IsEmpty (OmniversalSeparatorGhost G) :=
  no_omniversalSeparatorGhost_of_nativeOrbitPairingTotal G
    (nativeOrbitPairingTotal_of_gradedGeometricOrbitModuleCyclic G hcyclic)

/-- **DIRECT NO-GHOST LANDING FROM THE VERIFIED PROGRAM ORBIT.**
Once the native/projective/cut program orbit is cyclic, the limitless ghost
contradiction closes the exact Stage-2G Hodge statement. -/
theorem hodge_of_gradedGeometricOrbitModuleCyclic_noGhost
    (G : GeometricCycleClassSpine V H)
    (hcyclic :
      GSTClassicalHodgeGradedGeometricOrbitAlgebra.GradedGeometricOrbitModuleCyclic G) :
    BigradedBettiHodgeStatement V H :=
  (hodge_iff_no_omniversalSeparatorGhost G).2
    (no_omniversalSeparatorGhost_of_gradedGeometricOrbitModuleCyclic G hcyclic)

/-- **LIMITLESS NATIVE-ORBIT NO-GHOST FINALE.**
Once the verified native orbit is pairing-total in the unrestricted fibered
universe, the exact Stage-2G Hodge statement follows through the already-proved
ghost equivalence. -/
theorem hodge_of_nativeOrbitPairingTotal
    (G : GeometricCycleClassSpine V H)
    (htotal : OmniversalNativeOrbitPairingTotal G) :
    BigradedBettiHodgeStatement V H :=
  (hodge_iff_no_omniversalSeparatorGhost G).2
    (no_omniversalSeparatorGhost_of_nativeOrbitPairingTotal G htotal)

#check OmniversalSeparatorGhost
#check BasisAtomicSeparator.toOmniversalGhost
#check not_hodge_iff_nonempty_omniversalSeparatorGhost
#check hodge_iff_no_omniversalSeparatorGhost
#check omniversalGhost_kills_origin_orbit
#check nativeProgramHodgeState
#check nativeProgramFiberedAddress
#check OmniversalNativeOrbitPairingTotal
#check nativeOrbitPairingTotal_of_gradedGeometricOrbitModuleCyclic
#check no_omniversalSeparatorGhost_of_gradedGeometricOrbitModuleCyclic
#check hodge_of_gradedGeometricOrbitModuleCyclic_noGhost
#check omniversalSeparatorProbe_supported_on_weight
#check omniversalSeparatorProbe_kills_nativeProgramAddress
#check no_omniversalSeparatorGhost_of_nativeOrbitPairingTotal
#check hodge_of_nativeOrbitPairingTotal

#print axioms not_hodge_iff_nonempty_omniversalSeparatorGhost
#print axioms hodge_iff_no_omniversalSeparatorGhost
#print axioms omniversalGhost_kills_origin_orbit
#print axioms omniversalSeparatorProbe_kills_nativeProgramAddress
#print axioms no_omniversalSeparatorGhost_of_nativeOrbitPairingTotal
#print axioms hodge_of_nativeOrbitPairingTotal
#print axioms nativeOrbitPairingTotal_of_gradedGeometricOrbitModuleCyclic
#print axioms no_omniversalSeparatorGhost_of_gradedGeometricOrbitModuleCyclic
#print axioms hodge_of_gradedGeometricOrbitModuleCyclic_noGhost

end GSTClassicalHodgeOmniversalSeparatorGhostCrown
