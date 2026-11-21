import GSTImageThreeOriginalXNativeLanding
import GSTImageThreeCompanionSourceTransport
import Mathlib

/-!
# GST Image 3 — ALL finite N ORIGINAL-X cycle-class source compiler

The author's ORIGINAL GST wave has arbitrary independent N-hole
cohomology channels, original physical U, rational CM J and TRUE
SURVIVE source M. The all-N companion source theorem constructs
zero-local-M native folds with full 12N information rank.

This file realizes the corresponding ALL-N SOURCE-TRANSPORT ALGEBRA
on genuine original-X rational algebraic cycles, provided real
original-X native/Betti operator pairs U,J,M are supplied. It
proves the EXACT canonical rational Betti cycle-class square
for arbitrary N and arbitrary rational source/navigation matrices.
It does not presume a cycle preimage for any unknown Hodge class.

The spectral source companion C and navigation polynomial f(C)
are specific instances, and no universal existence of the true
U,J,M correspondences on every X is smuggled into the proof.
-/

set_option maxHeartbeats 6000000
noncomputable section

namespace GSTImageThreeAllNOriginalXSourceTransport

open GSTProjectiveOverC
open GSTGeometricRealizationStage2D
open GSTGeometricRealizationStage2F
open GSTGeometricRealizationStage2G
open GSTClassicalHodgeCycleOperatorNaturality
open GSTImageThreeCompanionSourceTransport

variable {V : SmoothProjectiveComplexScheme}
variable {H : HodgeBigradedBettiData V}
variable {p : Nat}

/-- Actual Chow-cycle sources indexed by ALL original N-hole worlds. -/
abbrev NativeChannels (N : Nat) :=
  Fin N → codimensionCycles V.X p

/-- Their canonical Betti rational-cohomology channels. -/
abbrev BettiChannels (N : Nat) :=
  Fin N → RationalSingularCohomology H.analytification (2 * p)

/-- The real original-X canonical cycle-class map pointwise on N holes. -/
def channelCycleClass (N : Nat)
    (Z : NativeChannels (V := V) (p := p) N) :
    BettiChannels (H := H) (p := p) N :=
  fun i => H.cycleClass p (Z i)

/-- The single native geometric GST F assembled from three ACTUAL
original-X Chow operators and rational cross-hole source/navigation
matrices. The original 12-state U,J,M are represented by their
certified cycle-class analogues, not arbitrary symbolic vectors. -/
def allNNativeF (N : Nat)
    (U J M : CycleClassOperatorPair V H p)
    (C B : Matrix (Fin N) (Fin N) ℚ)
    (Z : NativeChannels (V := V) (p := p) N) :
    NativeChannels (V := V) (p := p) N :=
  fun i =>
    U.cycleOperator (Z i) + J.cycleOperator (Z i)
      + (∑ j : Fin N, C i j • M.cycleOperator (Z j))
      + (∑ j : Fin N, B i j • Z j)

/-- The corresponding actual canonical Betti cohomological F. -/
def allNBettiF (N : Nat)
    (U J M : CycleClassOperatorPair V H p)
    (C B : Matrix (Fin N) (Fin N) ℚ)
    (alpha : BettiChannels (H := H) (p := p) N) :
    BettiChannels (H := H) (p := p) N :=
  fun i =>
    U.cohomologyOperator (alpha i) + J.cohomologyOperator (alpha i)
      + (∑ j : Fin N, C i j • M.cohomologyOperator (alpha j))
      + (∑ j : Fin N, B i j • alpha j)

/-- THE ALL-N ORIGINAL-X CANONICAL GST COHOMOLOGY SQUARE.

No basis of unknown Hodge classes, no unproved source existence,
and no abstract Chow inverse is supplied. -/
theorem allN_originalX_cycleClass_square (N : Nat)
    (U J M : CycleClassOperatorPair V H p)
    (C B : Matrix (Fin N) (Fin N) ℚ)
    (Z : NativeChannels (V := V) (p := p) N) :
    channelCycleClass N (allNNativeF N U J M C B Z) =
      allNBettiF N U J M C B (channelCycleClass N Z) := by
  funext i
  simp only [channelCycleClass, allNNativeF, allNBettiF]
  simp [map_add, map_sum, map_smul,
    U.cycleClass_cycleOperator,
    J.cycleClass_cycleOperator,
    M.cycleClass_cycleOperator]

/-- Specialize to the NEW zero-local-SURVIVE companion transport
at any N: the geometric square remains exact for actual certified
original-X U,J,M operators and ANY rational navigation B. -/
theorem companion_originalX_cycleClass_square (N : Nat)
    (U J M : CycleClassOperatorPair V H p)
    (coeff : Nat → ℚ) (address : Matrix (Fin N) (Fin N) ℚ)
    (Z : NativeChannels (V := V) (p := p) N) :
    channelCycleClass N
      (allNNativeF N U J M (companionSource N coeff) address Z) =
    allNBettiF N U J M (companionSource N coeff) address
      (channelCycleClass N Z) :=
  allN_originalX_cycleClass_square N U J M
    (companionSource N coeff) address Z

/-- The source coefficient acting ON the same world is zero for
every original N-hole channel when the companion is zero trace. -/
theorem companion_originalX_no_local_source (N : Nat)
    (coeff : Nat → ℚ) (htrace : coeff (N - 1) = 0)
    (i : Fin N) :
    companionSource N coeff i i = 0 :=
  companionSource_zero_diagonal N coeff htrace i

#check allNNativeF
#check allNBettiF
#check allN_originalX_cycleClass_square
#check companion_originalX_cycleClass_square
#check companion_originalX_no_local_source
#print axioms allN_originalX_cycleClass_square
#print axioms companion_originalX_no_local_source

end GSTImageThreeAllNOriginalXSourceTransport
