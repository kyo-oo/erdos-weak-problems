import GSTOmegaTerminalNormalForm
import GSTFinalPrefixOneStep6Infinite

set_option maxRecDepth 1000000
set_option maxHeartbeats 20000000

/-!
# Exact canonical perfect-power Omega-controller equivalence

This applies the new all-depth terminal normal form to the user's
actual residual GST perfect-power source, with no arbitrary surrogate
state and with the true zero-carry left boundary.

It identifies the precise physical parent BAD predicate that remains
to be contradicted in the universal proof. All the source identities
and CoupledInvariant fields are inherited from established exact laws.
-/

namespace GSTOmegaCanonicalBoundaryIff

open GSTGraphV2InfiniteControl
open GSTGraphV2InfiniteControllerBridge
open GSTGraphV2HandwrittenOmegaUBlock
open GSTOmegaTerminalNormalForm
open GSTV2

def source (s n : Nat) : Nat := residualEnergy s 1 n
def width (s : Nat) : Nat := residualWidth s
def baseRow (s : Nat) : Nat := s+2

def initial (s n : Nat) : CoupledState :=
  graphCoupledState (source s n) (width s) (baseRow s)

theorem canonical_source_left_boundary_zero
    (s n : Nat) (hs : 1 ≤ s) :
    (initial s n).childCarry = 0 := by
  have h := GSTFinalPrefixOneStep6Infinite.infinite_base_carry_zero s n hs
  change (graph (residualEnergy s 1 n) 0 (s+2)).seven.carry = 0 at h
  simpa [initial, source, width, baseRow, graphCoupledState] using h

theorem canonical_source_invariant
    (s n : Nat) :
    CoupledInvariant (4^(width s)) (initial s n) := by
  exact graphCoupledState_invariant (source s n) (width s) (baseRow s)

/-- Canonical perfect-power all-depth BAD controller is *equivalent*
to exactly one source-specific preterminal BAD property. This is
an unconditional equivalence; no conjectural collision is used. -/
theorem canonical_infinite_bad_iff_preterminal
    (s n : Nat) (hs : 1 ≤ s) :
    InfiniteBadCoupledControl (4^(width s)) (initial s n) ↔
      ∀ j, j <
        cutoff (initial s n).parentSeed
          ((initial s n).parentWord (4^(width s))) →
        ¬ Happy
          (affineCarry (initial s n).parentSeed
            ((initial s n).parentWord (4^(width s))) j)
          (digit ((initial s n).parentWord (4^(width s))) j) := by
  exact infinite_controller_iff_preterminal
    (4^(width s)) (initial s n) (by positivity)
    (canonical_source_invariant s n)
    (canonical_source_left_boundary_zero s n hs)

/-- Exact canonical all-depth controller hypothesis is not strengthened
by translating it into an infinite ledger: the BAD assumption is
the same at every observational depth, now in true physical coordinates. -/
theorem canonical_bad_iff_seeded_bad
    (s n : Nat) (hs : 1 ≤ s) :
    InfiniteBadCoupledControl (4^(width s)) (initial s n) ↔
      SeededBadTrace (initial s n).parentSeed
        ((initial s n).parentWord (4^(width s))) := by
  exact infinite_controller_iff_seeded_bad
    (4^(width s)) (initial s n) (by positivity)
    (canonical_source_invariant s n)
    (canonical_source_left_boundary_zero s n hs)

#print axioms canonical_source_left_boundary_zero
#print axioms canonical_source_invariant
#print axioms canonical_infinite_bad_iff_preterminal
#print axioms canonical_bad_iff_seeded_bad

end GSTOmegaCanonicalBoundaryIff
