import GSTGraphV2CanonicalEscape
import GSTGraphV2CanonicalTerminalExtinctionProbe

set_option maxRecDepth 1000000
set_option maxHeartbeats 20000000

namespace GSTGraphV2CanonicalSignedPrefixBridge

open GSTCanonicalSevenAxisBridge
open GSTU2DEventTransport
open GSTGraphV2InfiniteControl
open GSTGraphV2SeededPrefix
open GSTGraphV2CanonicalEscape
open GSTGraphV2PerfectPowerBlock
open GSTGraphV2HandwrittenAnchoredCocycle
open GSTGraphV2CanonicalTerminalExtinctionProbe
open GSTGraphV2CoupledUFlux

/-- Canonical specialization of the exact signed U-prefix certificate.
The child is the seed-zero canonical tail; the all-bad right boundary is the
seed-one canonical parent. -/
theorem canonical_seeded_u_gap_positive
    (s n q : Nat)
    (hChild : SeedHappy 0 0 (canonicalChildTail s n) q)
    (hRightBad : ∀ j,
      ¬ SeedHappy 1 1 (canonicalParentTail s n) j) :
    0 < Finset.sum (Finset.range (q+1)) (fun j =>
      (((3^j : Nat) : Int)) *
        (gstUJumpExact
            (GSTV2.affineCarry 1 (canonicalParentTail s n) j)
            (GSTV2.digit (canonicalParentTail s n) j) -
          (((4^(3^s) : Nat) : Int)) *
            gstUJumpExact
              (GSTV2.affineCarry 0 (canonicalChildTail s n) j)
              (GSTV2.digit (canonicalChildTail s n) j))) := by
  apply seeded_coupled_weighted_u_gap_positive
  · positivity
  · have h := (seedHappy_zero_iff (canonicalChildTail s n) q).1 hChild
    simpa [GSTV2.Happy, HappyCell, GSTV2.naturalCarry, GSTV2.digit,
      carry4, digit3] using h
  · intro j hHappy
    apply hRightBad j
    rw [seedHappy_one_iff]
    simpa [GSTV2.Happy, HappyCell,
      GSTGraphV2InfiniteControl.seededCarry,
      GSTV2.affineCarry, GSTV2.digit, digit3] using hHappy

/-- The same signed certificate on the literal physical canonical block. -/
theorem canonical_graph_u_gap_positive
    (s n q : Nat) (hs : 1 ≤ s)
    (hChild : SeedHappy 0 0 (canonicalChildTail s n) q)
    (hRightBad : ∀ j,
      ¬ SeedHappy 1 1 (canonicalParentTail s n) j) :
    0 < Finset.sum (Finset.range (q+1)) (fun j =>
      (((3^j : Nat) : Int)) *
        (gstUJumpExact
            (graph (canonicalEnergy s n) (canonicalWidth s) (s+2+j)).seven.carry
            (graph (canonicalEnergy s n) (canonicalWidth s) (s+2+j)).seven.digit -
          (((4^(canonicalWidth s) : Nat) : Int)) *
            gstUJumpExact
              (graph (canonicalEnergy s n) 0 (s+2+j)).seven.carry
              (graph (canonicalEnergy s n) 0 (s+2+j)).seven.digit)) := by
  have hGap :=
    canonical_seeded_u_gap_positive s n q hChild hRightBad
  simpa [canonicalEnergy, canonicalWidth,
    canonical_left_u_jump_adapter s n _ hs,
    canonical_right_u_jump_adapter s n _ hs] using hGap

/-- Exact positive vertical U-potential growth across the canonical block. -/
theorem canonical_graph_u_potential_growth_positive
    (s n q : Nat) (hs : 1 ≤ s)
    (hChild : SeedHappy 0 0 (canonicalChildTail s n) q)
    (hRightBad : ∀ j,
      ¬ SeedHappy 1 1 (canonicalParentTail s n) j) :
    0 <
      (((3^(q+1) : Nat) : Int)) *
          graphUPotential
            (canonicalEnergy s n) 0 (canonicalWidth s) (s+2+(q+1)) -
        graphUPotential
          (canonicalEnergy s n) 0 (canonicalWidth s) (s+2) := by
  rw [← graph_u_equationIII_shifted_telescope
    (canonicalEnergy s n) 0 (canonicalWidth s) (s+2) (q+1)]
  simpa [Nat.add_assoc] using
    canonical_graph_u_gap_positive s n q hs hChild hRightBad

#check canonical_seeded_u_gap_positive
#check canonical_graph_u_gap_positive
#check canonical_graph_u_potential_growth_positive
#print axioms canonical_seeded_u_gap_positive
#print axioms canonical_graph_u_gap_positive
#print axioms canonical_graph_u_potential_growth_positive

end GSTGraphV2CanonicalSignedPrefixBridge
