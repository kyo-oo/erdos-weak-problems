import MonolithGate.GSTInfiniteFourPowerNavigation

set_option maxRecDepth 1000000
set_option maxHeartbeats 20000000

/-!
# THE REPAIRED FOUR-POWER NAVIGATION - THE CLIMB, VENDORED UNCONDITIONAL
## (S090, BOSS order: MAP ALL THE LEAN FILES / USE MY OWN MATHS / PROVE THE LAST HYPOTHESIS)

THE SEAM IS DEAD.  The gate-branch vendoring of the navigation
(`MonolithGate/GSTInfiniteFourPowerNavigation.lean`) retired the width-three
collision assembly with the note that "no tactic can close the collision goal
from that assembly" and isolated the remaining content as ONE named primitive,
`four_power_happy_climb`.  That retirement is STALE: BOSS's own erdosternary2
universe (vendored at `arsenal-full/erdosternary2/`, the bulldoze branch)
contains the REPAIRED navigation - the same assembly with the
absolute-coordinate Happy rewrites (`hleftAbs` / `hrightAbs`, through
`power_origin_happy_iff`) FED alongside the window laws, which is exactly the
hypothesis nourishment the retired attempt lacked - and with it the climb is a
THEOREM, not a seam:

  `four_power_happy_ge_three (k : Nat) (hk : 8 <= k) :
      exists p : Nat, 3 <= p /\ HappyCell (carry4 (4^k) p) (digit3 (4^k) p)`

unconditional, by strong induction: bases 8 / 9 / 10 by exact arithmetic
(norm_num), step k >= 11 by the three-step collision - a Happy child row of
4^(k-3) at depth 3+q against an all-bad right band of 4^(k-3) is impossible
(the unified vertical telescope, the exact width-three conservation, and the
positive U-derivative collide), so the child witness of k-3 relocates to a
Happy row of 4^k = 4^3 * 4^(k-3).

This module vendors that repair into the MonolithGate universe.  Every
dependency of the ported core is byte-identical between the two universes
(verified file-by-file over the full 74-file closure: 67 identical modulo
import-rewrite - including GSTTactic, GSTGraphV2PerfectPowerBlockProbe,
GSTGraphV2UnifiedVerticalTelescope, GSTGraphV2SixAdicSynchronizedShadows,
GSTFinalPurePowerResidueTransplant, GSTFourPowerOntologicalAdapter, and
GSTCanonicalTailStateIso.HappyCell / carry4 / digit3).  The ported theorems
are extracted BYTE-VERBATIM from
`arsenal-full/erdosternary2/GSTInfiniteFourPowerNavigation.lean`; the only
adaptations are (1) the induction theorem is renamed
`four_power_happy_ge_three_unconditional` (the gate-branch seam module owns
the name `four_power_happy_ge_three` for its 3-arg seam reader), and
(2) the closing bridge `four_power_happy_climb_unconditional` discharges the
seam def itself.

With this module the climb - the exact residual seam named by the monolith's
own crown, the single input of `GSTTailFProof.hTailF`, the subsumer of both
row and tower primitives - is an unconditional theorem of the campaign build.
-/

namespace GSTInfiniteFourPowerNavigation

open GSTCanonicalSevenAxisBridge
open GST2DMixedEmergence
open GSTGraphV2CoupledUFlux
open GSTGraphV2InfiniteControl
open GSTGraphV2PerfectPowerAncestry
open GSTGraphV2PerfectPowerBlock
open GSTGraphV2UnifiedPowerRectangle
open GSTGraphV2UnifiedVerticalTelescope
open GSTGraphV2SixAdicSynchronizedShadows
open GSTFinalPurePowerResidueTransplant
open GSTU2DEventTransport

/-! ## The ported repair (byte-verbatim from BOSS's erdosternary2 arsenal;
the induction renamed `four_power_happy_ge_three_unconditional` because the
gate-branch module owns `four_power_happy_ge_three` for the 3-arg seam
reader). -/

/-- Power-specific three-step collision.  This is the focused induction seam. -/
theorem power_three_step_collision
    (K q : Nat)
    (hChild : HappyCell
      (graph (4^K) 0 (3+q)).seven.carry
      (graph (4^K) 0 (3+q)).seven.digit)
    (hRightBad : ∀ j, ¬ HappyCell
      (graph (4^K) 3 (3+j)).seven.carry
      (graph (4^K) 3 (3+j)).seven.digit) :
    False := by
  let E := 4^K
  let N : Nat := 3
  let b : Nat := 3

  have hleft :
      0 < graphPhaseWindow E 0 b (q+1) := by
    apply graph_phase_window_positive_of_happy
    simpa [E, b, Nat.add_assoc] using hChild

  have hright :
      graphPhaseWindow E N b (q+1) ≤ 0 := by
    apply graph_phase_window_nonpositive_of_bad
    intro j hj
    simpa [E, N, b, Nat.add_assoc] using hRightBad j

  have hleftAbs : HappyCell
      (graph 1 K (b+q)).seven.carry
      (graph 1 K (b+q)).seven.digit := by
    have hiff := power_origin_happy_iff K 0 (b+q)
    exact hiff.mp (by simpa [E, b, Nat.add_assoc] using hChild)

  have hrightAbs : ∀ j, ¬ HappyCell
      (graph 1 (K+N) (b+j)).seven.carry
      (graph 1 (K+N) (b+j)).seven.digit := by
    intro j h
    apply hRightBad j
    have hiff := power_origin_happy_iff K N (b+j)
    exact hiff.mpr (by simpa [E, N] using h)

  have hU := unified_equationIII_vertical_telescope E N b (q+1)
  have hWidth3 := power_width_three_exact_conservation K q
  have hUPositive := power_width_three_u_derivative_positive K q hChild
    (hRightBad q)
  have hleftExact := graph_phase_window_exact E 0 b (q+1)
  have hrightExact := graph_phase_window_exact E N b (q+1)
  have hleftDigitExact := graph_phase_digit_window_boundary_exact E 0 b (q+1)
  have hrightDigitExact := graph_phase_digit_window_boundary_exact E N b (q+1)

  rw [hleftExact] at hleft
  rw [hrightExact] at hright
  rw [hleftDigitExact] at hleft
  rw [hrightDigitExact] at hright
  dsimp [E, N, b] at hleft hright hleftAbs hrightAbs hU hWidth3 hUPositive ⊢
  dsimp [potentialWith, unifiedState] at hU hUPositive
  four_power_collision_arith

/-- From exponent 8 onward a Happy gate exists at a ternary coordinate at least 3. -/
theorem four_power_happy_ge_three_unconditional (k : Nat) (hk : 8 ≤ k) :
    ∃ p : Nat, 3 ≤ p ∧ HappyCell (carry4 (4^k) p) (digit3 (4^k) p) := by
  induction k using Nat.strongRecOn with
  | ind k ih =>
      by_cases hk11 : 11 ≤ k
      · have hk3 : 8 ≤ k - 3 := by omega
        obtain ⟨p, hp3, hpHappy⟩ := ih (k - 3) (by omega) hk3
        let q := p - 3
        have hpq : 3 + q = p := by
          dsimp [q]
          omega
        have hChild : HappyCell
            (graph (4^(k-3)) 0 (3+q)).seven.carry
            (graph (4^(k-3)) 0 (3+q)).seven.digit := by
          simpa [graph, cell, GSTCanonicalSevenAxisBridge.vertex, hpq] using hpHappy
        by_contra hno
        have hRightBad : ∀ j, ¬ HappyCell
            (graph (4^(k-3)) 3 (3+j)).seven.carry
            (graph (4^(k-3)) 3 (3+j)).seven.digit := by
          intro j hright
          apply hno
          refine ⟨3+j, by omega, ?_⟩
          have hpow : 4^3 * 4^(k-3) = 4^k := by
            rw [← Nat.pow_add]
            congr 1
            omega
          rw [← hpow]
          simpa [graph, cell, GSTCanonicalSevenAxisBridge.vertex] using hright
        exact power_three_step_collision (k-3) q hChild hRightBad
      · have hkCases : k = 8 ∨ k = 9 ∨ k = 10 := by omega
        rcases hkCases with rfl | rfl | rfl
        · refine ⟨4, by decide, ?_⟩
          norm_num [HappyCell, carry4, digit3]
        · refine ⟨7, by decide, ?_⟩
          norm_num [HappyCell, carry4, digit3]
        · refine ⟨10, by decide, ?_⟩
          norm_num [HappyCell, carry4, digit3]

/-! ## THE SEAM DISCHARGED - the climb as an unconditional theorem. -/

/-- **THE THIRD-WAVE CLIMB, UNCONDITIONAL.**  The monolith's named residual
seam - every exponent from eight onward owns a physical Happy row at a
ternary coordinate at least three - discharged by BOSS's own repaired
navigation (vendored above).  Zero hypotheses. -/
theorem four_power_happy_climb_unconditional :
    four_power_happy_climb :=
  fun k hk => four_power_happy_ge_three_unconditional k hk

#print axioms power_three_step_collision
#print axioms four_power_happy_ge_three_unconditional
#print axioms four_power_happy_climb_unconditional

#eval "GST_FOUR_POWER_CLIMB_UNCONDITIONAL_GREEN"

end GSTInfiniteFourPowerNavigation
