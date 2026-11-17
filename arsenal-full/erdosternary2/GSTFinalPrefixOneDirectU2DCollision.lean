import GSTU2DSharpCrossingBlock
import GSTGraphV2InfiniteControllerBridge
import GSTPerfectPowerTailNavigation
import GSTGraphV2HandwrittenOmegaUBlock

set_option maxRecDepth 1000000
set_option maxHeartbeats 20000000

namespace GSTFinalPrefixOneDirectU2DCollision

open GSTCanonicalSevenAxisBridge
open GST2DMixedEmergence
open GSTU2DEventTransport
open GSTGraphV2InfiniteControl
open GSTGraphV2HandwrittenOmegaUBlock
open GSTGraphV2InfiniteControllerBridge
open GSTU2DExactCrossingCharge
open GSTPerfectPowerTailNavigation

private def collisionC (s n : Nat) : Nat → Nat → Nat :=
  fun t p => (graph (residualEnergy s 1 n) t (s + 2 + p)).seven.carry

private def collisionD (s n : Nat) : Nat → Nat → Nat :=
  fun t p => (graph (residualEnergy s 1 n) t (s + 2 + p)).seven.digit

/-- The monolith's `gstNavigationConstant (s+1) n` is exactly this standalone
canonical tail.  This is the mathematical child object of the final splice. -/
def directChild (s n : Nat) : Nat := canonicalTail (s+1) n

theorem residualWidth_pos_of_s_pos
    (s : Nat) (hs : 1 ≤ s) : 1 ≤ residualWidth s := by
  unfold residualWidth
  have hpos : 0 < 3^s := Nat.pow_pos (by decide)
  omega

/-- A supplied child Navigation witness is a literal physical Happy cell on
row `s+2+q` of the left edge of the canonical residual rectangle. -/
theorem child_navigation_to_left_happy
    (s n : Nat) (hs : 1 ≤ s)
    (hchild : GSTCanonicalTailStateIso.Navigation (directChild s n)) :
    ∃ q,
      HappyCell
        (graph (residualEnergy s 1 n) 0 (s+2+q)).seven.carry
        (graph (residualEnergy s 1 n) 0 (s+2+q)).seven.digit := by
  obtain ⟨q, hHappyTail⟩ := hchild
  let E := residualEnergy s 1 n
  let T := directChild s n
  have hE : E = 1 + 3^(s+2) * T := by
    have h := canonical_tail_decomposition (s+1) n
    simpa [E, T, directChild, residualEnergy, Nat.add_assoc] using h
  have hone : 1 < 3^(s+2) := by
    have h9 : 9 ≤ 3^(s+2) := by
      rw [show (9 : Nat) = 3^2 by decide]
      exact Nat.pow_le_pow_of_le (by decide : 1 < 3) (by omega)
    omega
  have hiff := graph_prefix_slice_happy_iff
    E 0 (s+2) 1 T q
    (by simpa using hE)
    hone
  refine ⟨q, hiff.2 ?_⟩
  have hfour : 4 < 3^(s+2) := by
    have h27 : 27 ≤ 3^(s+2) := by
      rw [show (27 : Nat) = 3^3 by decide]
      exact Nat.pow_le_pow_of_le (by decide : 1 < 3) (by omega)
    omega
  have hseed : (4 * 1) / 3^(s+2) = 0 := Nat.div_eq_of_lt hfour
  rcases hHappyTail with ⟨hd, hc⟩
  refine ⟨?_, ?_⟩
  · simpa [T, directChild, GSTCanonicalTailStateIso.digit3,
      GSTCanonicalSevenAxisBridge.digit3] using hd
  · simpa [T, directChild, seededCarry, GSTCanonicalTailStateIso.carry4,
      GSTCanonicalSevenAxisBridge.carry4, hseed] using hc

/-- The residual child power has true zero carry at the production cut. -/
theorem residual_base_carry_zero
    (s n : Nat) (hs : 1 ≤ s) :
    (graph (residualEnergy s 1 n) 0 (s+2)).seven.carry = 0 := by
  let E := residualEnergy s 1 n
  let b := s + 2
  let T := canonicalTail (s+1) n
  have hE : E = 1 + 3^b * T := by
    have h := canonical_tail_decomposition (s+1) n
    simpa [E, b, T, residualEnergy, Nat.add_assoc] using h
  have hb : 1 < 3^b := by
    have h9 : 9 ≤ 3^b := by
      rw [show (9 : Nat) = 3^2 by decide]
      exact Nat.pow_le_pow_of_le (by decide : 1 < 3) (by dsimp [b]; omega)
    omega
  have hmod : E % 3^b = 1 := by
    rw [hE]
    have hmul : (3^b * T) % 3^b = 0 :=
      Nat.mod_eq_zero_of_dvd (Nat.dvd_mul_right _ _)
    calc
      (1 + 3^b * T) % 3^b = (1 % 3^b + (3^b * T) % 3^b) % 3^b := Nat.add_mod _ _ _
      _ = (1 % 3^b) % 3^b := by rw [hmul, Nat.add_zero]
      _ = 1 % 3^b := Nat.mod_mod_of_dvd _ (dvd_refl (3^b))
      _ = 1 := Nat.mod_eq_of_lt hb
  have hc : carry4 E b = 0 := by
    unfold carry4
    rw [hmod]
    apply Nat.div_eq_of_lt
    have hb27 : 27 ≤ 3^b := by
      rw [show (27 : Nat) = 3^3 by decide]
      exact Nat.pow_le_pow_of_le (by decide : 1 < 3) (by dsimp [b]; omega)
    omega
  simpa [E, b, graph, cell, GSTCanonicalSevenAxisBridge.vertex] using hc

/-- Exact U2D crossing telescope on the canonical finite rectangle. -/
theorem collision_rectangle_exact
    (s n K : Nat) :
    Finset.sum (Finset.range K) (fun p =>
      (((3^p : Nat) : Int)) *
        reverseCrossCode (fun t => collisionC s n t p)
          (fun t => collisionD s n t p) (residualWidth s)) =
      Finset.sum (Finset.range K) (fun p =>
        (((3^p : Nat) : Int)) *
          (digitPotential (collisionD s n (residualWidth s) p) -
            (((4^(residualWidth s) : Nat) : Int)) *
              digitPotential (collisionD s n 0 p) +
            84 * reverseSurviveCode (fun t => collisionC s n t p)
              (fun t => collisionD s n t p) (residualWidth s))) +
      reverseCarryCode (fun t => collisionC s n t 0) (residualWidth s) -
        (((3^K : Nat) : Int)) *
          reverseCarryCode (fun t => collisionC s n t K) (residualWidth s) := by
  apply reverseCrossRectangle_exact
  intro t p ht hp
  exact ⟨graph_carry_lt_four (residualEnergy s 1 n) t (s+2+p),
    graph_digit_lt_three (residualEnergy s 1 n) t (s+2+p),
    (graph_cell_exact (residualEnergy s 1 n) t (s+2+p)).1,
    by
      simpa [collisionC, collisionD, Nat.add_assoc] using
        (graph_cell_exact (residualEnergy s 1 n) t (s+2+p)).2⟩

/-- Step 6 of the final derivation.  Unlike a merely finite right-prefix sign
claim, this hypothesis is the complete all-depth right bad language and is
immediately packaged as the exact Infinite Controller. -/
theorem canonical_right_bad_forces_weighted_cross_nonpositive
    (s n q : Nat) (hs : 1 ≤ s) (hn : 1 ≤ n)
    (hRightBad : ∀ j,
      ¬ HappyCell
        (graph (residualEnergy s 1 n) (residualWidth s) (s+2+j)).seven.carry
        (graph (residualEnergy s 1 n) (residualWidth s) (s+2+j)).seven.digit) :
    weightedCrossPrefix (collisionC s n) (collisionD s n)
      (residualWidth s) (q+1) ≤ 0 := by
  let E := residualEnergy s 1 n
  let N := residualWidth s
  let b := s + 2
  have hBaseCarryZero : (graph E 0 b).seven.carry = 0 := by
    simpa [E, b] using residual_base_carry_zero s n hs
  have hController :
      GSTV2.InfiniteBadCoupledControl (4^N) (graphCoupledState E N b) := by
    apply graph_infinite_bad_control E N b hBaseCarryZero
    intro j
    simpa [E, N, b, Nat.add_assoc] using hRightBad j
  have hRightLocal : ∀ j,
      crossDensity (graph E N (b+j)).seven.carry
        (graph E N (b+j)).seven.digit ≤ 0 := by
    intro j
    exact crossDensity_nonpositive_of_not_happy
      (graph E N (b+j)).seven.carry (graph E N (b+j)).seven.digit
      (graph_carry_lt_four E N (b+j)) (graph_digit_lt_three E N (b+j))
      (by simpa [E, N, b, Nat.add_assoc] using hRightBad j)
  have hRightPrefix :
      Finset.sum (Finset.range (q+1)) (fun p =>
        (((3^p : Nat) : Int)) * crossDensity
          (graph E N (b+p)).seven.carry (graph E N (b+p)).seven.digit) ≤ 0 := by
    apply Finset.sum_nonpos
    intro p hp
    exact mul_nonpos_of_nonneg_of_nonpos (by positivity) (hRightLocal p)
  have hRect := collision_rectangle_exact s n (q+1)
  dsimp [collisionC, collisionD, E, N, b] at hRect ⊢
  trace_state
  omega

/-- Direct formal statement of the mathematical collision: child Navigation
plus an all-depth bad canonical right boundary is impossible. -/
theorem canonical_perfect_power_block_collision_direct
    (s n : Nat) (hs : 1 ≤ s) (hn : 1 ≤ n)
    (hchild : GSTCanonicalTailStateIso.Navigation (directChild s n))
    (hRightBad : ∀ j,
      ¬ HappyCell
        (graph (residualEnergy s 1 n) (residualWidth s) (s+2+j)).seven.carry
        (graph (residualEnergy s 1 n) (residualWidth s) (s+2+j)).seven.digit) :
    False := by
  obtain ⟨q, hChild⟩ := child_navigation_to_left_happy s n hs hchild
  have hPositive :
      0 < weightedCrossPrefix (collisionC s n) (collisionD s n)
        (residualWidth s) (q+1) := by
    apply weightedCrossPrefix_positive_of_top_leading_happy
    · exact residualWidth_pos_of_s_pos s hs
    · intro t p ht hp
      exact graph_carry_lt_four (residualEnergy s 1 n) t (s+2+p)
    · intro t p ht hp
      exact graph_digit_lt_three (residualEnergy s 1 n) t (s+2+p)
    · intro t p ht hp
      exact (graph_cell_exact (residualEnergy s 1 n) t (s+2+p)).1
    · simpa [collisionC, collisionD, Nat.add_assoc] using hChild
  have hNonpositive :=
    canonical_right_bad_forces_weighted_cross_nonpositive
      s n q hs hn hRightBad
  omega

/-- Equivalent no-Navigation form used by the eventual monolith splice. -/
theorem canonical_right_bad_forces_no_child_navigation
    (s n : Nat) (hs : 1 ≤ s) (hn : 1 ≤ n)
    (hRightBad : ∀ j,
      ¬ HappyCell
        (graph (residualEnergy s 1 n) (residualWidth s) (s+2+j)).seven.carry
        (graph (residualEnergy s 1 n) (residualWidth s) (s+2+j)).seven.digit) :
    ¬ GSTCanonicalTailStateIso.Navigation (directChild s n) := by
  intro hchild
  exact canonical_perfect_power_block_collision_direct
    s n hs hn hchild hRightBad

#check child_navigation_to_left_happy
#check residual_base_carry_zero
#check collision_rectangle_exact
#check canonical_right_bad_forces_weighted_cross_nonpositive
#check canonical_perfect_power_block_collision_direct
#check canonical_right_bad_forces_no_child_navigation
#print axioms canonical_perfect_power_block_collision_direct
#print axioms canonical_right_bad_forces_no_child_navigation

end GSTFinalPrefixOneDirectU2DCollision