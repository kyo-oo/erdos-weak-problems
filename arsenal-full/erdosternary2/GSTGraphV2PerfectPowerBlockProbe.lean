import GSTGraphV2PerfectPowerAncestry
import GSTU2DCanonicalPhaseDensity
import GSTGraphV2UnifiedPowerRectangle
import GSTGraphV2UnifiedVerticalTelescope

set_option maxRecDepth 1000000
set_option maxHeartbeats 10000000

namespace GSTGraphV2PerfectPowerBlock

open GSTCanonicalSevenAxisBridge
open GST2DMixedEmergence
open GSTU2DEventTransport
open GSTGraphV2InfiniteControl
open GSTU2DCanonicalPhaseDensity
open GSTGraphV2UnifiedPowerRectangle
open GSTGraphV2UnifiedVerticalTelescope

/-- The canonical full energy and the exact horizontal perfect-power width. -/
def canonicalEnergy (s n : Nat) : Nat := 4^(3^(s+1) * n)
def canonicalWidth (s : Nat) : Nat := 3^s

/-- A Happy cell on any column of the main Graph-V2 sheet creates strictly
positive base-three weighted phase pressure below and including that row. -/
theorem graph_phase_prefix_positive_of_happy
    (E t q : Nat)
    (hHappy : HappyCell
      (graph E t q).seven.carry
      (graph E t q).seven.digit) :
    0 < weightedPhaseColumnPrefix
      (fun p => (graph E t p).seven.carry)
      (fun p => (graph E t p).seven.digit) (q+1) := by
  apply weightedPhaseColumnPrefix_positive_of_top_happy
  · intro p hp
    exact graph_carry_lt_four E t p
  · intro p hp
    exact graph_digit_lt_three E t p
  · exact hHappy

/-- Conversely, a genuinely bad Graph-V2 column has nonpositive weighted
phase pressure at every finite observation height.  No support or terminal
hypothesis appears: `K` is an arbitrary observation height. -/
theorem graph_phase_prefix_nonpositive_of_bad
    (E t K : Nat)
    (hBad : ∀ p, p < K → ¬ HappyCell
      (graph E t p).seven.carry
      (graph E t p).seven.digit) :
    weightedPhaseColumnPrefix
      (fun p => (graph E t p).seven.carry)
      (fun p => (graph E t p).seven.digit) K ≤ 0 := by
  induction K with
  | zero =>
      simp [weightedPhaseColumnPrefix]
  | succ K ih =>
      have ih' := ih (fun p hp => hBad p (by omega))
      have hlocal :
          phaseDensity
              (graph E t K).seven.carry
              (graph E t K).seven.digit ≤ 0 :=
        phaseDensity_nonpositive_of_not_happy
          (graph E t K).seven.carry
          (graph E t K).seven.digit
          (graph_carry_lt_four E t K)
          (graph_digit_lt_three E t K)
          (hBad K (by omega))
      have hw : (0 : Int) ≤ (((3^K : Nat) : Int)) := by positivity
      rw [weightedPhaseColumnPrefix]
      exact add_nonpos ih' (mul_nonpos_of_nonneg_of_nonpos hw hlocal)

/-- Recursive phase prefix equals its literal base-three weighted finite sum. -/
theorem weightedPhaseColumnPrefix_eq_sum
    (C d : Nat → Nat) (K : Nat) :
    weightedPhaseColumnPrefix C d K =
      Finset.sum (Finset.range K) (fun p =>
        (((3^p : Nat) : Int)) * phaseDensity (C p) (d p)) := by
  induction K with
  | zero => simp [weightedPhaseColumnPrefix]
  | succ K ih =>
      rw [weightedPhaseColumnPrefix, Finset.sum_range_succ, ih]

/-- Exact reconstruction of the first `K` ternary digits.  This is the
arithmetic boundary identity needed to turn the phase-density divergence into
an equality of literal residues of the same perfect-power sheet. -/
theorem digit3_weighted_prefix_nat (R K : Nat) :
    Finset.sum (Finset.range K) (fun p => 3^p * digit3 R p) =
      R % 3^K := by
  induction K with
  | zero => simp [Nat.mod_one]
  | succ K ih =>
      rw [Finset.sum_range_succ, ih, Nat.pow_succ]
      unfold digit3
      rw [Nat.mod_mul]

/-- Integer chart of the same exact ternary-prefix reconstruction. -/
theorem digit3_weighted_prefix_int (R K : Nat) :
    Finset.sum (Finset.range K) (fun p =>
      (((3^p : Nat) : Int)) * ((digit3 R p : Nat) : Int)) =
        ((R % 3^K : Nat) : Int) := by
  exact_mod_cast digit3_weighted_prefix_nat R K

/-- Graph digits are literal ternary digits of `4^t * E`; hence their weighted
prefix is exactly the corresponding residue of that one arithmetic energy. -/
theorem graph_digit_weighted_prefix_exact (E t K : Nat) :
    Finset.sum (Finset.range K) (fun p =>
      (((3^p : Nat) : Int)) * (((graph E t p).seven.digit : Nat) : Int)) =
        (((4^t * E) % 3^K : Nat) : Int) := by
  simpa [graph, cell, GSTCanonicalSevenAxisBridge.vertex] using
    digit3_weighted_prefix_int (4^t * E) K

/-- The exact phase-column divergence specialized to the main infinite graph.
This is the conservation equation used by the perfect-power regeneration step. -/
theorem graph_phase_column_exact (E t K : Nat) :
    weightedPhaseColumnPrefix
        (fun p => (graph E t p).seven.carry)
        (fun p => (graph E t p).seven.digit) K =
      Finset.sum (Finset.range K) (fun p =>
        (((3^p : Nat) : Int)) *
          (phaseDigitPotential (graph E (t+1) p).seven.digit -
           phaseDigitPotential (graph E t p).seven.digit)) +
      phaseCarryPotential (graph E t 0).seven.carry -
        (((3^K : Nat) : Int)) *
          phaseCarryPotential (graph E t K).seven.carry +
      Finset.sum (Finset.range K) (fun p =>
        (((3^p : Nat) : Int)) *
          surviveI (graph E t p).seven.carry (graph E t p).seven.digit) := by
  rw [weightedPhaseColumnPrefix_eq_sum]
  have h := phaseColumn_exact
    (fun p => (graph E t p).seven.carry)
    (fun p => (graph E t p).seven.digit)
    (fun p => (graph E (t+1) p).seven.digit) K
    (by
      intro p hp
      exact ⟨graph_carry_lt_four E t p,
        graph_digit_lt_three E t p,
        (graph_cell_exact E t p).1,
        (graph_cell_exact E t p).2⟩)
  simpa using h

/-- Perfect-power ancestry can be used at the block level without changing any
physical Happy observable. -/
theorem canonical_power_origin_happy_iff
    (s n t p : Nat) :
    HappyCell
        (graph (canonicalEnergy s n) t p).seven.carry
        (graph (canonicalEnergy s n) t p).seven.digit ↔
      HappyCell
        (graph 1 (3^(s+1) * n + t) p).seven.carry
        (graph 1 (3^(s+1) * n + t) p).seven.digit := by
  simpa [canonicalEnergy] using
    GSTGraphV2PerfectPowerAncestry.power_origin_happy_iff
      (3^(s+1) * n) t p

/-! ## Shifted production window

The production socket starts at the exact canonical cut `b = s+2`.  The next
four lemmas move the all-depth phase equation to that cut without introducing
a support horizon or terminal row. -/

/-- Phase pressure in the vertical window beginning at the genuine production
slice `b`. -/
def graphPhaseWindow (E t b K : Nat) : Int :=
  weightedPhaseColumnPrefix
    (fun j => (graph E t (b+j)).seven.carry)
    (fun j => (graph E t (b+j)).seven.digit) K

/-- A Happy cell at the top of a shifted observation window forces positive
pressure in that exact window. -/
theorem graph_phase_window_positive_of_happy
    (E t b q : Nat)
    (hHappy : HappyCell
      (graph E t (b+q)).seven.carry
      (graph E t (b+q)).seven.digit) :
    0 < graphPhaseWindow E t b (q+1) := by
  unfold graphPhaseWindow
  apply weightedPhaseColumnPrefix_positive_of_top_happy
  · intro p hp
    exact graph_carry_lt_four E t (b+p)
  · intro p hp
    exact graph_digit_lt_three E t (b+p)
  · exact hHappy

/-- Complete badness above the same production cut makes every shifted phase
window nonpositive.  `K` remains an arbitrary observation depth. -/
theorem graph_phase_window_nonpositive_of_bad
    (E t b K : Nat)
    (hBad : ∀ j, j < K → ¬ HappyCell
      (graph E t (b+j)).seven.carry
      (graph E t (b+j)).seven.digit) :
    graphPhaseWindow E t b K ≤ 0 := by
  unfold graphPhaseWindow
  induction K with
  | zero => simp [weightedPhaseColumnPrefix]
  | succ K ih =>
      have ih' := ih (fun j hj => hBad j (by omega))
      have hlocal :
          phaseDensity
              (graph E t (b+K)).seven.carry
              (graph E t (b+K)).seven.digit ≤ 0 :=
        phaseDensity_nonpositive_of_not_happy
          (graph E t (b+K)).seven.carry
          (graph E t (b+K)).seven.digit
          (graph_carry_lt_four E t (b+K))
          (graph_digit_lt_three E t (b+K))
          (hBad K (by omega))
      have hw : (0 : Int) ≤ (((3^K : Nat) : Int)) := by positivity
      rw [weightedPhaseColumnPrefix]
      exact add_nonpos ih' (mul_nonpos_of_nonneg_of_nonpos hw hlocal)

/-- Exact ternary digit shift through the production prefix. -/
theorem digit3_add_shift (R b q : Nat) :
    digit3 R (b+q) = digit3 (R / 3^b) q := by
  unfold digit3
  rw [Nat.pow_add, ← Nat.div_div_eq_div_mul]

/-- The shifted graph digit boundary is the literal ternary residue of the
exposed quotient above the production cut. -/
theorem graph_digit_window_exact (E t b K : Nat) :
    Finset.sum (Finset.range K) (fun j =>
      (((3^j : Nat) : Int)) *
        (((graph E t (b+j)).seven.digit : Nat) : Int)) =
      ((((4^t * E) / 3^b) % 3^K : Nat) : Int) := by
  simpa [graph, cell, GSTCanonicalSevenAxisBridge.vertex, digit3_add_shift] using
    digit3_weighted_prefix_int ((4^t * E) / 3^b) K

/-- Exact phase divergence on the shifted production window.  The upper carry
boundary remains live; nothing is truncated or replaced by a terminal state. -/
theorem graph_phase_window_exact (E t b K : Nat) :
    graphPhaseWindow E t b K =
      Finset.sum (Finset.range K) (fun j =>
        (((3^j : Nat) : Int)) *
          (phaseDigitPotential (graph E (t+1) (b+j)).seven.digit -
           phaseDigitPotential (graph E t (b+j)).seven.digit)) +
      phaseCarryPotential (graph E t b).seven.carry -
        (((3^K : Nat) : Int)) *
          phaseCarryPotential (graph E t (b+K)).seven.carry +
      Finset.sum (Finset.range K) (fun j =>
        (((3^j : Nat) : Int)) *
          surviveI
            (graph E t (b+j)).seven.carry
            (graph E t (b+j)).seven.digit) := by
  unfold graphPhaseWindow
  rw [weightedPhaseColumnPrefix_eq_sum]
  have h := phaseColumn_exact
    (fun j => (graph E t (b+j)).seven.carry)
    (fun j => (graph E t (b+j)).seven.digit)
    (fun j => (graph E (t+1) (b+j)).seven.digit) K
    (by
      intro j hj
      exact ⟨graph_carry_lt_four E t (b+j),
        graph_digit_lt_three E t (b+j),
        (graph_cell_exact E t (b+j)).1,
        by simpa [Nat.add_assoc] using (graph_cell_exact E t (b+j)).2⟩)
  simpa [Nat.add_zero] using h

/-- The digit part of the shifted phase divergence is an exact difference of
two exposed ternary residues. -/
theorem graph_phase_digit_window_boundary_exact (E t b K : Nat) :
    Finset.sum (Finset.range K) (fun j =>
      (((3^j : Nat) : Int)) *
        (phaseDigitPotential (graph E (t+1) (b+j)).seven.digit -
         phaseDigitPotential (graph E t (b+j)).seven.digit)) =
      ((((4^(t+1) * E) / 3^b) % 3^K : Nat) : Int) -
      ((((4^t * E) / 3^b) % 3^K : Nat) : Int) := by
  calc
    Finset.sum (Finset.range K) (fun j =>
      (((3^j : Nat) : Int)) *
        (phaseDigitPotential (graph E (t+1) (b+j)).seven.digit -
         phaseDigitPotential (graph E t (b+j)).seven.digit)) =
      Finset.sum (Finset.range K) (fun j =>
        (((3^j : Nat) : Int)) * (((graph E (t+1) (b+j)).seven.digit : Nat) : Int) -
        (((3^j : Nat) : Int)) * (((graph E t (b+j)).seven.digit : Nat) : Int)) := by
          apply Finset.sum_congr rfl
          intro j hj
          simp [phaseDigitPotential]
          ring
    _ =
      Finset.sum (Finset.range K) (fun j =>
        (((3^j : Nat) : Int)) * (((graph E (t+1) (b+j)).seven.digit : Nat) : Int)) -
      Finset.sum (Finset.range K) (fun j =>
        (((3^j : Nat) : Int)) * (((graph E t (b+j)).seven.digit : Nat) : Int)) := by
          rw [Finset.sum_sub_distrib]
    _ = _ := by
      rw [graph_digit_window_exact, graph_digit_window_exact]

#check graph_phase_prefix_positive_of_happy
#check graph_phase_prefix_nonpositive_of_bad
#check weightedPhaseColumnPrefix_eq_sum
#check digit3_weighted_prefix_nat
#check graph_digit_weighted_prefix_exact
#check graph_phase_column_exact
#check canonical_power_origin_happy_iff
#check graph_phase_window_positive_of_happy
#check graph_phase_window_nonpositive_of_bad
#check graph_digit_window_exact
#check graph_phase_window_exact
#check graph_phase_digit_window_boundary_exact
#print axioms graph_phase_window_positive_of_happy
#print axioms graph_phase_window_nonpositive_of_bad
#print axioms graph_phase_window_exact
#print axioms graph_phase_digit_window_boundary_exact

end GSTGraphV2PerfectPowerBlock
