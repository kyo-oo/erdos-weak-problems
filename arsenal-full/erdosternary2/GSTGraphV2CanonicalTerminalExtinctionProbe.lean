import GSTGraphV2HandwrittenAnchoredCocycle
import GSTInfiniteBadTransport

set_option maxRecDepth 1000000
set_option maxHeartbeats 20000000

namespace GSTGraphV2CanonicalTerminalExtinctionProbe

open GSTCanonicalSevenAxisBridge
open GSTU2DEventTransport
open GSTGraphV2InfiniteControl
open GSTGraphV2HandwrittenAnchoredCocycle
open GSTGraphV2CoupledUFlux
open GSTGraphV2UnifiedPowerRectangle

/-- A concrete bridge from a physical Happy Graph-V2 cell to the strict
negative U-jump used by the handwritten vertical conservation law. -/
theorem physical_happy_forces_negative_u_jump
    (E t p : Nat)
    (hH : HappyCell
      (graph E t p).seven.carry
      (graph E t p).seven.digit) :
    gstUJumpExact
      (graph E t p).seven.carry
      (graph E t p).seven.digit < 0 := by
  exact (happy_iff_gst_u_jump_negative _ _
    (graph_carry_lt_four E t p)
    (graph_digit_lt_three E t p)).1 hH

/-- A physical bad Graph-V2 cell contributes a nonnegative U-jump. -/
theorem physical_bad_forces_nonnegative_u_jump
    (E t p : Nat)
    (hB : ¬ HappyCell
      (graph E t p).seven.carry
      (graph E t p).seven.digit) :
    0 ≤ gstUJumpExact
      (graph E t p).seven.carry
      (graph E t p).seven.digit := by
  exact gst_u_jump_nonnegative_of_not_happy _ _
    (graph_carry_lt_four E t p)
    (graph_digit_lt_three E t p) hB

/-- The exact one-row U derivative across a canonical width is strictly
positive whenever the left endpoint is Happy and the right endpoint is bad.
No width-three transport and no collision theorem is imported here. -/
theorem canonical_width_u_derivative_positive
    (s n p : Nat)
    (hLeft : HappyCell
      (graph 1 (3^(s+1) * n) p).seven.carry
      (graph 1 (3^(s+1) * n) p).seven.digit)
    (hRight : ¬ HappyCell
      (graph 1 (3^(s+1) * n + 3^s) p).seven.carry
      (graph 1 (3^(s+1) * n + 3^s) p).seven.digit) :
    0 <
      3 * graphUPotential
        1 (3^(s+1) * n) (3^s) (p+1)
      - graphUPotential
        1 (3^(s+1) * n) (3^s) p := by
  simpa [Nat.add_assoc] using
    graph_u_derivative_positive_of_child_happy_right_bad
      1 (3^(s+1) * n) (3^s) p hLeft hRight

/-- Exact base-three weighted sum of the standalone seeded U jumps. -/
theorem seeded_weighted_u_jump_exact
    (D X K : Nat) :
    Finset.sum (Finset.range K) (fun j =>
      (((3^j : Nat) : Int)) *
        gstUJumpExact
          (GSTV2.affineCarry D X j)
          (GSTV2.digit X j)) =
      (((3^K : Nat) : Int)) *
          gstUChargeExact (GSTV2.affineCarry D X K) -
        gstUChargeExact D -
        24 * ((X % 3^K : Nat) : Int) := by
  induction K with
  | zero =>
      have hx : X % 1 = 0 := Nat.mod_one X
      simp [GSTV2.affineCarry, hx, gstUChargeExact]
  | succ K ih =>
      rw [Finset.sum_range_succ, ih]
      have hnext :
          gstStepCarryExact
              (GSTV2.affineCarry D X K) (GSTV2.digit X K) =
            GSTV2.affineCarry D X (K+1) := by
        simpa [gstStepCarryExact, GSTV2.cellNextCarry, GSTV2.cellMass] using
          (GSTV2.affineCarry_forward D X K).symm
      have hprefix :
          X % 3^(K+1) =
            X % 3^K + 3^K * GSTV2.digit X K := by
        calc
          X % 3^(K+1) =
              Finset.sum (Finset.range (K+1))
                (fun j => 3^j * GSTV2.digit X j) := by
                  symm
                  exact GSTV2.digit_prefix_value X (K+1)
          _ = Finset.sum (Finset.range K)
                (fun j => 3^j * GSTV2.digit X j) +
              3^K * GSTV2.digit X K := by
                rw [Finset.sum_range_succ]
          _ = X % 3^K + 3^K * GSTV2.digit X K := by
                rw [GSTV2.digit_prefix_value]
      unfold gstUJumpExact jumpWith
      rw [hnext, hprefix, Nat.pow_succ]
      push_cast
      ring

/-- A seed-zero Happy gate makes the entire base-three weighted U prefix
strictly negative. -/
theorem seeded_zero_weighted_u_prefix_negative_of_happy
    (X q : Nat)
    (hHappy : GSTV2.Happy
      (GSTV2.naturalCarry X q) (GSTV2.digit X q)) :
    Finset.sum (Finset.range (q+1)) (fun j =>
      (((3^j : Nat) : Int)) *
        gstUJumpExact
          (GSTV2.affineCarry 0 X j)
          (GSTV2.digit X j)) < 0 := by
  rw [seeded_weighted_u_jump_exact 0 X (q+1)]
  rcases hHappy with ⟨hdigit, hcarry | hcarry⟩
  · have hnextNat := GSTV2.naturalCarry_forward X q
    rw [hcarry, hdigit] at hnextNat
    norm_num [GSTV2.cellNextCarry, GSTV2.cellMass] at hnextNat
    have hnext : GSTV2.affineCarry 0 X (q+1) = 2 := by
      simpa [GSTV2.affineCarry, GSTV2.naturalCarry] using hnextNat
    have hprefix :
        X % 3^(q+1) = X % 3^q + 3^q * 2 := by
      calc
        X % 3^(q+1) =
            Finset.sum (Finset.range (q+1))
              (fun j => 3^j * GSTV2.digit X j) := by
                symm
                exact GSTV2.digit_prefix_value X (q+1)
        _ = Finset.sum (Finset.range q)
              (fun j => 3^j * GSTV2.digit X j) +
            3^q * GSTV2.digit X q := by
              rw [Finset.sum_range_succ]
        _ = X % 3^q + 3^q * 2 := by
              rw [GSTV2.digit_prefix_value, hdigit]
    rw [hnext, hprefix, Nat.pow_succ]
    norm_num [gstUChargeExact]
    have hr : (0 : Int) ≤ (X : Int) % (3 : Int)^q := by
      exact Int.emod_nonneg _ (by positivity)
    have ha : (0 : Int) < (3 : Int)^q := by positivity
    norm_num only [Nat.cast_mul, Nat.cast_ofNat, Nat.cast_pow]
    nlinarith
  · have hnextNat := GSTV2.naturalCarry_forward X q
    rw [hcarry, hdigit] at hnextNat
    norm_num [GSTV2.cellNextCarry, GSTV2.cellMass] at hnextNat
    have hnext : GSTV2.affineCarry 0 X (q+1) = 3 := by
      simpa [GSTV2.affineCarry, GSTV2.naturalCarry] using hnextNat
    have hprefix :
        X % 3^(q+1) = X % 3^q + 3^q * 2 := by
      calc
        X % 3^(q+1) =
            Finset.sum (Finset.range (q+1))
              (fun j => 3^j * GSTV2.digit X j) := by
                symm
                exact GSTV2.digit_prefix_value X (q+1)
        _ = Finset.sum (Finset.range q)
              (fun j => 3^j * GSTV2.digit X j) +
            3^q * GSTV2.digit X q := by
              rw [Finset.sum_range_succ]
        _ = X % 3^q + 3^q * 2 := by
              rw [GSTV2.digit_prefix_value, hdigit]
    have hden : 0 < 3^q := by positivity
    have hdiv : (4 * (X % 3^q)) / 3^q = 3 := by
      simpa [GSTV2.naturalCarry] using hcarry
    have hquot : 3 ≤ (4 * (X % 3^q)) / 3^q := by omega
    have hlower : 3 * 3^q ≤ 4 * (X % 3^q) :=
      (Nat.le_div_iff_mul_le hden).mp hquot
    have hlowerInt :
        (3 : Int) * (((3^q : Nat) : Int)) ≤
          4 * ((X % 3^q : Nat) : Int) := by
      exact_mod_cast hlower
    rw [hnext, hprefix, Nat.pow_succ]
    norm_num [gstUChargeExact]
    have ha : (0 : Int) < (((3^q : Nat) : Int)) := by positivity
    norm_num only [Nat.cast_mul, Nat.cast_ofNat, Nat.cast_pow]
    nlinarith

/-- A seed-one affine carry is always one of the four physical GST carries. -/
theorem affineCarry_one_lt_four
    (X j : Nat) :
    GSTV2.affineCarry 1 X j < 4 := by
  have hpow : 0 < 3^j := by positivity
  have hrem : X % 3^j < 3^j := Nat.mod_lt _ hpow
  unfold GSTV2.affineCarry
  exact (Nat.div_lt_iff_lt_mul hpow).2 (by omega)

/-- An all-bad seed-one parent has a nonnegative exact weighted U prefix. -/
theorem seeded_one_bad_weighted_u_prefix_nonnegative
    (X K : Nat)
    (hBad : GSTV2.SeededBadTrace 1 X) :
    0 ≤ Finset.sum (Finset.range K) (fun j =>
      (((3^j : Nat) : Int)) *
        gstUJumpExact
          (GSTV2.affineCarry 1 X j)
          (GSTV2.digit X j)) := by
  apply Finset.sum_nonneg
  intro j hj
  have hCarry : GSTV2.affineCarry 1 X j < 4 :=
    affineCarry_one_lt_four X j
  have hDigit : GSTV2.digit X j < 3 := by
    unfold GSTV2.digit
    exact Nat.mod_lt _ (by decide)
  have hCellBad : ¬ HappyCell
      (GSTV2.affineCarry 1 X j)
      (GSTV2.digit X j) := by
    simpa [GSTV2.Happy, HappyCell] using hBad j
  have hJump : 0 ≤ gstUJumpExact
      (GSTV2.affineCarry 1 X j)
      (GSTV2.digit X j) :=
    gst_u_jump_nonnegative_of_not_happy _ _ hCarry hDigit hCellBad
  exact mul_nonneg (by positivity) hJump

/-- Exact signed coupled-prefix certificate.  A seed-zero child Happy gate and
an all-bad seed-one parent force the full base-three weighted parent-minus-child
U gap to be strictly positive through that gate. -/
theorem seeded_coupled_weighted_u_gap_positive
    (A child parent q : Nat)
    (hA : 0 < A)
    (hChild : GSTV2.Happy
      (GSTV2.naturalCarry child q) (GSTV2.digit child q))
    (hParentBad : GSTV2.SeededBadTrace 1 parent) :
    0 < Finset.sum (Finset.range (q+1)) (fun j =>
      (((3^j : Nat) : Int)) *
        (gstUJumpExact
            (GSTV2.affineCarry 1 parent j)
            (GSTV2.digit parent j) -
          (A : Int) *
            gstUJumpExact
              (GSTV2.affineCarry 0 child j)
              (GSTV2.digit child j))) := by
  have hParent :=
    seeded_one_bad_weighted_u_prefix_nonnegative parent (q+1) hParentBad
  have hChildSum :=
    seeded_zero_weighted_u_prefix_negative_of_happy child q hChild
  have hSplit :
      Finset.sum (Finset.range (q+1)) (fun j =>
        (((3^j : Nat) : Int)) *
          (gstUJumpExact
              (GSTV2.affineCarry 1 parent j)
              (GSTV2.digit parent j) -
            (A : Int) *
              gstUJumpExact
                (GSTV2.affineCarry 0 child j)
                (GSTV2.digit child j))) =
        Finset.sum (Finset.range (q+1)) (fun j =>
          (((3^j : Nat) : Int)) *
            gstUJumpExact
              (GSTV2.affineCarry 1 parent j)
              (GSTV2.digit parent j)) -
        (A : Int) *
          Finset.sum (Finset.range (q+1)) (fun j =>
            (((3^j : Nat) : Int)) *
              gstUJumpExact
                (GSTV2.affineCarry 0 child j)
                (GSTV2.digit child j)) := by
    rw [Finset.mul_sum, ← Finset.sum_sub_distrib]
    apply Finset.sum_congr rfl
    intro j hj
    ring
  rw [hSplit]
  have hAInt : (0 : Int) < (A : Int) := by exact_mod_cast hA
  nlinarith

/-- If every carry in a finite horizontal observation vanishes, the retained
reverse-base-four carry word is exactly zero. -/
theorem carryWord_eq_zero_of_window_neutral
    (E p start : Nat) : ∀ N : Nat,
    (∀ j, j < N → (graph E (start+j) p).seven.carry = 0) →
      carryWord E p start N = 0 := by
  intro N h
  induction N with
  | zero => simp [carryWord]
  | succ N ih =>
      rw [carryWord]
      have hprev : ∀ j, j < N → (graph E (start+j) p).seven.carry = 0 := by
        intro j hj
        exact h j (by omega)
      rw [ih hprev]
      have hlast := h N (by omega)
      simpa using hlast

/-- A finite horizontal U packet on a completely neutral row is not zero. -/
theorem graph_u_potential_vacuum_baseline_of_window_neutral
    (E start N p : Nat)
    (hLeft : (graph E start p).seven.carry = 0)
    (hRight : (graph E (start+N) p).seven.carry = 0)
    (hWindow : ∀ j, j < N →
      (graph E (start+j) p).seven.carry = 0) :
    graphUPotential E start N p =
      5 - (((4^N : Nat) : Int)) * 5 := by
  have hWord : carryWord E p start N = 0 :=
    carryWord_eq_zero_of_window_neutral E p start N hWindow
  unfold graphUPotential
  rw [hLeft, hRight, hWord]
  norm_num [gstUChargeExact]

/-- Direct arithmetic neutralization of a unit-sheet cell above its finite
x4 energy. -/
theorem unit_graph_cell_neutral_of_pow_lt
    (t p : Nat) (hpow : 4^(t+1) < 3^p) :
    (graph 1 t p).seven.carry = 0 ∧
      (graph 1 t p).seven.digit = 0 := by
  have ht : 4^t < 3^p := by
    have hle : 4^t ≤ 4^(t+1) := by
      rw [Nat.pow_succ]
      omega
    omega
  constructor
  · simp only [graph, cell, GSTCanonicalSevenAxisBridge.vertex, carry4]
    rw [Nat.mul_one, Nat.mod_eq_of_lt ht]
    have hshape : 4 * 4^t = 4^(t+1) := by
      rw [Nat.pow_succ]
      ring
    rw [hshape, Nat.div_eq_of_lt hpow]
  · simp only [graph, cell, GSTCanonicalSevenAxisBridge.vertex, digit3]
    rw [Nat.mul_one, Nat.div_eq_of_lt ht]

#check physical_happy_forces_negative_u_jump
#check physical_bad_forces_nonnegative_u_jump
#check canonical_width_u_derivative_positive
#check seeded_weighted_u_jump_exact
#check seeded_zero_weighted_u_prefix_negative_of_happy
#check affineCarry_one_lt_four
#check seeded_one_bad_weighted_u_prefix_nonnegative
#check seeded_coupled_weighted_u_gap_positive
#check carryWord_eq_zero_of_window_neutral
#check graph_u_potential_vacuum_baseline_of_window_neutral
#check unit_graph_cell_neutral_of_pow_lt
#print axioms physical_happy_forces_negative_u_jump
#print axioms physical_bad_forces_nonnegative_u_jump
#print axioms canonical_width_u_derivative_positive
#print axioms seeded_weighted_u_jump_exact
#print axioms seeded_zero_weighted_u_prefix_negative_of_happy
#print axioms affineCarry_one_lt_four
#print axioms seeded_one_bad_weighted_u_prefix_nonnegative
#print axioms seeded_coupled_weighted_u_gap_positive
#print axioms carryWord_eq_zero_of_window_neutral
#print axioms graph_u_potential_vacuum_baseline_of_window_neutral
#print axioms unit_graph_cell_neutral_of_pow_lt

end GSTGraphV2CanonicalTerminalExtinctionProbe
