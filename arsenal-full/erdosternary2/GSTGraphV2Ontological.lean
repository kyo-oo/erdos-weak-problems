import GSTGraphV2InfiniteControl

set_option maxRecDepth 1000000
set_option maxHeartbeats 10000000

namespace GSTGraphV2Ontological

open GST2DMixedEmergence
open GSTU2DEventTransport
open GSTGraphV2InfiniteControl

/-!
# GST Graph V2 — ontological current

This module is a finite-state certificate discovered from the exact twelve
physical x4/base3 cells.  It deliberately uses a reverse-base-seven horizontal
current: seven is the smallest tested pure-divergence scale for which the
resulting physical table simultaneously separates Happy from bad cells and
has enough no-erasure margin for the base-three highest-row domination.

No terminal-height, support-horizon, master theorem, or monolith dependency is
used here.
-/

/-- Horizontal information potential for the pure ontological current. -/
def ontDigitPotential (d : Nat) : Int :=
  if d = 0 then 9 else if d = 1 then -35 else -91

/-- Vertical carry potential for the pure ontological current. -/
def ontCarryPotential (C : Nat) : Int :=
  if C = 0 then 0 else if C = 1 then 77 else if C = 2 then 154 else 252

/-- Pure x7/base3 divergence.  Unlike the older crossing densities this has no
interior SURVIVE source term. -/
def ontDensity (C d : Nat) : Int :=
  ontDigitPotential (outDigit C d) - 7 * ontDigitPotential d +
    ontCarryPotential C - 3 * ontCarryPotential (nextCarry C d)

/-- Complete twelve-state certificate.  Exactly the two Happy cells are
positive; every bad physical cell is nonpositive; the global floor is -54. -/
theorem ontDensity_physical_table :
    ontDensity 0 0 = -54 ∧ ontDensity 0 1 = -21 ∧ ontDensity 0 2 = 84 ∧
    ontDensity 1 0 = -21 ∧ ontDensity 1 1 = 0 ∧ ontDensity 1 2 = -33 ∧
    ontDensity 2 0 = 0 ∧ ontDensity 2 1 = -54 ∧ ontDensity 2 2 = 0 ∧
    ontDensity 3 0 = -33 ∧ ontDensity 3 1 = 0 ∧ ontDensity 3 2 = 42 := by
  decide

/-- A physical Happy cell injects at least 42 units of ontological current. -/
theorem ontDensity_ge_42_of_happy
    (C d : Nat) (h : HappyCell C d) :
    (42 : Int) ≤ ontDensity C d := by
  rcases h with ⟨hd, hC⟩
  subst d
  rcases hC with h0 | h3
  · subst C
    norm_num [ontDensity, ontDigitPotential, ontCarryPotential,
      outDigit, nextCarry]
  · subst C
    norm_num [ontDensity, ontDigitPotential, ontCarryPotential,
      outDigit, nextCarry]

/-- Uniform floor of the ontological density on physical cells. -/
theorem ontDensity_ge_neg54
    (C d : Nat) (hC : C < 4) (hd : d < 3) :
    (-54 : Int) ≤ ontDensity C d := by
  have hCc : C = 0 ∨ C = 1 ∨ C = 2 ∨ C = 3 := by omega
  have hdc : d = 0 ∨ d = 1 ∨ d = 2 := by omega
  rcases hCc with rfl | rfl | rfl | rfl <;>
    rcases hdc with rfl | rfl | rfl <;>
    norm_num [ontDensity, ontDigitPotential, ontCarryPotential,
      outDigit, nextCarry]

/-- Every non-Happy physical cell has nonpositive ontological density. -/
theorem ontDensity_nonpositive_of_not_happy
    (C d : Nat) (hC : C < 4) (hd : d < 3)
    (hbad : ¬ HappyCell C d) :
    ontDensity C d ≤ 0 := by
  have hCc : C = 0 ∨ C = 1 ∨ C = 2 ∨ C = 3 := by omega
  have hdc : d = 0 ∨ d = 1 ∨ d = 2 := by omega
  rcases hCc with rfl | rfl | rfl | rfl <;>
    rcases hdc with rfl | rfl | rfl <;>
    simp [HappyCell] at hbad <;>
    norm_num [ontDensity, ontDigitPotential, ontCarryPotential,
      outDigit, nextCarry]

/-- Happy is exactly the positive sector of the pure ontological current. -/
theorem happy_iff_ontDensity_positive
    (C d : Nat) (hC : C < 4) (hd : d < 3) :
    HappyCell C d ↔ 0 < ontDensity C d := by
  constructor
  · intro h
    have h42 := ontDensity_ge_42_of_happy C d h
    omega
  · intro hpos
    by_contra hbad
    have hnonpos := ontDensity_nonpositive_of_not_happy C d hC hd hbad
    omega

/-- Reverse-base-seven accumulation of one horizontal graph row. -/
def reverseOntCode (C d : Nat → Nat) : Nat → Int
  | 0 => 0
  | N+1 => 7 * reverseOntCode C d N + ontDensity (C N) (d N)

/-- Matching reverse-base-seven accumulation of the vertical carry potential. -/
def reverseOntCarryCode (C : Nat → Nat) : Nat → Int
  | 0 => 0
  | N+1 => 7 * reverseOntCarryCode C N + ontCarryPotential (C N)

/-- Exact horizontal telescope of the pure ontological current. -/
theorem reverseOntCode_exact
    (C Cnext d : Nat → Nat) : ∀ N : Nat,
    (∀ t, t < N → outDigit (C t) (d t) = d (t+1)) →
    (∀ t, t < N → nextCarry (C t) (d t) = Cnext t) →
    reverseOntCode C d N =
      ontDigitPotential (d N) -
        (((7^N : Nat) : Int)) * ontDigitPotential (d 0) +
      reverseOntCarryCode C N - 3 * reverseOntCarryCode Cnext N := by
  intro N
  induction N with
  | zero =>
      intro hout hnext
      simp [reverseOntCode, reverseOntCarryCode]
  | succ N ih =>
      intro hout hnext
      have ih' := ih
        (fun t ht => hout t (by omega))
        (fun t ht => hnext t (by omega))
      have houtN := hout N (by omega)
      have hnextN := hnext N (by omega)
      rw [reverseOntCode, reverseOntCarryCode, reverseOntCarryCode,
        ih', ontDensity, houtN, hnextN, Nat.pow_succ]
      push_cast
      ring

/-- Global floor for an arbitrary physical horizontal row. -/
theorem reverseOntCode_ge_global_floor
    (C d : Nat → Nat) : ∀ N : Nat,
    (∀ t, t < N → C t < 4) →
    (∀ t, t < N → d t < 3) →
    9 - 9 * (((7^N : Nat) : Int)) ≤ reverseOntCode C d N := by
  intro N
  induction N with
  | zero =>
      intro hC hd
      simp [reverseOntCode]
  | succ N ih =>
      intro hC hd
      have ih' := ih
        (fun t ht => hC t (by omega))
        (fun t ht => hd t (by omega))
      have hlast := ontDensity_ge_neg54 (C N) (d N)
        (hC N (by omega)) (hd N (by omega))
      have hpow :
          (((7^(N+1) : Nat) : Int)) =
            7 * (((7^N : Nat) : Int)) := by
        rw [Nat.pow_succ]
        push_cast
        ring
      rw [reverseOntCode, hpow]
      omega

/-- **Pure horizontal no-erasure.**  A leading Happy cell starts with at least
42.  Every later physical cell costs at most 54 while the current is multiplied
by seven.  The scaled closed form avoids predecessor arithmetic:

  33*7^N + 63 ≤ 7*code_N.
-/
theorem reverseOntCode_ge_scaled_of_leading_happy
    (C d : Nat → Nat)
    (hfirst : HappyCell (C 0) (d 0)) : ∀ N : Nat,
    1 ≤ N →
    (∀ t, t < N → C t < 4) →
    (∀ t, t < N → d t < 3) →
    33 * (((7^N : Nat) : Int)) + 63 ≤ 7 * reverseOntCode C d N := by
  intro N
  induction N with
  | zero =>
      intro hN
      omega
  | succ N ih =>
      intro hN hC hd
      by_cases hN0 : N = 0
      · subst N
        have hlead := ontDensity_ge_42_of_happy (C 0) (d 0) hfirst
        simp only [reverseOntCode]
        norm_num
        omega
      · have hNpos : 1 ≤ N := Nat.one_le_iff_ne_zero.mpr hN0
        have ih' := ih hNpos
          (fun t ht => hC t (by omega))
          (fun t ht => hd t (by omega))
        have ih7 := mul_le_mul_of_nonneg_left ih' (by norm_num : (0 : Int) ≤ 7)
        have hlast := ontDensity_ge_neg54 (C N) (d N)
          (hC N (by omega)) (hd N (by omega))
        have hlast7 := mul_le_mul_of_nonneg_left hlast (by norm_num : (0 : Int) ≤ 7)
        have hpow :
            (((7^(N+1) : Nat) : Int)) =
              7 * (((7^N : Nat) : Int)) := by
          rw [Nat.pow_succ]
          push_cast
          ring
        rw [reverseOntCode, hpow]
        omega

/-- Base-three weighted prefix of horizontal ontological rows. -/
def weightedOntPrefix
    (C d : Nat → Nat → Nat) (N : Nat) : Nat → Int
  | 0 => 0
  | K+1 =>
      weightedOntPrefix C d N K +
        (((3^K : Nat) : Int)) *
          reverseOntCode (fun t => C t K) (fun t => d t K) N

/-- Exact accumulated worst-case floor for all rows below a given height. -/
theorem weightedOntPrefix_ge_global_floor
    (C d : Nat → Nat → Nat) (N : Nat) : ∀ K : Nat,
    (∀ t p, t < N → p < K → C t p < 4) →
    (∀ t p, t < N → p < K → d t p < 3) →
    (9 - 9 * (((7^N : Nat) : Int))) *
        ((((3^K : Nat) : Int)) - 1) ≤
      2 * weightedOntPrefix C d N K := by
  intro K
  induction K with
  | zero =>
      intro hC hd
      simp [weightedOntPrefix]
  | succ K ih =>
      intro hC hd
      have ih' := ih
        (fun t p ht hp => hC t p ht (by omega))
        (fun t p ht hp => hd t p ht (by omega))
      have hrow := reverseOntCode_ge_global_floor
        (fun t => C t K) (fun t => d t K) N
        (fun t ht => hC t K ht (by omega))
        (fun t ht => hd t K ht (by omega))
      have hw : (0 : Int) ≤ 2 * (((3^K : Nat) : Int)) := by positivity
      have hrowW := mul_le_mul_of_nonneg_left hrow hw
      have h3pow :
          (((3^(K+1) : Nat) : Int)) =
            3 * (((3^K : Nat) : Int)) := by
        rw [Nat.pow_succ]
        push_cast
        ring
      rw [weightedOntPrefix, h3pow]
      calc
        (9 - 9 * (((7^N : Nat) : Int))) *
            (3 * (((3^K : Nat) : Int)) - 1) =
          (9 - 9 * (((7^N : Nat) : Int))) *
              ((((3^K : Nat) : Int)) - 1) +
            (2 * (((3^K : Nat) : Int))) *
              (9 - 9 * (((7^N : Nat) : Int))) := by ring
        _ ≤ 2 * weightedOntPrefix C d N K +
            (2 * (((3^K : Nat) : Int))) *
              reverseOntCode (fun t => C t K) (fun t => d t K) N :=
          add_le_add ih' hrowW
        _ = 2 *
            (weightedOntPrefix C d N K +
              (((3^K : Nat) : Int)) *
                reverseOntCode (fun t => C t K) (fun t => d t K) N) := by ring

/-- **Ontological highest-Happy-row domination.**  The base-seven pure current
has enough margin that a leading Happy row beats the total worst-case mass of
all lower rows under the literal base-three vertical weighting. -/
theorem weightedOntPrefix_positive_of_top_leading_happy
    (C d : Nat → Nat → Nat) (N q : Nat)
    (hN : 1 ≤ N)
    (hC : ∀ t p, t < N → p ≤ q → C t p < 4)
    (hd : ∀ t p, t < N → p ≤ q → d t p < 3)
    (hHappy : HappyCell (C 0 q) (d 0 q)) :
    0 < weightedOntPrefix C d N (q+1) := by
  let A : Int := (((7^N : Nat) : Int))
  let w : Int := (((3^q : Nat) : Int))
  let P : Int := weightedOntPrefix C d N q
  let R : Int := reverseOntCode (fun t => C t q) (fun t => d t q) N

  have hlower0 := weightedOntPrefix_ge_global_floor C d N q
    (fun t p ht hp => hC t p ht (by omega))
    (fun t p ht hp => hd t p ht (by omega))
  have hlower : (9 - 9*A) * (w - 1) ≤ 2*P := by
    simpa [A, w, P] using hlower0

  have htop0 := reverseOntCode_ge_scaled_of_leading_happy
    (fun t => C t q) (fun t => d t q) hHappy N hN
    (fun t ht => hC t q ht (by omega))
    (fun t ht => hd t q ht (by omega))
  have htop : 33*A + 63 ≤ 7*R := by
    simpa [A, R] using htop0

  have hlower7 := mul_le_mul_of_nonneg_left hlower (by norm_num : (0:Int) ≤ 7)
  have hw0 : (0 : Int) ≤ 2*w := by
    dsimp [w]
    positivity
  have htopW := mul_le_mul_of_nonneg_left htop hw0

  have hApos : 0 < A := by
    dsimp [A]
    positivity
  have hwpos : 0 < w := by
    dsimp [w]
    positivity
  have hAwpos : 0 < A*w := mul_pos hApos hwpos

  have hpositive :
      0 < 7 * ((9 - 9*A) * (w - 1)) +
        (2*w) * (33*A + 63) := by
    have hshape :
        7 * ((9 - 9*A) * (w - 1)) +
            (2*w) * (33*A + 63) =
          3*A*w + 63*A + 189*w - 63 := by ring
    rw [hshape]
    nlinarith [hApos, hwpos, hAwpos]

  have hbound :
      7 * ((9 - 9*A) * (w - 1)) +
          (2*w) * (33*A + 63) ≤
        14 * (P + w*R) := by
    calc
      7 * ((9 - 9*A) * (w - 1)) +
          (2*w) * (33*A + 63) ≤
        7 * (2*P) + (2*w) * (7*R) := add_le_add hlower7 htopW
      _ = 14 * (P + w*R) := by ring

  have hsumpos : 0 < P + w*R := by omega
  simpa [weightedOntPrefix, P, R, w] using hsumpos

/-- Base-three telescope for the vertical ontological carry derivative. -/
theorem ternaryWeightedOntDiff_telescope (g : Nat → Int) (K : Nat) :
    Finset.sum (Finset.range K) (fun p =>
      (((3^p : Nat) : Int)) * (g p - 3 * g (p+1))) =
      g 0 - (((3^K : Nat) : Int)) * g K := by
  induction K with
  | zero => simp
  | succ K ih =>
      rw [Finset.sum_range_succ, ih, Nat.pow_succ]
      push_cast
      ring

/-- Exact pure-divergence rectangle identity.  There is no interior source
term: only the two horizontal digit boundaries and the two vertical carry
boundaries remain. -/
theorem reverseOntRectangle_exact
    (C d : Nat → Nat → Nat) (N K : Nat)
    (hcell : ∀ t p, t < N → p < K →
      C t p < 4 ∧ d t p < 3 ∧
      outDigit (C t p) (d t p) = d (t+1) p ∧
      nextCarry (C t p) (d t p) = C t (p+1)) :
    Finset.sum (Finset.range K) (fun p =>
      (((3^p : Nat) : Int)) *
        reverseOntCode (fun t => C t p) (fun t => d t p) N) =
      Finset.sum (Finset.range K) (fun p =>
        (((3^p : Nat) : Int)) *
          (ontDigitPotential (d N p) -
            (((7^N : Nat) : Int)) * ontDigitPotential (d 0 p))) +
      reverseOntCarryCode (fun t => C t 0) N -
        (((3^K : Nat) : Int)) *
          reverseOntCarryCode (fun t => C t K) N := by
  let g : Nat → Int := fun p => reverseOntCarryCode (fun t => C t p) N
  have htel := ternaryWeightedOntDiff_telescope g K
  calc
    Finset.sum (Finset.range K) (fun p =>
        (((3^p : Nat) : Int)) *
          reverseOntCode (fun t => C t p) (fun t => d t p) N) =
      Finset.sum (Finset.range K) (fun p =>
        (((3^p : Nat) : Int)) *
          ((ontDigitPotential (d N p) -
              (((7^N : Nat) : Int)) * ontDigitPotential (d 0 p)) +
            (g p - 3 * g (p+1)))) := by
      apply Finset.sum_congr rfl
      intro p hp
      have hpK : p < K := Finset.mem_range.mp hp
      have hrow := reverseOntCode_exact
        (fun t => C t p) (fun t => C t (p+1)) (fun t => d t p) N
        (fun t ht => (hcell t p ht hpK).2.2.1)
        (fun t ht => (hcell t p ht hpK).2.2.2)
      dsimp [g]
      rw [hrow]
      ring
    _ =
      Finset.sum (Finset.range K) (fun p =>
        (((3^p : Nat) : Int)) *
          (ontDigitPotential (d N p) -
            (((7^N : Nat) : Int)) * ontDigitPotential (d 0 p))) +
      Finset.sum (Finset.range K) (fun p =>
        (((3^p : Nat) : Int)) * (g p - 3 * g (p+1))) := by
      rw [← Finset.sum_add_distrib]
      apply Finset.sum_congr rfl
      intro p hp
      ring
    _ =
      Finset.sum (Finset.range K) (fun p =>
        (((3^p : Nat) : Int)) *
          (ontDigitPotential (d N p) -
            (((7^N : Nat) : Int)) * ontDigitPotential (d 0 p))) +
      g 0 - (((3^K : Nat) : Int)) * g K := by
        rw [htel]
        ring
    _ = _ := by rfl

/-- Shifted production-window specialization on the actual infinite Graph V2. -/
def graphOntWindow (E N b K : Nat) : Int :=
  weightedOntPrefix
    (fun t j => (graph E t (b+j)).seven.carry)
    (fun t j => (graph E t (b+j)).seven.digit) N K

/-- A Happy source on the left edge gives strictly positive ontological current
through every nonzero-width Graph-V2 block. -/
theorem graphOntWindow_positive_of_happy
    (E N b q : Nat) (hN : 1 ≤ N)
    (hHappy : HappyCell
      (graph E 0 (b+q)).seven.carry
      (graph E 0 (b+q)).seven.digit) :
    0 < graphOntWindow E N b (q+1) := by
  unfold graphOntWindow
  apply weightedOntPrefix_positive_of_top_leading_happy
  · exact hN
  · intro t p ht hp
    exact graph_carry_lt_four E t (b+p)
  · intro t p ht hp
    exact graph_digit_lt_three E t (b+p)
  · simpa [Nat.add_assoc] using hHappy

/-- Exact pure rectangle identity on a shifted observation window of Graph V2. -/
theorem graphOntWindow_exact
    (E N b K : Nat) :
    graphOntWindow E N b K =
      Finset.sum (Finset.range K) (fun j =>
        (((3^j : Nat) : Int)) *
          (ontDigitPotential (graph E N (b+j)).seven.digit -
            (((7^N : Nat) : Int)) *
              ontDigitPotential (graph E 0 (b+j)).seven.digit)) +
      reverseOntCarryCode (fun t => (graph E t b).seven.carry) N -
        (((3^K : Nat) : Int)) *
          reverseOntCarryCode (fun t => (graph E t (b+K)).seven.carry) N := by
  unfold graphOntWindow
  apply reverseOntRectangle_exact
  intro t j ht hj
  exact ⟨graph_carry_lt_four E t (b+j),
    graph_digit_lt_three E t (b+j),
    (graph_cell_exact E t (b+j)).1,
    by simpa [Nat.add_assoc] using (graph_cell_exact E t (b+j)).2⟩

#check ontDensity_physical_table
#check happy_iff_ontDensity_positive
#check reverseOntCode_ge_scaled_of_leading_happy
#check weightedOntPrefix_positive_of_top_leading_happy
#check reverseOntRectangle_exact
#check graphOntWindow_positive_of_happy
#check graphOntWindow_exact
#print axioms weightedOntPrefix_positive_of_top_leading_happy
#print axioms graphOntWindow_exact

end GSTGraphV2Ontological
