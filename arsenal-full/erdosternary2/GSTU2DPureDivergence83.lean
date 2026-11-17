import GSTGraphV2InfiniteControl

set_option maxRecDepth 1000000
set_option maxHeartbeats 10000000

namespace GSTU2DPureDivergence83

open GST2DMixedEmergence
open GSTU2DEventTransport
open GSTGraphV2InfiniteControl

/-! Pure 8×3 divergence on the existing infinite GST graph. -/

def digitPotential83 (d : Nat) : Int :=
  if d = 0 then 15 else if d = 1 then -48 else -132

def carryPotential83 (C : Nat) : Int :=
  if C = 0 then 0 else if C = 1 then 140 else if C = 2 then 252 else 420

def density83 (C d : Nat) : Int :=
  digitPotential83 (outDigit C d) - 8 * digitPotential83 d +
    carryPotential83 C - 3 * carryPotential83 (nextCarry C d)

theorem density83_physical_table :
    density83 0 0 = -105 ∧ density83 0 1 = -84 ∧ density83 0 2 = 168 ∧
    density83 1 0 = -28 ∧ density83 1 1 = -28 ∧ density83 1 2 = -49 ∧
    density83 2 0 = 0 ∧ density83 2 1 = -105 ∧ density83 2 2 = 0 ∧
    density83 3 0 = -105 ∧ density83 3 1 = 0 ∧ density83 3 2 = 84 := by
  decide

theorem happy_iff_density83_positive
    (C d : Nat) (hC : C < 4) (hd : d < 3) :
    HappyCell C d ↔ 0 < density83 C d := by
  have hCc : C = 0 ∨ C = 1 ∨ C = 2 ∨ C = 3 := by omega
  have hdc : d = 0 ∨ d = 1 ∨ d = 2 := by omega
  rcases hCc with h0 | h1 | h2 | h3 <;>
    rcases hdc with d0 | d1 | d2 <;>
    subst C <;> subst d <;>
    norm_num [HappyCell, density83, digitPotential83, carryPotential83,
      outDigit, nextCarry]

theorem density83_ge_neg105
    (C d : Nat) (hC : C < 4) (hd : d < 3) :
    (-105 : Int) ≤ density83 C d := by
  have hCc : C = 0 ∨ C = 1 ∨ C = 2 ∨ C = 3 := by omega
  have hdc : d = 0 ∨ d = 1 ∨ d = 2 := by omega
  rcases hCc with h0 | h1 | h2 | h3 <;>
    rcases hdc with d0 | d1 | d2 <;>
    subst C <;> subst d <;>
    norm_num [density83, digitPotential83, carryPotential83, outDigit, nextCarry]

theorem density83_nonpositive_of_not_happy
    (C d : Nat) (hC : C < 4) (hd : d < 3)
    (hbad : ¬ HappyCell C d) :
    density83 C d ≤ 0 := by
  by_contra h
  have hp : 0 < density83 C d := by omega
  exact hbad ((happy_iff_density83_positive C d hC hd).2 hp)

def reverseDensity83 (C d : Nat → Nat) : Nat → Int
  | 0 => 0
  | N+1 => 8 * reverseDensity83 C d N + density83 (C N) (d N)

def reverseCarry83 (C : Nat → Nat) : Nat → Int
  | 0 => 0
  | N+1 => 8 * reverseCarry83 C N + carryPotential83 (C N)

theorem reverseDensity83_ge_floor
    (C d : Nat → Nat) : ∀ N : Nat,
      (∀ t, t < N → C t < 4) →
      (∀ t, t < N → d t < 3) →
      (-15 : Int) * ((((8^N : Nat) : Int)) - 1) ≤ reverseDensity83 C d N := by
  intro N
  induction N with
  | zero =>
      intro hC hd
      simp [reverseDensity83]
  | succ N ih =>
      intro hC hd
      have ih' := ih
        (fun t ht => hC t (by omega))
        (fun t ht => hd t (by omega))
      have hlocal := density83_ge_neg105 (C N) (d N)
        (hC N (by omega)) (hd N (by omega))
      have hpow :
          (((8^(N+1) : Nat) : Int)) = 8 * (((8^N : Nat) : Int)) := by
        rw [Nat.pow_succ]
        push_cast
        ring
      rw [reverseDensity83, hpow]
      nlinarith

theorem reverseDensity83_ge_of_leading_happy
    (C d : Nat → Nat)
    (hHappy : HappyCell (C 0) (d 0)) :
    ∀ N : Nat,
      1 ≤ N →
      (∀ t, t < N → C t < 4) →
      (∀ t, t < N → d t < 3) →
      69 * (((8^(N-1) : Nat) : Int)) + 15 ≤ reverseDensity83 C d N := by
  intro N
  induction N with
  | zero =>
      intro hN
      omega
  | succ N ih =>
      intro hN hC hd
      by_cases hN0 : N = 0
      · subst N
        have htab : 84 ≤ density83 (C 0) (d 0) := by
          have hd2 : d 0 = 2 := hHappy.1
          rcases hHappy.2 with h0 | h3
          · rw [h0, hd2]
            norm_num [density83, digitPotential83, carryPotential83,
              outDigit, nextCarry]
          · rw [h3, hd2]
            norm_num [density83, digitPotential83, carryPotential83,
              outDigit, nextCarry]
        rw [reverseDensity83]
        norm_num [reverseDensity83] at htab ⊢
        exact htab
      · have hNpos : 1 ≤ N := Nat.one_le_iff_ne_zero.mpr hN0
        have ih' := ih hNpos
          (fun t ht => hC t (by omega))
          (fun t ht => hd t (by omega))
        have hlocal := density83_ge_neg105 (C N) (d N)
          (hC N (by omega)) (hd N (by omega))
        have hNm1 : (N - 1) + 1 = N := by omega
        have hpowNat : 8^N = 8 * 8^(N-1) := by
          calc
            8^N = 8^((N-1)+1) :=
              congrArg (fun k : Nat => 8^k) hNm1.symm
            _ = 8^(N-1) * 8 := Nat.pow_succ 8 (N-1)
            _ = 8 * 8^(N-1) := by ac_rfl
        have hpow :
            (((8^N : Nat) : Int)) = 8 * (((8^(N-1) : Nat) : Int)) := by
          exact_mod_cast hpowNat
        rw [reverseDensity83]
        change 69 * (((8^N : Nat) : Int)) + 15 ≤
          8 * reverseDensity83 C d N + density83 (C N) (d N)
        rw [hpow]
        nlinarith

theorem reverseDensity83_exact
    (C Cnext d : Nat → Nat) : ∀ N : Nat,
    (∀ t, t < N → outDigit (C t) (d t) = d (t+1)) →
    (∀ t, t < N → nextCarry (C t) (d t) = Cnext t) →
    reverseDensity83 C d N =
      digitPotential83 (d N) -
        (((8^N : Nat) : Int)) * digitPotential83 (d 0) +
      reverseCarry83 C N - 3 * reverseCarry83 Cnext N := by
  intro N
  induction N with
  | zero =>
      intro hout hnext
      simp [reverseDensity83, reverseCarry83]
  | succ N ih =>
      intro hout hnext
      have ih' := ih
        (fun t ht => hout t (by omega))
        (fun t ht => hnext t (by omega))
      have ho := hout N (by omega)
      have hc := hnext N (by omega)
      rw [reverseDensity83, reverseCarry83, reverseCarry83,
        ih', density83, ho, hc, Nat.pow_succ]
      push_cast
      ring_nf

theorem ternaryWeightedDiff83 (g : Nat → Int) (K : Nat) :
    Finset.sum (Finset.range K) (fun p =>
      (((3^p : Nat) : Int)) * (g p - 3 * g (p+1))) =
      g 0 - (((3^K : Nat) : Int)) * g K := by
  induction K with
  | zero => simp
  | succ K ih =>
      rw [Finset.sum_range_succ, ih, Nat.pow_succ]
      push_cast
      ring

theorem density83_rectangle_exact
    (C d : Nat → Nat → Nat) (N K : Nat)
    (hcell : ∀ t p, t < N → p < K →
      C t p < 4 ∧ d t p < 3 ∧
      outDigit (C t p) (d t p) = d (t+1) p ∧
      nextCarry (C t p) (d t p) = C t (p+1)) :
    Finset.sum (Finset.range K) (fun p =>
      (((3^p : Nat) : Int)) *
        reverseDensity83 (fun t => C t p) (fun t => d t p) N) =
      Finset.sum (Finset.range K) (fun p =>
        (((3^p : Nat) : Int)) *
          (digitPotential83 (d N p) -
            (((8^N : Nat) : Int)) * digitPotential83 (d 0 p))) +
      reverseCarry83 (fun t => C t 0) N -
        (((3^K : Nat) : Int)) * reverseCarry83 (fun t => C t K) N := by
  let g : Nat → Int := fun p => reverseCarry83 (fun t => C t p) N
  have htel := ternaryWeightedDiff83 g K
  calc
    Finset.sum (Finset.range K) (fun p =>
      (((3^p : Nat) : Int)) *
        reverseDensity83 (fun t => C t p) (fun t => d t p) N) =
      Finset.sum (Finset.range K) (fun p =>
        (((3^p : Nat) : Int)) *
          ((digitPotential83 (d N p) -
              (((8^N : Nat) : Int)) * digitPotential83 (d 0 p)) +
            (g p - 3 * g (p+1)))) := by
      apply Finset.sum_congr rfl
      intro p hp
      have hpK : p < K := Finset.mem_range.mp hp
      have hr := reverseDensity83_exact
        (fun t => C t p) (fun t => C t (p+1)) (fun t => d t p) N
        (fun t ht => (hcell t p ht hpK).2.2.1)
        (fun t ht => (hcell t p ht hpK).2.2.2)
      rw [hr]
      dsimp [g]
      ring
    _ =
      Finset.sum (Finset.range K) (fun p =>
        (((3^p : Nat) : Int)) *
          (digitPotential83 (d N p) -
            (((8^N : Nat) : Int)) * digitPotential83 (d 0 p))) +
      Finset.sum (Finset.range K) (fun p =>
        (((3^p : Nat) : Int)) * (g p - 3 * g (p+1))) := by
      rw [← Finset.sum_add_distrib]
      apply Finset.sum_congr rfl
      intro p hp
      ring
    _ = _ := by
      rw [htel]
      dsimp [g]
      ring

def weightedRectanglePrefix83
    (C d : Nat → Nat → Nat) (N : Nat) : Nat → Int
  | 0 => 0
  | K+1 => weightedRectanglePrefix83 C d N K +
      (((3^K : Nat) : Int)) *
        reverseDensity83 (fun t => C t K) (fun t => d t K) N

theorem weightedRectanglePrefix83_ge_floor
    (C d : Nat → Nat → Nat) (N : Nat) : ∀ K : Nat,
    (∀ t p, t < N → p < K → C t p < 4) →
    (∀ t p, t < N → p < K → d t p < 3) →
    (-15 : Int) * ((((8^N : Nat) : Int)) - 1) *
        ((((3^K : Nat) : Int)) - 1) ≤
      2 * weightedRectanglePrefix83 C d N K := by
  intro K
  induction K with
  | zero =>
      intro hC hd
      simp [weightedRectanglePrefix83]
  | succ K ih =>
      intro hC hd
      have ih' := ih
        (fun t p ht hp => hC t p ht (by omega))
        (fun t p ht hp => hd t p ht (by omega))
      have hrow := reverseDensity83_ge_floor
        (fun t => C t K) (fun t => d t K) N
        (fun t ht => hC t K ht (by omega))
        (fun t ht => hd t K ht (by omega))
      have hw : (0 : Int) ≤ 2 * (((3^K : Nat) : Int)) := by positivity
      have hrowW := mul_le_mul_of_nonneg_left hrow hw
      have hpow :
          (((3^(K+1) : Nat) : Int)) = 3 * (((3^K : Nat) : Int)) := by
        rw [Nat.pow_succ]
        push_cast
        ring
      rw [weightedRectanglePrefix83, hpow]
      calc
        (-15 : Int) * ((((8^N : Nat) : Int)) - 1) *
            (3 * (((3^K : Nat) : Int)) - 1) =
          (-15 : Int) * ((((8^N : Nat) : Int)) - 1) *
              ((((3^K : Nat) : Int)) - 1) +
            (2 * (((3^K : Nat) : Int))) *
              ((-15 : Int) * ((((8^N : Nat) : Int)) - 1)) := by ring
        _ ≤ 2 * weightedRectanglePrefix83 C d N K +
            (2 * (((3^K : Nat) : Int))) *
              reverseDensity83 (fun t => C t K) (fun t => d t K) N :=
          add_le_add ih' hrowW
        _ = 2 *
            (weightedRectanglePrefix83 C d N K +
              (((3^K : Nat) : Int)) *
                reverseDensity83 (fun t => C t K) (fun t => d t K) N) := by
          ring

theorem weightedRectanglePrefix83_positive_of_top_leading_happy
    (C d : Nat → Nat → Nat) (N q : Nat)
    (hN : 1 ≤ N)
    (hC : ∀ t p, t < N → p ≤ q → C t p < 4)
    (hd : ∀ t p, t < N → p ≤ q → d t p < 3)
    (hHappy : HappyCell (C 0 q) (d 0 q)) :
    0 < weightedRectanglePrefix83 C d N (q+1) := by
  have hlower := weightedRectanglePrefix83_ge_floor C d N q
    (fun t p ht hp => hC t p ht (by omega))
    (fun t p ht hp => hd t p ht (by omega))
  have htop := reverseDensity83_ge_of_leading_happy
    (fun t => C t q) (fun t => d t q) hHappy N hN
    (fun t ht => hC t q ht (by omega))
    (fun t ht => hd t q ht (by omega))
  let a : Int := (((8^(N-1) : Nat) : Int))
  let w : Int := (((3^q : Nat) : Int))
  let P : Int := weightedRectanglePrefix83 C d N q
  let R : Int := reverseDensity83 (fun t => C t q) (fun t => d t q) N
  have ha : 0 < a := by dsimp [a]; positivity
  have hw : 0 < w := by dsimp [w]; positivity
  have hNm1 : (N - 1) + 1 = N := by omega
  have hpowNat : 8^N = 8 * 8^(N-1) := by
    calc
      8^N = 8^((N-1)+1) := congrArg (fun k : Nat => 8^k) hNm1.symm
      _ = 8^(N-1) * 8 := Nat.pow_succ 8 (N-1)
      _ = 8 * 8^(N-1) := by ac_rfl
  have hpow : (((8^N : Nat) : Int)) = 8 * a := by
    dsimp [a]
    exact_mod_cast hpowNat
  have hlower' :
      (-15 : Int) * (8*a - 1) * (w - 1) ≤ 2*P := by
    simpa [P, w, hpow] using hlower
  have htop' : 69*a + 15 ≤ R := by
    simpa [a, R] using htop
  rw [weightedRectanglePrefix83]
  change 0 < P + w*R
  by_contra hnot
  have hnonpos : P + w*R ≤ 0 := by omega
  have htopW := mul_le_mul_of_nonneg_left htop'
    (show (0 : Int) ≤ 2*w by positivity)
  have hcombined :
      (-15 : Int) * (8*a - 1) * (w - 1) +
          (2*w) * (69*a + 15) ≤
        2 * (P + w*R) := by
    calc
      (-15 : Int) * (8*a - 1) * (w - 1) +
          (2*w) * (69*a + 15) ≤
        2*P + (2*w)*R := add_le_add hlower' htopW
      _ = 2 * (P + w*R) := by ring
  have haw : 0 < a*w := mul_pos ha hw
  have hpositive :
      0 < (-15 : Int) * (8*a - 1) * (w - 1) +
          (2*w) * (69*a + 15) := by
    nlinarith
  nlinarith

theorem graph_density83_rectangle_exact (E N K : Nat) :
    Finset.sum (Finset.range K) (fun p =>
      (((3^p : Nat) : Int)) *
        reverseDensity83
          (fun t => (graph E t p).seven.carry)
          (fun t => (graph E t p).seven.digit) N) =
      Finset.sum (Finset.range K) (fun p =>
        (((3^p : Nat) : Int)) *
          (digitPotential83 (graph E N p).seven.digit -
            (((8^N : Nat) : Int)) * digitPotential83 (graph E 0 p).seven.digit)) +
      reverseCarry83 (fun t => (graph E t 0).seven.carry) N -
        (((3^K : Nat) : Int)) *
          reverseCarry83 (fun t => (graph E t K).seven.carry) N := by
  apply density83_rectangle_exact
  intro t p ht hp
  exact ⟨graph_carry_lt_four E t p,
    graph_digit_lt_three E t p,
    (graph_cell_exact E t p).1,
    (graph_cell_exact E t p).2⟩

#check density83_physical_table
#check happy_iff_density83_positive
#check reverseDensity83_exact
#check density83_rectangle_exact
#check weightedRectanglePrefix83_positive_of_top_leading_happy
#check graph_density83_rectangle_exact
#print axioms density83_rectangle_exact
#print axioms weightedRectanglePrefix83_positive_of_top_leading_happy
#print axioms graph_density83_rectangle_exact

end GSTU2DPureDivergence83
