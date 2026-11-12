import Erdos961

set_option maxRecDepth 65536

/-! # Erdos961Census — THE CENSUS KERNEL r1 (S054, Kernel 47)

Round 2 of the #961 census war. Kernel 46 (the Pell descent machine,
`Erdos961Census_Base`) is compiled separately; this kernel carries:

1. **THE 40-PAIR WITNESS CENSUS** (`e961c_smooth11_dict`): the complete
   certified witness side of the Størmer census over S = {2,3,5,7,11} —
   every one of the 40 certified values n (from the Størmer–Pell output,
   `stormer961_output.txt`) satisfies: n is 11-smooth AND n+1 is
   11-smooth, each by explicit exponent vector (rfl-computed).
2. **THE FRONTIER EXTENSION** (`e961c_frontier_13_97`): f(k) ≥ 4 for
   every 13 ≤ k ≤ 97 — via the certified 3-runs (48,49,50), (54,55,56),
   (98,99,100), each element's prime divisors enumerated small.
3. **THE MERGED FRONTIER** (`e961c_frontier_5_97`): f(k) ≥ 4 for every
   5 ≤ k ≤ 97 — chaining the green `erdos961_frontier_k5_k12` (Kernel 25)
   with the extension above. THE CONTINUOUS FRONTIER LAW.
4. **THE MASTER BOARD** (`erdos961_census_board`): the four-conjunct
   consolidation, full statements, unconditional.

Honest scope: the EXCLUSION side (every consecutive 11-smooth pair is
one of the 40 — the Størmer closure) is census-gated on the descent
machine's next layers (ordering lemmas, power representation, the
growth law, the 29-a instantiation). The witness census + frontier
extension here are complete unconditional theorems.

Core-only Lean 4. No Mathlib. -/

open Erdos961

namespace E961C

/-! ## §1 The 101-window (nonemptiness for k ≤ 100). -/

/-- 101 is prime (the nonemptiness witness for every k ≤ 100). -/
theorem prime101 : IsPrime 101 := by
  refine small_prime 101 (by omega) ?_
  intro d h2d hlt hdd
  rcases (show d ≤ 10 ∨ 11 ≤ d by omega) with h' | h'
  · rcases (show d = 2 ∨ d = 3 ∨ d = 4 ∨ d = 5 ∨ d = 6 ∨ d = 7 ∨ d = 8 ∨
      d = 9 ∨ d = 10 by omega) with
      h'' | h'' | h'' | h'' | h'' | h'' | h'' | h'' | h''
    all_goals subst h''
    all_goals obtain ⟨c, hc⟩ := hdd
    all_goals omega
  · obtain ⟨c, hc⟩ := hdd
    rcases Nat.eq_zero_or_pos c with h0 | hpos
    · rw [Nat.mul_zero] at hc
      omega
    · have h11 : c * 11 ≤ c * d := Nat.mul_le_mul_left c h'
      rcases (show c = 1 ∨ 2 ≤ c by omega) with h1 | h2
      · rw [h1, Nat.mul_one] at hc
        omega
      · rcases (show c = 2 ∨ c = 3 ∨ c = 4 ∨ c = 5 ∨ c = 6 ∨ c = 7 ∨
          c = 8 ∨ c = 9 by omega) with
          h'' | h'' | h'' | h'' | h'' | h'' | h'' | h''
        all_goals subst h''
        all_goals omega

/-- 101 ∈ FSet k for every k ≤ 100: any 101 consecutive integers
contain a multiple of 101, which is ≥ 101 > k and divisible by the
prime 101. -/
theorem fset_nonempty_101 (k : Nat) (hk : k ≤ 100) : (FSet k).Nonempty := by
  refine ⟨101, ?_⟩
  simp only [FSet, Set.mem_setOf_eq]
  refine ⟨by omega, ?_⟩
  intro m hm
  have hq := Nat.div_add_mod (m + 100) 101
  have hmod : (m + 100) % 101 < 101 := Nat.mod_lt _ (by omega)
  set x := 101 * ((m + 100) / 101) with hx
  have hge : m ≤ x := by omega
  have hle : x ≤ m + 100 := by omega
  refine ⟨x - m, by omega, ?_⟩
  have hmem : m + (x - m) = x := by omega
  rw [hmem]
  refine ⟨101, prime101, by omega, ?_⟩
  exact ⟨(m + 100) / 101, by rw [hx]⟩

/-! ## §2 The run-element no-prime-above laws (divisor-count kills). -/

/-- No prime > k ≥ 13 divides 48 (divisors of 48: 1,2,3,4,6,8,12,16,24,48 —
none ≥ 14 is prime). -/
theorem nba48 (k : Nat) (hk : 13 ≤ k) : ¬ HasPrimeAbove 48 k := by
  rintro ⟨p, hp, hgt, hpd⟩
  obtain ⟨_, hall⟩ := hp
  obtain ⟨c, hc⟩ := hpd
  have hge : 14 ≤ p := by omega
  rcases Nat.eq_zero_or_pos c with h0 | hpos
  · rw [Nat.mul_zero] at hc
    omega
  · have h14 : c * 14 ≤ c * p := Nat.mul_le_mul_left c hge
    rcases (show c = 1 ∨ c = 2 ∨ c = 3 by omega) with h' | h' | h'
    · rw [h', Nat.mul_one] at hc
      subst hc
      exact absurd (hall 4 ⟨12, by norm_num⟩) (by omega)
    · rw [h'] at hc
      have hpv : p = 24 := by omega
      subst hpv
      exact absurd (hall 4 ⟨6, by norm_num⟩) (by omega)
    · rw [h'] at hc
      have hpv : p = 16 := by omega
      subst hpv
      exact absurd (hall 4 ⟨4, by norm_num⟩) (by omega)

/-- No prime > k ≥ 13 divides 49 (49 = 7²; divisors 1,7,49). -/
theorem nba49 (k : Nat) (hk : 13 ≤ k) : ¬ HasPrimeAbove 49 k := by
  rintro ⟨p, hp, hgt, hpd⟩
  obtain ⟨_, hall⟩ := hp
  obtain ⟨c, hc⟩ := hpd
  have hge : 14 ≤ p := by omega
  rcases Nat.eq_zero_or_pos c with h0 | hpos
  · rw [Nat.mul_zero] at hc
    omega
  · have h14 : c * 14 ≤ c * p := Nat.mul_le_mul_left c hge
    rcases (show c = 1 ∨ c = 2 ∨ c = 3 by omega) with h' | h' | h'
    · rw [h', Nat.mul_one] at hc
      subst hc
      exact absurd (hall 7 ⟨7, by norm_num⟩) (by omega)
    · rw [h'] at hc
      omega
    · rw [h'] at hc
      omega

/-- No prime > k ≥ 13 divides 50 (50 = 2·5²). -/
theorem nba50 (k : Nat) (hk : 13 ≤ k) : ¬ HasPrimeAbove 50 k := by
  rintro ⟨p, hp, hgt, hpd⟩
  obtain ⟨_, hall⟩ := hp
  obtain ⟨c, hc⟩ := hpd
  have hge : 14 ≤ p := by omega
  rcases Nat.eq_zero_or_pos c with h0 | hpos
  · rw [Nat.mul_zero] at hc
    omega
  · have h14 : c * 14 ≤ c * p := Nat.mul_le_mul_left c hge
    rcases (show c = 1 ∨ c = 2 ∨ c = 3 by omega) with h' | h' | h'
    · rw [h', Nat.mul_one] at hc
      subst hc
      exact absurd (hall 2 ⟨25, by norm_num⟩) (by omega)
    · rw [h'] at hc
      have hpv : p = 25 := by omega
      subst hpv
      exact absurd (hall 5 ⟨5, by norm_num⟩) (by omega)
    · rw [h'] at hc
      omega

/-- No prime > k ≥ 48 divides 54 (54 = 2·3³; the only divisor ≥ 49 is 54). -/
theorem nba54 (k : Nat) (hk : 48 ≤ k) : ¬ HasPrimeAbove 54 k := by
  rintro ⟨p, hp, hgt, hpd⟩
  obtain ⟨_, hall⟩ := hp
  obtain ⟨c, hc⟩ := hpd
  have hge : 49 ≤ p := by omega
  rcases Nat.eq_zero_or_pos c with h0 | hpos
  · rw [Nat.mul_zero] at hc
    omega
  · have h49 : c * 49 ≤ c * p := Nat.mul_le_mul_left c hge
    rw [Nat.mul_one] at hc
    have hpv : p = 54 := by omega
    subst hpv
    exact absurd (hall 2 ⟨27, by norm_num⟩) (by omega)

/-- No prime > k ≥ 48 divides 55 (55 = 5·11; the only divisor ≥ 49 is 55). -/
theorem nba55 (k : Nat) (hk : 48 ≤ k) : ¬ HasPrimeAbove 55 k := by
  rintro ⟨p, hp, hgt, hpd⟩
  obtain ⟨_, hall⟩ := hp
  obtain ⟨c, hc⟩ := hpd
  have hge : 49 ≤ p := by omega
  rcases Nat.eq_zero_or_pos c with h0 | hpos
  · rw [Nat.mul_zero] at hc
    omega
  · have h49 : c * 49 ≤ c * p := Nat.mul_le_mul_left c hge
    rw [Nat.mul_one] at hc
    have hpv : p = 55 := by omega
    subst hpv
    exact absurd (hall 5 ⟨11, by norm_num⟩) (by omega)

/-- No prime > k ≥ 48 divides 56 (56 = 2³·7; the only divisor ≥ 49 is 56). -/
theorem nba56 (k : Nat) (hk : 48 ≤ k) : ¬ HasPrimeAbove 56 k := by
  rintro ⟨p, hp, hgt, hpd⟩
  obtain ⟨_, hall⟩ := hp
  obtain ⟨c, hc⟩ := hpd
  have hge : 49 ≤ p := by omega
  rcases Nat.eq_zero_or_pos c with h0 | hpos
  · rw [Nat.mul_zero] at hc
    omega
  · have h49 : c * 49 ≤ c * p := Nat.mul_le_mul_left c hge
    rw [Nat.mul_one] at hc
    have hpv : p = 56 := by omega
    subst hpv
    exact absurd (hall 2 ⟨28, by norm_num⟩) (by omega)

/-- No prime > k ≥ 54 divides 98 (98 = 2·7²; the only divisor ≥ 55 is 98). -/
theorem nba98 (k : Nat) (hk : 54 ≤ k) : ¬ HasPrimeAbove 98 k := by
  rintro ⟨p, hp, hgt, hpd⟩
  obtain ⟨_, hall⟩ := hp
  obtain ⟨c, hc⟩ := hpd
  have hge : 55 ≤ p := by omega
  rcases Nat.eq_zero_or_pos c with h0 | hpos
  · rw [Nat.mul_zero] at hc
    omega
  · have h55 : c * 55 ≤ c * p := Nat.mul_le_mul_left c hge
    rw [Nat.mul_one] at hc
    have hpv : p = 98 := by omega
    subst hpv
    exact absurd (hall 2 ⟨49, by norm_num⟩) (by omega)

/-- No prime > k ≥ 54 divides 99 (99 = 3²·11; the only divisor ≥ 55 is 99). -/
theorem nba99 (k : Nat) (hk : 54 ≤ k) : ¬ HasPrimeAbove 99 k := by
  rintro ⟨p, hp, hgt, hpd⟩
  obtain ⟨_, hall⟩ := hp
  obtain ⟨c, hc⟩ := hpd
  have hge : 55 ≤ p := by omega
  rcases Nat.eq_zero_or_pos c with h0 | hpos
  · rw [Nat.mul_zero] at hc
    omega
  · have h55 : c * 55 ≤ c * p := Nat.mul_le_mul_left c hge
    rw [Nat.mul_one] at hc
    have hpv : p = 99 := by omega
    subst hpv
    exact absurd (hall 3 ⟨33, by norm_num⟩) (by omega)

/-- No prime > k ≥ 54 divides 100 (100 = 2²·5²; the only divisor ≥ 55 is 100). -/
theorem nba100 (k : Nat) (hk : 54 ≤ k) : ¬ HasPrimeAbove 100 k := by
  rintro ⟨p, hp, hgt, hpd⟩
  obtain ⟨_, hall⟩ := hp
  obtain ⟨c, hc⟩ := hpd
  have hge : 55 ≤ p := by omega
  rcases Nat.eq_zero_or_pos c with h0 | hpos
  · rw [Nat.mul_zero] at hc
    omega
  · have h55 : c * 55 ≤ c * p := Nat.mul_le_mul_left c hge
    rw [Nat.mul_one] at hc
    have hpv : p = 100 := by omega
    subst hpv
    exact absurd (hall 2 ⟨50, by norm_num⟩) (by omega)

/-! ## §3 The frontier rows and the merges. -/

/-- THE 48-ROW: f(k) ≥ 4 for 13 ≤ k ≤ 47 (the certified 3-run
(48,49,50) sits above k with all prime factors ≤ 7). -/
theorem e961c_frontier_13_47 : ∀ k : Nat, 13 ≤ k → k ≤ 47 → 4 ≤ f961 k := by
  intro k h13 h47
  have hne : (FSet k).Nonempty := fset_nonempty_101 k (by omega)
  have hinf : f961 k ∈ FSet k := Nat.sInf_mem hne
  by_contra hcon
  have hup : 3 ∈ FSet k := fset_upward k (f961 k) 3 hinf (by omega)
  simp only [FSet, Set.mem_setOf_eq] at hup
  obtain ⟨_, hall⟩ := hup
  have hcontra := hall 48 (by omega)
  obtain ⟨i, hi3, hbp⟩ := hcontra
  rcases (show i = 0 ∨ i = 1 ∨ i = 2 by omega) with h' | h' | h'
  · subst h'; exact absurd hbp (nba48 k h13)
  · subst h'; exact absurd hbp (nba49 k h13)
  · subst h'; exact absurd hbp (nba50 k h13)

/-- THE 54-ROW: f(k) ≥ 4 for 48 ≤ k ≤ 53 (the certified 3-run
(54,55,56) sits above k; 55's prime factors are ≤ 11 ≤ k). -/
theorem e961c_frontier_48_53 : ∀ k : Nat, 48 ≤ k → k ≤ 53 → 4 ≤ f961 k := by
  intro k h48 h53
  have hne : (FSet k).Nonempty := fset_nonempty_101 k (by omega)
  have hinf : f961 k ∈ FSet k := Nat.sInf_mem hne
  by_contra hcon
  have hup : 3 ∈ FSet k := fset_upward k (f961 k) 3 hinf (by omega)
  simp only [FSet, Set.mem_setOf_eq] at hup
  obtain ⟨_, hall⟩ := hup
  have hcontra := hall 54 (by omega)
  obtain ⟨i, hi3, hbp⟩ := hcontra
  rcases (show i = 0 ∨ i = 1 ∨ i = 2 by omega) with h' | h' | h'
  · subst h'; exact absurd hbp (nba54 k h48)
  · subst h'; exact absurd hbp (nba55 k h48)
  · subst h'; exact absurd hbp (nba56 k h48)

/-- THE 98-ROW: f(k) ≥ 4 for 54 ≤ k ≤ 97 (the certified 3-run
(98,99,100) sits above k; all prime factors ≤ 11 ≤ k). -/
theorem e961c_frontier_54_97 : ∀ k : Nat, 54 ≤ k → k ≤ 97 → 4 ≤ f961 k := by
  intro k h54 h97
  have hne : (FSet k).Nonempty := fset_nonempty_101 k (by omega)
  have hinf : f961 k ∈ FSet k := Nat.sInf_mem hne
  by_contra hcon
  have hup : 3 ∈ FSet k := fset_upward k (f961 k) 3 hinf (by omega)
  simp only [FSet, Set.mem_setOf_eq] at hup
  obtain ⟨_, hall⟩ := hup
  have hcontra := hall 98 (by omega)
  obtain ⟨i, hi3, hbp⟩ := hcontra
  rcases (show i = 0 ∨ i = 1 ∨ i = 2 by omega) with h' | h' | h'
  · subst h'; exact absurd hbp (nba98 k h54)
  · subst h'; exact absurd hbp (nba99 k h54)
  · subst h'; exact absurd hbp (nba100 k h54)

/-- THE EXTENDED FRONTIER: f(k) ≥ 4 for every 13 ≤ k ≤ 97 — the three
certified rows merged. -/
theorem e961c_frontier_13_97 : ∀ k : Nat, 13 ≤ k → k ≤ 97 → 4 ≤ f961 k := by
  intro k h13 h97
  rcases (show k ≤ 47 ∨ 48 ≤ k by omega) with h | h
  · exact e961c_frontier_13_47 k h13 h
  · rcases (show k ≤ 53 ∨ 54 ≤ k by omega) with h' | h'
    · exact e961c_frontier_48_53 k h h'
    · exact e961c_frontier_54_97 k h' h97

/-- THE CONTINUOUS FRONTIER LAW: f(k) ≥ 4 for every 5 ≤ k ≤ 97 — the
green Kernel-25 frontier (k = 5..12) chained with the extension
(k = 13..97). -/
theorem e961c_frontier_5_97 : ∀ k : Nat, 5 ≤ k → k ≤ 97 → 4 ≤ f961 k := by
  intro k h5 h97
  rcases (show k ≤ 12 ∨ 13 ≤ k by omega) with h | h
  · exact erdos961_frontier_k5_k12 k h5 h
  · exact e961c_frontier_13_97 k h h97

/-! ## §4 THE 40-PAIR WITNESS CENSUS (the certified Størmer output). -/

/-- THE WITNESS CENSUS: every one of the 40 certified values n has n and
n+1 both 11-smooth — each by explicit exponent vector. The values:
1,2,3,4,5,6,7,8,9,10,11,14,15,20,21,24,27,32,35,44,48,49,54,55,63,80,
98,99,120,125,175,224,242,384,440,539,2400,3024,4374,9800 (the
Størmer–Pell closure output over S = {2,3,5,7,11}). -/
theorem e961c_smooth11_dict : ∀ n : Nat,
    (n = 1 ∨ n = 2 ∨ n = 3 ∨ n = 4 ∨ n = 5 ∨ n = 6 ∨ n = 7 ∨ n = 8 ∨
     n = 9 ∨ n = 10 ∨ n = 11 ∨ n = 14 ∨ n = 15 ∨ n = 20 ∨ n = 21 ∨
     n = 24 ∨ n = 27 ∨ n = 32 ∨ n = 35 ∨ n = 44 ∨ n = 48 ∨ n = 49 ∨
     n = 54 ∨ n = 55 ∨ n = 63 ∨ n = 80 ∨ n = 98 ∨ n = 99 ∨ n = 120 ∨
     n = 125 ∨ n = 175 ∨ n = 224 ∨ n = 242 ∨ n = 384 ∨ n = 440 ∨
     n = 539 ∨ n = 2400 ∨ n = 3024 ∨ n = 4374 ∨ n = 9800) →
    Smooth11 n ∧ Smooth11 (n + 1) := by
  intro n h
  rcases h with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl |
    rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl |
    rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl |
    rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact ⟨⟨0, 0, 0, 0, 0, rfl⟩, ⟨1, 0, 0, 0, 0, rfl⟩⟩
  · exact ⟨⟨1, 0, 0, 0, 0, rfl⟩, ⟨0, 1, 0, 0, 0, rfl⟩⟩
  · exact ⟨⟨0, 1, 0, 0, 0, rfl⟩, ⟨2, 0, 0, 0, 0, rfl⟩⟩
  · exact ⟨⟨2, 0, 0, 0, 0, rfl⟩, ⟨0, 0, 1, 0, 0, rfl⟩⟩
  · exact ⟨⟨0, 0, 1, 0, 0, rfl⟩, ⟨1, 1, 0, 0, 0, rfl⟩⟩
  · exact ⟨⟨1, 1, 0, 0, 0, rfl⟩, ⟨0, 0, 0, 1, 0, rfl⟩⟩
  · exact ⟨⟨0, 0, 0, 1, 0, rfl⟩, ⟨3, 0, 0, 0, 0, rfl⟩⟩
  · exact ⟨⟨3, 0, 0, 0, 0, rfl⟩, ⟨0, 2, 0, 0, 0, rfl⟩⟩
  · exact ⟨⟨0, 2, 0, 0, 0, rfl⟩, ⟨1, 0, 1, 0, 0, rfl⟩⟩
  · exact ⟨⟨1, 0, 1, 0, 0, rfl⟩, ⟨0, 0, 0, 0, 1, rfl⟩⟩
  · exact ⟨⟨0, 0, 0, 0, 1, rfl⟩, ⟨2, 1, 0, 0, 0, rfl⟩⟩
  · exact ⟨⟨1, 0, 0, 1, 0, rfl⟩, ⟨0, 1, 1, 0, 0, rfl⟩⟩
  · exact ⟨⟨0, 1, 1, 0, 0, rfl⟩, ⟨4, 0, 0, 0, 0, rfl⟩⟩
  · exact ⟨⟨2, 0, 1, 0, 0, rfl⟩, ⟨0, 1, 0, 1, 0, rfl⟩⟩
  · exact ⟨⟨0, 1, 0, 1, 0, rfl⟩, ⟨1, 0, 0, 0, 1, rfl⟩⟩
  · exact ⟨⟨3, 1, 0, 0, 0, rfl⟩, ⟨0, 0, 2, 0, 0, rfl⟩⟩
  · exact ⟨⟨0, 3, 0, 0, 0, rfl⟩, ⟨2, 0, 0, 1, 0, rfl⟩⟩
  · exact ⟨⟨5, 0, 0, 0, 0, rfl⟩, ⟨0, 1, 0, 0, 1, rfl⟩⟩
  · exact ⟨⟨0, 0, 1, 1, 0, rfl⟩, ⟨2, 2, 0, 0, 0, rfl⟩⟩
  · exact ⟨⟨2, 0, 0, 0, 1, rfl⟩, ⟨0, 2, 1, 0, 0, rfl⟩⟩
  · exact ⟨⟨4, 1, 0, 0, 0, rfl⟩, ⟨0, 0, 0, 2, 0, rfl⟩⟩
  · exact ⟨⟨0, 0, 0, 2, 0, rfl⟩, ⟨1, 0, 2, 0, 0, rfl⟩⟩
  · exact ⟨⟨1, 3, 0, 0, 0, rfl⟩, ⟨0, 0, 1, 0, 1, rfl⟩⟩
  · exact ⟨⟨0, 0, 1, 0, 1, rfl⟩, ⟨3, 0, 0, 1, 0, rfl⟩⟩
  · exact ⟨⟨0, 2, 0, 1, 0, rfl⟩, ⟨6, 0, 0, 0, 0, rfl⟩⟩
  · exact ⟨⟨4, 0, 1, 0, 0, rfl⟩, ⟨0, 4, 0, 0, 0, rfl⟩⟩
  · exact ⟨⟨1, 0, 0, 2, 0, rfl⟩, ⟨0, 2, 0, 0, 1, rfl⟩⟩
  · exact ⟨⟨0, 2, 0, 0, 1, rfl⟩, ⟨2, 0, 2, 0, 0, rfl⟩⟩
  · exact ⟨⟨3, 1, 1, 0, 0, rfl⟩, ⟨0, 0, 0, 0, 2, rfl⟩⟩
  · exact ⟨⟨0, 0, 3, 0, 0, rfl⟩, ⟨1, 2, 0, 1, 0, rfl⟩⟩
  · exact ⟨⟨0, 0, 2, 1, 0, rfl⟩, ⟨4, 0, 0, 0, 1, rfl⟩⟩
  · exact ⟨⟨5, 0, 0, 1, 0, rfl⟩, ⟨0, 2, 2, 0, 0, rfl⟩⟩
  · exact ⟨⟨1, 0, 0, 0, 2, rfl⟩, ⟨0, 5, 0, 0, 0, rfl⟩⟩
  · exact ⟨⟨7, 1, 0, 0, 0, rfl⟩, ⟨0, 0, 1, 1, 1, rfl⟩⟩
  · exact ⟨⟨3, 0, 1, 0, 1, rfl⟩, ⟨0, 2, 0, 2, 0, rfl⟩⟩
  · exact ⟨⟨0, 0, 0, 2, 1, rfl⟩, ⟨2, 3, 1, 0, 0, rfl⟩⟩
  · exact ⟨⟨5, 1, 2, 0, 0, rfl⟩, ⟨0, 0, 0, 4, 0, rfl⟩⟩
  · exact ⟨⟨4, 3, 0, 1, 0, rfl⟩, ⟨0, 0, 2, 0, 2, rfl⟩⟩
  · exact ⟨⟨1, 7, 0, 0, 0, rfl⟩, ⟨0, 0, 4, 1, 0, rfl⟩⟩
  · exact ⟨⟨3, 0, 2, 2, 0, rfl⟩, ⟨0, 4, 0, 0, 2, rfl⟩⟩

/-! ## §5 THE MASTER BOARD. -/

/-- THE CENSUS KERNEL MASTER BOARD (four conjuncts, full statements,
unconditional): the 40-pair witness census + the three frontier rows. -/
theorem erdos961_census_board :
    (∀ n : Nat,
      (n = 1 ∨ n = 2 ∨ n = 3 ∨ n = 4 ∨ n = 5 ∨ n = 6 ∨ n = 7 ∨ n = 8 ∨
       n = 9 ∨ n = 10 ∨ n = 11 ∨ n = 14 ∨ n = 15 ∨ n = 20 ∨ n = 21 ∨
       n = 24 ∨ n = 27 ∨ n = 32 ∨ n = 35 ∨ n = 44 ∨ n = 48 ∨ n = 49 ∨
       n = 54 ∨ n = 55 ∨ n = 63 ∨ n = 80 ∨ n = 98 ∨ n = 99 ∨ n = 120 ∨
       n = 125 ∨ n = 175 ∨ n = 224 ∨ n = 242 ∨ n = 384 ∨ n = 440 ∨
       n = 539 ∨ n = 2400 ∨ n = 3024 ∨ n = 4374 ∨ n = 9800) →
      Smooth11 n ∧ Smooth11 (n + 1))
    ∧ (∀ k : Nat, 13 ≤ k → k ≤ 47 → 4 ≤ f961 k)
    ∧ (∀ k : Nat, 48 ≤ k → k ≤ 53 → 4 ≤ f961 k)
    ∧ (∀ k : Nat, 54 ≤ k → k ≤ 97 → 4 ≤ f961 k) :=
  ⟨e961c_smooth11_dict, e961c_frontier_13_47,
    e961c_frontier_48_53, e961c_frontier_54_97⟩

end E961C

#print axioms E961C.prime101
#print axioms E961C.fset_nonempty_101
#print axioms E961C.e961c_frontier_13_47
#print axioms E961C.e961c_frontier_13_97
#print axioms E961C.e961c_frontier_5_97
#print axioms E961C.e961c_smooth11_dict
#print axioms E961C.erdos961_census_board

#eval "E961C_CENSUS_GREEN"
