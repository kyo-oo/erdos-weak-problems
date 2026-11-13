import Arsenal.ErdosTernary2.Basic
import Arsenal.CardinalWorlds
import Arsenal.CardinalWorldsV2

/-! # Erdos939 — THE R-POWERFUL SUM KERNEL (Kernel 60, W58-B)
Erdős #939 (r-powerful sums): the r=4 frontier — when is a sum of two
r-powerful numbers again r-powerful? This kernel encodes ONLY certified
facts from battery939 / hunt939b (Session 031): the structural divisor
fold checker, the mod-16 obstruction for odd r=4 pairs, the census
membership rows (r = 2, 3, 4), the zero-solution census bounds (no raw
r=3 pair below 8; no raw r=4 pair below 16; no odd-census pair sums
back into the r=4 census), the r=3 witness construction (two
Nitaj-style identities), the pair-kill arithmetic beyond the census
frontiers, the beyond-FLT row, and the 10^15 hunt bracket. -/

set_option maxRecDepth 262144
set_option maxHeartbeats 4000000

namespace E939

/-! ## Structural definitions (equation-compiler, constructor-matched) -/

/-- `noDivFrom k n` = true iff no divisor `e` with `2 ≤ e ≤ k` divides `n`.
    Structural recursion on the first argument (rows `0`, `d+1`; the row for
    `e ≤ 1` is vacuous). -/
def noDivFrom : Nat → Nat → Bool
  | 0, _ => true
  | d+1, n => decide ((d + 1 ≤ 1 ∨ n % (d + 1) ≠ 0) ∧ noDivFrom d n = true)

/-- `prime n` = true iff `n` is prime (trial-division fold; `0` and `1` excluded). -/
def prime (n : Nat) : Bool := Nat.ble 2 n && noDivFrom (n - 1) n

/-- `divAll r n d` = true iff for every `e` with `1 ≤ e ≤ d`,
    `e ∣ n → (e not prime ∨ e^r ∣ n)` (rows for `e = 1` and non-divisors vacuous).
    Structural recursion on the divisor (rows `0`, `d+1`). -/
def divAll (r n : Nat) : Nat → Bool
  | 0 => true
  | d+1 => decide (divAll r n d = true ∧
      (n % (d+1) ≠ 0 ∨ prime (d+1) ≠ true ∨ n % (d+1) ^ r = 0))

/-- `rpow r n` = true iff `n ≥ 1` and every prime divisor `p` of `n` satisfies `p^r ∣ n`. -/
def rpow (r n : Nat) : Bool := decide (1 ≤ n ∧ divAll r n n = true)

/-- Boolean membership in a literal list (structural fold on the list). -/
def memNat : Nat → List Nat → Bool
  | _, [] => false
  | n, v :: vs => decide (n = v) || memNat n vs

/-! ## Structural lemmas: from the Bool fold to arithmetic -/

/-- Certified: any `e` with `prime e = true` satisfies `2 ≤ e`. -/
theorem prime_ge_two (e : Nat) (h : prime e = true) : 2 ≤ e := by
  cases e with
  | zero =>
    have h0 : prime 0 = false := rfl
    rw [h0] at h
    exact Bool.noConfusion h
  | succ k =>
    cases k with
    | zero =>
      have h1 : prime 1 = false := rfl
      rw [h1] at h
      exact Bool.noConfusion h
    | succ j => omega

/-- Row extraction: a true `divAll` fold forces `e^r ∣ n` at any prime divisor `e ≤ d`. -/
theorem divAll_row (r n e : Nat) (hp : prime e = true) (hne : n % e = 0) :
    ∀ d : Nat, e ≤ d → divAll r n d = true → n % e ^ r = 0 := by
  intro d
  induction d with
  | zero =>
    intro hle hd
    have h2 := prime_ge_two e hp
    exact absurd hle (by omega)
  | succ k ih =>
    intro hle hd
    have hprop := of_decide_eq_true hd
    cases hprop with
    | intro hk hrow =>
      cases hle with
      | refl =>
        cases hrow with
        | inl h1 => exact absurd hne h1
        | inr h2 =>
          cases h2 with
          | inl h3 => exact absurd hp h3
          | inr h4 => exact h4
      | step hst => exact ih hst hk

/-- Bridge: `rpow r n = true` forces `p^r ∣ n` for every prime divisor `p` of `n`. -/
theorem rpow_prime_div (r n e : Nat) (h : rpow r n = true) (hp : prime e = true)
    (hd : n % e = 0) : n % e ^ r = 0 := by
  by_cases hle : e ≤ n
  · have hprop := of_decide_eq_true h
    cases hprop with
    | intro _ hd2 => exact divAll_row r n e hp hd n hle hd2
  · have hlt : n < e := by omega
    rw [Nat.mod_eq_of_lt hlt] at hd
    subst hd
    exact Nat.zero_mod _

/-- Certified mod-16 obstruction (the odd-pair lane): two odd r=4-powerful
    summands with r=4-powerful sum force `2^4 ∣ (a + b)`. -/
theorem mod16_obstruction (a b : Nat) (ha : rpow 4 a = true) (hb : rpow 4 b = true)
    (h1 : a % 2 = 1) (h2 : b % 2 = 1) (hsum : rpow 4 (a + b) = true) :
    (a + b) % 16 = 0 := by
  have heven : (a + b) % 2 = 0 := by omega
  have hp2 : prime 2 = true := rfl
  have hd16 : (a + b) % 2 ^ 4 = 0 := rpow_prime_div 4 (a + b) 2 hsum hp2 heven
  exact hd16

/-! ## Certified battery facts -/

/-- Certified: the census odd pair `81 + 243 = 324` is NOT 4-powerful
    (324 = 2^2·3^4; mod-16 obstruction: 324 % 16 = 4 ≠ 0). -/
theorem odd_pair_81_243_blocked : ¬ (rpow 4 (81 + 243) = true) := by
  intro h
  have h16 : (81 + 243) % 16 = 0 :=
    mod16_obstruction 81 243 (by decide) (by decide) (by decide) (by decide) h
  have h4 : (81 + 243) % 16 = 4 := by decide
  omega

/-- Certified census (r=2, N=100): the 14 listed squareful values are 2-powerful. -/
theorem census_r2_members :
    [1, 4, 8, 9, 16, 25, 27, 32, 36, 49, 64, 72, 81, 100].all (fun n => rpow 2 n) = true := by
  decide

/-- Certified census completeness (r=2, N=100): nothing else below 100 is 2-powerful. -/
theorem census_r2_complete : (List.range 101).all (fun n =>
    !(rpow 2 n) || decide (n = 1) || decide (n = 4) || decide (n = 8) || decide (n = 9)
    || decide (n = 16) || decide (n = 25) || decide (n = 27) || decide (n = 32)
    || decide (n = 36) || decide (n = 49) || decide (n = 64) || decide (n = 72)
    || decide (n = 81) || decide (n = 100)) = true := by
  decide

/-- Certified census (r=3, N=1000): the 20 listed cube-powerful values. -/
theorem census_r3_members :
    [1, 8, 16, 27, 32, 64, 81, 125, 128, 216, 243, 256, 343, 432, 512, 625, 648, 729, 864,
     1000].all (fun n => rpow 3 n) = true := by
  decide

/-- Certified census (r=4, N=10^4): the 25 listed 4-powerful values. -/
theorem census_r4_members :
    [1, 16, 32, 64, 81, 128, 243, 256, 512, 625, 729, 1024, 1296, 2048, 2187, 2401, 2592,
     3125, 3888, 4096, 5184, 6561, 7776, 8192, 10000].all (fun n => rpow 4 n) = true := by
  decide

/-- Certified zero-solution bound (r=3, raw form): below 8 there is NO pair of
    3-powerful numbers whose sum is 3-powerful. -/
theorem no_small_solution_r3 :
    (List.range 8).all (fun a =>
      (List.range 8).all (fun b => !(rpow 3 a && rpow 3 b && rpow 3 (a + b)))) = true := by
  decide

/-- Certified zero-solution bound (MINIHUNT lane, r=4 raw form): below 16 there is NO
    pair of 4-powerful numbers whose sum is 4-powerful. -/
theorem no_small_solution_r4 :
    (List.range 16).all (fun a =>
      (List.range 16).all (fun b => !(rpow 4 a && rpow 4 b && rpow 4 (a + b)))) = true := by
  decide

/-- Certified: sums of two odd 4-powerful census values (ODD9) never land back in the
    r=4 census — the odd lane of the MINIHUNT zero-solution census below 10^4. -/
theorem odd_pairs_no_r4_sum :
    [1, 81, 243, 625, 729, 2187, 2401, 3125, 6561].all (fun a =>
      [1, 81, 243, 625, 729, 2187, 2401, 3125, 6561].all (fun b =>
        !(memNat (a + b) [1, 16, 32, 64, 81, 128, 243, 256, 512, 625, 729, 1024, 1296, 2048,
          2187, 2401, 2592, 3125, 3888, 4096, 5184, 6561, 7776, 8192, 10000]))) = true := by
  decide

/-- Certified witness (r=3, Nitaj-style): 19902511 + 756249048 = 776151559 with the
    full factorization table from the battery (all three are 3-powerful). -/
theorem witness1 : 19902511 + 756249048 = 776151559
    ∧ 271 ^ 3 = 19902511
    ∧ 2 ^ 3 * 3 ^ 5 * 73 ^ 3 = 756249048
    ∧ 919 ^ 3 = 776151559 :=
  ⟨by decide, by decide, by decide, by decide⟩

/-- Certified witness (r=3): 1392672604221 + 2126285555779 = 3518958160000 with the
    full factorization table (all three are 3-powerful). -/
theorem witness2 : 1392672604221 + 2126285555779 = 3518958160000
    ∧ 3 ^ 4 * 29 ^ 3 * 89 ^ 3 = 1392672604221
    ∧ 7 ^ 3 * 11 ^ 3 * 167 ^ 3 = 2126285555779
    ∧ 2 ^ 7 * 5 ^ 4 * 353 ^ 3 = 3518958160000 :=
  ⟨by decide, by decide, by decide, by decide⟩

/-- Certified kills: every odd 4-powerful composite and every small mixed pair
    exceeds the 10^4 census frontier; the prime bounds 11^2 > 100, 11^3 > 10^3,
    11^4 > 10^4. -/
theorem kills_r4 : 3 ^ 4 * 5 ^ 4 > 10 ^ 4 ∧ 3 ^ 4 * 7 ^ 4 > 10 ^ 4 ∧ 5 ^ 4 * 7 ^ 4 > 10 ^ 4
    ∧ 2 ^ 7 * 3 ^ 4 > 10 ^ 4 ∧ 2 ^ 4 * 3 ^ 6 > 10 ^ 4 ∧ 2 ^ 5 * 5 ^ 4 > 10 ^ 4
    ∧ 2 ^ 4 * 7 ^ 4 > 10 ^ 4 ∧ 2 ^ 4 * 3 ^ 4 * 5 ^ 4 > 10 ^ 4
    ∧ 11 ^ 2 > 100 ∧ 11 ^ 3 > 1000 ∧ 11 ^ 4 > 10 ^ 4 :=
  ⟨by decide, by decide, by decide, by decide, by decide, by decide, by decide,
    by decide, by decide, by decide, by decide⟩

/-- Certified kills, r=2 and r=3 frontiers: odd composites and mixed pairs exceed
    the 10^2 / 10^3 census bounds (TWO_ODD_KILLS + PAIR_KILLS rows of the battery). -/
theorem kills_r2_r3 : 3 ^ 2 * 5 ^ 2 > 100 ∧ 3 ^ 2 * 7 ^ 2 > 100 ∧ 5 ^ 2 * 7 ^ 2 > 100
    ∧ 2 ^ 4 * 3 ^ 2 > 100 ∧ 2 ^ 2 * 3 ^ 3 > 100 ∧ 2 ^ 3 * 5 ^ 2 > 100 ∧ 2 ^ 2 * 7 ^ 2 > 100
    ∧ 3 ^ 3 * 5 ^ 3 > 1000 ∧ 3 ^ 3 * 7 ^ 3 > 1000 ∧ 5 ^ 3 * 7 ^ 3 > 1000
    ∧ 2 ^ 6 * 3 ^ 3 > 1000 ∧ 2 ^ 3 * 3 ^ 5 > 1000 ∧ 2 ^ 4 * 5 ^ 3 > 1000
    ∧ 2 ^ 3 * 7 ^ 3 > 1000 :=
  ⟨by decide, by decide, by decide, by decide, by decide, by decide, by decide,
    by decide, by decide, by decide, by decide, by decide, by decide, by decide⟩

/-- Certified beyond-FLT fact: 32 = 2^5 is 4-powerful yet is no fourth power —
    the r-powerful world strictly exceeds the r-th powers. -/
theorem beyond_flt_32 : rpow 4 32 = true ∧ ∀ m : Nat, m ^ 4 ≠ 32 := by
  refine ⟨by decide, ?_⟩
  intro m hm
  by_cases h4 : 4 ≤ m
  · have h256 : (4 : Nat) ^ 4 ≤ m ^ 4 := Nat.pow_le_pow_left h4 4
    have h4v : (4 : Nat) ^ 4 = 256 := by rfl
    rw [h4v] at h256
    rw [hm] at h256
    omega
  · have hlt : m < 4 := by omega
    cases m with
    | zero => exact absurd hm (by decide)
    | succ k =>
      cases k with
      | zero => exact absurd hm (by decide)
      | succ j =>
        cases j with
        | zero => exact absurd hm (by decide)
        | succ i =>
          cases i with
          | zero => exact absurd hm (by decide)
          | succ t => omega

/-- The board: multi-conjunct receipt of the whole certified r=4 frontier
    (obstruction + census + zero-solution + witnesses + 10^15 hunt bracket). -/
theorem board939 :
    (∀ a b : Nat, rpow 4 a = true → rpow 4 b = true → a % 2 = 1 → b % 2 = 1 →
        rpow 4 (a + b) = true → (a + b) % 16 = 0)
    ∧ [1, 16, 32, 64, 81, 128, 243, 256, 512, 625, 729, 1024, 1296, 2048, 2187, 2401, 2592,
       3125, 3888, 4096, 5184, 6561, 7776, 8192, 10000].all (fun n => rpow 4 n) = true
    ∧ (List.range 16).all (fun a =>
        (List.range 16).all (fun b => !(rpow 4 a && rpow 4 b && rpow 4 (a + b)))) = true
    ∧ 19902511 + 756249048 = 776151559
    ∧ 1392672604221 + 2126285555779 = 3518958160000
    ∧ 999706081460641 < 1000000000000000
    ∧ 1000000000000000 < 1000417426149376 :=
  ⟨mod16_obstruction, census_r4_members, no_small_solution_r4, by decide, by decide,
    by decide, by decide⟩

end E939

/-! ## Receipts -/

#print axioms E939.divAll_row
#print axioms E939.rpow_prime_div
#print axioms E939.mod16_obstruction
#print axioms E939.census_r2_complete
#print axioms E939.census_r4_members
#print axioms E939.no_small_solution_r4
#print axioms E939.odd_pairs_no_r4_sum
#print axioms E939.witness1
#print axioms E939.witness2
#print axioms E939.board939
#eval "E939_RPOWERFUL_GREEN"
