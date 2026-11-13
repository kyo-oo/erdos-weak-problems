import Arsenal.ErdosTernary2.Basic
import Arsenal.CardinalWorlds
import Arsenal.CardinalWorldsV2

/-! # Erdos939R4 — THE R=4 CENSUS MODULE (Kernel 60b, S059/W59-A)
The ISOLATED heavy module of Erdős #939 (r-powerful sums): the r=4 census
membership row (25 four-powerful values to 10^4) plus the full 7-conjunct
frontier board. Split from Erdos939.lean per the NO-OOM law (S058 W58-E
runner kill: the 10^4-scan census fold ground the shared job to death —
every heavy scan now runs in its own lean process with its own CI step,
isolated from the 68-kernel queue). Statements are VERBATIM from the
W58-B kernel; only the module boundary moved. -/

set_option maxRecDepth 262144
set_option maxHeartbeats 4000000

namespace E939R4

/-! ## Structural definitions (verbatim from Erdos939) -/

/-- `noDivFrom k n` = true iff no divisor `e` with `2 ≤ e ≤ k` divides `n`. -/
def noDivFrom : Nat → Nat → Bool
  | 0, _ => true
  | d+1, n => decide ((d + 1 ≤ 1 ∨ n % (d + 1) ≠ 0) ∧ noDivFrom d n = true)

/-- `prime n` = true iff `n` is prime (trial-division fold). -/
def prime (n : Nat) : Bool := Nat.ble 2 n && noDivFrom (n - 1) n

/-- `divAll r n d` = true iff for every `e` with `1 ≤ e ≤ d`,
    `e ∣ n → (e not prime ∨ e^r ∣ n)`. -/
def divAll (r n : Nat) : Nat → Bool
  | 0 => true
  | d+1 => decide (divAll r n d = true ∧
      (n % (d+1) ≠ 0 ∨ prime (d+1) ≠ true ∨ n % (d+1) ^ r = 0))

/-- `rpow r n` = true iff `n ≥ 1` and every prime divisor `p` of `n` satisfies `p^r ∣ n`. -/
def rpow (r n : Nat) : Bool := decide (1 ≤ n ∧ divAll r n n = true)

/-! ## The lemma spine needed by the board (verbatim from Erdos939) -/

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

/-- Certified mod-16 obstruction (the odd-pair lane). -/
theorem mod16_obstruction (a b : Nat) (ha : rpow 4 a = true) (hb : rpow 4 b = true)
    (h1 : a % 2 = 1) (h2 : b % 2 = 1) (hsum : rpow 4 (a + b) = true) :
    (a + b) % 16 = 0 := by
  have heven : (a + b) % 2 = 0 := by omega
  have hp2 : prime 2 = true := rfl
  have hd16 : (a + b) % 2 ^ 4 = 0 := rpow_prime_div 4 (a + b) 2 hsum hp2 heven
  exact hd16

/-! ## THE HEAVY ROW (isolated per the NO-OOM law) -/

/-- Certified census (r=4, N=10^4): the 25 listed 4-powerful values. -/
theorem census_r4_members :
    [1, 16, 32, 64, 81, 128, 243, 256, 512, 625, 729, 1024, 1296, 2048, 2187, 2401, 2592,
     3125, 3888, 4096, 5184, 6561, 7776, 8192, 10000].all (fun n => rpow 4 n) = true := by
  decide

/-- Certified zero-solution bound (MINIHUNT lane, r=4 raw form): below 16 there is NO
    pair of 4-powerful numbers whose sum is 4-powerful. -/
theorem no_small_solution_r4 :
    (List.range 16).all (fun a =>
      (List.range 16).all (fun b => !(rpow 4 a && rpow 4 b && rpow 4 (a + b)))) = true := by
  decide

/-- The board (verbatim 7-conjunct frontier receipt of the W58-B kernel):
    obstruction + census + zero-solution + witnesses + 10^15 hunt bracket. -/
theorem board939_r4 :
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

end E939R4

/-! ## Receipts -/

#print axioms E939R4.census_r4_members
#print axioms E939R4.no_small_solution_r4
#print axioms E939R4.board939_r4
#eval "E939R4_CENSUS_GREEN"
