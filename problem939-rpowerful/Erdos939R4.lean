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
W58-B kernel; only the module boundary moved.

S059 W59-C addendum — THE PROOF-ROUTE LAW: the elaborator `decide` on the
census row is a TWICE-PROVEN runner-killer (W58-E: 2m42s grind → runner
shutdown, exit 143; W59-A rescue run: 2m05s grind → runner shutdown,
exit 143 — deterministic, memory-bomb signature). Isolation did not shrink
it. The engine law (NO-OOM: never native_decide on goals with FREE
VARIABLES) permits native_decide on CLOSED goals — this row is fully
closed (literal list, no free variables), so the census row is
native_decide-certified via the IR evaluator: milliseconds, bounded
memory. The receipt honestly shows `Lean.ofReduceBool` in the axiom set
(compiler-trust for closed literal goals — the standard, accepted
trade-off). Everything else in this module stays elaborator-decided. -/

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

/-! ## THE HEAVY ROW (isolated per the NO-OOM law; closed-goal
    native_decide per the S059 proof-route law — see header). -/

/-- Certified census (r=4, N=10^4): the 25 listed 4-powerful values. -/
theorem census_r4_members :
    [1, 16, 32, 64, 81, 128, 243, 256, 512, 625, 729, 1024, 1296, 2048, 2187, 2401, 2592,
     3125, 3888, 4096, 5184, 6561, 7776, 8192, 10000].all (fun n => rpow 4 n) = true := by
  native_decide

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

/-! ## The W63-B1 zero-box anchor rows (10^7, native_decide scale)

`LIST4P7` is the exhaustive 4-powerful list below 10^7 (234 values,
python-certified TWO WAYS in W63-B1: the DFS enumerator `gen4` — which
reproduces the K60 census row at 10^4 exactly — and an INDEPENDENT numpy
rad-sieve computing rad(n) for every n <= 10^7 with the rad^4 | n test; the two
constructions agree element-by-element at 10^7 — validate939_output.txt,
STATUS_W63.md). The two rows below are then CLOSED native_decide goals
(S059 proof-route law): no two COPRIME members of the list sum back into the
list, and no member's successor is a member (the a = 1 lane). Together with
the completeness certificate this is: NO pairwise-coprime triple of
4-powerful numbers a + b = c with c <= 10^7 — the 10^7 anchor of the W63-B1
box frontier (python-certified zero through 10^19; see STATUS_W63.md). -/

/-- Boolean membership in a literal list (structural fold; verbatim pattern
    from Erdos939.lean — this module is standalone by the NO-OOM law). -/
def memNat : Nat → List Nat → Bool
  | _, [] => false
  | n, v :: vs => decide (n = v) || memNat n vs

/-- The exhaustive 4-powerful list below 10^7 (234 values; python dual-method
    certificate: DFS enumerator == independent rad-sieve at 10^7). -/
def LIST4P7 : List Nat :=
[  16, 32, 64, 81, 128, 243, 256, 512, 625, 729,
  1024, 1296, 2048, 2187, 2401, 2592, 3125, 3888, 4096, 5184,
  6561, 7776, 8192, 10000, 10368, 11664, 14641, 15552, 15625, 16384,
  16807, 19683, 20000, 20736, 23328, 28561, 31104, 32768, 34992, 38416,
  40000, 41472, 46656, 50000, 50625, 59049, 62208, 65536, 69984, 76832,
  78125, 80000, 82944, 83521, 93312, 100000, 104976, 117649, 124416, 130321,
  131072, 139968, 151875, 153664, 160000, 161051, 165888, 177147, 186624, 194481,
  200000, 209952, 234256, 248832, 250000, 253125, 262144, 268912, 279841, 279936,
  307328, 314928, 320000, 331776, 371293, 373248, 390625, 400000, 419904, 455625,
  456976, 468512, 497664, 500000, 524288, 531441, 537824, 559872, 583443, 614656,
  629856, 640000, 663552, 707281, 746496, 759375, 800000, 810000, 823543, 839808,
  913952, 923521, 937024, 944784, 995328, 1000000, 1048576, 1075648, 1119744, 1185921,
  1229312, 1250000, 1259712, 1265625, 1280000, 1327104, 1336336, 1361367, 1366875, 1419857,
  1492992, 1500625, 1594323, 1600000, 1620000, 1679616, 1750329, 1771561, 1827904, 1874048,
  1874161, 1882384, 1889568, 1953125, 1990656, 2000000, 2085136, 2097152, 2151296, 2239488,
  2278125, 2313441, 2430000, 2458624, 2476099, 2500000, 2519424, 2560000, 2576816, 2654208,
  2672672, 2825761, 2834352, 2985984, 3111696, 3200000, 3240000, 3359232, 3418801, 3557763,
  3655808, 3748096, 3764768, 3779136, 3796875, 3981312, 4000000, 4050000, 4084101, 4100625,
  4170272, 4194304, 4302592, 4477456, 4478976, 4782969, 4826809, 4860000, 4879681, 4917248,
  5000000, 5038848, 5120000, 5153632, 5250987, 5308416, 5345344, 5668704, 5764801, 5940688,
  5971968, 6223392, 6250000, 6328125, 6400000, 6436343, 6480000, 6718464, 6765201, 6834375,
  6940323, 7290000, 7311616, 7496192, 7503125, 7529536, 7558272, 7890481, 7962624, 8000000,
  8100000, 8340544, 8388608, 8503056, 8605184, 8954912, 8957952, 9150625, 9335088, 9529569,
  9720000, 9765625, 9834496, 10000000]

/-- Certified zero-box (r=4, c <= 10^7, pair lane): NO two coprime members of
    the exhaustive 4-powerful list below 10^7 sum to another member. (Every
    pairwise-coprime 4-powerful triple a + b = c with c <= 10^7 would appear
    here — a, b < c <= 10^7 and all three in LIST4P7 by the completeness
    certificate.) -/
theorem box939_r4_1e7_pairs :
    LIST4P7.all (fun a => LIST4P7.all (fun b =>
      !(decide (Nat.gcd a b = 1) && memNat (a + b) LIST4P7))) = true := by
  native_decide

/-- Certified zero-box (r=4, c <= 10^7, successor lane): NO member of the
    exhaustive 4-powerful list below 10^7 has its successor in the list (the
    a = 1 lane: 1 is vacuously 4-powerful per `rpow 4 1 = true`). -/
theorem box939_r4_1e7_succ :
    LIST4P7.all (fun a => !(memNat (a + 1) LIST4P7)) = true := by
  native_decide

end E939R4

/-! ## Receipts -/

#print axioms E939R4.census_r4_members
#print axioms E939R4.no_small_solution_r4
#print axioms E939R4.board939_r4
#print axioms E939R4.box939_r4_1e7_pairs
#print axioms E939R4.box939_r4_1e7_succ
#eval "E939R4_CENSUS_GREEN"
