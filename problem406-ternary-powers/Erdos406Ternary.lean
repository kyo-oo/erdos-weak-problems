import Arsenal.ErdosTernary2.Basic
import Arsenal.CardinalWorlds
import Arsenal.CardinalWorldsV2

-- Family pattern (green kernels, K30/K36/K37 chains): explicit depth headroom.
set_option maxRecDepth 262144
set_option maxHeartbeats 4000000
-- 2^500 / 3^700 kernel evaluations (the NO-OOM legal cap; no bigger use)
set_option exponentiation.threshold 1000

/-!
# ERDŐS #406 — THE TERNARY CENSUS LAW (Kernel 38, S043 full-proof campaign;
board-complete extension S050-A3 — formalizes the COMPLETE_PROOF.md theorem
board: the census, the two general laws, the semantic law, the units-digit
refinement, the digit-count floor, and the standing constraints)

## THE PROBLEM (verbatim, erdosproblems.com/406 — BOSS's own front, admitted
to the army by the S042 full-proof-campaign order)

> Is it true that there are only finitely many powers of $2$ which have only
> the digits $0$ and $1$ when written in base $3$?

Corpus addendum: "The only examples seem to be $1$, $4=1+3$, and
$256=1+3+9+243$."

## WHAT THIS KERNEL PROVES (statement first, proofs below — the NEW RULE)

Reading: a power of 2 "has only the digits 0 and 1 in base 3" iff it is a
sum of DISTINCT powers of 3 (the 0/1 ternary digit condition), formalized
as `2 ^ k = tfold b` for a Bool list `b` (each `true` = the digit 1 at that
position, head = least significant). Board reference: COMPLETE_PROOF.md —
the complete-proof document whose theorem board this kernel formalizes
(the section headers below cite the doc's §-numbers; the doc's Lemma A2 /
Corollary A1 are the two semantic-law directions already formalized as
`tfold_of_tern01` / `tern01_of_tfold`).

1. **THE MOD-3 PARITY LAW** (`erdos406_odd_excluded`, GENERAL — every odd
   exponent, no bound): NO odd power of 2 is a sum of distinct powers of 3.
   Proof: a 0/1-digit ternary number is ≡ 0 or 1 (mod 3), but 2^(2j+1) ≡ 2.
   Unconditionally excludes an infinite class of exponents.
2. **THE MOD-8 BUDGET LAW** (`erdos406_mod8_budget`, GENERAL — every k ≥ 3):
   if 2^k = tfold b with k ≥ 3 then (E + 3·O) ≡ 0 (mod 8), where E = the
   count of 1-digits at even ternary positions, O = at odd positions
   (`tfold b % 8 = (E + 3O) % 8`, and 2^k ≡ 0 mod 8). On the witness 256:
   E = O = 2, 2 + 3·2 = 8 ≡ 0.
3. **THE SEMANTIC LAW** (`tern01_iff_tfold`): the fuel-indexed digit
   checker `tern01` is EXACTLY the representation predicate: for n < 3^f,
   `tern01 f n = true ↔ ∃ b, n = tfold b` (the forward direction uses the
   Arsenal's `lt_three_cases` trichotomy on the ternary digit).
4. **THE CENSUS** (`erdos406_census`, kernel-decided in the 480-discipline
   chunks 480 + 21): for EVERY k < 501,
   `tern01 700 (2^k) = true ↔ k ∈ {0, 2, 8}`.
5. **THE MAIN THEOREM** (`erdos406_main`): for every k ≤ 500:
   2^k is a sum of distinct powers of 3 ↔ k ∈ {0, 2, 8}; the three
   positive witnesses explicit: 1 = tfold [true], 4 = tfold [true, true],
   256 = tfold [true, true, true, false, false, true].
6. **THE ARSENAL BRIDGE** (`erdos406_arsenal_bridge`): erdosternary2's
   `isTernaryDigit` on the ternary digits of the witnesses + HC-PROOF's
   `carryAtPos_bound` + `v2r_ternary_scaling` at the witness pair (8, 256).
7. **THE UNITS-DIGIT REFINEMENT** (`erdos406_units_digit_one`, doc §4
   "Sharpness and refinement"): every solution, at any size, ends its
   ternary expansion with the digit 1 — the units digit ε_0 is exactly 1
   (b = true :: b').
8. **THE DIGIT-COUNT FLOOR** (doc §5, Corollary C3): `erdos406_digit_floor`
   (D = E + O ≥ 4 — every k ≥ 3 solution has at least 4 nonzero ternary
   digits), `erdos406_min_profile` (D = 4 exactly on the 256 profile
   (E, O) = (2, 2)), `erdos406_six_floor` (D ≥ 6 whenever E + 3O ≥ 16).
9. **THE STANDING CONSTRAINTS** (`erdos406_standing_constraints`, doc §7):
   every hypothetical large solution (2^k = tfold b with k > 500, beyond
   the certified census range) satisfies ALL of: even k, units digit 1,
   the mod-8 budget with its floors; `erdos406_complete_structure` (§6+§7):
   every solution is either a census witness (k ∈ {0, 2, 8}) or a
   fully-constrained hypothetical large solution — the complete
   unconditional structure short of the open all-k finiteness core.

Honest scope: the census settles k ≤ 500 unconditionally; the general
finiteness question (all k) remains the open core, with the general laws
(odd exclusion, units digit, mod-8 budget, digit floors) as the standing
structural constraints every hypothetical large solution must satisfy. -/

namespace Erdos406T

/-! ## §0 The definitions. -/

/-- The value of a 0/1 ternary digit list (head = least significant digit):
`tfold b = Σ_i (digit_i)·3^i` with each digit 0 or 1. -/
def tfold (b : List Bool) : Nat :=
  b.foldr (fun d acc => 3 * acc + cond d 1 0) 0

/-- The fuel-indexed ternary 0/1-digit checker: true iff every base-3
digit of n is ≤ 1, given enough fuel (fuel 0 short-circuits true; the
semantic law §2 makes the reading exact for n < 3^fuel). -/
def tern01 : Nat → Nat → Bool
  | 0, _ => true
  | f + 1, n => n == 0 || (decide (n % 3 ≤ 1) && tern01 f (n / 3))

/-- The even/odd position 1-digit counts of a 0/1 ternary digit list
(head = position 0 = even; the tail's parities flip). -/
def altsum : List Bool → Nat × Nat
  | [] => (0, 0)
  | d :: b' => ((altsum b').2 + cond d 1 0, (altsum b').1)

/-! ## §1 Canonical step lemmas (the green-kernel discipline). -/

theorem tfold_nil : tfold [] = 0 := rfl

theorem tfold_cons (d : Bool) (b : List Bool) :
    tfold (d :: b) = 3 * tfold b + cond d 1 0 := rfl

theorem altsum_cons_fst (d : Bool) (b : List Bool) :
    (altsum (d :: b)).1 = (altsum b).2 + cond d 1 0 := rfl

theorem altsum_cons_snd (d : Bool) (b : List Bool) :
    (altsum (d :: b)).2 = (altsum b).1 := rfl

theorem altsum_nil_fst : (altsum []).1 = 0 := rfl
theorem altsum_nil_snd : (altsum []).2 = 0 := rfl

theorem tern01_zero (f : Nat) : tern01 f 0 = true := by
  cases f <;> rfl

theorem tern01_succ (f n : Nat) :
    tern01 (f + 1) n = (n == 0 || (decide (n % 3 ≤ 1) && tern01 f (n / 3))) := rfl

/-- The digit bound on `cond` (kernel receipts both cases). -/
theorem cond_le_one (d : Bool) : cond d 1 0 ≤ 1 := by cases d <;> decide

/-! ## §2 The semantic law: tern01 ⟺ sum of distinct powers of 3. -/

/-- Forward: the checker certifies a fold-representation. -/
theorem tfold_of_tern01 : ∀ (f n : Nat), n < 3 ^ f → tern01 f n = true →
    ∃ b : List Bool, n = tfold b := by
  intro f
  induction f with
  | zero =>
    intro n hn _
    have h0 : n = 0 := by omega
    subst h0
    exact ⟨[], tfold_nil.symm⟩
  | succ f' ih =>
    intro n hn hval
    by_cases h0 : n = 0
    · subst h0
      exact ⟨[], tfold_nil.symm⟩
    · rw [tern01_succ, Bool.or_eq_true] at hval
      rcases hval with hbeq | hval
      · have hn0 : n = 0 := by simpa using hbeq
        exact absurd hn0 h0
      · rw [Bool.and_eq_true] at hval
        obtain ⟨hdig, hrec⟩ := hval
        have hmod : n % 3 ≤ 1 := of_decide_eq_true hdig
        rw [Nat.pow_succ] at hn
        have hdiv : n / 3 < 3 ^ f' := by omega
        obtain ⟨b', hb'⟩ := ih (n / 3) hdiv hrec
        have h3 : n % 3 < 3 := by omega
        -- THE ARSENAL TRICHOTOMY on the ternary digit (n % 3)
        rcases ErdosTernary2.lt_three_cases (n % 3) h3 with h | h | h
        · refine ⟨false :: b', ?_⟩
          rw [tfold_cons, ← hb']
          have hc : cond false 1 0 = 0 := rfl
          rw [hc]
          omega
        · refine ⟨true :: b', ?_⟩
          rw [tfold_cons, ← hb']
          have hc : cond true 1 0 = 1 := rfl
          rw [hc]
          omega
        · exfalso
          omega

/-- Backward: a fold-representation passes the checker. -/
theorem tern01_of_tfold : ∀ (b : List Bool) (f : Nat), tfold b < 3 ^ f →
    tern01 f (tfold b) = true := by
  intro b
  induction b with
  | nil => intro f _; exact tern01_zero f
  | cons d b' ih =>
    intro f hf
    cases f with
    | zero => rfl
    | succ f' =>
      by_cases h0 : 3 * tfold b' + cond d 1 0 = 0
      · rw [tfold_cons, h0, tern01_succ]
        rfl
      · rw [tfold_cons, tern01_succ, Bool.or_eq_true, Bool.and_eq_true]
        refine Or.inr ⟨?_, ?_⟩
        · have hc := cond_le_one d
          have hsplit : (3 * tfold b' + cond d 1 0) % 3 = cond d 1 0 := by omega
          rw [hsplit]
          cases d <;> rfl
        · have hc := cond_le_one d
          have hdiv : (3 * tfold b' + cond d 1 0) / 3 = tfold b' := by omega
          rw [hdiv]
          rw [tfold_cons, Nat.pow_succ] at hf
          have hf' : tfold b' < 3 ^ f' := by omega
          exact ih f' hf'

/-- **THE SEMANTIC LAW**: the checker is exactly the representation
predicate (n a sum of distinct powers of 3). -/
theorem tern01_iff_tfold (f n : Nat) (hn : n < 3 ^ f) :
    (tern01 f n = true ↔ ∃ b : List Bool, n = tfold b) :=
  ⟨tfold_of_tern01 f n hn, fun ⟨b, hb⟩ => by subst hb; exact tern01_of_tfold b f hn⟩

/-! ## §3 THE MOD-3 PARITY LAW: every odd exponent is excluded. -/

theorem tfold_mod3_le_one : ∀ b : List Bool, tfold b % 3 ≤ 1 := by
  intro b
  induction b with
  | nil => simp [tfold]
  | cons d b' _ =>
    rw [tfold_cons]
    have hc := cond_le_one d
    omega

theorem pow4_mod3 : ∀ j : Nat, 4 ^ j % 3 = 1 := by
  intro j
  induction j with
  | zero => rfl
  | succ j' ihj =>
    have hp : 4 ^ (j' + 1) = 4 * 4 ^ j' := by
      rw [Nat.pow_succ]
      ring
    omega

theorem pow2_odd_mod3 : ∀ j : Nat, 2 ^ (2 * j + 1) % 3 = 2 := by
  intro j
  have h1 : 2 ^ (2 * j + 1) = 2 * 4 ^ j := by
    rw [Nat.pow_succ, Nat.pow_mul]
    ring
  have h2 := pow4_mod3 j
  omega

/-- **THE MOD-3 PARITY LAW** — no odd power of 2 is a sum of distinct
powers of 3 (unconditional, every exponent). -/
theorem erdos406_odd_excluded : ∀ j : Nat, ¬ ∃ b : List Bool, 2 ^ (2 * j + 1) = tfold b := by
  intro j ⟨b, hb⟩
  have h1 := tfold_mod3_le_one b
  have h2 := pow2_odd_mod3 j
  rw [hb] at h2
  omega

/-! ## §3b The units-digit refinement (COMPLETE_PROOF.md §4, "Sharpness and
refinement"): every solution, at any size, ends its ternary expansion with
the digit 1. -/

/-- No power of 2 is divisible by 3 (the doc's 2^k ≡ (-1)^k (mod 3) route:
2^k % 3 ∈ {1, 2} for every k). -/
theorem pow2_mod3_ne_zero : ∀ k : Nat, 2 ^ k % 3 ≠ 0 := by
  intro k
  induction k with
  | zero => decide
  | succ k' ih =>
    have hmul : 2 ^ (k' + 1) = 2 * 2 ^ k' := by rw [Nat.pow_succ]
    omega

/-- The even-exponent residue (doc §4: for even k, 2^k ≡ 1 (mod 3)). -/
theorem pow2_even_mod3 : ∀ j : Nat, 2 ^ (2 * j) % 3 = 1 := by
  intro j
  have h : 2 ^ (2 * j) = 4 ^ j := by
    rw [Nat.pow_mul]
    ring
  have h2 := pow4_mod3 j
  omega

/-- **THE UNITS-DIGIT REFINEMENT** (doc §4): every solution 2^k = tfold b,
at any size, ends its ternary expansion with the digit 1 — the units
ternary digit ε_0 is exactly 1 (b = true :: b'). -/
theorem erdos406_units_digit_one : ∀ (k : Nat) (b : List Bool), 2 ^ k = tfold b →
    ∃ b' : List Bool, b = true :: b' := by
  intro k b hb
  have hpos : 0 < 2 ^ k := Nat.pow_pos (by decide)
  cases b with
  | nil =>
    rw [tfold_nil] at hb
    exfalso
    omega
  | cons d b' =>
    cases d with
    | false =>
      rw [tfold_cons] at hb
      have hc : cond false 1 0 = 0 := rfl
      rw [hc] at hb
      exfalso
      have h1 := pow2_mod3_ne_zero k
      omega
    | true => exact ⟨b', rfl⟩

/-! ## §4 THE MOD-8 BUDGET LAW (k ≥ 3). -/

theorem tfold_mod8 : ∀ b : List Bool,
    tfold b % 8 = ((altsum b).1 + 3 * (altsum b).2) % 8 := by
  intro b
  induction b with
  | nil => rfl
  | cons d b' ih =>
    rw [tfold_cons, altsum_cons_fst, altsum_cons_snd]
    have hc := cond_le_one d
    omega

theorem pow2_mod8 : ∀ k : Nat, 3 ≤ k → 2 ^ k % 8 = 0 := by
  intro k hk
  obtain ⟨s, hs⟩ : ∃ s, k = s + 3 := ⟨k - 3, by omega⟩
  subst hs
  have hp : 2 ^ (s + 3) = 2 ^ s * 2 ^ 3 := by rw [Nat.pow_add]
  have h8 : (2 : Nat) ^ 3 = 8 := by rfl
  rw [hp, h8]
  omega

/-- **THE MOD-8 BUDGET LAW** — every k ≥ 3 solution satisfies the even/odd
digit-count budget (E + 3O) ≡ 0 (mod 8). -/
theorem erdos406_mod8_budget : ∀ (b : List Bool) (k : Nat), 3 ≤ k →
    2 ^ k = tfold b → ((altsum b).1 + 3 * (altsum b).2) % 8 = 0 := by
  intro b k hk hb
  have h1 := tfold_mod8 b
  have h2 := pow2_mod8 k hk
  rw [← hb] at h1
  omega

/-! ## §4b The digit-count floor (COMPLETE_PROOF.md §5, Corollary C3) — the
standing structural constraint every k ≥ 3 solution carries. -/

/-- If a 0/1-digit list has no 1-digits at all (E + O = 0), its fold value
is 0 (doc §5: "(E, O) ≠ (0,0): if all digits are 0 then tfold = 0 ≠ 2^k"). -/
theorem tfold_eq_zero_of_counts_zero : ∀ b : List Bool,
    (altsum b).1 + (altsum b).2 = 0 → tfold b = 0 := by
  intro b
  induction b with
  | nil => intro _; rfl
  | cons d b' ih =>
    intro h
    rw [altsum_cons_fst, altsum_cons_snd] at h
    rw [tfold_cons]
    have h' : (altsum b').1 + (altsum b').2 = 0 := by omega
    rw [ih h']
    omega

/-- **Corollary C3.1 — THE DIGIT-COUNT FLOOR**: every solution 2^k = tfold b
with k ≥ 3 has at least 4 nonzero ternary digits (D = E + O ≥ 4). -/
theorem erdos406_digit_floor : ∀ (b : List Bool) (k : Nat), 3 ≤ k → 2 ^ k = tfold b →
    4 ≤ (altsum b).1 + (altsum b).2 := by
  intro b k hk hb
  have hpos : 0 < 2 ^ k := Nat.pow_pos (by decide)
  have hne : (altsum b).1 + (altsum b).2 ≠ 0 := by
    intro h0
    have hz := tfold_eq_zero_of_counts_zero b h0
    omega
  have h1 := erdos406_mod8_budget b k hk hb
  omega

/-- **Corollary C3.2 — THE MINIMAL PROFILE**: for a k ≥ 3 solution, D = 4
exactly on the 256 profile (E, O) = (2, 2). -/
theorem erdos406_min_profile : ∀ (b : List Bool) (k : Nat), 3 ≤ k → 2 ^ k = tfold b →
    ((altsum b).1 + (altsum b).2 = 4 ↔
      ((altsum b).1 = 2 ∧ (altsum b).2 = 2)) := by
  intro b k hk hb
  have h1 := erdos406_mod8_budget b k hk hb
  constructor
  · intro h4
    have hE : (altsum b).1 = 2 := by omega
    have hO : (altsum b).2 = 2 := by omega
    exact ⟨hE, hO⟩
  · rintro ⟨hE, hO⟩
    omega

/-- **Corollary C3.3 — THE SIX-FLOOR**: a k ≥ 3 solution with a doubled
budget (E + 3O ≥ 16) has at least 6 nonzero ternary digits. -/
theorem erdos406_six_floor : ∀ (b : List Bool) (k : Nat), 3 ≤ k → 2 ^ k = tfold b →
    16 ≤ (altsum b).1 + 3 * (altsum b).2 → 6 ≤ (altsum b).1 + (altsum b).2 := by
  intro b k hk hb hS
  have h1 := erdos406_mod8_budget b k hk hb
  omega

/-! ## §5 THE CENSUS (kernel-decided, the 480-discipline chunks 480 + 21). -/

/-- The census checker for exponent k (Bool form: the checker rejects 2^k,
or k is one of the three witnesses). -/
def censusCheckB (k : Nat) : Bool :=
  (tern01 700 (2 ^ k) == false) || decide (k = 0 ∨ k = 2 ∨ k = 8)

theorem censusCheckB_iff (k : Nat) : censusCheckB k = true ↔
    (tern01 700 (2 ^ k) = false ∨ (k = 0 ∨ k = 2 ∨ k = 8)) := by
  unfold censusCheckB
  cases h : tern01 700 (2 ^ k) with
  | true => simp [h]
  | false => simp [h]

/-- Chunk 1: k ∈ [0, 480). -/
theorem census_chunk1 : (List.range 480).all censusCheckB = true := by decide

/-- Chunk 2: k ∈ [480, 501). -/
theorem census_chunk2 :
    (List.range 21).all (fun j => censusCheckB (480 + j)) = true := by decide

/-- **THE CENSUS** (the 480-discipline chunks 480 + 21): for every k ≤ 500,
the digit checker accepts 2^k only at k ∈ {0, 2, 8} (fuel 700 ≥ 316 = the
ternary length of 2^500). -/
theorem erdos406_census (k : Nat) (hk : k < 501) :
    tern01 700 (2 ^ k) = true → (k = 0 ∨ k = 2 ∨ k = 8) := by
  intro hval
  rcases (by omega : k < 480 ∨ 480 ≤ k) with h | h
  · have hc := (List.all_eq_true.mp census_chunk1) k (List.mem_range.mpr h)
    rcases (censusCheckB_iff k).mp hc with hneg | hmem
    · rw [hneg] at hval
      exact absurd hval (by decide)
    · exact hmem
  · have hmem : k - 480 ∈ List.range 21 := List.mem_range.mpr (by omega)
    have h1 := (List.all_eq_true.mp census_chunk2) (k - 480) hmem
    rw [Nat.add_sub_cancel' h] at h1
    rcases (censusCheckB_iff k).mp h1 with hneg | hmem2
    · rw [hneg] at hval
      exact absurd hval (by decide)
    · exact hmem2

theorem two_pow_500_lt : 2 ^ 500 < 3 ^ 700 := by decide

/-! ## §6 THE MAIN THEOREM. -/

/-- **THE MAIN THEOREM**: below 2^500, the powers of 2 that are sums of
distinct powers of 3 (0/1 ternary digits) are EXACTLY 1, 4, 256. -/
theorem erdos406_main : ∀ k ≤ 500,
    ((∃ b : List Bool, 2 ^ k = tfold b) ↔ (k = 0 ∨ k = 2 ∨ k = 8)) := by
  intro k hk
  constructor
  · intro ⟨b, hb⟩
    have hs : 2 ^ 500 = 2 ^ k * 2 ^ (500 - k) := by
      rw [← Nat.pow_add]
      congr 1
      omega
    have hp : 0 < 2 ^ (500 - k) := Nat.pow_pos (by decide)
    have hle : 2 ^ k ≤ 2 ^ 500 := by
      rw [hs]
      calc 2 ^ k = 2 ^ k * 1 := by ring
        _ ≤ 2 ^ k * 2 ^ (500 - k) := Nat.mul_le_mul_left _ (by omega)
    have hlt : 2 ^ 500 < 3 ^ 700 := two_pow_500_lt
    have hb3 : tfold b < 3 ^ 700 := by omega
    have h4 : tern01 700 (tfold b) = true := tern01_of_tfold b 700 hb3
    rw [← hb] at h4
    exact erdos406_census k (by omega) h4
  · rintro (rfl | rfl | rfl)
    · exact ⟨[true], by rfl⟩
    · exact ⟨[true, true], by rfl⟩
    · exact ⟨[true, true, true, false, false, true], by rfl⟩

/-! ## §6b THE STANDING CONSTRAINTS on every hypothetical large solution
(COMPLETE_PROOF.md §7 — the open-core boundary): a hypothetical large
solution is a pair (b, k) with 2^k = tfold b and k > 500, beyond the
certified census range. -/

/-- Every solution exponent is even — Theorem B read off a solution
(the doc §7 constraint 1). -/
theorem erdos406_solution_even : ∀ (k : Nat) (b : List Bool), 2 ^ k = tfold b →
    ∃ j : Nat, k = 2 * j := by
  intro k b hb
  have hme : k % 2 = 0 ∨ k % 2 = 1 := by omega
  rcases hme with h0 | h1
  · exact ⟨k / 2, by omega⟩
  · exfalso
    have hk : k = 2 * (k / 2) + 1 := by omega
    rw [hk] at hb
    exact erdos406_odd_excluded (k / 2) ⟨b, hb⟩

/-- **THE STANDING CONSTRAINTS** (doc §7): every hypothetical large solution
(b, k) — 2^k = tfold b with k > 500 — satisfies ALL of the doc's
unconditional constraints simultaneously: (1) k is even; (2) the units
ternary digit is exactly ε_0 = 1; (3) the mod-8 budget E + 3O ≡ 0 (mod 8)
with the digit floors D ≥ 4, the D = 4 → (E, O) = (2, 2) minimal profile,
and D ≥ 6 at doubled budget E + 3O ≥ 16. (Constraint 4 — the census
boundary k > 500 — is the defining hypothesis: erdos406_main has already
classified every exponent ≤ 500.) -/
theorem erdos406_standing_constraints : ∀ (b : List Bool) (k : Nat),
    500 < k → 2 ^ k = tfold b →
    (∃ j : Nat, k = 2 * j) ∧
    (∃ b' : List Bool, b = true :: b') ∧
    ((altsum b).1 + 3 * (altsum b).2) % 8 = 0 ∧
    4 ≤ (altsum b).1 + (altsum b).2 ∧
    ((altsum b).1 + (altsum b).2 = 4 → (altsum b).1 = 2 ∧ (altsum b).2 = 2) ∧
    (16 ≤ (altsum b).1 + 3 * (altsum b).2 → 6 ≤ (altsum b).1 + (altsum b).2) := by
  intro b k hlarge hsol
  have hk3 : 3 ≤ k := by omega
  exact ⟨erdos406_solution_even k b hsol, erdos406_units_digit_one k b hsol,
    erdos406_mod8_budget b k hk3 hsol, erdos406_digit_floor b k hk3 hsol,
    (erdos406_min_profile b k hk3 hsol).mp, erdos406_six_floor b k hk3 hsol⟩

/-- **THE COMPLETE STRUCTURE THEOREM** (doc §6 + §7 — the assembly's close):
every solution 2^k = tfold b is either one of the three census witnesses
(k ∈ {0, 2, 8} — the complete below-2^500 classification, Theorem E) or a
hypothetical large solution (k > 500) carrying the full standing
constraint set — the complete unconditional structure delivered short of
the open all-k finiteness core (the doc's §7 open-core boundary). -/
theorem erdos406_complete_structure : ∀ (b : List Bool) (k : Nat), 2 ^ k = tfold b →
    (k = 0 ∨ k = 2 ∨ k = 8) ∨
    (500 < k ∧
      (∃ j : Nat, k = 2 * j) ∧
      (∃ b' : List Bool, b = true :: b') ∧
      ((altsum b).1 + 3 * (altsum b).2) % 8 = 0 ∧
      4 ≤ (altsum b).1 + (altsum b).2 ∧
      ((altsum b).1 + (altsum b).2 = 4 → (altsum b).1 = 2 ∧ (altsum b).2 = 2) ∧
      (16 ≤ (altsum b).1 + 3 * (altsum b).2 → 6 ≤ (altsum b).1 + (altsum b).2)) := by
  intro b k hsol
  rcases (by omega : k ≤ 500 ∨ 500 < k) with hle | hgt
  · exact Or.inl ((erdos406_main k hle).mp ⟨b, hsol⟩)
  · have hc := erdos406_standing_constraints b k hgt hsol
    exact Or.inr ⟨hgt, hc.1, hc.2.1, hc.2.2.1, hc.2.2.2.1, hc.2.2.2.2.1, hc.2.2.2.2.2⟩

/-! ## §7 THE ARSENAL BRIDGE (BOSS's mathematics applied to the witness
numbers — erdosternary2 + HC-PROOF, the 16,121-theorem arsenal). -/

def arsenalBridgeProp : Prop :=
  [256 % 3, (256 / 3) % 3, (256 / 9) % 3, (256 / 27) % 3,
   (256 / 81) % 3, (256 / 243) % 3].all
    (fun d => ErdosTernary2.isTernaryDigit d) ∧
  [1 % 3, (1 / 3) % 3, (4 / 3) % 3].all (fun d => ErdosTernary2.isTernaryDigit d) ∧
  carryAtPos 256 1 < 4 ∧
  v2r (3 ^ 8 * 256) = v2r 256

theorem erdos406_arsenal_bridge : arsenalBridgeProp :=
  ⟨by decide, by decide, carryAtPos_bound 256 1, CardinalWorldsV2.v2r_ternary_scaling 8 256⟩

/-! ## §8 Receipts (kernel-decided instances + axiom audits). -/

/-- The three witnesses as fold-representations (kernel receipts). -/
theorem witness_one : 2 ^ 0 = tfold [true] := rfl
theorem witness_four : 2 ^ 2 = tfold [true, true] := rfl
theorem witness_256 : 2 ^ 8 = tfold [true, true, true, false, false, true] := rfl

/-- The mod-8 budget on the 256 witness: E = 2, O = 2, 2 + 3·2 = 8 ≡ 0. -/
theorem witness_256_budget : ((altsum [true, true, true, false, false, true]).1 +
    3 * (altsum [true, true, true, false, false, true]).2) % 8 = 0 :=
  erdos406_mod8_budget [true, true, true, false, false, true] 8 (by omega) witness_256

/-- The 256 receipt for Corollary C3 (doc §5): the minimal profile
(E, O) = (2, 2) with D = E + O = 4 — the budget's minimal profile,
attained at the largest known solution, exactly as C3 predicts. -/
theorem witness_256_min_profile :
    (altsum [true, true, true, false, false, true]).1 = 2 ∧
    (altsum [true, true, true, false, false, true]).2 = 2 ∧
    (altsum [true, true, true, false, false, true]).1 +
      (altsum [true, true, true, false, false, true]).2 = 4 := by decide

/-- The first excluded even exponents (kernel receipts of the census). -/
theorem census_receipts :
    (tern01 700 (2 ^ 4) = false ∧ tern01 700 (2 ^ 10) = false ∧
     tern01 700 (2 ^ 100) = false ∧ tern01 700 (2 ^ 500) = false) := by decide

#eval (tfold [true], tfold [true, true],
       tfold [true, true, true, false, false, true], 2 ^ 8)
#eval (tern01 700 (2 ^ 4), tern01 700 (2 ^ 8), tern01 700 (2 ^ 256))
#eval ((altsum [true, true, true, false, false, true]).1,
       (altsum [true, true, true, false, false, true]).2)

#print axioms erdos406_odd_excluded
#print axioms erdos406_mod8_budget
#print axioms tern01_iff_tfold
#print axioms erdos406_census
#print axioms erdos406_main
#print axioms erdos406_arsenal_bridge
#print axioms pow2_mod3_ne_zero
#print axioms pow2_even_mod3
#print axioms erdos406_units_digit_one
#print axioms tfold_eq_zero_of_counts_zero
#print axioms erdos406_digit_floor
#print axioms erdos406_min_profile
#print axioms erdos406_six_floor
#print axioms erdos406_solution_even
#print axioms erdos406_standing_constraints
#print axioms erdos406_complete_structure

#eval "ERDOS406_TERNARY_KERNEL_GREEN"
#eval "ERDOS406_COMPLETE_PROOF_BOARD_GREEN"

end Erdos406T
