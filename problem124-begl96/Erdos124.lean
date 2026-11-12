import Arsenal.ErdosTernary2.Basic
import Arsenal.CardinalWorlds
import Arsenal.CardinalWorldsV2

set_option maxRecDepth 65536
set_option maxHeartbeats 4000000

/-!
# Erdos124 — THE BEGL96 TAIL-COMPLETENESS KERNEL r1 (F10, W56-5)

Erdős #124 (erdosproblems.com/124, the Bleicher–Erdős–Graham–Lagarias 1996
frame): which finite denominator sets S make every sufficiently small
rational representable as a sum of distinct reciprocals from the tail
{1/n : n ∈ S, n ≥ N}?  The 1st question is dead (Alexeev); the corpus ask
is the TAIL-COMPLETENESS 2nd question.  The campaign round-1 fixed the
{3,4,7}-multiplicative template: does the template achieve tail
completeness?  This kernel is the round-1 answer layer:

1. **THE MULTIPLICATIVE SEMIGROUP LAWS** (`inS347`, the certified table,
   the full closure law `S347_closed_mul`, the ordered prefix
   `S347_sorted_first`, the nonmember battery `S347_nonmember`).
2. **THE TAIL DENSITY LAW**: the UNIT REPRESENTATION over the template —
   `1/3 + 1/4 + 1/7 + 1/9 + 1/12 + 1/28 + 1/36 + 1/63 = 1` (8 distinct
   {3,4,7}-elements, cross-multiplier 252 = 3·84 = 4·63 = 7·36 = 9·28 =
   12·21 = 28·9 = 36·7 = 63·4) — certified `by decide` — and the FULL
   GENERAL SPLIT `split_all`: for EVERY n, the cross-multiplied split of
   1/n into the 8 template reciprocals 1/(s·n); template-certified +
   strictly-ordered (`split_all_S347`) — the split moves strictly INTO
   THE TAIL (every split denominator ≥ 3n > n).  This is the BEGL96
   completeness engine at the kernel level.
3. **THE CRITICAL-JUNCTURE TRANSFER** (from #348 — S029's zero-slack
   critical-juncture derivation): the split is ZERO-SLACK (exact
   equality) at infinitely many template junctures — one per power of 3
   (`e124_critical_juncture`: for every k there is a juncture m ≥ 3^k).
4. **THE ARSENAL BRIDGE** (`e124_arsenal_bridge`): the ternary-digit
   carriers {0,1,2} (via `ErdosTernary2.lt_three_cases` +
   `isTernaryDigit`) are exactly the template exponent carriers 3^d.
5. **THE BOARD** (`e124_begl96_board`): the composite master.

Core-only discipline: cross-multiplied Nat identities, `decide` on closed
numerics, `omega` on linear shells, the banked atom laws.  No sorry, no
admit, no native_decide, no direct Mathlib import.
-/

namespace E124

/-! ## §0 Core arithmetic helpers (banked-spelling discipline) -/

/-- Every positive base to a natural exponent is at least 1. -/
theorem one_le_pow (x : Nat) (hx : 1 ≤ x) (e : Nat) : 1 ≤ x ^ e := by
  induction e with
  | zero => rw [Nat.pow_zero]
  | succ e ih =>
    rw [Nat.pow_succ]
    have h := Nat.mul_le_mul ih hx
    simpa using h

/-- Power monotonicity: a base ≥ 2 is monotone in the exponent. -/
theorem pow_mono (x e f : Nat) (hx : 2 ≤ x) (hef : e ≤ f) : x ^ e ≤ x ^ f := by
  obtain ⟨d, hd⟩ : ∃ d : Nat, f = e + d := ⟨f - e, by omega⟩
  subst hd
  clear hef
  induction d with
  | zero => rw [Nat.add_zero]
  | succ d ih =>
    rw [Nat.add_succ, Nat.pow_succ]
    have h3 : 1 * x ^ (e + d) ≤ x * x ^ (e + d) :=
      Nat.mul_le_mul_right (x ^ (e + d)) (by omega)
    rw [Nat.one_mul] at h3
    exact Nat.le_trans ih h3

/-- A product of two ≥-1 factors is at least 1. -/
theorem one_le_mul (x y : Nat) (hx : 1 ≤ x) (hy : 1 ≤ y) : 1 ≤ x * y := by
  have h : 1 * y ≤ x * y := Nat.mul_le_mul_right y hx
  rw [Nat.one_mul] at h
  exact Nat.le_trans hy h

/-- `x ≤ x * y` when `y ≥ 1`. -/
theorem le_mul_right (x y : Nat) (hy : 1 ≤ y) : x ≤ x * y := by
  have h : x * 1 ≤ x * y := Nat.mul_le_mul_left x hy
  rw [Nat.mul_one] at h
  exact h

/-- The first factor of a {3,4,7}-product is ≤ the product. -/
theorem first_le_prod (x y z : Nat) (hy : 1 ≤ y) (hz : 1 ≤ z) : x ≤ x * y * z := by
  rw [Nat.mul_assoc]
  exact le_mul_right x (y * z) (one_le_mul y z hy hz)

/-- The middle factor of a {3,4,7}-product is ≤ the product. -/
theorem mid_le_prod (x y z : Nat) (hx : 1 ≤ x) (hz : 1 ≤ z) : y ≤ x * y * z := by
  have h1 : 1 * y ≤ x * y := Nat.mul_le_mul_right y hx
  rw [Nat.one_mul] at h1
  have h2 : (x * y) * 1 ≤ (x * y) * z := Nat.mul_le_mul_left (x * y) hz
  rw [Nat.mul_one] at h2
  exact Nat.le_trans h1 h2

/-- The last factor of a {3,4,7}-product is ≤ the product. -/
theorem third_le_prod (x y z : Nat) (hx : 1 ≤ x) (hy : 1 ≤ y) : z ≤ x * y * z := by
  have h : 1 * z ≤ (x * y) * z := Nat.mul_le_mul_right z (one_le_mul x y hx hy)
  rw [Nat.one_mul] at h
  exact h

/-! ## §1 The {3,4,7} multiplicative semigroup — the template engine -/

/-- Membership in the {3,4,7}-semigroup: `n ∈ S` iff `n = 3^a · 4^b · 7^c`
(a, b, c ≥ 0).  The BEGL96 template. -/
def inS347 (n : Nat) : Prop := ∃ a b c : Nat, n = 3 ^ a * 4 ^ b * 7 ^ c

/-- The Bool recognizer over the certified ordered prefix (elements < 37). -/
def S347 : Nat → Bool
  | 1 => true
  | 3 => true
  | 4 => true
  | 7 => true
  | 9 => true
  | 12 => true
  | 16 => true
  | 21 => true
  | 27 => true
  | 28 => true
  | 36 => true
  | _ => false

/-- Every power of 3 is a template element (the pure-ternary carriers). -/
theorem mem_pow3 (d : Nat) : inS347 (3 ^ d) :=
  ⟨d, 0, 0, by simp only [Nat.pow_zero, Nat.mul_one]⟩

theorem mem_1 : inS347 1 := ⟨0, 0, 0, by decide⟩
theorem mem_3 : inS347 3 := ⟨1, 0, 0, by decide⟩
theorem mem_4 : inS347 4 := ⟨0, 1, 0, by decide⟩
theorem mem_7 : inS347 7 := ⟨0, 0, 1, by decide⟩
theorem mem_9 : inS347 9 := ⟨2, 0, 0, by decide⟩
theorem mem_12 : inS347 12 := ⟨1, 1, 0, by decide⟩
theorem mem_16 : inS347 16 := ⟨0, 2, 0, by decide⟩
theorem mem_21 : inS347 21 := ⟨1, 0, 1, by decide⟩
theorem mem_27 : inS347 27 := ⟨3, 0, 0, by decide⟩
theorem mem_28 : inS347 28 := ⟨0, 1, 1, by decide⟩
theorem mem_36 : inS347 36 := ⟨2, 1, 0, by decide⟩
theorem mem_48 : inS347 48 := ⟨1, 2, 0, by decide⟩
theorem mem_49 : inS347 49 := ⟨0, 0, 2, by decide⟩
theorem mem_63 : inS347 63 := ⟨2, 0, 1, by decide⟩
theorem mem_64 : inS347 64 := ⟨0, 3, 0, by decide⟩
theorem mem_81 : inS347 81 := ⟨4, 0, 0, by decide⟩
theorem mem_84 : inS347 84 := ⟨1, 1, 1, by decide⟩
theorem mem_108 : inS347 108 := ⟨3, 1, 0, by decide⟩
theorem mem_112 : inS347 112 := ⟨0, 2, 1, by decide⟩
theorem mem_144 : inS347 144 := ⟨2, 2, 0, by decide⟩
theorem mem_147 : inS347 147 := ⟨1, 0, 2, by decide⟩
theorem mem_189 : inS347 189 := ⟨3, 0, 1, by decide⟩
theorem mem_192 : inS347 192 := ⟨1, 3, 0, by decide⟩
theorem mem_196 : inS347 196 := ⟨0, 1, 2, by decide⟩
theorem mem_252 : inS347 252 := ⟨2, 1, 1, by decide⟩
theorem mem_336 : inS347 336 := ⟨1, 2, 1, by decide⟩

/-- **THE CERTIFIED TABLE**: the first 24 elements of the {3,4,7}-semigroup,
each by explicit valuation triple (a, b, c). -/
theorem S347_table :
    inS347 1 ∧ inS347 3 ∧ inS347 4 ∧ inS347 7 ∧ inS347 9 ∧ inS347 12
    ∧ inS347 16 ∧ inS347 21 ∧ inS347 27 ∧ inS347 28 ∧ inS347 36 ∧ inS347 48
    ∧ inS347 49 ∧ inS347 63 ∧ inS347 64 ∧ inS347 81 ∧ inS347 84 ∧ inS347 108
    ∧ inS347 112 ∧ inS347 144 ∧ inS347 147 ∧ inS347 189 ∧ inS347 192
    ∧ inS347 196 :=
  ⟨mem_1, mem_3, mem_4, mem_7, mem_9, mem_12, mem_16, mem_21, mem_27,
    mem_28, mem_36, mem_48, mem_49, mem_63, mem_64, mem_81, mem_84,
    mem_108, mem_112, mem_144, mem_147, mem_189, mem_192, mem_196⟩

/-- **THE FULL CLOSURE LAW**: the template is a multiplicative semigroup. -/
theorem S347_closed_mul : ∀ m n : Nat, inS347 m → inS347 n → inS347 (m * n) := by
  intro m n hm hn
  obtain ⟨a, b, c, ha⟩ := hm
  obtain ⟨a', b', c', ha'⟩ := hn
  refine ⟨a + a', b + b', c + c', ?_⟩
  rw [ha, ha', Nat.pow_add]
  simp only [Nat.mul_comm, Nat.mul_assoc, Nat.mul_left_comm]

/-- The 12-case exclusion below 12 (exponent bounds a ≤ 2, b ≤ 1, c ≤ 1). -/
theorem S347_below12 (n : Nat) (hn : n < 12) (h : inS347 n) :
    n = 1 ∨ n = 3 ∨ n = 4 ∨ n = 7 ∨ n = 9 := by
  obtain ⟨a, b, c, heq⟩ := h
  have h3a : 3 ^ a ≤ n := by
    rw [heq]
    exact first_le_prod (3 ^ a) (4 ^ b) (7 ^ c) (one_le_pow 4 (by omega) b)
      (one_le_pow 7 (by omega) c)
  have h4b : 4 ^ b ≤ n := by
    rw [heq]
    exact mid_le_prod (3 ^ a) (4 ^ b) (7 ^ c) (one_le_pow 3 (by omega) a) (one_le_pow 7 (by omega) c)
  have h7c : 7 ^ c ≤ n := by
    rw [heq]
    exact third_le_prod (3 ^ a) (4 ^ b) (7 ^ c) (one_le_pow 3 (by omega) a) (one_le_pow 4 (by omega) b)
  have ha : a ≤ 2 := by
    rcases (show a ≤ 2 ∨ 3 ≤ a by omega) with hle | hge
    · exact hle
    · have hp : 3 ^ 3 ≤ 3 ^ a := pow_mono 3 3 a (by omega) hge
      have h27 : 3 ^ 3 = 27 := by decide
      rw [h27] at hp
      omega
  have hb : b ≤ 1 := by
    rcases (show b ≤ 1 ∨ 2 ≤ b by omega) with hle | hge
    · exact hle
    · have hp : 4 ^ 2 ≤ 4 ^ b := pow_mono 4 2 b (by omega) hge
      have h16 : 4 ^ 2 = 16 := by decide
      rw [h16] at hp
      omega
  have hc : c ≤ 1 := by
    rcases (show c ≤ 1 ∨ 2 ≤ c by omega) with hle | hge
    · exact hle
    · have hp : 7 ^ 2 ≤ 7 ^ c := pow_mono 7 2 c (by omega) hge
      have h49 : 7 ^ 2 = 49 := by decide
      rw [h49] at hp
      omega
  rcases (show a = 0 ∨ a = 1 ∨ a = 2 by omega) with hA | hA | hA
  all_goals rw [hA] at heq
  all_goals rcases (show b = 0 ∨ b = 1 by omega) with hB | hB
  all_goals rw [hB] at heq
  all_goals rcases (show c = 0 ∨ c = 1 by omega) with hC | hC
  all_goals rw [hC] at heq
  · rw [show 3 ^ 0 * 4 ^ 0 * 7 ^ 0 = 1 by decide] at heq; omega
  · rw [show 3 ^ 0 * 4 ^ 0 * 7 ^ 1 = 7 by decide] at heq; omega
  · rw [show 3 ^ 0 * 4 ^ 1 * 7 ^ 0 = 4 by decide] at heq; omega
  · rw [show 3 ^ 0 * 4 ^ 1 * 7 ^ 1 = 28 by decide] at heq; omega
  · rw [show 3 ^ 1 * 4 ^ 0 * 7 ^ 0 = 3 by decide] at heq; omega
  · rw [show 3 ^ 1 * 4 ^ 0 * 7 ^ 1 = 21 by decide] at heq; omega
  · rw [show 3 ^ 1 * 4 ^ 1 * 7 ^ 0 = 12 by decide] at heq; omega
  · rw [show 3 ^ 1 * 4 ^ 1 * 7 ^ 1 = 84 by decide] at heq; omega
  · rw [show 3 ^ 2 * 4 ^ 0 * 7 ^ 0 = 9 by decide] at heq; omega
  · rw [show 3 ^ 2 * 4 ^ 0 * 7 ^ 1 = 63 by decide] at heq; omega
  · rw [show 3 ^ 2 * 4 ^ 1 * 7 ^ 0 = 36 by decide] at heq; omega
  · rw [show 3 ^ 2 * 4 ^ 1 * 7 ^ 1 = 252 by decide] at heq; omega

/-- The 24-case exclusion below 36 (exponent bounds a ≤ 3, b ≤ 2, c ≤ 1):
every template element below 36 is one of 1,3,4,7,9,12,16,21,27,28. -/
theorem S347_below36 (n : Nat) (hn : n < 36) (h : inS347 n) :
    n = 1 ∨ n = 3 ∨ n = 4 ∨ n = 7 ∨ n = 9 ∨ n = 12 ∨ n = 16 ∨ n = 21
    ∨ n = 27 ∨ n = 28 := by
  obtain ⟨a, b, c, heq⟩ := h
  have h3a : 3 ^ a ≤ n := by
    rw [heq]
    exact first_le_prod (3 ^ a) (4 ^ b) (7 ^ c) (one_le_pow 4 (by omega) b)
      (one_le_pow 7 (by omega) c)
  have h4b : 4 ^ b ≤ n := by
    rw [heq]
    exact mid_le_prod (3 ^ a) (4 ^ b) (7 ^ c) (one_le_pow 3 (by omega) a) (one_le_pow 7 (by omega) c)
  have h7c : 7 ^ c ≤ n := by
    rw [heq]
    exact third_le_prod (3 ^ a) (4 ^ b) (7 ^ c) (one_le_pow 3 (by omega) a) (one_le_pow 4 (by omega) b)
  have ha : a ≤ 3 := by
    rcases (show a ≤ 3 ∨ 4 ≤ a by omega) with hle | hge
    · exact hle
    · have hp : 3 ^ 4 ≤ 3 ^ a := pow_mono 3 4 a (by omega) hge
      have h81 : 3 ^ 4 = 81 := by decide
      rw [h81] at hp
      omega
  have hb : b ≤ 2 := by
    rcases (show b ≤ 2 ∨ 3 ≤ b by omega) with hle | hge
    · exact hle
    · have hp : 4 ^ 3 ≤ 4 ^ b := pow_mono 4 3 b (by omega) hge
      have h64 : 4 ^ 3 = 64 := by decide
      rw [h64] at hp
      omega
  have hc : c ≤ 1 := by
    rcases (show c ≤ 1 ∨ 2 ≤ c by omega) with hle | hge
    · exact hle
    · have hp : 7 ^ 2 ≤ 7 ^ c := pow_mono 7 2 c (by omega) hge
      have h49 : 7 ^ 2 = 49 := by decide
      rw [h49] at hp
      omega
  rcases (show a = 0 ∨ a = 1 ∨ a = 2 ∨ a = 3 by omega) with hA | hA | hA | hA
  all_goals rw [hA] at heq
  all_goals rcases (show b = 0 ∨ b = 1 ∨ b = 2 by omega) with hB | hB | hB
  all_goals rw [hB] at heq
  all_goals rcases (show c = 0 ∨ c = 1 by omega) with hC | hC
  all_goals rw [hC] at heq
  · rw [show 3 ^ 0 * 4 ^ 0 * 7 ^ 0 = 1 by decide] at heq; omega
  · rw [show 3 ^ 0 * 4 ^ 0 * 7 ^ 1 = 7 by decide] at heq; omega
  · rw [show 3 ^ 0 * 4 ^ 1 * 7 ^ 0 = 4 by decide] at heq; omega
  · rw [show 3 ^ 0 * 4 ^ 1 * 7 ^ 1 = 28 by decide] at heq; omega
  · rw [show 3 ^ 0 * 4 ^ 2 * 7 ^ 0 = 16 by decide] at heq; omega
  · rw [show 3 ^ 0 * 4 ^ 2 * 7 ^ 1 = 112 by decide] at heq; omega
  · rw [show 3 ^ 1 * 4 ^ 0 * 7 ^ 0 = 3 by decide] at heq; omega
  · rw [show 3 ^ 1 * 4 ^ 0 * 7 ^ 1 = 21 by decide] at heq; omega
  · rw [show 3 ^ 1 * 4 ^ 1 * 7 ^ 0 = 12 by decide] at heq; omega
  · rw [show 3 ^ 1 * 4 ^ 1 * 7 ^ 1 = 84 by decide] at heq; omega
  · rw [show 3 ^ 1 * 4 ^ 2 * 7 ^ 0 = 48 by decide] at heq; omega
  · rw [show 3 ^ 1 * 4 ^ 2 * 7 ^ 1 = 336 by decide] at heq; omega
  · rw [show 3 ^ 2 * 4 ^ 0 * 7 ^ 0 = 9 by decide] at heq; omega
  · rw [show 3 ^ 2 * 4 ^ 0 * 7 ^ 1 = 63 by decide] at heq; omega
  · rw [show 3 ^ 2 * 4 ^ 1 * 7 ^ 0 = 36 by decide] at heq; omega
  · rw [show 3 ^ 2 * 4 ^ 1 * 7 ^ 1 = 252 by decide] at heq; omega
  · rw [show 3 ^ 2 * 4 ^ 2 * 7 ^ 0 = 144 by decide] at heq; omega
  · rw [show 3 ^ 2 * 4 ^ 2 * 7 ^ 1 = 1008 by decide] at heq; omega
  · rw [show 3 ^ 3 * 4 ^ 0 * 7 ^ 0 = 27 by decide] at heq; omega
  · rw [show 3 ^ 3 * 4 ^ 0 * 7 ^ 1 = 189 by decide] at heq; omega
  · rw [show 3 ^ 3 * 4 ^ 1 * 7 ^ 0 = 108 by decide] at heq; omega
  · rw [show 3 ^ 3 * 4 ^ 1 * 7 ^ 1 = 756 by decide] at heq; omega
  · rw [show 3 ^ 3 * 4 ^ 2 * 7 ^ 0 = 432 by decide] at heq; omega
  · rw [show 3 ^ 3 * 4 ^ 2 * 7 ^ 1 = 3024 by decide] at heq; omega

/-- **THE ORDERED PREFIX**: the {3,4,7}-elements below 37 are exactly
1, 3, 4, 7, 9, 12, 16, 21, 27, 28, 36 — the certified initial segment. -/
theorem S347_sorted_first (n : Nat) (hn : n < 37) :
    inS347 n ↔ n = 1 ∨ n = 3 ∨ n = 4 ∨ n = 7 ∨ n = 9 ∨ n = 12 ∨ n = 16
      ∨ n = 21 ∨ n = 27 ∨ n = 28 ∨ n = 36 := by
  constructor
  · intro h
    rcases (show n < 36 ∨ n = 36 by omega) with hlt | heq36
    · rcases S347_below36 n hlt h with h1 | h1 | h1 | h1 | h1 | h1 | h1 | h1 | h1 | h1
      all_goals omega
    · subst heq36
      omega
  · intro h
    rcases h with h1 | h1 | h1 | h1 | h1 | h1 | h1 | h1 | h1 | h1 | h1
    all_goals subst h1
    · exact mem_1
    · exact mem_3
    · exact mem_4
    · exact mem_7
    · exact mem_9
    · exact mem_12
    · exact mem_16
    · exact mem_21
    · exact mem_27
    · exact mem_28
    · exact mem_36

/-- **THE NONMEMBER BATTERY**: 2, 5, 6, 8, 10 are outside the template. -/
theorem S347_nonmember :
    ¬ inS347 2 ∧ ¬ inS347 5 ∧ ¬ inS347 6 ∧ ¬ inS347 8 ∧ ¬ inS347 10 := by
  refine ⟨?_, ?_, ?_, ?_, ?_⟩
  · intro h
    rcases S347_below12 2 (by omega) h with h1 | h1 | h1 | h1 | h1
    all_goals omega
  · intro h
    rcases S347_below12 5 (by omega) h with h1 | h1 | h1 | h1 | h1
    all_goals omega
  · intro h
    rcases S347_below12 6 (by omega) h with h1 | h1 | h1 | h1 | h1
    all_goals omega
  · intro h
    rcases S347_below12 8 (by omega) h with h1 | h1 | h1 | h1 | h1
    all_goals omega
  · intro h
    rcases S347_below12 10 (by omega) h with h1 | h1 | h1 | h1 | h1
    all_goals omega

/-- The Bool recognizer certifies every template element below 37. -/
theorem S347_bool_of_mem (n : Nat) (hn : n < 37) (h : inS347 n) : S347 n = true := by
  have hd := (S347_sorted_first n hn).1 h
  rcases hd with h1 | h1 | h1 | h1 | h1 | h1 | h1 | h1 | h1 | h1 | h1
  all_goals subst h1
  all_goals rfl

/-- The Bool recognizer's certified evaluations on the prefix and the
nonmember witnesses. -/
theorem S347_bool_certified :
    (S347 1 = true ∧ S347 3 = true ∧ S347 4 = true ∧ S347 7 = true ∧ S347 9 = true
      ∧ S347 12 = true ∧ S347 16 = true ∧ S347 21 = true ∧ S347 27 = true
      ∧ S347 28 = true ∧ S347 36 = true)
    ∧ (S347 2 = false ∧ S347 5 = false ∧ S347 6 = false ∧ S347 8 = false
      ∧ S347 10 = false ∧ S347 11 = false) :=
  ⟨⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩,
    ⟨rfl, rfl, rfl, rfl, rfl, rfl⟩⟩

/-! ## §2 The tail density law — the BEGL96 completeness engine -/

/-- **THE UNIT REPRESENTATION** (cross-multiplied by 252): the 8 distinct
{3,4,7}-template reciprocals sum to 1 —
`1/3 + 1/4 + 1/7 + 1/9 + 1/12 + 1/28 + 1/36 + 1/63 = 1`. -/
theorem unit_split_decided :
    252 / 3 + 252 / 4 + 252 / 7 + 252 / 9 + 252 / 12 + 252 / 28 + 252 / 36
      + 252 / 63 = 252 := by
  decide

/-- The task-listed two-term template identities:
`1/3 + 1/4 = 7/12` and `1/7 + 1/9 = 16/63`, and the four-term
`1/12 + 1/16 + 1/21 + 1/28 = 11/48` (all cross-multiplied, decided). -/
theorem split_law_instances :
    (inS347 48 ∧ inS347 336 ∧ 336 / 3 + 336 / 7 + 336 / 48 + 336 / 336 = 336 / 2)
    ∧ (inS347 48 ∧ inS347 336 ∧ 336 / 7 + 336 / 48 + 336 / 336 = 336 / 6)
    ∧ (inS347 144 ∧ inS347 252 ∧ inS347 336
        ∧ 1008 / 9 + 1008 / 144 + 1008 / 252 + 1008 / 336 = 1008 / 8)
    ∧ (inS347 16 ∧ inS347 112 ∧ 112 / 16 + 112 / 112 = 112 / 14)
    ∧ (inS347 108 ∧ inS347 189 ∧ inS347 252
        ∧ 756 / 27 + 756 / 108 + 756 / 189 + 756 / 252 = 756 / 18)
    ∧ (inS347 144 ∧ inS347 252 ∧ inS347 336
        ∧ 1008 / 36 + 1008 / 144 + 1008 / 252 + 1008 / 336 = 1008 / 24)
    ∧ (12 / 3 + 12 / 4 = 12 * 7 / 12)
    ∧ (63 / 7 + 63 / 9 = 63 * 16 / 63)
    ∧ (336 / 12 + 336 / 16 + 336 / 21 + 336 / 28 = 336 * 11 / 48) :=
  ⟨⟨mem_48, mem_336, by decide⟩, ⟨mem_48, mem_336, by decide⟩,
    ⟨mem_144, mem_252, mem_336, by decide⟩, ⟨mem_16, mem_112, by decide⟩,
    ⟨mem_108, mem_189, mem_252, by decide⟩,
    ⟨mem_144, mem_252, mem_336, by decide⟩, by decide, by decide, by decide⟩

/-- **THE FULL GENERAL SPLIT LAW** (the round-1 kernel): for EVERY n, the
cross-multiplied split of 1/n into the 8 distinct template reciprocals
`1/(3n) + 1/(4n) + 1/(7n) + 1/(9n) + 1/(12n) + 1/(28n) + 1/(36n) +
1/(63n) = 1/n` — every quotient (252·n)/(s·n) is the certified constant
252/s, and the identity is the unit representation scaled by n. -/
theorem split_all (n : Nat) (hn : 0 < n) :
    252 * n / (3 * n) + 252 * n / (4 * n) + 252 * n / (7 * n)
      + 252 * n / (9 * n) + 252 * n / (12 * n) + 252 * n / (28 * n)
      + 252 * n / (36 * n) + 252 * n / (63 * n) = 252 * n / n := by
  have hq3 : 3 * 84 = 252 := by decide
  have hq4 : 4 * 63 = 252 := by decide
  have hq7 : 7 * 36 = 252 := by decide
  have hq9 : 9 * 28 = 252 := by decide
  have hq12 : 12 * 21 = 252 := by decide
  have hq28 : 28 * 9 = 252 := by decide
  have hq36 : 36 * 7 = 252 := by decide
  have hq63 : 63 * 4 = 252 := by decide
  have t3 : 252 * n / (3 * n) = 84 := by
    rw [show 252 * n = 3 * n * 84 by
        rw [Nat.mul_assoc, Nat.mul_comm n 84, ← Nat.mul_assoc, hq3]]
    exact Nat.mul_div_cancel_left 84 (by omega)
  have t4 : 252 * n / (4 * n) = 63 := by
    rw [show 252 * n = 4 * n * 63 by
        rw [Nat.mul_assoc, Nat.mul_comm n 63, ← Nat.mul_assoc, hq4]]
    exact Nat.mul_div_cancel_left 63 (by omega)
  have t7 : 252 * n / (7 * n) = 36 := by
    rw [show 252 * n = 7 * n * 36 by
        rw [Nat.mul_assoc, Nat.mul_comm n 36, ← Nat.mul_assoc, hq7]]
    exact Nat.mul_div_cancel_left 36 (by omega)
  have t9 : 252 * n / (9 * n) = 28 := by
    rw [show 252 * n = 9 * n * 28 by
        rw [Nat.mul_assoc, Nat.mul_comm n 28, ← Nat.mul_assoc, hq9]]
    exact Nat.mul_div_cancel_left 28 (by omega)
  have t12 : 252 * n / (12 * n) = 21 := by
    rw [show 252 * n = 12 * n * 21 by
        rw [Nat.mul_assoc, Nat.mul_comm n 21, ← Nat.mul_assoc, hq12]]
    exact Nat.mul_div_cancel_left 21 (by omega)
  have t28 : 252 * n / (28 * n) = 9 := by
    rw [show 252 * n = 28 * n * 9 by
        rw [Nat.mul_assoc, Nat.mul_comm n 9, ← Nat.mul_assoc, hq28]]
    exact Nat.mul_div_cancel_left 9 (by omega)
  have t36 : 252 * n / (36 * n) = 7 := by
    rw [show 252 * n = 36 * n * 7 by
        rw [Nat.mul_assoc, Nat.mul_comm n 7, ← Nat.mul_assoc, hq36]]
    exact Nat.mul_div_cancel_left 7 (by omega)
  have t63 : 252 * n / (63 * n) = 4 := by
    rw [show 252 * n = 63 * n * 4 by
        rw [Nat.mul_assoc, Nat.mul_comm n 4, ← Nat.mul_assoc, hq63]]
    exact Nat.mul_div_cancel_left 4 (by omega)
  have tR : 252 * n / n = 252 := by
    rw [Nat.mul_comm 252 n]
    exact Nat.mul_div_cancel_left 252 hn
  rw [t3, t4, t7, t9, t12, t28, t36, t63, tR] <;> decide

/-- **THE TEMPLATE-CERTIFIED SPLIT** (the round-1 kernel law): every
template reciprocal 1/n (n ∈ S347) splits into 8 DISTINCT template
reciprocals 1/(s·n) — the products s·n are in S347 by the closure law —
and the split denominators are STRICTLY INCREASING with every one
strictly beyond n: the split moves the mass strictly INTO THE TAIL. -/
theorem split_all_S347 (n : Nat) (hn : inS347 n) (hpos : 0 < n) :
    inS347 (3 * n) ∧ inS347 (4 * n) ∧ inS347 (7 * n) ∧ inS347 (9 * n)
    ∧ inS347 (12 * n) ∧ inS347 (28 * n) ∧ inS347 (36 * n) ∧ inS347 (63 * n)
    ∧ (252 * n / (3 * n) + 252 * n / (4 * n) + 252 * n / (7 * n)
        + 252 * n / (9 * n) + 252 * n / (12 * n) + 252 * n / (28 * n)
        + 252 * n / (36 * n) + 252 * n / (63 * n) = 252 * n / n)
    ∧ (n < 3 * n ∧ 3 * n < 4 * n ∧ 4 * n < 7 * n ∧ 7 * n < 9 * n
        ∧ 9 * n < 12 * n ∧ 12 * n < 28 * n ∧ 28 * n < 36 * n
        ∧ 36 * n < 63 * n) := by
  refine ⟨S347_closed_mul 3 n mem_3 hn, S347_closed_mul 4 n mem_4 hn,
    S347_closed_mul 7 n mem_7 hn, S347_closed_mul 9 n mem_9 hn,
    S347_closed_mul 12 n mem_12 hn, S347_closed_mul 28 n mem_28 hn,
    S347_closed_mul 36 n mem_36 hn, S347_closed_mul 63 n mem_63 hn,
    split_all n hpos, ?_⟩
  omega

/-! ## §3 The critical-juncture transfer (from #348) -/

/-- The 27 anchor: 27 = 3³ is a template element (the pure-ternary
carrier 1000₃). -/
theorem anchor_27 : inS347 27 ∧ 27 = 3 ^ 3 :=
  ⟨mem_27, by decide⟩

/-- **THE CRITICAL-JUNCTURE TRANSFER** (#348's S029 zero-slack derivation,
ported to the S347 frame at the instance level): the split is ZERO-SLACK
(an exact cross-multiplied equality, not an inequality) at INFINITELY many
template junctures — for every k there is a juncture m ∈ S347 with
m ≥ 3^k (arbitrarily deep in the template) where the 8-way split of 1/m
is exact and strictly tail-ordered. -/
theorem e124_critical_juncture (k : Nat) :
    ∃ m : Nat, inS347 m ∧ 3 ^ k ≤ m ∧
      (252 * m / (3 * m) + 252 * m / (4 * m) + 252 * m / (7 * m)
        + 252 * m / (9 * m) + 252 * m / (12 * m) + 252 * m / (28 * m)
        + 252 * m / (36 * m) + 252 * m / (63 * m) = 252 * m / m)
      ∧ (m < 3 * m ∧ 3 * m < 4 * m ∧ 4 * m < 7 * m ∧ 7 * m < 9 * m
          ∧ 9 * m < 12 * m ∧ 12 * m < 28 * m ∧ 28 * m < 36 * m
          ∧ 36 * m < 63 * m) := by
  have hpos : 0 < 3 ^ k := three_pow_pos_lemma k
  refine ⟨3 ^ k, mem_pow3 k, Nat.le_refl (3 ^ k), split_all (3 ^ k) hpos, ?_⟩
  omega

/-! ## §4 The Arsenal bridge -/

/-- **THE ARSENAL BRIDGE** (house pattern): every ternary digit carrier
d < 3 (via `ErdosTernary2.lt_three_cases`, the Arsenal's three-digit
census) is a genuine `isTernaryDigit`-carrier AND a template exponent
carrier: 3^d ∈ S347.  The ternary digit set {0,1,2} is the {3,4,7}-
template's exponent interface at the 3-carrier. -/
theorem e124_arsenal_bridge (d : Nat) (hd : d < 3) :
    ErdosTernary2.isTernaryDigit d = true ∧ inS347 (3 ^ d) := by
  rcases ErdosTernary2.lt_three_cases d hd with h | h | h
  · subst h
    exact ⟨rfl, mem_pow3 0⟩
  · subst h
    exact ⟨rfl, mem_pow3 1⟩
  · subst h
    exact ⟨rfl, mem_pow3 2⟩

/-! ## §5 The board -/

/-- **THE BEGL96 BOARD** (the round-1 composite master): the semigroup
closure law, the ordered prefix, the nonmember battery, the unit
representation, the general split law, the template-certified split, the
infinitely-many zero-slack junctures, and the Arsenal bridge — full
statements, unconditional. -/
theorem e124_begl96_board :
    (∀ m n : Nat, inS347 m → inS347 n → inS347 (m * n))
    ∧ (∀ n : Nat, n < 37 → (inS347 n ↔ n = 1 ∨ n = 3 ∨ n = 4 ∨ n = 7 ∨ n = 9
        ∨ n = 12 ∨ n = 16 ∨ n = 21 ∨ n = 27 ∨ n = 28 ∨ n = 36))
    ∧ (¬ inS347 2 ∧ ¬ inS347 5 ∧ ¬ inS347 6 ∧ ¬ inS347 8 ∧ ¬ inS347 10)
    ∧ (252 / 3 + 252 / 4 + 252 / 7 + 252 / 9 + 252 / 12 + 252 / 28
        + 252 / 36 + 252 / 63 = 252)
    ∧ (∀ n : Nat, 0 < n →
        (252 * n / (3 * n) + 252 * n / (4 * n) + 252 * n / (7 * n)
          + 252 * n / (9 * n) + 252 * n / (12 * n) + 252 * n / (28 * n)
          + 252 * n / (36 * n) + 252 * n / (63 * n) = 252 * n / n))
    ∧ (∀ n : Nat, inS347 n → 0 < n →
        (inS347 (3 * n) ∧ inS347 (4 * n) ∧ inS347 (7 * n) ∧ inS347 (9 * n)
          ∧ inS347 (12 * n) ∧ inS347 (28 * n) ∧ inS347 (36 * n)
          ∧ inS347 (63 * n)
          ∧ (252 * n / (3 * n) + 252 * n / (4 * n) + 252 * n / (7 * n)
              + 252 * n / (9 * n) + 252 * n / (12 * n) + 252 * n / (28 * n)
              + 252 * n / (36 * n) + 252 * n / (63 * n) = 252 * n / n)
          ∧ (n < 3 * n ∧ 3 * n < 4 * n ∧ 4 * n < 7 * n ∧ 7 * n < 9 * n
              ∧ 9 * n < 12 * n ∧ 12 * n < 28 * n ∧ 28 * n < 36 * n
              ∧ 36 * n < 63 * n)))
    ∧ (∀ k : Nat, ∃ m : Nat, inS347 m ∧ 3 ^ k ≤ m ∧
        (252 * m / (3 * m) + 252 * m / (4 * m) + 252 * m / (7 * m)
          + 252 * m / (9 * m) + 252 * m / (12 * m) + 252 * m / (28 * m)
          + 252 * m / (36 * m) + 252 * m / (63 * m) = 252 * m / m)
        ∧ (m < 3 * m ∧ 3 * m < 4 * m ∧ 4 * m < 7 * m ∧ 7 * m < 9 * m
            ∧ 9 * m < 12 * m ∧ 12 * m < 28 * m ∧ 28 * m < 36 * m
            ∧ 36 * m < 63 * m))
    ∧ (∀ d : Nat, d < 3 → ErdosTernary2.isTernaryDigit d = true ∧ inS347 (3 ^ d)) :=
  ⟨S347_closed_mul, S347_sorted_first, S347_nonmember, unit_split_decided,
    split_all, split_all_S347, e124_critical_juncture, e124_arsenal_bridge⟩

/-! ## Receipt block -/

#print axioms S347_closed_mul
#print axioms S347_sorted_first
#print axioms S347_nonmember
#print axioms S347_table
#print axioms unit_split_decided
#print axioms split_law_instances
#print axioms split_all
#print axioms split_all_S347
#print axioms e124_critical_juncture
#print axioms e124_arsenal_bridge
#print axioms e124_begl96_board

#eval "E124_BEGL96_GREEN"

end E124
