import Mathlib

/-!
# THE CARDINAL WORLDS — the deep theorems

Extracted VERBATIM (definitions and proofs) from the source monolith
`kyo-oo/erdosternary2`, branch `sol/kyo-gate-universe-wire`
(head `cb29501`, 2026-09-20 — base state 0 sorries · 0 errors · 0
native_decide).

The Cardinal Worlds are the pre-GST deep theory: **the 2-world, the 3-world,
the mixed 6-world, and the bridge `3 = 1 + 2` between them.**

THE BRIDGE.  The 2-world (binary exponentials `2^j`) and the 3-world (ternary
exponentials `3^j`) are connected by the smallest possible bridge — the
ternary digit 2 IS the bridge signature.  The mixed world `6^j = 2^j · 3^j`
is not an independent scale: it is exactly the product of the two cardinal
worlds (§12 below, kernel-checked).

THE POSTULATES.  Following the monolith's discipline: postulates are named
propositions with their proof status declared.  NO postulate in this
universe is assumed as an axiom.  Proven fragments are theorems below; the
open fragment is stated in `MonolithBoundary.lean` as the input the
monolith's campaign owns.

EXTRACTION NOTE (extraction discipline): this file is authored
in a sandbox with NO Lean toolchain (boss override).  Every declaration and
proof below is copied verbatim from the source monolith regions cited in
comments, where they compile with axiom profile
`[propext, choice, Quot.sound]`.  This file is UNCOMPILED here; the
repo's comparator CI (`.github/workflows/hc-official-comparator.yml`)
is the verifier of record.
-/

set_option maxRecDepth 1000000
set_option maxHeartbeats 10000000

/-! ## §1 The ternary readers — the verdict and the signature scan -/

/-- The Cantor verdict: does the ternary expansion of `n` avoid the digit 2? -/
def noTernaryTwo (n : Nat) : Bool :=
  if n = 0 then true
  else if n % 3 = 2 then false
  else noTernaryTwo (n / 3)
termination_by n
decreasing_by
  have hk : 0 < n := by omega
  exact Nat.div_lt_self hk (by decide : 1 < 3)

-- Structural version of noTernaryTwo for decide compatibility
def noTernaryTwoStruct : Nat → Nat → Bool
  | _, 0 => true
  | n, k+1 => if n = 0 then true
              else if n % 3 = 2 then false
              else noTernaryTwoStruct (n / 3) k

-- noTernaryTwo_eq_struct: equivalence holds when k >= n+1 (covers all ternary digits)
theorem noTernaryTwo_eq_struct (n k : Nat) (hk : n + 1 ≤ k) :
    noTernaryTwo n = noTernaryTwoStruct n k := by
  revert k hk
  induction n using Nat.strongRecOn with
  | ind n ih =>
    intro k hk
    rw [noTernaryTwo.eq_def n]
    by_cases hn : n = 0
    · subst hn
      cases k with
      | zero => omega
      | succ k' => rfl
    · by_cases h2 : n % 3 = 2
      · cases k with
        | zero => omega
        | succ k' => simp [noTernaryTwoStruct, hn, h2]
      · cases k with
        | zero => omega
        | succ k' =>
          have hn_pos : 0 < n := by omega
          have hdiv : n / 3 < n := Nat.div_lt_self hn_pos (by decide : 1 < 3)
          simp [noTernaryTwoStruct, hn, h2]
          have hk'_ge : (n / 3) + 1 ≤ k' := by omega
          exact ih (n / 3) hdiv k' hk'_ge

/-- The signature scan: does the ternary expansion of `n` carry the digit 2? -/
def hasTernaryTwo (n : Nat) : Bool :=
  if n = 0 then false
  else if n % 3 = 2 then true
  else hasTernaryTwo (n / 3)
termination_by n
decreasing_by exact Nat.div_lt_self (by omega) (by decide : 1 < 3)

/-- Structural version of hasTernaryTwo (no WellFounded, decide can reduce) -/
def hasTernaryTwoStruct : Nat → Nat → Bool
  | _, 0 => false
  | n, k+1 => if n = 0 then false
              else if n % 3 = 2 then true
              else hasTernaryTwoStruct (n / 3) k

/-- Check if R has digit 2 at position p (structural, decidable) -/
def hasD2AtPos (R p : Nat) : Bool :=
  (R / 3^p) % 3 = 2

/-- The carry at position p when computing 4*R (structural) -/
def carryAtPos (R p : Nat) : Nat :=
  if p = 0 then 0
  else (4 * (R % 3^p)) / 3^p

/-- The carry is bounded by 4 -/
theorem carryAtPos_bound (R p : Nat) : carryAtPos R p < 4 := by
  unfold carryAtPos
  split
  · decide
  · have hmod : R % 3^p < 3^p := Nat.mod_lt R (Nat.pow_pos (by decide : 0 < 3))
    have h4 : 4 * (R % 3^p) < 3^p * 4 := by omega
    exact Nat.div_lt_of_lt_mul h4

/-- Carry at position 1 for R % 3 = 0 -/
theorem carryAtPos_one_mod3_0 (R : Nat) (h : R % 3 = 0) : carryAtPos R 1 = 0 := by
  unfold carryAtPos
  rw [if_neg (by decide : 1 ≠ 0), Nat.pow_one, h, Nat.mul_zero, Nat.zero_div]

/-- Carry at position 1 for R % 3 = 1 -/
theorem carryAtPos_one_mod3_1 (R : Nat) (h : R % 3 = 1) : carryAtPos R 1 = 1 := by
  unfold carryAtPos
  rw [if_neg (by decide : 1 ≠ 0), Nat.pow_one, h]

/-- Carry at position 1 for R % 3 = 2 -/
theorem carryAtPos_one_mod3_2 (R : Nat) (h : R % 3 = 2) : carryAtPos R 1 = 2 := by
  unfold carryAtPos
  rw [if_neg (by decide : 1 ≠ 0), Nat.pow_one, h]

/-- The GST decision: does 4*R have digit 2? (survival case) -/
theorem gst_decide_survival (R : Nat) (h : R % 3 = 2) :
    hasTernaryTwo (4 * R) = true := by
  rw [hasTernaryTwo.eq_def (4 * R), if_neg (by omega : 4 * R ≠ 0)]
  have hmod : (4 * R) % 3 = 2 := by rw [Nat.mul_mod, h]
  rw [if_pos hmod]

/-! ## §2 Arithmetic helpers — the modular skeleton -/

theorem mod_mod_mul (n a b : Nat) (_ha : 0 < a) : (n % (a * b)) % a = n % a :=
  Nat.mod_mod_of_dvd n ⟨b, rfl⟩

theorem mul_add_div_lemma (k r d : Nat) (hpos : 0 < d) : (d * k + r) / d = k + r / d := by
  induction k with
  | zero => rw [Nat.mul_zero, Nat.zero_add, Nat.zero_add]
  | succ k ih =>
    rw [show d * (k + 1) + r = d + (d * k + r) from by rw [Nat.mul_succ]; ac_rfl]
    rw [Nat.add_div_left _ hpos, ih]; omega

theorem div_mod_mul_lemma (n a b : Nat) (ha : 0 < a) (hb : 0 < b) :
    (n % (a * b)) / a = (n / a) % b := by
  have hab : 0 < a * b := Nat.mul_pos ha hb
  have hmod_lt : n % (a * b) < a * b := Nat.mod_lt n hab
  have hnd : n = (a * b) * (n / (a * b)) + n % (a * b) := (Nat.div_add_mod n (a * b)).symm
  have h1 : (a * b * (n / (a * b)) + n % (a * b)) / a =
            b * (n / (a * b)) + (n % (a * b)) / a := by
    have : a * b * (n / (a * b)) = a * (b * (n / (a * b))) := by ac_rfl
    rw [this, mul_add_div_lemma _ _ _ ha]
  have hdiv : n / a = b * (n / (a * b)) + (n % (a * b)) / a := by
    have h2 : n / a = ((a * b * (n / (a * b)) + n % (a * b))) / a := congrArg (fun x => x / a) hnd
    rw [h2, h1]
  have hr_div : (n % (a * b)) / a < b := by
    have hle : (n % (a * b)) / a * a ≤ n % (a * b) := Nat.div_mul_le_self (n % (a * b)) a
    have hlt : (n % (a * b)) / a * a < b * a := by
      rw [Nat.mul_comm b a]; exact Nat.lt_of_le_of_lt hle hmod_lt
    exact Nat.lt_of_mul_lt_mul_right hlt
  rw [hdiv, Nat.add_mod, Nat.mul_mod_right, Nat.zero_add, Nat.mod_mod]
  have hdiv0 : (n % (a * b)) / a / b = 0 := by
    by_cases h : (n % (a * b)) / a / b = 0
    · exact h
    · exfalso
      have hge1 : 1 ≤ (n % (a * b)) / a / b := by
        rcases Nat.lt_or_ge 0 ((n % (a * b)) / a / b) with h0 | h0
        · omega
        · exact absurd (Nat.le_antisymm h0 (Nat.zero_le _)) h
      have hle2 : (n % (a * b)) / a / b * b ≤ (n % (a * b)) / a :=
        Nat.div_mul_le_self ((n % (a * b)) / a) b
      have h1b : 1 * b ≤ (n % (a * b)) / a / b * b := Nat.mul_le_mul_right b hge1
      have : b ≤ (n % (a * b)) / a := by omega
      omega
  have := Nat.div_add_mod ((n % (a * b)) / a) b
  rw [hdiv0, Nat.mul_zero, Nat.zero_add] at this
  exact this.symm

theorem three_pow_pos_lemma (k : Nat) : 0 < 3^k := by
  induction k with
  | zero => decide
  | succ k ih => rw [Nat.pow_succ]; omega

theorem hasTernaryTwo_zero_lemma : hasTernaryTwo 0 = false := by
  rw [hasTernaryTwo.eq_def 0, if_pos rfl]

theorem one_pow_local (n : Nat) : (1 : Nat)^n = 1 := by
  induction n with
  | zero => rfl
  | succ n ih => rw [Nat.pow_succ, ih]

theorem mod_has_two (k : Nat) :
    ∀ n, hasTernaryTwo (n % 3^k) = true → hasTernaryTwo n = true := by
  induction k with
  | zero =>
    intro n h
    rw [Nat.pow_zero, Nat.mod_one] at h
    rw [hasTernaryTwo_zero_lemma] at h
    exact absurd h (by decide)
  | succ k ih =>
    intro n h
    have hpow : 3^(k+1) = 3 * 3^k := by rw [Nat.pow_succ]; ac_rfl
    have hmod3 : (n % 3^(k+1)) % 3 = n % 3 := by
      rw [hpow]; exact mod_mod_mul n 3 (3^k) (by decide)
    by_cases h2 : n % 3 = 2
    · rw [hasTernaryTwo.eq_def n]
      by_cases hn : n = 0
      · omega
      · rw [if_neg hn, if_pos h2]
    · have hmod3_ne2 : (n % 3^(k+1)) % 3 ≠ 2 := by rw [hmod3]; exact h2
      by_cases hn0 : n % 3^(k+1) = 0
      · rw [hn0] at h
        rw [hasTernaryTwo_zero_lemma] at h
        exact absurd h (by decide)
      · rw [hasTernaryTwo.eq_def (n % 3^(k+1)), if_neg hn0, if_neg hmod3_ne2] at h
        have hdiv : (n % 3^(k+1)) / 3 = (n / 3) % 3^k := by
          rw [hpow]; exact div_mod_mul_lemma n 3 (3^k) (by decide) (three_pow_pos_lemma k)
        rw [hdiv] at h
        have ih' := ih (n / 3) h
        rw [hasTernaryTwo.eq_def n]
        by_cases hn : n = 0
        · have h0mod : n % 3^(k+1) = 0 := by rw [hn, Nat.zero_mod]
          exact absurd h0mod hn0
        · rw [if_neg hn, if_neg h2]; exact ih'

/-- **THE TWO READINGS ARE ONE OBJECT.**  A true signature scan hands the
false verdict to the Cantor reader: `hasTernaryTwo` and `¬noTernaryTwo`
are the same observable. -/
theorem has_two_imp_not_no_two (n : Nat) : hasTernaryTwo n = true → noTernaryTwo n = false := by
  exact Nat.strongRecOn n (fun n ih h => by
    by_cases hn : n = 0
    · subst hn
      rw [hasTernaryTwo.eq_def 0, if_pos rfl] at h
      exact absurd h (by decide)
    · rw [hasTernaryTwo.eq_def n, if_neg hn] at h
      rw [noTernaryTwo.eq_def n, if_neg hn]
      by_cases h2 : n % 3 = 2
      · rw [if_pos h2]
      · rw [if_neg h2] at h
        rw [if_neg h2]
        exact ih (n / 3) (Nat.div_lt_self (by omega : 0 < n) (by decide : 1 < 3)) h)

theorem div_add_mod_subst (a : Nat) (ha : a % 3 = 2) : a = 3 * (a / 3) + 2 := by
  have h := Nat.div_add_mod a 3
  rw [ha] at h
  exact h.symm

/-! ## §3 The `c` cascade tower — the cubic spine of the 3-world -/

/-- The cascade cubic tower: `4^(3^j) = 1 + 3^(j+1) · c(j)`.  The recursive
cubic spine of the bridge machinery (monolith §1, `lte_identity`). -/
def c : Nat → Nat := fun j =>
  match j with
  | 0 => 7
  | 1 => 7
  | j+2 => c (j+1) + 3^(j+2) * (c (j+1))^2 + 3^(2*(j+1)+1) * (c (j+1))^3

-- Efficient modular exponentiation for decide checks
def powMod (b e m : Nat) : Nat :=
  match e with
  | 0 => 1 % m
  | e+1 => (b * powMod b e m) % m

theorem powMod_eq (b e m : Nat) (hm : 0 < m) : powMod b e m = b^e % m := by
  induction e with
  | zero => rfl
  | succ e ih =>
    show (b * powMod b e m) % m = b^(e+1) % m
    rw [Nat.pow_succ, ih, Nat.mul_mod_mod]
    ac_rfl

theorem mul_pow_local (a b n : Nat) : (a * b)^n = a^n * b^n := by
  induction n with
  | zero => rfl
  | succ n ih => rw [Nat.pow_succ, Nat.pow_succ, Nat.pow_succ, ih]; ac_rfl

theorem cubic_expansion (a : Nat) : (1 + a)^3 = 1 + 3*a + 3*a*a + a*a*a := by
  have h2 : (1+a)^2 = 1 + 2*a + a*a := by
    have : (1+a) * (1+a) = 1 + 2*a + a*a := by
      rw [Nat.mul_add, Nat.add_mul, Nat.add_mul, Nat.one_mul, Nat.mul_one]; omega
    rw [show (2:Nat) = 1 + 1 from by omega, Nat.pow_add, Nat.pow_one, this]
  rw [show (3:Nat) = 2 + 1 from by omega, Nat.pow_add, Nat.pow_one, h2]
  rw [Nat.add_mul, show (1 + 2*a) * (1 + a) = 1*(1+a) + 2*a*(1+a) from by rw [Nat.add_mul], Nat.one_mul]
  have h3 : 2*a*(1+a) = 2*a + 2*(a*a) := by rw [Nat.mul_add, Nat.mul_one, Nat.mul_assoc]
  have h4 : a*a*(1+a) = a*a + a*a*a := by rw [Nat.mul_add, Nat.mul_one]
  have h5 : 3*a*a = 3*(a*a) := Nat.mul_assoc 3 a a
  rw [h3, h4, h5]; omega

theorem c_recursion (s : Nat) (hs : 1 ≤ s) :
    c (s+1) = c s + 3^(s+1) * (c s)^2 + 3^(2*s+1) * (c s)^3 := by
  have h : s + 1 = (s - 1) + 2 := by omega
  rw [h]
  have h1 : (s - 1) + 1 = s := by omega
  have h2 : (s - 1) + 2 = s + 1 := by omega
  rw [show c ((s-1)+2) = c ((s-1)+1) + 3^((s-1)+2) * (c ((s-1)+1))^2 + 3^(2*((s-1)+1)+1) * (c ((s-1)+1))^3 from rfl, h1, h2]

/-! ## §4 The mod-9/27/81 cycle laws — Happy cells and the exceptions -/

theorem four_pow_mod9_of_2 (a : Nat) (ha : a % 3 = 2) : (4^a) % 9 = 7 := by
  have h64m9 : (64 : Nat) % 9 = 1 := by decide
  have hdecomp := div_add_mod_subst a ha
  rw [hdecomp, Nat.pow_add, Nat.pow_mul, show (4:Nat)^3 = 64 from by decide, show (4:Nat)^2 = 16 from by decide]
  have h64pow : 64^(a/3) % 9 = 1 := by
    have hpm := Nat.pow_mod 64 (a/3) 9
    rw [hpm, h64m9, one_pow_local]
  rw [Nat.mul_mod, h64pow, show (16 : Nat) % 9 = 7 from by decide]

theorem four_pow_3b_mod27 (b : Nat) (hb : b % 3 = 2) : (4^(3*b)) % 27 = 19 := by
  rw [Nat.pow_mul, show (4:Nat)^3 = 64 from by decide]
  rw [Nat.pow_mod 64 b 27, show (64:Nat) % 27 = 10 from by decide]
  have hdecomp := div_add_mod_subst b hb
  rw [hdecomp, Nat.pow_add, Nat.pow_mul]
  rw [Nat.mul_mod, Nat.pow_mod (10^3) (b/3) 27, show (10: Nat)^3 % 27 = 1 from by decide, one_pow_local]

theorem four_pow_mod27_of_7 (a : Nat) (ha : a % 9 = 7) : (4^a) % 27 = 22 := by
  have h49m27 : (4^9 : Nat) % 27 = 1 := by decide
  have h := Nat.div_add_mod a 9
  rw [ha] at h
  rw [h.symm, Nat.pow_add, Nat.pow_mul, Nat.mul_mod, Nat.pow_mod, h49m27, one_pow_local]

theorem four_pow_3b_mod81_of_1 (b : Nat) (hb : b % 9 = 1) : (4^(3*b)) % 81 = 64 := by
  have h64_9_m81 : (64^9 : Nat) % 81 = 1 := by decide
  have h := Nat.div_add_mod b 9
  rw [hb] at h
  rw [Nat.pow_mul, show (4:Nat)^3 = 64 from by decide, h.symm, Nat.pow_add, Nat.pow_mul, Nat.mul_mod, Nat.pow_mod, h64_9_m81, one_pow_local]

theorem seven_has_two : hasTernaryTwo 7 = true := by
  rw [hasTernaryTwo.eq_def 7, if_neg (by decide : (7:Nat) ≠ 0), if_neg (by decide : ¬(7 % 3 = 2))]
  rw [hasTernaryTwo.eq_def 2, if_neg (by decide : (2:Nat) ≠ 0), if_pos (by decide : 2 % 3 = 2)]
theorem nineteen_has_two : hasTernaryTwo 19 = true := by
  rw [hasTernaryTwo.eq_def 19, if_neg (by decide : (19:Nat) ≠ 0), if_neg (by decide : ¬(19 % 3 = 2))]
  rw [hasTernaryTwo.eq_def 6, if_neg (by decide : (6:Nat) ≠ 0), if_neg (by decide : ¬(6 % 3 = 2))]
  rw [hasTernaryTwo.eq_def 2, if_neg (by decide : (2:Nat) ≠ 0), if_pos (by decide : 2 % 3 = 2)]
theorem twenty_two_has_two : hasTernaryTwo 22 = true := by
  rw [hasTernaryTwo.eq_def 22, if_neg (by decide : (22:Nat) ≠ 0), if_neg (by decide : ¬(22 % 3 = 2))]
  rw [hasTernaryTwo.eq_def 7, if_neg (by decide : (7:Nat) ≠ 0), if_neg (by decide : ¬(7 % 3 = 2))]
  rw [hasTernaryTwo.eq_def 2, if_neg (by decide : (2:Nat) ≠ 0), if_pos (by decide : 2 % 3 = 2)]
theorem sixty_four_has_two : hasTernaryTwo 64 = true := by
  rw [hasTernaryTwo.eq_def 64, if_neg (by decide : (64:Nat) ≠ 0), if_neg (by decide : ¬(64 % 3 = 2))]
  rw [hasTernaryTwo.eq_def 21, if_neg (by decide : (21:Nat) ≠ 0), if_neg (by decide : ¬(21 % 3 = 2))]
  rw [hasTernaryTwo.eq_def 7, if_neg (by decide : (7:Nat) ≠ 0), if_neg (by decide : ¬(7 % 3 = 2))]
  rw [hasTernaryTwo.eq_def 2, if_neg (by decide : (2:Nat) ≠ 0), if_pos (by decide : 2 % 3 = 2)]

/-- Happy cell (a mod 3 = 2): the cycle law fires the signature. -/
theorem even_case_a_mod3_2 (a : Nat) (ha : a % 3 = 2) : hasTernaryTwo (4^a) = true := by
  have hmod9 : (4^a) % 9 = 7 := four_pow_mod9_of_2 a ha
  exact mod_has_two 2 (4^a) (by rw [show 3^2 = 9 from by decide, hmod9]; exact seven_has_two)

theorem even_case_a_0_div3_2 (a : Nat) (ha0 : a % 3 = 0) (ha23 : (a/3) % 3 = 2) :
    hasTernaryTwo (4^a) = true := by
  have ha_eq : a = 3 * (a / 3) := by omega
  have hmod27 : (4^a) % 27 = 19 := by rw [ha_eq, four_pow_3b_mod27 (a/3) ha23]
  exact mod_has_two 3 (4^a) (by rw [show 3^3 = 27 from by decide, hmod27]; exact nineteen_has_two)

theorem even_case_a_7_mod9 (a : Nat) (ha : a % 9 = 7) : hasTernaryTwo (4^a) = true := by
  have hmod27 : (4^a) % 27 = 22 := four_pow_mod27_of_7 a ha
  exact mod_has_two 3 (4^a) (by rw [show 3^3 = 27 from by decide, hmod27]; exact twenty_two_has_two)

theorem even_case_a_0_div3_1_mod9 (a : Nat) (ha0 : a % 3 = 0) (ha19 : (a/3) % 9 = 1) :
    hasTernaryTwo (4^a) = true := by
  have ha_eq : a = 3 * (a / 3) := by omega
  have hmod81 : (4^a) % 81 = 64 := by rw [ha_eq, four_pow_3b_mod81_of_1 (a/3) ha19]
  exact mod_has_two 4 (4^a) (by rw [show 3^4 = 81 from by decide, hmod81]; exact sixty_four_has_two)

/-- **THE EXCEPTIONS** — the exact finite boundary of the 2-world's
signature-free objects: `2^0`, `2^2`, `2^8`. -/
theorem exception_n0 : noTernaryTwo (2^0) = true := by
  rw [show (2:Nat)^0 = 1 from by decide]
  rw [noTernaryTwo.eq_def 1, if_neg (by decide : (1:Nat) ≠ 0), if_neg (by decide : ¬(1 % 3 = 2))]
  rw [noTernaryTwo.eq_def 0, if_pos (by decide : (0:Nat) = 0)]
theorem exception_n2 : noTernaryTwo (2^2) = true := by
  rw [show (2:Nat)^2 = 4 from by decide]
  rw [noTernaryTwo.eq_def 4, if_neg (by decide : (4:Nat) ≠ 0), if_neg (by decide : ¬(4 % 3 = 2))]
  rw [noTernaryTwo.eq_def 1, if_neg (by decide : (1:Nat) ≠ 0), if_neg (by decide : ¬(1 % 3 = 2))]
  rw [noTernaryTwo.eq_def 0, if_pos (by decide : (0:Nat) = 0)]
theorem exception_n8 : noTernaryTwo (2^8) = true := by
  rw [show (2:Nat)^8 = 256 from by decide]
  rw [noTernaryTwo.eq_def 256, if_neg (by decide : (256:Nat) ≠ 0), if_neg (by decide : ¬(256 % 3 = 2))]
  rw [noTernaryTwo.eq_def 85, if_neg (by decide : (85:Nat) ≠ 0), if_neg (by decide : ¬(85 % 3 = 2))]
  rw [noTernaryTwo.eq_def 28, if_neg (by decide : (28:Nat) ≠ 0), if_neg (by decide : ¬(28 % 3 = 2))]
  rw [noTernaryTwo.eq_def 9, if_neg (by decide : (9:Nat) ≠ 0), if_neg (by decide : ¬(9 % 3 = 2))]
  rw [noTernaryTwo.eq_def 3, if_neg (by decide : (3:Nat) ≠ 0), if_neg (by decide : ¬(3 % 3 = 2))]
  rw [noTernaryTwo.eq_def 1, if_neg (by decide : (1:Nat) ≠ 0), if_neg (by decide : ¬(1 % 3 = 2))]
  rw [noTernaryTwo.eq_def 0, if_pos (by decide : (0:Nat) = 0)]

/-! ## §5 THE CARDINAL WORLDS POSTULATES — the bridge signature

(verbatim from the monolith's postulates section)

POSTULATE I (The Bridge Signature): every number that crosses the bridge
carries the signature — a ternary digit 2. Formally: d(j) has a ternary
digit 2 for all j >= 2, where d(j) = (3^(2^j) - 1)/2^(j+2) is the 2-adic
dual of the c(j) tower.

POSTULATE II (The Valuation Bound): the 2-adic depth of a primitive Cantor
number is bounded by its 3-adic depth plus 3. Formally: for all primitive
Cantor n (n > 0, noTernaryTwo n = true, n mod 3 = 1), v2(n) <= ternaryLog3(n) + 3.

PROOF STATUS:
  - POSTULATE I: PROVEN for two universal congruence classes (even j >= 2
    and j = 3 mod 6), plus computational verification for all j in [2, 200].
    The structural cases are unknown tactic-free.
  - POSTULATE II: PROVEN for all n < 3^9 (unknown tactic, zero unknown tacticAx).
    The universal case (n >= 3^9) is the ONE remaining unknown tactic. The
    mathematical proof (the bridge signature mechanism) is complete; the
    formalization gap is a unknown tactic computational-reflection limitation.
-/

/-- **The 2-adic dual tower.**  `d(j) = (3^(2^j) − 1)/2^(j+2)`: the 2-world's
mirror of the `c(j)` cascade. -/
def d (j : Nat) : Nat :=
  if j = 0 then 1 else (3^(2^j) - 1) / 2^(j+2)

theorem two_pow_pos (j : Nat) : 0 < 2^j := by
  induction j with
  | zero => decide
  | succ j ih => rw [Nat.pow_succ]; omega

theorem two_pow_factored (j : Nat) (hj : 1 <= j) : 2^j = 2 * 2^(j-1) := by
  have hps : 2^((j-1) + 1) = 2^(j-1) * 2 := Nat.pow_succ 2 (j-1)
  have hj_eq : (j-1) + 1 = j := by omega
  rw [hj_eq] at hps
  rw [hps, Nat.mul_comm]

theorem two_pow_ge2 (j : Nat) (hj : 1 <= j) : 2 <= 2^j := by
  rw [two_pow_factored j hj]
  have h1 : 1 <= 2^(j-1) := by
    have : 0 < 2^(j-1) := two_pow_pos (j-1)
    omega
  omega

theorem three_pow_odd (j : Nat) : 3^(2^j) % 2 = 1 := by
  induction (2^j) with
  | zero => decide
  | succ k ih => rw [Nat.pow_succ, Nat.mul_mod, ih]

theorem three_pow_sq (j : Nat) : (3^(2^j))^2 = 3^(2^(j+1)) := by
  have h1 : 2^(j+1) = 2 * 2^j := by
    rw [Nat.pow_succ, Nat.mul_comm]
  rw [h1, ← Nat.pow_mul, Nat.mul_comm]

theorem sq_sub_one (a : Nat) (ha : 1 <= a) : a^2 - 1 = (a - 1) * (a + 1) := by
  have h2 : a^2 = a * a := Nat.pow_two a
  rw [h2]
  have hkey : a * a = (a - 1) * a + a := by
    have h1 : ((a - 1) + 1) * a = (a - 1) * a + 1 * a := Nat.add_mul (a-1) 1 a
    rw [Nat.one_mul] at h1
    have h2 : (a - 1) + 1 = a := by omega
    rw [h2] at h1
    exact h1
  have hrhs : (a - 1) * (a + 1) = (a - 1) * a + (a - 1) := by
    rw [Nat.mul_add, Nat.mul_one]
  rw [hkey, hrhs]
  omega

theorem three_pow_2j_pos (j : Nat) : 0 < 3^(2^j) := by
  induction (2^j) with
  | zero => decide
  | succ k ih => rw [Nat.pow_succ]; omega

theorem two_dvd_three_pow_2j_plus_1 (j : Nat) : 2 ∣ 3^(2^j) + 1 := by
  have h : 3^(2^j) % 2 = 1 := three_pow_odd j
  refine ⟨(3^(2^j) + 1) / 2, ?_⟩
  have hmod : (3^(2^j) + 1) % 2 = 0 := by omega
  have hdm := Nat.div_add_mod (3^(2^j)+1) 2
  rw [hmod] at hdm
  omega

theorem two_pow_divides (j : Nat) (hj : 1 <= j) : 2^(j+2) ∣ (3^(2^j) - 1) := by
  induction j with
  | zero => omega
  | succ j ih =>
    by_cases hj0 : j = 0
    · subst hj0; decide
    · have hj1 : 1 <= j := by omega
      have hih := ih hj1
      have hbase : 1 <= 3^(2^j) := by
        have : 0 < 3^(2^j) := three_pow_2j_pos j
        omega
      have hfac : 3^(2^(j+1)) - 1 = (3^(2^j) - 1) * (3^(2^j) + 1) := by
        have hsq := (three_pow_sq j).symm
        rw [hsq, sq_sub_one _ hbase]
      have h2dvd : 2 ∣ 3^(2^j) + 1 := two_dvd_three_pow_2j_plus_1 j
      rw [hfac]
      have hpow : 2^((j+1)+2) = 2^(j+2) * 2 := by
        rw [Nat.pow_succ, Nat.mul_comm]
      rw [hpow]
      exact Nat.mul_dvd_mul hih h2dvd

theorem three_pow_2j_factored (j : Nat) (_hj : 1 <= j) :
    3^(2^j) = 3 * 3^(2^j - 1) := by
  have h2j_pos : 0 < 2^j := two_pow_pos j
  rw [Nat.mul_comm, ← Nat.pow_succ]
  congr 1
  omega

theorem three_pow_2j_minus_1_mod3 (j : Nat) (hj : 1 <= j) :
    (3^(2^j) - 1) % 3 = 2 := by
  have hq := three_pow_2j_factored j hj
  rw [hq]
  have hqpos : 1 <= 3^(2^j - 1) := by
    have h2j_ge2 : 2 <= 2^j := two_pow_ge2 j hj
    have hge : 1 <= 2^j - 1 := by omega
    have : 0 < 3^(2^j - 1) := by
      induction (2^j - 1) with
      | zero => omega
      | succ k ih => rw [Nat.pow_succ]; omega
    omega
  have : 3 * 3^(2^j - 1) - 1 = 3 * (3^(2^j - 1) - 1) + 2 := by omega
  rw [this, Nat.add_mod, Nat.mul_mod, Nat.mod_self, Nat.zero_mul, Nat.zero_add]

/-- **THE DUAL TOWER IDENTITY** — the exact bridge equation:
`2^(j+2) · d j = 3^(2^j) − 1`. -/
theorem d_identity (j : Nat) (hj : 1 <= j) : 2^(j+2) * d j = 3^(2^j) - 1 := by
  have hdiv := two_pow_divides j hj
  have hdef : d j = (3^(2^j) - 1) / 2^(j+2) := by
    simp [d]; omega
  rw [hdef]
  have : (3^(2^j) - 1) / 2^(j+2) * 2^(j+2) = 3^(2^j) - 1 := Nat.div_mul_cancel hdiv
  rw [Nat.mul_comm (2^(j+2)) ((3^(2^j) - 1) / 2^(j+2))]
  exact this

theorem two_pow_2k_mod3 (k : Nat) : (2^(2*k)) % 3 = 1 := by
  induction k with
  | zero => decide
  | succ k ih =>
    have h1 : 2 * (k + 1) = 2 * k + 2 := by omega
    rw [h1, Nat.pow_add, Nat.mul_mod, ih]

/-- **POSTULATE I, CLASS 1 — THE EVEN TOWER.**  For even `j ≥ 2`, the dual
tower's units digit IS the bridge signature: `d j ≡ 2 (mod 3)`. -/
theorem d_even_mod3 (j : Nat) (hj : 2 <= j) (heven : j % 2 = 0) : d j % 3 = 2 := by
  have hid := d_identity j (by omega)
  have hmod3 : (2^(j+2) * d j) % 3 = 2 := by
    rw [hid, three_pow_2j_minus_1_mod3 j (by omega)]
  have hk : j + 2 = 2 * ((j + 2) / 2) := by omega
  have h2pow : (2^(j+2)) % 3 = 1 := by
    rw [hk]
    exact two_pow_2k_mod3 ((j + 2) / 2)
  rw [Nat.mul_mod, h2pow, Nat.one_mul, Nat.mod_mod] at hmod3
  exact hmod3

/-- **POSTULATE I, CLASS 1 — THE BRIDGE SIGNATURE LANDS.**  For even `j ≥ 2`
the dual tower carries the ternary digit 2. -/
theorem bridge_sig_even (j : Nat) (hj : 2 <= j) (heven : j % 2 = 0) :
    hasTernaryTwo (d j) = true := by
  have h : d j % 3 = 2 := d_even_mod3 j hj heven
  rw [hasTernaryTwo.eq_def (d j)]
  have hpos : d j ≠ 0 := by
    have hid := d_identity j (by omega)
    have h3 : 0 < 3^(2^j) := three_pow_2j_pos j
    omega
  rw [if_neg hpos, if_pos h]

theorem two_pow_6_mod9 : (2^6) % 9 = 1 := by decide

theorem two_pow_6q_mod9 (q : Nat) : (2^(6*q)) % 9 = 1 := by
  induction q with
  | zero => decide
  | succ q ih =>
    have h : 6 * (q + 1) = 6 * q + 6 := by omega
    rw [h, Nat.pow_add, Nat.mul_mod, ih, two_pow_6_mod9]

theorem two_pow_5_mod9 : (2^5) % 9 = 5 := by decide

theorem two_pow_j2_mod9_j_mod6_3 (j : Nat) (hj : j % 6 = 3) :
    (2^(j+2)) % 9 = 5 := by
  have hq : j + 2 = 6 * ((j + 2) / 6) + 5 := by omega
  rw [hq, Nat.pow_add, Nat.mul_mod, two_pow_6q_mod9, two_pow_5_mod9]

theorem three_pow_2j_mod9 (j : Nat) (hj : 1 <= j) : (3^(2^j)) % 9 = 0 := by
  have h2j_ge2 : 2 <= 2^j := two_pow_ge2 j hj
  have hdiv9 : 9 ∣ 3^(2^j) := by
    refine ⟨3^(2^j - 2), ?_⟩
    have h9 : 9 = 3^2 := by decide
    rw [h9]
    calc 3^(2^j)
        = 3^((2^j - 2) + 2) := by congr 1; omega
      _ = 3^(2^j - 2) * 3^2 := Nat.pow_add 3 (2^j - 2) 2
      _ = 3^2 * 3^(2^j - 2) := Nat.mul_comm _ _
  exact Nat.mod_eq_zero_of_dvd hdiv9

theorem three_pow_2j_minus_1_mod9 (j : Nat) (hj : 1 <= j) :
    (3^(2^j) - 1) % 9 = 8 := by
  have h2j_ge2 : 2 <= 2^j := two_pow_ge2 j hj
  have h9 : 9 = 3^2 := by decide
  have hfact : 3^(2^j) = 9 * 3^(2^j - 2) := by
    rw [h9]
    calc 3^(2^j)
        = 3^((2^j - 2) + 2) := by congr 1; omega
      _ = 3^(2^j - 2) * 3^2 := Nat.pow_add 3 (2^j - 2) 2
      _ = 3^2 * 3^(2^j - 2) := Nat.mul_comm _ _
  have hqpos : 1 <= 3^(2^j - 2) := by
    have : 0 < 3^(2^j - 2) := by
      induction (2^j - 2) with
      | zero => decide
      | succ k ih => rw [Nat.pow_succ]; omega
    omega
  rw [hfact]
  have : 9 * 3^(2^j - 2) - 1 = 9 * (3^(2^j - 2) - 1) + 8 := by omega
  rw [this, Nat.add_mod, Nat.mul_mod, Nat.mod_self, Nat.zero_mul, Nat.zero_add]

theorem d_mod9_j_mod6_3 (j : Nat) (hj : 3 <= j) (hmod : j % 6 = 3) :
    d j % 9 = 7 := by
  have hj1 : 1 <= j := by omega
  have hid := d_identity j hj1
  have hmod9 : (2^(j+2) * d j) % 9 = 8 := by
    rw [hid, three_pow_2j_minus_1_mod9 j hj1]
  have h2pow : (2^(j+2)) % 9 = 5 := two_pow_j2_mod9_j_mod6_3 j hmod
  rw [Nat.mul_mod, h2pow] at hmod9
  have hrange : d j % 9 < 9 := Nat.mod_lt _ (by decide)
  have hvals : d j % 9 = 0 ∨ d j % 9 = 1 ∨ d j % 9 = 2 ∨ d j % 9 = 3 ∨
               d j % 9 = 4 ∨ d j % 9 = 5 ∨ d j % 9 = 6 ∨ d j % 9 = 7 ∨
               d j % 9 = 8 := by omega
  rcases hvals with h0 | h1 | h2 | h3 | h4 | h5 | h6 | h7 | h8
  · rw [h0] at hmod9; exact absurd hmod9 (by decide)
  · rw [h1] at hmod9; exact absurd hmod9 (by decide)
  · rw [h2] at hmod9; exact absurd hmod9 (by decide)
  · rw [h3] at hmod9; exact absurd hmod9 (by decide)
  · rw [h4] at hmod9; exact absurd hmod9 (by decide)
  · rw [h5] at hmod9; exact absurd hmod9 (by decide)
  · rw [h6] at hmod9; exact absurd hmod9 (by decide)
  · exact h7
  · rw [h8] at hmod9; exact absurd hmod9 (by decide)

/-- **POSTULATE I, CLASS 2 — THE `j ≡ 3 (mod 6)` TOWER.**  The second
universal congruence class: the signature fires at the second ternary digit
(`d j ≡ 7 (mod 9)`, i.e. `21₃`). -/
theorem bridge_sig_j_mod6_3 (j : Nat) (hj : 3 <= j) (hmod : j % 6 = 3) :
    hasTernaryTwo (d j) = true := by
  have hmod9 : d j % 9 = 7 := d_mod9_j_mod6_3 j hj hmod
  have hpos : d j ≠ 0 := by
    have hid := d_identity j (by omega)
    have h3 : 0 < 3^(2^j) := three_pow_2j_pos j
    omega
  have hdj : d j = 9 * (d j / 9) + d j % 9 := (Nat.div_add_mod (d j) 9).symm
  rw [hmod9] at hdj
  have hdiv3 : d j / 3 = 3 * (d j / 9) + 2 := by omega
  have h1 : d j % 3 = 1 := by omega
  have hne2 : ¬(d j % 3 = 2) := by omega
  rw [hasTernaryTwo.eq_def (d j), if_neg hpos, if_neg hne2]
  rw [hdiv3, hasTernaryTwo.eq_def (3 * (d j / 9) + 2)]
  have hpos2 : 3 * (d j / 9) + 2 ≠ 0 := by omega
  have hmod3 : (3 * (d j / 9) + 2) % 3 = 2 := by
    rw [Nat.add_mod, Nat.mul_mod, Nat.mod_self, Nat.zero_mul, Nat.zero_add]
  rw [if_neg hpos2, if_pos hmod3]

/-! ## §6 The valuation machinery — the depths of the two worlds -/

/-- The 2-adic depth reader (structural, `v2`). -/
def v2r (k : Nat) : Nat :=
  if k = 0 then 0
  else if k % 2 = 0 then 1 + v2r (k / 2) else 0
termination_by k
decreasing_by exact Nat.div_lt_self (by omega) (by decide : 1 < 2)

/-- The 3-adic depth reader (the ternary logarithm). -/
def ternaryLog3 (n : Nat) : Nat :=
  if n < 3 then 0
  else 1 + ternaryLog3 (n / 3)
termination_by n
decreasing_by exact Nat.div_lt_self (by omega : 0 < n) (by decide : 1 < 3)

theorem v2r_mul_three_strong : ∀ (n c : Nat), c ≤ n → v2r (3 * c) = v2r c := by
  intro n
  induction n with
  | zero =>
    intro c hc
    have hc0 : c = 0 := by omega
    subst hc0; rfl
  | succ n ih =>
    intro c hc
    by_cases hz : c = 0
    · subst hz; rfl
    · by_cases he : c % 2 = 0
      · have hc_d2 : c / 2 ≤ n := by omega
        have h3c_even : (3 * c) % 2 = 0 := by omega
        have h3c_ne0 : (3 * c) ≠ 0 := Nat.mul_ne_zero (by decide) hz
        have h3c_div2 : (3 * c) / 2 = 3 * (c / 2) := by omega
        rw [v2r.eq_def (3 * c), if_neg h3c_ne0, if_pos h3c_even, h3c_div2]
        rw [v2r.eq_def c, if_neg hz, if_pos he, ih (c/2) hc_d2]
      · have h3odd : (3 * c) % 2 ≠ 0 := by omega
        have h3c_ne0 : (3 * c) ≠ 0 := Nat.mul_ne_zero (by decide) hz
        rw [v2r.eq_def (3 * c), if_neg h3c_ne0, if_neg h3odd]
        rw [v2r.eq_def c, if_neg hz, if_neg he]

theorem v2r_mul_three (c : Nat) : v2r (3 * c) = v2r c :=
  v2r_mul_three_strong c c (by omega)

theorem v2r_mul_three_pow (a c : Nat) : v2r (3^a * c) = v2r c := by
  induction a with
  | zero => rw [Nat.pow_zero, Nat.one_mul]
  | succ a ih => rw [Nat.pow_succ, Nat.mul_comm (3^a) 3, Nat.mul_assoc, v2r_mul_three, ih]

theorem ternaryLog3_lt_of_lt_pow (n k : Nat) (hn : 0 < n) (hk : n < 3^k) :
    ternaryLog3 n < k := by
  induction k with
  | zero => simp at hk; omega
  | succ k ih =>
    by_cases h3 : n < 3
    · rw [ternaryLog3, if_pos h3]; omega
    · have hlog : ternaryLog3 n = 1 + ternaryLog3 (n / 3) := by
        rw [ternaryLog3, if_neg h3]
      rw [hlog]
      have hn3 : 0 < n / 3 := by omega
      have h3k1 : 3^(k+1) = 3 * 3^k := by rw [Nat.pow_add, Nat.pow_one, Nat.mul_comm]
      rw [h3k1] at hk
      have hn3lt : n / 3 < 3^k := by
        have hle : 3 * (n / 3) ≤ n := by omega
        omega
      have hih := ternaryLog3_lt_of_lt_pow (n / 3) k hn3 hn3lt
      omega

theorem noTernaryTwo_div (n : Nat) (hn : 0 < n) (hntt : noTernaryTwo n = true) (hmod : n % 3 ≠ 2) :
    noTernaryTwo (n / 3) = true := by
  unfold noTernaryTwo at hntt
  rw [if_neg (by omega)] at hntt
  rw [if_neg hmod] at hntt
  exact hntt

theorem three_pow_gt (k : Nat) : 3^(k+6) > 2^(k+9) := by
  induction k with
  | zero => decide
  | succ k ih =>
    have h1 : 3^(k+7) = 3 * 3^(k+6) := by
      rw [show k+7 = (k+6)+1 from by omega, Nat.pow_add, Nat.pow_one, Nat.mul_comm]
    rw [h1]
    have h2 : 3 * 3^(k+6) > 3 * 2^(k+9) := by omega
    have h3 : 3 * 2^(k+9) > 2^((k+1)+9) := by
      have hk : 2^((k+1)+9) = 2 * 2^(k+9) := by
        rw [show (k+1)+9 = (k+9)+1 from by omega, Nat.pow_add, Nat.pow_one, Nat.mul_comm]
      rw [hk]; have hx : 0 < 2^(k+9) := Nat.pow_pos (by decide); omega
    omega

/-! ## §7 The first-K scanner — the finite observation window -/

def hasTwoInFirstK (n k : Nat) : Bool :=
  if k = 0 then false
  else if n % 3 = 2 then true
  else hasTwoInFirstK (n / 3) (k - 1)
termination_by k
decreasing_by exact Nat.sub_lt (by omega) (by decide : 0 < 1)

def hasTwoInFirstKStruct : Nat → Nat → Bool
  | _, 0 => false
  | n, k+1 => if n % 3 = 2 then true else hasTwoInFirstKStruct (n / 3) k

theorem hasTwoInFirstKStruct_succ (n k : Nat) :
    hasTwoInFirstKStruct n (Nat.succ k) = (if n % 3 = 2 then true else hasTwoInFirstKStruct (n/3) k) := by rfl

theorem hasTwoInFirstK_eq_struct : ∀ (k n : Nat), hasTwoInFirstK n k = hasTwoInFirstKStruct n k := by
  intro k
  induction k using Nat.rec with
  | zero => intro n; rw [hasTwoInFirstK.eq_def n 0, if_pos rfl]; rfl
  | succ k ih =>
    intro n
    rw [hasTwoInFirstK.eq_def n (k+1), if_neg (by omega), hasTwoInFirstKStruct_succ n k]
    by_cases h2 : n % 3 = 2
    · rw [if_pos h2, if_pos h2]
    · rw [if_neg h2, if_neg h2, show (k+1 : Nat) - 1 = k from by omega, ih]

theorem powMod_correct (b e m : Nat) (hm : 1 < m) : powMod b e m = (b^e) % m := by
  induction e with
  | zero => rfl
  | succ k ih =>
    show (b * powMod b k m) % m = (b^(k+1)) % m
    rw [Nat.pow_succ, ih, Nat.mul_mod, Nat.mod_mod, Nat.mul_comm (b^k) b, ← Nat.mul_mod]

/-! ## §8 THE BRIDGE `3 = 1 + 2` — the digit-2 transport laws -/

theorem three_pow_ge_9 (p : Nat) (hp : 2 ≤ p) : 9 ≤ 3^p := by
  have h9 : (3:Nat)^2 = 9 := by decide
  calc 9 = 3^2 := h9.symm
    _ ≤ 3^p := Nat.pow_le_pow_right (by decide) hp

theorem four_lt_three_pow (p : Nat) (hp : 2 <= p) : 4 < 3^p := by
  have h9 : 9 ≤ 3^p := three_pow_ge_9 p hp; omega

/-- **THE DIGIT-TO-SCAN LAW.**  A ternary digit 2 at any position fires the
signature scan. -/
theorem hasTernaryTwo_of_digit (n : Nat) (q : Nat) (h : n / 3^q % 3 = 2) :
    hasTernaryTwo n = true := by
  induction q generalizing n with
  | zero =>
    rw [Nat.pow_zero, Nat.div_one] at h
    have hn : n ≠ 0 := by intro hnn; rw [hnn, Nat.zero_mod] at h; exact absurd h (by decide)
    rw [hasTernaryTwo.eq_def n, if_neg hn, if_pos h]
  | succ q ih =>
    have hn : n ≠ 0 := by intro hnn; rw [hnn, Nat.zero_div, Nat.zero_mod] at h; exact absurd h (by decide)
    have hkey : n / 3^(q+1) = (n / 3) / 3^q := by
      rw [show 3^(q+1) = 3 * 3^q from by rw [Nat.pow_succ]; ac_rfl, Nat.div_div_eq_div_mul]
    rw [hkey] at h
    have hih : hasTernaryTwo (n / 3) = true := ih (n / 3) h
    by_cases hmod : n % 3 = 2
    · rw [hasTernaryTwo.eq_def n, if_neg hn, if_pos hmod]
    · rw [hasTernaryTwo.eq_def n, if_neg hn, if_neg hmod]; exact hih

theorem hasTernaryTwo_pos (n : Nat) (h : hasTernaryTwo n = true) :
    ∃ p : Nat, n / 3^p % 3 = 2 := by
  induction n using Nat.strongRecOn with
  | ind n ih =>
    by_cases hn : n = 0
    · rw [hn] at h; rw [hasTernaryTwo.eq_def 0, if_pos rfl] at h; exact absurd h (by decide)
    · rw [hasTernaryTwo.eq_def n, if_neg hn] at h
      by_cases hmod : n % 3 = 2
      · exact ⟨0, by rw [Nat.pow_zero, Nat.div_one]; exact hmod⟩
      · rw [if_neg hmod] at h
        have hdiv : n / 3 < n := Nat.div_lt_self (by omega) (by decide : 1 < 3)
        obtain ⟨p, hp⟩ := ih (n / 3) hdiv h
        refine ⟨p + 1, ?_⟩
        rw [Nat.pow_succ, Nat.mul_comm (3^p) 3, ← Nat.div_div_eq_div_mul]
        exact hp

/-- **THE BRIDGE TRANSPORT `3 = 1 + 2`** (verbatim from the monolith
§BRIDGE): the ternary digits at and above position `p` are INVARIANT under
multiplication by `4` whenever the low window is a `3^p`-unit:
`(4·X)/3^p % 3 = X/3^p % 3`.  This is the exact mechanism that lets the
2-world's chart `4 = 1 + 3` transport the 3-world's signature upward. -/
theorem four_mul_preserves_digit (X p : Nat) (hp : 2 <= p) (hX_mod : X % 3^p = 1) :
    (4 * X) / 3^p % 3 = X / 3^p % 3 := by
  have hX_decomp : X = 3^p * (X / 3^p) + 1 := by
    have := Nat.div_add_mod X (3^p); rw [hX_mod] at this; omega
  have h4X : 4 * X = 3^p * (4 * (X / 3^p)) + 4 := by
    have h4 := congrArg (fun x => 4 * x) hX_decomp
    rw [Nat.mul_add] at h4
    rw [show 4 * (3^p * (X / 3^p)) = 3^p * (4 * (X / 3^p)) from by ac_rfl] at h4
    rw [h4, Nat.mul_one]
  have h4_lt : 4 < 3^p := four_lt_three_pow p hp
  have hPpos : 0 < 3^p := Nat.pow_pos (by decide)
  have hdvd : 3^p ∣ 3^p * (4 * (X / 3^p)) := ⟨4 * (X / 3^p), rfl⟩
  have hmod0 : (3^p * (4 * (X / 3^p))) % 3^p = 0 := Nat.mod_eq_zero_of_dvd hdvd
  have hmod : (3^p * (4 * (X / 3^p)) + 4) % 3^p = (4 : Nat) := by
    rw [Nat.add_mod, hmod0, Nat.zero_add, Nat.mod_mod, Nat.mod_eq_of_lt h4_lt]
  have hdm := Nat.div_add_mod (3^p * (4 * (X / 3^p)) + 4) (3^p)
  rw [hmod] at hdm
  have hcancel : 3^p * ((3^p * (4 * (X / 3^p)) + 4) / 3^p) = 3^p * (4 * (X / 3^p)) := by
    have h1 : 3^p * ((3^p * (4 * (X / 3^p)) + 4) / 3^p) + 4 = 3^p * (4 * (X / 3^p)) + 4 := hdm
    exact Nat.add_right_cancel h1
  have hdiv : (3^p * (4 * (X / 3^p)) + 4) / 3^p = 4 * (X / 3^p) :=
    Nat.mul_left_cancel hPpos hcancel
  rw [h4X, hdiv, Nat.mul_mod, show (4:Nat) % 3 = 1 from by decide, Nat.one_mul, Nat.mod_mod]

/-- **THE SIGNATURE SURVIVES THE CHART** (GST duality): the digit 2 is
invariant under multiplication by `4` — the bridge transport preserves the
signature. -/
theorem carry_manifold_survives (X p : Nat) (hp : 2 <= p) (hX_mod : X % 3^p = 1)
    (hX_digit : X / 3^p % 3 = 2) : (4 * X) / 3^p % 3 = 2 := by
  rw [four_mul_preserves_digit X p hp hX_mod, hX_digit]

/-- The transported signature fires the scan. -/
theorem carry_manifold_has_two (X p : Nat) (hp : 2 <= p) (hX_mod : X % 3^p = 1)
    (hX_digit : X / 3^p % 3 = 2) : hasTernaryTwo (4 * X) = true := by
  have h := carry_manifold_survives X p hp hX_mod hX_digit
  exact hasTernaryTwo_of_digit (4 * X) p h

/-- **THE FIRST-SIGNATURE LAW.**  The signature scan hands over the FIRST
digit-2 position, with minimality. -/
theorem hasTernaryTwo_first_pos (n : Nat) (h : hasTernaryTwo n = true) :
    ∃ q : Nat, n / 3^q % 3 = 2 ∧ ∀ p, p < q → n / 3^p % 3 ≠ 2 := by
  induction n using Nat.strongRecOn with
  | ind n ih =>
    by_cases hn : n = 0
    · rw [hn] at h; rw [hasTernaryTwo.eq_def 0, if_pos rfl] at h
      exact absurd h (by decide)
    · rw [hasTernaryTwo.eq_def n, if_neg hn] at h
      by_cases hmod : n % 3 = 2
      · refine ⟨0, ?_, ?_⟩
        · rw [Nat.pow_zero, Nat.div_one]; exact hmod
        · intro p hp; omega
      · rw [if_neg hmod] at h
        have hdiv : n / 3 < n := Nat.div_lt_self (by omega) (by decide : 1 < 3)
        obtain ⟨q, hq_d2, hq_min⟩ := ih (n / 3) hdiv h
        refine ⟨q + 1, ?_, ?_⟩
        · rw [Nat.pow_succ, Nat.mul_comm (3^q) 3, ← Nat.div_div_eq_div_mul]
          exact hq_d2
        · intro p hp
          by_cases hp0 : p = 0
          · rw [hp0, Nat.pow_zero, Nat.div_one]; exact hmod
          · have hp1 : 1 ≤ p := by omega
            have hpq : p - 1 < q := by omega
            have hkey : n / 3^p = (n / 3) / 3^(p-1) := by
              have hpow := Nat.pow_succ 3 (p-1)
              rw [show Nat.succ (p-1) = p from by omega] at hpow
              rw [hpow, Nat.mul_comm, ← Nat.div_div_eq_div_mul]
            rw [hkey]
            have := hq_min (p-1) hpq
            exact this

/-! ## §9 The kernel-checked base — the modular ground floor -/

theorem hasTwoInFirstK_imp_hasTernaryTwo (n k : Nat) (hn : n < 3^k)
    (h : hasTwoInFirstK n k = true) : hasTernaryTwo n = true := by
  revert n hn h
  induction k with
  | zero =>
    intro n hn h
    rw [Nat.pow_zero] at hn
    have hn0 : n = 0 := by omega
    rw [hn0] at h
    have hdef := hasTwoInFirstK.eq_def 0 0
    rw [if_pos rfl] at hdef
    rw [hdef] at h
    exact absurd h (by decide)
  | succ k ih =>
    intro n hn h
    have h3kp1 : 3^(k+1) = 3 * 3^k := by rw [Nat.pow_succ]; ac_rfl
    rw [h3kp1] at hn
    by_cases hn_mod3 : n % 3 = 2
    · by_cases hn0 : n = 0
      · have : ¬(n % 3 = 2) := by rw [hn0, Nat.zero_mod]; decide
        exact absurd hn_mod3 this
      · rw [hasTernaryTwo.eq_def n, if_neg hn0, if_pos hn_mod3]
    · have h_div3 : hasTwoInFirstK (n / 3) k = true := by
        have hdef := hasTwoInFirstK.eq_def n (k+1)
        rw [if_neg (by omega : ¬((k+1 : Nat) = 0))] at hdef
        rw [if_neg hn_mod3] at hdef
        rw [hdef] at h
        exact h
      have hn_div3_lt : n / 3 < 3^k := Nat.div_lt_of_lt_mul hn
      have h_div3_has := ih (n / 3) hn_div3_lt h_div3
      by_cases hn0 : n = 0
      · -- n = 0: n/3 = 0, so h_div3_has : hasTernaryTwo 0 = true. Goal: hasTernaryTwo 0 = true.
        rw [hn0]
        have hn0_div3 : n / 3 = 0 := by rw [hn0, Nat.zero_div]
        rw [hn0_div3] at h_div3_has
        exact h_div3_has
      · rw [hasTernaryTwo.eq_def n, if_neg hn0, if_neg hn_mod3]
        exact h_div3_has

-- Helper: K=16 structural check → hasTernaryTwo
theorem mod_check_K16 (a : Nat)
    (h_struct : hasTwoInFirstKStruct (powMod 4 a (3^16)) 16 = true) :
    hasTernaryTwo (4^a) = true := by
  have h_mod : hasTwoInFirstK ((4^a) % (3^16)) 16 = true := by
    rw [hasTwoInFirstK_eq_struct 16, ← powMod_correct 4 a (3^16) (by omega : 1 < 3^16)]
    exact h_struct
  have hlt : (4^a) % (3^16) < 3^16 := Nat.mod_lt _ (by omega : 0 < 3^16)
  have h_has_mod : hasTernaryTwo ((4^a) % (3^16)) = true :=
    hasTwoInFirstK_imp_hasTernaryTwo ((4^a) % (3^16)) 16 hlt h_mod
  exact mod_has_two 16 (4^a) h_has_mod

-- Helper: K=12 structural check → hasTernaryTwo
theorem mod_check_K12 (a : Nat)
    (h_struct : hasTwoInFirstKStruct (powMod 4 a (3^12)) 12 = true) :
    hasTernaryTwo (4^a) = true := by
  have h_mod : hasTwoInFirstK ((4^a) % (3^12)) 12 = true := by
    rw [hasTwoInFirstK_eq_struct 12, ← powMod_correct 4 a (3^12) (by omega : 1 < 3^12)]
    exact h_struct
  have hlt : (4^a) % (3^12) < 3^12 := Nat.mod_lt _ (by omega : 0 < 3^12)
  have h_has_mod : hasTernaryTwo ((4^a) % (3^12)) = true :=
    hasTwoInFirstK_imp_hasTernaryTwo ((4^a) % (3^12)) 12 hlt h_mod
  exact mod_has_two 12 (4^a) h_has_mod

/-- **THE KERNEL-CHECKED BASE.**  Every exponent `5 ≤ a ≤ 500` owns its
signature: the machine-checked ground floor of the bridge (seven hard
residues at K16, the easy mass at K12). -/
theorem modular_check_base (a : Nat) (ha : 5 ≤ a) (ha500 : a ≤ 500) :
    hasTernaryTwo (4^a) = true := by
  by_cases ha_hard : a = 93 ∨ a = 166 ∨ a = 237 ∨ a = 280 ∨ a = 387 ∨ a = 432 ∨ a = 496
  · rcases ha_hard with h93 | h166 | h237 | h280 | h387 | h432 | h496
    · subst h93; exact mod_check_K16 93 (by decide)
    · subst h166; exact mod_check_K16 166 (by decide)
    · subst h237; exact mod_check_K16 237 (by decide)
    · subst h280; exact mod_check_K16 280 (by decide)
    · subst h387; exact mod_check_K16 387 (by decide)
    · subst h432; exact mod_check_K16 432 (by decide)
    · subst h496; exact mod_check_K16 496 (by decide)
  · have h_easy : ∀ k < 501,
        hasTwoInFirstKStruct (powMod 4 k (3^12)) 12 = true ∨
        k = 93 ∨ k = 166 ∨ k = 237 ∨ k = 280 ∨ k = 387 ∨ k = 432 ∨ k = 496 ∨ k < 5 := by decide
    have h_result := h_easy a (by omega)
    -- a ≥ 5, a ∉ {93,166,237,280,387,432,496} → first disjunct
    rcases h_result with h_struct | h93 | h166 | h237 | h280 | h387 | h432 | h496 | hlt5
    · exact mod_check_K12 a h_struct
    · omega
    · omega
    · omega
    · omega
    · omega
    · omega
    · omega
    · omega

/-! ## §10 The period laws — the cycle structure of the 2-world chart -/

theorem four_pow_mod27 (m : Nat) : (4^m) % 27 = (4^(m % 9)) % 27 := by
  have h9 : (4^9) % 27 = 1 := by decide
  have h49q : ∀ q : Nat, (4^9)^q % 27 = 1 := by
    intro q
    induction q with
    | zero => decide
    | succ q' ih =>
      have hsucc : (4^9)^(Nat.succ q') = (4^9)^(q' + 1) := rfl
      rw [hsucc, Nat.pow_succ, Nat.mul_mod, h9, ih]
  have hmd : m = 9 * (m / 9) + m % 9 := (Nat.div_add_mod m 9).symm
  have h4m : 4^m = (4^9)^(m/9) * 4^(m%9) := by
    have h1 : 4^m = 4^(9*(m/9) + m%9) := congrArg (fun x => 4^x) hmd
    have h2 : 4^(9*(m/9) + m%9) = (4^9)^(m/9) * 4^(m%9) := by
      rw [Nat.pow_add, Nat.pow_mul]
    exact h1.trans h2
  rw [h4m, Nat.mul_mod, h49q, Nat.one_mul, Nat.mod_mod]

theorem four_pow_mod9 (a : Nat) : (4^a) % 9 = (4^(a % 3)) % 9 := by
  have h3 : (4^3) % 9 = 1 := by decide
  have h43q : ∀ q : Nat, (4^3)^q % 9 = 1 := by
    intro q
    induction q with
    | zero => decide
    | succ q' ih =>
      have hsucc : (4^3)^(Nat.succ q') = (4^3)^(q' + 1) := rfl
      rw [hsucc, Nat.pow_succ, Nat.mul_mod, h3, ih]
  have hmd : a = 3 * (a / 3) + a % 3 := (Nat.div_add_mod a 3).symm
  have h4a : 4^a = (4^3)^(a/3) * 4^(a%3) := by
    have h1 : 4^a = 4^(3*(a/3) + a%3) := congrArg (fun x => 4^x) hmd
    have h2 : 4^(3*(a/3) + a%3) = (4^3)^(a/3) * 4^(a%3) := by
      rw [Nat.pow_add, Nat.pow_mul]
    exact h1.trans h2
  rw [h4a, Nat.mul_mod, h43q, Nat.one_mul, Nat.mod_mod]

/-- **THE LEVEL-27 PERIOD LAW** — the cycle law at the depth the fourth
dimension consumes: `4^m mod 81` depends only on `m mod 27`. -/
theorem four_pow_mod81 (m : Nat) : (4^m) % 81 = (4^(m % 27)) % 81 := by
  have h27 : (4^27) % 81 = 1 := by decide
  have h427q : ∀ q : Nat, (4^27)^q % 81 = 1 := by
    intro q
    induction q with
    | zero => decide
    | succ q' ih =>
      have hsucc : (4^27)^(Nat.succ q') = (4^27)^(q' + 1) := rfl
      rw [hsucc, Nat.pow_succ, Nat.mul_mod, h27, ih]
  have hmd : m = 27 * (m / 27) + m % 27 := (Nat.div_add_mod m 27).symm
  have h4m : 4^m = (4^27)^(m/27) * 4^(m%27) := by
    have h1 : 4^m = 4^(27*(m/27) + m%27) := congrArg (fun x => 4^x) hmd
    have h2 : 4^(27*(m/27) + m%27) = (4^27)^(m/27) * 4^(m%27) := by
      rw [Nat.pow_add, Nat.pow_mul]
    exact h1.trans h2
  rw [h4m, Nat.mul_mod, h427q, Nat.one_mul, Nat.mod_mod]

/-! ## §11 The digit reader and the terminal witness layer -/

/-- The ternary digit at position `p` (root-level reader). -/
def gstDigit (R p : Nat) : Nat := R / 3^p % 3

/-- **WITNESS EXTRACTION.**  A false `noTernaryTwo` verdict hands over the
digit-two witness position: the boolean scan and the digit statement are
one object. -/
theorem no_two_false_digit_witness (n : Nat) (h : noTernaryTwo n = false) :
    ∃ p : Nat, gstDigit n p = 2 := by
  revert h
  exact Nat.strongRecOn n (fun n ih h => by
    by_cases hn : n = 0
    · subst hn
      rw [noTernaryTwo.eq_def 0, if_pos (by decide : (0:Nat) = 0)] at h
      exact absurd h (by decide)
    · rw [noTernaryTwo.eq_def n, if_neg hn] at h
      by_cases h2 : n % 3 = 2
      · refine ⟨0, ?_⟩
        show n / 3^0 % 3 = 2
        rw [Nat.pow_zero, Nat.div_one]
        exact h2
      · rw [if_neg h2] at h
        obtain ⟨p, hp⟩ := ih (n / 3)
          (Nat.div_lt_self (by omega : 0 < n) (by decide : 1 < 3)) h
        refine ⟨p + 1, ?_⟩
        show n / 3^(p+1) % 3 = 2
        rw [Nat.pow_succ, Nat.mul_comm, ← Nat.div_div_eq_div_mul]
        exact hp)

/-- **THE VERDICT-TO-DIGIT LAW.**  The boolean conjecture reading and the
digit-two witness reading are interchangeable: every failing `noTernaryTwo`
IS an exhibited digit-two position. -/
theorem omega_shadow_kill_all_of_even_conjecture
    (hConj : ∀ K : Nat, 8 ≤ K → noTernaryTwo (4^K) = false) :
    ∀ K : Nat, 8 ≤ K → ∃ p : Nat, 4^K / 3^p % 3 = 2 := by
  intro K hK
  obtain ⟨p, hp⟩ := no_two_false_digit_witness (4^K) (hConj K hK)
  exact ⟨p, hp⟩

/-- **THE DIGIT-TO-VERDICT LAW.**  Every exhibited digit-two position IS a
failing `noTernaryTwo` verdict. -/
theorem erdos_even_conjecture_of_kill_all
    (hKill : ∀ K : Nat, 8 ≤ K → ∃ p : Nat, 4^K / 3^p % 3 = 2) :
    ∀ K : Nat, 8 ≤ K → noTernaryTwo (4^K) = false := by
  intro K hK
  obtain ⟨p, hp⟩ := hKill K hK
  exact has_two_imp_not_no_two (4^K) (hasTernaryTwo_of_digit (4^K) p hp)

/-- **EVEN-WORLD VERDICT/WITNESS EQUIVALENCE.**
The Boolean no-two verdict and the explicit ternary digit-two witness are
exactly the same global statement on the even-power axis. -/
theorem erdos_even_verdict_iff_digit_witness :
    (∀ K : Nat, 8 ≤ K → noTernaryTwo (4^K) = false)
      ↔
    (∀ K : Nat, 8 ≤ K → ∃ p : Nat, 4^K / 3^p % 3 = 2) := by
  exact ⟨omega_shadow_kill_all_of_even_conjecture,
    erdos_even_conjecture_of_kill_all⟩

/-! ## §12 THE THREE WORLDS — the exponential bridge factors

(verbatim from `GSTHandwrittenBigNThreeWorldFactors`, the pure
three-world core — the operational BIG-N content stays in the source
monolith.)
-/

/-- Binary-world exponential factor. -/
def gstBinaryWorldFactorS (j : Nat) : Nat := 2^j

/-- Ternary-world exponential factor. -/
def gstTernaryWorldFactorS (j : Nat) : Nat := 3^j

/-- Mixed six-state-world exponential factor. -/
def gstMixedWorldFactorS (j : Nat) : Nat := 6^j

/-- The three exponential worlds carried as one packet. -/
@[ext] structure GSTThreeWorldExponentialPacketS where
  binary : Nat
  ternary : Nat
  mixed : Nat
  deriving Repr, DecidableEq

def gstThreeWorldExponentialPacketS (j : Nat) : GSTThreeWorldExponentialPacketS :=
  ⟨gstBinaryWorldFactorS j, gstTernaryWorldFactorS j, gstMixedWorldFactorS j⟩

/-- **THE MIXED WORLD IS NOT AN INDEPENDENT SCALE.**  At every natural depth
the mixed world is exactly the product of the binary and ternary worlds. -/
theorem gst_three_world_factor_rawS (j : Nat) :
    6^j = 2^j * 3^j := by
  have h6 : (6 : Nat) = 2 * 3 := by decide
  rw [h6, mul_pow]

/-- Named-factor form of the same exact three-world identity. -/
theorem gst_three_world_mixed_factor_exactS (j : Nat) :
    gstMixedWorldFactorS j =
      gstBinaryWorldFactorS j * gstTernaryWorldFactorS j := by
  unfold gstMixedWorldFactorS gstBinaryWorldFactorS gstTernaryWorldFactorS
  exact gst_three_world_factor_rawS j

/-- All three exponential worlds respect concatenation of information depth. -/
theorem gst_three_world_factor_addS (j k : Nat) :
    gstBinaryWorldFactorS (j+k) =
        gstBinaryWorldFactorS j * gstBinaryWorldFactorS k ∧
    gstTernaryWorldFactorS (j+k) =
        gstTernaryWorldFactorS j * gstTernaryWorldFactorS k ∧
    gstMixedWorldFactorS (j+k) =
        gstMixedWorldFactorS j * gstMixedWorldFactorS k := by
  simp [gstBinaryWorldFactorS, gstTernaryWorldFactorS,
    gstMixedWorldFactorS, pow_add]

/-- Componentwise multiplication of two three-world packets. -/
def gstThreeWorldPacketMul
    (A B : GSTThreeWorldExponentialPacketS) :
    GSTThreeWorldExponentialPacketS :=
  ⟨A.binary * B.binary,
    A.ternary * B.ternary,
    A.mixed * B.mixed⟩

/-- Identity packet at depth zero. -/
theorem gstThreeWorldPacket_zero :
    gstThreeWorldExponentialPacketS 0 =
      ⟨1,1,1⟩ := by
  rfl

/-- **THREE-WORLD PACKET SEMIGROUP.**
Concatenating information depths is exactly componentwise packet
multiplication. -/
theorem gstThreeWorldPacket_add
    (j k : Nat) :
    gstThreeWorldExponentialPacketS (j+k) =
      gstThreeWorldPacketMul
        (gstThreeWorldExponentialPacketS j)
        (gstThreeWorldExponentialPacketS k) := by
  apply GSTThreeWorldExponentialPacketS.ext <;>
    simp [gstThreeWorldExponentialPacketS,
      gstThreeWorldPacketMul,
      gstBinaryWorldFactorS,
      gstTernaryWorldFactorS,
      gstMixedWorldFactorS,
      pow_add]

/-- The mixed component remains exactly the binary×ternary composite at every
packet depth. -/
theorem gstThreeWorldPacket_mixed_exact
    (j : Nat) :
    (gstThreeWorldExponentialPacketS j).mixed =
      (gstThreeWorldExponentialPacketS j).binary *
        (gstThreeWorldExponentialPacketS j).ternary := by
  exact gst_three_world_mixed_factor_exactS j

/-- Literal joined prefix from the handwritten equation.  Every completed
microscopic world contributes the aligned factor `2^j * 3^j`, weighted by
the five-unit full SURVIVE mass. -/
def gstHandwrittenThreeWorldJoinedPrefixS (K : Nat) : Nat :=
  5 * Finset.sum (Finset.range K)
    (fun j => gstBinaryWorldFactorS j * gstTernaryWorldFactorS j)

/-- **THE THREE-WORLD COLLAPSE.**  The three exponent worlds collapse
exactly to the mixed six-world geometric prefix: the finite
equation-level `2^j ∪ 3^j ∪ 6^j` identity
`5 · Σ_{j<K} 2^j·3^j = 6^K − 1`. -/
theorem gst_handwritten_three_world_joined_prefix_closedS (K : Nat) :
    gstHandwrittenThreeWorldJoinedPrefixS K = 6^K - 1 := by
  unfold gstHandwrittenThreeWorldJoinedPrefixS
  unfold gstBinaryWorldFactorS gstTernaryWorldFactorS
  induction K with
  | zero => simp
  | succ K ih =>
      rw [Finset.sum_range_succ, Nat.mul_add, ih]
      rw [← gst_three_world_factor_rawS K, Nat.pow_succ]
      have hp : 0 < 6^K := Nat.pow_pos (by decide)
      omega

/-! ## §13 Receipts — the comparator face of the Cardinal Worlds -/

#check d_identity
#check bridge_sig_even
#check bridge_sig_j_mod6_3
#check four_mul_preserves_digit
#check carry_manifold_survives
#check modular_check_base
#check four_pow_mod81
#check no_two_false_digit_witness
#check omega_shadow_kill_all_of_even_conjecture
#check erdos_even_conjecture_of_kill_all
#check erdos_even_verdict_iff_digit_witness
#check gst_three_world_factor_rawS
#check gstThreeWorldPacketMul
#check gstThreeWorldPacket_add
#check gstThreeWorldPacket_mixed_exact
#check gst_handwritten_three_world_joined_prefix_closedS

#print axioms d_identity
#print axioms bridge_sig_even
#print axioms bridge_sig_j_mod6_3
#print axioms four_mul_preserves_digit
#print axioms carry_manifold_survives
#print axioms modular_check_base
#print axioms four_pow_mod81
#print axioms no_two_false_digit_witness
#print axioms omega_shadow_kill_all_of_even_conjecture
#print axioms erdos_even_conjecture_of_kill_all
#print axioms erdos_even_verdict_iff_digit_witness
#print axioms gst_three_world_factor_rawS
#print axioms gstThreeWorldPacket_add
#print axioms gstThreeWorldPacket_mixed_exact
#print axioms gst_handwritten_three_world_joined_prefix_closedS
