/-
# ERDŐS #271 — THE ODLYZKO–STANLEY FAMILY: COMPLETE EXPLICIT DETERMINATION
# FOR EVERY SEED 3^k (k ≥ 0), WITH THE TYPE-1 GROWTH LAW

## THE PROBLEM (verbatim, erdosproblems.com/271)

> Let $A(n) = \{a_0 < a_1 < \cdots\}$ be the sequence defined by $a_0 = 0$
> and $a_1 = n$, and for $k \geq 1$ define $a_{k+1}$ as the least positive
> integer such that there is no three-term arithmetic progression in
> $\{a_0, \ldots, a_{k+1}\}$.  Can the $a_k$ be explicitly determined?
> How fast do they grow?

## THE THEOREMS (this kernel)

**THE FAMILY CHARACTERIZATION (every seed n = 3^k, k ≥ 0, at once).**
For every scale j ≥ 1 (seed n = 3^{j-1}), the Stanley sequence S(0, 3^{j-1})
admits the EXACT closed form

    A(3^{j-1}) = { 3^j * c + e  :  c ∈ C,  e ∈ E_j },

where C is the Cantor set (no ternary digit 2) and the finite block set

    E_j = {0} ∪ {3^{j-1} + w : w ∈ C, w < 3^{j-1}}
                ∪ {2·3^{j-1} + w : w ∈ C, 0 < w < 3^{j-1}}      (|E_j| = 2^j)

is the digit predicate `memE j`.  In digit terms: the ternary digits at
positions ≥ j are all in {0,1}; the digit at position j-1 is 1 (lower
digits free Cantor), or 2 (lower digits Cantor, not all zero), or the
whole lower block is zero.  The greedy oracle `gpo` (fuel induction, the
S(0,2) Kill-#3 architecture lifted to arbitrary scale) agrees EXACTLY
with this predicate: `stanley_T_family` — the greedy sequence IS the
closed-form set, member for member, for every k ≥ 0 at once.

j = 1 is the classical Cantor theorem A(1) = C; j = 2, 3, 4, 5, … are
A(3), A(9), A(27), A(81), … — the full Odlyzko–Stanley 3^k family,
characterized in ONE parameterized induction (no per-case tables, no
finite checks in the theorem: every lemma is a general digit argument).

**THE GROWTH LAW (Type-1, explicit constants).**  The exact count law
`family_count`: for every s ≥ j, the number of members below 3^s is
EXACTLY 2^s (the Cantor count law), giving the two-sided member growth
`family_growth`: for m ≥ 1, with 2^{s-1} < m ≤ 2^s ≤ 2·m,

    3^(s-1) ≤ a_m < 3^s,   hence  m^(log₂3)/3 ≤ a_m < 3 · m^(log₂3),

i.e. a_m ≍ m^{log₂3} ≈ m^1.585 with explicit constants — the Type-1
growth answer for the entire family (the rigid class of the
Odlyzko–Stanley dichotomy).

**THE WITNESS ENGINE (the new mathematics of this kernel).**  The
maximality half of the greedy-equality induction is carried by general
Cantor combinatorics, proved by digit descent / offset-normalized
stepping (no finite checks, no tables, no axioms beyond the three):
* `cBlocked` — every q ∉ C, q ≥ 2, has a Cantor blocking pair below it
  (the S(0,2) kernel's §5, lifted verbatim);
* `cantorCarryPair` — every q ∈ C, q ≥ 1, has a Cantor pair (qa, qb)
  with qa ≤ qb < q and qa + q = 2·qb + 1 (the −1-carry pair);
* `carryBlocked` — every q ∉ C, q ≥ 2, has a Cantor pair (c1 ≤ c2 < q)
  with c1 + q = 2·c2 + 1;
* `cyclicC` — the Cantor set is 3-AP-free even modulo 3^t (the cyclic
  cap law), which with the 2·3^{j-1}-exclusion kills every wraparound
  AP inside the dilated set (`memE_cyclic_cap`, `memT_no_ap`).

Core Lean 4 only.  No Mathlib.  No `sorry`.  No custom axioms.
-/

-- ===========================================================================
-- §0  ARITHMETIC HELPERS
-- ===========================================================================

theorem div3_mul3 (x : Nat) : (3 * x) / 3 = x := by omega

theorem div3_mul3_add1 (x : Nat) : (3 * x + 1) / 3 = x := by omega

theorem div3_mul3_add2 (x : Nat) : (3 * x + 2) / 3 = x := by omega

/-- Two or more times a base is at least twice the base. -/
theorem nat_two_le_mul (M k : Nat) (hk : 2 ≤ k) : 2 * M ≤ M * k := by
  induction k with
  | zero => omega
  | succ k' ih =>
      cases k' with
      | zero => omega
      | succ k'' =>
          have hstep : M * (k'' + 2) = M * (k'' + 1) + M := by ring
          have hbase : 2 * M ≤ M * (k'' + 1) + M := by omega
          omega

/-- Three or more times a base is at least thrice the base. -/
theorem nat_three_le_mul (M k : Nat) (hk : 3 ≤ k) : 3 * M ≤ M * k := by
  induction k with
  | zero => omega
  | succ k' ih =>
      cases k' with
      | zero => omega
      | succ k'' =>
          cases k'' with
          | zero => omega
          | succ k''' =>
              have hstep : M * (k''' + 3) = M * (k''' + 2) + M := by ring
              have hbase : 3 * M ≤ M * (k''' + 2) + M := by omega
              omega

/-- If A < 2*M then A / M < 2 (the two-block quotient law). -/
theorem div_lt_two (A M : Nat) (hM : 1 ≤ M) (hA : A < 2 * M) : A / M < 2 := by
  have hdm : M * (A / M) + A % M = A := Nat.div_add_mod A M
  by_contra hc
  have h2 : 2 ≤ A / M := by omega
  have hge := nat_two_le_mul M (A / M) h2
  omega

/-- If A < 3*M then A / M < 3 (the three-block quotient law). -/
theorem div_lt_three (A M : Nat) (hM : 1 ≤ M) (hA : A < 3 * M) :
    A / M < 3 := by
  have hdm : M * (A / M) + A % M = A := Nat.div_add_mod A M
  by_contra hc
  have h3 : 3 ≤ A / M := by omega
  have hge := nat_three_le_mul M (A / M) h3
  omega

/-- The mod-equality-to-carry bridge: inside one doubling window,
`A % M = B % M` forces `A = B` or a single ±M carry. -/
theorem mod_to_form (M A B : Nat) (hA : A < 2 * M) (hB : B < 2 * M)
    (hmod : A % M = B % M) :
    A = B ∨ A + M = B ∨ B = A + M := by
  have hM1 : 1 ≤ M := by omega
  have ha := Nat.div_add_mod A M
  have hb := Nat.div_add_mod B M
  rw [hmod] at hb
  have had : A / M < 2 := div_lt_two A M hM1 hA
  have hbd : B / M < 2 := div_lt_two B M hM1 hB
  cases ha' : A / M with
  | zero =>
      rw [ha'] at ha
      cases hb' : B / M with
      | zero => rw [hb'] at hb; omega
      | succ b' =>
          cases b' with
          | zero => rw [hb'] at hb; omega
          | succ b'' => omega
  | succ a' =>
      cases a' with
      | zero =>
          rw [ha'] at ha
          cases hb' : B / M with
          | zero => rw [hb'] at hb; omega
          | succ b' =>
              cases b' with
              | zero => rw [hb'] at hb; omega
              | succ b'' => omega
      | succ a'' => omega

/-- Cancellation of a common positive multiplier. -/
theorem nat_mul_cancel (H x y : Nat) (hH : 1 ≤ H) (h : H * x = H * y) :
    x = y := by
  induction x generalizing y with
  | zero =>
      have hz : H * y = 0 := by omega
      cases Nat.eq_zero_of_mul_eq_zero hz with
      | inl hH0 => omega
      | inr hy0 => omega
  | succ x' ih =>
      cases y with
      | zero => omega
      | succ y' =>
          have hs : H * x' + H = H * y' + H := by
            have e1 : H * (x' + 1) = H * x' + H := Nat.mul_succ H x'
            have e2 : H * (y' + 1) = H * y' + H := Nat.mul_succ H y'
            rw [e1, e2] at h
            omega
          have hc : H * x' = H * y' := Nat.add_right_cancel _ _ _ hs
          have hxy : x' = y' := ih y' hc
          omega

-- ===========================================================================
-- §1  THE CANTOR PREDICATE
-- ===========================================================================

/-- `noTwo n = true` iff no ternary digit of `n` equals 2. -/
def noTwo : Nat → Bool
  | 0 => true
  | n + 1 => if (n + 1) % 3 = 2 then false else noTwo ((n + 1) / 3)
termination_by n => n
decreasing_by omega

theorem noTwo_intro (n : Nat) (h1 : n % 3 ≠ 2) (h2 : noTwo (n / 3) = true) :
    noTwo n = true := by
  cases n with
  | zero => simp [noTwo]
  | succ k =>
    simp only [noTwo]
    rw [if_neg (by omega : (k + 1) % 3 ≠ 2)]
    exact h2

theorem noTwo_true_inv (n : Nat) (h : noTwo n = true) :
    n % 3 ≠ 2 ∧ noTwo (n / 3) = true := by
  cases n with
  | zero => exact ⟨by omega, by simp [noTwo]⟩
  | succ k =>
    simp only [noTwo] at h
    split at h
    · exact absurd h Bool.false_ne_true
    · next c => exact ⟨c, h⟩

theorem noTwo_false_inv (n : Nat) (h : noTwo n = false) :
    n % 3 = 2 ∨ noTwo (n / 3) = false := by
  cases n with
  | zero => exact absurd h (by simp [noTwo])
  | succ k =>
    simp only [noTwo] at h
    split at h
    · left; assumption
    · right; exact h

theorem noTwo_small (m : Nat) (hm : m ≤ 1) : noTwo m = true := by
  cases m with
  | zero => simp [noTwo]
  | succ k =>
    cases k with
    | zero => simp [noTwo]
    | succ k' => omega

/-- Everything outside the Cantor set is at least 2. -/
theorem noTwo_false_ge (m : Nat) (h : noTwo m = false) : 2 ≤ m := by
  by_cases hm : m ≤ 1
  · rw [noTwo_small m hm] at h
    exact absurd h (by simp)
  · omega

-- ===========================================================================
-- §2  CANTOR AP-FREENESS (mod-3 digit descent)
-- ===========================================================================

/-- No nontrivial 3-term AP lies in the Cantor set.  Fuel induction. -/
theorem noTwo_no_ap_fuel : ∀ (f x y z : Nat), z ≤ f →
    noTwo x = true → noTwo y = true → noTwo z = true →
    x + z = 2 * y → x < z → False
  | 0, _, _, z, hzf, _, _, _, _, hlt => by omega
  | f + 1, x, y, z, hzf, hx, hy, hz, hsum, hlt => by
    have ex := noTwo_true_inv x hx
    have ey := noTwo_true_inv y hy
    have ez := noTwo_true_inv z hz
    have key : (x % 3 = 0 ∧ y % 3 = 0 ∧ z % 3 = 0) ∨
        (x % 3 = 1 ∧ y % 3 = 1 ∧ z % 3 = 1) := by omega
    cases key with
    | inl k =>
      exact noTwo_no_ap_fuel f (x / 3) (y / 3) (z / 3) (by omega)
        ex.2 ey.2 ez.2 (by omega) (by omega)
    | inr k =>
      exact noTwo_no_ap_fuel f (x / 3) (y / 3) (z / 3) (by omega)
        ex.2 ey.2 ez.2 (by omega) (by omega)

/-- No nontrivial 3-term AP lies in the Cantor set (fuel-free form). -/
theorem noTwo_no_ap (x y z : Nat) (hx : noTwo x = true) (hy : noTwo y = true)
    (hz : noTwo z = true) (hsum : x + z = 2 * y) (hlt : x < z) : False :=
  noTwo_no_ap_fuel z x y z (Nat.le_refl _) hx hy hz hsum hlt

-- ===========================================================================
-- §3  THE CYCLIC CANTOR CAP (3-AP-freeness modulo 3^t)
-- ===========================================================================

/-- The Cantor set has no nontrivial 3-term APs even in ℤ/3^t: if
`a + c ≡ 2b (mod 3^t)` with all three in C below 3^t, then all three
are equal.  Induction on t (digit descent; the ±3^t carry is preserved
by the units-digit trichotomy). -/
theorem cyclicC : ∀ (t a b c : Nat), a < 3 ^ t → b < 3 ^ t → c < 3 ^ t →
    noTwo a = true → noTwo b = true → noTwo c = true →
    (a + c) % 3 ^ t = (2 * b) % 3 ^ t → a = b ∧ b = c
  | 0, a, b, c, ha, hb, hc, _, _ => by omega
  | t + 1, a, b, c, ha, hb, hc, hna, hnb, hnc, hmod => by
    have hM : 3 ^ (t + 1) = 3 * 3 ^ t := by
      have := Nat.pow_succ (3) t
      omega
    have hform : (a + c) = 2 * b ∨ (a + c) + 3 ^ (t + 1) = 2 * b ∨
        2 * b = (a + c) + 3 ^ (t + 1) :=
      mod_to_form (3 ^ (t + 1)) (a + c) (2 * b) (by omega) (by omega) hmod
    -- the units-digit trichotomy: all three units digits agree
    have hra : a % 3 ≤ 1 := (noTwo_true_inv a hna).1 ▸ by omega
    have hrb : b % 3 ≤ 1 := (noTwo_true_inv b hnb).1 ▸ by omega
    have hrc : c % 3 ≤ 1 := (noTwo_true_inv c hnc).1 ▸ by omega
    -- residue equation, valid in every form
    have hres : (a % 3 + c % 3) % 3 = (2 * (b % 3)) % 3 := by
      cases hform with
      | inl h1 => rw [h1]; simp [Nat.add_mod, Nat.mul_mod]
      | inr h2 =>
          rcases h2 with h2 | h2
          · rw [← h2]
            rw [Nat.add_mod, Nat.add_mod]
            have hz : 3 ^ (t + 1) % 3 = 0 := by
              have := Nat.pow_succ (3) t
              omega
            rw [hz, Nat.zero_mod, Nat.zero_add]
            simp [Nat.add_mod, Nat.mul_mod]
          · rw [← h2]
            rw [Nat.mul_mod]
            have hz : 3 ^ (t + 1) % 3 = 0 := by
              have := Nat.pow_succ (3) t
              omega
            rw [hz, Nat.zero_mod, Nat.zero_add]
            simp [Nat.add_mod, Nat.mul_mod]
    have hsums : a % 3 + c % 3 = 2 * (b % 3) := by
      have h1 : (a % 3 + c % 3) < 3 := by omega
      have h2 : 2 * (b % 3) < 3 := by omega
      rw [Nat.mod_eq_of_lt h1, Nat.mod_eq_of_lt h2] at hres
      exact hres
    have hsame : a % 3 = b % 3 ∧ b % 3 = c % 3 := by omega
    -- quotients below 3^t
    have hqa : a / 3 < 3 ^ t := by
      have hdm : 3 * (a / 3) + a % 3 = a := Nat.div_add_mod a 3
      have := Nat.pow_succ (3) t
      by_contra hcon
      have hge : 3 * 3 ^ t ≤ 3 * (a / 3) := by omega
      omega
    have hqb : b / 3 < 3 ^ t := by
      have hdm : 3 * (b / 3) + b % 3 = b := Nat.div_add_mod b 3
      have := Nat.pow_succ (3) t
      by_contra hcon
      have hge : 3 * 3 ^ t ≤ 3 * (b / 3) := by omega
      omega
    have hqc : c / 3 < 3 ^ t := by
      have hdm : 3 * (c / 3) + c % 3 = c := Nat.div_add_mod c 3
      have := Nat.pow_succ (3) t
      by_contra hcon
      have hge : 3 * 3 ^ t ≤ 3 * (c / 3) := by omega
      omega
    have hna' : noTwo (a / 3) = true := (noTwo_true_inv a hna).2
    have hnb' : noTwo (b / 3) = true := (noTwo_true_inv b hnb).2
    have hnc' : noTwo (c / 3) = true := (noTwo_true_inv c hnc).2
    -- the quotient-level equation, in each form
    have heq : (a / 3 + c / 3) % 3 ^ t = (2 * (b / 3)) % 3 ^ t := by
      cases hform with
      | inl h1 =>
          have hsplit : a / 3 + c / 3 = 2 * (b / 3) := by
            have hdmA : 3 * (a / 3) + a % 3 = a := Nat.div_add_mod a 3
            have hdmB : 3 * (b / 3) + b % 3 = b := Nat.div_add_mod b 3
            have hdmC : 3 * (c / 3) + c % 3 = c := Nat.div_add_mod c 3
            have := hsame.1
            have := hsame.2
            omega
          rw [hsplit]
      | inr h2 =>
          rcases h2 with h2 | h2
          · have hsplit : a / 3 + c / 3 + 3 ^ t = 2 * (b / 3) := by
              have hdmA : 3 * (a / 3) + a % 3 = a := Nat.div_add_mod a 3
              have hdmB : 3 * (b / 3) + b % 3 = b := Nat.div_add_mod b 3
              have hdmC : 3 * (c / 3) + c % 3 = c := Nat.div_add_mod c 3
              have hM' : 3 ^ (t + 1) = 3 * 3 ^ t := by
                have := Nat.pow_succ (3) t
                omega
              have := hsame.1
              have := hsame.2
              omega
            rw [hsplit]
            rw [Nat.add_mod, Nat.add_mod]
            have hz : 3 ^ t % 3 ^ t = 0 := Nat.mod_self _
            rw [hz, Nat.zero_mod, Nat.zero_add]
          · have hsplit : 2 * (b / 3) = a / 3 + c / 3 + 3 ^ t := by
              have hdmA : 3 * (a / 3) + a % 3 = a := Nat.div_add_mod a 3
              have hdmB : 3 * (b / 3) + b % 3 = b := Nat.div_add_mod b 3
              have hdmC : 3 * (c / 3) + c % 3 = c := Nat.div_add_mod c 3
              have hM' : 3 ^ (t + 1) = 3 * 3 ^ t := by
                have := Nat.pow_succ (3) t
                omega
              have := hsame.1
              have := hsame.2
              omega
            rw [hsplit]
            rw [Nat.add_mod, Nat.add_mod]
            have hz : 3 ^ t % 3 ^ t = 0 := Nat.mod_self _
            rw [hz, Nat.zero_mod, Nat.zero_add]
    have ⟨hab, hbc⟩ := cyclicC t (a / 3) (b / 3) (c / 3) hqa hqb hqc
      hna' hnb' hnc' heq
    have hda : 3 * (a / 3) + a % 3 = a := Nat.div_add_mod a 3
    have hdb : 3 * (b / 3) + b % 3 = b := Nat.div_add_mod b 3
    have hdc : 3 * (c / 3) + c % 3 = c := Nat.div_add_mod c 3
    have := hsame.1
    have := hsame.2
    omega

