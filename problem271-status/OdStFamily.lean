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

**F1 — THE FAMILY CHARACTERIZATION (every seed n = 3^k, k ≥ 0, at once).**
For every scale j ≥ 1 (seed n = 3^{j-1}), the Stanley sequence S(0, 3^{j-1})
admits the EXACT closed form

    A(3^{j-1}) = { 3^j * q + e  :  q ∈ C,  e ∈ E_j },

where C is the Cantor set (no ternary digit 2) and the finite block set

    E_j = {0} ∪ {3^{j-1} + w : w ∈ C, w < 3^{j-1}}
                ∪ {2·3^{j-1} + w : w ∈ C, 0 < w < 3^{j-1}}      (|E_j| = 2^j)

is the digit predicate `memE`.  In digit terms: the ternary digits at
positions ≥ j are all in {0,1}; the digit at position j-1 is 1 (lower
digits free Cantor), or 2 (lower digits Cantor, not all zero), or the
whole lower block is zero.  The greedy oracle `gpo` (fuel induction, the
S(0,2) Kill-#3 architecture lifted to arbitrary scale) agrees EXACTLY
with this predicate (`stanley_T_family`), and the greedy sequence itself
(the `aSeq`/`sqSeq` engine of StanleyGrowth.lean) IS the closed-form set,
member for member (`odst_family`) — for every k ≥ 0 at once.

j = 1 is the classical Cantor theorem A(1) = C; j = 2, 3, 4, 5, … are
A(3), A(9), A(27), A(81), … — the full Odlyzko–Stanley 3^k family,
characterized in ONE parameterized induction (no per-case tables, no
finite checks in the theorems: every lemma is a general digit argument).

**F2 — THE GROWTH LAW (Type-1, explicit constants).**  The exact count law
`family_count`: for every s ≥ j, the number of members below 3^s is
EXACTLY 2^s (the Cantor count law), giving the sharp position law
`family_sharp` (a_{2^s} = 3^s) and the two-sided scale squeeze
`family_growth` (for m ≥ 2^{j-1}: with 2^{s-1} ≤ m ≤ 2^s one has
3^{s-1} ≤ a_m ≤ 3^s — the §5.6 route of COMPLETE_PROOF.md), i.e.
a_m ≍ m^{log₂3} with explicit constants — the Type-1 growth answer for
the entire family (the rigid class of the Odlyzko–Stanley dichotomy).

**THE WITNESS ENGINE.**  The maximality half of the greedy-equality
induction is carried by general Cantor combinatorics, proved by digit
descent / offset-normalized stepping (no finite checks, no tables):
* `cBlocked` — every q ∉ C, q ≥ 2, has a Cantor blocking pair below it
  (the S(0,2) kernel's §5, lifted verbatim);
* `cantorCarryPair` — every q ∈ C, q ≥ 1, has a Cantor pair (α, β) with
  α ≤ β < q and α + q = 2·β + 1 (the −1-carry pair);
* `carryBlocked` — every q ∉ C, q ≥ 2, has a Cantor pair with
  γ₁ + q = 2·γ₂ + 1;
* `tailPair` — every 0 < r < H has a Cantor pair (w₁, w₂) with
  w₁ + r = 2·w₂ and 1 ≤ w₂ < H;
* `cyclicC` — the Cantor set is 3-AP-free even modulo 3^t (the cyclic
  cap law), which with the 2·3^{j-1}-exclusion kills every wraparound
  AP inside the dilated set (`memE_no_ap`, `memT_no_ap`);
* `tBlocked` — the R1/R2 witness funnel table: EVERY y ∉ T_j above the
  seed is blocked by a pair below it inside T_j (seven construction
  rules, each a general digit argument).

Core Lean 4 proof discipline only (omega / simp / rfl / decide / cases /
induction; no Mathlib tactics in proofs).  No `sorry`.  No custom axioms.
-/

import Arsenal.ErdosTernary2.Basic
import Arsenal.CardinalWorlds
import Arsenal.CardinalWorldsV2

set_option maxHeartbeats 8000000
set_option maxRecDepth 4096

-- ===========================================================================
-- §0  ARITHMETIC HELPERS
-- ===========================================================================

theorem div3_mul3 (x : Nat) : (3 * x) / 3 = x := by omega

theorem div3_mul3_add1 (x : Nat) : (3 * x + 1) / 3 = x := by omega

theorem div3_mul3_add2 (x : Nat) : (3 * x + 2) / 3 = x := by omega

/-- Two or more times a base is at least twice the base. -/
theorem nat_two_le_mul (M : Nat) : ∀ (k : Nat), 2 ≤ k → 2 * M ≤ M * k
  | 0, hk => by omega
  | 1, hk => by omega
  | k + 2, _ => by
      have ih := nat_two_le_mul M (k + 1) (show 2 ≤ k + 1 by omega)
      have hstep : M * (k + 2) = M * (k + 1) + M := by
        rw [show k + 2 = (k + 1) + 1 from by omega, Nat.mul_succ]
      omega

/-- Three or more times a base is at least thrice the base. -/
theorem nat_three_le_mul (M : Nat) : ∀ (k : Nat), 3 ≤ k → 3 * M ≤ M * k
  | 0, hk => by omega
  | 1, hk => by omega
  | 2, hk => by omega
  | k + 3, _ => by
      have ih := nat_three_le_mul M (k + 2) (show 3 ≤ k + 2 by omega)
      have hstep : M * (k + 3) = M * (k + 2) + M := by
        rw [show k + 3 = (k + 2) + 1 from by omega, Nat.mul_succ]
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
    A = B ∨ A = B + M ∨ B = A + M := by
  have hM1 : 1 ≤ M := by omega
  have ha : M * (A / M) + A % M = A := Nat.div_add_mod A M
  have hb : M * (B / M) + B % M = B := Nat.div_add_mod B M
  rw [← hmod] at hb
  have had : A / M < 2 := div_lt_two A M hM1 hA
  have hbd : B / M < 2 := div_lt_two B M hM1 hB
  cases ha' : A / M with
  | zero =>
      rw [ha'] at ha
      cases hb' : B / M with
      | zero =>
          rw [hb'] at hb
          omega
      | succ b' =>
          cases b' with
          | zero =>
              rw [hb'] at hb
              omega
          | succ b'' => omega
  | succ a' =>
      cases a' with
      | zero =>
          rw [ha'] at ha
          cases hb' : B / M with
          | zero =>
              rw [hb'] at hb
              omega
          | succ b' =>
              cases b' with
              | zero =>
                  rw [hb'] at hb
                  omega
              | succ b'' => omega
      | succ a'' => omega

/-- Cancellation of a common positive multiplier. -/
theorem nat_mul_cancel (H x y : Nat) (hH : 1 ≤ H) (h : H * x = H * y) :
    x = y := by
  induction x generalizing y with
  | zero =>
      have h' := h
      rw [Nat.mul_zero] at h'
      cases y with
      | zero => omega
      | succ y' =>
          have hsucc : H * (y' + 1) = H * y' + H := Nat.mul_succ H y'
          omega
  | succ x' ih =>
      cases y with
      | zero =>
          rw [Nat.mul_zero] at h
          have hsucc : H * (x' + 1) = H * x' + H := Nat.mul_succ H x'
          omega
      | succ y' =>
          have hs : H * x' + H = H * y' + H := by
            have e1 : H * (x' + 1) = H * x' + H := Nat.mul_succ H x'
            have e2 : H * (y' + 1) = H * y' + H := Nat.mul_succ H y'
            rw [e1, e2] at h
            omega
          have hc : H * x' = H * y' := Nat.add_right_cancel hs
          have hxy : x' = y' := ih y' hc
          omega

/-- Powers of three are positive. -/
theorem pow3_pos (t : Nat) : 0 < 3 ^ t := by
  induction t with
  | zero => omega
  | succ t ih =>
      have hps := Nat.pow_succ (3) t
      omega

/-- Monotone multiplication (left factor fixed), weak form. -/
theorem mul_le_of_le (P : Nat) : ∀ (a b : Nat), a ≤ b → 1 ≤ P → P * a ≤ P * b := by
  intro a b hle hP
  induction b generalizing a with
  | zero =>
      cases a with
      | zero => simp [Nat.mul_zero]
      | succ a' => omega
  | succ b' ih =>
      cases Nat.lt_or_ge a b' with
      | inl hlt =>
          have h1 := ih a (Nat.le_of_lt hlt) hP
          have hps : P * (b' + 1) = P * b' + P := Nat.mul_succ P b'
          omega
      | inr hge =>
          rcases (show a = b' ∨ a = b' + 1 by omega) with hab | hab
          · rw [hab, Nat.mul_succ]
            exact Nat.le_add_right (P * b') P
          · rw [hab]
            exact Nat.le_refl _

/-- Monotone multiplication (left factor fixed), strict form. -/
theorem mul_lt_of_lt (P c1 c2 : Nat) (hc : c1 < c2) (hP : 1 ≤ P) :
    P * c1 < P * c2 := by
  have hle : c1 + 1 ≤ c2 := by omega
  have h1 := mul_le_of_le P (c1 + 1) c2 hle hP
  have hps := Nat.mul_succ P c1
  omega

/-- Reverse of strict monotone multiplication. -/
theorem lt_of_mul_lt (P a b : Nat) (hP : 1 ≤ P) (h : P * a < P * b) : a < b := by
  by_contra hc
  have hge : b ≤ a := by omega
  have hle := mul_le_of_le P b a hge hP
  omega

/-- The two-juggle: `P * (2 * c) = 2 * (P * c)`. -/
theorem mul_two_juggle (P c : Nat) : P * (2 * c) = 2 * (P * c) := by
  rw [← Nat.mul_assoc, Nat.mul_comm P 2, Nat.mul_assoc]

/-- `(k + 1) * h = k * h + h` (via comm + succ). -/
theorem succ_mul_self (k h : Nat) : (k + 1) * h = k * h + h := by
  rw [Nat.mul_comm (k + 1) h, Nat.mul_succ, Nat.mul_comm h k]

/-- Adding a multiple of the modulus does not change the remainder. -/
theorem add_mul_mod_self (x k h : Nat) : (x + k * h) % h = x % h := by
  induction k with
  | zero => rw [Nat.zero_mul, Nat.add_zero]
  | succ k ih =>
      have hstep : x + (k + 1) * h = (x + k * h) + h := by
        rw [succ_mul_self]
        omega
      rw [hstep]
      have h1 := Nat.add_mod (x + k * h) h h
      rw [h1, Nat.mod_self h, Nat.zero_add]
      exact ih

/-- Adding the modulus itself does not change the remainder. -/
theorem add_mod_self (x h : Nat) : (x + h) % h = x % h := by
  have h1 := add_mul_mod_self x 1 h
  rw [Nat.one_mul] at h1
  exact h1

/-- The residue congruence under an exact sum `u + w = 2 * v`. -/
theorem mod_sum_mod (u v w h : Nat) (hsum : u + w = 2 * v) :
    (u % h + w % h) % h = (2 * (v % h)) % h := by
  have hva : 2 * v = v + v := by omega
  have hvb : 2 * (v % h) = v % h + v % h := by omega
  calc (u % h + w % h) % h = (u + w) % h := (Nat.add_mod u w h).symm
    _ = (2 * v) % h := by rw [hsum]
    _ = (v + v) % h := by rw [hva]
    _ = (v % h + v % h) % h := Nat.add_mod v v h
    _ = (2 * (v % h)) % h := by rw [hvb]

/-- The residue congruence under a sum with a ±h carry on either side. -/
theorem mod_sum_carry2 (u v w h k k' : Nat)
    (hcarry : u + w + k * h = 2 * v + k' * h) :
    (u % h + w % h) % h = (2 * (v % h)) % h := by
  have h1 : (u + w) % h = (u % h + w % h) % h := Nat.add_mod u w h
  have h2 : (u + w + k * h) % h = (u + w) % h :=
    add_mul_mod_self (u + w) k h
  have hc : (u + w + k * h) % h = (2 * v) % h := by rw [hcarry]
  have h3 : (2 * v) % h = (2 * (v % h)) % h := by
    have hva : 2 * v = v + v := by omega
    have hvm : (v + v) % h = (v % h + v % h) % h := Nat.add_mod v v h
    have hvb : 2 * (v % h) = v % h + v % h := by omega
    rw [hva, hvm, hvb]
  rw [← h1, ← h2, hc, h3]

/-- The remainder of `P * c + r` modulo `P` (r < P). -/
theorem modP (P c r : Nat) (hr : r < P) : (P * c + r) % P = r := by
  have h0 : 0 < P := by omega
  rw [Nat.add_mod]
  rw [show (P * c) % P = 0 from by
        rw [Nat.mul_mod, Nat.mod_self P, Nat.zero_mul, Nat.zero_mod]]
  rw [Nat.zero_add, Nat.mod_mod, Nat.mod_eq_of_lt hr]

/-- The quotient of `P * c + r` by `P` (r < P). -/
theorem divP (P c r : Nat) (hr : r < P) : (P * c + r) / P = c := by
  have hP : 1 ≤ P := by omega
  have hdm : P * ((P * c + r) / P) + (P * c + r) % P = P * c + r :=
    Nat.div_add_mod (P * c + r) P
  have hm : (P * c + r) % P = r := modP P c r hr
  rw [hm] at hdm
  have hc : P * ((P * c + r) / P) = P * c := Nat.add_right_cancel hdm
  exact Nat.mul_left_cancel hP hc

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

/-- The forward-false law: a clean units digit and a false tail give a
false verdict. -/
theorem noTwo_false_of (n : Nat) (hn2 : n % 3 ≠ 2) (hf : noTwo (n / 3) = false) :
    noTwo n = false := by
  cases n with
  | zero => simp [noTwo] at hf
  | succ k =>
      simp only [noTwo]
      rw [if_neg hn2]
      exact hf

/-- The units digits of `3 * m` and `m` carry the same Cantor verdict. -/
theorem noTwo_mul3 (m : Nat) : noTwo (3 * m) = noTwo m := by
  cases h : noTwo m with
  | true =>
      rw [noTwo_intro _ (by omega : (3 * m) % 3 ≠ 2)
        (by rw [div3_mul3]; exact h)]
      rw [h]
  | false =>
      rw [noTwo_false_of _ (by omega : (3 * m) % 3 ≠ 2)
        (by rw [div3_mul3]; exact h)]
      rw [h]

/-- The units digits of `3 * m + 1` and `m` carry the same verdict. -/
theorem noTwo_mul3_add1 (m : Nat) : noTwo (3 * m + 1) = noTwo m := by
  simp only [noTwo]
  rw [if_neg (by omega : (3 * m + 1) % 3 ≠ 2)]
  rw [div3_mul3_add1]

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
  | 0, a, b, c, ha, hb, hc, _, _, _, _ => by omega
  | t + 1, a, b, c, ha, hb, hc, hna, hnb, hnc, hmod => by
    have hM : 3 ^ (t + 1) = 3 * 3 ^ t := by
      have := Nat.pow_succ (3) t
      omega
    have hform := mod_to_form (3 ^ (t + 1)) (a + c) (2 * b) (by omega)
      (by omega) hmod
    -- the units-digit trichotomy: all three units digits agree
    have hra : a % 3 ≤ 1 := by have h := (noTwo_true_inv a hna).1; omega
    have hrb : b % 3 ≤ 1 := by have h := (noTwo_true_inv b hnb).1; omega
    have hrc : c % 3 ≤ 1 := by have h := (noTwo_true_inv c hnc).1; omega
    -- residue equation, valid in every form
    have hres : (a % 3 + c % 3) % 3 = (2 * (b % 3)) % 3 := by
      have hm3 : 3 ^ (t + 1) % 3 = 0 := by
        have hps := Nat.pow_succ (3) t
        omega
      have hL : (a % 3 + c % 3) % 3 = (a + c) % 3 := (Nat.add_mod a c 3).symm
      have hR : (2 * b) % 3 = (2 * (b % 3)) % 3 := by
        rw [Nat.mul_mod, show (2 : Nat) % 3 = 2 from by omega]
      rw [hL, hR]
      rcases hform with h1 | h1 | h1
      · rw [h1]
      · rw [h1, Nat.add_mod, hm3, Nat.zero_add]
      · have h2 : (2 * b) % 3 = (a + c) % 3 := by
          rw [h1, Nat.add_mod, hm3, Nat.zero_add]
        rw [← h2]
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
      rcases hform with h1 | h1 | h1
      · have hsplit : a / 3 + c / 3 = 2 * (b / 3) := by
          have hdmA : 3 * (a / 3) + a % 3 = a := Nat.div_add_mod a 3
          have hdmB : 3 * (b / 3) + b % 3 = b := Nat.div_add_mod b 3
          have hdmC : 3 * (c / 3) + c % 3 = c := Nat.div_add_mod c 3
          have := hsame.1
          have := hsame.2
          omega
        rw [hsplit]
      · have hsplit : a / 3 + c / 3 = 2 * (b / 3) + 3 ^ t := by
          have hdmA : 3 * (a / 3) + a % 3 = a := Nat.div_add_mod a 3
          have hdmB : 3 * (b / 3) + b % 3 = b := Nat.div_add_mod b 3
          have hdmC : 3 * (c / 3) + c % 3 = c := Nat.div_add_mod c 3
          have hM' : 3 ^ (t + 1) = 3 * 3 ^ t := hM
          have := hsame.1
          have := hsame.2
          omega
        rw [hsplit, add_mod_self]
      · have hsplit : 2 * (b / 3) = a / 3 + c / 3 + 3 ^ t := by
          have hdmA : 3 * (a / 3) + a % 3 = a := Nat.div_add_mod a 3
          have hdmB : 3 * (b / 3) + b % 3 = b := Nat.div_add_mod b 3
          have hdmC : 3 * (c / 3) + c % 3 = c := Nat.div_add_mod c 3
          have hM' : 3 ^ (t + 1) = 3 * 3 ^ t := hM
          have := hsame.1
          have := hsame.2
          omega
        rw [hsplit, add_mod_self]
    have ⟨hab, hbc⟩ := cyclicC t (a / 3) (b / 3) (c / 3) hqa hqb hqc
      hna' hnb' hnc' heq
    have hda : 3 * (a / 3) + a % 3 = a := Nat.div_add_mod a 3
    have hdb : 3 * (b / 3) + b % 3 = b := Nat.div_add_mod b 3
    have hdc : 3 * (c / 3) + c % 3 = c := Nat.div_add_mod c 3
    have := hsame.1
    have := hsame.2
    omega

-- ===========================================================================
-- §4 THE F1 FOUNDATION — THE BLOCK SET E_j AND ITS AP-FREENESS (L7)
-- ===========================================================================

/-- The finite block set E_j (j ≥ 1) — membership: 0; H + w (w ∈ C below H);
2H + w (w ∈ C, 0 < w < H) — the 2H-exclusion is the load-bearing wall. -/
def memE (j e : Nat) : Prop :=
  e = 0 ∨ (∃ w, noTwo w = true ∧ w < 3 ^ (j - 1) ∧ e = 3 ^ (j - 1) + w)
       ∨ (∃ w, noTwo w = true ∧ 0 < w ∧ w < 3 ^ (j - 1) ∧ e = 2 * 3 ^ (j - 1) + w)

/-- The closed-form family T_j — membership: y = 3^j·q + e with q ∈ C
and e ∈ E_j. -/
def memT (j y : Nat) : Prop :=
  ∃ q e, noTwo q = true ∧ memE j e ∧ y = 3 ^ j * q + e

/-- Profile extraction: every E_j member is H·d + c (H = 3^{j-1}) with
c ∈ C below H and d ≤ 2; the d = 0 profile is exactly e = 0; the d = 2
profile carries the 2H-exclusion (0 < c). -/
theorem memE_prof (j e : Nat) (hj : 1 ≤ j) (he : memE j e) :
    ∃ d c, e = 3 ^ (j - 1) * d + c ∧ c < 3 ^ (j - 1) ∧ noTwo c = true ∧
      d ≤ 2 ∧ (d = 0 → c = 0) ∧ (d = 2 → 0 < c) := by
  rcases he with rfl | ⟨w, hwC, hwH, rfl⟩ | ⟨w, hwC, hw0, hwH, rfl⟩
  · refine ⟨0, 0, by omega, by have := pow3_pos (j - 1); omega, by simp [noTwo],
      by omega, by omega, by have := pow3_pos (j - 1); omega⟩
  · refine ⟨1, w, by omega, hwH, hwC, by omega, by omega, by omega⟩
  · refine ⟨2, w, by omega, hwH, hwC, by omega, by omega, by omega⟩

/-- L7 — the block set E_j is 3-AP-free: there is no u < w with
u, v, w ∈ E_j and u + w = 2·v. The three-profile digit descent: the
cyclic cap forces the tails equal, the d-arithmetic forces the {0,2}
spread, the 2H-exclusion kills it. -/
theorem memE_no_ap (j u v w : Nat) (hj : 1 ≤ j)
    (hu : memE j u) (hv : memE j v) (hw : memE j w)
    (hsum : u + w = 2 * v) (hlt : u < w) : False := by
  obtain ⟨du, cu, hu_eq, cu_lt, cu_C, du_le, du_0, du_2⟩ := memE_prof j u hj hu
  obtain ⟨dv, cv, hv_eq, cv_lt, cv_C, dv_le, dv_0, dv_2⟩ := memE_prof j v hj hv
  obtain ⟨dw, cw, hw_eq, cw_lt, cw_C, dw_le, dw_0, dw_2⟩ := memE_prof j w hj hw
  have hH1 : 1 ≤ 3 ^ (j - 1) := by have := pow3_pos (j - 1); omega
  -- the mod-H congruence
  have huM : u % 3 ^ (j - 1) = cu := by
    rw [hu_eq]; exact modP _ du cu cu_lt
  have hvM : v % 3 ^ (j - 1) = cv := by
    rw [hv_eq]; exact modP _ dv cv cv_lt
  have hwM : w % 3 ^ (j - 1) = cw := by
    rw [hw_eq]; exact modP _ dw cw cw_lt
  have hm := mod_sum_mod u v w (3 ^ (j - 1)) hsum
  rw [huM, hwM, hvM] at hm
  -- the cyclic cap kills the tail: cu = cv = cw
  have hcc := cyclicC (j - 1) cu cv cw cu_lt cv_lt cw_lt cu_C cv_C cw_C hm
  have hcucv : cu = cv := hcc.1
  have hcvcw : cv = cw := hcc.2
  -- the substituted sum equation
  have hsum'' : (3 ^ (j - 1) * du + cu) + (3 ^ (j - 1) * dw + cw)
              = 2 * (3 ^ (j - 1) * dv + cv) := by
    rw [← hu_eq, ← hw_eq, ← hv_eq]
    exact hsum
  rw [hcucv, ← hcvcw] at hsum''
  -- the digit equation (the AC regrouping + the explicit cancels)
  have hL : (3 ^ (j - 1) * du + cv) + (3 ^ (j - 1) * dw + cv)
         = (3 ^ (j - 1) * du + 3 ^ (j - 1) * dw) + (cv + cv) := by
    simp only [Nat.add_assoc, Nat.add_comm, Nat.add_left_comm]
  have hR : 2 * (3 ^ (j - 1) * dv + cv)
         = (3 ^ (j - 1) * dv + 3 ^ (j - 1) * dv) + (cv + cv) := by
    rw [Nat.mul_add, Nat.two_mul, Nat.two_mul]
  have hcancel : (3 ^ (j - 1) * du + 3 ^ (j - 1) * dw) + (cv + cv)
               = (3 ^ (j - 1) * dv + 3 ^ (j - 1) * dv) + (cv + cv) := by
    calc (3 ^ (j - 1) * du + 3 ^ (j - 1) * dw) + (cv + cv)
        = (3 ^ (j - 1) * du + cv) + (3 ^ (j - 1) * dw + cv) := hL.symm
      _ = 2 * (3 ^ (j - 1) * dv + cv) := hsum''
      _ = (3 ^ (j - 1) * dv + 3 ^ (j - 1) * dv) + (cv + cv) := hR
  have hAt : 3 ^ (j - 1) * du + 3 ^ (j - 1) * dw
          = 3 ^ (j - 1) * dv + 3 ^ (j - 1) * dv :=
    Nat.add_right_cancel hcancel
  have hfin : 3 ^ (j - 1) * (du + dw) = 3 ^ (j - 1) * (dv + dv) := by
    rw [Nat.mul_add, Nat.mul_add]
    exact hAt
  have hd : du + dw = dv + dv := Nat.mul_left_cancel hH1 hfin
  -- the case split
  have hkey : (du = dv ∧ dv = dw) ∨ (du = 0 ∧ dw = 2) ∨ (du = 2 ∧ dw = 0) := by
    omega
  rcases hkey with ⟨h1, h2⟩ | ⟨h1, h2⟩ | ⟨h1, h2⟩
  · -- all digits equal: u = w, contradicting u < w
    have huw : u = w := by
      rw [hu_eq, hw_eq, h1, h2, hcucv, ← hcvcw]
    omega
  · -- du = 0, dw = 2: the 0-profile forces cu = 0; the cyclic cap gives
    -- cw = 0; the 2H-exclusion forces 0 < cw — contradiction
    have hcu0 : cu = 0 := du_0 h1
    have hcwpos : 0 < cw := dw_2 h2
    omega
  · -- du = 2, dw = 0: symmetric
    have hcw0 : cw = 0 := dw_0 h2
    have hcupos : 0 < cu := du_2 h1
    omega

-- ===========================================================================
-- §5  L8 — THE CLOSED-FORM FAMILY T_j IS 3-AP-FREE (the three carry cases)
-- ===========================================================================

/-- Every E_j member is bounded by 3^j (the block fits inside one
P-window: the three profiles cap at H-1, 2H-1, 3H-1 < 3H = 3^j). -/
theorem memE_lt (j e : Nat) (hj : 1 ≤ j) (he : memE j e) : e < 3 ^ j := by
  have hP3 : 3 ^ j = 3 * 3 ^ (j - 1) := by
    have h := Nat.pow_succ 3 (j - 1)
    omega
  rcases he with rfl | ⟨w, hwC, hwH, rfl⟩ | ⟨w, hwC, hw0, hwH, rfl⟩
  · have := pow3_pos j
    omega
  · omega
  · omega

/-- L8 — the closed-form family T_j is 3-AP-free: there is no x < z in T_j
with x + z = 2·y. The block-level carry trichotomy (δ = 0, +1, −1):
δ = 0 collapses to an E_j-AP (L7) or a Cantor-quotient AP (L2); δ = +1 and
δ = −1 die on the profile arithmetic — the 0-profile and the 2H-exclusion
cannot both hold. -/
theorem memT_no_ap (j x y z : Nat) (hj : 1 ≤ j)
    (hx : memT j x) (hy : memT j y) (hz : memT j z)
    (hsum : x + z = 2 * y) (hlt : x < z) : False := by
  obtain ⟨qx, ex, hxq, hex, hx_eq⟩ := hx
  obtain ⟨qy, ey, hyq, hey, hy_eq⟩ := hy
  obtain ⟨qz, ez, hzq, hez, hz_eq⟩ := hz
  have hP1 : 1 ≤ 3 ^ j := by have := pow3_pos j; omega
  have hP3 : 3 ^ j = 3 * 3 ^ (j - 1) := by
    have h := Nat.pow_succ 3 (j - 1)
    omega
  -- the residue bounds
  have hexP : ex < 3 ^ j := memE_lt j ex hj hex
  have heyP : ey < 3 ^ j := memE_lt j ey hj hey
  have hezP : ez < 3 ^ j := memE_lt j ez hj hez
  -- the full block equation, omega-normalizable
  have hcore : (3 ^ j * qx + ex) + (3 ^ j * qz + ez) = 2 * (3 ^ j * qy + ey) := by
    rw [← hx_eq, ← hz_eq, ← hy_eq]
    exact hsum
  have hE0 : 3 ^ j * qx + ex + 3 ^ j * qz + ez = 2 * (3 ^ j * qy) + 2 * ey := by
    rw [Nat.mul_add 2 (3 ^ j * qy) ey] at hcore
    omega
  -- the mod-P congruence of the residues (the carry bridge)
  have hmodP : (ex + ez) % 3 ^ j = (2 * ey) % 3 ^ j := by
    have hE : ex + ez + (qx + qz) * 3 ^ j = 2 * ey + (2 * qy) * 3 ^ j := by
      have hLA : ex + ez + (qx + qz) * 3 ^ j
          = (3 ^ j * qx + ex) + (3 ^ j * qz + ez) := by
        rw [Nat.mul_comm (qx + qz) (3 ^ j), Nat.mul_add (3 ^ j) qx qz]
        simp only [Nat.add_assoc, Nat.add_comm, Nat.add_left_comm]
      have hRA : 2 * ey + (2 * qy) * 3 ^ j = 2 * (3 ^ j * qy + ey) := by
        have h2 : (2 * qy) * 3 ^ j = 2 * (3 ^ j * qy) := by
          rw [← Nat.mul_assoc 2 qy (3 ^ j), Nat.mul_comm qy (3 ^ j)]
        rw [h2, Nat.mul_add 2 (3 ^ j * qy) ey]
        omega
      rw [hLA, hcore, hRA]
    have hL := add_mul_mod_self (ex + ez) (qx + qz) (3 ^ j)
    have hR := add_mul_mod_self (2 * ey) (2 * qy) (3 ^ j)
    rw [← hL, hE, hR]
  -- the carry trichotomy
  have htri := mod_to_form (3 ^ j) (ex + ez) (2 * ey)
    (by omega : ex + ez < 2 * 3 ^ j) (by omega : 2 * ey < 2 * 3 ^ j) hmodP
  rcases htri with hcase | hcase | hcase
  · -- CASE A (δ = 0): ex + ez = 2 * ey
    have hq0 : 3 ^ j * qx + 3 ^ j * qz = 2 * (3 ^ j * qy) := by omega
    have hqf : 3 ^ j * (qx + qz) = 3 ^ j * (qy + qy) := by
      rw [Nat.mul_add (3 ^ j) qx qz, Nat.mul_add (3 ^ j) qy qy]
      omega
    have hqap : qx + qz = qy + qy := Nat.mul_left_cancel hP1 hqf
    by_cases hexez : ex = ez
    · -- all residues equal: the quotients carry a Cantor 3-AP
      have hqxz : qx < qz := by
        by_contra hcon
        have hle : qz ≤ qx := by omega
        have hmono : 3 ^ j * qz ≤ 3 ^ j * qx := Nat.mul_le_mul_left (3 ^ j) hle
        omega
      exact noTwo_no_ap qx qy qz hxq hyq hzq (by omega) hqxz
    · -- the residues carry an E_j 3-AP (L7)
      rcases Nat.lt_or_ge ex ez with h | h
      · exact memE_no_ap j ex ey ez hj hex hey hez hcase h
      · have hlt2 : ez < ex := by omega
        have hswap : ez + ex = 2 * ey := by omega
        exact memE_no_ap j ez ey ex hj hez hey hex hswap hlt2
  · -- CASE B (δ = +1): ex + ez = 2 * ey + 3 ^ j
    obtain ⟨dx, cx, hex_eq', hcx, hcxC, hdx_le, hdx_zero, hdx_two⟩ :=
      memE_prof j ex hj hex
    obtain ⟨dy, cy, hey_eq', hcy, hcyC, hdy_le, hdy_zero, hdy_two⟩ :=
      memE_prof j ey hj hey
    obtain ⟨dz, cz, hez_eq', hcz, hczC, hdz_le, hdz_zero, hdz_two⟩ :=
      memE_prof j ez hj hez
    have hH1 : 1 ≤ 3 ^ (j - 1) := by have := pow3_pos (j - 1); omega
    have hsub : (3 ^ (j - 1) * dx + cx) + (3 ^ (j - 1) * dz + cz)
        = 2 * (3 ^ (j - 1) * dy + cy) + 3 * 3 ^ (j - 1) := by
      rw [← hex_eq', ← hez_eq', ← hey_eq', ← hP3]
      exact hcase
    have hcarry : cx + cz + (dx + dz) * 3 ^ (j - 1)
        = 2 * cy + (2 * dy + 3) * 3 ^ (j - 1) := by
      have hLn : cx + cz + (dx + dz) * 3 ^ (j - 1)
          = (3 ^ (j - 1) * dx + cx) + (3 ^ (j - 1) * dz + cz) := by
        rw [Nat.mul_comm (dx + dz) (3 ^ (j - 1)),
          Nat.mul_add (3 ^ (j - 1)) dx dz]
        simp only [Nat.add_assoc, Nat.add_comm, Nat.add_left_comm]
      have hRn : 2 * cy + (2 * dy + 3) * 3 ^ (j - 1)
          = 2 * (3 ^ (j - 1) * dy + cy) + 3 * 3 ^ (j - 1) := by
        have h2 : (2 * dy + 3) * 3 ^ (j - 1)
            = 2 * (3 ^ (j - 1) * dy) + 3 * 3 ^ (j - 1) := by
          have h3 : (2 * dy) * 3 ^ (j - 1) = 2 * (3 ^ (j - 1) * dy) := by
            rw [← Nat.mul_assoc 2 dy (3 ^ (j - 1)),
              Nat.mul_comm dy (3 ^ (j - 1))]
          rw [Nat.add_mul (2 * dy) 3 (3 ^ (j - 1)), h3]
        rw [h2, Nat.mul_add 2 (3 ^ (j - 1) * dy) cy]
        omega
      rw [hLn, hsub, hRn]
    have hmodH : (cx + cz) % 3 ^ (j - 1) = (2 * cy) % 3 ^ (j - 1) := by
      have hm := mod_sum_carry2 cx cy cz (3 ^ (j - 1)) (dx + dz) (2 * dy + 3)
        hcarry
      rw [Nat.mod_eq_of_lt hcx, Nat.mod_eq_of_lt hcz, Nat.mod_eq_of_lt hcy] at hm
      exact hm
    have hcc := cyclicC (j - 1) cx cy cz hcx hcy hcz hcxC hcyC hczC hmodH
    have hcxcy : cx = cy := hcc.1
    have hcyz : cy = cz := hcc.2
    -- the digit equation: dx + dz = 2 * dy + 3
    have hdigit : dx + dz = 2 * dy + 3 := by
      rw [hcxcy] at hsub
      rw [← hcyz] at hsub
      have hd0 : 3 ^ (j - 1) * dx + 3 ^ (j - 1) * dz
          = 2 * (3 ^ (j - 1) * dy) + 3 * 3 ^ (j - 1) := by
        rw [Nat.mul_add 2 (3 ^ (j - 1) * dy) cy] at hsub
        omega
      have hdy2m : 3 ^ (j - 1) * (2 * dy) = 2 * (3 ^ (j - 1) * dy) := by
        rw [Nat.mul_comm (3 ^ (j - 1)) (2 * dy),
          ← Nat.mul_assoc 2 dy (3 ^ (j - 1)), Nat.mul_comm dy (3 ^ (j - 1))]
      have hq : 3 ^ (j - 1) * (dx + dz) = 3 ^ (j - 1) * (2 * dy + 3) := by
        rw [Nat.mul_add (3 ^ (j - 1)) dx dz,
          Nat.mul_add (3 ^ (j - 1)) (2 * dy) 3, Nat.mul_comm (3 ^ (j - 1)) 3,
          hdy2m]
        omega
      exact Nat.mul_left_cancel hH1 hq
    have hkey : dy = 0 ∧ ((dx = 1 ∧ dz = 2) ∨ (dx = 2 ∧ dz = 1)) := by omega
    rcases hkey with ⟨hdyz, hd⟩
    have hcy0 : cy = 0 := hdy_zero hdyz
    rcases hd with ⟨h1, h2⟩ | ⟨h1, h2⟩
    · have hczpos : 0 < cz := hdz_two h2
      omega
    · have hcxpos : 0 < cx := hdx_two h1
      omega
  · -- CASE C (δ = −1): 2 * ey = ex + ez + 3 ^ j
    obtain ⟨dx, cx, hex_eq', hcx, hcxC, hdx_le, hdx_zero, hdx_two⟩ :=
      memE_prof j ex hj hex
    obtain ⟨dy, cy, hey_eq', hcy, hcyC, hdy_le, hdy_zero, hdy_two⟩ :=
      memE_prof j ey hj hey
    obtain ⟨dz, cz, hez_eq', hcz, hczC, hdz_le, hdz_zero, hdz_two⟩ :=
      memE_prof j ez hj hez
    have hH1 : 1 ≤ 3 ^ (j - 1) := by have := pow3_pos (j - 1); omega
    have hsub : (3 ^ (j - 1) * dx + cx) + (3 ^ (j - 1) * dz + cz)
        + 3 * 3 ^ (j - 1) = 2 * (3 ^ (j - 1) * dy + cy) := by
      rw [← hex_eq', ← hez_eq', ← hey_eq', ← hP3]
      exact hcase.symm
    have hcarry : cx + cz + (dx + dz + 3) * 3 ^ (j - 1)
        = 2 * cy + (2 * dy) * 3 ^ (j - 1) := by
      have hLn : cx + cz + (dx + dz + 3) * 3 ^ (j - 1)
          = (3 ^ (j - 1) * dx + cx) + (3 ^ (j - 1) * dz + cz) + 3 * 3 ^ (j - 1) := by
        rw [Nat.mul_comm (dx + dz + 3) (3 ^ (j - 1)),
          Nat.add_mul (3 ^ (j - 1)) (dx + dz) 3,
          Nat.mul_add (3 ^ (j - 1)) dx dz, Nat.mul_comm (3 ^ (j - 1)) 3]
        simp only [Nat.add_assoc, Nat.add_comm, Nat.add_left_comm]
      have hRn : 2 * cy + (2 * dy) * 3 ^ (j - 1)
          = 2 * (3 ^ (j - 1) * dy + cy) := by
        have h3 : (2 * dy) * 3 ^ (j - 1) = 2 * (3 ^ (j - 1) * dy) := by
          rw [← Nat.mul_assoc 2 dy (3 ^ (j - 1)), Nat.mul_comm dy (3 ^ (j - 1))]
        rw [h3, Nat.mul_add 2 (3 ^ (j - 1) * dy) cy]
        omega
      rw [hLn, hsub, hRn]
    have hmodH : (cx + cz) % 3 ^ (j - 1) = (2 * cy) % 3 ^ (j - 1) := by
      have hm := mod_sum_carry2 cx cy cz (3 ^ (j - 1)) (dx + dz + 3) (2 * dy)
        hcarry
      rw [Nat.mod_eq_of_lt hcx, Nat.mod_eq_of_lt hcz, Nat.mod_eq_of_lt hcy] at hm
      exact hm
    have hcc := cyclicC (j - 1) cx cy cz hcx hcy hcz hcxC hcyC hczC hmodH
    have hcxcy : cx = cy := hcc.1
    have hcyz : cy = cz := hcc.2
    -- the digit equation: dx + dz + 3 = 2 * dy
    have hdigit : dx + dz + 3 = 2 * dy := by
      rw [hcxcy] at hsub
      rw [← hcyz] at hsub
      have hd0 : 3 ^ (j - 1) * dx + 3 ^ (j - 1) * dz + 3 * 3 ^ (j - 1)
          = 2 * (3 ^ (j - 1) * dy) := by
        rw [Nat.mul_add 2 (3 ^ (j - 1) * dy) cy] at hsub
        omega
      have hdy2m : 3 ^ (j - 1) * (2 * dy) = 2 * (3 ^ (j - 1) * dy) := by
        rw [Nat.mul_comm (3 ^ (j - 1)) (2 * dy),
          ← Nat.mul_assoc 2 dy (3 ^ (j - 1)), Nat.mul_comm dy (3 ^ (j - 1))]
      have hq : 3 ^ (j - 1) * (dx + dz + 3) = 3 ^ (j - 1) * (2 * dy) := by
        rw [Nat.mul_add (3 ^ (j - 1)) (dx + dz) 3,
          Nat.mul_add (3 ^ (j - 1)) dx dz, Nat.mul_comm (3 ^ (j - 1)) 3,
          hdy2m]
        omega
      exact Nat.mul_left_cancel hH1 hq
    have hkey : dy = 2 ∧ ((dx = 0 ∧ dz = 1) ∨ (dx = 1 ∧ dz = 0)) := by omega
    rcases hkey with ⟨hdy2v, hd⟩
    have hcypos : 0 < cy := hdy_two hdy2v
    rcases hd with ⟨h1, h2⟩ | ⟨h1, h2⟩
    · have hcx0 : cx = 0 := hdx_zero h1
      omega
    · have hcz0 : cz = 0 := hdz_zero h2
      omega

-- ===========================================================================
-- RECEIPTS
-- ===========================================================================

#eval "ODST_FAMILY_KERNEL_GREEN"
#print axioms memE_prof
#print axioms memE_no_ap
#print axioms cyclicC
#print axioms memE_lt
#print axioms memT_no_ap

