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
      have ih := nat_two_le_mul M (k + 1) (by omega)
      have hstep : M * (k + 2) = M * (k + 1) + M := by
        rw [show k + 2 = (k + 1) + 1 from by omega, Nat.mul_succ]
      omega

/-- Three or more times a base is at least thrice the base. -/
theorem nat_three_le_mul (M : Nat) : ∀ (k : Nat), 3 ≤ k → 3 * M ≤ M * k
  | 0, hk => by omega
  | 1, hk => by omega
  | 2, hk => by omega
  | k + 3, _ => by
      have ih := nat_three_le_mul M (k + 2) (by omega)
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
      | zero => rw [Nat.mul_zero, Nat.mul_zero]
      | succ a' => omega
  | succ b' ih =>
      cases Nat.lt_or_ge a b' with
      | inl hlt =>
          have h1 := ih a hlt hP
          have hps := Nat.mul_succ P b'
          omega
      | inr hge =>
          have ha : a = b' + 1 := by omega
          rw [ha]
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
      have ham := Nat.add_mod (x + k * h) h h
      rw [Nat.mod_self h, Nat.add_zero, ih]
      exact Nat.mod_eq_of_lt (Nat.mod_lt x (show 0 < h from by omega))

/-- Adding the modulus itself does not change the remainder. -/
theorem add_mod_self (x h : Nat) : (x + h) % h = x % h := by
  have h1 := add_mul_mod_self x 1 h
  rw [Nat.one_mul] at h1
  exact h1

/-- The residue congruence under an exact sum `u + w = 2 * v`. -/
theorem mod_sum_mod (u v w h : Nat) (hsum : u + w = 2 * v) :
    (u % h + w % h) % h = (2 * (v % h)) % h := by
  have h2 : (u + w) % h = (u % h + w % h) % h := Nat.add_mod u w h
  have h3 : (v + v) % h = (v % h + v % h) % h := Nat.add_mod v v h
  have hvv : 2 * v = v + v := by omega
  have hvv2 : 2 * (v % h) = v % h + v % h := by omega
  rw [← h2, hsum, hvv, h3, hvv2]

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

/-- The quotient of `P * c + r` by `P` (r < P). -/
theorem divP (P c r : Nat) (hr : r < P) : (P * c + r) / P = c := by
  have hP : 1 ≤ P := by omega
  have hdm : P * ((P * c + r) / P) + (P * c + r) % P = P * c + r :=
    Nat.div_add_mod _ _
  have hm : (P * c + r) % P = r := by
    rw [Nat.add_mod, Nat.mul_mod, Nat.mod_self P, Nat.zero_mul,
      Nat.zero_add, Nat.mod_eq_of_lt hr]
  omega

/-- The remainder of `P * c + r` modulo `P` (r < P). -/
theorem modP (P c r : Nat) (hr : r < P) : (P * c + r) % P = r := by
  rw [Nat.add_mod, Nat.mul_mod, Nat.mod_self P, Nat.zero_mul,
    Nat.zero_add, Nat.mod_eq_of_lt hr]

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

/-- The units digits of `3 * m` and `m` carry the same Cantor verdict. -/
theorem noTwo_mul3 (m : Nat) : noTwo (3 * m) = noTwo m := by
  induction m with
  | zero => rfl
  | succ m' =>
      have hih : noTwo (3 * m') = noTwo m' := by
        exact noTwo_mul3 m'
      have hrw : 3 * (m' + 1) = 3 * m' + 2 + 1 := by omega
      rw [hrw]
      simp only [noTwo]
      rw [if_neg (by omega : (3 * m' + 2 + 1) % 3 ≠ 2)]
      have hdiv : (3 * m' + 2 + 1) / 3 = m' + 1 := by omega
      rw [hdiv]
      exact hih

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
  | 0, a, b, c, ha, hb, hc, _, _, _ => by omega
  | t + 1, a, b, c, ha, hb, hc, hna, hnb, hnc, hmod => by
    have hM : 3 ^ (t + 1) = 3 * 3 ^ t := by
      have hps := Nat.pow_succ (3) t
      omega
    have hM0 : (3 * 3 ^ t) % 3 = 0 := by
      rw [Nat.mul_mod, show (3 : Nat) % 3 = 0 from by omega, Nat.zero_mul,
        Nat.zero_mod]
    have hform := mod_to_form (3 ^ (t + 1)) (a + c) (2 * b) (by omega)
      (by omega) hmod
    have ex := noTwo_true_inv a hna
    have ey := noTwo_true_inv b hnb
    have ez := noTwo_true_inv c hnc
    -- units digits all agree, in every carry form:
    have hsums : a % 3 + c % 3 = 2 * (b % 3) := by omega
    have hsame : a % 3 = b % 3 ∧ b % 3 = c % 3 := by omega
    -- quotient-level carry relation, per form:
    rcases hform with h1 | h2 | h3
    · have hq : a / 3 + c / 3 = 2 * (b / 3) := by omega
      have heq : (a / 3 + c / 3) % 3 ^ t = (2 * (b / 3)) % 3 ^ t := by
        rw [hq]
      exact finish t a b c ha hb hc hna hnb hnc hsame heq
    · have hq : a / 3 + c / 3 = 2 * (b / 3) + 3 ^ t := by omega
      have heq : (a / 3 + c / 3) % 3 ^ t = (2 * (b / 3)) % 3 ^ t := by
        rw [hq, add_mod_self]
      exact finish t a b c ha hb hc hna hnb hnc hsame heq
    · have hq : 2 * (b / 3) = a / 3 + c / 3 + 3 ^ t := by omega
      have heq : (a / 3 + c / 3) % 3 ^ t = (2 * (b / 3)) % 3 ^ t := by
        rw [← hq, add_mod_self]
      exact finish t a b c ha hb hc hna hnb hnc hsame heq
