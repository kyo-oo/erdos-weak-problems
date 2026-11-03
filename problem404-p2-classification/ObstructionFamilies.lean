/-
# ERDŐS #404 — THE p = 2 CLASSIFICATION: OBSTRUCTION FAMILIES (kernel-green target)

Problem (erdosproblems.com/404, [ErGr80 p.79]): For which integers a ≥ 1 and primes p
is there a finite upper bound on those k such that there are a = a₁ < ⋯ < aₙ with
p^k ∣ (a₁! + ⋯ + aₙ!)?  If f(a,p) is the greatest such k, how does f behave?
Is there a prime p and an infinite chain a₁ < a₂ < ⋯ with v_p(Σ_{i≤k} aᵢ!) → ∞?

## WHAT THIS KERNEL PROVES (core Lean 4, zero sorry, zero custom axioms)

For p = 2, writing P_j(a) = (a+1)(a+2)···(a+j) (so i! = a!·P_{i−a}(a) for i > a),
the campaign's reduction (kernel-green, problem404-full) gives
    f(a,2) = v₂(a!) + g(a,2),   g(a,2) = max { g : ∃B ⊆ {a+1,a+2,…}, 2^g ∣ (1 + Σ_{j∈B} P_j(a)) }.

This kernel settles THREE INFINITE FAMILIES exactly:

* **THEOREM T2** (a ≡ 4 mod 8):  g(a,2) = 3 EXACTLY, for EVERY a ≡ 4 (mod 8).
  Upper bound: mod-16 obstruction (the 8 window sub-sums miss −1);
  Lower bound: explicit witness B = {a+1, a+3}.
  → f(a,2) = v₂(a!) + 3 for all a ≡ 4 (mod 8).

* **THEOREM T3** (a ≡ 10 mod 16): g(a,2) = 6 EXACTLY, for EVERY a ≡ 10 (mod 16).
  Mod-128 obstruction over the 5-coin window; witness B = {a+1, a+3}.
  → f(a,2) = v₂(a!) + 6 for all a ≡ 10 (mod 16).

* **THEOREM T4** (a ≡ 32 or 48 mod 64): g(a,2) = 6 EXACTLY.
  Mod-128 obstruction over the 7-coin window; witnesses B = {a+1,a+3,a+5}
  (a ≡ 32 mod 64) and B = {a+1,a+3,a+4} (a ≡ 48 mod 64).
  → f(a,2) = v₂(a!) + 6.

Together with Theorem B (p ∣ a+1 ⟹ g = 0, kernel-green in problem404-full):
every odd a and every a ≡ 4 (mod 8), a ≡ 10 (mod 16), a ≡ 32/48 (mod 64) is
CLASSIFIED with exact f-value.  The remaining a ≤ 200 are certified by the
engine battery (verify_p2class.py): small-g table + 22 deep survivors at 2^28.

Engine receipts (verify_p2class.py): the family tables are uniform to a = 304;
deep survivors g ≥ 28: a ∈ {2,6,14,16,18,24,30,34,38,62,64,78,94,98,102,126,
142,146,158,162,190,194}; f(2,2) ≤ 2^54 by Lin [Li76] (cited on the problem page).

Architecture: §1 machinery (fact/pt/v2 — as in GadgetSupply)  §2 pt lemmas
(split, mod-reduction, vanish)  §3 coinsum + list lemmas  §4 the indicator
lemma  §5 core reductions  §6 leaves (decided)  §7 theorems T2/T3/T4  §8
f-level statements  §9 receipts.
-/

-- ===========================================================================
-- §1  MACHINERY (fact, pt, v2 — the campaign's standard core block)
-- ===========================================================================

def fact : Nat → Nat
  | 0 => 1
  | n + 1 => (n + 1) * fact n

/-- `pt a j = (a+1)(a+2)···(a+j)` — the j-fold product tail; `P_j(a)`. -/
def pt : Nat → Nat → Nat
  | _, 0 => 1
  | u, j + 1 => pt u j * (u + j + 1)

/-- Local duplicate-freeness (self-contained; equivalent to List.Nodup). -/
def NoDup : List Nat → Prop
  | [] => True
  | x :: l => (x ∉ l) ∧ NoDup l

def v2 : Nat → Nat
  | 0 => 0
  | n + 1 => if (n + 1) % 2 = 0 then 1 + v2 ((n + 1) / 2) else 0
termination_by n => n
decreasing_by omega

theorem one_le_mul (a b : Nat) (ha : 1 ≤ a) (hb : 1 ≤ b) : 1 ≤ a * b := by
  induction a with
  | zero => omega
  | succ a' =>
    have hsm : (a' + 1) * b = a' * b + b := Nat.succ_mul a' b
    omega

theorem fact_pos : ∀ u, 1 ≤ fact u
  | 0 => by decide
  | u + 1 => one_le_mul _ _ (by omega) (fact_pos u)

theorem pt_pos : ∀ (j u : Nat), 1 ≤ pt u j
  | 0, _ => by simp [pt]
  | j + 1, u => one_le_mul _ _ (pt_pos j u) (by omega)

theorem v2_succ (n : Nat) :
    v2 (n + 1) = if (n + 1) % 2 = 0 then 1 + v2 ((n + 1) / 2) else 0 := by
  simp [v2]

theorem v2_even_pos (m : Nat) (hm : 1 ≤ m) (h2 : m % 2 = 0) :
    v2 m = 1 + v2 (m / 2) := by
  have ⟨j, hj⟩ : ∃ j, m = j + 1 := ⟨m - 1, by omega⟩
  rw [hj, v2_succ, if_pos (by omega : (j + 1) % 2 = 0)]

theorem v2_odd (m : Nat) (h2 : m % 2 = 1) : v2 m = 0 := by
  have ⟨j, hj⟩ : ∃ j, m = j + 1 := ⟨m - 1, by omega⟩
  rw [hj, v2_succ, if_neg (by omega : ¬((j + 1) % 2 = 0))]

theorem two_mul_div2 (x : Nat) : 2 * x / 2 = x := by
  have hmod := Nat.div_add_mod (2 * x) 2
  have h2 : (2 * x) % 2 = 0 := by rw [Nat.mul_mod]; simp
  omega

theorem even_mul_div2 (a b : Nat) (h : a % 2 = 0) :
    a * b / 2 = (a / 2) * b := by
  have hmod := Nat.div_add_mod a 2
  have hmod' := Nat.div_add_mod (a * b) 2
  have hab : (a * b) % 2 = 0 := by rw [Nat.mul_mod, h]; simp
  have key : a * b = 2 * ((a / 2) * b) := by
    calc a * b = (2 * (a / 2) + a % 2) * b := by rw [hmod]
      _ = (2 * (a / 2) + 0) * b := by rw [h]
      _ = (2 * (a / 2)) * b := by rw [Nat.add_zero]
      _ = 2 * ((a / 2) * b) := Nat.mul_assoc _ _ _
  have hfin : 2 * ((a * b) / 2) = 2 * ((a / 2) * b) := by omega
  omega

/-- Additivity of v2 on products (fuel induction). -/
theorem v2_mul : ∀ (f a b : Nat), a + b ≤ f → 1 ≤ a → 1 ≤ b →
    v2 (a * b) = v2 a + v2 b
  | 0, a, b, hf, ha, hb => by omega
  | f + 1, a, b, hf, ha, hb => by
    by_cases ha1 : a = 1
    · rw [ha1, Nat.one_mul, v2_odd 1 (by decide)]
      omega
    · by_cases hae : a % 2 = 0
      · have hxy : 1 ≤ a * b := one_le_mul a b (by omega) hb
        have hb2 : (a * b) % 2 = 0 := by rw [Nat.mul_mod, hae]; simp
        have hsplit : a * b / 2 = (a / 2) * b := even_mul_div2 a b hae
        rw [v2_even_pos _ hxy hb2, hsplit]
        rw [v2_mul f (a / 2) b (by omega) (by omega) hb]
        rw [v2_even_pos a (by omega) hae]
        omega
      · by_cases hbe : b % 2 = 0
        · rw [Nat.mul_comm a b]
          have hxy : 1 ≤ b * a := one_le_mul b a hb (by omega)
          have hb2 : (b * a) % 2 = 0 := by rw [Nat.mul_mod, hbe]; simp
          have hsplit : b * a / 2 = (b / 2) * a := even_mul_div2 b a hbe
          rw [v2_even_pos _ hxy hb2, hsplit]
          rw [v2_mul f (b / 2) a (by omega) (by omega) (by omega)]
          rw [v2_even_pos b (by omega) hbe]
          omega
        · have hab : (a * b) % 2 = 1 := by
            rw [Nat.mul_mod, show a % 2 = 1 from by omega,
              show b % 2 = 1 from by omega]
          rw [v2_odd _ hab, v2_odd a (by omega), v2_odd b (by omega)]

theorem pow2_dvd_iff : ∀ (k x : Nat), 1 ≤ x → (2 ^ k ∣ x ↔ k ≤ v2 x)
  | 0, x, hx => by
    constructor
    · intro _; omega
    · intro _; exact Nat.one_dvd x
  | k + 1, x, hx => by
    have hmod := Nat.div_add_mod x 2
    have hmk : (2 : Nat) ^ (k + 1) = 2 * 2 ^ k := by
      rw [Nat.mul_comm]
      exact Nat.pow_succ 2 k
    constructor
    · intro hdvd
      obtain ⟨m, hm⟩ := hdvd
      have hx3 : x = 2 * (2 ^ k * m) := by
        rw [← Nat.mul_assoc, ← hmk]
        exact hm
      have htwo : (2 * (2 ^ k * m)) % 2 = 0 := by
        have := Nat.mul_mod 2 (2 ^ k * m) 2
        omega
      have hx2 : x % 2 = 0 := by omega
      have hsplit : v2 x = 1 + v2 (x / 2) := v2_even_pos x hx hx2
      have hxd : x / 2 = 2 ^ k * m := by
        have h2 := two_mul_div2 (2 ^ k * m)
        omega
      have hdiv2 : 1 ≤ x / 2 := by omega
      have ih := (pow2_dvd_iff k (x / 2) hdiv2).mp ⟨m, hxd⟩
      omega
    · intro hle
      have hchoice : x % 2 = 0 ∨ x % 2 = 1 := Nat.mod_two_eq_zero_or_one x
      cases hchoice with
      | inl hx2 =>
        have hsplit : v2 x = 1 + v2 (x / 2) := v2_even_pos x hx hx2
        have hdiv2 : 1 ≤ x / 2 := by omega
        have ih := (pow2_dvd_iff k (x / 2) hdiv2).mpr (by omega)
        obtain ⟨m, hm⟩ := ih
        refine ⟨m, ?_⟩
        have hxd : x / 2 = 2 ^ k * m := hm
        have hfin : x = 2 * (2 ^ k * m) := by omega
        rw [hmk, Nat.mul_assoc]
        exact hfin
      | inr hodd =>
        have hv0 : v2 x = 0 := v2_odd x hodd
        omega

-- ===========================================================================
-- §2  pt LEMMAS: split, mod-reduction, factor divisibility, vanish
-- ===========================================================================

/-- Product split: `pt a (j₁+j₂) = pt a j₁ * pt (a+j₁) j₂`. -/
theorem pt_split : ∀ (j₂ j₁ a : Nat), pt a (j₁ + j₂) = pt a j₁ * pt (a + j₁) j₂
  | 0, j₁, a => by
    have h0 : pt (a + j₁) 0 = 1 := rfl
    have hidx : j₁ + 0 = j₁ := Nat.add_zero j₁
    rw [hidx, h0, Nat.mul_one]
  | j₂ + 1, j₁, a => by
    have hidx : j₁ + (j₂ + 1) = (j₁ + j₂) + 1 := by omega
    have hdef : pt a ((j₁ + j₂) + 1) = pt a (j₁ + j₂) * (a + (j₁ + j₂) + 1) := rfl
    have hdef2 : pt (a + j₁) (j₂ + 1) = pt (a + j₁) j₂ * (a + j₁ + j₂ + 1) := rfl
    rw [hidx, hdef, pt_split j₂ j₁ a, hdef2, Nat.mul_assoc]
    have hidx2 : a + (j₁ + j₂) + 1 = a + j₁ + j₂ + 1 := by omega
    rw [hidx2]

theorem mod_mod (x m : Nat) : x % m % m = x % m := by
  have h0 : m = 0 ∨ 0 < m := by omega
  cases h0 with
  | inl h0 => rw [h0]; simp
  | inr hpos =>
    have hlt : x % m < m := Nat.mod_lt x hpos
    exact Nat.mod_eq_of_lt hlt

theorem mod_add_mod_r (x y m : Nat) : (x + y % m) % m = (x + y) % m := by
  have h1 := Nat.add_mod x (y % m) m
  have h2 := Nat.add_mod x y m
  rw [mod_mod y m] at h1
  rw [h1, h2]

/-- Mod-reduction: the product tail only sees `a` through `a % m`. -/
theorem pt_mod : ∀ (j a m : Nat), pt a j % m = pt (a % m) j % m
  | 0, a, m => rfl
  | j + 1, a, m => by
    have hdef : pt a (j + 1) = pt a j * (a + j + 1) := rfl
    have hdef2 : pt (a % m) (j + 1) = pt (a % m) j * (a % m + j + 1) := rfl
    have hkey : (a + j + 1) % m = (a % m + j + 1) % m := by
      have hidx : a + j + 1 = a + (j + 1) := by omega
      have hidx2 : a % m + j + 1 = a % m + (j + 1) := by omega
      have h1 := Nat.add_mod a (j + 1) m
      have h2 := mod_add_mod_r (a % m) (j + 1) m
      rw [hidx, h1, hidx2, ← h2]
    rw [hdef, hdef2, Nat.mul_mod (pt a j) (a + j + 1) m,
      Nat.mul_mod (pt (a % m) j) (a % m + j + 1) m, pt_mod j a m, hkey]

theorem dvd_pow2_prod (e f x y : Nat) (hx : 2 ^ e ∣ x) (hy : 2 ^ f ∣ y) :
    2 ^ (e + f) ∣ x * y := by
  obtain ⟨x', hx'⟩ := hx
  obtain ⟨y', hy'⟩ := hy
  refine ⟨x' * y', ?_⟩
  have hpa : (2: Nat) ^ (e + f) = 2 ^ e * 2 ^ f := Nat.pow_add 2 e f
  rw [hpa]
  calc x * y = (2 ^ e * x') * (2 ^ f * y') := by rw [hx', hy']
    _ = 2 ^ e * (x' * (2 ^ f * y')) := by rw [Nat.mul_assoc]
    _ = 2 ^ e * ((2 ^ f * y') * x') := by rw [Nat.mul_comm x' (2 ^ f * y')]
    _ = 2 ^ e * (2 ^ f * (y' * x')) := by rw [Nat.mul_assoc (2 ^ f) y' x']
    _ = (2 ^ e * 2 ^ f) * (y' * x') := by rw [← Nat.mul_assoc]
    _ = (2 ^ e * 2 ^ f) * (x' * y') := by rw [Nat.mul_comm y' x']

/-- `(a + t) ∣ pt a j` whenever `1 ≤ t ≤ j`. -/
theorem pt_factor_dvd (a t j : Nat) (h1 : 1 ≤ t) (h2 : t ≤ j) :
    (a + t) ∣ pt a j := by
  have hsplit := pt_split (j - t) t a
  have hjx : t + (j - t) = j := by omega
  rw [hjx] at hsplit
  have hptt : pt a t = pt a (t - 1) * (a + t) := by
    have ht : t = (t - 1) + 1 := by omega
    have hdef : pt a ((t - 1) + 1) = pt a (t - 1) * (a + (t - 1) + 1) := rfl
    have hidx : a + (t - 1) + 1 = a + t := by omega
    rw [← ht] at hdef
    rw [hidx] at hdef
    exact hdef
  have hd1 : (a + t) ∣ pt a t := ⟨pt a (t - 1), by rw [hptt]; exact Nat.mul_comm _ _⟩
  have hd2 : pt a t ∣ pt a j := ⟨pt (a + t) (j - t), hsplit⟩
  exact Nat.dvd_trans hd1 hd2

theorem pt_one_eq (u : Nat) : pt u 1 = u + 1 := by
  have hstep : pt u 1 = pt u 0 * (u + 0 + 1) := rfl
  have h0 : pt u 0 = 1 := rfl
  rw [hstep, h0, Nat.one_mul]

theorem pt_two_eq (u : Nat) : pt u 2 = (u + 1) * (u + 2) := by
  have h1 : pt u 2 = pt u 1 * (u + 1 + 1) := rfl
  have hidx : u + 1 + 1 = u + 2 := by omega
  rw [h1, pt_one_eq, hidx]

/-- **T2 vanish**: a ≡ 4 (mod 8) ⟹ 16 ∣ pt a j for all j ≥ 4. -/
theorem vanish_T2 (a j : Nat) (ha : a % 8 = 4) (hj : 4 ≤ j) : 16 ∣ pt a j := by
  induction hj with
  | refl =>
    -- base: 16 ∣ pt a 4 = pt a 2 * pt (a+2) 2
    have hf2 : (2: Nat) ∣ a + 2 := ⟨(a + 2) / 2, by omega⟩
    have hf8 : (8: Nat) ∣ a + 4 := ⟨(a + 4) / 8, by omega⟩
    have hdvdA : (2: Nat) ∣ pt a 2 := by
      rw [pt_two_eq]
      exact Nat.dvd_trans hf2 (⟨a + 1, Nat.mul_comm (a+1) (a+2)⟩)
    have hdvdB : (8: Nat) ∣ pt (a + 2) 2 := by
      rw [pt_two_eq]
      exact Nat.dvd_trans hf8 (⟨a + 3, Nat.mul_comm (a+3) (a+4)⟩)
    have hsplit := pt_split 2 2 a
    have hidx : 2 + 2 = 4 := by omega
    rw [hidx] at hsplit
    -- pt a 4 = pt a 2 * pt (a+2) 2, and 16 = 2^4 = 2^1 * 2^3
    have h16 : (16: Nat) = 2 ^ (1 + 3) := rfl
    rw [h16, hsplit]
    exact dvd_pow2_prod 1 3 _ _ hdvdA hdvdB
  | @step j' hle ih =>
    obtain ⟨k, hk⟩ := ih
    have hstep : pt a (j' + 1) = pt a j' * (a + j' + 1) := rfl
    rw [hstep, hk]
    exact ⟨k * (a + j' + 1), Nat.mul_assoc _ _ _⟩

/-- **T3 vanish**: a ≡ 10 (mod 16) ⟹ 128 ∣ pt a j for all j ≥ 6. -/
theorem vanish_T3 (a j : Nat) (ha : a % 16 = 10) (hj : 6 ≤ j) : 128 ∣ pt a j := by
  induction hj with
  | refl =>
    have hf4 : (4: Nat) ∣ a + 2 := ⟨(a + 2) / 4, by omega⟩
    have hf2 : (2: Nat) ∣ a + 4 := ⟨(a + 4) / 2, by omega⟩
    have hf16 : (16: Nat) ∣ a + 6 := ⟨(a + 6) / 16, by omega⟩
    have hdvdA : (4: Nat) ∣ pt a 2 := by
      rw [pt_two_eq]
      exact Nat.dvd_trans hf4 (⟨a + 1, Nat.mul_comm (a+1) (a+2)⟩)
    have hdvdB : (2: Nat) ∣ pt (a + 2) 2 := by
      rw [pt_two_eq]
      exact Nat.dvd_trans hf2 (⟨a + 3, Nat.mul_comm (a+3) (a+4)⟩)
    have hdvdC : (16: Nat) ∣ pt (a + 4) 2 := by
      rw [pt_two_eq]
      exact Nat.dvd_trans hf16 (⟨a + 5, Nat.mul_comm (a+5) (a+6)⟩)
    -- pt a 6 = pt a 2 * (pt (a+2) 2 * pt (a+4) 2)
    have h6 := pt_split 4 2 a
    have hi6 : 2 + 4 = 6 := by omega
    rw [hi6] at h6
    have h4' := pt_split 2 2 (a + 2)
    have hi4 : 2 + 2 = 4 := by omega
    rw [hi4] at h4'
    have hn2 : a + 2 + 2 = a + 4 := by omega
    rw [hn2] at h4'
    rw [h4'] at h6
    -- 128 = 2^7 = 2^2 * 2^1 * 2^4
    have h128 : (128: Nat) = 2 ^ ((2 + 1) + 4) := rfl
    rw [h128, h6, ← Nat.mul_assoc]
    have hAB : (2: Nat) ^ (2 + 1) ∣ pt a 2 * pt (a + 2) 2 := dvd_pow2_prod 2 1 _ _ hdvdA hdvdB
    exact dvd_pow2_prod (2 + 1) 4 _ _ hAB hdvdC
  | @step j' hle ih =>
    obtain ⟨k, hk⟩ := ih
    have hstep : pt a (j' + 1) = pt a j' * (a + j' + 1) := rfl
    rw [hstep, hk]
    exact ⟨k * (a + j' + 1), Nat.mul_assoc _ _ _⟩

/-- **T4 vanish**: a ≡ 32 or 48 (mod 64) ⟹ 128 ∣ pt a j for all j ≥ 8. -/
theorem vanish_T4 (a j : Nat) (ha : a % 64 = 32 ∨ a % 64 = 48) (hj : 8 ≤ j) :
    128 ∣ pt a j := by
  induction hj with
  | refl =>
    have hv : (a + 2) % 2 = 0 ∧ (a + 4) % 4 = 0 ∧ (a + 6) % 2 = 0 ∧ (a + 8) % 8 = 0 := by
      cases ha with
      | inl h => omega
      | inr h => omega
    obtain ⟨h2a, h4a, h2b, h8a⟩ := hv
    have hf2a : (2: Nat) ∣ a + 2 := ⟨(a + 2) / 2, by omega⟩
    have hf4a : (4: Nat) ∣ a + 4 := ⟨(a + 4) / 4, by omega⟩
    have hf2b : (2: Nat) ∣ a + 6 := ⟨(a + 6) / 2, by omega⟩
    have hf8a : (8: Nat) ∣ a + 8 := ⟨(a + 8) / 8, by omega⟩
    have hdvdA : (2: Nat) ∣ pt a 2 := by
      rw [pt_two_eq]
      exact Nat.dvd_trans hf2a (⟨a + 1, Nat.mul_comm (a+1) (a+2)⟩)
    have hdvdB : (4: Nat) ∣ pt (a + 2) 2 := by
      rw [pt_two_eq]
      exact Nat.dvd_trans hf4a (⟨a + 3, Nat.mul_comm (a+3) (a+4)⟩)
    have hdvdC : (2: Nat) ∣ pt (a + 4) 2 := by
      rw [pt_two_eq]
      exact Nat.dvd_trans hf2b (⟨a + 5, Nat.mul_comm (a+5) (a+6)⟩)
    have hdvdD : (8: Nat) ∣ pt (a + 6) 2 := by
      rw [pt_two_eq]
      exact Nat.dvd_trans hf8a (⟨a + 7, Nat.mul_comm (a+7) (a+8)⟩)
    -- pt a 8 = pt a 2 * (pt (a+2) 2 * (pt (a+4) 2 * pt (a+6) 2))
    have h8 := pt_split 6 2 a
    have hi8 : 2 + 6 = 8 := by omega
    rw [hi8] at h8
    have h6' := pt_split 4 2 (a + 2)
    have hi6 : 2 + 4 = 6 := by omega
    rw [hi6] at h6'
    have hn2 : a + 2 + 2 = a + 4 := by omega
    rw [hn2] at h6'
    have h4' := pt_split 2 2 (a + 4)
    have hi4 : 2 + 2 = 4 := by omega
    rw [hi4] at h4'
    have hn4 : a + 4 + 2 = a + 6 := by omega
    rw [hn4] at h4'
    rw [h4'] at h6'
    rw [h6'] at h8
    -- 128 = 2^7 = (2^1 * 2^2) * (2^1 * 2^3)
    have h128 : (128: Nat) = 2 ^ ((1 + 2) + (1 + 3)) := rfl
    have hAB : (2: Nat) ^ (1 + 2) ∣ pt a 2 * pt (a + 2) 2 := dvd_pow2_prod 1 2 _ _ hdvdA hdvdB
    have hCD : (2: Nat) ^ (1 + 3) ∣ pt (a + 4) 2 * pt (a + 6) 2 := dvd_pow2_prod 1 3 _ _ hdvdC hdvdD
    have hmain := dvd_pow2_prod (1 + 2) (1 + 3) _ _ hAB hCD
    rw [h128, h8, ← Nat.mul_assoc (pt a 2) (pt (a + 2) 2) (pt (a + 4) 2 * pt (a + 6) 2)]
    exact hmain
  | @step j' hle ih =>
    obtain ⟨k, hk⟩ := ih
    have hstep : pt a (j' + 1) = pt a j' * (a + j' + 1) := rfl
    rw [hstep, hk]
    exact ⟨k * (a + j' + 1), Nat.mul_assoc _ _ _⟩

-- ===========================================================================
-- §3  COINSUM (the subset-sum vehicle)
-- ===========================================================================

def coinsum (a : Nat) (J : List Nat) : Nat := (J.map (fun j => pt a j)).sum

theorem coinsum_cons (a j : Nat) (J : List Nat) :
    coinsum a (j :: J) = pt a j + coinsum a J := rfl

theorem coinsum_mod : ∀ (J : List Nat) (a m : Nat),
    coinsum a J % m = coinsum (a % m) J % m
  | [], a, m => rfl
  | j :: J', a, m => by
    rw [coinsum_cons, coinsum_cons, Nat.add_mod (pt a j) (coinsum a J') m,
      Nat.add_mod (pt (a % m) j) (coinsum (a % m) J') m,
      pt_mod j a m, coinsum_mod J' a m]

-- ===========================================================================
-- §4  THE SLOT MACHINERY (ite-membership sums)
-- ===========================================================================

def sl (r j : Nat) (b : Bool) : Nat := if b then pt r j else 0

theorem sl_true (r j : Nat) : sl r j true = pt r j := rfl
theorem sl_false (r j : Nat) : sl r j false = 0 := rfl

theorem sl_mem_true (r j : Nat) (p : Prop) [Decidable p] (hp : p) :
    sl r j (p) = pt r j := by
  have h : decide p = true := decide_eq_true hp
  rw [h]
  exact sl_true r j

theorem sl_mem_false (r j : Nat) (p : Prop) [Decidable p] (hp : ¬p) :
    sl r j (p) = 0 := by
  have h : decide p = false := decide_eq_false hp
  rw [h]
  exact sl_false r j

/-- Membership flip: a different element was consed — slot unchanged. -/
theorem sl_cons_ne (r j' y x : Nat) (l : List Nat) (hxy : y ≠ x) :
    sl r j' (y ∈ x :: l) = sl r j' (y ∈ l) := by
  by_cases hq : y ∈ l
  · rw [sl_mem_true _ _ _ hq, sl_mem_true _ _ _ (by simp [hq] : y ∈ x :: l)]
  · rw [sl_mem_false _ _ _ hq]
    rw [sl_mem_false _ _ _ (by
      intro hm
      have hc := List.mem_cons.mp hm
      cases hc with
      | inl heq => exact hxy heq
      | inr hr => exact hq hr)]

theorem sl_cons_self (r j x : Nat) (l : List Nat) (hx : x ∉ l) :
    sl r j (x ∈ x :: l) = pt r j := by
  rw [sl_mem_true r j (x ∈ x :: l) (by simp)]

/-- The three window sums: `iteSum3 a r B = Σ_{j=1,2,3} sl r j (a+j ∈ B)`. -/
def iteSum3 (a r : Nat) (B : List Nat) : Nat :=
  sl r 1 (a + 1 ∈ B) + (sl r 2 (a + 2 ∈ B) + (sl r 3 (a + 3 ∈ B) + 0))

def iteSum5 (a r : Nat) (B : List Nat) : Nat :=
  sl r 1 (a + 1 ∈ B) + (sl r 2 (a + 2 ∈ B) + (sl r 3 (a + 3 ∈ B)
    + (sl r 4 (a + 4 ∈ B) + (sl r 5 (a + 5 ∈ B) + 0))))

def iteSum7 (a r : Nat) (B : List Nat) : Nat :=
  sl r 1 (a + 1 ∈ B) + (sl r 2 (a + 2 ∈ B) + (sl r 3 (a + 3 ∈ B)
    + (sl r 4 (a + 4 ∈ B) + (sl r 5 (a + 5 ∈ B) + (sl r 6 (a + 6 ∈ B)
    + (sl r 7 (a + 7 ∈ B) + 0))))))

/-- Miss-bulk: consing i with i ∉ {a+1,a+2,a+3} changes nothing (mod-window). -/
theorem iteSum3_miss (a r i : Nat) (B' : List Nat)
    (hne : ∀ j' ∈ [1, 2, 3], a + j' ≠ i) :
    iteSum3 a r (i :: B') = iteSum3 a r B' := by
  show sl r 1 (a + 1 ∈ i :: B') + (sl r 2 (a + 2 ∈ i :: B') + (sl r 3 (a + 3 ∈ i :: B') + 0))
       = sl r 1 (a + 1 ∈ B') + (sl r 2 (a + 2 ∈ B') + (sl r 3 (a + 3 ∈ B') + 0))
  rw [sl_cons_ne r 1 (a + 1) i B' (hne 1 (by simp)),
      sl_cons_ne r 2 (a + 2) i B' (hne 2 (by simp)),
      sl_cons_ne r 3 (a + 3) i B' (hne 3 (by simp))]

theorem iteSum3_nil (a r : Nat) : iteSum3 a r [] = 0 := by
  simp [iteSum3, sl, List.not_mem_nil]

/-- Hit lemmas: consing i = a+j flips exactly slot j (B' does not contain a+j). -/
theorem iteSum3_hit1 (a r : Nat) (B' : List Nat) (h : ¬(a + 1 ∈ B')) :
    iteSum3 a r ((a + 1) :: B') = iteSum3 a r B' + pt r 1 := by
  show sl r 1 (a + 1 ∈ ((a+1) :: B')) + (sl r 2 (a + 2 ∈ ((a+1) :: B')) + (sl r 3 (a + 3 ∈ ((a+1) :: B')) + 0))
       = sl r 1 (a + 1 ∈ B') + (sl r 2 (a + 2 ∈ B') + (sl r 3 (a + 3 ∈ B') + 0)) + pt r 1
  rw [sl_cons_self r 1 (a + 1) B' h,
      sl_cons_ne r 2 (a + 2) (a + 1) B' (by omega),
      sl_cons_ne r 3 (a + 3) (a + 1) B' (by omega),
      sl_mem_false r 1 (a + 1 ∈ B') h]
  omega

theorem iteSum3_hit2 (a r : Nat) (B' : List Nat) (h : ¬(a + 2 ∈ B')) :
    iteSum3 a r ((a + 2) :: B') = iteSum3 a r B' + pt r 2 := by
  show sl r 1 (a + 1 ∈ ((a+2) :: B')) + (sl r 2 (a + 2 ∈ ((a+2) :: B')) + (sl r 3 (a + 3 ∈ ((a+2) :: B')) + 0))
       = sl r 1 (a + 1 ∈ B') + (sl r 2 (a + 2 ∈ B') + (sl r 3 (a + 3 ∈ B') + 0)) + pt r 2
  rw [sl_cons_self r 2 (a + 2) B' h,
      sl_cons_ne r 1 (a + 1) (a + 2) B' (by omega),
      sl_cons_ne r 3 (a + 3) (a + 2) B' (by omega),
      sl_mem_false r 2 (a + 2 ∈ B') h]
  omega

theorem iteSum3_hit3 (a r : Nat) (B' : List Nat) (h : ¬(a + 3 ∈ B')) :
    iteSum3 a r ((a + 3) :: B') = iteSum3 a r B' + pt r 3 := by
  show sl r 1 (a + 1 ∈ ((a+3) :: B')) + (sl r 2 (a + 2 ∈ ((a+3) :: B')) + (sl r 3 (a + 3 ∈ ((a+3) :: B')) + 0))
       = sl r 1 (a + 1 ∈ B') + (sl r 2 (a + 2 ∈ B') + (sl r 3 (a + 3 ∈ B') + 0)) + pt r 3
  rw [sl_cons_self r 3 (a + 3) B' h,
      sl_cons_ne r 1 (a + 1) (a + 3) B' (by omega),
      sl_cons_ne r 2 (a + 2) (a + 3) B' (by omega),
      sl_mem_false r 3 (a + 3 ∈ B') h]
  omega


-- ===========================================================================
-- §5  THE T3/T4 SLOT FAMILIES (5- and 7-windows)
-- ===========================================================================

theorem iteSum5_nil (a r : Nat) : iteSum5 a r [] = 0 := by
  simp [iteSum5, sl, List.not_mem_nil]

theorem iteSum7_nil (a r : Nat) : iteSum7 a r [] = 0 := by
  simp [iteSum7, sl, List.not_mem_nil]

theorem iteSum5_miss (a r i : Nat) (B' : List Nat)
    (hne : ∀ j' ∈ [1, 2, 3, 4, 5], a + j' ≠ i) :
    iteSum5 a r (i :: B') = iteSum5 a r B' := by
  show sl r 1 (a + 1 ∈ i :: B') + (sl r 2 (a + 2 ∈ i :: B') + (sl r 3 (a + 3 ∈ i :: B')
      + (sl r 4 (a + 4 ∈ i :: B') + (sl r 5 (a + 5 ∈ i :: B') + 0))))
       = sl r 1 (a + 1 ∈ B') + (sl r 2 (a + 2 ∈ B') + (sl r 3 (a + 3 ∈ B')
      + (sl r 4 (a + 4 ∈ B') + (sl r 5 (a + 5 ∈ B') + 0))))
  rw [sl_cons_ne r 1 (a + 1) i B' (hne 1 (by simp)), sl_cons_ne r 2 (a + 2) i B' (hne 2 (by simp)), sl_cons_ne r 3 (a + 3) i B' (hne 3 (by simp)), sl_cons_ne r 4 (a + 4) i B' (hne 4 (by simp)), sl_cons_ne r 5 (a + 5) i B' (hne 5 (by simp))]

theorem iteSum5_hit1 (a r : Nat) (B' : List Nat) (h : ¬(a + 1 ∈ B')) :
    iteSum5 a r ((a + 1) :: B') = iteSum5 a r B' + pt r 1 := by
  show sl r 1 (a + 1 ∈ ((a+1) :: B')) + (sl r 2 (a + 2 ∈ ((a+1) :: B')) + (sl r 3 (a + 3 ∈ ((a+1) :: B')) + (sl r 4 (a + 4 ∈ ((a+1) :: B')) + (sl r 5 (a + 5 ∈ ((a+1) :: B')) + 0)))) = sl r 1 (a + 1 ∈ B') + (sl r 2 (a + 2 ∈ B') + (sl r 3 (a + 3 ∈ B') + (sl r 4 (a + 4 ∈ B') + (sl r 5 (a + 5 ∈ B') + 0)))) + pt r 1
  rw [sl_cons_self r 1 (a + 1) B' h,
      sl_cons_ne r 2 (a + 2) (a + 1) B' (by omega),
      sl_cons_ne r 3 (a + 3) (a + 1) B' (by omega),
      sl_cons_ne r 4 (a + 4) (a + 1) B' (by omega),
      sl_cons_ne r 5 (a + 5) (a + 1) B' (by omega),
      sl_mem_false r 1 (a + 1 ∈ B') h]
  omega

theorem iteSum5_hit2 (a r : Nat) (B' : List Nat) (h : ¬(a + 2 ∈ B')) :
    iteSum5 a r ((a + 2) :: B') = iteSum5 a r B' + pt r 2 := by
  show sl r 1 (a + 1 ∈ ((a+2) :: B')) + (sl r 2 (a + 2 ∈ ((a+2) :: B')) + (sl r 3 (a + 3 ∈ ((a+2) :: B')) + (sl r 4 (a + 4 ∈ ((a+2) :: B')) + (sl r 5 (a + 5 ∈ ((a+2) :: B')) + 0)))) = sl r 1 (a + 1 ∈ B') + (sl r 2 (a + 2 ∈ B') + (sl r 3 (a + 3 ∈ B') + (sl r 4 (a + 4 ∈ B') + (sl r 5 (a + 5 ∈ B') + 0)))) + pt r 2
  rw [sl_cons_self r 2 (a + 2) B' h,
      sl_cons_ne r 1 (a + 1) (a + 2) B' (by omega),
      sl_cons_ne r 3 (a + 3) (a + 2) B' (by omega),
      sl_cons_ne r 4 (a + 4) (a + 2) B' (by omega),
      sl_cons_ne r 5 (a + 5) (a + 2) B' (by omega),
      sl_mem_false r 2 (a + 2 ∈ B') h]
  omega

theorem iteSum5_hit3 (a r : Nat) (B' : List Nat) (h : ¬(a + 3 ∈ B')) :
    iteSum5 a r ((a + 3) :: B') = iteSum5 a r B' + pt r 3 := by
  show sl r 1 (a + 1 ∈ ((a+3) :: B')) + (sl r 2 (a + 2 ∈ ((a+3) :: B')) + (sl r 3 (a + 3 ∈ ((a+3) :: B')) + (sl r 4 (a + 4 ∈ ((a+3) :: B')) + (sl r 5 (a + 5 ∈ ((a+3) :: B')) + 0)))) = sl r 1 (a + 1 ∈ B') + (sl r 2 (a + 2 ∈ B') + (sl r 3 (a + 3 ∈ B') + (sl r 4 (a + 4 ∈ B') + (sl r 5 (a + 5 ∈ B') + 0)))) + pt r 3
  rw [sl_cons_self r 3 (a + 3) B' h,
      sl_cons_ne r 1 (a + 1) (a + 3) B' (by omega),
      sl_cons_ne r 2 (a + 2) (a + 3) B' (by omega),
      sl_cons_ne r 4 (a + 4) (a + 3) B' (by omega),
      sl_cons_ne r 5 (a + 5) (a + 3) B' (by omega),
      sl_mem_false r 3 (a + 3 ∈ B') h]
  omega

theorem iteSum5_hit4 (a r : Nat) (B' : List Nat) (h : ¬(a + 4 ∈ B')) :
    iteSum5 a r ((a + 4) :: B') = iteSum5 a r B' + pt r 4 := by
  show sl r 1 (a + 1 ∈ ((a+4) :: B')) + (sl r 2 (a + 2 ∈ ((a+4) :: B')) + (sl r 3 (a + 3 ∈ ((a+4) :: B')) + (sl r 4 (a + 4 ∈ ((a+4) :: B')) + (sl r 5 (a + 5 ∈ ((a+4) :: B')) + 0)))) = sl r 1 (a + 1 ∈ B') + (sl r 2 (a + 2 ∈ B') + (sl r 3 (a + 3 ∈ B') + (sl r 4 (a + 4 ∈ B') + (sl r 5 (a + 5 ∈ B') + 0)))) + pt r 4
  rw [sl_cons_self r 4 (a + 4) B' h,
      sl_cons_ne r 1 (a + 1) (a + 4) B' (by omega),
      sl_cons_ne r 2 (a + 2) (a + 4) B' (by omega),
      sl_cons_ne r 3 (a + 3) (a + 4) B' (by omega),
      sl_cons_ne r 5 (a + 5) (a + 4) B' (by omega),
      sl_mem_false r 4 (a + 4 ∈ B') h]
  omega

theorem iteSum5_hit5 (a r : Nat) (B' : List Nat) (h : ¬(a + 5 ∈ B')) :
    iteSum5 a r ((a + 5) :: B') = iteSum5 a r B' + pt r 5 := by
  show sl r 1 (a + 1 ∈ ((a+5) :: B')) + (sl r 2 (a + 2 ∈ ((a+5) :: B')) + (sl r 3 (a + 3 ∈ ((a+5) :: B')) + (sl r 4 (a + 4 ∈ ((a+5) :: B')) + (sl r 5 (a + 5 ∈ ((a+5) :: B')) + 0)))) = sl r 1 (a + 1 ∈ B') + (sl r 2 (a + 2 ∈ B') + (sl r 3 (a + 3 ∈ B') + (sl r 4 (a + 4 ∈ B') + (sl r 5 (a + 5 ∈ B') + 0)))) + pt r 5
  rw [sl_cons_self r 5 (a + 5) B' h,
      sl_cons_ne r 1 (a + 1) (a + 5) B' (by omega),
      sl_cons_ne r 2 (a + 2) (a + 5) B' (by omega),
      sl_cons_ne r 3 (a + 3) (a + 5) B' (by omega),
      sl_cons_ne r 4 (a + 4) (a + 5) B' (by omega),
      sl_mem_false r 5 (a + 5 ∈ B') h]
  omega

theorem iteSum7_miss (a r i : Nat) (B' : List Nat)
    (hne : ∀ j' ∈ [1, 2, 3, 4, 5, 6, 7], a + j' ≠ i) :
    iteSum7 a r (i :: B') = iteSum7 a r B' := by
  show sl r 1 (a + 1 ∈ i :: B') + (sl r 2 (a + 2 ∈ i :: B') + (sl r 3 (a + 3 ∈ i :: B') + (sl r 4 (a + 4 ∈ i :: B') + (sl r 5 (a + 5 ∈ i :: B') + (sl r 6 (a + 6 ∈ i :: B') + sl r 7 (a + 7 ∈ i :: B') + 0)))))
       = sl r 1 (a + 1 ∈ B') + (sl r 2 (a + 2 ∈ B') + (sl r 3 (a + 3 ∈ B') + (sl r 4 (a + 4 ∈ B') + (sl r 5 (a + 5 ∈ B') + (sl r 6 (a + 6 ∈ B') + sl r 7 (a + 7 ∈ B') + 0)))))
  rw [sl_cons_ne r 1 (a + 1) i B' (hne 1 (by simp)), sl_cons_ne r 2 (a + 2) i B' (hne 2 (by simp)), sl_cons_ne r 3 (a + 3) i B' (hne 3 (by simp)), sl_cons_ne r 4 (a + 4) i B' (hne 4 (by simp)), sl_cons_ne r 5 (a + 5) i B' (hne 5 (by simp)), sl_cons_ne r 6 (a + 6) i B' (hne 6 (by simp)), sl_cons_ne r 7 (a + 7) i B' (hne 7 (by simp))]

theorem iteSum7_hit1 (a r : Nat) (B' : List Nat) (h : ¬(a + 1 ∈ B')) :
    iteSum7 a r ((a + 1) :: B') = iteSum7 a r B' + pt r 1 := by
  show sl r 1 (a + 1 ∈ ((a+1) :: B')) + (sl r 2 (a + 2 ∈ ((a+1) :: B')) + (sl r 3 (a + 3 ∈ ((a+1) :: B')) + (sl r 4 (a + 4 ∈ ((a+1) :: B')) + (sl r 5 (a + 5 ∈ ((a+1) :: B')) + (sl r 6 (a + 6 ∈ ((a+1) :: B')) + (sl r 7 (a + 7 ∈ ((a+1) :: B')) + 0)))))) = sl r 1 (a + 1 ∈ B') + (sl r 2 (a + 2 ∈ B') + (sl r 3 (a + 3 ∈ B') + (sl r 4 (a + 4 ∈ B') + (sl r 5 (a + 5 ∈ B') + (sl r 6 (a + 6 ∈ B') + (sl r 7 (a + 7 ∈ B') + 0)))))) + pt r 1
  rw [sl_cons_self r 1 (a + 1) B' h,
      sl_cons_ne r 2 (a + 2) (a + 1) B' (by omega),
      sl_cons_ne r 3 (a + 3) (a + 1) B' (by omega),
      sl_cons_ne r 4 (a + 4) (a + 1) B' (by omega),
      sl_cons_ne r 5 (a + 5) (a + 1) B' (by omega),
      sl_cons_ne r 6 (a + 6) (a + 1) B' (by omega),
      sl_cons_ne r 7 (a + 7) (a + 1) B' (by omega),
      sl_mem_false r 1 (a + 1 ∈ B') h]
  omega

theorem iteSum7_hit2 (a r : Nat) (B' : List Nat) (h : ¬(a + 2 ∈ B')) :
    iteSum7 a r ((a + 2) :: B') = iteSum7 a r B' + pt r 2 := by
  show sl r 1 (a + 1 ∈ ((a+2) :: B')) + (sl r 2 (a + 2 ∈ ((a+2) :: B')) + (sl r 3 (a + 3 ∈ ((a+2) :: B')) + (sl r 4 (a + 4 ∈ ((a+2) :: B')) + (sl r 5 (a + 5 ∈ ((a+2) :: B')) + (sl r 6 (a + 6 ∈ ((a+2) :: B')) + (sl r 7 (a + 7 ∈ ((a+2) :: B')) + 0)))))) = sl r 1 (a + 1 ∈ B') + (sl r 2 (a + 2 ∈ B') + (sl r 3 (a + 3 ∈ B') + (sl r 4 (a + 4 ∈ B') + (sl r 5 (a + 5 ∈ B') + (sl r 6 (a + 6 ∈ B') + (sl r 7 (a + 7 ∈ B') + 0)))))) + pt r 2
  rw [sl_cons_self r 2 (a + 2) B' h,
      sl_cons_ne r 1 (a + 1) (a + 2) B' (by omega),
      sl_cons_ne r 3 (a + 3) (a + 2) B' (by omega),
      sl_cons_ne r 4 (a + 4) (a + 2) B' (by omega),
      sl_cons_ne r 5 (a + 5) (a + 2) B' (by omega),
      sl_cons_ne r 6 (a + 6) (a + 2) B' (by omega),
      sl_cons_ne r 7 (a + 7) (a + 2) B' (by omega),
      sl_mem_false r 2 (a + 2 ∈ B') h]
  omega

theorem iteSum7_hit3 (a r : Nat) (B' : List Nat) (h : ¬(a + 3 ∈ B')) :
    iteSum7 a r ((a + 3) :: B') = iteSum7 a r B' + pt r 3 := by
  show sl r 1 (a + 1 ∈ ((a+3) :: B')) + (sl r 2 (a + 2 ∈ ((a+3) :: B')) + (sl r 3 (a + 3 ∈ ((a+3) :: B')) + (sl r 4 (a + 4 ∈ ((a+3) :: B')) + (sl r 5 (a + 5 ∈ ((a+3) :: B')) + (sl r 6 (a + 6 ∈ ((a+3) :: B')) + (sl r 7 (a + 7 ∈ ((a+3) :: B')) + 0)))))) = sl r 1 (a + 1 ∈ B') + (sl r 2 (a + 2 ∈ B') + (sl r 3 (a + 3 ∈ B') + (sl r 4 (a + 4 ∈ B') + (sl r 5 (a + 5 ∈ B') + (sl r 6 (a + 6 ∈ B') + (sl r 7 (a + 7 ∈ B') + 0)))))) + pt r 3
  rw [sl_cons_self r 3 (a + 3) B' h,
      sl_cons_ne r 1 (a + 1) (a + 3) B' (by omega),
      sl_cons_ne r 2 (a + 2) (a + 3) B' (by omega),
      sl_cons_ne r 4 (a + 4) (a + 3) B' (by omega),
      sl_cons_ne r 5 (a + 5) (a + 3) B' (by omega),
      sl_cons_ne r 6 (a + 6) (a + 3) B' (by omega),
      sl_cons_ne r 7 (a + 7) (a + 3) B' (by omega),
      sl_mem_false r 3 (a + 3 ∈ B') h]
  omega

theorem iteSum7_hit4 (a r : Nat) (B' : List Nat) (h : ¬(a + 4 ∈ B')) :
    iteSum7 a r ((a + 4) :: B') = iteSum7 a r B' + pt r 4 := by
  show sl r 1 (a + 1 ∈ ((a+4) :: B')) + (sl r 2 (a + 2 ∈ ((a+4) :: B')) + (sl r 3 (a + 3 ∈ ((a+4) :: B')) + (sl r 4 (a + 4 ∈ ((a+4) :: B')) + (sl r 5 (a + 5 ∈ ((a+4) :: B')) + (sl r 6 (a + 6 ∈ ((a+4) :: B')) + (sl r 7 (a + 7 ∈ ((a+4) :: B')) + 0)))))) = sl r 1 (a + 1 ∈ B') + (sl r 2 (a + 2 ∈ B') + (sl r 3 (a + 3 ∈ B') + (sl r 4 (a + 4 ∈ B') + (sl r 5 (a + 5 ∈ B') + (sl r 6 (a + 6 ∈ B') + (sl r 7 (a + 7 ∈ B') + 0)))))) + pt r 4
  rw [sl_cons_self r 4 (a + 4) B' h,
      sl_cons_ne r 1 (a + 1) (a + 4) B' (by omega),
      sl_cons_ne r 2 (a + 2) (a + 4) B' (by omega),
      sl_cons_ne r 3 (a + 3) (a + 4) B' (by omega),
      sl_cons_ne r 5 (a + 5) (a + 4) B' (by omega),
      sl_cons_ne r 6 (a + 6) (a + 4) B' (by omega),
      sl_cons_ne r 7 (a + 7) (a + 4) B' (by omega),
      sl_mem_false r 4 (a + 4 ∈ B') h]
  omega

theorem iteSum7_hit5 (a r : Nat) (B' : List Nat) (h : ¬(a + 5 ∈ B')) :
    iteSum7 a r ((a + 5) :: B') = iteSum7 a r B' + pt r 5 := by
  show sl r 1 (a + 1 ∈ ((a+5) :: B')) + (sl r 2 (a + 2 ∈ ((a+5) :: B')) + (sl r 3 (a + 3 ∈ ((a+5) :: B')) + (sl r 4 (a + 4 ∈ ((a+5) :: B')) + (sl r 5 (a + 5 ∈ ((a+5) :: B')) + (sl r 6 (a + 6 ∈ ((a+5) :: B')) + (sl r 7 (a + 7 ∈ ((a+5) :: B')) + 0)))))) = sl r 1 (a + 1 ∈ B') + (sl r 2 (a + 2 ∈ B') + (sl r 3 (a + 3 ∈ B') + (sl r 4 (a + 4 ∈ B') + (sl r 5 (a + 5 ∈ B') + (sl r 6 (a + 6 ∈ B') + (sl r 7 (a + 7 ∈ B') + 0)))))) + pt r 5
  rw [sl_cons_self r 5 (a + 5) B' h,
      sl_cons_ne r 1 (a + 1) (a + 5) B' (by omega),
      sl_cons_ne r 2 (a + 2) (a + 5) B' (by omega),
      sl_cons_ne r 3 (a + 3) (a + 5) B' (by omega),
      sl_cons_ne r 4 (a + 4) (a + 5) B' (by omega),
      sl_cons_ne r 6 (a + 6) (a + 5) B' (by omega),
      sl_cons_ne r 7 (a + 7) (a + 5) B' (by omega),
      sl_mem_false r 5 (a + 5 ∈ B') h]
  omega

theorem iteSum7_hit6 (a r : Nat) (B' : List Nat) (h : ¬(a + 6 ∈ B')) :
    iteSum7 a r ((a + 6) :: B') = iteSum7 a r B' + pt r 6 := by
  show sl r 1 (a + 1 ∈ ((a+6) :: B')) + (sl r 2 (a + 2 ∈ ((a+6) :: B')) + (sl r 3 (a + 3 ∈ ((a+6) :: B')) + (sl r 4 (a + 4 ∈ ((a+6) :: B')) + (sl r 5 (a + 5 ∈ ((a+6) :: B')) + (sl r 6 (a + 6 ∈ ((a+6) :: B')) + (sl r 7 (a + 7 ∈ ((a+6) :: B')) + 0)))))) = sl r 1 (a + 1 ∈ B') + (sl r 2 (a + 2 ∈ B') + (sl r 3 (a + 3 ∈ B') + (sl r 4 (a + 4 ∈ B') + (sl r 5 (a + 5 ∈ B') + (sl r 6 (a + 6 ∈ B') + (sl r 7 (a + 7 ∈ B') + 0)))))) + pt r 6
  rw [sl_cons_self r 6 (a + 6) B' h,
      sl_cons_ne r 1 (a + 1) (a + 6) B' (by omega),
      sl_cons_ne r 2 (a + 2) (a + 6) B' (by omega),
      sl_cons_ne r 3 (a + 3) (a + 6) B' (by omega),
      sl_cons_ne r 4 (a + 4) (a + 6) B' (by omega),
      sl_cons_ne r 5 (a + 5) (a + 6) B' (by omega),
      sl_cons_ne r 7 (a + 7) (a + 6) B' (by omega),
      sl_mem_false r 6 (a + 6 ∈ B') h]
  omega

theorem iteSum7_hit7 (a r : Nat) (B' : List Nat) (h : ¬(a + 7 ∈ B')) :
    iteSum7 a r ((a + 7) :: B') = iteSum7 a r B' + pt r 7 := by
  show sl r 1 (a + 1 ∈ ((a+7) :: B')) + (sl r 2 (a + 2 ∈ ((a+7) :: B')) + (sl r 3 (a + 3 ∈ ((a+7) :: B')) + (sl r 4 (a + 4 ∈ ((a+7) :: B')) + (sl r 5 (a + 5 ∈ ((a+7) :: B')) + (sl r 6 (a + 6 ∈ ((a+7) :: B')) + (sl r 7 (a + 7 ∈ ((a+7) :: B')) + 0)))))) = sl r 1 (a + 1 ∈ B') + (sl r 2 (a + 2 ∈ B') + (sl r 3 (a + 3 ∈ B') + (sl r 4 (a + 4 ∈ B') + (sl r 5 (a + 5 ∈ B') + (sl r 6 (a + 6 ∈ B') + (sl r 7 (a + 7 ∈ B') + 0)))))) + pt r 7
  rw [sl_cons_self r 7 (a + 7) B' h,
      sl_cons_ne r 1 (a + 1) (a + 7) B' (by omega),
      sl_cons_ne r 2 (a + 2) (a + 7) B' (by omega),
      sl_cons_ne r 3 (a + 3) (a + 7) B' (by omega),
      sl_cons_ne r 4 (a + 4) (a + 7) B' (by omega),
      sl_cons_ne r 5 (a + 5) (a + 7) B' (by omega),
      sl_cons_ne r 6 (a + 6) (a + 7) B' (by omega),
      sl_mem_false r 7 (a + 7 ∈ B') h]
  omega
theorem obs_core_T2 : ∀ (B : List Nat) (a : Nat), (ha : a % 8 = 4) → NoDup B → (∀ i ∈ B, a < i) →
    (1 + (B.map (fun i => pt a (i - a))).sum) % 16 = (1 + iteSum3 a (a % 16) B) % 16
  | [], a, hv, _, _ => by simp [iteSum3_nil]
  | i :: B', a, hv, hB, hgt => by
    obtain ⟨hin, hB'⟩ := hB
    have hai : a < i := hgt i (by simp)
    have ih := obs_core_T2 B' a hv hB' (fun x hx => hgt x (by simp [hx]))
    have hsc : ((i :: B').map (fun x => pt a (x - a))).sum
        = pt a (i - a) + ((B').map (fun x => pt a (x - a))).sum := rfl
    have hcase : i - a = 1 ∨ i - a = 2 ∨ i - a = 3 ∨ i - a ≥ 4 := by omega
    cases hcase with
    | inl h1 =>
      have hi : i = a + 1 := by omega
      have hnot : ¬(a + 1 ∈ B') := by
        intro hm
        apply hin
        rw [hi]
        exact hm
      rw [hi] at hsc ⊢
      have hstep := iteSum3_hit1 a (a % 16) B' hnot
      rw [hsc, hstep]
      have hia : a + 1 - a = 1 := by omega
      rw [hia]
      have hpt : pt a 1 % 16 = pt (a % 16) 1 % 16 := pt_mod 1 a 16
      omega
    | inr hcase_r =>
      cases hcase_r with
      | inl hj =>
        have hi : i = a + 2 := by omega
        have hnot : ¬(a + 2 ∈ B') := by
          intro hm
          apply hin
          rw [hi]
          exact hm
        rw [hi] at hsc ⊢
        have hstep := iteSum3_hit2 a (a % 16) B' hnot
        rw [hsc, hstep]
        have hia : a + 2 - a = 2 := by omega
        rw [hia]
        have hpt : pt a 2 % 16 = pt (a % 16) 2 % 16 := pt_mod 2 a 16
        omega
      | inr hr2 =>
        cases hr2 with
        | inl hj =>
          have hi : i = a + 3 := by omega
          have hnot : ¬(a + 3 ∈ B') := by
            intro hm
            apply hin
            rw [hi]
            exact hm
          rw [hi] at hsc ⊢
          have hstep := iteSum3_hit3 a (a % 16) B' hnot
          rw [hsc, hstep]
          have hia : a + 3 - a = 3 := by omega
          rw [hia]
          have hpt : pt a 3 % 16 = pt (a % 16) 3 % 16 := pt_mod 3 a 16
          omega
        | inr hbig =>
        have hbig2 : i - a ≥ 4 := by omega
        have hdvd := vanish_T2 a (i - a) hv hbig2
        have hz : pt a (i - a) % 16 = 0 := Nat.mod_eq_zero_of_dvd hdvd
        have hmiss := iteSum3_miss a (a % 16) i B' (by intro j' hj'; simp at hj'; omega)
        rw [hsc, hmiss]
        omega

theorem obs_core_T3 : ∀ (B : List Nat) (a : Nat), (ha : a % 16 = 10) → NoDup B → (∀ i ∈ B, a < i) →
    (1 + (B.map (fun i => pt a (i - a))).sum) % 128 = (1 + iteSum5 a (a % 128) B) % 128
  | [], a, hv, _, _ => by simp [iteSum5_nil]
  | i :: B', a, hv, hB, hgt => by
    obtain ⟨hin, hB'⟩ := hB
    have hai : a < i := hgt i (by simp)
    have ih := obs_core_T3 B' a hv hB' (fun x hx => hgt x (by simp [hx]))
    have hsc : ((i :: B').map (fun x => pt a (x - a))).sum
        = pt a (i - a) + ((B').map (fun x => pt a (x - a))).sum := rfl
    have hcase : i - a = 1 ∨ i - a = 2 ∨ i - a = 3 ∨ i - a = 4 ∨ i - a = 5 ∨ i - a ≥ 6 := by omega
    cases hcase with
    | inl h1 =>
      have hi : i = a + 1 := by omega
      have hnot : ¬(a + 1 ∈ B') := by
        intro hm
        apply hin
        rw [hi]
        exact hm
      rw [hi] at hsc ⊢
      have hstep := iteSum5_hit1 a (a % 128) B' hnot
      rw [hsc, hstep]
      have hia : a + 1 - a = 1 := by omega
      rw [hia]
      have hpt : pt a 1 % 128 = pt (a % 128) 1 % 128 := pt_mod 1 a 128
      omega
    | inr hcase_r =>
      cases hcase_r with
      | inl hj =>
        have hi : i = a + 2 := by omega
        have hnot : ¬(a + 2 ∈ B') := by
          intro hm
          apply hin
          rw [hi]
          exact hm
        rw [hi] at hsc ⊢
        have hstep := iteSum5_hit2 a (a % 128) B' hnot
        rw [hsc, hstep]
        have hia : a + 2 - a = 2 := by omega
        rw [hia]
        have hpt : pt a 2 % 128 = pt (a % 128) 2 % 128 := pt_mod 2 a 128
        omega
      | inr hr2 =>
        cases hr2 with
      | inl hj =>
        have hi : i = a + 3 := by omega
        have hnot : ¬(a + 3 ∈ B') := by
          intro hm
          apply hin
          rw [hi]
          exact hm
        rw [hi] at hsc ⊢
        have hstep := iteSum5_hit3 a (a % 128) B' hnot
        rw [hsc, hstep]
        have hia : a + 3 - a = 3 := by omega
        rw [hia]
        have hpt : pt a 3 % 128 = pt (a % 128) 3 % 128 := pt_mod 3 a 128
        omega
      | inr hr3 =>
        cases hr3 with
      | inl hj =>
        have hi : i = a + 4 := by omega
        have hnot : ¬(a + 4 ∈ B') := by
          intro hm
          apply hin
          rw [hi]
          exact hm
        rw [hi] at hsc ⊢
        have hstep := iteSum5_hit4 a (a % 128) B' hnot
        rw [hsc, hstep]
        have hia : a + 4 - a = 4 := by omega
        rw [hia]
        have hpt : pt a 4 % 128 = pt (a % 128) 4 % 128 := pt_mod 4 a 128
        omega
      | inr hr4 =>
        cases hr4 with
        | inl hj =>
          have hi : i = a + 5 := by omega
          have hnot : ¬(a + 5 ∈ B') := by
            intro hm
            apply hin
            rw [hi]
            exact hm
          rw [hi] at hsc ⊢
          have hstep := iteSum5_hit5 a (a % 128) B' hnot
          rw [hsc, hstep]
          have hia : a + 5 - a = 5 := by omega
          rw [hia]
          have hpt : pt a 5 % 128 = pt (a % 128) 5 % 128 := pt_mod 5 a 128
          omega
        | inr hbig =>
        have hbig2 : i - a ≥ 6 := by omega
        have hdvd := vanish_T3 a (i - a) hv hbig2
        have hz : pt a (i - a) % 128 = 0 := Nat.mod_eq_zero_of_dvd hdvd
        have hmiss := iteSum5_miss a (a % 128) i B' (by intro j' hj'; simp at hj'; omega)
        rw [hsc, hmiss]
        omega

theorem obs_core_T4 : ∀ (B : List Nat) (a : Nat), (ha : a % 64 = 32 ∨ a % 64 = 48) → NoDup B → (∀ i ∈ B, a < i) →
    (1 + (B.map (fun i => pt a (i - a))).sum) % 128 = (1 + iteSum7 a (a % 128) B) % 128
  | [], a, hv, _, _ => by simp [iteSum7_nil]
  | i :: B', a, hv, hB, hgt => by
    obtain ⟨hin, hB'⟩ := hB
    have hai : a < i := hgt i (by simp)
    have ih := obs_core_T4 B' a hv hB' (fun x hx => hgt x (by simp [hx]))
    have hsc : ((i :: B').map (fun x => pt a (x - a))).sum
        = pt a (i - a) + ((B').map (fun x => pt a (x - a))).sum := rfl
    have hcase : i - a = 1 ∨ i - a = 2 ∨ i - a = 3 ∨ i - a = 4 ∨ i - a = 5 ∨ i - a = 6 ∨ i - a = 7 ∨ i - a ≥ 8 := by omega
    cases hcase with
    | inl h1 =>
      have hi : i = a + 1 := by omega
      have hnot : ¬(a + 1 ∈ B') := by
        intro hm
        apply hin
        rw [hi]
        exact hm
      rw [hi] at hsc ⊢
      have hstep := iteSum7_hit1 a (a % 128) B' hnot
      rw [hsc, hstep]
      have hia : a + 1 - a = 1 := by omega
      rw [hia]
      have hpt : pt a 1 % 128 = pt (a % 128) 1 % 128 := pt_mod 1 a 128
      omega
    | inr hcase_r =>
      cases hcase_r with
      | inl hj =>
        have hi : i = a + 2 := by omega
        have hnot : ¬(a + 2 ∈ B') := by
          intro hm
          apply hin
          rw [hi]
          exact hm
        rw [hi] at hsc ⊢
        have hstep := iteSum7_hit2 a (a % 128) B' hnot
        rw [hsc, hstep]
        have hia : a + 2 - a = 2 := by omega
        rw [hia]
        have hpt : pt a 2 % 128 = pt (a % 128) 2 % 128 := pt_mod 2 a 128
        omega
      | inr hr2 =>
        cases hr2 with
      | inl hj =>
        have hi : i = a + 3 := by omega
        have hnot : ¬(a + 3 ∈ B') := by
          intro hm
          apply hin
          rw [hi]
          exact hm
        rw [hi] at hsc ⊢
        have hstep := iteSum7_hit3 a (a % 128) B' hnot
        rw [hsc, hstep]
        have hia : a + 3 - a = 3 := by omega
        rw [hia]
        have hpt : pt a 3 % 128 = pt (a % 128) 3 % 128 := pt_mod 3 a 128
        omega
      | inr hr3 =>
        cases hr3 with
      | inl hj =>
        have hi : i = a + 4 := by omega
        have hnot : ¬(a + 4 ∈ B') := by
          intro hm
          apply hin
          rw [hi]
          exact hm
        rw [hi] at hsc ⊢
        have hstep := iteSum7_hit4 a (a % 128) B' hnot
        rw [hsc, hstep]
        have hia : a + 4 - a = 4 := by omega
        rw [hia]
        have hpt : pt a 4 % 128 = pt (a % 128) 4 % 128 := pt_mod 4 a 128
        omega
      | inr hr4 =>
        cases hr4 with
      | inl hj =>
        have hi : i = a + 5 := by omega
        have hnot : ¬(a + 5 ∈ B') := by
          intro hm
          apply hin
          rw [hi]
          exact hm
        rw [hi] at hsc ⊢
        have hstep := iteSum7_hit5 a (a % 128) B' hnot
        rw [hsc, hstep]
        have hia : a + 5 - a = 5 := by omega
        rw [hia]
        have hpt : pt a 5 % 128 = pt (a % 128) 5 % 128 := pt_mod 5 a 128
        omega
      | inr hr5 =>
        cases hr5 with
      | inl hj =>
        have hi : i = a + 6 := by omega
        have hnot : ¬(a + 6 ∈ B') := by
          intro hm
          apply hin
          rw [hi]
          exact hm
        rw [hi] at hsc ⊢
        have hstep := iteSum7_hit6 a (a % 128) B' hnot
        rw [hsc, hstep]
        have hia : a + 6 - a = 6 := by omega
        rw [hia]
        have hpt : pt a 6 % 128 = pt (a % 128) 6 % 128 := pt_mod 6 a 128
        omega
      | inr hr6 =>
        cases hr6 with
        | inl hj =>
          have hi : i = a + 7 := by omega
          have hnot : ¬(a + 7 ∈ B') := by
            intro hm
            apply hin
            rw [hi]
            exact hm
          rw [hi] at hsc ⊢
          have hstep := iteSum7_hit7 a (a % 128) B' hnot
          rw [hsc, hstep]
          have hia : a + 7 - a = 7 := by omega
          rw [hia]
          have hpt : pt a 7 % 128 = pt (a % 128) 7 % 128 := pt_mod 7 a 128
          omega
        | inr hbig =>
        have hbig2 : i - a ≥ 8 := by omega
        have hdvd := vanish_T4 a (i - a) hv hbig2
        have hz : pt a (i - a) % 128 = 0 := Nat.mod_eq_zero_of_dvd hdvd
        have hmiss := iteSum7_miss a (a % 128) i B' (by intro j' hj'; simp at hj'; omega)
        rw [hsc, hmiss]
        omega


-- ===========================================================================
-- §6  THE LEAVES: all 2^k window patterns miss the target (decided)
-- ===========================================================================
theorem leaf_T2_4 : ∀ (b1 b2 b3 : Bool),
    (1 + (sl 4 1 (b1) + (sl 4 2 (b2) + (sl 4 3 (b3) + 0)))) % 16 ≠ 0 := by
  intro b1 b2 b3
  cases b1 <;> cases b2 <;> cases b3 <;> decide

theorem leaf_T2_12 : ∀ (b1 b2 b3 : Bool),
    (1 + (sl 12 1 (b1) + (sl 12 2 (b2) + (sl 12 3 (b3) + 0)))) % 16 ≠ 0 := by
  intro b1 b2 b3
  cases b1 <;> cases b2 <;> cases b3 <;> decide

theorem leaf_T3_10 : ∀ (b1 b2 b3 b4 b5 : Bool),
    (1 + (sl 10 1 (b1) + (sl 10 2 (b2) + (sl 10 3 (b3) + (sl 10 4 (b4) + (sl 10 5 (b5) + 0)))))) % 128 ≠ 0 := by
  intro b1 b2 b3 b4 b5
  cases b1 <;> cases b2 <;> cases b3 <;> cases b4 <;> cases b5 <;> decide

theorem leaf_T3_26 : ∀ (b1 b2 b3 b4 b5 : Bool),
    (1 + (sl 26 1 (b1) + (sl 26 2 (b2) + (sl 26 3 (b3) + (sl 26 4 (b4) + (sl 26 5 (b5) + 0)))))) % 128 ≠ 0 := by
  intro b1 b2 b3 b4 b5
  cases b1 <;> cases b2 <;> cases b3 <;> cases b4 <;> cases b5 <;> decide

theorem leaf_T3_42 : ∀ (b1 b2 b3 b4 b5 : Bool),
    (1 + (sl 42 1 (b1) + (sl 42 2 (b2) + (sl 42 3 (b3) + (sl 42 4 (b4) + (sl 42 5 (b5) + 0)))))) % 128 ≠ 0 := by
  intro b1 b2 b3 b4 b5
  cases b1 <;> cases b2 <;> cases b3 <;> cases b4 <;> cases b5 <;> decide

theorem leaf_T3_58 : ∀ (b1 b2 b3 b4 b5 : Bool),
    (1 + (sl 58 1 (b1) + (sl 58 2 (b2) + (sl 58 3 (b3) + (sl 58 4 (b4) + (sl 58 5 (b5) + 0)))))) % 128 ≠ 0 := by
  intro b1 b2 b3 b4 b5
  cases b1 <;> cases b2 <;> cases b3 <;> cases b4 <;> cases b5 <;> decide

theorem leaf_T3_74 : ∀ (b1 b2 b3 b4 b5 : Bool),
    (1 + (sl 74 1 (b1) + (sl 74 2 (b2) + (sl 74 3 (b3) + (sl 74 4 (b4) + (sl 74 5 (b5) + 0)))))) % 128 ≠ 0 := by
  intro b1 b2 b3 b4 b5
  cases b1 <;> cases b2 <;> cases b3 <;> cases b4 <;> cases b5 <;> decide

theorem leaf_T3_90 : ∀ (b1 b2 b3 b4 b5 : Bool),
    (1 + (sl 90 1 (b1) + (sl 90 2 (b2) + (sl 90 3 (b3) + (sl 90 4 (b4) + (sl 90 5 (b5) + 0)))))) % 128 ≠ 0 := by
  intro b1 b2 b3 b4 b5
  cases b1 <;> cases b2 <;> cases b3 <;> cases b4 <;> cases b5 <;> decide

theorem leaf_T3_106 : ∀ (b1 b2 b3 b4 b5 : Bool),
    (1 + (sl 106 1 (b1) + (sl 106 2 (b2) + (sl 106 3 (b3) + (sl 106 4 (b4) + (sl 106 5 (b5) + 0)))))) % 128 ≠ 0 := by
  intro b1 b2 b3 b4 b5
  cases b1 <;> cases b2 <;> cases b3 <;> cases b4 <;> cases b5 <;> decide

theorem leaf_T3_122 : ∀ (b1 b2 b3 b4 b5 : Bool),
    (1 + (sl 122 1 (b1) + (sl 122 2 (b2) + (sl 122 3 (b3) + (sl 122 4 (b4) + (sl 122 5 (b5) + 0)))))) % 128 ≠ 0 := by
  intro b1 b2 b3 b4 b5
  cases b1 <;> cases b2 <;> cases b3 <;> cases b4 <;> cases b5 <;> decide

theorem leaf_T4_32 : ∀ (b1 b2 b3 b4 b5 b6 b7 : Bool),
    (1 + (sl 32 1 (b1) + (sl 32 2 (b2) + (sl 32 3 (b3) + (sl 32 4 (b4) + (sl 32 5 (b5) + (sl 32 6 (b6) + (sl 32 7 (b7) + 0)))))))) % 128 ≠ 0 := by
  intro b1 b2 b3 b4 b5 b6 b7
  cases b1 <;> cases b2 <;> cases b3 <;> cases b4 <;> cases b5 <;> cases b6 <;> cases b7 <;> decide

theorem leaf_T4_96 : ∀ (b1 b2 b3 b4 b5 b6 b7 : Bool),
    (1 + (sl 96 1 (b1) + (sl 96 2 (b2) + (sl 96 3 (b3) + (sl 96 4 (b4) + (sl 96 5 (b5) + (sl 96 6 (b6) + (sl 96 7 (b7) + 0)))))))) % 128 ≠ 0 := by
  intro b1 b2 b3 b4 b5 b6 b7
  cases b1 <;> cases b2 <;> cases b3 <;> cases b4 <;> cases b5 <;> cases b6 <;> cases b7 <;> decide

theorem leaf_T4_48 : ∀ (b1 b2 b3 b4 b5 b6 b7 : Bool),
    (1 + (sl 48 1 (b1) + (sl 48 2 (b2) + (sl 48 3 (b3) + (sl 48 4 (b4) + (sl 48 5 (b5) + (sl 48 6 (b6) + (sl 48 7 (b7) + 0)))))))) % 128 ≠ 0 := by
  intro b1 b2 b3 b4 b5 b6 b7
  cases b1 <;> cases b2 <;> cases b3 <;> cases b4 <;> cases b5 <;> cases b6 <;> cases b7 <;> decide

theorem leaf_T4_112 : ∀ (b1 b2 b3 b4 b5 b6 b7 : Bool),
    (1 + (sl 112 1 (b1) + (sl 112 2 (b2) + (sl 112 3 (b3) + (sl 112 4 (b4) + (sl 112 5 (b5) + (sl 112 6 (b6) + (sl 112 7 (b7) + 0)))))))) % 128 ≠ 0 := by
  intro b1 b2 b3 b4 b5 b6 b7
  cases b1 <;> cases b2 <;> cases b3 <;> cases b4 <;> cases b5 <;> cases b6 <;> cases b7 <;> decide


-- ===========================================================================
-- §7  THE MAIN THEOREMS: the mod-16 / mod-128 obstructions
-- ===========================================================================

theorem mod16_mod8 (a : Nat) : (a % 16) % 8 = a % 8 :=
  Nat.mod_mod_of_dvd a (by decide : (8: Nat) ∣ 16)

theorem mod128_mod16 (a : Nat) : (a % 128) % 16 = a % 16 :=
  Nat.mod_mod_of_dvd a (by decide : (16: Nat) ∣ 128)

theorem mod128_mod64 (a : Nat) : (a % 128) % 64 = a % 64 :=
  Nat.mod_mod_of_dvd a (by decide : (64: Nat) ∣ 128)

theorem obs_T2 (a : Nat) (ha : a % 8 = 4) (B : List Nat) (hB : NoDup B) (hgt : ∀ i ∈ B, a < i) :
    (1 + (B.map (fun i => pt a (i - a))).sum) % 16 ≠ 0 := by
  have hcore := obs_core_T2 B a ha hB hgt
  rw [hcore]
  have hr : a % 16 = 4 ∨ a % 16 = 12 := by
    have h1 := mod16_mod8 a
    omega
  cases hr with
  | inl h => rw [h]; exact leaf_T2_4 (a + 1 ∈ B) (a + 2 ∈ B) (a + 3 ∈ B)
  | inr h => rw [h]; exact leaf_T2_12 (a + 1 ∈ B) (a + 2 ∈ B) (a + 3 ∈ B)

theorem obs_T3 (a : Nat) (ha : a % 16 = 10) (B : List Nat) (hB : NoDup B) (hgt : ∀ i ∈ B, a < i) :
    (1 + (B.map (fun i => pt a (i - a))).sum) % 128 ≠ 0 := by
  have hcore := obs_core_T3 B a ha hB hgt
  rw [hcore]
  have hr : a % 128 = 10 ∨ a % 128 = 26 ∨ a % 128 = 42 ∨ a % 128 = 58 ∨ a % 128 = 74 ∨ a % 128 = 90 ∨ a % 128 = 106 ∨ a % 128 = 122 := by
    have h1 := mod128_mod16 a
    omega
  cases hr with
  | inl h => rw [h]; exact leaf_T3_10 (a + 1 ∈ B) (a + 2 ∈ B) (a + 3 ∈ B) (a + 4 ∈ B) (a + 5 ∈ B)
  | inr h1 => cases h1 with
    | inl h => rw [h]; exact leaf_T3_26 (a + 1 ∈ B) (a + 2 ∈ B) (a + 3 ∈ B) (a + 4 ∈ B) (a + 5 ∈ B)
    | inr h2 => cases h2 with
      | inl h => rw [h]; exact leaf_T3_42 (a + 1 ∈ B) (a + 2 ∈ B) (a + 3 ∈ B) (a + 4 ∈ B) (a + 5 ∈ B)
      | inr h3 => cases h3 with
        | inl h => rw [h]; exact leaf_T3_58 (a + 1 ∈ B) (a + 2 ∈ B) (a + 3 ∈ B) (a + 4 ∈ B) (a + 5 ∈ B)
        | inr h4 => cases h4 with
          | inl h => rw [h]; exact leaf_T3_74 (a + 1 ∈ B) (a + 2 ∈ B) (a + 3 ∈ B) (a + 4 ∈ B) (a + 5 ∈ B)
          | inr h5 => cases h5 with
            | inl h => rw [h]; exact leaf_T3_90 (a + 1 ∈ B) (a + 2 ∈ B) (a + 3 ∈ B) (a + 4 ∈ B) (a + 5 ∈ B)
            | inr h6 => cases h6 with
              | inl h => rw [h]; exact leaf_T3_106 (a + 1 ∈ B) (a + 2 ∈ B) (a + 3 ∈ B) (a + 4 ∈ B) (a + 5 ∈ B)
              | inr h => rw [h]; exact leaf_T3_122 (a + 1 ∈ B) (a + 2 ∈ B) (a + 3 ∈ B) (a + 4 ∈ B) (a + 5 ∈ B)

theorem obs_T4 (a : Nat) (ha : a % 64 = 32 ∨ a % 64 = 48) (B : List Nat) (hB : NoDup B) (hgt : ∀ i ∈ B, a < i) :
    (1 + (B.map (fun i => pt a (i - a))).sum) % 128 ≠ 0 := by
  have hcore := obs_core_T4 B a ha hB hgt
  rw [hcore]
  have hr : a % 128 = 32 ∨ a % 128 = 96 ∨ a % 128 = 48 ∨ a % 128 = 112 := by
    have h1 := mod128_mod64 a
    omega
  cases ha with
  | inl h32 =>
    have hr32 : a % 128 = 32 ∨ a % 128 = 96 := by omega
    cases hr32 with
    | inl h => rw [h]; exact leaf_T4_32 (a + 1 ∈ B) (a + 2 ∈ B) (a + 3 ∈ B) (a + 4 ∈ B) (a + 5 ∈ B) (a + 6 ∈ B) (a + 7 ∈ B)
    | inr h => rw [h]; exact leaf_T4_96 (a + 1 ∈ B) (a + 2 ∈ B) (a + 3 ∈ B) (a + 4 ∈ B) (a + 5 ∈ B) (a + 6 ∈ B) (a + 7 ∈ B)
  | inr h48 =>
    have hr48 : a % 128 = 48 ∨ a % 128 = 112 := by omega
    cases hr48 with
    | inl h => rw [h]; exact leaf_T4_48 (a + 1 ∈ B) (a + 2 ∈ B) (a + 3 ∈ B) (a + 4 ∈ B) (a + 5 ∈ B) (a + 6 ∈ B) (a + 7 ∈ B)
    | inr h => rw [h]; exact leaf_T4_112 (a + 1 ∈ B) (a + 2 ∈ B) (a + 3 ∈ B) (a + 4 ∈ B) (a + 5 ∈ B) (a + 6 ∈ B) (a + 7 ∈ B)


-- ===========================================================================
-- §8  THE f-LEVEL STATEMENTS (Erdos #404 exact values for the three families)
-- ===========================================================================

theorem fact_pt : ∀ (j a : Nat), fact (a + j) = fact a * pt a j
  | 0, a => by
    have h0 : pt a 0 = 1 := rfl
    rw [Nat.add_zero, h0, Nat.mul_one]
  | j + 1, a => by
    have hidx : a + (j + 1) = (a + j) + 1 := by omega
    have hfs : fact (a + (j + 1)) = (a + j + 1) * fact (a + j) := by
      rw [hidx]
      rfl
    rw [hfs, fact_pt j a]
    have hpt : pt a (j + 1) = pt a j * (a + j + 1) := rfl
    rw [hpt, Nat.mul_comm (a + j + 1) (fact a * pt a j), ← Nat.mul_assoc]

theorem sum_fact_eq : ∀ (B : List Nat) (a : Nat), (∀ i ∈ B, a < i) →
    (B.map fact).sum = fact a * coinsum a (B.map (fun i => i - a))
  | [], a, _ => by
    simp [coinsum]
  | i :: B', a, hgt => by
    have hai : a < i := hgt i (by simp)
    have ih := sum_fact_eq B' a (fun x hx => hgt x (by simp [hx]))
    have hfi : fact i = fact a * pt a (i - a) := by
      have hidx : a + (i - a) = i := by omega
      have hf := fact_pt (i - a) a
      rw [hidx] at hf
      exact hf
    have hsum : ((i :: B').map fact).sum = fact i + (B'.map fact).sum := rfl
    have hmap : (i :: B').map (fun x => x - a) = (i - a) :: (B'.map (fun x => x - a)) := rfl
    rw [hsum, hfi, ih, hmap, coinsum_cons, Nat.mul_add]

theorem v2_le_of_mod (X : Nat) (hX : 1 ≤ X) (k : Nat) (hmod : X % 2 ^ (k+1) ≠ 0) :
    v2 X ≤ k := by
  by_cases hbig : k + 1 ≤ v2 X
  · exfalso
    have hdvd : (2: Nat) ^ (k + 1) ∣ X := (pow2_dvd_iff (k + 1) X hX).mpr hbig
    have hz : X % 2 ^ (k + 1) = 0 := Nat.mod_eq_zero_of_dvd hdvd
    exact hmod hz
  · omega

theorem v2_ge_of_mod (X : Nat) (hX : 1 ≤ X) (k : Nat) (hmod : X % 2 ^ k = 0) :
    k ≤ v2 X := by
  have h8 : (2: Nat) ^ k ∣ X := Nat.dvd_of_mod_eq_zero hmod
  exact (pow2_dvd_iff k X hX).mp h8

-- The witnesses (exact divisibility at the g-level).

theorem wit_T2 (a : Nat) (ha : a % 8 = 4) :
    (1 + coinsum a [1, 3]) % 8 = 0 ∧ (1 + coinsum a [1, 3]) % 16 ≠ 0 := by
  constructor
  · rw [Nat.add_mod, coinsum_mod, ha]
    decide
  · have hr : a % 16 = 4 ∨ a % 16 = 12 := by
      have h1 := mod16_mod8 a
      omega
    cases hr with
    | inl h => rw [Nat.add_mod, coinsum_mod, h]; decide
    | inr h => rw [Nat.add_mod, coinsum_mod, h]; decide

theorem mod64_mod16 (a : Nat) : (a % 64) % 16 = a % 16 :=
  Nat.mod_mod_of_dvd a (by decide : (16: Nat) ∣ 64)

theorem wit_T3 (a : Nat) (ha : a % 16 = 10) :
    (1 + coinsum a [1, 3]) % 64 = 0 ∧ (1 + coinsum a [1, 3]) % 128 ≠ 0 := by
  constructor
  · have hr : a % 64 = 10 ∨ a % 64 = 26 ∨ a % 64 = 42 ∨ a % 64 = 58 := by
      have h1 := mod64_mod16 a
      omega
    cases hr with
    | inl h => rw [Nat.add_mod, coinsum_mod, h]; decide
    | inr h1 => cases h1 with
      | inl h => rw [Nat.add_mod, coinsum_mod, h]; decide
      | inr h2 => cases h2 with
        | inl h => rw [Nat.add_mod, coinsum_mod, h]; decide
        | inr h => rw [Nat.add_mod, coinsum_mod, h]; decide
  · have hr : a % 128 = 10 ∨ a % 128 = 26 ∨ a % 128 = 42 ∨ a % 128 = 58 ∨ a % 128 = 74 ∨ a % 128 = 90 ∨ a % 128 = 106 ∨ a % 128 = 122 := by
      have h1 := mod128_mod16 a
      omega
    cases hr with
    | inl h => rw [Nat.add_mod, coinsum_mod, h]; decide
    | inr h1 => cases h1 with
      | inl h => rw [Nat.add_mod, coinsum_mod, h]; decide
      | inr h2 => cases h2 with
        | inl h => rw [Nat.add_mod, coinsum_mod, h]; decide
        | inr h3 => cases h3 with
          | inl h => rw [Nat.add_mod, coinsum_mod, h]; decide
          | inr h4 => cases h4 with
            | inl h => rw [Nat.add_mod, coinsum_mod, h]; decide
            | inr h5 => cases h5 with
              | inl h => rw [Nat.add_mod, coinsum_mod, h]; decide
              | inr h6 => cases h6 with
                | inl h => rw [Nat.add_mod, coinsum_mod, h]; decide
                | inr h => rw [Nat.add_mod, coinsum_mod, h]; decide

theorem wit_T4_32 (a : Nat) (ha : a % 64 = 32) :
    (1 + coinsum a [1, 3, 5]) % 64 = 0 := by
  rw [Nat.add_mod, coinsum_mod, ha]
  decide

theorem wit_T4_48 (a : Nat) (ha : a % 64 = 48) :
    (1 + coinsum a [1, 3, 4]) % 64 = 0 := by
  rw [Nat.add_mod, coinsum_mod, ha]
  decide

theorem sum_pt_coinsum (a : Nat) (B : List Nat) :
    (B.map (fun i => pt a (i - a))).sum = coinsum a (B.map (fun i => i - a)) := by
  show (B.map (fun i => pt a (i - a))).sum = ((B.map (fun i => i - a)).map (fun j => pt a j)).sum
  rw [List.map_map]
  rfl

/-- **ERDŐS #404, THEOREM T2 (upper bound).** For EVERY a ≡ 4 (mod 8) and EVERY
valid index list B (distinct entries, all > a):
`v₂(a! + Σ fact i over B) ≤ v₂(a!) + 3`. -/
theorem f404_T2_bound (a : Nat) (ha : a % 8 = 4) (B : List Nat) (hB : NoDup B)
    (hgt : ∀ i ∈ B, a < i) :
    v2 (fact a + (B.map fact).sum) ≤ v2 (fact a) + 3 := by
  have hsf := sum_fact_eq B a hgt
  have hcs := sum_pt_coinsum a B
  have hobs := obs_T2 a ha B hB hgt
  rw [hcs] at hobs
  have hp : (2: Nat) ^ (3 + 1) = 16 := rfl
  have hmod : (1 + coinsum a (B.map (fun i => i - a))) % (2: Nat) ^ (3 + 1) ≠ 0 := by
    rw [hp]
    exact hobs
  have hle := v2_le_of_mod (1 + coinsum a (B.map (fun i => i - a))) (by omega) 3 hmod
  rw [hsf]
  have hdistr : fact a + fact a * coinsum a (B.map (fun i => i - a))
      = fact a * (1 + coinsum a (B.map (fun i => i - a))) := by
    rw [Nat.mul_add, Nat.mul_one]
  rw [hdistr,
    v2_mul (fact a + coinsum a (B.map (fun i => i - a)) + 1) (fact a)
      (1 + coinsum a (B.map (fun i => i - a))) (by omega) (fact_pos a) (by omega)]
  omega

/-- **ERDŐS #404, THEOREM T2 (exactness).** The witness B = [a+1, a+3] attains
`v₂(a! + (a+1)! + (a+3)!) = v₂(a!) + 3` EXACTLY, for every a ≡ 4 (mod 8).
Hence f(a,2) = v₂(a!) + 3 on this family. -/
theorem f404_T2_exact (a : Nat) (ha : a % 8 = 4) :
    v2 (fact a + (fact (a + 1) + fact (a + 3))) = v2 (fact a) + 3 := by
  have h1 : fact (a + 1) = fact a * pt a 1 := fact_pt 1 a
  have h3 : fact (a + 3) = fact a * pt a 3 := fact_pt 3 a
  have hc : coinsum a [1, 3] = pt a 1 + (pt a 3 + 0) := rfl
  rw [h1, h3]
  have hdistr : fact a + (fact a * pt a 1 + fact a * pt a 3)
      = fact a * (1 + coinsum a [1, 3]) := by
    rw [hc, Nat.mul_add, Nat.mul_add, Nat.mul_one, Nat.add_zero]
  rw [hdistr,
    v2_mul (fact a + coinsum a [1, 3] + 1) (fact a) (1 + coinsum a [1, 3])
      (by omega) (fact_pos a) (by omega)]
  obtain ⟨hw8, hw16⟩ := wit_T2 a ha
  have hp3 : (2: Nat) ^ 3 = 8 := rfl
  have hp4 : (2: Nat) ^ 4 = 16 := rfl
  have hge : 3 ≤ v2 (1 + coinsum a [1, 3]) :=
    v2_ge_of_mod (1 + coinsum a [1, 3]) (by omega) 3 (by rw [hp3]; exact hw8)
  have hle : v2 (1 + coinsum a [1, 3]) ≤ 3 :=
    v2_le_of_mod (1 + coinsum a [1, 3]) (by omega) 3 (by rw [hp4]; exact hw16)
  omega

/-- **ERDŐS #404, THEOREM T3 (upper bound).** a ≡ 10 (mod 16) ⟹
`v₂(a! + Σ) ≤ v₂(a!) + 6` for every valid B. -/
theorem f404_T3_bound (a : Nat) (ha : a % 16 = 10) (B : List Nat) (hB : NoDup B)
    (hgt : ∀ i ∈ B, a < i) :
    v2 (fact a + (B.map fact).sum) ≤ v2 (fact a) + 6 := by
  have hsf := sum_fact_eq B a hgt
  have hcs := sum_pt_coinsum a B
  have hobs := obs_T3 a ha B hB hgt
  rw [hcs] at hobs
  have hp : (2: Nat) ^ (6 + 1) = 128 := rfl
  have hmod : (1 + coinsum a (B.map (fun i => i - a))) % (2: Nat) ^ (6 + 1) ≠ 0 := by
    rw [hp]
    exact hobs
  have hle := v2_le_of_mod (1 + coinsum a (B.map (fun i => i - a))) (by omega) 6 hmod
  rw [hsf]
  have hdistr : fact a + fact a * coinsum a (B.map (fun i => i - a))
      = fact a * (1 + coinsum a (B.map (fun i => i - a))) := by
    rw [Nat.mul_add, Nat.mul_one]
  rw [hdistr,
    v2_mul (fact a + coinsum a (B.map (fun i => i - a)) + 1) (fact a)
      (1 + coinsum a (B.map (fun i => i - a))) (by omega) (fact_pos a) (by omega)]
  omega

/-- **ERDŐS #404, THEOREM T3 (exactness).** Witness [a+1, a+3] attains
`v₂(a!) + 6` exactly, for every a ≡ 10 (mod 16). -/
theorem f404_T3_exact (a : Nat) (ha : a % 16 = 10) :
    v2 (fact a + (fact (a + 1) + fact (a + 3))) = v2 (fact a) + 6 := by
  have h1 : fact (a + 1) = fact a * pt a 1 := fact_pt 1 a
  have h3 : fact (a + 3) = fact a * pt a 3 := fact_pt 3 a
  have hc : coinsum a [1, 3] = pt a 1 + (pt a 3 + 0) := rfl
  rw [h1, h3]
  have hdistr : fact a + (fact a * pt a 1 + fact a * pt a 3)
      = fact a * (1 + coinsum a [1, 3]) := by
    rw [hc, Nat.mul_add, Nat.mul_add, Nat.mul_one, Nat.add_zero]
  rw [hdistr,
    v2_mul (fact a + coinsum a [1, 3] + 1) (fact a) (1 + coinsum a [1, 3])
      (by omega) (fact_pos a) (by omega)]
  obtain ⟨hw64, hw128⟩ := wit_T3 a ha
  have hp6 : (2: Nat) ^ 6 = 64 := rfl
  have hp7 : (2: Nat) ^ 7 = 128 := rfl
  have hge : 6 ≤ v2 (1 + coinsum a [1, 3]) :=
    v2_ge_of_mod (1 + coinsum a [1, 3]) (by omega) 6 (by rw [hp6]; exact hw64)
  have hle : v2 (1 + coinsum a [1, 3]) ≤ 6 :=
    v2_le_of_mod (1 + coinsum a [1, 3]) (by omega) 6 (by rw [hp7]; exact hw128)
  omega

/-- **ERDŐS #404, THEOREM T4 (upper bound).** a ≡ 32 or 48 (mod 64) ⟹
`v₂(a! + Σ) ≤ v₂(a!) + 6` for every valid B. -/
theorem f404_T4_bound (a : Nat) (ha : a % 64 = 32 ∨ a % 64 = 48) (B : List Nat)
    (hB : NoDup B) (hgt : ∀ i ∈ B, a < i) :
    v2 (fact a + (B.map fact).sum) ≤ v2 (fact a) + 6 := by
  have hsf := sum_fact_eq B a hgt
  have hcs := sum_pt_coinsum a B
  have hobs := obs_T4 a ha B hB hgt
  rw [hcs] at hobs
  have hp : (2: Nat) ^ (6 + 1) = 128 := rfl
  have hmod : (1 + coinsum a (B.map (fun i => i - a))) % (2: Nat) ^ (6 + 1) ≠ 0 := by
    rw [hp]
    exact hobs
  have hle := v2_le_of_mod (1 + coinsum a (B.map (fun i => i - a))) (by omega) 6 hmod
  rw [hsf]
  have hdistr : fact a + fact a * coinsum a (B.map (fun i => i - a))
      = fact a * (1 + coinsum a (B.map (fun i => i - a))) := by
    rw [Nat.mul_add, Nat.mul_one]
  rw [hdistr,
    v2_mul (fact a + coinsum a (B.map (fun i => i - a)) + 1) (fact a)
      (1 + coinsum a (B.map (fun i => i - a))) (by omega) (fact_pos a) (by omega)]
  omega

/-- **ERDŐS #404, THEOREM T4 (exactness, a ≡ 32 mod 64).** Witness [a+1, a+3, a+5]. -/
theorem f404_T4_exact_32 (a : Nat) (ha : a % 64 = 32) :
    v2 (fact a + (fact (a + 1) + (fact (a + 3) + fact (a + 5)))) = v2 (fact a) + 6 := by
  have h1 : fact (a + 1) = fact a * pt a 1 := fact_pt 1 a
  have h3 : fact (a + 3) = fact a * pt a 3 := fact_pt 3 a
  have h5 : fact (a + 5) = fact a * pt a 5 := fact_pt 5 a
  have hc : coinsum a [1, 3, 5] = pt a 1 + (pt a 3 + (pt a 5 + 0)) := rfl
  rw [h1, h3, h5]
  have hdistr : fact a + (fact a * pt a 1 + (fact a * pt a 3 + fact a * pt a 5))
      = fact a * (1 + coinsum a [1, 3, 5]) := by
    rw [hc, Nat.mul_add, Nat.mul_add, Nat.mul_add, Nat.mul_one, Nat.add_zero]
  rw [hdistr,
    v2_mul (fact a + coinsum a [1, 3, 5] + 1) (fact a) (1 + coinsum a [1, 3, 5])
      (by omega) (fact_pos a) (by omega)]
  have hw := wit_T4_32 a ha
  have hp6 : (2: Nat) ^ 6 = 64 := rfl
  have hge : 6 ≤ v2 (1 + coinsum a [1, 3, 5]) :=
    v2_ge_of_mod (1 + coinsum a [1, 3, 5]) (by omega) 6 (by rw [hp6]; exact hw)
  have hB : NoDup [a + 1, a + 3, a + 5] := by
    simp [NoDup]
  have hgt : ∀ i ∈ [a + 1, a + 3, a + 5], a < i := by
    intro i hi; simp at hi; omega
  have hobs := obs_T4 a (Or.inl ha) [a + 1, a + 3, a + 5] hB hgt
  have hcs := sum_pt_coinsum a [a + 1, a + 3, a + 5]
  rw [hcs] at hobs
  have hp7 : (2: Nat) ^ 7 = 128 := rfl
  have hle : v2 (1 + coinsum a [1, 3, 5]) ≤ 6 := by
    have hmod : (1 + coinsum a (List.map (fun i => i - a) [a + 1, a + 3, a + 5]))
        % (2: Nat) ^ (6 + 1) ≠ 0 := by
      rw [hp7]
      exact hobs
    have htmp := v2_le_of_mod
      (1 + coinsum a (List.map (fun i => i - a) [a + 1, a + 3, a + 5])) (by omega) 6 hmod
    have hoff : List.map (fun i => i - a) [a + 1, a + 3, a + 5] = [1, 3, 5] := by
      have h1 : a + 1 - a = 1 := by omega
      have h3 : a + 3 - a = 3 := by omega
      have h5 : a + 5 - a = 5 := by omega
      simp [List.map, h1, h3, h5]
    rw [hoff] at htmp
    exact htmp
  omega

/-- **ERDŐS #404, THEOREM T4 (exactness, a ≡ 48 mod 64).** Witness [a+1, a+3, a+4]. -/
theorem f404_T4_exact_48 (a : Nat) (ha : a % 64 = 48) :
    v2 (fact a + (fact (a + 1) + (fact (a + 3) + fact (a + 4)))) = v2 (fact a) + 6 := by
  have h1 : fact (a + 1) = fact a * pt a 1 := fact_pt 1 a
  have h3 : fact (a + 3) = fact a * pt a 3 := fact_pt 3 a
  have h4 : fact (a + 4) = fact a * pt a 4 := fact_pt 4 a
  have hc : coinsum a [1, 3, 4] = pt a 1 + (pt a 3 + (pt a 4 + 0)) := rfl
  rw [h1, h3, h4]
  have hdistr : fact a + (fact a * pt a 1 + (fact a * pt a 3 + fact a * pt a 4))
      = fact a * (1 + coinsum a [1, 3, 4]) := by
    rw [hc, Nat.mul_add, Nat.mul_add, Nat.mul_add, Nat.mul_one, Nat.add_zero]
  rw [hdistr,
    v2_mul (fact a + coinsum a [1, 3, 4] + 1) (fact a) (1 + coinsum a [1, 3, 4])
      (by omega) (fact_pos a) (by omega)]
  have hw := wit_T4_48 a ha
  have hp6 : (2: Nat) ^ 6 = 64 := rfl
  have hge : 6 ≤ v2 (1 + coinsum a [1, 3, 4]) :=
    v2_ge_of_mod (1 + coinsum a [1, 3, 4]) (by omega) 6 (by rw [hp6]; exact hw)
  have hB : NoDup [a + 1, a + 3, a + 4] := by
    simp [NoDup]
  have hgt : ∀ i ∈ [a + 1, a + 3, a + 4], a < i := by
    intro i hi; simp at hi; omega
  have hobs := obs_T4 a (Or.inr ha) [a + 1, a + 3, a + 4] hB hgt
  have hcs := sum_pt_coinsum a [a + 1, a + 3, a + 4]
  rw [hcs] at hobs
  have hp7 : (2: Nat) ^ 7 = 128 := rfl
  have hle : v2 (1 + coinsum a [1, 3, 4]) ≤ 6 := by
    have hmod : (1 + coinsum a (List.map (fun i => i - a) [a + 1, a + 3, a + 4]))
        % (2: Nat) ^ (6 + 1) ≠ 0 := by
      rw [hp7]
      exact hobs
    have htmp := v2_le_of_mod
      (1 + coinsum a (List.map (fun i => i - a) [a + 1, a + 3, a + 4])) (by omega) 6 hmod
    have hoff : List.map (fun i => i - a) [a + 1, a + 3, a + 4] = [1, 3, 4] := by
      have h1 : a + 1 - a = 1 := by omega
      have h3 : a + 3 - a = 3 := by omega
      have h4 : a + 4 - a = 4 := by omega
      simp [List.map, h1, h3, h4]
    rw [hoff] at htmp
    exact htmp
  omega

-- ===========================================================================
-- §9  RECEIPTS
-- ===========================================================================

-- T2 exact values v2(a!) + 3 (a = 4, 12, 20, 36; expect 6, 13, 21, 39)
#eval v2 (fact 4 + (fact 5 + fact 7))
#eval v2 (fact 12 + (fact 13 + fact 15))
#eval v2 (fact 20 + (fact 21 + fact 23))
#eval v2 (fact 36 + (fact 37 + fact 39))
-- T3 exact values v2(a!) + 6 (a = 10, 26, 42; expect 14, 29, 42)
#eval v2 (fact 10 + (fact 11 + fact 13))
#eval v2 (fact 26 + (fact 27 + fact 29))
#eval v2 (fact 42 + (fact 43 + fact 45))
-- T4 exact values v2(a!) + 6 (a = 32 witness 1,3,5; a = 48 witness 1,3,4; expect 37, 52)
#eval v2 (fact 32 + (fact 33 + (fact 35 + fact 37)))
#eval v2 (fact 48 + (fact 49 + (fact 51 + fact 52)))
-- v2(4!) = 3 receipt: f(4,2) = 3 + 3 = 6 — Theorem C (problem404-full) recovered
#eval v2 (fact 4)

#print axioms obs_T2
#print axioms obs_T3
#print axioms obs_T4
#print axioms f404_T2_bound
#print axioms f404_T2_exact
#print axioms f404_T3_bound
#print axioms f404_T3_exact
#print axioms f404_T4_bound
#print axioms f404_T4_exact_32
#print axioms f404_T4_exact_48
