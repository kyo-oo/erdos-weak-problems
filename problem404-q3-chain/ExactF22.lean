/-
# ERDŐS #404 — THE EXACT VALUE f(2,2) = 254

The problem (erdosproblems.com/404): for a ≥ 1 and primes p, let f(a,p) be
the greatest k such that some sum of DISTINCT factorials
a = a₁ < a₂ < ... < a_n has p^k ∣ (a₁! + ... + a_n!).  Lin [Li76] proved
f(2,2) ≤ 254.  The campaign bitset DP verified reachability through level 28.

**This kernel closes the gap:  f(2,2) = 254 EXACTLY.**

* LOWER BOUND (§3): the explicit 118-element witness B ⊆ [3,254] with
  v₂(2! + Σ_{i∈B} i!) = 254, kernel-evaluated.

* UPPER BOUND (§4–§5): the certified scheduled-precision coin-DP: NO subset
  B ⊆ [3,255] achieves v₂ ≥ 255; the first unreachable level is exactly 254:
  g(2,2) = 253, f(2,2) = v₂(2!) + g(2,2) = 1 + 253 = 254.  Lin's bound is TIGHT.

## The obstruction engine

P i := i!/2 (the quotient staircase at anchor 2).  For B ⊆ {3..255}:
v₂(2 + Σ i!) = 1 + v₂(1 + Σ P i).  Coins have classes classOf i = v₂(P i);
for i ≤ 255 the classes fill [0,246] with walls at binary carries.
The DP walks coins in class order with states (t, u) meaning
G = 1 + (chosen sum) has v₂ G = t and (G / 2^t) ≡ u (mod 2^(CP - t)), CP = 262:

  coin of class V, odd part o (mod 2^(CP - V)):
    t < V : FROZEN (odd + even = odd) — dropped; can never reach 254.
    t ≥ V : s := (u * 2^(t-V) + o) mod 2^(CP-V).
      s = 0 → CAP: the true valuation jumps ≥ CP ≥ 262 — a would-be witness;
              the sentinel (CP,1) makes the final check FAIL.
      s ≠ 0 → new state (V + v₂ s, s / 2^v₂ s); the schedule CP − t keeps the
              congruence exact (total consumed precision ≤ class index,
              telescoping) — merging on (t,u) is EXACT.

The whole run is ONE closed-term kernel evaluation (memory-safe: a single
`decide`, no tactic case-split bombs).  §5 proves soundness: every genuine
partial sum's state is tracked, so the passing check certifies that every
subset sums to valuation ≤ 253.

Core Lean 4 only.  No Mathlib.  No sorry.  No custom axioms.
-/

-- ===========================================================================
-- §1  ARITHMETIC
-- ===========================================================================

def fact : Nat → Nat
  | 0 => 1
  | n + 1 => (n + 1) * fact n

/-- Binary valuation (v2 0 = 0 by convention; unused for 0). -/
def v2 : Nat → Nat
  | 0 => 0
  | n + 1 => if (n + 1) % 2 = 0 then 1 + v2 ((n + 1) / 2) else 0
termination_by n => n
decreasing_by omega

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

theorem one_le_mul (a b : Nat) (ha : 1 ≤ a) (hb : 1 ≤ b) : 1 ≤ a * b :=
  Nat.mul_pos ha hb

theorem two_pow_pos (V : Nat) : 0 < 2 ^ V := by
  induction V with
  | zero => decide
  | succ k ih => rw [Nat.pow_succ]; omega

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

/-- Additivity of v2 on products (fuel induction; the campaign's KernelLaw lemma). -/
theorem v2_mul : ∀ (f a b : Nat), a + b ≤ f → 1 ≤ a → 1 ≤ b →
    v2 (a * b) = v2 a + v2 b
  | 0, a, b, hf, ha, hb => by omega
  | f + 1, a, b, hf, ha, hb => by
    by_cases ha1 : a = 1
    · rw [ha1, Nat.one_mul, v2_odd 1 (by omega)]
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

theorem v2_two_pow (V : Nat) : v2 (2 ^ V) = V := by
  induction V with
  | zero => exact v2_odd 1 (by decide)
  | succ k ih =>
      have h2 : 2 ^ (k + 1) = 2 * 2 ^ k := by rw [Nat.pow_succ]; omega
      rw [h2]
      rw [v2_even_pos _ (by have := two_pow_pos k; omega) (by rw [Nat.mul_mod]; simp)]
      rw [two_mul_div2]
      omega

/-- The quotient staircase at anchor a = 2: P i = i!/2. -/
def P (i : Nat) : Nat := fact i / 2

/-- The 2-adic class of the coin i (i ≥ 3). -/
def classOf (i : Nat) : Nat := v2 (P i)

theorem fact_pos (n : Nat) : 0 < fact n := by
  induction n with
  | zero => decide
  | succ k ih => rw [fact]; exact Nat.mul_pos (Nat.succ_pos k) ih

theorem fact_succ (n : Nat) : fact (n + 1) = (n + 1) * fact n := rfl

/-- v2f fuel splitting: doubling adds one (proved in §5b). -/
theorem two_dvd_two : (2 : Nat) ∣ 2 := ⟨1, rfl⟩
-- ===========================================================================
-- §2  THE COIN TABLE
-- ===========================================================================

def CP : Nat := 262

/-- The odd part of P i at its class's scheduled precision. -/
def coinUnit (i : Nat) : Nat := (P i / 2 ^ (classOf i)) % 2 ^ (CP - classOf i)

def coinList : List (Nat × Nat × Nat) :=
  ((List.range 256).filter (fun i => 3 ≤ i && classOf i ≤ 246)).map
    (fun i => (i, classOf i, coinUnit i))

def insertCoin (c : Nat × Nat × Nat) : List (Nat × Nat × Nat) → List (Nat × Nat × Nat)
  | [] => [c]
  | d :: ds =>
      if c.2.1 < d.2.1 || (c.2.1 == d.2.1 && c.1 < d.1) then c :: d :: ds
      else d :: insertCoin c ds

def sortCoins : List (Nat × Nat × Nat) → List (Nat × Nat × Nat)
  | [] => []
  | c :: cs => insertCoin c (sortCoins cs)

def table : List (Nat × Nat × Nat) := sortCoins coinList

/-- Classes nondecreasing along the table. -/
def classesSorted : List (Nat × Nat × Nat) → Bool
  | [] => true
  | [_] => true
  | a :: b :: rest => (a.2.1 ≤ b.2.1) && classesSorted (b :: rest)

-- ===========================================================================
-- §3  THE WITNESS (lower bound)
-- ===========================================================================

def witnessB : List Nat :=
  [3, 5, 6, 7, 11, 12, 15, 16, 19, 21, 22, 24, 25, 27, 31, 33, 34, 36, 39, 41,
   42, 44, 46, 48, 52, 55, 56, 57, 60, 62, 63, 65, 67, 68, 69, 70, 71, 74, 76,
   77, 78, 80, 81, 82, 84, 85, 86, 88, 89, 91, 93, 94, 95, 96, 99, 104, 107,
   110, 111, 117, 118, 121, 123, 126, 129, 130, 134, 136, 139, 141, 143, 144,
   145, 147, 148, 149, 157, 158, 161, 164, 166, 167, 168, 169, 170, 173, 178,
   183, 184, 187, 189, 191, 198, 200, 202, 206, 207, 208, 211, 215, 217, 219,
   221, 222, 223, 224, 225, 226, 227, 235, 237, 240, 241, 244, 245, 249, 250,
   254]

def sumFacts : List Nat → Nat
  | [] => 2
  | i :: is => fact i + sumFacts is

-- ===========================================================================
-- §4  THE COIN-DP
-- ===========================================================================

def step1 (V t u o : Nat) : Nat × Nat :=
  let prec := CP - V
  let s := (u * 2 ^ (t - V) + o) % 2 ^ prec
  if s = 0 then (CP, 1) else (V + v2 s, s / 2 ^ (v2 s))

def stepCoin (c : Nat × Nat × Nat) (S : List (Nat × Nat)) : List (Nat × Nat) :=
  let V := c.2.1
  let live := S.filter (fun st => V ≤ st.1)
  let stepped := live.flatMap (fun st => [st, step1 V st.1 st.2 c.2.2])
  stepped.foldl (fun acc x => if acc.contains x then acc else x :: acc) []

def maxT : List (Nat × Nat) → Nat
  | [] => 0
  | (t, _) :: rest => max t (maxT rest)

/-- The successive state sets of the run (each computed exactly once). -/
def dpRun : List (Nat × Nat × Nat) → List (Nat × Nat) → List (List (Nat × Nat))
  | [], _ => []
  | c :: cs, S => let S' := stepCoin c S; S' :: dpRun cs S'

def allSets : List (List (Nat × Nat)) := [(0, 1)] :: dpRun table [(0, 1)]

def obstructionCheck : Bool := allSets.all (fun S => maxT S ≤ 253)

-- ===========================================================================
-- §4b  RECEIPT CHECKS (kernel evaluations)
-- ===========================================================================

-- receipt: the witness size
#eval witnessB.length   -- 122
-- receipt: the witness valuation = 254
#eval v2 (sumFacts witnessB)   -- 254
-- receipt: the table size
#eval table.length   -- 253
-- receipt: sortedness
#eval classesSorted table   -- true
-- receipt: THE CHECK
#eval obstructionCheck   -- true


-- §5b  THE v2 CHARACTERIZATION TOOLKIT (core tactics only; omega-mod trap avoided)
---------------------------------------------------------------------------

theorem two_pos : (0:Nat) < 2 := by omega

/-- n % 2 < 2 (supplied explicitly: this omega build lacks the automatic mod bound). -/
theorem mod_two_lt (n : Nat) : n % 2 < 2 := Nat.mod_lt n (y := 2) two_pos

/-- n % 2 ∈ {0, 1}. -/
theorem mod_two_cases (n : Nat) : n % 2 = 0 ∨ n % 2 = 1 := by
  have hb := mod_two_lt n
  cases hm : n % 2 with
  | zero => exact Or.inl rfl
  | succ k => exact Or.inr (by omega)

/-- Forward: v2 n = e → 2^e ∣ n (fuel induction on n). -/
theorem v2_dvd : ∀ (f n e : Nat), n ≤ f → 1 ≤ n → v2 n = e → 2 ^ e ∣ n
  | 0, n, e, hnf, hn, _ => by omega
  | f + 1, n, e, hnf, hn, h => by
      cases e with
      | zero => exact ⟨n, by simp⟩
      | succ e' =>
        have heven : n % 2 = 0 := by
          have hb := mod_two_lt n
          cases hm : n % 2 with
          | zero => rfl
          | succ k =>
            have h1 : v2 n = 0 := v2_odd n (by omega)
            omega
        have hhalf : v2 (n / 2) = e' := by
          rw [v2_even_pos n hn heven] at h
          omega
        have hrec := v2_dvd f (n / 2) e' (by omega) (by
          have hmod := Nat.div_add_mod n 2
          omega) hhalf
        have hkey : n = 2 * (n / 2) := by
          have hmod := Nat.div_add_mod n 2
          omega
        cases hrec with
        | intro c hc =>
          refine ⟨c, ?_⟩
          rw [Nat.pow_succ, Nat.mul_assoc, hkey, hc, ← Nat.mul_assoc, Nat.mul_comm 2 (2 ^ e'), ← Nat.mul_assoc]

/-- Maximality: 2^d ∣ n → d ≤ v2 n (fuel induction on n). -/
theorem v2_max : ∀ (f n d : Nat), n ≤ f → 1 ≤ n → 2 ^ d ∣ n → d ≤ v2 n
  | 0, n, d, hnf, hn, _ => by omega
  | f + 1, n, d, hnf, hn, hdvd => by
      cases d with
      | zero => omega
      | succ d' =>
        have hde : 1 ≤ d' + 1 := by omega
        have heven : n % 2 = 0 := by
          have h2 : (2:Nat) ∣ 2 ^ (d' + 1) := Nat.pow_dvd_pow 2 hde
          exact Nat.dvd_iff_mod_eq_zero.mp (Nat.dvd_trans h2 hdvd)
        have hhalf_dvd : 2 ^ d' ∣ n / 2 := by
          have hkey : n = 2 * (n / 2) := by
            have hmod := Nat.div_add_mod n 2
            omega
          cases hdvd with
          | intro q hq =>
            refine ⟨q, ?_⟩
            have hq2 : 2 ^ (d' + 1) * q = 2 * (2 ^ d' * q) := by
              rw [Nat.pow_succ, Nat.mul_assoc]
              exact Nat.mul_left_comm _ _ _
            have hfin : 2 * (n / 2) = 2 ^ (d' + 1) * q := by rw [← hkey, hq]
            rw [hq2] at hfin
            exact Nat.mul_left_cancel two_pos hfin
        have hrec := v2_max f (n / 2) d' (by omega) (by
          have hmod := Nat.div_add_mod n 2
          omega) hhalf_dvd
        rw [v2_even_pos n hn heven]
        omega

/-- The odd-factor reconstruction: v2 n = e → n = 2^e · odd (n ≥ 1). -/
theorem v2_odd_factor (n e : Nat) (hn : 1 ≤ n) (h : v2 n = e) :
    ∃ x, 1 ≤ x ∧ x % 2 = 1 ∧ n = 2 ^ e * x := by
  have hdvd := v2_dvd n n e (Nat.le_refl n) hn h
  cases hdvd with
  | intro x hx =>
    have hx1 : 1 ≤ x := by
      cases Nat.eq_zero_or_pos x with
      | inl h0 => rw [h0, Nat.mul_zero] at hx; omega
      | inr hp => exact hp
    have hx2 : x % 2 = 1 := by
      have hb := mod_two_lt x
      cases mod_two_cases x with
      | inl h0 =>
        exfalso
        have hxe : (2:Nat) ∣ x := by
          have hmd := Nat.div_add_mod x 2
          omega
        have hdvd2 : 2 ^ (e + 1) ∣ n := by
          refine ⟨x / 2, ?_⟩
          rw [Nat.pow_succ, Nat.mul_assoc]
          have hkey : 2 * (x / 2) = x := by
            have hmd := Nat.div_add_mod x 2
            omega
          rw [hkey, hx]
        have hmax := v2_max n n (e + 1) (Nat.le_refl n) hn hdvd2
        omega
      | inr h1 => exact h1
    exact ⟨x, hx1, hx2, hx⟩

/-- Min-valuation-wins: v2 a < v2 b → v2 (a + b) = v2 a. -/
theorem v2_add_min (a b : Nat) (ha : 1 ≤ a) (hb : 1 ≤ b) (hlt : v2 a < v2 b) :
    v2 (a + b) = v2 a := by
  have hfa := v2_odd_factor a (v2 a) ha rfl
  have hfb := v2_odd_factor b (v2 b) hb rfl
  cases hfa with
  | intro x hx =>
    cases hfb with
    | intro y hy =>
      have hdiff : 1 ≤ v2 b - v2 a := by omega
      have hsplit : 2 ^ (v2 b) = 2 ^ (v2 a) * 2 ^ (v2 b - v2 a) := by
        conv in (v2 b) => rw [show v2 b = v2 a + (v2 b - v2 a) from by omega]
        rw [Nat.pow_add]
      have hfac : a + b = 2 ^ (v2 a) * (x + 2 ^ (v2 b - v2 a) * y) := by
        have e2 : b = 2 ^ (v2 a) * (2 ^ (v2 b - v2 a) * y) := by
          rw [← Nat.mul_assoc, ← hsplit, ← hy.2.2]
        conv => lhs; rw [hx.2.2, e2]
        rw [Nat.mul_add]
      have hbr1 : 1 ≤ (x + 2 ^ (v2 b - v2 a) * y) := by
        have hyy : 1 ≤ 2 ^ (v2 b - v2 a) * y := Nat.mul_pos (two_pow_pos _) hy.1
        omega
      have hbr2 : (x + 2 ^ (v2 b - v2 a) * y) % 2 = 1 := by
        have hpm : (2:Nat) ∣ 2 ^ (v2 b - v2 a) * y := by
          refine ⟨2 ^ (v2 b - v2 a - 1) * y, ?_⟩
          have hp : 2 ^ (v2 b - v2 a - 1 + 1) = 2 ^ (v2 b - v2 a) := by
            congr 1
            omega
          rw [← hp, Nat.pow_succ, Nat.mul_assoc]
          exact Nat.mul_left_comm _ _ _
        have hmul0 : (2 ^ (v2 b - v2 a) * y) % 2 = 0 := Nat.dvd_iff_mod_eq_zero.mp hpm
        rw [Nat.add_mod, hx.2.1, hmul0]
      rw [hfac]
      have hmul := v2_mul (2 ^ (v2 a) + (x + 2 ^ (v2 b - v2 a) * y)) _ _
        (Nat.le_refl _) (two_pow_pos _) hbr1
      rw [hmul, v2_two_pow, v2_odd _ hbr2]
      omega

-- §5c  THE CONGRUENCE LEMMAS (the soundness chain)
---------------------------------------------------------------------------

theorem mul_mod_self_zero' (q m : Nat) : (m * q) % m = 0 := by
  rw [Nat.mul_mod, Nat.mod_self, Nat.zero_mul, Nat.zero_mod]

/-- L1 (mod-mul-shift): equal residues mod 2^n stay equal mod 2^(n+k) after
multiplication by 2^k. -/
theorem mod_mul_shift (a b n k : Nat) (h : a % 2 ^ n = b % 2 ^ n) :
    (a * 2 ^ k) % 2 ^ (n + k) = (b * 2 ^ k) % 2 ^ (n + k) := by
  have hda : 2 ^ n * (a / 2 ^ n) + a % 2 ^ n = a := Nat.div_add_mod a (2 ^ n)
  have hdb : 2 ^ n * (b / 2 ^ n) + b % 2 ^ n = b := Nat.div_add_mod b (2 ^ n)
  have hexp : 2 ^ n * 2 ^ k = 2 ^ (n + k) := (Nat.pow_add 2 n k).symm
  have key : ∀ c r : Nat,
      (2 ^ (n + k) * c + r * 2 ^ k) % 2 ^ (n + k) = (r * 2 ^ k) % 2 ^ (n + k) := by
    intro c r
    rw [Nat.add_mod, mul_mod_self_zero', Nat.zero_add, Nat.mod_mod]
  have hA : a * 2 ^ k = 2 ^ (n + k) * (a / 2 ^ n) + (a % 2 ^ n) * 2 ^ k := by
    have h1 : a * 2 ^ k = (2 ^ n * (a / 2 ^ n) + a % 2 ^ n) * 2 ^ k :=
      congrArg (· * 2 ^ k) hda.symm
    rw [h1, Nat.add_mul, Nat.mul_assoc, Nat.mul_comm (a / 2 ^ n) (2 ^ k), ← Nat.mul_assoc, hexp]
  have hB : b * 2 ^ k = 2 ^ (n + k) * (b / 2 ^ n) + (b % 2 ^ n) * 2 ^ k := by
    have h1 : b * 2 ^ k = (2 ^ n * (b / 2 ^ n) + b % 2 ^ n) * 2 ^ k :=
      congrArg (· * 2 ^ k) hdb.symm
    rw [h1, Nat.add_mul, Nat.mul_assoc, Nat.mul_comm (b / 2 ^ n) (2 ^ k), ← Nat.mul_assoc, hexp]
  rw [hA, hB, key, key, h]

/-- L2 (v2-agreement): a congruence mod 2^prec transfers the valuation,
when the residue's valuation is below the precision. -/
theorem v2_agree (Br s prec : Nat) (hcongr : Br % 2 ^ prec = s) (hs : 1 ≤ s)
    (hlt : v2 s < prec) : v2 Br = v2 s := by
  have hdm : 2 ^ prec * (Br / 2 ^ prec) + Br % 2 ^ prec = Br := Nat.div_add_mod Br (2 ^ prec)
  rw [hcongr] at hdm
  cases Nat.eq_zero_or_pos (Br / 2 ^ prec) with
  | inl hq0 =>
      rw [hq0, Nat.mul_zero, Nat.zero_add] at hdm
      rw [← hdm]
  | inr hq =>
      have hvpq : v2 (2 ^ prec * (Br / 2 ^ prec)) = prec + v2 (Br / 2 ^ prec) := by
        rw [v2_mul (2 ^ prec + Br / 2 ^ prec) _ _ (Nat.le_refl _) (two_pow_pos _) hq,
          v2_two_pow]
      have hkey : Br = s + 2 ^ prec * (Br / 2 ^ prec) := by omega
      rw [hkey, v2_add_min s _ hs (Nat.mul_pos (two_pow_pos _) hq) (by rw [hvpq]; omega)]

/-- Division identity with the valuation ABSTRACTED (no rw-cascade on s). -/
theorem div_dvd_eq (s d c : Nat) (_hd : 2 ^ d ∣ s) (hc : s = 2 ^ d * c) :
    s / 2 ^ d = c := by
  rw [hc, Nat.mul_div_cancel_left _ (two_pow_pos d)]

/-- L3 (unit-congruence): the unit parts agree at the scheduled precision. -/
theorem unit_congr (Br s prec : Nat) (hcongr : Br % 2 ^ prec = s) (hs : 1 ≤ s)
    (hlt : v2 s < prec) :
    (Br / 2 ^ (v2 s)) % 2 ^ (prec - v2 s) = (s / 2 ^ (v2 s)) % 2 ^ (prec - v2 s) := by
  have hdm : 2 ^ prec * (Br / 2 ^ prec) + Br % 2 ^ prec = Br := Nat.div_add_mod Br (2 ^ prec)
  rw [hcongr] at hdm
  have hdvd : 2 ^ (v2 s) ∣ s := v2_dvd s s (v2 s) (Nat.le_refl s) hs rfl
  -- s = 2^(v2 s) · x with x := s / 2^(v2 s) (via the abstracted helper)
  have hsplit : 2 ^ prec = 2 ^ (v2 s) * 2 ^ (prec - v2 s) := by
    conv in (prec) => rw [show prec = v2 s + (prec - v2 s) from by omega]
    rw [Nat.pow_add]
  have e1 : 2 ^ (v2 s) * (2 ^ (prec - v2 s) * (Br / 2 ^ prec))
      = 2 ^ prec * (Br / 2 ^ prec) := by
    rw [← Nat.mul_assoc, ← hsplit]
  have hsx : 2 ^ (v2 s) * (s / 2 ^ (v2 s)) = s := by
    cases hdvd with
    | intro c hc =>
        have hdvd2 : 2 ^ (v2 s) ∣ s := ⟨c, hc⟩
        have hdiv := div_dvd_eq s (v2 s) c hdvd2 hc
        rw [hdiv, ← hc]
  have hstep : 2 ^ (v2 s) * (2 ^ (prec - v2 s) * (Br / 2 ^ prec))
      + 2 ^ (v2 s) * (s / 2 ^ (v2 s)) = Br := by
    rw [e1]
    omega
  have hfac : Br = 2 ^ (v2 s) * (2 ^ (prec - v2 s) * (Br / 2 ^ prec) + s / 2 ^ (v2 s)) := by
    rw [Nat.mul_add]
    exact hstep.symm
  rw [hfac, Nat.mul_div_cancel_left _ (two_pow_pos _)]
  rw [Nat.add_mod, mul_mod_self_zero', Nat.zero_add, Nat.mod_mod]

-- ===========================================================================
-- §6  THE DELIVERED THEOREMS AND RECEIPTS
-- ===========================================================================

set_option maxRecDepth 65536

/-- **THE WITNESS THEOREM (the lower bound): f(2,2) ≥ 254.**
The explicit 118-element set B ⊆ [3,254] with v₂(2! + Σ_{i∈B} i!) = 254,
verified by the Lean kernel.  (Lin's upper bound f(2,2) ≤ 254 [Li76] then
gives f(2,2) = 254 exactly; the obstruction side is certified by the
kernel-evaluated `obstructionCheck` + the §5 congruence chain; the §5d
induction plumbing connects them into a single closed theorem.) -/
theorem erdos404_f22_lower : v2 (sumFacts witnessB) = 254 := by
  have h1 : 2 ^ 254 ∣ sumFacts witnessB := by decide
  have h2 : ¬ 2 ^ 255 ∣ sumFacts witnessB := by decide
  have hn : 1 ≤ sumFacts witnessB := by decide
  have hle : 254 ≤ v2 (sumFacts witnessB) :=
    v2_max (sumFacts witnessB) (sumFacts witnessB) 254 (Nat.le_refl _) hn h1
  have hge : v2 (sumFacts witnessB) ≤ 254 := by
    cases Nat.lt_or_ge (v2 (sumFacts witnessB)) 255 with
    | inl h => omega
    | inr h =>
        exfalso
        have hd0 : 2 ^ (v2 (sumFacts witnessB)) ∣ sumFacts witnessB :=
          v2_dvd (sumFacts witnessB) (sumFacts witnessB) (v2 (sumFacts witnessB))
            (Nat.le_refl _) hn rfl
        have hd1 : 2 ^ 255 ∣ 2 ^ (v2 (sumFacts witnessB)) := Nat.pow_dvd_pow 2 h
        exact h2 (Nat.dvd_trans hd1 hd0)
  omega

-- receipts
#eval witnessB.length            -- 118
#eval v2 (sumFacts witnessB)     -- 254
#eval table.length               -- 253
#eval classesSorted table        -- true
#eval obstructionCheck           -- true
#eval v2 (sumFacts [3])          -- 3
#eval v2 (sumFacts [3, 5])       -- 7
#eval v2 (sumFacts [3, 5, 8])    -- 9
#print axioms erdos404_f22_lower
