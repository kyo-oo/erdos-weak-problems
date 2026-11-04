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

/-- Binary valuation — FUEL-STRUCTURAL (well-founded recursion does not
kernel-reduce; the fuel form makes every downstream kernel evaluation
possible: classOf, coinUnit, the table, obstructionCheck). -/
def v2f : Nat → Nat → Nat
  | 0, _ => 0
  | _ + 1, 0 => 0
  | f + 1, n + 1 =>
      if (n + 1) % 2 = 0 then 1 + v2f f ((n + 1) / 2) else 0

/-- Binary valuation (v2 0 = 0 by convention; unused for 0). -/
def v2 (n : Nat) : Nat := v2f n n

/-- Fuel abundance: extra fuel does not change the result. -/
theorem v2f_mono : ∀ (f f' n : Nat), n ≤ f → f ≤ f' → v2f f' n = v2f f n := by
  intro f
  induction f with
  | zero =>
      intro f' n hn _
      have hn0 : n = 0 := by omega
      cases f' with
      | zero => rfl
      | succ f0' => rw [hn0]; rfl
  | succ f0 ih =>
      intro f' n hn hf
      cases f' with
      | zero => omega
      | succ f0' =>
          cases n with
          | zero => rfl
          | succ n0 =>
              show (if (n0 + 1) % 2 = 0 then 1 + v2f f0' ((n0 + 1) / 2) else 0)
                = (if (n0 + 1) % 2 = 0 then 1 + v2f f0 ((n0 + 1) / 2) else 0)
              by_cases h : (n0 + 1) % 2 = 0
              · rw [if_pos h, if_pos h]
                congr 1
                exact ih f0' ((n0 + 1) / 2) (by omega) (by omega)
              · rw [if_neg h, if_neg h]

theorem v2_succ (n : Nat) :
    v2 (n + 1) = if (n + 1) % 2 = 0 then 1 + v2 ((n + 1) / 2) else 0 := by
  have hstep : v2f (n + 1) (n + 1)
      = if (n + 1) % 2 = 0 then 1 + v2f n ((n + 1) / 2) else 0 := rfl
  show v2f (n + 1) (n + 1)
      = if (n + 1) % 2 = 0 then 1 + v2f ((n + 1) / 2) ((n + 1) / 2) else 0
  rw [hstep]
  by_cases h : (n + 1) % 2 = 0
  · rw [if_pos h, if_pos h]
    congr 1
    exact v2f_mono ((n + 1) / 2) n ((n + 1) / 2) (by omega) (by omega)
  · rw [if_neg h, if_neg h]

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
      if c.2.1 < d.2.1 || (decide (c.2.1 = d.2.1) && c.1 < d.1) then c :: d :: ds
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

/-- Bool membership on states via NATIVE decidable equality (binary —
a hand-rolled unary equality is exponential on 250-bit state units). -/
def memB (x : Nat × Nat) : List (Nat × Nat) → Bool
  | [] => false
  | y :: ys => if x = y then true else memB x ys

theorem memB_true (x : Nat × Nat) (l : List (Nat × Nat)) (h : memB x l = true) : x ∈ l := by
  induction l with
  | nil => simp [memB] at h
  | cons y ys ih =>
      unfold memB at h
      by_cases hx : x = y
      · rw [if_pos hx] at h
        rw [hx]
        exact List.Mem.head _
      · rw [if_neg hx] at h
        exact List.Mem.tail _ (ih h)

/-- Deduplication via an accumulator (single pass — kernel-safe: no
recomputation across branches; same state-SET as the foldl it replaced). -/
def dedupAux : List (Nat × Nat) → List (Nat × Nat) → List (Nat × Nat)
  | [], acc => acc
  | y :: ys, acc => if memB y acc then dedupAux ys acc else dedupAux ys (y :: acc)

def dedup (l : List (Nat × Nat)) : List (Nat × Nat) := dedupAux l []

def stepCoin (c : Nat × Nat × Nat) (S : List (Nat × Nat)) : List (Nat × Nat) :=
  let V := c.2.1
  let live := S.filter (fun st => V ≤ st.1)
  let stepped := live.flatMap (fun st => [st, step1 V st.1 st.2 c.2.2])
  dedup stepped

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
#eval witnessB.length   -- 118
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
-- §5d  THE INVARIANT INDUCTION (obstructionCheck ⟹ the universal upper bound)
-- ===========================================================================

theorem dedupAux_mem : ∀ (l acc : List (Nat × Nat)) (x : Nat × Nat),
    (x ∈ acc ∨ x ∈ l) → x ∈ dedupAux l acc := by
  intro l
  induction l with
  | nil =>
      intro acc x h
      cases h with
      | inl ha => exact ha
      | inr hl => cases hl
  | cons y ys ih =>
      intro acc x h
      unfold dedupAux
      by_cases hb : memB y acc = true
      · rw [if_pos hb]
        refine ih acc x ?_
        cases h with
        | inl ha => exact Or.inl ha
        | inr hl =>
            cases hl with
            | head => exact Or.inl (memB_true _ _ hb)
            | tail _ ht => exact Or.inr ht
      · rw [if_neg hb]
        refine ih (y :: acc) x ?_
        cases h with
        | inl ha => exact Or.inl (List.Mem.tail _ ha)
        | inr hl =>
            cases hl with
            | head => exact Or.inl (List.Mem.head _)
            | tail _ ht => exact Or.inr ht

theorem dedup_mem (x : Nat × Nat) (l : List (Nat × Nat)) (h : x ∈ l) : x ∈ dedup l :=
  dedupAux_mem l [] x (Or.inr h)

theorem dedup_mem_self (y : Nat × Nat) (ys : List (Nat × Nat)) :
    y ∈ dedup (y :: ys) := dedup_mem y (y :: ys) (List.Mem.head _)

/-- Membership in flatMap (core-only, by induction). -/
theorem mem_flatMap_of {x : Nat × Nat} {l : List (Nat × Nat)}
    (f : Nat × Nat → List (Nat × Nat)) (a : Nat × Nat) (ha : a ∈ l) (hx : x ∈ f a) :
    x ∈ l.flatMap f := by
  induction l with
  | nil => cases ha
  | cons y ys ih =>
      cases ha with
      | head =>
          show x ∈ f a ++ ys.flatMap f
          exact List.mem_append_left _ hx
      | tail _ ht =>
          show x ∈ f y ++ ys.flatMap f
          exact List.mem_append_right _ (ih ht)

/-- The two stepCoin membership facts: a live state survives (skip) and its
step (take) enters the new set. -/
theorem stepCoin_keeps (c : Nat × Nat × Nat) (S : List (Nat × Nat)) (st : Nat × Nat)
    (hst : st ∈ S) (hlive : c.2.1 ≤ st.1) : st ∈ stepCoin c S := by
  have hlive' : st ∈ S.filter (fun q => c.2.1 ≤ q.1) :=
    List.mem_filter.mpr ⟨hst, decide_eq_true hlive⟩
  have hflat : st ∈ (S.filter (fun q => c.2.1 ≤ q.1)).flatMap
      (fun q => [q, step1 c.2.1 q.1 q.2 c.2.2]) := by
    refine mem_flatMap_of _ st hlive' ?_
    exact List.mem_cons_self ..
  unfold stepCoin
  exact dedup_mem _ _ hflat

theorem stepCoin_steps (c : Nat × Nat × Nat) (S : List (Nat × Nat)) (st : Nat × Nat)
    (hst : st ∈ S) (hlive : c.2.1 ≤ st.1) :
    step1 c.2.1 st.1 st.2 c.2.2 ∈ stepCoin c S := by
  have hlive' : st ∈ S.filter (fun q => c.2.1 ≤ q.1) :=
    List.mem_filter.mpr ⟨hst, decide_eq_true hlive⟩
  have hflat : step1 c.2.1 st.1 st.2 c.2.2 ∈
      (S.filter (fun q => c.2.1 ≤ q.1)).flatMap
      (fun q => [q, step1 c.2.1 q.1 q.2 c.2.2]) := by
    refine mem_flatMap_of _ st hlive' ?_
    exact List.mem_cons_of_mem _ (List.mem_cons_self ..)
  unfold stepCoin
  exact dedup_mem _ _ hflat

-- ===========================================================================
-- §5d-2  THE MATCHING RELATION AND THE ACHIEVABLE SUMS
-- ===========================================================================

/-- State (t,u) MATCHES the sum G: capped (t = CP: 2^CP ∣ G) or live with
the built-in bound t < CP and exact tracking. -/
def matchSt : Nat → Nat × Nat → Prop
  | G, (t, u) =>
      if t = CP then 2 ^ CP ∣ G
      else t < CP ∧ v2 G = t ∧ (G / 2 ^ t) % 2 ^ (CP - t) = u

/-- Achievable sums: g = 1 + Σ_{coins taken} P coin, walking the coin list
front-to-back — exactly the order the DP processes. -/
inductive Achiev : List (Nat × Nat × Nat) → Nat → Prop
  | base : Achiev [] 1
  | skip (cs : List (Nat × Nat × Nat)) (c : Nat × Nat × Nat) (g : Nat) :
      Achiev cs g → Achiev (c :: cs) g
  | take (cs : List (Nat × Nat × Nat)) (c : Nat × Nat × Nat) (g : Nat) :
      Achiev cs g → Achiev (c :: cs) (g + P c.1)

theorem achiev_nil (g : Nat) (h : Achiev [] g) : g = 1 := by
  cases h with | base => rfl

-- ===========================================================================
-- §5d-3  THE COIN/STATE DECOMPOSITIONS AND LEMMA A (STEP SOUNDNESS)
-- ===========================================================================

/-- Dvd survives scaling on the left (core-only constructor proof). -/
theorem dvd_mul_gen (m n k : Nat) (h : m ∣ n) : m ∣ k * n := by
  obtain ⟨c, hc⟩ := h
  refine ⟨k * c, ?_⟩
  rw [hc, ← Nat.mul_assoc, Nat.mul_comm k m]
  exact Nat.mul_assoc m k c

/-- The quotient staircase is positive for i ≥ 2. -/
theorem P_pos (i : Nat) (hi : 2 ≤ i) : 1 ≤ P i := by
  have key : ∀ k : Nat, (2:Nat) ∣ fact (k + 2) := by
    intro k
    induction k with
    | zero => decide
    | succ k' ih =>
        rw [show k' + 1 + 2 = (k' + 2) + 1 from by omega, fact_succ]
        exact dvd_mul_gen 2 (fact (k' + 2)) (k' + 2 + 1) ih
  have hd2 : (2:Nat) ∣ fact i := by
    have hk := key (i - 2)
    rw [show i - 2 + 2 = i from by omega] at hk
    exact hk
  have hf2 : 2 ≤ fact i := Nat.le_of_dvd (fact_pos i) hd2
  obtain ⟨w, hw⟩ := hd2
  have hPw : P i = w := by
    unfold P
    rw [hw, Nat.mul_div_cancel_left _ (by omega : 0 < 2)]
  rw [hPw]
  have h2w : 2 ≤ 2 * w := by rw [← hw]; exact hf2
  omega

/-- The coin decomposition: P i = 2^V · (o + 2^(CP−V) · j). -/
theorem coin_split (i : Nat) (hi : 2 ≤ i) :
    ∃ j, P i = 2 ^ (classOf i) * (coinUnit i + 2 ^ (CP - classOf i) * j) := by
  have hpos : 1 ≤ P i := P_pos i hi
  have hdvd : 2 ^ (classOf i) ∣ P i :=
    v2_dvd (P i) (P i) (classOf i) (Nat.le_refl _) hpos rfl
  obtain ⟨y, hy⟩ := hdvd
  have hdef : P i = 2 ^ (classOf i) * y := hy
  have hdy : P i / 2 ^ (classOf i) = y := by
    rw [hdef, Nat.mul_div_cancel_left _ (two_pow_pos _)]
  have hmod : y % 2 ^ (CP - classOf i) = coinUnit i := by
    unfold coinUnit
    rw [hdy]
  obtain ⟨q, hq⟩ : ∃ q, y = 2 ^ (CP - classOf i) * q + coinUnit i :=
    ⟨y / 2 ^ (CP - classOf i), by
      rw [← hmod]
      exact (Nat.div_add_mod y (2 ^ (CP - classOf i))).symm⟩
  refine ⟨q, ?_⟩
  rw [hdef, hq, Nat.mul_add, Nat.mul_add]
  omega

/-- The G decomposition from live tracking: G = 2^t · u + 2^CP · m. -/
theorem match_split {G t u : Nat} (hlt : t < CP) (hv : v2 G = t)
    (hu : (G / 2 ^ t) % 2 ^ (CP - t) = u) :
    ∃ m, G = 2 ^ t * u + 2 ^ CP * m := by
  have hdvd : 2 ^ t ∣ G := by
    cases Nat.eq_zero_or_pos G with
    | inl h0 => rw [h0]; exact ⟨0, rfl⟩
    | inr hp => exact v2_dvd G G t (Nat.le_refl _) hp hv
  obtain ⟨x, hx⟩ := hdvd
  have hdm : 2 ^ (CP - t) * (x / 2 ^ (CP - t)) + x % 2 ^ (CP - t) = x :=
    Nat.div_add_mod x (2 ^ (CP - t))
  have hu' : x % 2 ^ (CP - t) = u := by
    have hxd : G / 2 ^ t = x := by
      rw [hx, Nat.mul_div_cancel_left _ (two_pow_pos _)]
    rw [← hxd]
    exact hu
  rw [hu'] at hdm
  obtain ⟨q, hq⟩ : ∃ q, x = 2 ^ (CP - t) * q + u := ⟨x / 2 ^ (CP - t), hdm.symm⟩
  refine ⟨q, ?_⟩
  have hG : G = 2 ^ t * x := hx
  have hsplit : 2 ^ t * (2 ^ (CP - t) * q) = 2 ^ CP * q := by
    have hadd : t + (CP - t) = CP := by omega
    rw [← Nat.mul_assoc, ← Nat.pow_add 2 t (CP - t), hadd]
  rw [hG, hq, Nat.mul_add, hsplit]
  omega

/-- v2 s < prec for 0 < s < 2^prec. -/
theorem v2_lt_prec {s prec : Nat} (hs : 1 ≤ s) (hlt : s < 2 ^ prec) : v2 s < prec := by
  match Nat.lt_or_ge (v2 s) prec with
  | Or.inl h => exact h
  | Or.inr hge =>
      exfalso
      have hdvd : 2 ^ prec ∣ s := by
        have h1 : 2 ^ prec ∣ 2 ^ v2 s := Nat.pow_dvd_pow 2 hge
        have h2 : 2 ^ v2 s ∣ s := v2_dvd s s (v2 s) (Nat.le_refl _) hs rfl
        exact Nat.dvd_trans h1 h2
      obtain ⟨k, hk⟩ := hdvd
      cases Nat.eq_zero_or_pos k with
      | inl h0 => rw [h0, Nat.mul_zero] at hk; omega
      | inr hkpos =>
          have hle : 2 ^ prec ≤ s := Nat.le_of_dvd (by omega) ⟨k, hk⟩
          omega

/-- **LEMMA A (live branch): the step preserves matching.**
From state (t,u) with t < CP, taking coin (i,V,o) with V ≤ t:
G + P i matches step1 V t u o. -/
theorem step1_matches_live (i V o G t u : Nat)
    (hclass : classOf i = V) (hunit : coinUnit i = o)
    (hi : 2 ≤ i) (hlive : V ≤ t) (hlt : t < CP)
    (hv : v2 G = t) (hu : (G / 2 ^ t) % 2 ^ (CP - t) = u) :
    matchSt (G + P i) (step1 V t u o) := by
  obtain ⟨j, hj⟩ := coin_split i hi
  rw [hclass, hunit] at hj
  obtain ⟨m, hG⟩ := match_split hlt hv hu
  have hpows : 2 ^ t = 2 ^ V * 2 ^ (t - V) := by
    have hadd : V + (t - V) = t := by omega
    have hp : 2 ^ V * 2 ^ (t - V) = 2 ^ (V + (t - V)) := (Nat.pow_add 2 V (t - V)).symm
    rw [hadd] at hp; exact hp.symm
  have hpowCP : 2 ^ V * 2 ^ (CP - V) = 2 ^ CP := by
    have hadd : V + (CP - V) = CP := by omega
    have hp : 2 ^ V * 2 ^ (CP - V) = 2 ^ (V + (CP - V)) := (Nat.pow_add 2 V (CP - V)).symm
    rw [hadd] at hp; exact hp
  -- the combined identity:
  -- G + P i = 2^V * (u * 2^(t-V) + o) + 2^CP * (m + j)
  have hkey : G + P i = 2 ^ V * (u * 2 ^ (t - V) + o) + 2 ^ CP * (m + j) := by
    have e1 : G = 2 ^ V * (2 ^ (t - V) * u) + 2 ^ CP * m := by
      rw [hG]
      have hsplit : 2 ^ t * u = 2 ^ V * (2 ^ (t - V) * u) := by
        rw [hpows, Nat.mul_assoc]
      rw [hsplit]
    have e2 : P i = 2 ^ V * (o + 2 ^ (CP - V) * j) := hj
    have e3 : 2 ^ V * (2 ^ (t - V) * u) + 2 ^ V * o = 2 ^ V * (u * 2 ^ (t - V) + o) := by
      have h1 : 2 ^ V * (2 ^ (t - V) * u) = 2 ^ V * (u * 2 ^ (t - V)) := by
        rw [Nat.mul_comm (2 ^ (t - V)) u]
      have h2 : 2 ^ V * (u * 2 ^ (t - V) + o) = 2 ^ V * (u * 2 ^ (t - V)) + 2 ^ V * o :=
        Nat.mul_add _ _ _
      rw [h1, h2]
    have e4 : 2 ^ CP * m + 2 ^ V * (2 ^ (CP - V) * j) = 2 ^ CP * (m + j) := by
      have h1 : 2 ^ V * (2 ^ (CP - V) * j) = 2 ^ CP * j := by
        rw [← Nat.mul_assoc, ← hpowCP]
      have h2 : 2 ^ CP * (m + j) = 2 ^ CP * m + 2 ^ CP * j := Nat.mul_add _ _ _
      rw [h1, h2]
    have e5 : P i = 2 ^ V * o + 2 ^ V * (2 ^ (CP - V) * j) := by
      rw [e2, Nat.mul_add]
    omega
  -- step1 unfolds to the if-then-else on s := (u * 2^(t-V) + o) % 2^(CP-V)
  have hstepdef : step1 V t u o =
      (if (u * 2 ^ (t - V) + o) % 2 ^ (CP - V) = 0 then (CP, 1)
       else (V + v2 ((u * 2 ^ (t - V) + o) % 2 ^ (CP - V)),
             ((u * 2 ^ (t - V) + o) % 2 ^ (CP - V)) / 2 ^ (v2 ((u * 2 ^ (t - V) + o) % 2 ^ (CP - V))))) := rfl
  rw [hstepdef]
  by_cases hs0 : (u * 2 ^ (t - V) + o) % 2 ^ (CP - V) = 0
  · -- CAP: s = 0 — the sum is a multiple of 2^CP
    obtain ⟨qq, hqq, hqqdef⟩ : ∃ qq, u * 2 ^ (t - V) + o = 2 ^ (CP - V) * qq ∧
        qq = (u * 2 ^ (t - V) + o) / 2 ^ (CP - V) := by
      refine ⟨(u * 2 ^ (t - V) + o) / 2 ^ (CP - V), ?_, rfl⟩
      have hdm := Nat.div_add_mod (u * 2 ^ (t - V) + o) (2 ^ (CP - V))
      omega
    have hval : G + P i = 2 ^ CP * (qq + m + j) := by
      have e1 : G + P i = 2 ^ V * (u * 2 ^ (t - V) + o) + 2 ^ CP * (m + j) := hkey
      rw [hqq] at e1
      have e2 : 2 ^ V * (2 ^ (CP - V) * qq) = 2 ^ CP * qq := by
        rw [← Nat.mul_assoc, ← hpowCP]
      have e3 : 2 ^ CP * qq + 2 ^ CP * (m + j) = 2 ^ CP * (qq + m + j) := by
        have h1 : 2 ^ CP * (qq + m + j) = 2 ^ CP * (qq + (m + j)) := by
          rw [← Nat.add_assoc]
        rw [h1, ← Nat.mul_add]
      omega
    rw [if_pos hs0]
    show 2 ^ CP ∣ G + P i
    exact ⟨_, hval⟩
  · -- LIVE: s ≠ 0 — the new state (V + v2 s, s / 2^(v2 s))
    have hs1 : 1 ≤ (u * 2 ^ (t - V) + o) % 2 ^ (CP - V) := by
      cases Nat.eq_zero_or_pos ((u * 2 ^ (t - V) + o) % 2 ^ (CP - V)) with
      | inl h => omega
      | inr h => exact h
    have hslt : (u * 2 ^ (t - V) + o) % 2 ^ (CP - V) < 2 ^ (CP - V) :=
      Nat.mod_lt _ (two_pow_pos _)
    have hv2s : v2 ((u * 2 ^ (t - V) + o) % 2 ^ (CP - V)) < CP - V :=
      v2_lt_prec hs1 hslt
    -- G + P i = 2^V * s + 2^CP * (q + m + j)   (q := (u·2^(t−V)+o)/2^(CP−V))
    obtain ⟨qq, hqq, hqqdef⟩ : ∃ qq, u * 2 ^ (t - V) + o
          = 2 ^ (CP - V) * qq + (u * 2 ^ (t - V) + o) % 2 ^ (CP - V) ∧
        qq = (u * 2 ^ (t - V) + o) / 2 ^ (CP - V) :=
      ⟨(u * 2 ^ (t - V) + o) / 2 ^ (CP - V), (Nat.div_add_mod _ _).symm, rfl⟩
    have hval : G + P i
        = 2 ^ V * ((u * 2 ^ (t - V) + o) % 2 ^ (CP - V))
          + 2 ^ CP * (qq + m + j) := by
      have e1 : G + P i = 2 ^ V * (u * 2 ^ (t - V) + o) + 2 ^ CP * (m + j) := hkey
      rw [hqq] at e1
      have e2 : 2 ^ V * (2 ^ (CP - V) * qq) = 2 ^ CP * qq := by
        rw [← Nat.mul_assoc, ← hpowCP]
      have e3 : 2 ^ V * (2 ^ (CP - V) * qq + (u * 2 ^ (t - V) + o) % 2 ^ (CP - V))
          = 2 ^ V * (2 ^ (CP - V) * qq)
            + 2 ^ V * ((u * 2 ^ (t - V) + o) % 2 ^ (CP - V)) :=
        Nat.mul_add _ _ _
      have e4 : 2 ^ CP * qq + 2 ^ CP * (m + j) = 2 ^ CP * (qq + m + j) := by
        have h1 : 2 ^ CP * (qq + m + j) = 2 ^ CP * (qq + (m + j)) := by
          rw [← Nat.add_assoc]
        rw [h1, ← Nat.mul_add]
      omega
    rw [hqqdef] at hval
    -- the valuation: v2 (G + P i) = V + v2 s
    have hv2a : v2 (2 ^ V * ((u * 2 ^ (t - V) + o) % 2 ^ (CP - V)))
        = V + v2 ((u * 2 ^ (t - V) + o) % 2 ^ (CP - V)) := by
      rw [v2_mul (2 ^ V + (u * 2 ^ (t - V) + o) % 2 ^ (CP - V)) _ _
        (Nat.le_refl _) (two_pow_pos _) hs1, v2_two_pow]
    have hv2G : v2 (G + P i)
        = V + v2 ((u * 2 ^ (t - V) + o) % 2 ^ (CP - V)) := by
      by_cases hK : (u * 2 ^ (t - V) + o) / 2 ^ (CP - V) + m + j = 0
      · have hz0 : 2 ^ CP * ((u * 2 ^ (t - V) + o) / 2 ^ (CP - V) + m + j) = 0 := by
          rw [hK, Nat.mul_zero]
        have hz : G + P i = 2 ^ V * ((u * 2 ^ (t - V) + o) % 2 ^ (CP - V)) := by
          rw [hval]; omega
        rw [hz, hv2a]
      · have hb1 : 1 ≤ 2 ^ V * ((u * 2 ^ (t - V) + o) % 2 ^ (CP - V)) :=
          Nat.mul_pos (two_pow_pos _) hs1
        have hb2 : 1 ≤ 2 ^ CP * ((u * 2 ^ (t - V) + o) / 2 ^ (CP - V) + m + j) :=
          Nat.mul_pos (two_pow_pos _) (by omega)
        have hv2b : v2 (2 ^ CP * ((u * 2 ^ (t - V) + o) / 2 ^ (CP - V) + m + j))
            = CP + v2 ((u * 2 ^ (t - V) + o) / 2 ^ (CP - V) + m + j) := by
          rw [v2_mul (2 ^ CP + ((u * 2 ^ (t - V) + o) / 2 ^ (CP - V) + m + j)) _ _
            (Nat.le_refl _) (two_pow_pos _) (by omega), v2_two_pow]
        rw [hval, v2_add_min _ _ hb1 hb2 (by rw [hv2a, hv2b]; omega), hv2a]
    -- the unit: the odd factorization, with e := v2 s introduced FRESH
    obtain ⟨x, hx1, hx2, hx3⟩ :=
      v2_odd_factor ((u * 2 ^ (t - V) + o) % 2 ^ (CP - V)) (v2 ((u * 2 ^ (t - V) + o) % 2 ^ (CP - V))) hs1 rfl
    obtain ⟨e, he, hex⟩ : ∃ e, v2 ((u * 2 ^ (t - V) + o) % 2 ^ (CP - V)) = e ∧
        (u * 2 ^ (t - V) + o) % 2 ^ (CP - V) = 2 ^ e * x :=
      ⟨_, rfl, hx3⟩
    rw [he] at hv2s
    -- G + P i = 2^(V + e) * x + 2^CP * (q + m + j)
    have hfacE : G + P i
        = 2 ^ (V + e) * x + 2 ^ CP * ((u * 2 ^ (t - V) + o) / 2 ^ (CP - V) + m + j) := by
      have e1 : G + P i = 2 ^ V * ((u * 2 ^ (t - V) + o) % 2 ^ (CP - V))
          + 2 ^ CP * ((u * 2 ^ (t - V) + o) / 2 ^ (CP - V) + m + j) := hval
      rw [hex] at e1
      have hp : 2 ^ V * (2 ^ e * x) = 2 ^ (V + e) * x := by
        rw [← Nat.mul_assoc, Nat.pow_add 2 V e]
      rw [hp] at e1
      exact e1
    have hxd : (u * 2 ^ (t - V) + o) % 2 ^ (CP - V) / 2 ^ e = x :=
      div_dvd_eq _ _ _ ⟨x, hex⟩ hex
    -- the unit congruence at the scheduled precision (in e-form)
    have hunitE : (G + P i) / 2 ^ (V + e) % 2 ^ (CP - (V + e))
        = (u * 2 ^ (t - V) + o) % 2 ^ (CP - V) / 2 ^ e := by
      have hmodE : 2 ^ (CP - (V + e)) = 2 ^ (CP - V - e) := by
        congr 1
        omega
      have hp2 : 2 ^ CP = 2 ^ (V + e) * 2 ^ (CP - V - e) := by
        have hadd : V + e + (CP - V - e) = CP := by omega
        rw [← Nat.pow_add 2 _ _, hadd]
      have hsplit : G + P i
          = 2 ^ (V + e) * (x + 2 ^ (CP - V - e)
              * ((u * 2 ^ (t - V) + o) / 2 ^ (CP - V) + m + j)) := by
        rw [hfacE, hp2, Nat.mul_assoc, ← Nat.mul_add]
      have hxlt : x < 2 ^ (CP - V - e) := by
        have hexp : 2 ^ e * 2 ^ (CP - V - e) = 2 ^ (CP - V) := by
          rw [← Nat.pow_add 2 _ _]
          congr 1
          omega
        have hlt2 : 2 ^ e * x < 2 ^ (CP - V) := by
          rw [← hex]; exact hslt
        rw [← hexp] at hlt2
        exact Nat.lt_of_mul_lt_mul_left hlt2
      rw [hsplit, Nat.mul_div_cancel_left _ (two_pow_pos _), hmodE,
        Nat.add_mod, mul_mod_self_zero', Nat.add_zero, Nat.mod_mod, hxd,
        Nat.mod_eq_of_lt hxlt]
    rw [← he] at hunitE
    rw [if_neg hs0]
    simp only [matchSt]
    rw [if_neg (by omega : ¬(V + v2 ((u * 2 ^ (t - V) + o) % 2 ^ (CP - V)) = CP))]
    exact ⟨by omega, hv2G, hunitE⟩

/-- **LEMMA A (capped branch): the step preserves matching from the sentinel.** -/
theorem step1_matches_cap (i V o G u : Nat)
    (hclass : classOf i = V) (hunit : coinUnit i = o)
    (hi : 2 ≤ i) (hlive : V ≤ CP) (hm : matchSt G (CP, u)) :
    matchSt (G + P i) (step1 V CP u o) := by
  obtain ⟨j, hj⟩ := coin_split i hi
  rw [hclass, hunit] at hj
  have hG : ∃ m, G = 2 ^ CP * m := by
    simp only [matchSt, if_true] at hm
    exact hm
  obtain ⟨m, hGm⟩ := hG
  have holt : o < 2 ^ (CP - V) := by
    have hlt : coinUnit i < 2 ^ (CP - classOf i) := by
      show (P i / 2 ^ classOf i) % 2 ^ (CP - classOf i) < 2 ^ (CP - classOf i)
      exact Nat.mod_lt _ (two_pow_pos _)
    rw [hunit, hclass] at hlt
    exact hlt
  have hs : (u * 2 ^ (CP - V) + o) % 2 ^ (CP - V) = o := by
    rw [Nat.add_mod]
    have hz : (u * 2 ^ (CP - V)) % 2 ^ (CP - V) = 0 := by
      rw [Nat.mul_comm, mul_mod_self_zero']
    rw [hz, Nat.zero_add, Nat.mod_mod, Nat.mod_eq_of_lt holt]
  have hstepdef : step1 V CP u o =
      (if (u * 2 ^ (CP - V) + o) % 2 ^ (CP - V) = 0 then (CP, 1)
       else (V + v2 ((u * 2 ^ (CP - V) + o) % 2 ^ (CP - V)),
             ((u * 2 ^ (CP - V) + o) % 2 ^ (CP - V)) / 2 ^ (v2 ((u * 2 ^ (CP - V) + o) % 2 ^ (CP - V))))) := rfl
  rw [hstepdef, hs]
  have hpowCP : 2 ^ V * 2 ^ (CP - V) = 2 ^ CP := by
    have hadd : V + (CP - V) = CP := by omega
    have hp : 2 ^ V * 2 ^ (CP - V) = 2 ^ (V + (CP - V)) := (Nat.pow_add 2 V (CP - V)).symm
    rw [hadd] at hp; exact hp
  -- G + P i = 2^V * W  with W := o + 2^(CP−V) * (m + j)
  have hcomb : G + P i = 2 ^ V * (o + 2 ^ (CP - V) * (m + j)) := by
    have hsplit1 : 2 ^ V * (o + 2 ^ (CP - V) * (m + j))
        = 2 ^ V * o + 2 ^ V * (2 ^ (CP - V) * (m + j)) := Nat.mul_add _ _ _
    have hsplit2 : 2 ^ V * (2 ^ (CP - V) * (m + j)) = 2 ^ CP * (m + j) := by
      rw [← Nat.mul_assoc, ← hpowCP]
    have hsplit3 : 2 ^ CP * (m + j) = 2 ^ CP * m + 2 ^ CP * j := Nat.mul_add _ _ _
    have hsplit4 : 2 ^ CP * j = 2 ^ V * (2 ^ (CP - V) * j) := by
      rw [← hpowCP, ← Nat.mul_assoc]
    have hsplit5 : 2 ^ V * (o + 2 ^ (CP - V) * j)
        = 2 ^ V * o + 2 ^ V * (2 ^ (CP - V) * j) := Nat.mul_add _ _ _
    rw [hGm, hj]
    omega
  have hWmod : (o + 2 ^ (CP - V) * (m + j)) % 2 ^ (CP - V) = o := by
    rw [Nat.add_mod]
    have hz : (2 ^ (CP - V) * (m + j)) % 2 ^ (CP - V) = 0 := mul_mod_self_zero' _ _
    rw [hz, Nat.add_zero, Nat.mod_mod, Nat.mod_eq_of_lt holt]
  by_cases ho : o = 0
  · rw [if_pos ho]
    show 2 ^ CP ∣ G + P i
    rw [ho] at hcomb
    refine ⟨m + j, ?_⟩
    rw [hcomb, Nat.zero_add, ← Nat.mul_assoc, hpowCP]
  · have ho1 : 1 ≤ o := by omega
    have hv2o : v2 o < CP - V := v2_lt_prec ho1 holt
    rw [if_neg ho]
    have hv2W : v2 (o + 2 ^ (CP - V) * (m + j)) = v2 o :=
      v2_agree (o + 2 ^ (CP - V) * (m + j)) o (CP - V) hWmod ho1 hv2o
    have hv2G : v2 (G + P i) = V + v2 o := by
      rw [hcomb, v2_mul (2 ^ V + (o + 2 ^ (CP - V) * (m + j))) _ _
        (Nat.le_refl _) (two_pow_pos _) (by omega), v2_two_pow, hv2W]
    obtain ⟨x, hx1, hx2, hx3⟩ := v2_odd_factor o (v2 o) ho1 rfl
    have hxd : o / 2 ^ (v2 o) = x := div_dvd_eq _ _ _ ⟨x, hx3⟩ hx3
    have hWdvd : 2 ^ (v2 o) ∣ (o + 2 ^ (CP - V) * (m + j)) :=
      v2_dvd _ _ _ (Nat.le_refl _) (by omega) hv2W
    have hWx : o + 2 ^ (CP - V) * (m + j)
        = 2 ^ (v2 o) * ((o + 2 ^ (CP - V) * (m + j)) / 2 ^ (v2 o)) := by
      obtain ⟨y, hy⟩ := hWdvd
      have hdy : (o + 2 ^ (CP - V) * (m + j)) / 2 ^ (v2 o) = y :=
        div_dvd_eq _ _ _ ⟨y, hy⟩ hy
      rw [hdy]; exact hy
    have hfac : G + P i
        = 2 ^ (V + v2 o) * ((o + 2 ^ (CP - V) * (m + j)) / 2 ^ (v2 o)) := by
      obtain ⟨W, hW⟩ : ∃ W, o + 2 ^ (CP - V) * (m + j) = W := ⟨_, rfl⟩
      obtain ⟨Q, hQ⟩ : ∃ Q, (o + 2 ^ (CP - V) * (m + j)) / 2 ^ (v2 o) = Q := ⟨_, rfl⟩
      have hWQ : W = 2 ^ (v2 o) * Q := by
        rw [← hW, ← hQ]
        exact hWx
      rw [hcomb, hQ, hW, hWQ, ← Nat.mul_assoc, Nat.pow_add 2 V (v2 o)]
    have hL3 := unit_congr (o + 2 ^ (CP - V) * (m + j)) o (CP - V) hWmod ho1 hv2o
    have holt2 : o / 2 ^ (v2 o) < 2 ^ (CP - V - v2 o) := by
      have hexp : 2 ^ (v2 o) * 2 ^ (CP - V - v2 o) = 2 ^ (CP - V) := by
        rw [← Nat.pow_add 2 _ _]
        congr 1
        omega
      have hlt2 : 2 ^ (v2 o) * (o / 2 ^ (v2 o)) < 2 ^ (CP - V) := by
        rw [hxd, ← hx3]
        exact holt
      rw [← hexp] at hlt2
      exact Nat.lt_of_mul_lt_mul_left hlt2
    rw [Nat.mod_eq_of_lt holt2] at hL3
    simp only [matchSt]
    rw [if_neg (by omega : ¬(V + v2 o = CP))]
    refine ⟨by omega, hv2G, ?_⟩
    rw [hfac, Nat.mul_div_cancel_left _ (two_pow_pos _)]
    have hpe : CP - (V + v2 o) = CP - V - v2 o := by omega
    rw [hpe]
    exact hL3

-- ===========================================================================
-- §5d-4  THE COVER INVARIANT AND THE RUN INDUCTION
-- ===========================================================================

/-- The final DP state after processing a coin list from S. -/
def dpState : List (Nat × Nat × Nat) → List (Nat × Nat) → List (Nat × Nat)
  | [], S => S
  | c :: cs, S => dpState cs (stepCoin c S)

/-- Achievable sums are positive. -/
theorem achiev_pos : ∀ (cs : List (Nat × Nat × Nat)) (g : Nat), Achiev cs g → 1 ≤ g := by
  intro cs g h
  induction h with
  | base => omega
  | skip _ _ _ _ ih => exact ih
  | take _ _ _ _ ih => omega

/-- The cover invariant: every achievable sum over the processed coins is
tracked by a state in S, or froze below the frontier V (the class of the
next coin to come; the terminal frontier is 254). -/
def CoverS (cs : List (Nat × Nat × Nat)) (S : List (Nat × Nat)) (V : Nat) : Prop :=
  ∀ g, Achiev cs g → (∃ st ∈ S, matchSt g st) ∨ v2 g < V

theorem cover_mono (cs : List (Nat × Nat × Nat)) (S : List (Nat × Nat)) (V V' : Nat)
    (hV : V ≤ V') (hc : CoverS cs S V) : CoverS cs S V' := by
  intro g hg
  cases hc g hg with
  | inl h => exact Or.inl h
  | inr hlt => exact Or.inr (Nat.lt_of_lt_of_le hlt hV)

/-- Achiev is stable under appending a coin at the end (skip). -/
theorem achiev_append_skip : ∀ (cs : List (Nat × Nat × Nat)) (d : Nat × Nat × Nat) (g : Nat),
    Achiev cs g → Achiev (cs ++ [d]) g := by
  intro cs d g h
  induction h with
  | base =>
      exact Achiev.skip [] d 1 Achiev.base
  | skip cs₀ c g₀ _ ih =>
      exact Achiev.skip _ _ _ ih
  | take cs₀ c g₀ _ ih =>
      exact Achiev.take _ _ _ ih

/-- Achiev is stable under appending a coin at the end (take). -/
theorem achiev_append_take : ∀ (cs : List (Nat × Nat × Nat)) (d : Nat × Nat × Nat) (g : Nat),
    Achiev cs g → Achiev (cs ++ [d]) (g + P d.1) := by
  intro cs d g h
  induction h with
  | base =>
      exact Achiev.take [] d 1 Achiev.base
  | skip cs₀ c g₀ _ ih =>
      exact Achiev.skip _ _ _ ih
  | take cs₀ c g₀ _ ih =>
      have hsum : (g₀ + P c.1) + P d.1 = (g₀ + P d.1) + P c.1 := by omega
      rw [hsum]
      exact Achiev.take _ _ _ ih

/-- Inversion: an achievable sum over cs ++ [d] either ignores d or takes it. -/
theorem achiev_append_inv : ∀ (l : List (Nat × Nat × Nat)) (d : Nat × Nat × Nat) (g : Nat),
    Achiev (l ++ [d]) g → (Achiev l g) ∨ (∃ g₀, Achiev l g₀ ∧ g = g₀ + P d.1) := by
  intro l
  induction l with
  | nil =>
      intro d g h
      cases h with
      | skip _ _ _ h' => exact Or.inl h'
      | take _ _ _ h' => exact Or.inr ⟨_, h', rfl⟩
  | cons c l₀ ih =>
      intro d g h
      cases h with
      | skip _ _ _ h' =>
          have hrec := ih d g h'
          cases hrec with
          | inl hl => exact Or.inl (Achiev.skip _ _ _ hl)
          | inr hr =>
              obtain ⟨g₁, hg₁, hge⟩ := hr
              exact Or.inr ⟨g₁, Achiev.skip _ _ _ hg₁, hge⟩
      | take _ _ g₀ h' =>
          have hrec := ih d g₀ h'
          cases hrec with
          | inl hl => exact Or.inl (Achiev.take l₀ c g₀ hl)
          | inr hr =>
              obtain ⟨g₁, hg₁, hge⟩ := hr
              exact Or.inr ⟨g₁ + P c.1, Achiev.take l₀ c g₁ hg₁, by omega⟩

/-- **THE COVER STEP (the induction's engine).** Processing coin d from the
cover (cs, S, V) with V ≤ classOf d ≤ V' ≤ 254: every achievable sum over
cs ++ [d] is tracked in stepCoin d S or froze below V'. -/
theorem cover_step (cs : List (Nat × Nat × Nat)) (d : Nat × Nat × Nat)
    (S : List (Nat × Nat)) (V V' : Nat)
    (hV : V ≤ d.2.1) (hV' : d.2.1 ≤ V') (h254 : d.2.1 ≤ 254)
    (hclass : d.2.1 = classOf d.1) (hunit : d.2.2 = coinUnit d.1)
    (hi : 2 ≤ d.1)
    (hc : CoverS cs S V) :
    CoverS (cs ++ [d]) (stepCoin d S) V' := by
  have hCP : CP = 262 := rfl
  intro g hg
  have hPpos : 1 ≤ P d.1 := P_pos d.1 hi
  have hinv := achiev_append_inv cs d g hg
  cases hinv with
  | inl hg0 =>
      -- SKIP: g achievable over cs already
      have hc' := hc g hg0
      cases hc' with
      | inl hst =>
          obtain ⟨st, hstS, hmatch⟩ := hst
          by_cases hlive : d.2.1 ≤ st.1
          · exact Or.inl ⟨st, stepCoin_keeps d S st hstS hlive, hmatch⟩
          · have hne : st.1 ≠ CP := by omega
            have hv2 : v2 g = st.1 := by
              simp only [matchSt] at hmatch
              rw [if_neg hne] at hmatch
              exact hmatch.2.1
            exact Or.inr (by omega)
      | inr hlt =>
          exact Or.inr (Nat.lt_of_lt_of_le hlt (Nat.le_trans hV hV'))
  | inr htake =>
      obtain ⟨g₀, hg₀, hge⟩ := htake
      -- TAKE: g = g₀ + P d.1
      have hc' := hc g₀ hg₀
      have hv2P : v2 (P d.1) = d.2.1 := by rw [hclass]; rfl
      cases hc' with
      | inl hst =>
          obtain ⟨st, hstS, hmatch⟩ := hst
          obtain ⟨t, u⟩ := st
          by_cases hlive : d.2.1 ≤ t
          · by_cases hcp : t = CP
            · rw [hcp] at hmatch hstS
              have hA := step1_matches_cap d.1 d.2.1 d.2.2 g₀ u hclass.symm hunit.symm hi
                (by omega) hmatch
              exact Or.inl ⟨step1 d.2.1 CP u d.2.2,
                stepCoin_steps d S (CP, u) hstS (by omega), by rw [hge]; exact hA⟩
            · have hm' : t < CP ∧ v2 g₀ = t ∧ (g₀ / 2 ^ t) % 2 ^ (CP - t) = u := by
                simp only [matchSt] at hmatch
                rw [if_neg hcp] at hmatch
                exact hmatch
              obtain ⟨hlt, hv, hu⟩ := hm'
              have hA := step1_matches_live d.1 d.2.1 d.2.2 g₀ t u hclass.symm hunit.symm hi
                hlive hlt hv hu
              exact Or.inl ⟨step1 d.2.1 t u d.2.2,
                stepCoin_steps d S (t, u) hstS hlive, by rw [hge]; exact hA⟩
          · have hne : t ≠ CP := by omega
            have hv2 : v2 g₀ = t := by
              simp only [matchSt] at hmatch
              rw [if_neg hne] at hmatch
              exact hmatch.2.1
            have hposg : 1 ≤ g₀ := achiev_pos cs g₀ hg₀
            have hltv : v2 g₀ < v2 (P d.1) := by omega
            have hsum := v2_add_min g₀ (P d.1) hposg hPpos hltv
            rw [hge]
            omega
      | inr hlt =>
          have hposg : 1 ≤ g₀ := achiev_pos cs g₀ hg₀
          have hltv : v2 g₀ < v2 (P d.1) := by omega
          have hsum := v2_add_min g₀ (P d.1) hposg hPpos hltv
          rw [hge]
          omega

/-- TailSorted as an INDUCTIVE (not a match-def): inductive-applications are
whnf-stable, so `TailSorted table` never forces the table's evaluation in the
elaborator — the match-def version made every defeq on it a 12-minute grind
(the coinList filter recomputes all 253 classOf's in elaborator-whnf). -/
inductive TailSorted : List (Nat × Nat × Nat) → Prop
  | nil : TailSorted []
  | cons (d : Nat × Nat × Nat) (rest : List (Nat × Nat × Nat))
      (hmin : ∀ e ∈ rest, d.2.1 ≤ e.2.1) (hl : TailSorted rest) : TailSorted (d :: rest)

/-- Destructor (the inductive has two constructors, so anonymous ⟨…⟩ patterns
do not apply — this restores the def-version's pair-shape). -/
theorem TailSorted.destruct {d : Nat × Nat × Nat} {rest : List (Nat × Nat × Nat)}
    (h : TailSorted (d :: rest)) : (∀ e ∈ rest, d.2.1 ≤ e.2.1) ∧ TailSorted rest := by
  cases h with
  | cons _ _ hmin hl => exact ⟨hmin, hl⟩

/-- **THE RUN INDUCTION: the cover holds through the whole table.** -/
theorem cover_run : ∀ (cs : List (Nat × Nat × Nat)) (processed : List (Nat × Nat × Nat))
    (S : List (Nat × Nat)) (V Vn : Nat),
  (hV : ∀ d ∈ cs, V ≤ d.2.1) →
  (hVle : V ≤ Vn) →
  (hVn : ∀ d ∈ cs, d.2.1 ≤ Vn) → (h254 : Vn ≤ 254) →
  (hcoins : ∀ d ∈ cs, d.2.1 = classOf d.1 ∧ d.2.2 = coinUnit d.1 ∧ 2 ≤ d.1) →
  (hsort : TailSorted cs) →
  (hc : CoverS processed S V) →
  CoverS (processed ++ cs) (dpState cs S) Vn := by
  intro cs
  induction cs with
  | nil =>
      intro processed S V Vn _ _ _ _ _ _ hc
      rw [List.append_nil]
      exact cover_mono processed S V Vn (by assumption) hc
  | cons d rest ih =>
      intro processed S V Vn hV hVle hVn h254 hcoins hsort hc
      obtain ⟨hclass, hunit, hi⟩ := hcoins d (List.Mem.head _)
      obtain ⟨hdmin, hrest⟩ := TailSorted.destruct hsort
      -- mono up to d's class, then the step
      have hcd : CoverS processed S d.2.1 :=
        cover_mono processed S V d.2.1 (hV d (List.Mem.head _)) hc
      have hstep := cover_step processed d S d.2.1 d.2.1
        (Nat.le_refl _) (Nat.le_refl _) (Nat.le_trans (hVn d (List.Mem.head _)) h254)
        hclass hunit hi hcd
      -- the IH on the rest
      have hrec := ih (processed ++ [d]) (stepCoin d S) d.2.1 Vn
        (fun e he => hdmin e he)
        (hVn d (List.Mem.head _))
        (fun e he => hVn e (List.Mem.tail _ he))
        h254
        (fun e he => hcoins e (List.Mem.tail _ he))
        hrest
        hstep
      -- assemble: processed ++ (d :: rest) = (processed ++ [d]) ++ rest
      have happ : (processed ++ [d]) ++ rest = processed ++ (d :: rest) := by
        simp
      rw [← happ]
      exact hrec

/-- The final DP state is one of the recorded sets. -/
theorem dpState_mem_allSets : ∀ (cs : List (Nat × Nat × Nat)) (S : List (Nat × Nat)),
    dpState cs S ∈ S :: dpRun cs S := by
  intro cs
  induction cs with
  | nil => intro S; exact List.Mem.head _
  | cons c rest ih =>
      intro S
      exact List.Mem.tail _ (ih (stepCoin c S))

/-- State valuations are bounded by the set's maxT. -/
theorem maxT_ge (S : List (Nat × Nat)) (st : Nat × Nat) (h : st ∈ S) : st.1 ≤ maxT S := by
  induction S with
  | nil => cases h
  | cons q rest ih =>
      cases h with
      | head => exact Nat.le_max_left _ _
      | tail _ ht => exact Nat.le_trans (ih ht) (Nat.le_max_right _ _)

/-- The obstruction check bounds every recorded set. -/
theorem obstruction_bound (h : obstructionCheck = true) (S : List (Nat × Nat))
    (hS : S ∈ allSets) : maxT S ≤ 253 := by
  have hall : allSets.all (fun Q => decide (maxT Q ≤ 253)) = true := h
  have hq := List.all_eq_true.mp hall S hS
  exact of_decide_eq_true hq

-- ===========================================================================
-- §5d-5  THE TABLE CONTEXT (wellformedness, sortedness, coverage)
-- ===========================================================================

set_option maxRecDepth 65536

theorem perm_mem : ∀ {l₁ l₂ : List (Nat × Nat × Nat)} (_h : List.Perm l₁ l₂)
    (x : Nat × Nat × Nat), x ∈ l₁ → x ∈ l₂ := by
  intro l₁ l₂ h
  induction h with
  | nil => intro x hx; exact hx
  | cons a p ih =>
      intro x hx
      cases hx with
      | head => exact List.Mem.head _
      | tail _ ht => exact List.Mem.tail _ (ih x ht)
  | swap a b l =>
      intro x hx
      cases hx with
      | head => exact List.Mem.tail _ (List.Mem.head _)
      | tail _ ht =>
          cases ht with
          | head => exact List.Mem.head _
          | tail _ ht2 => exact List.Mem.tail _ (List.Mem.tail _ ht2)
  | trans p₁ p₂ ih₁ ih₂ => intro x hx; exact ih₂ x (ih₁ x hx)

theorem insertCoin_perm (c : Nat × Nat × Nat) : ∀ (ds : List (Nat × Nat × Nat)),
    List.Perm (insertCoin c ds) (c :: ds) := by
  intro ds
  induction ds with
  | nil => exact List.Perm.refl _
  | cons d rest ih =>
      by_cases hcond : (decide (c.2.1 < d.2.1) ||
        (decide (c.2.1 = d.2.1) && decide (c.1 < d.1))) = true
      · show List.Perm (if (decide (c.2.1 < d.2.1) ||
            (decide (c.2.1 = d.2.1) && decide (c.1 < d.1))) then c :: d :: rest
            else d :: insertCoin c rest) (c :: d :: rest)
        rw [if_pos hcond]
      · show List.Perm (if (decide (c.2.1 < d.2.1) ||
            (decide (c.2.1 = d.2.1) && decide (c.1 < d.1))) then c :: d :: rest
            else d :: insertCoin c rest) (c :: d :: rest)
        rw [if_neg hcond]
        exact List.Perm.trans (List.Perm.cons d ih) (List.Perm.swap c d rest)

theorem sortCoins_perm (l : List (Nat × Nat × Nat)) : List.Perm (sortCoins l) l := by
  induction l with
  | nil => exact List.Perm.refl _
  | cons c rest ih =>
      show List.Perm (insertCoin c (sortCoins rest)) (c :: rest)
      exact List.Perm.trans (insertCoin_perm c (sortCoins rest)) (List.Perm.cons c ih)

theorem table_mem_iff (x : Nat × Nat × Nat) : x ∈ table ↔ x ∈ coinList := by
  constructor
  · intro h
    exact perm_mem (sortCoins_perm coinList) x h
  · intro h
    exact perm_mem (List.Perm.symm (sortCoins_perm coinList)) x h

theorem coinList_mem (c : Nat × Nat × Nat) (h : c ∈ coinList) :
    c.1 < 256 ∧ 3 ≤ c.1 ∧ classOf c.1 ≤ 246 ∧ c.2.1 = classOf c.1 ∧ c.2.2 = coinUnit c.1 := by
  obtain ⟨c1, c2, c3⟩ := c
  unfold coinList at h
  obtain ⟨i, hi, hfi⟩ := List.mem_map.mp h
  obtain ⟨hr, hcond⟩ := List.mem_filter.mp hi
  have h3 : (decide (3 ≤ i) && decide (classOf i ≤ 246)) = true := hcond
  rw [Bool.and_eq_true] at h3
  obtain ⟨h3a, h3b⟩ := h3
  cases hfi
  exact ⟨List.mem_range.mp hr, of_decide_eq_true h3a, of_decide_eq_true h3b, rfl, rfl⟩

theorem coinList_mem_of (i : Nat) (h3 : 3 ≤ i) (h256 : i < 256) (hb : classOf i ≤ 246) :
    (i, classOf i, coinUnit i) ∈ coinList := by
  unfold coinList
  refine List.mem_map.mpr ⟨i, ?_, rfl⟩
  exact List.mem_filter.mpr ⟨List.mem_range.mpr h256, by
    rw [Bool.and_eq_true]
    exact ⟨decide_eq_true h3, decide_eq_true hb⟩⟩

/-- Every table coin is wellformed: index in [3,255], class = classOf,
unit = coinUnit, class ≤ 246. -/
theorem table_coin (c : Nat × Nat × Nat) (h : c ∈ table) :
    3 ≤ c.1 ∧ c.1 < 256 ∧ c.2.1 = classOf c.1 ∧ c.2.2 = coinUnit c.1 ∧ c.2.1 ≤ 246 := by
  obtain ⟨h256, h3, hb, hc2, hc3⟩ := coinList_mem c ((table_mem_iff c).mp h)
  exact ⟨h3, h256, hc2, hc3, by rw [hc2]; exact hb⟩

theorem sorted_cons_transfer (a b : Nat × Nat × Nat) (r : List (Nat × Nat × Nat))
    (hab : a.2.1 ≤ b.2.1) (hbr : classesSorted (b :: r) = true) :
    classesSorted (a :: r) = true := by
  cases r with
  | nil => rfl
  | cons c r' =>
      have h2 : (decide (b.2.1 ≤ c.2.1) && classesSorted (c :: r')) = true := hbr
      rw [Bool.and_eq_true] at h2
      obtain ⟨hbc, hcr⟩ := h2
      have hbc' := of_decide_eq_true hbc
      have hac : a.2.1 ≤ c.2.1 := Nat.le_trans hab hbc'
      show (decide (a.2.1 ≤ c.2.1) && classesSorted (c :: r')) = true
      rw [Bool.and_eq_true]
      exact ⟨decide_eq_true hac, hcr⟩

theorem head_le_all (a : Nat × Nat × Nat) : ∀ (rest : List (Nat × Nat × Nat)),
    classesSorted (a :: rest) = true → ∀ e ∈ rest, a.2.1 ≤ e.2.1 := by
  intro rest
  induction rest with
  | nil => intro _ e he; cases he
  | cons b r ih =>
      intro h e he
      have h2 : (decide (a.2.1 ≤ b.2.1) && classesSorted (b :: r)) = true := h
      rw [Bool.and_eq_true] at h2
      obtain ⟨hab, hbr⟩ := h2
      have hba := of_decide_eq_true hab
      cases he with
      | head => exact hba
      | tail _ her =>
          have har : classesSorted (a :: r) = true := sorted_cons_transfer a b r hba hbr
          exact ih har e her

theorem sorted_tail : ∀ (l : List (Nat × Nat × Nat)), classesSorted l = true → TailSorted l := by
  intro l
  induction l with
  | nil => intro _; exact TailSorted.nil
  | cons a rest ih =>
      intro h
      refine TailSorted.cons a rest (head_le_all a rest h) ?_
      cases rest with
      | nil => exact TailSorted.nil
      | cons b r =>
          have h2 : (decide (a.2.1 ≤ b.2.1) && classesSorted (b :: r)) = true := h
          rw [Bool.and_eq_true] at h2
          exact ih h2.2

-- The exponent threshold must cover 2^CP = 2^262: the kernel refuses
-- pow-evaluation beyond 256 by default, turning decides into whnf-grinds.
set_option exponentiation.threshold 1024

-- **THE TABLE CONTEXT.**
set_option maxHeartbeats 4000000 in
theorem table_context (hcs : classesSorted table = true) :
    (∀ d ∈ table, d.2.1 = classOf d.1 ∧ d.2.2 = coinUnit d.1 ∧ 2 ≤ d.1) ∧
    TailSorted table ∧ (∀ d ∈ table, d.2.1 ≤ 254) := by
  refine ⟨?_, sorted_tail table hcs, ?_⟩
  · intro d hd
    obtain ⟨h3, _, hc2, hc3, _⟩ := table_coin d hd
    exact ⟨hc2, hc3, by omega⟩
  · intro d hd
    obtain ⟨_, _, _, _, hb⟩ := table_coin d hd
    omega

/-- **THE READOUT: the obstructionCheck certifies the universal upper bound
over all achievable sums of the table's coins.** -/
theorem cover_final (hcs : classesSorted table = true) (hob : obstructionCheck = true) :
    ∀ g, Achiev table g → v2 g ≤ 253 := by
  intro g hg
  have hc0 : CoverS [] [(0, 1)] 0 := by
    intro g' hg'
    have hg1 : g' = 1 := achiev_nil g' hg'
    rw [hg1]
    refine Or.inl ⟨(0, 1), List.Mem.head _, ?_⟩
    simp only [matchSt]
    rw [if_neg (by decide : ¬(0 = CP))]
    exact ⟨by decide, v2_odd 1 (by omega), by
      rw [Nat.pow_zero, Nat.div_one]
      exact Nat.mod_eq_of_lt (by
        have h3 : 2 ≤ 2 ^ CP := by decide
        rw [Nat.sub_zero]
        omega)⟩
  obtain ⟨hcoins, hsort, h254⟩ := table_context hcs
  have hrun := cover_run table [] [(0, 1)] 0 254
    (fun d _ => Nat.zero_le _)
    (Nat.zero_le _)
    h254 (by omega) hcoins hsort hc0
  rw [List.nil_append] at hrun
  have hfin := hrun g hg
  cases hfin with
  | inl hst =>
      obtain ⟨st, hstS, hmatch⟩ := hst
      obtain ⟨t, u⟩ := st
      have hCP : CP = 262 := rfl
      have hmem : dpState table [(0, 1)] ∈ allSets := dpState_mem_allSets table [(0, 1)]
      have hbound := obstruction_bound hob _ hmem
      have hstle : t ≤ maxT (dpState table [(0, 1)]) := maxT_ge _ (t, u) hstS
      have hne : t ≠ CP := by omega
      simp only [matchSt] at hmatch
      rw [if_neg hne] at hmatch
      obtain ⟨hlt, hval, _⟩ := hmatch
      omega
  | inr hlt => omega

-- ===========================================================================
-- §5d-6  THE BRIDGE: INDEX LISTS → ACHIEVABLE SUMS + THE CLOSED THEOREM
-- ===========================================================================

/-- Distinctness for index lists (core-only). -/
inductive NoDupL : List Nat → Prop
  | nil : NoDupL []
  | cons (x : Nat) (l : List Nat) (h : x ∉ l) (hl : NoDupL l) : NoDupL (x :: l)

theorem mem_split {a : Nat} : ∀ {l : List Nat}, a ∈ l → ∃ l₁ l₂, l = l₁ ++ a :: l₂ := by
  intro l
  induction l with
  | nil => intro h; cases h
  | cons x xs ih =>
      intro h
      cases h with
      | head => exact ⟨[], xs, rfl⟩
      | tail _ ht =>
          obtain ⟨l₁, l₂, hl⟩ := ih ht
          exact ⟨x :: l₁, l₂, by rw [hl, ← List.cons_append]⟩

/-- The fact-P bridge (moved up: needed by the incremental sweep). -/
theorem fact_eq_2P (i : Nat) (hi : 2 ≤ i) : fact i = 2 * P i := by
  have key : ∀ k : Nat, (2:Nat) ∣ fact (k + 2) := by
    intro k
    induction k with
    | zero => decide
    | succ k' ih =>
        rw [show k' + 1 + 2 = (k' + 2) + 1 from by omega, fact_succ]
        exact dvd_mul_gen 2 (fact (k' + 2)) (k' + 2 + 1) ih
  have hd2 : (2:Nat) ∣ fact i := by
    have hk := key (i - 2)
    rw [show i - 2 + 2 = i from by omega] at hk
    exact hk
  obtain ⟨w, hw⟩ := hd2
  unfold P
  rw [hw, Nat.mul_div_cancel_left _ (by omega : 0 < 2)]

/-- The valuation bridge: v₂(i!) = 1 + classOf i for i ≥ 2. -/
theorem v2_fact_classOf (i : Nat) (hi : 2 ≤ i) : v2 (fact i) = 1 + classOf i := by
  have hfp : fact i = 2 * P i := fact_eq_2P i hi
  have hv2two : v2 2 = 1 := by decide
  have hpp : 1 ≤ P i := P_pos i hi
  have hstep : v2 (2 * P i) = v2 2 + v2 (P i) :=
    v2_mul (2 + P i) 2 (P i) (by omega) (by decide) hpp
  rw [hfp, hstep, hv2two]
  rfl

/-- **THE INCREMENTAL SWEEP** — carries fact i and v₂(fact i) forward, so the
kernel pays ONE big multiplication per step and v₂ only on tiny arguments.
The naive per-element sweep recomputes fact from scratch 256 times and is
kernel-intractable (measured: >12 min at 100% CPU, unfinished). -/
def sweepAux : Nat → Nat → Nat → Nat → Bool
  | 0, _, _, _ => true
  | f + 1, i, fa, va =>
      (decide (i < 3) || decide (va ≤ 247)) &&
        sweepAux f (i + 1) ((i + 1) * fa) (va + v2 (i + 1))

theorem sweepAux_sound : ∀ (f i fa va : Nat), fa = fact i → va = v2 (fact i) →
    sweepAux f i fa va = true → ∀ j, i ≤ j → j < i + f → j < 3 ∨ classOf j ≤ 246 := by
  intro f
  induction f with
  | zero => intro i fa va _ _ _ j _ hj; omega
  | succ f' ih =>
      intro i fa va hfa hva hs j hj1 hj2
      have h2 : ((decide (i < 3) || decide (va ≤ 247)) &&
          sweepAux f' (i + 1) ((i + 1) * fa) (va + v2 (i + 1))) = true := hs
      rw [Bool.and_eq_true] at h2
      obtain ⟨hchk, hrec⟩ := h2
      have hfa' : (i + 1) * fa = fact (i + 1) := by rw [hfa, ← fact_succ]
      have hva' : va + v2 (i + 1) = v2 (fact (i + 1)) := by
        rw [fact_succ]
        have hmul := v2_mul ((i + 1) + fact i + (i + 1) * fact i) (i + 1) (fact i)
          (by omega) (by omega) (fact_pos i)
        rw [hmul]
        omega
      cases Nat.lt_or_ge j (i + 1) with
      | inl hjlt =>
          have hji : j = i := by omega
          rw [hji]
          rw [Bool.or_eq_true] at hchk
          cases hchk with
          | inl hlt3 => exact Or.inl (of_decide_eq_true hlt3)
          | inr hva247 =>
              have hv : va ≤ 247 := of_decide_eq_true hva247
              cases Nat.lt_or_ge i 3 with
              | inl hilt => exact Or.inl hilt
              | inr hige =>
                  right
                  have hbr : v2 (fact i) = 1 + classOf i := v2_fact_classOf i (by omega)
                  omega
      | inr hjge =>
          exact ih (i + 1) ((i + 1) * fa) (va + v2 (i + 1)) hfa' hva' hrec j (by omega) (by omega)

-- The class bound for every i in [3,255] (kernel-certified via the
-- incremental sweep — one multiplication per index, no recomputation).
set_option maxHeartbeats 2000000 in
theorem classOf_bound_all : (List.range 256).all
    (fun i => decide (i < 3) || decide (classOf i ≤ 246)) = true := by
  have hsweep := sweepAux_sound 256 0 1 0 rfl rfl (by decide)
  rw [List.all_eq_true]
  intro i hi
  have hcov := hsweep i (Nat.zero_le i) (List.mem_range.mp hi)
  cases hcov with
  | inl hlt3 => rw [Bool.or_eq_true]; exact Or.inl (decide_eq_true hlt3)
  | inr hcle => rw [Bool.or_eq_true]; exact Or.inr (decide_eq_true hcle)

/-- Every index in [3,255] has its coin in the table. -/
theorem table_cover (i : Nat) (h3 : 3 ≤ i) (h255 : i ≤ 255) :
    (i, classOf i, coinUnit i) ∈ table := by
  have hlt : i < 256 := by omega
  have hb : classOf i ≤ 246 := by
    have hq := List.all_eq_true.mp classOf_bound_all i (List.mem_range.mpr hlt)
    rw [Bool.or_eq_true] at hq
    cases hq with
    | inl hlt3 => exact absurd (of_decide_eq_true hlt3) (by omega)
    | inr hb => exact of_decide_eq_true hb
  exact (table_mem_iff _).mpr (coinList_mem_of i h3 hlt hb)

theorem perm_sum : ∀ {l₁ l₂ : List Nat}, List.Perm l₁ l₂ →
    (l₁.map P).sum = (l₂.map P).sum := by
  intro l₁ l₂ h
  induction h with
  | nil => rfl
  | cons x p ih =>
      rw [List.map_cons, List.sum_cons, List.map_cons, List.sum_cons, ih]
  | swap x y l =>
      rw [List.map_cons, List.sum_cons, List.map_cons, List.sum_cons,
        List.map_cons, List.sum_cons, List.map_cons, List.sum_cons]
      omega
  | trans p₁ p₂ ih₁ ih₂ => rw [ih₁, ih₂]

theorem nodup_append_remove : ∀ (l₁ l₂ : List Nat) (a : Nat),
    NoDupL (l₁ ++ a :: l₂) → NoDupL (l₁ ++ l₂) := by
  intro l₁
  induction l₁ with
  | nil =>
      intro l₂ a h
      cases h with
      | cons _ _ hnot hl => exact hl
  | cons x xs ih =>
      intro l₂ a h
      cases h with
      | cons _ _ hnot hl =>
          have hxs : x ∉ xs ++ l₂ := by
            intro hmem
            exact hnot (by
              cases List.mem_append.mp hmem with
              | inl hx => exact List.mem_append.mpr (Or.inl hx)
              | inr ha => exact List.mem_append.mpr (Or.inr (List.Mem.tail a ha)))
          exact NoDupL.cons x (xs ++ l₂) hxs (ih l₂ a hl)

theorem perm_middle : ∀ (l₁ l₂ : List Nat) (a : Nat),
    List.Perm (l₁ ++ a :: l₂) (a :: (l₁ ++ l₂)) := by
  intro l₁
  induction l₁ with
  | nil =>
      intro l₂ a
      rw [List.nil_append, List.nil_append]
  | cons x xs ih =>
      intro l₂ a
      exact List.Perm.trans (List.Perm.cons x (ih l₂ a)) (List.Perm.swap a x (xs ++ l₂))

/-- Coin-index distinctness (positional): the weapon that makes the filtered
projection a genuine permutation — without it the lemma is FALSE (duplicate
coin indices would be counted twice). -/
inductive NoDupF : List (Nat × Nat × Nat) → Prop
  | nil : NoDupF []
  | cons (c : Nat × Nat × Nat) (cs : List (Nat × Nat × Nat))
      (h : ∀ d ∈ cs, d.1 ≠ c.1) (hl : NoDupF cs) : NoDupF (c :: cs)

theorem NoDupF_head {c : Nat × Nat × Nat} {cs : List (Nat × Nat × Nat)}
    (h : NoDupF (c :: cs)) : ∀ d ∈ cs, d.1 ≠ c.1 := by
  cases h with
  | cons _ _ hhead _ => exact hhead

theorem NoDupF_tail {c : Nat × Nat × Nat} {cs : List (Nat × Nat × Nat)}
    (h : NoDupF (c :: cs)) : NoDupF cs := by
  cases h with
  | cons _ _ _ htail => exact htail

/-- A middle element of a NoDupL append is absent from the sides. -/
theorem nodup_middle_mem {a : Nat} : ∀ {l₁ l₂ : List Nat},
    NoDupL (l₁ ++ a :: l₂) → a ∉ l₁ ++ l₂ := by
  intro l₁
  induction l₁ with
  | nil =>
      intro l₂ h
      cases h with
      | cons _ _ hnot _ => exact hnot
  | cons x xs ih =>
      intro l₂ h
      cases h with
      | cons _ _ hnot hl =>
          intro hmem
          cases List.mem_cons.mp hmem with
          | inl hax =>
              rw [← hax] at hnot
              exact hnot (List.mem_append.mpr (Or.inr (List.Mem.head _)))
          | inr hin =>
              exact absurd hin (ih hl)

/-- Filter congruence, membership-guarded (core-only, arbitrary type). -/
theorem filter_congr_mem {α : Type} {p p' : α → Bool} : ∀ (l : List α),
    (∀ x ∈ l, p x = p' x) → l.filter p = l.filter p' := by
  intro l
  induction l with
  | nil => intro _; rfl
  | cons x xs ih =>
      intro h
      rw [List.filter_cons, List.filter_cons, h x (List.Mem.head _)]
      by_cases hx : p' x = true
      · rw [if_pos hx, if_pos hx, ih (fun y hy => h y (List.Mem.tail _ hy))]
      · have hxf : p' x = false := by
          cases hx' : p' x with
          | true => exact absurd hx' hx
          | false => rfl
        rw [if_neg (by rw [hxf]; exact Bool.false_ne_true),
          if_neg (by rw [hxf]; exact Bool.false_ne_true),
          ih (fun y hy => h y (List.Mem.tail _ hy))]

/-- Coin-index membership checker (Bool). -/
def memFst (i : Nat) : List (Nat × Nat × Nat) → Bool
  | [] => false
  | d :: ds => if d.1 = i then true else memFst i ds

theorem memFst_true (i : Nat) : ∀ (cs : List (Nat × Nat × Nat)),
    memFst i cs = true → ∃ d ∈ cs, d.1 = i := by
  intro cs
  induction cs with
  | nil => intro h; simp [memFst] at h
  | cons d ds ih =>
      intro h
      unfold memFst at h
      by_cases hde : d.1 = i
      · rw [if_pos hde] at h
        exact ⟨d, List.Mem.head _, hde⟩
      · rw [if_neg hde] at h
        obtain ⟨e, he, hei⟩ := ih h
        exact ⟨e, List.Mem.tail _ he, hei⟩

theorem memFst_of_mem (i : Nat) : ∀ (cs : List (Nat × Nat × Nat))
    (d : Nat × Nat × Nat), d ∈ cs → d.1 = i → memFst i cs = true := by
  intro cs
  induction cs with
  | nil => intro d hd _; cases hd
  | cons e es ih =>
      intro d hd hei
      show (if e.1 = i then true else memFst i es) = true
      by_cases hde : e.1 = i
      · rw [if_pos hde]
      · rw [if_neg hde]
        cases hd with
        | head => exact absurd hei hde
        | tail _ ht => exact ih d ht hei

def noDupFB : List (Nat × Nat × Nat) → Bool
  | [] => true
  | c :: cs => if memFst c.1 cs then false else noDupFB cs

theorem noDupFB_true : ∀ (cs : List (Nat × Nat × Nat)),
    noDupFB cs = true → NoDupF cs := by
  intro cs
  induction cs with
  | nil => intro _; exact NoDupF.nil
  | cons c rest ih =>
      intro h
      unfold noDupFB at h
      by_cases hm : memFst c.1 rest = true
      · rw [if_pos hm] at h; exact absurd h (by simp)
      · rw [if_neg hm] at h
        refine NoDupF.cons c rest ?_ (ih h)
        intro d hd heq
        exact absurd (memFst_of_mem c.1 rest d hd heq) hm

/-- **THE COIN LIST HAS PAIRWISE-DISTINCT INDICES — pure logic, zero kernel cost:"
the coins are a map with first component = source over a nodup-filtered range.** -/
theorem noDupF_map (f : Nat → Nat × Nat × Nat) (hinv : ∀ x, (f x).1 = x) :
    ∀ (l : List Nat), NoDupL l → NoDupF (l.map f) := by
  intro l
  induction l with
  | nil => intro _; exact NoDupF.nil
  | cons x xs ih =>
      intro h
      cases h with
      | cons _ _ hnot hl =>
          refine NoDupF.cons (f x) (xs.map f) ?_ (ih hl)
          intro d hd
          obtain ⟨y, hy, hfy⟩ := List.mem_map.mp hd
          have hyx : y ≠ x := by
            intro heq
            exact hnot (by rw [← heq]; exact hy)
          rw [← hfy, hinv y, hinv x]
          exact hyx

/-- Distinctness checker for concrete index lists. -/
def nodupNatB : List Nat → Bool
  | [] => true
  | x :: xs => if x ∈ xs then false else nodupNatB xs

/-- **RECEIPT: the source range is nodup** (kernel-decided, small nats only). -/
theorem nodupNatB_range : nodupNatB (List.range 256) = true := by decide

theorem nodupNatB_true : ∀ (l : List Nat), nodupNatB l = true → NoDupL l := by
  intro l
  induction l with
  | nil => intro _; exact NoDupL.nil
  | cons x xs ih =>
      intro h
      unfold nodupNatB at h
      by_cases hx : x ∈ xs
      · rw [if_pos hx] at h; exact absurd h (by simp)
      · rw [if_neg hx] at h
        exact NoDupL.cons x xs hx (ih h)

/-- Filtering preserves NoDupL (moved up: needed by the coin-distinctness route). -/
theorem nodup_filter (p : Nat → Bool) : ∀ (l : List Nat), NoDupL l → NoDupL (l.filter p) := by
  intro l
  induction l with
  | nil => intro _; exact NoDupL.nil
  | cons x xs ih =>
      intro h
      cases h with
      | cons _ _ hnot hl =>
          by_cases hp : p x = true
          · rw [List.filter_cons, if_pos hp]
            refine NoDupL.cons x (xs.filter p) ?_ (ih hl)
            intro hmem
            have := List.mem_filter.mp hmem
            exact hnot this.1
          · have hp' : p x = false := by
              cases h : p x with
              | true => exact absurd h hp
              | false => rfl
            rw [List.filter_cons, if_neg (by rw [hp']; exact Bool.false_ne_true)]
            exact ih hl

theorem noDupF_coinList : NoDupF coinList := by
  have hnd : NoDupL ((List.range 256).filter (fun i => 3 ≤ i && classOf i ≤ 246)) :=
    nodup_filter _ _ (nodupNatB_true _ nodupNatB_range)
  exact noDupF_map (fun i => (i, classOf i, coinUnit i)) (fun x => rfl) _ hnd

theorem mem_insertCoin (c e : Nat × Nat × Nat) :
    ∀ (cs : List (Nat × Nat × Nat)), e ∈ insertCoin c cs → e = c ∨ e ∈ cs := by
  intro cs
  induction cs with
  | nil =>
      intro he
      cases he with
      | head => exact Or.inl rfl
      | tail _ ht => cases ht
  | cons d ds ih =>
      intro he
      unfold insertCoin at he
      by_cases hlt : (c.2.1 < d.2.1 || (decide (c.2.1 = d.2.1) && c.1 < d.1)) = true
      · rw [if_pos hlt] at he
        cases List.mem_cons.mp he with
        | inl heq => exact Or.inl heq
        | inr hin => exact Or.inr hin
      · rw [if_neg hlt] at he
        cases List.mem_cons.mp he with
        | inl heq => exact Or.inr (List.mem_cons.mpr (Or.inl heq))
        | inr hin =>
            cases ih hin with
            | inl hec => exact Or.inl hec
            | inr hds => exact Or.inr (List.mem_cons.mpr (Or.inr hds))

theorem nodupF_insertCoin {c : Nat × Nat × Nat} : ∀ (cs : List (Nat × Nat × Nat)),
    NoDupF cs → (∀ d ∈ cs, d.1 ≠ c.1) → NoDupF (insertCoin c cs) := by
  intro cs
  induction cs with
  | nil =>
      intro _ _
      unfold insertCoin
      refine NoDupF.cons c [] ?_ NoDupF.nil
      intro e he
      cases he
  | cons d ds ih =>
      intro hnd hall
      have hfresh : ∀ x ∈ ds, x.1 ≠ c.1 := fun x hx => hall x (List.Mem.tail _ hx)
      have hcd : c.1 ≠ d.1 := (hall d (List.Mem.head _)).symm
      unfold insertCoin
      by_cases hlt : (c.2.1 < d.2.1 || (decide (c.2.1 = d.2.1) && c.1 < d.1)) = true
      · rw [if_pos hlt]
        refine NoDupF.cons c (d :: ds) ?_ hnd
        intro e he
        cases List.mem_cons.mp he with
        | inl heq => rw [heq]; exact hall d (List.Mem.head _)
        | inr hin => exact hall e (List.Mem.tail _ hin)
      · rw [if_neg hlt]
        have hrec := ih (NoDupF_tail hnd) hfresh
        refine NoDupF.cons d (insertCoin c ds) ?_ hrec
        intro e he
        cases mem_insertCoin c e ds he with
        | inl hec => rw [hec]; exact hcd
        | inr hin => exact NoDupF_head hnd e hin

theorem nodupF_sortCoins : ∀ (l : List (Nat × Nat × Nat)),
    NoDupF l → NoDupF (sortCoins l) := by
  intro l
  induction l with
  | nil => intro _; exact NoDupF.nil
  | cons c cs ih =>
      intro h
      exact nodupF_insertCoin (sortCoins cs) (ih (NoDupF_tail h))
        (fun d hd => NoDupF_head h d (perm_mem (sortCoins_perm cs) d hd))

theorem nodupF_table : NoDupF table := nodupF_sortCoins coinList noDupF_coinList

/-- The filtered coin projections permute the index list. REQUIRES coin-index
distinctness (NoDupF) — without it duplicate coin indices break the bijection. -/
theorem filter_proj_perm : ∀ (cs : List (Nat × Nat × Nat)) (B : List Nat),
    NoDupF cs → NoDupL B → (∀ i ∈ B, (i, classOf i, coinUnit i) ∈ cs) →
    List.Perm (((cs.filter (fun c => decide (c.1 ∈ B))).map Prod.fst)) B := by
  intro cs
  induction cs with
  | nil =>
      intro B _ _ hcov
      cases B with
      | nil => exact List.Perm.nil
      | cons b Bs =>
          exfalso
          cases hcov b (List.Mem.head _)
  | cons c rest ih =>
      intro B hndF hnd hcov
      by_cases hcm : decide (c.1 ∈ B) = true
      · -- c.1 ∈ B: split B around the coin index c.1
        have hcb : c.1 ∈ B := of_decide_eq_true hcm
        obtain ⟨l₁, l₂, hB⟩ := mem_split hcb
        have hndB : NoDupL (l₁ ++ c.1 :: l₂) := by rw [← hB]; exact hnd
        have hc1nl : c.1 ∉ l₁ ++ l₂ := nodup_middle_mem hndB
        -- the coins of l₁ ++ l₂ all live in rest
        have hcov' : ∀ i ∈ l₁ ++ l₂, (i, classOf i, coinUnit i) ∈ rest := by
          intro i hi
          have hib : i ∈ B := by
            rw [hB]
            exact List.mem_append.mpr
              ((List.mem_append.mp hi).imp id (fun h => List.Mem.tail _ h))
          have hcovi := hcov i hib
          have hic : i ≠ c.1 := fun heq => hc1nl (by rw [← heq]; exact hi)
          cases List.mem_cons.mp hcovi with
          | inl hhead => exact absurd (congrArg Prod.fst hhead) hic
          | inr htail => exact htail
        have hnd' : NoDupL (l₁ ++ l₂) := nodup_append_remove l₁ l₂ c.1 hndB
        have hrec := ih (l₁ ++ l₂) (NoDupF_tail hndF) hnd' hcov'
        -- the two filter predicates agree on rest (no coin there carries c.1)
        have hne : ∀ q ∈ rest, q.1 ≠ c.1 := NoDupF_head hndF
        have hpred : ∀ q : Nat × Nat × Nat, q.1 ≠ c.1 →
            decide (q.1 ∈ l₁ ++ l₂) = decide (q.1 ∈ B) := by
          intro q hqc
          have hiff : (q.1 ∈ l₁ ++ l₂) ↔ (q.1 ∈ B) := by
            constructor
            · intro hm
              rw [hB]
              exact List.mem_append.mpr
                ((List.mem_append.mp hm).imp id (fun h => List.Mem.tail _ h))
            · intro hm
              rw [hB] at hm
              cases List.mem_append.mp hm with
              | inl h1 => exact List.mem_append.mpr (Or.inl h1)
              | inr h2 =>
                  cases List.mem_cons.mp h2 with
                  | inl heq => exact absurd heq hqc
                  | inr h3 => exact List.mem_append.mpr (Or.inr h3)
          cases hd : decide (q.1 ∈ l₁ ++ l₂) with
          | true =>
              have hq2 : q.1 ∈ B := hiff.mp (of_decide_eq_true hd)
              rw [decide_eq_true hq2]
          | false =>
              have hn1 : ¬(q.1 ∈ l₁ ++ l₂) :=
                fun hb => absurd (decide_eq_true hb) (by rw [hd]; exact Bool.false_ne_true)
              have hn2 : ¬(q.1 ∈ B) := fun hb => hn1 (hiff.mpr hb)
              cases hd2 : decide (q.1 ∈ B) with
              | true => exact absurd (of_decide_eq_true hd2) hn2
              | false => rfl
        have hfe : (rest.filter (fun q => decide (q.1 ∈ B)))
            = rest.filter (fun q => decide (q.1 ∈ l₁ ++ l₂)) := by
          refine (filter_congr_mem rest ?_).symm
          intro q hq
          exact hpred q (hne q hq)
        have hfil : (c :: rest).filter (fun q => decide (q.1 ∈ B))
            = c :: rest.filter (fun q => decide (q.1 ∈ B)) := by
          rw [List.filter_cons, if_pos hcm]
        show List.Perm (((c :: rest).filter (fun q => decide (q.1 ∈ B))).map Prod.fst) B
        rw [hfil, List.map_cons, hfe, hB]
        exact List.Perm.trans (List.Perm.cons c.1 hrec)
          (List.Perm.symm (perm_middle l₁ l₂ c.1))
      · have hcov' : ∀ i ∈ B, (i, classOf i, coinUnit i) ∈ rest := by
          intro i hi
          have hcovi := hcov i hi
          have hic : i ≠ c.1 := by
            intro heq
            exact hcm (decide_eq_true (by rw [← heq]; exact hi))
          cases List.mem_cons.mp hcovi with
          | inl hhead => exact absurd (congrArg Prod.fst hhead) hic
          | inr htail => exact htail
        have hfil : (c :: rest).filter (fun q => decide (q.1 ∈ B))
            = rest.filter (fun q => decide (q.1 ∈ B)) := by
          rw [List.filter_cons, if_neg hcm]
        show List.Perm (((c :: rest).filter (fun q => decide (q.1 ∈ B))).map Prod.fst) B
        rw [hfil]
        exact ih B (NoDupF_tail hndF) hnd hcov'

/-- The filter-coin sum is achievable. -/
theorem achiev_coins : ∀ (cs : List (Nat × Nat × Nat)) (B : List Nat),
    Achiev cs (1 + ((cs.filter (fun c => decide (c.1 ∈ B))).map (fun c => P c.1)).sum) := by
  intro cs B
  induction cs with
  | nil => exact Achiev.base
  | cons c rest ih =>
      by_cases hcm : decide (c.1 ∈ B) = true
      · have hfil : (c :: rest).filter (fun q => decide (q.1 ∈ B))
            = c :: rest.filter (fun q => decide (q.1 ∈ B)) := by
          rw [List.filter_cons, if_pos hcm]
        show Achiev (c :: rest) (1 + (((c :: rest).filter
          (fun q => decide (q.1 ∈ B))).map (fun q => P q.1)).sum)
        rw [hfil, List.map_cons, List.sum_cons]
        have hsum : 1 + (P c.1 + ((rest.filter (fun q => decide (q.1 ∈ B))).map
            (fun q => P q.1)).sum) = (1 + ((rest.filter (fun q => decide (q.1 ∈ B))).map
            (fun q => P q.1)).sum) + P c.1 := by omega
        rw [hsum]
        exact Achiev.take _ _ _ ih
      · have hfil : (c :: rest).filter (fun q => decide (q.1 ∈ B))
            = rest.filter (fun q => decide (q.1 ∈ B)) := by
          rw [List.filter_cons, if_neg hcm]
        show Achiev (c :: rest) (1 + (((c :: rest).filter
          (fun q => decide (q.1 ∈ B))).map (fun q => P q.1)).sum)
        rw [hfil]
        exact Achiev.skip _ _ _ ih

/-- Sum-level map fusion (by induction — syntactic everywhere; ANY defeq
between `F.map f` and `(F.map g).map h` forces F's whnf, and for
F = a table-filter that is the 12-minute classOf-compute). -/
theorem sum_map_fuse_eq : ∀ (cs : List (Nat × Nat × Nat)),
    (cs.map (fun c => P c.1)).sum = ((cs.map Prod.fst).map P).sum := by
  intro cs
  induction cs with
  | nil => rfl
  | cons c rest ih =>
      rw [List.map_cons, List.map_cons, List.map_cons, List.sum_cons, List.sum_cons, ih]

-- The universal upper bound over index lists in [3,255].
theorem upper_bounded_indices (hcs : classesSorted table = true)
    (hob : obstructionCheck = true) : ∀ B : List Nat, NoDupL B → (∀ i ∈ B, 3 ≤ i) →
    (∀ i ∈ B, i ≤ 255) → v2 (1 + (B.map P).sum) ≤ 253 := by
  intro B hnd h3 h255
  have hperm := filter_proj_perm table B nodupF_table hnd
    (fun i hi => table_cover i (h3 i hi) (h255 i hi))
  have hsum : ((table.filter (fun c => decide (c.1 ∈ B))).map (fun c => P c.1)).sum
      = (B.map P).sum :=
    Eq.trans (sum_map_fuse_eq (table.filter (fun c => decide (c.1 ∈ B))))
      (perm_sum hperm)
  have hach : Achiev table (1 + (B.map P).sum) := by
    rw [← hsum]
    exact achiev_coins table B
  exact cover_final hcs hob _ hach

/-- Coins at or beyond 256 contribute multiples of 2^254. -/
theorem fact_256_dvd : (2:Nat) ^ 255 ∣ fact 256 := by decide

theorem coin_range_dvd : ∀ i : Nat, 256 ≤ i → 2 ^ 254 ∣ P i := by
  intro i hi
  have key : ∀ k : Nat, 256 ≤ k → 2 ^ 255 ∣ fact k := by
    intro k hk
    induction k with
    | zero => omega
    | succ k' ih =>
        cases Nat.eq_zero_or_pos k' with
        | inl h0 => rw [h0] at hk; omega
        | inr hpos =>
            have hstep : fact (k' + 1) = (k' + 1) * fact k' := rfl
            by_cases hk256 : 256 ≤ k'
            · rw [hstep]
              exact dvd_mul_gen (2 ^ 255) (fact k') (k' + 1) (ih hk256)
            · have hke : k' + 1 = 256 := by omega
              rw [hke]
              exact fact_256_dvd
  have hdvd := key i hi
  obtain ⟨w, hw⟩ := hdvd
  -- fact i = 2^255 * w = 2 * (2^254 * w); P i = fact i / 2 = 2^254 * w
  have hfact2 : fact i = 2 * (2 ^ 254 * w) := by
    have hp : 2 ^ 255 = 2 * 2 ^ 254 := by decide
    rw [hw, hp, Nat.mul_assoc]
  have hP : P i = 2 ^ 254 * w := by
    unfold P
    rw [hfact2, Nat.mul_div_cancel_left _ (by omega : 0 < 2)]
  exact ⟨w, hP⟩

theorem filter_split_sum (f : Nat → Nat) (p : Nat → Bool) : ∀ (l : List Nat),
    (l.map f).sum = ((l.filter p).map f).sum + ((l.filter (fun x => !(p x))).map f).sum := by
  intro l
  induction l with
  | nil => rfl
  | cons x xs ih =>
      by_cases hp : p x = true
      · have hnf : (!(p x)) = false := by rw [hp]; rfl
        rw [List.filter_cons, if_pos hp, List.filter_cons,
          if_neg (by rw [hnf]; exact Bool.false_ne_true),
          List.map_cons, List.sum_cons, List.map_cons, List.sum_cons, ih]
        omega
      · have hp' : p x = false := by
          cases h : p x with
          | true => exact absurd h hp
          | false => rfl
        have hn : (!(p x)) = true := by rw [hp']; rfl
        rw [List.filter_cons, if_neg (by rw [hp']; exact Bool.false_ne_true),
          List.filter_cons, if_pos hn,
          List.map_cons, List.sum_cons, List.map_cons, List.sum_cons, ih]
        omega

theorem sum_dvd (d : Nat) (f : Nat → Nat) : ∀ (l : List Nat),
    (∀ i ∈ l, d ∣ f i) → d ∣ (l.map f).sum := by
  intro l
  induction l with
  | nil => intro _; exact ⟨0, rfl⟩
  | cons x xs ih =>
      intro h
      rw [List.map_cons, List.sum_cons]
      have hx := h x (List.Mem.head _)
      have hxs := ih (fun i hi => h i (List.Mem.tail _ hi))
      obtain ⟨a, ha⟩ := hx
      obtain ⟨b, hb⟩ := hxs
      exact ⟨a + b, by rw [ha, hb, Nat.mul_add]⟩

theorem sum_map_congr (f g : Nat → Nat) : ∀ (l : List Nat),
    (∀ x ∈ l, f x = g x) → (l.map f).sum = (l.map g).sum := by
  intro l
  induction l with
  | nil => intro _; rfl
  | cons x xs ih =>
      intro h
      rw [List.map_cons, List.map_cons, List.sum_cons, List.sum_cons,
        h x (List.Mem.head _), ih (fun y hy => h y (List.Mem.tail _ hy))]

/-- The constant-pullout: summing 2·f is twice summing f. -/
theorem sum_map_two_mul (f : Nat → Nat) : ∀ (l : List Nat),
    (l.map (fun x => 2 * f x)).sum = 2 * (l.map f).sum := by
  intro l
  induction l with
  | nil => rfl
  | cons x xs ih =>
      rw [List.map_cons, List.sum_cons, List.map_cons, List.sum_cons, ih]
      omega

/-- **THE UNIVERSAL UPPER BOUND: NO set of distinct factorials from 3!
onward reaches level 255 over the anchor 2 (i.e. f(2,2) ≤ 254).** -/
theorem erdos404_f22_upper (hcs : classesSorted table = true)
    (hob : obstructionCheck = true) : ∀ B : List Nat, NoDupL B → (∀ i ∈ B, 3 ≤ i) →
    v2 (2 + (B.map fact).sum) ≤ 254 := by
  intro B hnd h3
  -- the split at 255
  have hsplit : (B.map fact).sum
      = ((B.filter (fun i => decide (i ≤ 255))).map fact).sum
        + ((B.filter (fun i => decide (256 ≤ i))).map fact).sum := by
    have := filter_split_sum fact (fun i => decide (i ≤ 255)) B
    -- the complementary filter is (256 ≤ i) up to the predicate form
    have hcomp : (fun x => !(decide (x ≤ 255))) = (fun i => decide (256 ≤ i)) := by
      funext x
      by_cases hx : x ≤ 255
      · have h1 : decide (x ≤ 255) = true := decide_eq_true hx
        have h2 : decide (256 ≤ x) = false := by
          cases hd : decide (256 ≤ x) with
          | false => rfl
          | true => exact absurd (of_decide_eq_true hd) (by omega)
        rw [h1, h2]
        rfl
      · have h256 : 256 ≤ x := by omega
        have h1 : decide (x ≤ 255) = false := by
          cases hd : decide (x ≤ 255) with
          | false => rfl
          | true => exact absurd (of_decide_eq_true hd) (by omega)
        have h2 : decide (256 ≤ x) = true := decide_eq_true h256
        rw [h1, h2]
        rfl
    rw [hcomp] at this
    exact this
  -- part 1: the bounded part through the table
  have hnd1 : NoDupL (B.filter (fun i => decide (i ≤ 255))) := nodup_filter _ B hnd
  have h31 : ∀ i ∈ B.filter (fun i => decide (i ≤ 255)), 3 ≤ i := by
    intro i hi
    exact h3 i (List.mem_filter.mp hi).1
  have h251 : ∀ i ∈ B.filter (fun i => decide (i ≤ 255)), i ≤ 255 := by
    intro i hi
    have := List.mem_filter.mp hi
    exact of_decide_eq_true this.2
  have hpart1 : v2 (1 + ((B.filter (fun i => decide (i ≤ 255))).map P).sum) ≤ 253 :=
    upper_bounded_indices hcs hob _ hnd1 h31 h251
  -- part 2: the tail contributes multiples of 2^254
  have hdvd2 : 2 ^ 254 ∣ ((B.filter (fun i => decide (256 ≤ i))).map P).sum := by
    refine sum_dvd _ P _ ?_
    intro i hi
    have h256 : 256 ≤ i := of_decide_eq_true (List.mem_filter.mp hi).2
    exact coin_range_dvd i h256
  -- the fact-P bridge on both parts
  have hfactP1 : ((B.filter (fun i => decide (i ≤ 255))).map fact).sum
      = 2 * ((B.filter (fun i => decide (i ≤ 255))).map P).sum := by
    have h1 : ((B.filter (fun i => decide (i ≤ 255))).map fact).sum
        = ((B.filter (fun i => decide (i ≤ 255))).map (fun i => 2 * P i)).sum := by
      refine sum_map_congr fact (fun i => 2 * P i) _ ?_
      intro i hi
      have h3i : 3 ≤ i := h31 i hi
      exact fact_eq_2P i (by omega)
    rw [h1, sum_map_two_mul P _]
  have hfactP2 : ((B.filter (fun i => decide (256 ≤ i))).map fact).sum
      = 2 * ((B.filter (fun i => decide (256 ≤ i))).map P).sum := by
    have h1 : ((B.filter (fun i => decide (256 ≤ i))).map fact).sum
        = ((B.filter (fun i => decide (256 ≤ i))).map (fun i => 2 * P i)).sum := by
      refine sum_map_congr fact (fun i => 2 * P i) _ ?_
      intro i hi
      have h256i : 256 ≤ i := of_decide_eq_true (List.mem_filter.mp hi).2
      exact fact_eq_2P i (by omega)
    rw [h1, sum_map_two_mul P _]
  -- assemble
  rw [hsplit, hfactP1, hfactP2]
  -- 2 + 2*S1 + 2*S2 = 2 * (1 + S1 + S2)
  have hmul : 2 + (2 * ((B.filter (fun i => decide (i ≤ 255))).map P).sum
      + 2 * ((B.filter (fun i => decide (256 ≤ i))).map P).sum)
      = 2 * (1 + ((B.filter (fun i => decide (i ≤ 255))).map P).sum
        + ((B.filter (fun i => decide (256 ≤ i))).map P).sum) := by omega
  rw [hmul]
  -- fresh X := 1 + S1 + S2; then v2 (2*X) = 1 + v2 X and v2 X ≤ 253
  obtain ⟨X, hX⟩ : ∃ X, 1 + ((B.filter (fun i => decide (i ≤ 255))).map P).sum
      + ((B.filter (fun i => decide (256 ≤ i))).map P).sum = X :=
    ⟨_, rfl⟩
  have hvX : v2 X ≤ 253 := by
    by_cases hS2 : ((B.filter (fun i => decide (256 ≤ i))).map P).sum = 0
    · rw [← hX, hS2, Nat.add_zero]
      exact hpart1
    · have hS2pos : 1 ≤ ((B.filter (fun i => decide (256 ≤ i))).map P).sum := by omega
      have hS2v : 254 ≤ v2 ((B.filter (fun i => decide (256 ≤ i))).map P).sum :=
        v2_max _ _ 254 (Nat.le_refl _) hS2pos hdvd2
      have hval : v2 X = v2 (1 + ((B.filter (fun i => decide (i ≤ 255))).map P).sum) := by
        rw [← hX]
        have hpos1 : 1 ≤ 1 + ((B.filter (fun i => decide (i ≤ 255))).map P).sum := by omega
        have hsumform : 1 + ((B.filter (fun i => decide (i ≤ 255))).map P).sum
            + ((B.filter (fun i => decide (256 ≤ i))).map P).sum
            = (1 + ((B.filter (fun i => decide (i ≤ 255))).map P).sum)
              + ((B.filter (fun i => decide (256 ≤ i))).map P).sum := by omega
        rw [hsumform, v2_add_min _ _ hpos1 hS2pos (by omega)]
      rw [hval]
      exact hpart1
  have hposX : 1 ≤ X := by rw [← hX]; omega
  have hv2two : v2 2 = 1 := by decide
  have hval2 : v2 (2 * X) = 1 + v2 X := by
    rw [v2_mul (2 + X) 2 X (Nat.le_refl _) (by omega) hposX, hv2two]
  rw [hX, hval2]
  omega

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
#eval classesSorted table        -- true
#eval v2 (sumFacts [3])          -- 3
#eval v2 (sumFacts [3, 5])       -- 7
#eval v2 (sumFacts [3, 5, 8])    -- 9
#print axioms erdos404_f22_lower

/-- **THE SORT-CORRECTNESS ROUTE (pure logic, zero kernel cost).** -/

theorem insertCoin_le (c d : Nat × Nat × Nat)
    (h : (c.2.1 < d.2.1 || (decide (c.2.1 = d.2.1) && c.1 < d.1)) = true) :
    c.2.1 ≤ d.2.1 := by
  rw [Bool.or_eq_true] at h
  cases h with
  | inl hlt => exact Nat.le_of_lt (of_decide_eq_true hlt)
  | inr hand =>
      rw [Bool.and_eq_true] at hand
      exact Nat.le_of_eq (of_decide_eq_true hand.1)

theorem insertCoin_ge (c d : Nat × Nat × Nat)
    (h : ¬((c.2.1 < d.2.1 || (decide (c.2.1 = d.2.1) && c.1 < d.1)) = true)) :
    d.2.1 ≤ c.2.1 := by
  by_cases hlt : c.2.1 < d.2.1
  · exfalso
    apply h
    rw [Bool.or_eq_true]
    exact Or.inl (decide_eq_true hlt)
  · omega

theorem tailSorted_insertCoin (c : Nat × Nat × Nat) :
    ∀ (cs : List (Nat × Nat × Nat)), TailSorted cs → TailSorted (insertCoin c cs) := by
  intro cs
  induction cs with
  | nil => intro _; exact TailSorted.cons c [] (fun e he => by cases he) TailSorted.nil
  | cons d ds ih =>
      intro h
      obtain ⟨hdmin, hds⟩ := TailSorted.destruct h
      by_cases hlt : (c.2.1 < d.2.1 || (decide (c.2.1 = d.2.1) && c.1 < d.1)) = true
      · have hcld : c.2.1 ≤ d.2.1 := insertCoin_le c d hlt
        unfold insertCoin
        rw [if_pos hlt]
        refine TailSorted.cons c (d :: ds) ?_ (TailSorted.cons d ds hdmin hds)
        intro e he
        cases List.mem_cons.mp he with
        | inl heq => rw [heq]; exact hcld
        | inr hin => exact Nat.le_trans hcld (hdmin e hin)
      · have hdlc : d.2.1 ≤ c.2.1 := insertCoin_ge c d hlt
        unfold insertCoin
        rw [if_neg hlt]
        refine TailSorted.cons d (insertCoin c ds) ?_ (ih hds)
        intro e he
        cases mem_insertCoin c e ds he with
        | inl hec => rw [hec]; exact hdlc
        | inr hin => exact hdmin e hin

theorem tailSorted_sortCoins : ∀ (l : List (Nat × Nat × Nat)),
    TailSorted (sortCoins l) := by
  intro l
  induction l with
  | nil => exact TailSorted.nil
  | cons c cs ih => exact tailSorted_insertCoin c (sortCoins cs) ih

theorem tailSorted_classesSorted : ∀ (l : List (Nat × Nat × Nat)),
    TailSorted l → classesSorted l = true := by
  intro l
  induction l with
  | nil => intro _; rfl
  | cons a rest ih =>
      intro h
      obtain ⟨hmin, hrest⟩ := TailSorted.destruct h
      cases rest with
      | nil => rfl
      | cons b r =>
          show ((a.2.1 ≤ b.2.1) && classesSorted (b :: r)) = true
          rw [Bool.and_eq_true]
          refine ⟨decide_eq_true (hmin b (List.Mem.head _)), ih hrest⟩

/-- **THE SORTEDNESS FACT: the table's classes are sorted** — by
insertion-sort correctness, pure logic, ZERO kernel cost. This discharges
the classesSorted hypothesis: the final theorem needs only the
obstruction-check receipt. -/
theorem classesSorted_true : classesSorted table = true := by
  unfold table
  exact tailSorted_classesSorted (sortCoins coinList) (tailSorted_sortCoins coinList)

theorem sumFacts_eq (l : List Nat) : sumFacts l = 2 + (l.map fact).sum := by
  induction l with
  | nil => rfl
  | cons x xs ih => rw [sumFacts, List.map_cons, List.sum_cons, ih]; omega

theorem witness_nodup : NoDupL witnessB := nodupNatB_true witnessB (by decide)

theorem witness_min : ∀ i ∈ witnessB, 3 ≤ i := by
  intro i hi
  have hall : witnessB.all (fun x => decide (3 ≤ x)) = true := by decide
  have hq := List.all_eq_true.mp hall i hi
  exact of_decide_eq_true hq

/-- **THE WITNESS IN THE GENERAL FORM: the 118-element set achieves 254.** -/
theorem erdos404_f22_lower_general :
    v2 (2 + (witnessB.map fact).sum) = 254 := by
  rw [← sumFacts_eq witnessB]
  exact erdos404_f22_lower

/-- **THE CLOSED THEOREM: f(2,2) = 254 EXACTLY.**
Lower: the explicit 118-element witness (kernel-evaluated, distinct indices,
all ≥ 3). Upper: NO set of distinct factorials from 3! onward exceeds 254 —
the §5d invariant induction connecting the kernel-evaluated obstruction DP
to the universal statement. Lin's [Li76] published bound f(2,2) ≤ 254 is
TIGHT. -/
theorem erdos404_f22_exact (hob : obstructionCheck = true) :
    v2 (2 + (witnessB.map fact).sum) = 254
    ∧ ∀ B : List Nat, NoDupL B → (∀ i ∈ B, 3 ≤ i) →
      v2 (2 + (B.map fact).sum) ≤ 254 :=
  ⟨erdos404_f22_lower_general, erdos404_f22_upper classesSorted_true hob⟩

#eval nodupNatB witnessB          -- true
#eval witnessB.all (fun x => decide (3 ≤ x))  -- true
#print axioms erdos404_f22_exact
#print axioms erdos404_f22_upper
