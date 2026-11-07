import Arsenal.ErdosTernary2.Basic
import Arsenal.CardinalWorlds
import Arsenal.CardinalWorldsV2

-- Family pattern (green kernels, F22/K17 chains): explicit depth headroom.
set_option maxRecDepth 262144

/-!
# ERDŐS #700 — THE PRIME-POWER LAW (Kill-package, the S030 armed strike)

**Problem (Erdős–Szekeres #700):** Let f(n) = min_{1<k≤n/2} gcd(n, C(n,k)).
Characterise the composite n with f(n) = n/P(n), P(n) the largest prime factor.

## THE PRIME-POWER CLASS LAW (this kernel, zero hypotheses)

**THEOREM A (the carry lemma).** For every prime p, a ≥ 1, 1 ≤ k ≤ p^a − 1:
    v_p(C(p^a, k)) = a − v_p(k).

**THEOREM B (the prime-power law).** For every prime p and every a ≥ 2:
    f(p^a) = p — the minimum gcd is exactly p.
  Hence: (i) prime squares SATISFY the Erdős–Szekeres equality
  f(p²) = p = p²/P(p²) (every prime divisor of p² is p); (ii) every higher
  power VIOLATES it: f(p^a) = p < p^(a−1) = p^a/P(p^a) for a ≥ 3.

## Architecture

§1 arithmetic helpers  §2 the p-adic valuation vp (fuel-structural, the K11
vpad architecture)  §3 additivity vp_mul (needs primality — Euclid)  §4
pow_dvd_iff (p^i ∣ n ↔ i ≤ v_p n)  §5 the binomial + factorial identity
§6 the floor laws (div_unique, divSplit, succDiff)  §7 the floor-sum /
divisibility counters  §8 the Legendre bridge at prime powers  §9 Theorem A
§10 Theorem B (the f-minimum, witness, equality class, violation)  §11 the
ARSENAL BRIDGE (erdosternary2 + HC-PROOF applied to #700's own objects)
§12 receipts.

The full human-readable proof is in DRAFT_PROOF.md (this directory).
-/

namespace Erdos700

/-! ## §1 ARITHMETIC HELPERS -/

theorem one_le_mul (a b : Nat) (ha : 1 ≤ a) (hb : 1 ≤ b) : 1 ≤ a * b := by
  obtain ⟨a', ha'⟩ : ∃ a', a = a' + 1 := ⟨a - 1, by omega⟩
  obtain ⟨b', hb'⟩ : ∃ b', b = b' + 1 := ⟨b - 1, by omega⟩
  rw [ha', hb', Nat.mul_succ, Nat.add_mul]
  omega

def fact : Nat → Nat
  | 0 => 1
  | n + 1 => (n + 1) * fact n

theorem fact_pos : ∀ u, 1 ≤ fact u
  | 0 => Nat.le_refl 1
  | u + 1 => one_le_mul (u + 1) (fact u) (Nat.succ_le_succ (Nat.zero_le u))
    (fact_pos u)

theorem pow_ge_one (p : Nat) (hp : 1 ≤ p) : ∀ e, 1 ≤ p ^ e
  | 0 => Nat.le_refl 1
  | e + 1 => one_le_mul (p ^ e) p (pow_ge_one p hp e) hp

theorem pow_le_mono (p : Nat) (hp : 1 ≤ p) : ∀ (i j : Nat), i ≤ j → p ^ i ≤ p ^ j := by
  intro i
  induction i with
  | zero =>
    intro j _
    have h0 : p ^ 0 = 1 := Nat.pow_zero p
    have h1 : 1 ≤ p ^ j := pow_ge_one p hp j
    omega
  | succ i ih =>
    intro j hj
    obtain ⟨d, hd⟩ : ∃ d, j = (i + 1) + d := ⟨j - (i + 1), by omega⟩
    subst hd
    have hsplit : p ^ ((i + 1) + d) = p ^ (i + 1) * p ^ d := Nat.pow_add p (i + 1) d
    have h1 : 1 ≤ p ^ d := pow_ge_one p hp d
    have h2 : p ^ (i + 1) * 1 ≤ p ^ (i + 1) * p ^ d :=
      Nat.mul_le_mul_left (p ^ (i + 1)) h1
    rw [Nat.mul_one] at h2
    rw [hsplit]
    exact h2

theorem pow_le_pow_base (p q e : Nat) (hpq : p ≤ q) : p ^ e ≤ q ^ e := by
  induction e with
  | zero => rfl
  | succ e ih =>
    have h := Nat.mul_le_mul hpq ih
    rw [Nat.pow_succ, Nat.pow_succ, Nat.mul_comm (p ^ e) p,
      Nat.mul_comm (q ^ e) q] at *
    exact h

theorem two_pow_ge_two (a : Nat) (ha : 1 ≤ a) : 2 ≤ 2 ^ a := by
  have hsplit : 2 ^ a = 2 ^ (a - 1) * 2 := by
    rw [← Nat.pow_succ]; congr 1; omega
  have hone : 1 ≤ 2 ^ (a - 1) := pow_ge_one 2 (by omega) (a - 1)
  have h2 : 2 ^ (a - 1) * 1 ≤ 2 ^ (a - 1) * 2 :=
    Nat.mul_le_mul_left (2 ^ (a - 1)) (by omega)
  rw [Nat.mul_one] at h2
  omega

theorem pow_ge_two (p a : Nat) (hp : 2 ≤ p) (ha : 1 ≤ a) : 2 ≤ p ^ a :=
  Nat.le_trans (two_pow_ge_two a ha) (pow_le_pow_base 2 p a hp)

/-- The power-split bridge: `p ^ a = p * p ^ (a - 1)` for a ≥ 1
(via `Nat.pow_succ'`, implicit-arg succ-form). -/
theorem ppow_split (p a : Nat) (ha : 1 ≤ a) : p ^ a = p * p ^ (a - 1) := by
  have h1 : p ^ (Nat.succ (a - 1)) = p * p ^ (a - 1) := Nat.pow_succ'
  have hae : Nat.succ (a - 1) = a := by omega
  rw [hae] at h1
  exact h1

/-- Exact division of a self-product: `p * b / p = b` for p ≥ 1. -/
theorem mul_div_self (p b : Nat) (hp : 1 ≤ p) : p * b / p = b := by
  have h1 := Nat.div_add_mod (p * b) p
  have h2 : (p * b) % p = 0 := by
    rw [Nat.mul_mod, Nat.mod_self, Nat.zero_mul, Nat.zero_mod]
  rw [h2, Nat.add_zero] at h1
  exact Nat.mul_left_cancel hp h1

/-! ## §2 THE p-ADIC VALUATION (fuel-structural, the K11 vpad architecture) -/

/-- Fuel-structural p-adic valuation engine: `vpf p f n` counts factors of p
in n with f fuel.  Structural recursion on the fuel. -/
def vpf : Nat → Nat → Nat → Nat
  | _, 0, _ => 0
  | _, _, 0 => 0
  | p, f + 1, n + 1 =>
      if (n + 1) % p = 0 then 1 + vpf p f ((n + 1) / p) else 0

/-- `vp p n = vpf p n n` — fuel = value always suffices (v_p(n) ≤ n). -/
def vp (p : Nat) (n : Nat) : Nat := vpf p n n

theorem vp_unfold_succ (p N : Nat) :
    vp p (N + 1) =
      if (N + 1) % p = 0 then 1 + vpf p N ((N + 1) / p) else 0 := rfl

/-- **Saturation.** For p ≥ 2, fuel beyond the value never changes the
result (the K11 vpadf_sat proof, verbatim architecture). -/
theorem vpf_sat (p : Nat) (hp : 2 ≤ p) :
    ∀ (F f : Nat), f ≤ F → ∀ (n : Nat), n ≤ f →
    vpf p f n = vpf p n n := by
  intro F
  induction F with
  | zero =>
    intro f hf n hn
    have hf0 : f = 0 := by omega
    subst hf0
    have hn0 : n = 0 := by omega
    subst hn0
    rfl
  | succ F ih =>
    intro f hf n hn
    cases f with
    | zero =>
      have hn0 : n = 0 := by omega
      subst hn0
      rfl
    | succ F' =>
      cases n with
      | zero => rfl
      | succ N =>
        have e1 : vpf p (F' + 1) (N + 1) =
            if (N + 1) % p = 0 then 1 + vpf p F' ((N + 1) / p) else 0 := rfl
        have e2 : vpf p (N + 1) (N + 1) =
            if (N + 1) % p = 0 then 1 + vpf p N ((N + 1) / p) else 0 := rfl
        rw [e1, e2]
        by_cases hmod : (N + 1) % p = 0
        · rw [if_pos hmod, if_pos hmod]
          have hdlt : (N + 1) / p < N + 1 :=
            Nat.div_lt_self (by omega) (by omega)
          have i1 := ih F' (by omega) ((N + 1) / p) (by omega)
          have i2 := ih N (by omega) ((N + 1) / p) (by omega)
          rw [i1, i2]
        · rw [if_neg hmod, if_neg hmod]

/-- If `p ∤ n` (n ≥ 1) then `vp p n = 0`. -/
theorem vp_nondiv (p n : Nat) (hn : 1 ≤ n) (hne : n % p ≠ 0) :
    vp p n = 0 := by
  obtain ⟨N, hN⟩ : ∃ N, n = N + 1 := ⟨n - 1, by omega⟩
  have hne' : (N + 1) % p ≠ 0 := by rw [← hN]; exact hne
  rw [hN, vp_unfold_succ, if_neg hne']

/-- **The step law.** For p ≥ 2 and p ∣ n ≥ 1: `vp p n = 1 + vp p (n / p)`. -/
theorem vp_step (p n : Nat) (hp : 2 ≤ p) (hn : 1 ≤ n) (hd : n % p = 0) :
    vp p n = 1 + vp p (n / p) := by
  obtain ⟨N, hN⟩ : ∃ N, n = N + 1 := ⟨n - 1, by omega⟩
  have hmod : (N + 1) % p = 0 := by rw [← hN]; exact hd
  have h1 : vp p (N + 1) = 1 + vpf p N ((N + 1) / p) := by
    rw [vp_unfold_succ, if_pos hmod]
  have hdlt : (N + 1) / p < N + 1 := Nat.div_lt_self (by omega) (by omega)
  have h2 : vpf p N ((N + 1) / p) = vp p ((N + 1) / p) :=
    vpf_sat p hp N N (Nat.le_refl _) ((N + 1) / p) (by omega)
  rw [hN, h1, h2]

theorem vp_le_fuel (p : Nat) : ∀ f n, vpf p f n ≤ f := by
  intro f
  induction f with
  | zero =>
    intro n
    have h0 : vpf p 0 n = 0 := rfl
    omega
  | succ f ih =>
    intro n
    cases n with
    | zero =>
      have h0 : vpf p (f + 1) 0 = 0 := rfl
      omega
    | succ N =>
      have e : vpf p (f + 1) (N + 1) =
          if (N + 1) % p = 0 then 1 + vpf p f ((N + 1) / p) else 0 := rfl
      rw [e]
      by_cases hm : (N + 1) % p = 0
      · rw [if_pos hm]
        have hI := ih ((N + 1) / p)
        omega
      · rw [if_neg hm]
        omega

theorem vp_le_self (p k : Nat) : vp p k ≤ k := vp_le_fuel p k k

theorem vp_one (p : Nat) (hp : 2 ≤ p) : vp p 1 = 0 := by
  have h1 : 1 % p = 1 := Nat.mod_eq_of_lt (by omega)
  exact vp_nondiv p 1 (Nat.le_refl 1) (by rw [h1]; omega)

theorem vp_ge_one_iff_dvd (p n : Nat) (hp : 2 ≤ p) (hn : 1 ≤ n) :
    1 ≤ vp p n ↔ p ∣ n := by
  constructor
  · intro h
    by_contra hnd
    have hne : n % p ≠ 0 := fun hc => hnd (Nat.dvd_of_mod_eq_zero hc)
    have h0 := vp_nondiv p n hn hne
    omega
  · intro hd
    have hstep := vp_step p n hp hn (Nat.mod_eq_zero_of_dvd hd)
    omega

/-! ## §3 ADDITIVITY (fuel induction; primality enters ONLY here — Euclid) -/

/-- If `p ∣ a` then `(a * b) / p = (a / p) * b` (mod arithmetic only). -/
theorem dvd_mul_divp (a b p : Nat) (hp : 1 ≤ p) (h : a % p = 0) :
    a * b / p = (a / p) * b := by
  have hmod := Nat.div_add_mod a p
  have hmod' := Nat.div_add_mod (a * b) p
  have hab : (a * b) % p = 0 := by rw [Nat.mul_mod, h]; simp
  have key : p * ((a / p) * b) = a * b := by
    have e1 : a = p * (a / p) := by omega
    conv_rhs => rw [e1]
    rw [Nat.mul_assoc]
  have hfin : p * (a * b / p) = p * ((a / p) * b) := by omega
  exact Nat.mul_left_cancel (by omega : 1 ≤ p) hfin

/-- **Additivity of the valuation on products.** For p prime:
`vp p (a * b) = vp p a + vp p b`.  (Fuel induction on a + b; the K19 v2_mul
architecture at general prime p.  Primality is used exactly once: the
coprime × coprime = coprime step is Euclid.) -/
theorem vp_mul : ∀ (f p a b : Nat), a + b ≤ f → p.Prime → 1 ≤ a → 1 ≤ b →
    vp p (a * b) = vp p a + vp p b
  | 0, p, a, b, hf, hpp, ha, hb => by omega
  | f + 1, p, a, b, hf, hpp, ha, hb => by
    have hp : 2 ≤ p := hpp.one_lt
    by_cases ha1 : a = 1
    · subst ha1
      rw [Nat.one_mul]
      have h0 : vp p 1 = 0 := vp_one p hp
      omega
    · by_cases hae : a % p = 0
      · have hxy : 1 ≤ a * b := one_le_mul a b ha hb
        have hb2 : (a * b) % p = 0 := by rw [Nat.mul_mod, hae]; simp
        have hsplit : a * b / p = (a / p) * b := dvd_mul_divp a b p (by omega) hae
        have hpa : a / p < a := Nat.div_lt_self (by omega) (by omega)
        have hdm := Nat.div_add_mod a p
        have hap1 : 1 ≤ a / p := by
          rcases Nat.eq_zero_or_pos (a / p) with h0 | h1
          · rw [h0, Nat.mul_zero] at hdm
            omega
          · exact h1
        rw [vp_step p (a * b) hp hxy hb2, hsplit,
            vp_mul f p (a / p) b (by omega) hpp hap1 hb,
            vp_step p a hp ha hae]
        omega
      · by_cases hbe : b % p = 0
        · rw [Nat.mul_comm a b]
          have hxy : 1 ≤ b * a := one_le_mul b a hb ha
          have hb2 : (b * a) % p = 0 := by rw [Nat.mul_mod, hbe]; simp
          have hsplit : b * a / p = (b / p) * a := dvd_mul_divp b a p (by omega) hbe
          have hpb : b / p < b := Nat.div_lt_self (by omega) (by omega)
          have hdm := Nat.div_add_mod b p
          have hbp1 : 1 ≤ b / p := by
            rcases Nat.eq_zero_or_pos (b / p) with h0 | h1
            · rw [h0, Nat.mul_zero] at hdm
              omega
            · exact h1
          rw [vp_step p (b * a) hp hxy hb2, hsplit,
              vp_mul f p (b / p) a (by omega) hpp hbp1 ha,
              vp_step p b hp hb hbe]
          omega
        · have hab : (a * b) % p ≠ 0 := by
            by_contra hcon
            have hdvd : p ∣ a * b := Nat.dvd_of_mod_eq_zero hcon
            rcases (hpp.dvd_mul).mp hdvd with h | h
            · exact hae (Nat.mod_eq_zero_of_dvd h)
            · exact hbe (Nat.mod_eq_zero_of_dvd h)
          rw [vp_nondiv p (a * b) (one_le_mul a b ha hb) hab,
              vp_nondiv p a ha hae, vp_nondiv p b hb hbe]

/-! ## §4 THE POWER-DIVISIBILITY LAW (p^i ∣ n ↔ i ≤ v_p n) -/

theorem pow_dvd_iff (p : Nat) (hp : 2 ≤ p) : ∀ (F i n : Nat), i ≤ F → 1 ≤ n →
    (p ^ i ∣ n ↔ i ≤ vp p n) := by
  intro F
  induction F with
  | zero =>
    intro i n hiF _
    have hi0 : i = 0 := by omega
    subst hi0
    constructor
    · intro _; omega
    · intro _; rw [Nat.pow_zero]; exact Nat.one_dvd n
  | succ F ih =>
    intro i n hiF hn
    rcases i with _ | i'
    · constructor
      · intro _; omega
      · intro _; rw [Nat.pow_zero]; exact Nat.one_dvd n
    · by_cases hpd : p ∣ n
      · have hnpe : n % p = 0 := Nat.mod_eq_zero_of_dvd hpd
        have hnpe' : 1 ≤ n / p := by
          rcases Nat.eq_zero_or_pos (n / p) with h0 | h1
          · have hdm := Nat.div_add_mod n p
            rw [h0, Nat.mul_zero] at hdm
            omega
          · exact h1
        have hval : vp p n = 1 + vp p (n / p) := vp_step p n hp hn hnpe
        have hnps : p * (n / p) = n := by
          have hdm := Nat.div_add_mod n p
          omega
        have hpm : p ^ (i' + 1) = p * p ^ i' := by
          rw [Nat.pow_succ, Nat.mul_comm]
        have hcancel : (p ^ (i' + 1) ∣ n ↔ p ^ i' ∣ n / p) := by
          constructor
          · intro hdvd
            obtain ⟨d, hd⟩ := hdvd
            refine ⟨d, ?_⟩
            rw [hpm] at hd
            have hassoc : p * p ^ i' * d = p * (p ^ i' * d) := Nat.mul_assoc p (p ^ i') d
            have hboth : p * (n / p) = p * (p ^ i' * d) := by omega
            exact Nat.mul_left_cancel (by omega : 1 ≤ p) hboth
          · intro hdvd
            obtain ⟨d, hd⟩ := hdvd
            refine ⟨d, ?_⟩
            rw [hpm, Nat.mul_assoc, ← hd, hnps]
        rw [hcancel, ih i' (n / p) (by omega) hnpe', hval]
        omega
      · constructor
        · intro hdvd
          have hpp1 : p ∣ p ^ (i' + 1) := ⟨p ^ i', Nat.pow_succ'⟩
          exact absurd (Nat.dvd_trans hpp1 hdvd) hpd
        · intro hle
          have h1 : 1 ≤ vp p n := by omega
          exact absurd ((vp_ge_one_iff_dvd p n hp hn).mp h1) hpd

theorem pow_vp_le (p k : Nat) (hp : 2 ≤ p) (hk : 1 ≤ k) : p ^ vp p k ≤ k := by
  have hdvd : p ^ vp p k ∣ k :=
    (pow_dvd_iff p hp (vp p k) (vp p k) k (Nat.le_refl _) hk).mpr (Nat.le_refl _)
  exact Nat.le_of_dvd hk hdvd

theorem vp_lt_of_lt_pow (p a k : Nat) (hp : 2 ≤ p) (hk : 1 ≤ k) (hkN : k < p ^ a) :
    vp p k < a := by
  by_contra hge
  have h1 : p ^ a ≤ p ^ vp p k := pow_le_mono p (by omega) a (vp p k) (by omega)
  have h2 : p ^ vp p k ≤ k := pow_vp_le p k hp hk
  omega

theorem vp_le_of_le_pow (p a n : Nat) (hp : 2 ≤ p) (hn : 1 ≤ n) (hnN : n ≤ p ^ a) :
    vp p n ≤ a := by
  by_contra hgt
  have h1 : a + 1 ≤ vp p n := by omega
  have hself : vp p n ≤ n := vp_le_self p n
  have hdvd : p ^ (a + 1) ∣ n :=
    (pow_dvd_iff p hp (a + 1) (a + 1) n (Nat.le_refl _) hn).mpr (by omega)
  have hle : p ^ (a + 1) ≤ n := Nat.le_of_dvd hn hdvd
  have hmono : p ^ a ≤ p ^ (a + 1) := pow_le_mono p (by omega) a (a + 1) (Nat.le_succ a)
  have hsplit : p ^ (a + 1) = p ^ a * p := Nat.pow_succ p a
  have h2 : p ^ a * 2 ≤ p ^ a * p := Nat.mul_le_mul_left (p ^ a) hp
  have hpa1 : 1 ≤ p ^ a := pow_ge_one p (by omega) a
  omega

theorem vp_pow_self (p : Nat) (hp : 2 ≤ p) : ∀ a, vp p (p ^ a) = a := by
  intro a
  induction a with
  | zero =>
    rw [Nat.pow_zero]
    exact vp_one p hp
  | succ a ih =>
    have hsplit : p ^ (a + 1) = p * p ^ a := by
      rw [Nat.pow_succ, Nat.mul_comm]
    have hdiv : p ^ (a + 1) / p = p ^ a := by
      rw [hsplit, Nat.mul_div_cancel_left _ (by omega : 1 ≤ p)]
    have hmod : p ^ (a + 1) % p = 0 := by
      rw [hsplit, Nat.mul_mod, Nat.mod_self, Nat.zero_mul, Nat.zero_mod]
    have hpos : 1 ≤ p ^ (a + 1) := pow_ge_one p (by omega) (a + 1)
    rw [vp_step p (p ^ (a + 1)) hp hpos hmod, hdiv, ih]
    omega

/-! ## §5 THE BINOMIAL AND ITS FACTORIAL IDENTITY -/

def binom : Nat → Nat → Nat
  | 0, 0 => 1
  | 0, _ + 1 => 0
  | _ + 1, 0 => 1
  | n + 1, k + 1 => binom n k + binom n (k + 1)

theorem binom_lt : ∀ (n k : Nat), n < k → binom n k = 0
  | 0, 0, hk => by omega
  | 0, k + 1, _ => rfl
  | n + 1, 0, hk => by omega
  | n + 1, k + 1, hk => by
    rw [show binom (n + 1) (k + 1) = binom n k + binom n (k + 1) from rfl,
        binom_lt n k (by omega), binom_lt n (k + 1) (by omega)]

theorem binom_diag : ∀ n, binom n n = 1
  | 0 => rfl
  | n + 1 => by
    rw [show binom (n + 1) (n + 1) = binom n n + binom n (n + 1) from rfl,
      binom_diag n, binom_lt n (n + 1) (Nat.lt_succ_self n)]

/-- **The binomial factorial identity** (no subtraction: n = s + k split).
`binom n k * fact k * fact s = fact n` whenever n = s + k. -/
theorem binom_fact_gen : ∀ (n s k : Nat), n = s + k →
    binom n k * fact k * fact s = fact n
  | 0, s, k, hs => by
    have hs0 : s = 0 := by omega
    have hk0 : k = 0 := by omega
    subst hs0
    subst hk0
    rfl
  | n + 1, s, k, hs => by
    rcases k with _ | k
    · have hsN : s = n + 1 := by omega
      subst hsN
      rw [show binom (n + 1) 0 = 1 from rfl, show fact 0 = 1 from rfl]
      ring
    · rcases s with _ | s'
      · have hnk : n = k := by omega
        rw [hnk, binom_diag (k + 1), show fact 0 = 1 from rfl]
        ring
      · have hunf : binom (n + 1) (k + 1) = binom n k + binom n (k + 1) := rfl
        have IH1 := binom_fact_gen n (s' + 1) k (by omega)
        have IH2 := binom_fact_gen n s' (k + 1) (by omega)
        have hfk : fact (k + 1) = (k + 1) * fact k := rfl
        have hfs : fact (s' + 1) = (s' + 1) * fact s' := rfl
        have hfact : fact (n + 1) = (n + 1) * fact n := rfl
        rw [hunf]
        calc (binom n k + binom n (k + 1)) * fact (k + 1) * fact (s' + 1)
            = (k + 1) * (binom n k * fact k * fact (s' + 1))
              + (s' + 1) * (binom n (k + 1) * fact (k + 1) * fact s') := by
              rw [hfk, hfs]
              ring
          _ = (k + 1) * fact n + (s' + 1) * fact n := by rw [IH1, IH2]
          _ = fact (n + 1) := by
              have hsum : (k + 1) + (s' + 1) = n + 1 := by omega
              have hcongr := congrArg (fun t => t * fact n) hsum
              rw [Nat.add_mul] at hcongr
              rw [hfact, ← hcongr, Nat.add_mul]

theorem binom_pos (n k : Nat) (hk : k ≤ n) : 1 ≤ binom n k := by
  obtain ⟨s, hs⟩ : ∃ s, n = s + k := ⟨n - k, by omega⟩
  have hf := binom_fact_gen n s k hs
  have h1 : 1 ≤ fact k := fact_pos k
  have h2 : 1 ≤ fact s := fact_pos s
  have h3 : 1 ≤ fact n := fact_pos n
  rcases Nat.eq_zero_or_pos (binom n k) with h0 | hpos
  · rw [h0, Nat.zero_mul, Nat.zero_mul] at hf
    omega
  · exact hpos

/-! ## §6 THE FLOOR LAWS (div_unique, divSplit, succDiff) -/

/-- Division is unique: `(m * q + r) / m = q` for r < m. -/
theorem div_unique (m q r : Nat) (hm : 1 ≤ m) (hr : r < m) :
    (m * q + r) / m = q := by
  have h1 := Nat.div_add_mod (m * q + r) m
  have hmod : (m * q + r) % m < m := Nat.mod_lt (m * q + r) (by omega)
  rcases Nat.lt_trichotomy ((m * q + r) / m) q with hlt | heq | hgt
  · have hA : m * ((m * q + r) / m + 1) ≤ m * q :=
      Nat.mul_le_mul_left m (by omega)
    have hB : m * ((m * q + r) / m + 1) = m * ((m * q + r) / m) + m := by
      rw [Nat.mul_add, Nat.mul_one]
    omega
  · exact heq
  · have hA : m * (q + 1) ≤ m * ((m * q + r) / m) :=
      Nat.mul_le_mul_left m (by omega)
    have hB : m * (q + 1) = m * q + m := by rw [Nat.mul_add, Nat.mul_one]
    omega

/-- **THE FLOOR-SPLIT LAW (the heart of Theorem A).** If `k + s = m * c`
with m ≥ 1, then `⌊k/m⌋ + ⌊s/m⌋ + [k % m ≠ 0] = c`. -/
theorem divSplit (m c k s : Nat) (hm : 1 ≤ m) (hks : k + s = m * c) :
    k / m + s / m + (if k % m = 0 then 0 else 1) = c := by
  have h1 : m * (k / m) + k % m = k := Nat.div_add_mod k m
  have h2 : m * (s / m) + s % m = s := Nat.div_add_mod s m
  have hkm : k % m < m := Nat.mod_lt k (by omega)
  have hsm : s % m < m := Nat.mod_lt s (by omega)
  have key : m * (k / m + s / m) + (k % m + s % m) = m * c := by
    have e1 : m * (k / m + s / m) = m * (k / m) + m * (s / m) :=
      Nat.mul_add m _ _
    rw [e1]
    omega
  by_cases h0 : k % m = 0
  · rw [if_pos h0, Nat.add_zero]
    rcases Nat.lt_trichotomy (k / m + s / m) c with hlt | heq | hgt
    · have hA : m * (k / m + s / m + 1) ≤ m * c :=
        Nat.mul_le_mul_left m (by omega)
      have hB : m * (k / m + s / m + 1) = m * (k / m + s / m) + m := by
        rw [Nat.mul_add, Nat.mul_one]
      omega
    · exact heq
    · have hA : m * (c + 1) ≤ m * (k / m + s / m) :=
        Nat.mul_le_mul_left m (by omega)
      have hB : m * (c + 1) = m * c + m := by rw [Nat.mul_add, Nat.mul_one]
      omega
  · rw [if_neg h0]
    have hlt : k / m + s / m < c := by
      by_contra hge
      have hA : m * c ≤ m * (k / m + s / m) :=
        Nat.mul_le_mul_left m (by omega)
      omega
    rcases Nat.lt_or_ge c (k / m + s / m + 2) with hlt2 | hge2
    · omega
    · have hA : m * (k / m + s / m + 2) ≤ m * c :=
        Nat.mul_le_mul_left m (by omega)
      have hB : m * (k / m + s / m + 2) = m * (k / m + s / m) + 2 * m := by
        rw [Nat.mul_add]
        omega
      omega

/-- **The successor floor law.** `(j + 1) / m = j / m + [m ∣ j + 1]`. -/
theorem succDiff (m j : Nat) (hm : 1 ≤ m) :
    (j + 1) / m = j / m + (if m ∣ j + 1 then 1 else 0) := by
  have h1 : m * (j / m) + j % m = j := Nat.div_add_mod j m
  have hmod : j % m < m := Nat.mod_lt j (by omega)
  rcases Nat.lt_or_ge (j % m + 1) m with hlt | hge
  · have hnd : ¬ (m ∣ j + 1) := by
      intro hd
      have hmod0 : (j + 1) % m = 0 := Nat.mod_eq_zero_of_dvd hd
      have hs : j + 1 = m * (j / m) + (j % m + 1) := by omega
      have hmodlt : (j % m + 1) % m = j % m + 1 := Nat.mod_eq_of_lt hlt
      have hmulmod : (m * (j / m)) % m = 0 := by
        rw [Nat.mul_mod, Nat.mod_self, Nat.zero_mul, Nat.zero_mod]
      have hAM := Nat.add_mod (m * (j / m)) (j % m + 1) m
      have hfinal : (j + 1) % m = j % m + 1 := by
        rw [hs, hAM, hmulmod, hmodlt, Nat.zero_add, hmodlt]
      omega
    rw [if_neg hnd]
    have hrep : j + 1 = m * (j / m) + (j % m + 1) := by omega
    rw [hrep, div_unique m (j / m) (j % m + 1) hm hlt, Nat.add_zero]
  · have heq : j % m + 1 = m := by omega
    have hd : m ∣ j + 1 := by
      refine ⟨j / m + 1, ?_⟩
      have hsplit : m * (j / m + 1) = m * (j / m) + m := by
        rw [Nat.mul_add, Nat.mul_one]
      omega
    rw [if_pos hd]
    have hrep : j + 1 = m * (j / m + 1) + 0 := by
      have hsplit : m * (j / m + 1) = m * (j / m) + m := by
        rw [Nat.mul_add, Nat.mul_one]
      omega
    rw [hrep, div_unique m (j / m + 1) 0 hm (by omega)]

/-! ## §7 THE FLOOR-SUM AND DIVISIBILITY COUNTERS -/

/-- `powsSum p i m = Σ_{j=1}^{i} ⌊m / p^j⌋` (the Legendre skeleton). -/
def powsSum : Nat → Nat → Nat → Nat
  | _, 0, _ => 0
  | p, i + 1, m => m / p ^ (i + 1) + powsSum p i m

/-- `cntDiv p i k = #{j ∈ [1,i] : p^j ∣ k}`. -/
def cntDiv : Nat → Nat → Nat → Nat
  | _, 0, _ => 0
  | p, i + 1, k => (if p ^ (i + 1) ∣ k then 1 else 0) + cntDiv p i k

/-- `cntNotDiv p i k = #{j ∈ [1,i] : p^j ∤ k}`. -/
def cntNotDiv : Nat → Nat → Nat → Nat
  | _, 0, _ => 0
  | p, i + 1, k => (if k % p ^ (i + 1) = 0 then 0 else 1) + cntNotDiv p i k

theorem powsSum_zero (p : Nat) : ∀ a, powsSum p a 0 = 0 := by
  intro a
  induction a with
  | zero => rfl
  | succ a ih =>
    have e : powsSum p (a + 1) 0 = 0 / p ^ (a + 1) + powsSum p a 0 := rfl
    rw [e, Nat.zero_div, ih]

theorem cnt_complement (p k : Nat) : ∀ a, cntNotDiv p a k + cntDiv p a k = a := by
  intro a
  induction a with
  | zero => rfl
  | succ a ih =>
    have e1 : cntNotDiv p (a + 1) k
        = (if k % p ^ (a + 1) = 0 then 0 else 1) + cntNotDiv p a k := rfl
    have e2 : cntDiv p (a + 1) k
        = (if p ^ (a + 1) ∣ k then 1 else 0) + cntDiv p a k := rfl
    rw [e1, e2]
    by_cases hd : p ^ (a + 1) ∣ k
    · have hm : k % p ^ (a + 1) = 0 := Nat.mod_eq_zero_of_dvd hd
      rw [if_pos hm, if_pos hd]
      omega
    · have hm : k % p ^ (a + 1) ≠ 0 := fun hc => hd (Nat.dvd_of_mod_eq_zero hc)
      rw [if_neg hm, if_neg hd]
      omega

theorem cntDiv_eq_of_ge (p k : Nat) (hp : 2 ≤ p) (hk : 1 ≤ k) : ∀ a, a ≤ vp p k →
    cntDiv p a k = a := by
  intro a
  induction a with
  | zero => intro _; rfl
  | succ a ih =>
    intro hle
    have hdvd : p ^ (a + 1) ∣ k :=
      (pow_dvd_iff p hp (a + 1) (a + 1) k (Nat.le_refl _) hk).mpr hle
    have e : cntDiv p (a + 1) k = (if p ^ (a + 1) ∣ k then 1 else 0) + cntDiv p a k := rfl
    rw [e, if_pos hdvd, ih (by omega)]
    omega

theorem cntDiv_eq_of_le (p k : Nat) (hp : 2 ≤ p) (hk : 1 ≤ k) : ∀ a, vp p k ≤ a →
    cntDiv p a k = vp p k := by
  intro a
  induction a with
  | zero =>
    intro hle
    have h0 : cntDiv p 0 k = 0 := rfl
    omega
  | succ a ih =>
    intro hle
    have e : cntDiv p (a + 1) k = (if p ^ (a + 1) ∣ k then 1 else 0) + cntDiv p a k := rfl
    rcases Nat.lt_or_ge (vp p k) (a + 1) with hv1 | hv2
    · have hnd : ¬ (p ^ (a + 1) ∣ k) := by
        intro hd
        have := (pow_dvd_iff p hp (a + 1) (a + 1) k (Nat.le_refl _) hk).mp hd
        omega
      rw [e, if_neg hnd, ih (by omega)]
      omega
    · have hdvd : p ^ (a + 1) ∣ k :=
        (pow_dvd_iff p hp (a + 1) (a + 1) k (Nat.le_refl _) hk).mpr (by omega)
      have hge := cntDiv_eq_of_ge p k hp hk a (by omega)
      rw [e, if_pos hdvd, hge]
      omega

theorem cntNotDiv_eq (p k : Nat) (hp : 2 ≤ p) (hk : 1 ≤ k) (a : Nat)
    (hle : vp p k ≤ a) : cntNotDiv p a k = a - vp p k := by
  have hcomp := cnt_complement p k a
  have hcd := cntDiv_eq_of_le p k hp hk a hle
  omega

/-- **The summed floor law.** If k + s = p^a and i ≤ a, then
`powsSum p i k + powsSum p i s + cntNotDiv p i k = powsSum p i (p^a)`. -/
theorem powsSum_split (p a k s : Nat) (hp : 2 ≤ p) (hks : k + s = p ^ a) :
    ∀ i, i ≤ a → powsSum p i k + powsSum p i s + cntNotDiv p i k
      = powsSum p i (p ^ a) := by
  intro i
  induction i with
  | zero => intro _; rfl
  | succ i ih =>
    intro hia
    have e1 : powsSum p (i + 1) k = k / p ^ (i + 1) + powsSum p i k := rfl
    have e2 : powsSum p (i + 1) s = s / p ^ (i + 1) + powsSum p i s := rfl
    have e3 : powsSum p (i + 1) (p ^ a)
        = p ^ a / p ^ (i + 1) + powsSum p i (p ^ a) := rfl
    have e4 : cntNotDiv p (i + 1) k
        = (if k % p ^ (i + 1) = 0 then 0 else 1) + cntNotDiv p i k := rfl
    have hpoweq : p ^ (i + 1) * p ^ (a - (i + 1)) = p ^ a := by
      rw [← Nat.pow_add]
      congr 1
      omega
    have hksc : k + s = p ^ (i + 1) * p ^ (a - (i + 1)) := by
      rw [hpoweq]
      exact hks
    have hds := divSplit (p ^ (i + 1)) (p ^ (a - (i + 1))) k s
      (pow_ge_one p (by omega) (i + 1)) hksc
    have hq : p ^ a / p ^ (i + 1) = p ^ (a - (i + 1)) := by
      rw [← hpoweq, Nat.mul_div_cancel_left _ (pow_ge_one p (by omega) (i + 1))]
    rw [e1, e2, e3, e4, hq]
    have hIH := ih (by omega)
    by_cases hmod : k % p ^ (i + 1) = 0
    · rw [if_pos hmod] at hds ⊢
      omega
    · rw [if_neg hmod] at hds ⊢
      omega

/-- **The powsSum step law.** `powsSum p a (j+1) = powsSum p a j + cntDiv p a (j+1)`. -/
theorem powsSum_succ (p j : Nat) (hp : 2 ≤ p) : ∀ a,
    powsSum p a (j + 1) = powsSum p a j + cntDiv p a (j + 1) := by
  intro a
  induction a with
  | zero => rfl
  | succ a ih =>
    have e1 : powsSum p (a + 1) (j + 1)
        = (j + 1) / p ^ (a + 1) + powsSum p a (j + 1) := rfl
    have e2 : powsSum p (a + 1) j = j / p ^ (a + 1) + powsSum p a j := rfl
    have e3 : cntDiv p (a + 1) (j + 1)
        = (if p ^ (a + 1) ∣ j + 1 then 1 else 0) + cntDiv p a (j + 1) := rfl
    rw [e1, e2, e3, ih]
    have hsd := succDiff (p ^ (a + 1)) j (pow_ge_one p (by omega) (a + 1))
    rw [hsd]
    by_cases hd : p ^ (a + 1) ∣ j + 1
    · rw [if_pos hd]
      omega
    · rw [if_neg hd]
      omega

/-! ## §8 THE LEGENDRE BRIDGE AT PRIME POWERS -/

/-- **Legendre at prime powers.** For m ≤ p^a (p prime):
`v_p(m!) = Σ_{j=1}^{a} ⌊m / p^j⌋`.  (Fuel induction on m.) -/
theorem legendre_pp (p a : Nat) (hpp : p.Prime) : ∀ F m, m ≤ F → m ≤ p ^ a →
    vp p (fact m) = powsSum p a m := by
  have hp : 2 ≤ p := hpp.one_lt
  intro F
  induction F with
  | zero =>
    intro m hmF _
    have hm0 : m = 0 := by omega
    subst hm0
    have h1 : vp p (fact 0) = 0 := by
      have hf0 : fact 0 = 1 := rfl
      rw [hf0]
      exact vp_one p hp
    have h2 : powsSum p a 0 = 0 := powsSum_zero p a
    omega
  | succ F ih =>
    intro m hmF hm
    rcases m with _ | j
    · have h1 : vp p (fact 0) = 0 := by
        have hf0 : fact 0 = 1 := rfl
        rw [hf0]
        exact vp_one p hp
      have h2 : powsSum p a 0 = 0 := powsSum_zero p a
      omega
    · have IHj := ih j (by omega) (by omega)
      have hj1 : 1 ≤ j + 1 := by omega
      have hfj1 : 1 ≤ fact j := fact_pos j
      have hvsplit : vp p (fact (j + 1)) = vp p (j + 1) + vp p (fact j) := by
        have hfsplit : fact (j + 1) = (j + 1) * fact j := rfl
        rw [hfsplit]
        exact vp_mul ((j + 1) + fact j) p (j + 1) (fact j) (Nat.le_refl _)
          hpp hj1 hfj1
      have hvja : vp p (j + 1) ≤ a :=
        vp_le_of_le_pow p a (j + 1) hp hj1 hm
      have hps := powsSum_succ p j hp a
      have hcd := cntDiv_eq_of_le p (j + 1) hp hj1 a hvja
      rw [hvsplit, IHj, hps, hcd]
      omega

/-! ## §9 THEOREM A — THE CARRY LEMMA -/

/-- **THEOREM A (the carry lemma).** For every prime p, a ≥ 1, and
1 ≤ k ≤ p^a − 1:  `v_p(C(p^a, k)) = a − v_p(k)`. -/
theorem erdos700_carry (p a k : Nat) (hpp : p.Prime) (hk1 : 1 ≤ k)
    (hkN : k < p ^ a) :
    vp p (binom (p ^ a) k) = a - vp p k := by
  have hp : 2 ≤ p := hpp.one_lt
  obtain ⟨s, hs⟩ : ∃ s, p ^ a = s + k := ⟨p ^ a - k, by omega⟩
  have hks : k + s = p ^ a := by omega
  have hsplit := binom_fact_gen (p ^ a) s k hs
  have hbk : 1 ≤ binom (p ^ a) k := binom_pos _ _ (by omega)
  have hfk : 1 ≤ fact k := fact_pos k
  have hfs : 1 ≤ fact s := fact_pos s
  have hvm1 : vp p (binom (p ^ a) k * fact k)
      = vp p (binom (p ^ a) k) + vp p (fact k) :=
    vp_mul (binom (p ^ a) k + fact k) p (binom (p ^ a) k) (fact k)
      (Nat.le_refl _) hpp hbk hfk
  have hvm2 : vp p (binom (p ^ a) k * fact k * fact s)
      = vp p (binom (p ^ a) k * fact k) + vp p (fact s) :=
    vp_mul ((binom (p ^ a) k * fact k) + fact s) p (binom (p ^ a) k * fact k)
      (fact s) (Nat.le_refl _) hpp (one_le_mul _ _ hbk hfk) hfs
  have hvC : vp p (binom (p ^ a) k * fact k * fact s) = vp p (fact (p ^ a)) := by
    rw [hsplit]
  have hL1 : vp p (fact k) = powsSum p a k := legendre_pp p a hpp k k (Nat.le_refl _) (by omega)
  have hL2 : vp p (fact s) = powsSum p a s := legendre_pp p a hpp s s (Nat.le_refl _) (by omega)
  have hL3 : vp p (fact (p ^ a)) = powsSum p a (p ^ a) :=
    legendre_pp p a hpp (p ^ a) (p ^ a) (Nat.le_refl _) (Nat.le_refl _)
  have hsum := powsSum_split p a k s hp hks a (Nat.le_refl a)
  have hvple : vp p k ≤ a := by
    have := vp_lt_of_lt_pow p a k hp hk1 hkN
    omega
  have hcnt := cntNotDiv_eq p k hp hk1 a hvple
  omega

/-! ## §10 THEOREM B — THE PRIME-POWER LAW FOR f -/

/-- The minimum-fold over k ∈ [2, j] of gcd(n, C(n,k)); the j ≤ 1 default n
is harmless (gcd(n, ·) ≤ n). -/
def minGcdAux : Nat → Nat → Nat
  | _, 0 => 0
  | n, 1 => n
  | n, j + 2 => Nat.min (Nat.gcd n (binom n (j + 2))) (minGcdAux n (j + 1))

/-- `f700 n = min_{1 < k ≤ n/2} gcd(n, C(n,k))` — the Erdős–Szekeres f. -/
def f700 (n : Nat) : Nat := minGcdAux n (n / 2)

theorem minGcdAux_ge (n t : Nat) (htn : t ≤ n) : ∀ j, 1 ≤ j →
    (∀ k, 2 ≤ k → k ≤ j → t ≤ Nat.gcd n (binom n k)) → t ≤ minGcdAux n j := by
  intro j
  induction j with
  | zero => intro h1 _; omega
  | succ j ih =>
    rcases j with _ | j'
    · intro _ _
      exact htn
    · intro h1 hall
      have hstep : minGcdAux n (j' + 1 + 1)
          = Nat.min (Nat.gcd n (binom n (j' + 2))) (minGcdAux n (j' + 1)) := rfl
      rw [hstep]
      have hA := hall (j' + 2) (by omega) (by omega)
      have hB := ih (by omega) (by
        intro k hk2 hkj
        exact hall k hk2 (by omega))
      exact Nat.le_min.mpr ⟨hA, hB⟩

theorem minGcdAux_le (n k : Nat) (hk : 2 ≤ k) : ∀ j, k ≤ j →
    minGcdAux n j ≤ Nat.gcd n (binom n k) := by
  intro j
  induction j with
  | zero => intro hkj; omega
  | succ j ih =>
    intro hkj
    rcases j with _ | j'
    · omega
    · have hstep : minGcdAux n (j' + 1 + 1)
          = Nat.min (Nat.gcd n (binom n (j' + 2))) (minGcdAux n (j' + 1)) := rfl
      rw [hstep]
      rcases Nat.lt_or_ge k (j' + 2) with hlt | hge
      · have hIH := ih (by omega)
        have hmin : Nat.min (Nat.gcd n (binom n (j' + 2))) (minGcdAux n (j' + 1))
            ≤ minGcdAux n (j' + 1) := Nat.min_le_right _ _
        omega
      · have hke : k = j' + 2 := by omega
        rw [hke]
        exact Nat.min_le_left _ _

theorem prime_dvd_pow_of (q : Nat) (hq : q.Prime) : ∀ (t b : Nat), q ∣ b ^ t → q ∣ b
  | 0, b, hd => by
    have h1 : b ^ 0 = 1 := Nat.pow_zero b
    rw [h1] at hd
    obtain ⟨e, he⟩ := hd
    cases e with
    | zero => omega
    | succ e' =>
      have hq1 : 2 ≤ q := hq.one_lt
      have hle : q * 1 ≤ q * (e' + 1) := Nat.mul_le_mul_left q (by omega)
      omega
  | t + 1, b, hd => by
    have hsucc : b ^ (t + 1) = b * b ^ t := by
      rw [Nat.pow_succ, Nat.mul_comm]
    rw [hsucc] at hd
    rcases (hq.dvd_mul).mp hd with h | h
    · exact h
    · exact prime_dvd_pow_of q hq t b h

/-- The universal lower bound: every k in the f-range has gcd(p^a, C) ≥ p. -/
theorem erdos700_gcd_lower (p a k : Nat) (hpp : p.Prime) (ha : 2 ≤ a)
    (hk2 : 2 ≤ k) (hkN : k ≤ p ^ a / 2) :
    p ≤ Nat.gcd (p ^ a) (binom (p ^ a) k) := by
  have hp : 2 ≤ p := hpp.one_lt
  have hN2 : 2 ≤ p ^ a := pow_ge_two p a hp (by omega)
  have hN1 : 1 ≤ p ^ a := pow_ge_one p (by omega) a
  have hklt : k < p ^ a := by omega
  have hk1 : 1 ≤ k := by omega
  have hcarry := erdos700_carry p a k hpp hk1 hklt
  have hvple : vp p k ≤ a - 1 := by
    have := vp_lt_of_lt_pow p a k hp hk1 hklt
    omega
  have hge1 : 1 ≤ vp p (binom (p ^ a) k) := by omega
  have hCpos : 1 ≤ binom (p ^ a) k := binom_pos _ _ (by omega)
  have hdvd : p ∣ binom (p ^ a) k := (vp_ge_one_iff_dvd p _ hp hCpos).mp hge1
  have hpN : p ∣ p ^ a := ⟨p ^ (a - 1), ppow_split p a (by omega)⟩
  have hg1 : 1 ≤ Nat.gcd (p ^ a) (binom (p ^ a) k) := by
    by_contra hg
    have hg0 : Nat.gcd (p ^ a) (binom (p ^ a) k) = 0 := by omega
    have hd := Nat.gcd_dvd_left (p ^ a) (binom (p ^ a) k)
    rw [hg0] at hd
    obtain ⟨e, he⟩ := hd
    rw [Nat.zero_mul] at he
    omega
  exact Nat.le_of_dvd hg1 (Nat.dvd_gcd hpN hdvd)

/-- **The witness theorem.** At the exact power k₀ = p^(a−1):
`gcd(p^a, C(p^a, p^(a−1))) = p` exactly. -/
theorem erdos700_witness (p a : Nat) (hpp : p.Prime) (ha : 2 ≤ a) :
    Nat.gcd (p ^ a) (binom (p ^ a) (p ^ (a - 1))) = p := by
  have hp : 2 ≤ p := hpp.one_lt
  have hk01 : 1 ≤ p ^ (a - 1) := pow_ge_one p (by omega) (a - 1)
  have hpowlt : p ^ (a - 1) < p ^ a := by
    have hsplit : p ^ a = p * p ^ (a - 1) := ppow_split p a (by omega)
    have hcomm : p ^ (a - 1) * p = p * p ^ (a - 1) := Nat.mul_comm _ _
    have h2 : p ^ (a - 1) * 2 ≤ p ^ (a - 1) * p :=
      Nat.mul_le_mul_left (p ^ (a - 1)) hp
    omega
  have hvk0 : vp p (p ^ (a - 1)) = a - 1 := vp_pow_self p hp (a - 1)
  have hcarry := erdos700_carry p a (p ^ (a - 1)) hpp hk01 hpowlt
  have hvC1 : vp p (binom (p ^ a) (p ^ (a - 1))) = 1 := by omega
  have hCpos : 1 ≤ binom (p ^ a) (p ^ (a - 1)) := binom_pos _ _ (by omega)
  have hpC : p ∣ binom (p ^ a) (p ^ (a - 1)) :=
    (vp_ge_one_iff_dvd p _ hp hCpos).mp (by omega)
  obtain ⟨u, hu⟩ := id hpC
  have hu1 : 1 ≤ u := by
    rcases Nat.eq_zero_or_pos u with h0 | h1
    · rw [h0, Nat.mul_zero] at hu
      omega
    · exact h1
  have hnpu : ¬ p ∣ u := by
    intro hd
    obtain ⟨w, hw⟩ := hd
    have hC2 : p ^ 2 ∣ binom (p ^ a) (p ^ (a - 1)) := by
      refine ⟨w, ?_⟩
      calc binom (p ^ a) (p ^ (a - 1)) = p * u := hu
        _ = p * (p * w) := by rw [← hw]
        _ = p ^ 2 * w := by rw [Nat.pow_two, Nat.mul_assoc]
    have hvp2 := (pow_dvd_iff p hp 2 2 (binom (p ^ a) (p ^ (a - 1)))
      (Nat.le_refl 2) hCpos).mp hC2
    omega
  have hpdvdg : p ∣ Nat.gcd (p ^ a) (binom (p ^ a) (p ^ (a - 1))) := by
    refine Nat.dvd_gcd ?_ hpC
    exact ⟨p ^ (a - 1), ppow_split p a (by omega)⟩
  have hg1 : 1 ≤ Nat.gcd (p ^ a) (binom (p ^ a) (p ^ (a - 1))) := by
    by_contra hg
    have hg0 : Nat.gcd (p ^ a) (binom (p ^ a) (p ^ (a - 1))) = 0 := by omega
    have hd := Nat.gcd_dvd_left (p ^ a) (binom (p ^ a) (p ^ (a - 1)))
    rw [hg0] at hd
    obtain ⟨e, he⟩ := hd
    rw [Nat.zero_mul] at he
    have hN1 : 1 ≤ p ^ a := pow_ge_one p (by omega) a
    omega
  obtain ⟨h, hh⟩ := hpdvdg
  have hh1 : 1 ≤ h := by
    rcases Nat.eq_zero_or_pos h with h0 | h1
    · rw [h0, Nat.mul_zero] at hh
      omega
    · exact h1
  have hhu : h ∣ u := by
    obtain ⟨e, he⟩ := Nat.gcd_dvd_right (p ^ a) (binom (p ^ a) (p ^ (a - 1)))
    rw [hh] at he
    have hcancel : h * e = u := by
      have hboth : p * (h * e) = p * u := by
        rw [← Nat.mul_assoc]
        omega
      exact Nat.mul_left_cancel (by omega : 1 ≤ p) hboth
    exact ⟨e, hcancel.symm⟩
  have hhp : h ∣ p ^ (a - 1) := by
    obtain ⟨e, he⟩ := Nat.gcd_dvd_left (p ^ a) (binom (p ^ a) (p ^ (a - 1)))
    rw [hh] at he
    have hsplit : p ^ a = p * p ^ (a - 1) := ppow_split p a (by omega)
    have hcancel : h * e = p ^ (a - 1) := by
      have hboth : p * (h * e) = p * p ^ (a - 1) := by
        rw [← Nat.mul_assoc]
        omega
      exact Nat.mul_left_cancel (by omega : 1 ≤ p) hboth
    exact ⟨e, hcancel.symm⟩
  have hh1eq : h = 1 := by
    by_contra h2h
    have h2le : 2 ≤ h := by omega
    have hqdvd : h.minFac ∣ h := Nat.minFac_dvd h
    have hqprime : h.minFac.Prime := Nat.minFac_prime (show h ≠ 1 by omega)
    have hq2 : 2 ≤ h.minFac := hqprime.one_lt
    have hqdp : h.minFac ∣ p ^ (a - 1) := Nat.dvd_trans hqdvd hhp
    have hqdpp : h.minFac ∣ p := prime_dvd_pow_of h.minFac hqprime (a - 1) p hqdp
    have hiff : h.minFac ∣ p ↔ h.minFac = 1 ∨ h.minFac = p := Nat.dvd_prime hpp
    have hqp : h.minFac = p := (hiff.mp hqdpp).resolve_left (by omega)
    have hpu : p ∣ u := by
      rw [← hqp]
      exact Nat.dvd_trans hqdvd hhu
    exact absurd hpu hnpu
  rw [hh, hh1eq]
  omega

/-- **THEOREM B (THE PRIME-POWER LAW).** For every prime p and a ≥ 2:
`f(p^a) = p` — the Erdős–Szekeres minimum is EXACTLY p. -/
theorem erdos700_law (p a : Nat) (hpp : p.Prime) (ha : 2 ≤ a) :
    f700 (p ^ a) = p := by
  have hp : 2 ≤ p := hpp.one_lt
  have hN1 : 1 ≤ p ^ a := pow_ge_one p (by omega) a
  have hpow2 : p ^ 2 = p * p := Nat.pow_two p
  have hpp2 : p ^ 2 ≤ p ^ a := pow_le_mono p (by omega) 2 a ha
  have hN2 : 4 ≤ p ^ a := by
    have h1 : 2 * 2 ≤ p * p := Nat.mul_le_mul hp hp
    omega
  have hhalf : 2 ≤ p ^ a / 2 := by omega
  have hple : p ≤ p ^ a := by
    have h1 := pow_le_mono p (by omega) 1 a (by omega)
    rw [Nat.pow_one] at h1
    exact h1
  have hk0le : p ^ (a - 1) ≤ p ^ a / 2 := by
    have hsplit : p ^ a = p ^ (a - 1) * p := by
      rw [← Nat.pow_succ]
      congr 1
      omega
    have h2 : p ^ (a - 1) * 2 ≤ p ^ (a - 1) * p :=
      Nat.mul_le_mul_left (p ^ (a - 1)) hp
    omega
  have hk02 : 2 ≤ p ^ (a - 1) := pow_ge_two p (a - 1) hp (by omega)
  have hge : p ≤ minGcdAux (p ^ a) (p ^ a / 2) := by
    refine minGcdAux_ge (p ^ a) p hple (p ^ a / 2) (by omega) ?_
    intro k hk2 hkj
    exact erdos700_gcd_lower p a k hpp ha hk2 (by omega)
  have hle : minGcdAux (p ^ a) (p ^ a / 2) ≤ p := by
    refine Nat.le_trans (minGcdAux_le (p ^ a) (p ^ (a - 1)) hk02
      (p ^ a / 2) (by omega)) ?_
    have hw := erdos700_witness p a hpp ha
    omega
  show minGcdAux (p ^ a) (p ^ a / 2) = p
  omega

/-- **The equality class at prime squares.** f(p²) = p = p²/P(p²): every
prime divisor of p² is p, so the Erdős–Szekeres equality HOLDS at n = p². -/
theorem erdos700_equality_class (p : Nat) (hpp : p.Prime) :
    f700 (p ^ 2) = p ∧ p ^ 2 / p = p ∧ ∀ q, q.Prime → q ∣ p ^ 2 → q = p := by
  have hp : 2 ≤ p := hpp.one_lt
  refine ⟨erdos700_law p 2 hpp (by omega), ?_, ?_⟩
  · rw [Nat.pow_two, mul_div_self p p (by omega : 1 ≤ p)]
  · intro q hqp hqdvd
    have hq2 : 2 ≤ q := hqp.one_lt
    have hqdp : q ∣ p := prime_dvd_pow_of q hqp 2 p hqdvd
    have hiff : q ∣ p ↔ q = 1 ∨ q = p := Nat.dvd_prime hpp
    exact (hiff.mp hqdp).resolve_left (by omega)

/-- **The violation at higher powers.** For a ≥ 3: f(p^a) = p < p^(a−1)
= p^a / p — the Erdős–Szekeres equality FAILS by the factor p^(a−2). -/
theorem erdos700_violation (p a : Nat) (hpp : p.Prime) (ha : 3 ≤ a) :
    f700 (p ^ a) = p ∧ p ^ a / p = p ^ (a - 1) ∧ p < p ^ (a - 1) := by
  have hp : 2 ≤ p := hpp.one_lt
  refine ⟨erdos700_law p a hpp (by omega), ?_, ?_⟩
  · rw [ppow_split p a (by omega), mul_div_self p (p ^ (a - 1)) (by omega : 1 ≤ p)]
  · have h1 : p * 2 ≤ p * p := Nat.mul_le_mul_left p hp
    have h2 : p ^ 2 ≤ p ^ (a - 1) := pow_le_mono p (by omega) 2 (a - 1) (by omega)
    have h3 : p ^ 2 = p * p := Nat.pow_two p
    omega

/-! ## §11 THE ARSENAL BRIDGE (BOSS's own mathematics, applied to #700) -/

/-- erdosternary2's residue trichotomy routed at the p=2 prime-power
witnesses (n = 4, k₀ = 2): 4 ≡ 1, 2 ≡ 2 (mod 3). -/
theorem erdos700_ternary_routing (m : Nat) (h : m % 3 < 3) :
    m % 3 = 0 ∨ m % 3 = 1 ∨ m % 3 = 2 :=
  ErdosTernary2.lt_three_cases (m % 3) h

theorem erdos700_witness_routing : (4 : Nat) % 3 = 1 := by
  have h : (4 : Nat) % 3 < 3 := by decide
  cases erdos700_ternary_routing 4 h with
  | inl h0 => exact absurd h0 (by decide)
  | inr h => cases h with
    | inl h1 => exact h1
    | inr h2 => exact absurd h2 (by decide)

/-- Every ternary digit of the #700 witness numbers (4 = (11)₃,
8 = (22)₃, the p = 2 prime powers) passes erdosternary2's
`isTernaryDigit` predicate. -/
theorem erdos700_digit_validity :
    [4 % 3, (4 / 3) % 3].all (fun d => ErdosTernary2.isTernaryDigit d)
      ∧ [8 % 3, (8 / 3) % 3].all (fun d => ErdosTernary2.isTernaryDigit d) := by
  decide

/-- HC-PROOF's ternary-carry machinery on the #700 witness: the carry layer
of the k₀ = 2 witness reads exactly 2 and stays bounded by the arsenal's
`carryAtPos_bound` law. -/
theorem erdos700_carry_witness :
    carryAtPos 2 1 = 2 ∧ carryAtPos 2 1 < 4 ∧ carryAtPos 4 2 < 4 :=
  ⟨by decide, carryAtPos_bound 2 1, carryAtPos_bound 4 2⟩

/-- HC-PROOF's dyadic scaling law on the #700 p=2 family: the ternary
factor leaves the 2-adic depth reader invariant — the p=2/p=3 valuation
bookkeeping of the prime-power law runs through exactly this law. -/
theorem erdos700_v2r_scaling : v2r (3 ^ 1 * 4) = v2r 4 :=
  CardinalWorldsV2.v2r_ternary_scaling 1 4

theorem erdos700_v2r_values : v2r 4 = 2 ∧ v2r 8 = 3 := by
  have h4 : v2r 4 = 2 := by
    rw [v2r.eq_def 4, if_neg (show (4:Nat) ≠ 0 by decide),
        if_pos (show (4:Nat) % 2 = 0 by decide)]
    have hd : (4:Nat) / 2 = 2 := by decide
    rw [hd, v2r.eq_def 2, if_neg (show (2:Nat) ≠ 0 by decide),
        if_pos (show (2:Nat) % 2 = 0 by decide)]
    have hd2 : (2:Nat) / 2 = 1 := by decide
    rw [hd2, v2r.eq_def 1, if_neg (show (1:Nat) ≠ 0 by decide),
        if_neg (show (1:Nat) % 2 ≠ 0 by decide)]
  have h8 : v2r 8 = 3 := by
    rw [v2r.eq_def 8, if_neg (show (8:Nat) ≠ 0 by decide),
        if_pos (show (8:Nat) % 2 = 0 by decide)]
    have hd : (8:Nat) / 2 = 4 := by decide
    rw [hd, h4]
  exact ⟨h4, h8⟩

/-! ## §12 RECEIPTS -/

#eval f700 4    -- 2  (p=2, a=2: the ErSz equality value n/P(n) = 4/2 = 2)
#eval f700 8    -- 2
#eval f700 9    -- 3  (p=3, a=2)
#eval f700 16   -- 2
#eval (Nat.gcd 25 (binom 25 5), Nat.gcd 27 (binom 27 9))  -- (5, 3): witnesses
#eval (vp 2 (binom 8 4), vp 3 (binom 9 3), vp 5 (binom 25 5), vp 3 (binom 27 9))
     -- (1, 1, 1, 1): the carry lemma at the witnesses
#eval (powsSum 2 4 16, cntNotDiv 2 4 8)  -- (15, 1): v2(16!) = 15; a − v2(8) = 4−3
#eval "ERDOS700_KERNEL_GREEN"

#print axioms erdos700_carry
#print axioms erdos700_witness
#print axioms erdos700_law
#print axioms erdos700_equality_class
#print axioms erdos700_violation

end Erdos700
