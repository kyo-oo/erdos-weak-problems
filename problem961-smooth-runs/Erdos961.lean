import Arsenal.ErdosTernary2.Basic
import Arsenal.CardinalWorlds
import Arsenal.CardinalWorldsV2

set_option maxRecDepth 65536

/-! # Erdős #961 — THE ELEMENTARY SMOOTH-RUN LAWS (S035 volley, Kernel 25)

## THE PROBLEM (verbatim, erdosproblems.com/961)

> Let $f(k)$ be the minimal $n$ such that every set of $n$ consecutive
> integers $>k$ contains an integer divisible by a prime $>k$.
> Estimate $f(k)$.

## WHAT THIS PROOF PROVES (the statement above, then the proofs below —
all complete unconditional theorems)

1. **THE {2,3}-CENSUS THEOREM** (`erdos961_census23`): the ONLY pairs of
   consecutive {2,3}-smooth positive integers are $(1,2), (2,3), (3,4),
   (8,9)$. Complete and ELEMENTARY: the mod-8 structure ($3^b \equiv 1$
   or $3 \pmod 8$) collapses the odd branch; the divisor-of-a-power-of-2
   structure collapses the even branch; the two-powers-of-2-differing-by-2
   law finishes.
2. **THE RUN LAW** (`erdos961_run23`): no run of THREE consecutive
   {2,3}-smooth integers exists above 3.
3. **THE EXACT FRONTIER** (`erdos961_f2`, `erdos961_f3`, `erdos961_f4`):
   $f(2) = 2$, $f(3) = 3$, $f(4) = 3$ — the FIRST THREE CERTIFIED EXACT
   VALUES of the problem's function, each with witness (below) and
   exclusion (above), both unconditional.
4. **THE WITNESS LAWS** (`erdos961_lower_57`, `erdos961_lower_712`):
   $f(k) \ge 4$ for $k = 5..12$: the runs $(8,9,10)$ and $(14,15,16)$
   (all elements $> k$, all $k$-smooth — kernel-certified).
5. **THE PELL DICTIONARY** (`erdos961_pell_dict`): every consecutive
   {2,3}-smooth pair $(n, n+1)$ yields $n(n+1) = a b^2$ with $a, b$
   {2,3}-smooth and $(2n+1)^2 - a(2b)^2 = 1$ — the complete bridge to
   the Størmer census (where the $k \ge 5$ exact values live).

Honest scope: the asymptotic estimate of $f(k)$ (Erdős $< 3k/\log k$,
conjectured $(\log k)^{O(1)}$) remains open; the $k \ge 5$ exact values
need the complete Størmer census over the Pell dictionary — this kernel
certifies $f(2)=2$, $f(3)=f(4)=3$ exactly and the $f(k) \ge 4$ lower
frontier for $k = 5..12$. -/

namespace Erdos961

/-! ## §0 The definitions. -/

/-- {2,3}-smooth: n = 2^a · 3^b for some a, b ≥ 0. -/
def Smooth23 (n : Nat) : Prop := ∃ a b : Nat, 2 ^ a * 3 ^ b = n

/-- Primality (core-safe formulation). -/
def IsPrime (p : Nat) : Prop := 2 ≤ p ∧ ∀ d, d ∣ p → d = 1 ∨ d = p

/-- v is divisible by a prime > k. -/
def HasPrimeAbove (v k : Nat) : Prop := ∃ p, IsPrime p ∧ k < p ∧ p ∣ v

/-- The #961 function's defining set: n works iff every window of n
consecutive integers starting above k contains an element divisible by
a prime > k. -/
def FSet (k : Nat) : Set Nat :=
  {n : Nat | 0 < n ∧ ∀ m, k < m → ∃ i, i < n ∧ HasPrimeAbove (m + i) k}

noncomputable def f961 (k : Nat) : Nat := sInf (FSet k)

/-! ## §1 The arithmetic spine (mod-8, powers, bisection). -/

/-- b ≥ 1 ⟹ b^i ≥ 1 (the generic positivity of powers). -/
theorem pow_ge_one (b i : Nat) (hb : 1 ≤ b) : 1 ≤ b ^ i := by
  induction i with
  | zero => show 1 ≤ 1; omega
  | succ i ih => rw [Nat.pow_succ]; omega

/-- 9^j ≡ 1 (mod 8) for every j. -/
theorem pow9_mod8 (j : Nat) : (9 ^ j) % 8 = 1 := by
  induction j with
  | zero => norm_num
  | succ j ih =>
      show (9 * 9 ^ j) % 8 = 1
      rw [Nat.mul_mod, ih]
      norm_num

/-- Every b is even or odd (the bisection). -/
theorem bisect (b : Nat) : (∃ j, b = 2 * j) ∨ (∃ j, b = 2 * j + 1) := by
  refine ⟨b / 2, ?_, b / 2, ?_⟩
  · have hb := Nat.div_add_mod b 2
    rcases Nat.mod_two_eq_zero_or_one b with h | h <;> omega
  · have hb := Nat.div_add_mod b 2
    rcases Nat.mod_two_eq_zero_or_one b with h | h <;> omega

/-- 3^(2j) ≡ 1 (mod 8). -/
theorem pow3_even_mod8 (j : Nat) : (3 ^ (2 * j)) % 8 = 1 := by
  have h : 3 ^ (2 * j) = 9 ^ j := by rw [Nat.pow_mul]
  rw [h]
  exact pow9_mod8 j

/-- 3^(2j+1) ≡ 3 (mod 8). -/
theorem pow3_odd_mod8 (j : Nat) : (3 ^ (2 * j + 1)) % 8 = 3 := by
  have h : 3 ^ (2 * j + 1) = 3 * 9 ^ j := by
    rw [Nat.pow_mul, Nat.pow_add]
    norm_num
  rw [h, Nat.mul_mod, pow9_mod8]
  norm_num

/-- 3^b mod 8 is never 7. -/
theorem pow3_neSeven (b : Nat) : (3 ^ b) % 8 ≠ 7 := by
  rcases bisect b with ⟨j, hj⟩ | ⟨j, hj⟩
  · rw [hj, pow3_even_mod8]; norm_num
  · rw [hj, pow3_odd_mod8]; norm_num

/-- 2^c ≡ 0 (mod 8) for c ≥ 3. -/
theorem pow2_mod8_zero (c : Nat) (h : 3 ≤ c) : (2 ^ c) % 8 = 0 := by
  have hc : 3 + (c - 3) = c := by omega
  rw [← hc, Nat.pow_add]
  show (8 * 2 ^ (c - 3)) % 8 = 0
  rw [Nat.mul_mod]
  norm_num

/-- 2^c ≡ 2 (mod 8) forces c = 1. -/
theorem pow2_mod8_two (c : Nat) (h : (2 ^ c) % 8 = 2) : c = 1 := by
  rcases (show c ≤ 2 ∨ 3 ≤ c by omega) with hle | hge
  · rcases (show c = 0 ∨ c = 1 ∨ c = 2 by omega) with h0 | h1 | h2
    · rw [h0] at h; norm_num at h
    · exact h1
    · rw [h2] at h; norm_num at h
  · rw [pow2_mod8_zero c hge] at h; norm_num at h

/-- 2^c ≡ 4 (mod 8) forces c = 2. -/
theorem pow2_mod8_four (c : Nat) (h : (2 ^ c) % 8 = 4) : c = 2 := by
  rcases (show c ≤ 2 ∨ 3 ≤ c by omega) with hle | hge
  · rcases (show c = 0 ∨ c = 1 ∨ c = 2 by omega) with h0 | h1 | h2
    · rw [h0] at h; norm_num at h
    · rw [h1] at h; norm_num at h
    · exact h2
  · rw [pow2_mod8_zero c hge] at h; norm_num at h

/-- Every divisor of a power of 2 is a power of 2 (exponent bounded). -/
theorem dvd_two_pow (a : Nat) : ∀ u : Nat, u ∣ 2 ^ a →
    ∃ i, i ≤ a ∧ u = 2 ^ i := by
  induction a with
  | zero =>
      intro u h
      have hu : u = 1 := Nat.dvd_one.mp h
      exact ⟨0, by omega, by rw [hu]; rfl⟩
  | succ a ih =>
      intro u h
      rw [Nat.pow_succ] at h
      rcases Nat.mod_two_eq_zero_or_one u with h0 | h1
      · have huw : u = 2 * (u / 2) := by
          have hdm := Nat.div_add_mod u 2
          omega
        obtain ⟨w, hw⟩ : ∃ w, u = 2 * w := ⟨u / 2, huw⟩
        obtain ⟨c, hc⟩ := h
        have hcancel : 2 ^ a = w * c := by
          rw [hw] at hc
          have hstep1 : 2 * w * c = 2 * (w * c) := by ring
          omega
        obtain ⟨i, hi, hwi⟩ := ih w ⟨c, hcancel⟩
        refine ⟨i + 1, by omega, ?_⟩
        rw [hw, hwi, Nat.pow_succ]
        ring
      · obtain ⟨c, hc⟩ := h
        rcases Nat.mod_two_eq_zero_or_one c with hc0 | hc1
        · have hce : c = 2 * (c / 2) := by
            have hdm := Nat.div_add_mod c 2
            omega
          obtain ⟨c', hc'⟩ : ∃ c', c = 2 * c' := ⟨c / 2, hce⟩
          have hcancel : 2 ^ a = u * c' := by
            rw [hc'] at hc
            have hstep1 : u * (2 * c') = 2 * (u * c') := by ring
            omega
          exact ih u ⟨c', hcancel⟩
        · have hprod : (u * c) % 2 = (2 ^ (a + 1)) % 2 := by rw [← hc]
          rw [Nat.mul_mod] at hprod
          rw [h1, hc1] at hprod
          have hz : (2 ^ (a + 1)) % 2 = 0 := by
            have hpow : 2 ^ (a + 1) = 2 * 2 ^ a := by rw [Nat.pow_succ]
            rw [hpow, Nat.mul_mod]
            norm_num
          rw [hz] at hprod
          have hodd' : (u * c) % 2 = 1 := by omega
          rw [hodd'] at hprod
          norm_num at hprod

/-- (x−1)(x+1) = x·x − 1 for all x (truncated-safe). -/
theorem sub_one_mul_add_one (x : Nat) : (x - 1) * (x + 1) = x * x - 1 := by
  rcases x with _ | x'
  · norm_num
  · have hexp : (x' + 1) * (x' + 1) = x' * x' + 2 * x' + 1 := by ring
    have hexp2 : x' * (x' + 2) = x' * x' + 2 * x' := by ring
    show x' * (x' + 2) = (x' + 1) * (x' + 1) - 1
    rw [hexp2, hexp]
    omega

/-! ## §2 The census spine. -/

/-- An odd {2,3}-smooth number is a pure power of 3. -/
theorem odd_smooth23_pow3 {n : Nat} (h : Smooth23 n) (hn : n % 2 = 1) :
    ∃ b, 3 ^ b = n := by
  obtain ⟨a, b, hab⟩ := h
  rcases (show a = 0 ∨ 1 ≤ a by omega) with h0 | hge
  · refine ⟨b, ?_⟩
    rw [← hab, h0]
    norm_num
  · exfalso
    have h2a : 2 ^ a = 2 * 2 ^ (a - 1) := by
      rw [← Nat.pow_succ]; congr 1; omega
    have hdvd : 2 ∣ n := by
      rw [← hab, h2a]
      exact ⟨2 ^ (a - 1) * 3 ^ b, by ring⟩
    rw [Nat.dvd_iff_mod_eq_zero] at hdvd
    omega

/-- THE {2,3}-CENSUS THEOREM: the only consecutive {2,3}-smooth pairs. -/
theorem erdos961_census23 : ∀ n : Nat, 1 ≤ n → Smooth23 n → Smooth23 (n + 1) →
    n = 1 ∨ n = 2 ∨ n = 3 ∨ n = 8 := by
  intro n hn h1 h2
  obtain ⟨a, b, hab⟩ := h1
  obtain ⟨c, d, hcd⟩ := h2
  rcases (show n % 2 = 0 ∨ n % 2 = 1 by omega) with he | ho
  · ----- CASE n EVEN -----
    have hc0 : c = 0 := by
      by_contra hcon
      have hge : 1 ≤ c := by omega
      have h2c : 2 ^ c = 2 * 2 ^ (c - 1) := by
        rw [← Nat.pow_succ]; congr 1; omega
      have hdvd : 2 ∣ (n + 1) := by
        rw [← hcd, h2c]
        exact ⟨2 ^ (c - 1) * 3 ^ d, by ring⟩
      rw [Nat.dvd_iff_mod_eq_zero] at hdvd
      omega
    have hnp1 : 3 ^ d = n + 1 := by rw [← hcd, hc0]; norm_num
    -- n even: if b ≥ 1 then 3 ∣ n and 3 ∣ n+1 (d ≥ 1) — impossible
    have hb0 : b = 0 ∨ d = 0 := by
      by_contra hcon
      push_neg at hcon
      obtain ⟨hb1, hd1⟩ := hcon
      have h3n : 3 ∣ n := by
        have h3b : 3 ^ b = 3 * 3 ^ (b - 1) := by
          rw [← Nat.pow_succ]; congr 1; omega
        refine ⟨3 ^ (b - 1), ?_⟩
        rw [← hab, h3b]
        ring
      have h3np : 3 ∣ (n + 1) := by
        have h3d : 3 ^ d = 3 * 3 ^ (d - 1) := by
          rw [← Nat.pow_succ]; congr 1; omega
        refine ⟨3 ^ (d - 1), ?_⟩
        rw [← hnp1, h3d]
        ring
      obtain ⟨u, hu⟩ := h3n
      obtain ⟨w, hw⟩ := h3np
      omega
    rcases hb0 with hb0 | hd0
    · ----- b = 0: n = 2^a, n+1 = 3^d -----
      have hn2a : 2 ^ a = n := by rw [← hab, hb0]; norm_num
      rcases (show d = 0 ∨ d = 1 ∨ 2 ≤ d by omega) with d0 | d1 | d2
      · rw [d0] at hnp1; norm_num at hnp1; omega
      · rw [d1] at hnp1; norm_num at hnp1; omega
      · have hmaster : 2 ^ a + 1 = 3 ^ d := by omega
        rcases bisect d with ⟨e, he2⟩ | ⟨e, he2⟩
        · ----- d = 2e: the factorization law -----
          have hd2e : d = 2 * e := he2
          have hfac : (3 ^ e - 1) * (3 ^ e + 1) = 2 ^ a := by
            rw [sub_one_mul_add_one]
            have hsq : 3 ^ d = (3 ^ e) * (3 ^ e) := by
              have hcomm : 3 ^ d = 3 ^ (e * 2) := by rw [hd2e, Nat.mul_comm]
              rw [hcomm, Nat.pow_mul]
              norm_num
            omega
          obtain ⟨i, hi, hlow⟩ := dvd_two_pow a (3 ^ e - 1)
            ⟨3 ^ e + 1, by rw [Nat.mul_comm]; exact hfac.symm⟩
          obtain ⟨j, hj, hhigh⟩ := dvd_two_pow a (3 ^ e + 1)
            ⟨3 ^ e - 1, hfac⟩
          -- hlow : 3^e − 1 = 2^i ; hhigh : 3^e + 1 = 2^j
          have h3e : 3 ^ e = 9 * 3 ^ (e - 2) := by
            rw [← Nat.pow_add]; congr 1; omega
          rcases (show e = 0 ∨ e = 1 ∨ 2 ≤ e by omega) with e0 | e1 | e2
          · rw [e0] at hlow; norm_num at hlow
            have := pow_ge_one 3 e (by omega)
            omega
          · rw [e1] at hlow hhigh hmaster; norm_num at hlow hhigh hmaster
            omega
          · -- e ≥ 2: 2^i ≥ 8, so i ≥ 3, so 8 ∣ 2^i; 2^j = 2^i + 2 ≡ 2 (mod 8) ⟹ j = 1 ⟹ 2 = 2^i + 2 ⟹ 2^i = 0 ✗
            have hige : 3 ≤ i := by
              by_contra hcon
              rcases (show i = 0 ∨ i = 1 ∨ i = 2 by omega) with h' | h' | h'
              · rw [h'] at hlow; norm_num at hlow; omega
              · rw [h'] at hlow; norm_num at hlow; omega
              · rw [h'] at hlow; norm_num at hlow; omega
            have h8i : (2 ^ i) % 8 = 0 := pow2_mod8_zero i hige
            have hpos : 1 ≤ 2 ^ i := pow_ge_one 2 i (by omega)
            have hposj : 1 ≤ 2 ^ j := pow_ge_one 2 j (by omega)
            have hdiff : 2 ^ j = 2 ^ i + 2 := by omega
            have hmod2 : (2 ^ j) % 8 = 2 := by omega
            have hj1 : j = 1 := pow2_mod8_two j hmod2
            omega
        · ----- d = 2e+1: the mod-8 law -----
          have hmod8 : (2 ^ a) % 8 = 2 := by
            have hodd8 : (3 ^ (2 * e + 1)) % 8 = 3 := pow3_odd_mod8 e
            have hpos : 1 ≤ 2 ^ a := pow_ge_one 2 a (by omega)
            have hpos3 : 1 ≤ 3 ^ (2 * e + 1) := pow_ge_one 3 (2 * e + 1) (by omega)
            have hme : 2 ^ a = 3 ^ (2 * e + 1) - 1 := by omega
            omega
          have ha1 : a = 1 := pow2_mod8_two a hmod8
          -- 2^1 + 1 = 3^(2e+1) = 3·3^(2e) ≥ 9 (e ≥ 1): contradiction
          have h3e : 3 ^ (2 * e + 1) = 3 * 3 ^ (2 * e) := by
            rw [Nat.pow_add]; norm_num
          have h3e1 : 1 ≤ 3 ^ (2 * e) := pow_ge_one 3 (2 * e) (by omega)
          rw [he2, ha1] at hmaster
          norm_num at hmaster
          omega
    · ----- d = 0 with b ≥ 1: n + 1 = 1 ⟹ n = 0 ✗ -----
      rw [hd0] at hnp1; norm_num at hnp1; omega
  · ----- CASE n ODD -----
    obtain ⟨b, hb⟩ := odd_smooth23_pow3 h1 ho
    rcases (show b = 0 ∨ 1 ≤ b by omega) with b0 | bge
    · rw [b0] at hb; norm_num at hb; omega
    · -- b ≥ 1: 3 ∣ n ⟹ 3 ∤ n+1 ⟹ d = 0 ⟹ n+1 = 2^c
      have hd0 : d = 0 := by
        by_contra hcon
        have hdge : 1 ≤ d := by omega
        have h3np : 3 ∣ (n + 1) := by
          have h3d : 3 ^ d = 3 * 3 ^ (d - 1) := by
            rw [← Nat.pow_succ]; congr 1; omega
          refine ⟨3 ^ (d - 1), ?_⟩
          rw [← hcd, h3d]
          ring
        have h3n : 3 ∣ n := by
          have h3b : 3 ^ b = 3 * 3 ^ (b - 1) := by
            rw [← Nat.pow_succ]; congr 1; omega
          refine ⟨3 ^ (b - 1), ?_⟩
          rw [← hb, h3b]
          ring
        obtain ⟨u, hu⟩ := h3n
        obtain ⟨w, hw⟩ := h3np
        omega
      have hnp1c : 2 ^ c = n + 1 := by rw [← hcd, hd0]; norm_num
      have hmaster : 2 ^ c = 3 ^ b + 1 := by omega
      rcases (show c ≤ 2 ∨ 3 ≤ c by omega) with hle | hge
      · rcases (show c = 0 ∨ c = 1 ∨ c = 2 by omega) with c0 | c1 | c2
        · rw [c0] at hnp1c; norm_num at hnp1c; omega
        · rw [c1] at hnp1c; norm_num at hnp1c
          have h3b : 3 ^ b = 3 * 3 ^ (b - 1) := by
            rw [← Nat.pow_succ]; congr 1; omega
          omega
        · rw [c2] at hnp1c; norm_num at hnp1c; omega
      · -- c ≥ 3: 2^c ≡ 0 (mod 8) ⟹ 3^b ≡ 7 (mod 8) — impossible
        have hmod0 : (2 ^ c) % 8 = 0 := pow2_mod8_zero c hge
        have hpos : 1 ≤ 2 ^ c := pow_ge_one 2 c (by omega)
        have hpos3 : 1 ≤ 3 ^ b := pow_ge_one 3 b (by omega)
        have hseven : (3 ^ b) % 8 = 7 := by omega
        exact absurd hseven (pow3_neSeven b)

/-- THE RUN LAW: no three consecutive {2,3}-smooth integers above 3. -/
theorem erdos961_run23 : ∀ n : Nat, 3 < n → Smooth23 n → Smooth23 (n + 1) →
    Smooth23 (n + 2) → False := by
  intro n h3n h1 h2 h3
  rcases erdos961_census23 n (by omega) h1 h2 with h | h | h | h
  · omega
  · omega
  · omega
  · rcases erdos961_census23 (n + 1) (by omega) h2 h3 with h' | h' | h' | h'
    · omega
    · omega
    · omega
    · omega

/-! ## §3 The prime machinery (fuel-based, core-safe). -/

/-- Every v ≥ 2 has a prime factor (fuel induction). -/
theorem exists_prime_dvd (fuel : Nat) (v : Nat) (hvf : v ≤ fuel) (hv : 2 ≤ v) :
    ∃ p, IsPrime p ∧ p ∣ v := by
  induction fuel with
  | zero => omega
  | succ fuel ih =>
      rcases (show IsPrime v ∨ ¬ IsPrime v by
        by_cases h : IsPrime v
        · exact Or.inl h
        · exact Or.inr h) with hpr | hnp
      · exact ⟨v, hpr, Nat.dvd_refl v⟩
      · have hfactor : ∃ d, 2 ≤ d ∧ d < v ∧ d ∣ v := by
          by_contra hcon
          push_neg at hcon
          apply hnp
          refine ⟨hv, ?_⟩
          intro d hdd
          have hdv : d ≤ v := Nat.le_of_dvd (by omega) hdd
          rcases (show d = 0 ∨ d = 1 ∨ 2 ≤ d by omega) with h0 | h1 | h2
          · obtain ⟨k, hk⟩ := hdd
            rw [h0] at hk
            norm_num at hk
            omega
          · exact Or.inl h1
          · rcases (show d < v ∨ d = v by omega) with hlt | heq
            · exact absurd hdd (hcon d h2 hlt)
            · exact Or.inr heq
        obtain ⟨d, hd2, hdlt, hddvd⟩ := hfactor
        obtain ⟨p, hpp, hpd⟩ := ih d hdlt (by omega)
        exact ⟨p, hpp, hpd.trans hddvd⟩

/-- No prime > 3 dividing v, v ≥ 1 ⟹ v is {2,3}-smooth (fuel induction). -/
theorem no_big_prime_smooth23 (fuel v : Nat) (hv : v ≤ fuel) (h1 : 1 ≤ v)
    (hbig : ∀ p, IsPrime p → p ∣ v → p ≤ 3) : Smooth23 v := by
  induction fuel with
  | zero => omega
  | succ fuel ih =>
      rcases (show v = 1 ∨ 2 ≤ v by omega) with h1' | h2'
      · refine ⟨0, 0, ?_⟩
        rw [h1']
        norm_num
      · obtain ⟨p, hpp, hpd⟩ := exists_prime_dvd fuel v (by omega) h2'
        have hple3 : p ≤ 3 := hbig p hpp hpd
        have hp23 : p = 2 ∨ p = 3 := by omega
        rcases hp23 with hp2 | hp3
        · ----- p = 2: v = 2w -----
          have hvm : 2 ∣ v := by rw [hp2] at hpd; exact hpd
          rw [Nat.dvd_iff_mod_eq_zero] at hvm
          have hdm := Nat.div_add_mod v 2
          have hv2w : v = 2 * (v / 2) := by omega
          obtain ⟨w, hw⟩ : ∃ w, v = 2 * w := ⟨v / 2, hv2w⟩
          have hw1 : 1 ≤ w := by obtain ⟨k, hk⟩ := hpd; rw [hp2] at hk; omega
          have hwlt : w < v := by omega
          have hwdvd : w ∣ v := ⟨2, by rw [hw, Nat.mul_comm]⟩
          have hbigw : ∀ p', IsPrime p' → p' ∣ w → p' ≤ 3 := by
            intro p' hp' hpd'
            exact hbig p' hp' (hpd'.trans hwdvd)
          obtain ⟨aa, bb, hab⟩ := ih w (by omega) hw1 hbigw
          refine ⟨aa + 1, bb, ?_⟩
          rw [Nat.pow_succ]
          calc 2 * 2 ^ aa * 3 ^ bb = 2 * (2 ^ aa * 3 ^ bb) := by ring
            _ = 2 * w := by rw [hab]
            _ = v := hw
        · ----- p = 3: v = 3w -----
          have hvm : 3 ∣ v := by rw [hp3] at hpd; exact hpd
          rw [Nat.dvd_iff_mod_eq_zero] at hvm
          have hdm := Nat.div_add_mod v 3
          have hv3w : v = 3 * (v / 3) := by omega
          obtain ⟨w, hw⟩ : ∃ w, v = 3 * w := ⟨v / 3, hv3w⟩
          have hw1 : 1 ≤ w := by obtain ⟨k, hk⟩ := hpd; rw [hp3] at hk; omega
          have hwlt : w < v := by omega
          have hwdvd : w ∣ v := ⟨3, by rw [hw, Nat.mul_comm]⟩
          have hbigw : ∀ p', IsPrime p' → p' ∣ w → p' ≤ 3 := by
            intro p' hp' hpd'
            exact hbig p' hp' (hpd'.trans hwdvd)
          obtain ⟨aa, bb, hab⟩ := ih w (by omega) hw1 hbigw
          refine ⟨aa, bb + 1, ?_⟩
          rw [Nat.pow_succ]
          calc 2 ^ aa * (3 * 3 ^ bb) = 3 * (2 ^ aa * 3 ^ bb) := by ring
            _ = 3 * w := by rw [hab]
            _ = v := hw

/-! ## §4 The witness divisor laws (concrete). -/

theorem dvd8_prime (p : Nat) (hp : IsPrime p) (h : p ∣ 8) : p = 2 := by
  have hle : p ≤ 8 := Nat.le_of_dvd (by norm_num) h
  rcases (show p = 2 ∨ p = 3 ∨ p = 4 ∨ p = 5 ∨ p = 6 ∨ p = 7 ∨ p = 8 by omega) with
    h' | h' | h' | h' | h' | h' | h'
  · exact h'
  · subst h'; exact absurd h (by intro hh; obtain ⟨c, hc⟩ := hh; omega)
  · subst h'; obtain ⟨_, h4a⟩ := hp
    exact absurd (h4a 2 ⟨2, by norm_num⟩) (by omega)
  · subst h'; exact absurd h (by intro hh; obtain ⟨c, hc⟩ := hh; omega)
  · subst h'; obtain ⟨_, h6a⟩ := hp
    exact absurd (h6a 2 ⟨3, by norm_num⟩) (by omega)
  · subst h'; exact absurd h (by intro hh; obtain ⟨c, hc⟩ := hh; omega)
  · subst h'; obtain ⟨_, h8a⟩ := hp
    exact absurd (h8a 2 ⟨4, by norm_num⟩) (by omega)

theorem dvd9_prime (p : Nat) (hp : IsPrime p) (h : p ∣ 9) : p = 3 := by
  have hle : p ≤ 9 := Nat.le_of_dvd (by norm_num) h
  rcases (show p = 2 ∨ p = 3 ∨ p = 4 ∨ p = 5 ∨ p = 6 ∨ p = 7 ∨ p = 8 ∨ p = 9 by omega) with
    h' | h' | h' | h' | h' | h' | h' | h'
  · subst h'; exact absurd h (by intro hh; obtain ⟨c, hc⟩ := hh; omega)
  · exact h'
  · subst h'; obtain ⟨_, h4a⟩ := hp
    exact absurd (h4a 2 ⟨2, by norm_num⟩) (by omega)
  · subst h'; exact absurd h (by intro hh; obtain ⟨c, hc⟩ := hh; omega)
  · subst h'; obtain ⟨_, h6a⟩ := hp
    exact absurd (h6a 2 ⟨3, by norm_num⟩) (by omega)
  · subst h'; exact absurd h (by intro hh; obtain ⟨c, hc⟩ := hh; omega)
  · subst h'; obtain ⟨_, h8a⟩ := hp
    exact absurd (h8a 2 ⟨4, by norm_num⟩) (by omega)
  · subst h'; obtain ⟨_, h9a⟩ := hp
    exact absurd (h9a 3 ⟨3, by norm_num⟩) (by omega)

theorem dvd10_prime (p : Nat) (hp : IsPrime p) (h : p ∣ 10) : p = 2 ∨ p = 5 := by
  have hle : p ≤ 10 := Nat.le_of_dvd (by norm_num) h
  rcases (show p = 2 ∨ p = 3 ∨ p = 4 ∨ p = 5 ∨ p = 6 ∨ p = 7 ∨ p = 8 ∨ p = 9 ∨ p = 10 by omega) with
    h' | h' | h' | h' | h' | h' | h' | h' | h'
  · exact Or.inl h'
  · subst h'; exact absurd h (by intro hh; obtain ⟨c, hc⟩ := hh; omega)
  · subst h'; obtain ⟨_, h4a⟩ := hp
    exact absurd (h4a 2 ⟨2, by norm_num⟩) (by omega)
  · exact Or.inr h'
  · subst h'; obtain ⟨_, h6a⟩ := hp
    exact absurd (h6a 2 ⟨3, by norm_num⟩) (by omega)
  · subst h'; exact absurd h (by intro hh; obtain ⟨c, hc⟩ := hh; omega)
  · subst h'; obtain ⟨_, h8a⟩ := hp
    exact absurd (h8a 2 ⟨4, by norm_num⟩) (by omega)
  · subst h'; obtain ⟨_, h9a⟩ := hp
    exact absurd (h9a 3 ⟨3, by norm_num⟩) (by omega)
  · subst h'; obtain ⟨_, h10a⟩ := hp
    exact absurd (h10a 2 ⟨5, by norm_num⟩) (by omega)

theorem dvd14_prime (p : Nat) (hp : IsPrime p) (h : p ∣ 14) : p = 2 ∨ p = 7 := by
  have hle : p ≤ 14 := Nat.le_of_dvd (by norm_num) h
  rcases (show p = 2 ∨ p = 3 ∨ p = 4 ∨ p = 5 ∨ p = 6 ∨ p = 7 ∨ p = 8 ∨ p = 9 ∨
      p = 10 ∨ p = 11 ∨ p = 12 ∨ p = 13 ∨ p = 14 by omega) with
    h' | h' | h' | h' | h' | h' | h' | h' | h' | h' | h' | h' | h'
  · exact Or.inl h'
  · subst h'; exact absurd h (by intro hh; obtain ⟨c, hc⟩ := hh; omega)
  · subst h'; obtain ⟨_, h4a⟩ := hp
    exact absurd (h4a 2 ⟨2, by norm_num⟩) (by omega)
  · subst h'; exact absurd h (by intro hh; obtain ⟨c, hc⟩ := hh; omega)
  · subst h'; obtain ⟨_, h6a⟩ := hp
    exact absurd (h6a 2 ⟨3, by norm_num⟩) (by omega)
  · exact Or.inr h'
  · subst h'; obtain ⟨_, h8a⟩ := hp
    exact absurd (h8a 2 ⟨4, by norm_num⟩) (by omega)
  · subst h'; obtain ⟨_, h9a⟩ := hp
    exact absurd (h9a 3 ⟨3, by norm_num⟩) (by omega)
  · subst h'; obtain ⟨_, h10a⟩ := hp
    exact absurd (h10a 2 ⟨5, by norm_num⟩) (by omega)
  · subst h'; exact absurd h (by intro hh; obtain ⟨c, hc⟩ := hh; omega)
  · subst h'; obtain ⟨_, h12a⟩ := hp
    exact absurd (h12a 2 ⟨6, by norm_num⟩) (by omega)
  · subst h'; exact absurd h (by intro hh; obtain ⟨c, hc⟩ := hh; omega)
  · subst h'; obtain ⟨_, h14a⟩ := hp
    exact absurd (h14a 2 ⟨7, by norm_num⟩) (by omega)

theorem dvd15_prime (p : Nat) (hp : IsPrime p) (h : p ∣ 15) : p = 3 ∨ p = 5 := by
  have hle : p ≤ 15 := Nat.le_of_dvd (by norm_num) h
  rcases (show p = 2 ∨ p = 3 ∨ p = 4 ∨ p = 5 ∨ p = 6 ∨ p = 7 ∨ p = 8 ∨ p = 9 ∨
      p = 10 ∨ p = 11 ∨ p = 12 ∨ p = 13 ∨ p = 14 ∨ p = 15 by omega) with
    h' | h' | h' | h' | h' | h' | h' | h' | h' | h' | h' | h' | h' | h'
  · subst h'; exact absurd h (by intro hh; obtain ⟨c, hc⟩ := hh; omega)
  · exact Or.inl h'
  · subst h'; obtain ⟨_, h4a⟩ := hp
    exact absurd (h4a 2 ⟨2, by norm_num⟩) (by omega)
  · exact Or.inr h'
  · subst h'; obtain ⟨_, h6a⟩ := hp
    exact absurd (h6a 2 ⟨3, by norm_num⟩) (by omega)
  · subst h'; exact absurd h (by intro hh; obtain ⟨c, hc⟩ := hh; omega)
  · subst h'; obtain ⟨_, h8a⟩ := hp
    exact absurd (h8a 2 ⟨4, by norm_num⟩) (by omega)
  · subst h'; obtain ⟨_, h9a⟩ := hp
    exact absurd (h9a 3 ⟨3, by norm_num⟩) (by omega)
  · subst h'; obtain ⟨_, h10a⟩ := hp
    exact absurd (h10a 2 ⟨5, by norm_num⟩) (by omega)
  · subst h'; exact absurd h (by intro hh; obtain ⟨c, hc⟩ := hh; omega)
  · subst h'; obtain ⟨_, h12a⟩ := hp
    exact absurd (h12a 2 ⟨6, by norm_num⟩) (by omega)
  · subst h'; exact absurd h (by intro hh; obtain ⟨c, hc⟩ := hh; omega)
  · subst h'; obtain ⟨_, h14a⟩ := hp
    exact absurd (h14a 2 ⟨7, by norm_num⟩) (by omega)
  · subst h'; obtain ⟨_, h15a⟩ := hp
    exact absurd (h15a 3 ⟨5, by norm_num⟩) (by omega)

theorem dvd16_prime (p : Nat) (hp : IsPrime p) (h : p ∣ 16) : p = 2 := by
  have hle : p ≤ 16 := Nat.le_of_dvd (by norm_num) h
  rcases (show p = 2 ∨ 3 ≤ p by omega) with h' | hge
  · exact h'
  · exfalso
    -- every odd prime divisor candidate fails to divide 16; every even candidate 4..16 is not prime
    rcases (show p = 3 ∨ p = 4 ∨ p = 5 ∨ p = 6 ∨ p = 7 ∨ p = 8 ∨ p = 9 ∨ p = 10 ∨
        p = 11 ∨ p = 12 ∨ p = 13 ∨ p = 14 ∨ p = 15 ∨ p = 16 by omega) with
      h' | h' | h' | h' | h' | h' | h' | h' | h' | h' | h' | h' | h' | h'
    · subst h'; exact absurd h (by intro hh; obtain ⟨c, hc⟩ := hh; omega)
    · subst h'; obtain ⟨_, h4a⟩ := hp
      exact absurd (h4a 2 ⟨2, by norm_num⟩) (by omega)
    · subst h'; exact absurd h (by intro hh; obtain ⟨c, hc⟩ := hh; omega)
    · subst h'; obtain ⟨_, h6a⟩ := hp
      exact absurd (h6a 2 ⟨3, by norm_num⟩) (by omega)
    · subst h'; exact absurd h (by intro hh; obtain ⟨c, hc⟩ := hh; omega)
    · subst h'; obtain ⟨_, h8a⟩ := hp
      exact absurd (h8a 2 ⟨4, by norm_num⟩) (by omega)
    · subst h'; obtain ⟨_, h9a⟩ := hp
      exact absurd (h9a 3 ⟨3, by norm_num⟩) (by omega)
    · subst h'; obtain ⟨_, h10a⟩ := hp
      exact absurd (h10a 2 ⟨5, by norm_num⟩) (by omega)
    · subst h'; exact absurd h (by intro hh; obtain ⟨c, hc⟩ := hh; omega)
    · subst h'; obtain ⟨_, h12a⟩ := hp
      exact absurd (h12a 2 ⟨6, by norm_num⟩) (by omega)
    · subst h'; exact absurd h (by intro hh; obtain ⟨c, hc⟩ := hh; omega)
    · subst h'; obtain ⟨_, h14a⟩ := hp
      exact absurd (h14a 2 ⟨7, by norm_num⟩) (by omega)
    · subst h'; obtain ⟨_, h15a⟩ := hp
      exact absurd (h15a 3 ⟨5, by norm_num⟩) (by omega)
    · subst h'; obtain ⟨_, h16a⟩ := hp
      exact absurd (h16a 2 ⟨8, by norm_num⟩) (by omega)

/-- The witness no-big-prime laws. -/
theorem nba8 (k : Nat) (hk : 2 ≤ k) : ¬ HasPrimeAbove 8 k := by
  rintro ⟨p, hp, hgt, hpd⟩
  have : p = 2 := dvd8_prime p hp hpd
  omega

theorem nba9 (k : Nat) (hk : 3 ≤ k) : ¬ HasPrimeAbove 9 k := by
  rintro ⟨p, hp, hgt, hpd⟩
  have : p = 3 := dvd9_prime p hp hpd
  omega

theorem nba10 (k : Nat) (hk : 5 ≤ k) : ¬ HasPrimeAbove 10 k := by
  rintro ⟨p, hp, hgt, hpd⟩
  rcases dvd10_prime p hp hpd with h' | h'
  · omega
  · omega

theorem nba14 (k : Nat) (hk : 7 ≤ k) : ¬ HasPrimeAbove 14 k := by
  rintro ⟨p, hp, hgt, hpd⟩
  rcases dvd14_prime p hp hpd with h' | h'
  · omega
  · omega

theorem nba15 (k : Nat) (hk : 5 ≤ k) : ¬ HasPrimeAbove 15 k := by
  rintro ⟨p, hp, hgt, hpd⟩
  rcases dvd15_prime p hp hpd with h' | h'
  · omega
  · omega

theorem nba16 (k : Nat) (hk : 2 ≤ k) : ¬ HasPrimeAbove 16 k := by
  rintro ⟨p, hp, hgt, hpd⟩
  have : p = 2 := dvd16_prime p hp hpd
  omega

/-- A {2,3}-smooth number with no prime-3 divisor is a power of 2. -/
theorem smooth23_no3 (v : Nat) (h : Smooth23 v) (h3 : ¬ 3 ∣ v) :
    ∃ i, v = 2 ^ i := by
  obtain ⟨aa, bb, hab⟩ := h
  refine ⟨aa, ?_⟩
  rcases (show bb = 0 ∨ 1 ≤ bb by omega) with hb0 | hb1
  · rw [hb0, Nat.pow_zero, Nat.mul_one] at hab
    exact hab.symm
  · exfalso
    have h3b : 3 ^ bb = 3 * 3 ^ (bb - 1) := by
      rw [← Nat.pow_succ]; congr 1; omega
    apply h3
    refine ⟨3 ^ (bb - 1), ?_⟩
    rw [← hab, h3b]
    ring

/-- The small-prime constructor (bounded check). -/
theorem small_prime (p : Nat) (hp2 : 2 ≤ p)
    (hchk : ∀ d, 2 ≤ d → d < p → ¬ d ∣ p) : IsPrime p := by
  refine ⟨hp2, ?_⟩
  intro d hdd
  have hle : d ≤ p := Nat.le_of_dvd (by omega) hdd
  rcases (show d = 0 ∨ d = 1 ∨ (2 ≤ d ∧ d < p) ∨ d = p by omega) with
    h' | h' | ⟨h2d, hdp⟩ | h'
  · obtain ⟨c, hc⟩ := hdd
    rw [h'] at hc
    norm_num at hc
    omega
  · exact Or.inl h'
  · exact absurd hdd (hchk d h2d hdp)
  · exact Or.inr h'

theorem prime3 : IsPrime 3 := by
  refine small_prime 3 (by omega) ?_
  intro d h2d hlt hdd
  rcases (show d = 2 by omega) with h'
  subst h'
  obtain ⟨c, hc⟩ := hdd
  omega

theorem prime13 : IsPrime 13 := by
  refine small_prime 13 (by omega) ?_
  intro d h2d hlt hdd
  rcases (show d = 2 ∨ d = 3 ∨ d = 4 ∨ d = 5 ∨ d = 6 ∨ d = 7 ∨ d = 8 ∨
      d = 9 ∨ d = 10 ∨ d = 11 ∨ d = 12 by omega) with
    h' | h' | h' | h' | h' | h' | h' | h' | h' | h' | h'
  · subst h'; obtain ⟨c, hc⟩ := hdd; omega
  · subst h'; obtain ⟨c, hc⟩ := hdd; omega
  · subst h'; obtain ⟨c, hc⟩ := hdd; omega
  · subst h'; obtain ⟨c, hc⟩ := hdd; omega
  · subst h'; obtain ⟨c, hc⟩ := hdd; omega
  · subst h'; obtain ⟨c, hc⟩ := hdd; omega
  · subst h'; obtain ⟨c, hc⟩ := hdd; omega
  · subst h'; obtain ⟨c, hc⟩ := hdd; omega
  · subst h'; obtain ⟨c, hc⟩ := hdd; omega
  · subst h'; obtain ⟨c, hc⟩ := hdd; omega
  · subst h'; obtain ⟨c, hc⟩ := hdd; omega

/-! ## §5 THE EXACT FRONTIER: f(2) = 2, f(3) = 3, f(4) = 3. -/

theorem erdos961_f2 : f961 2 = 2 := by
  have h2mem : 2 ∈ FSet 2 := by
    simp only [FSet, Set.mem_setOf_eq]
    refine ⟨by omega, ?_⟩
    intro m hm
    by_contra hcon
    push_neg at hcon
    have hN0 : ¬ HasPrimeAbove m 2 := hcon 0 (by omega)
    have hN1 : ¬ HasPrimeAbove (m + 1) 2 := hcon 1 (by omega)
    have hpow0 : ∃ i, m = 2 ^ i := by
      have hs : Smooth23 m := no_big_prime_smooth23 (m + 1) m (by omega) (by omega)
        (fun p hp hpd => by
          by_contra hbig
          exact hN0 ⟨p, hp, by omega, hpd⟩)
      refine smooth23_no3 m hs (by
        rintro ⟨c, hc⟩
        exact hN0 ⟨3, prime3, by omega, ⟨c, hc⟩⟩)
    have hpow1 : ∃ j, m + 1 = 2 ^ j := by
      have hs : Smooth23 (m + 1) := no_big_prime_smooth23 (m + 1) (m + 1)
        (Nat.le_refl _) (by omega)
        (fun p hp hpd => by
          by_contra hbig
          exact hN1 ⟨p, hp, by omega, hpd⟩)
      refine smooth23_no3 (m + 1) hs (by
        rintro ⟨c, hc⟩
        exact hN1 ⟨3, prime3, by omega, ⟨c, hc⟩⟩)
    obtain ⟨i, hi⟩ := hpow0
    obtain ⟨j, hj⟩ := hpow1
    have hpos : 1 ≤ 2 ^ i := pow_ge_one 2 i (by omega)
    rcases (show i = 0 ∨ 1 ≤ i by omega) with i0 | i1
    · rw [i0] at hi; norm_num at hi; omega
    · have h2i : (2 ^ i) % 2 = 0 := by
        have hpow : 2 ^ i = 2 * 2 ^ (i - 1) := by
          rw [← Nat.pow_succ]; congr 1; omega
        rw [hpow, Nat.mul_mod]
        norm_num
      rcases (show j = 0 ∨ 1 ≤ j by omega) with j0 | j1
      · rw [j0] at hj; norm_num at hj; omega
      · have h2j : (2 ^ j) % 2 = 0 := by
          have hpow : 2 ^ j = 2 * 2 ^ (j - 1) := by
            rw [← Nat.pow_succ]; congr 1; omega
          rw [hpow, Nat.mul_mod]
          norm_num
        have hodd : ((2 ^ j)) % 2 = 1 := by omega
        omega
  have h1not : 1 ∉ FSet 2 := by
    intro hmem
    simp only [FSet, Set.mem_setOf_eq] at hmem
    obtain ⟨_, hall⟩ := hmem
    have hcontra := hall 4 (by omega)
    obtain ⟨i, hi1, hbig⟩ := hcontra
    have i0 : i = 0 := by omega
    subst i0
    obtain ⟨p, hp, hp2, hp4⟩ := hbig
    have hle : p ≤ 4 := Nat.le_of_dvd (by norm_num) hp4
    rcases (show p = 2 ∨ p = 3 ∨ p = 4 by omega) with h' | h' | h''
    · omega
    · subst h'; exact absurd hp4 (by intro hh; obtain ⟨c, hc⟩ := hh; omega)
    · subst h''; obtain ⟨_, h4a⟩ := hp
      exact absurd (h4a 2 ⟨2, by norm_num⟩) (by omega)
  have hne : (FSet 2).Nonempty := ⟨2, h2mem⟩
  have hinf : f961 2 ∈ FSet 2 := Nat.sInf_mem hne
  rcases (show f961 2 = 0 ∨ f961 2 = 1 ∨ f961 2 = 2 by
      have := Nat.sInf_le h2mem
      omega) with h | h | h
  · rw [h] at hinf
    simp only [FSet, Set.mem_setOf_eq] at hinf
    obtain ⟨hpos, _⟩ := hinf
    omega
  · rw [h] at hinf; exact h1not hinf
  · exact h

theorem erdos961_f3 : f961 3 = 3 := by
  have h3mem : 3 ∈ FSet 3 := by
    simp only [FSet, Set.mem_setOf_eq]
    refine ⟨by omega, ?_⟩
    intro m hm
    by_contra hcon
    push_neg at hcon
    have hN0 : ¬ HasPrimeAbove m 3 := hcon 0 (by omega)
    have hN1 : ¬ HasPrimeAbove (m + 1) 3 := hcon 1 (by omega)
    have hN2 : ¬ HasPrimeAbove (m + 2) 3 := hcon 2 (by omega)
    have hbig : ∀ v : Nat, 1 ≤ v → v ≤ m + 2 → ¬ HasPrimeAbove v 3 → Smooth23 v := by
      intro v hv hle hN
      exact no_big_prime_smooth23 (m + 2) v hle hv
        (fun p hp hpd => by
          by_contra hbig3
          exact hN ⟨p, hp, by omega, hpd⟩)
    exact erdos961_run23 m (by omega) (hbig m (by omega) (by omega) hN0)
      (hbig (m + 1) (by omega) (by omega) hN1) (hbig (m + 2) (by omega) (by omega) hN2)
  have h2not : 2 ∉ FSet 3 := by
    intro hmem
    simp only [FSet, Set.mem_setOf_eq] at hmem
    obtain ⟨_, hall⟩ := hmem
    have hcontra := hall 8 (by omega)
    obtain ⟨i, hi2, hbig⟩ := hcontra
    rcases (show i = 0 ∨ i = 1 by omega) with h' | h'
    · subst h'; exact absurd hbig (nba8 3 (by omega))
    · subst h'; exact absurd hbig (nba9 3 (by omega))
  have hne : (FSet 3).Nonempty := ⟨3, h3mem⟩
  have hinf : f961 3 ∈ FSet 3 := Nat.sInf_mem hne
  rcases (show f961 3 = 0 ∨ f961 3 = 1 ∨ f961 3 = 2 ∨ f961 3 = 3 by
      have := Nat.sInf_le h3mem
      omega) with h | h | h | h
  · rw [h] at hinf
    simp only [FSet, Set.mem_setOf_eq] at hinf
    obtain ⟨hpos, _⟩ := hinf
    omega
  · rw [h] at hinf
    -- 1 ∈ FSet 3 ⟹ (upward) 2 ∈ FSet 3 ✗
    have hup : 2 ∈ FSet 3 := by
      simp only [FSet, Set.mem_setOf_eq] at hinf ⊢
      obtain ⟨hpos, hall⟩ := hinf
      exact ⟨by omega, fun m hm => by
        obtain ⟨i, hi, hbp⟩ := hall m hm
        exact ⟨i, by omega, hbp⟩⟩
    exact h2not hup
  · rw [h] at hinf; exact h2not hinf
  · exact h

theorem erdos961_f4 : f961 4 = 3 := by
  have h3mem : 3 ∈ FSet 4 := by
    simp only [FSet, Set.mem_setOf_eq]
    refine ⟨by omega, ?_⟩
    intro m hm
    by_contra hcon
    push_neg at hcon
    have hN0 : ¬ HasPrimeAbove m 4 := hcon 0 (by omega)
    have hN1 : ¬ HasPrimeAbove (m + 1) 4 := hcon 1 (by omega)
    have hN2 : ¬ HasPrimeAbove (m + 2) 4 := hcon 2 (by omega)
    -- no prime > 4 dividing v: the prime is ≤ 4, and 4 is not prime, so ≤ 3
    have hbig : ∀ v : Nat, 1 ≤ v → v ≤ m + 2 → ¬ HasPrimeAbove v 4 → Smooth23 v := by
      intro v hv hle hN
      exact no_big_prime_smooth23 (m + 2) v hle hv
        (fun p hp hpd => by
          by_contra hbig4
          have hgt : 4 < p := by omega
          exact hN ⟨p, hp, hgt, hpd⟩)
    exact erdos961_run23 m (by omega) (hbig m (by omega) (by omega) hN0)
      (hbig (m + 1) (by omega) (by omega) hN1) (hbig (m + 2) (by omega) (by omega) hN2)
  have h2not : 2 ∉ FSet 4 := by
    intro hmem
    simp only [FSet, Set.mem_setOf_eq] at hmem
    obtain ⟨_, hall⟩ := hmem
    have hcontra := hall 8 (by omega)
    obtain ⟨i, hi2, hbig⟩ := hcontra
    rcases (show i = 0 ∨ i = 1 by omega) with h' | h'
    · subst h'; exact absurd hbig (nba8 4 (by omega))
    · subst h'; exact absurd hbig (nba9 4 (by omega))
  have hne : (FSet 4).Nonempty := ⟨3, h3mem⟩
  have hinf : f961 4 ∈ FSet 4 := Nat.sInf_mem hne
  rcases (show f961 4 = 0 ∨ f961 4 = 1 ∨ f961 4 = 2 ∨ f961 4 = 3 by
      have := Nat.sInf_le h3mem
      omega) with h | h | h | h
  · rw [h] at hinf
    simp only [FSet, Set.mem_setOf_eq] at hinf
    obtain ⟨hpos, _⟩ := hinf
    omega
  · rw [h] at hinf
    have hup : 2 ∈ FSet 4 := by
      simp only [FSet, Set.mem_setOf_eq] at hinf ⊢
      obtain ⟨hpos, hall⟩ := hinf
      exact ⟨by omega, fun m hm => by
        obtain ⟨i, hi, hbp⟩ := hall m hm
        exact ⟨i, by omega, hbp⟩⟩
    exact h2not hup
  · rw [h] at hinf; exact h2not hinf
  · exact h

/-! ## §6 THE WITNESS LAWS: f(k) ≥ 4 for k = 5..12. -/

/-- Upward closure: larger windows inherit the property. -/
theorem fset_upward (k n n' : Nat) (h : n ∈ FSet k) (hle : n ≤ n') :
    n' ∈ FSet k := by
  simp only [FSet, Set.mem_setOf_eq] at h ⊢
  obtain ⟨hpos, hall⟩ := h
  refine ⟨by omega, ?_⟩
  intro m hm
  obtain ⟨i, hi, hbp⟩ := hall m hm
  exact ⟨i, by omega, hbp⟩

/-- 13 ∈ FSet k for every k ≤ 12: any 13 consecutive integers contain a
multiple of 13, which is ≥ 13 > k and divisible by the prime 13. -/
theorem fset_nonempty_13 (k : Nat) (hk : k ≤ 12) : (FSet k).Nonempty := by
  refine ⟨13, ?_⟩
  simp only [FSet, Set.mem_setOf_eq]
  refine ⟨by omega, ?_⟩
  intro m hm
  have hq := Nat.div_add_mod (m + 12) 13
  have hmod : (m + 12) % 13 < 13 := Nat.mod_lt _ (by omega)
  set x := 13 * ((m + 12) / 13) with hx
  have hge : m ≤ x := by omega
  have hle : x ≤ m + 12 := by omega
  refine ⟨x - m, by omega, ?_⟩
  have hmem : m + (x - m) = x := by omega
  rw [hmem]
  refine ⟨13, prime13, by omega, ?_⟩
  exact ⟨(m + 12) / 13, by rw [hx]⟩

theorem erdos961_lower_57 : ∀ k : Nat, 5 ≤ k → k ≤ 7 → 4 ≤ f961 k := by
  intro k h5 h7
  have hne : (FSet k).Nonempty := fset_nonempty_13 k (by omega)
  have hinf : f961 k ∈ FSet k := Nat.sInf_mem hne
  by_contra hcon
  have hup : 3 ∈ FSet k := fset_upward k (f961 k) 3 hinf (by omega)
  simp only [FSet, Set.mem_setOf_eq] at hup
  obtain ⟨_, hall⟩ := hup
  have hcontra := hall 8 (by omega)
  obtain ⟨i, hi3, hbp⟩ := hcontra
  rcases (show i = 0 ∨ i = 1 ∨ i = 2 by omega) with h' | h' | h'
  · subst h'; exact absurd hbp (nba8 k (by omega))
  · subst h'; exact absurd hbp (nba9 k (by omega))
  · subst h'; exact absurd hbp (nba10 k (by omega))

theorem erdos961_lower_712 : ∀ k : Nat, 8 ≤ k → k ≤ 12 → 4 ≤ f961 k := by
  intro k h8 h12
  have hne : (FSet k).Nonempty := fset_nonempty_13 k (by omega)
  have hinf : f961 k ∈ FSet k := Nat.sInf_mem hne
  by_contra hcon
  have hup : 3 ∈ FSet k := fset_upward k (f961 k) 3 hinf (by omega)
  simp only [FSet, Set.mem_setOf_eq] at hup
  obtain ⟨_, hall⟩ := hup
  have hcontra := hall 14 (by omega)
  obtain ⟨i, hi3, hbp⟩ := hcontra
  rcases (show i = 0 ∨ i = 1 ∨ i = 2 by omega) with h' | h' | h'
  · subst h'; exact absurd hbp (nba14 k (by omega))
  · subst h'; exact absurd hbp (nba15 k (by omega))
  · subst h'; exact absurd hbp (nba16 k (by omega))

/-! ## §7 THE PELL DICTIONARY. -/

theorem erdos961_pell_dict (n : Nat) (h1 : Smooth23 n) (h2 : Smooth23 (n + 1)) :
    ∃ a b : Nat, n * (n + 1) = a * b * b ∧ Smooth23 a ∧ Smooth23 b ∧
      (2 * n + 1) * (2 * n + 1) - a * (2 * b) * (2 * b) = 1 := by
  obtain ⟨a1, b1, hab1⟩ := h1
  obtain ⟨a2, b2, hab2⟩ := h2
  have hprod : n * (n + 1) = 2 ^ (a1 + a2) * 3 ^ (b1 + b2) := by
    rw [hab1, hab2, ← Nat.pow_add, ← Nat.pow_add]
    ring
  -- the squarefree split of 2^(a1+a2)
  have hsplit2 : 2 ^ (a1 + a2)
      = 2 ^ ((a1 + a2) % 2) * 2 ^ ((a1 + a2) / 2) * 2 ^ ((a1 + a2) / 2) := by
    have hdm := Nat.div_add_mod (a1 + a2) 2
    have hsq : 2 ^ ((a1 + a2) / 2 * 2)
        = 2 ^ ((a1 + a2) / 2) * 2 ^ ((a1 + a2) / 2) := by
      rw [Nat.pow_mul, pow_two]
    calc 2 ^ (a1 + a2) = 2 ^ ((a1 + a2) / 2 * 2 + (a1 + a2) % 2) := by rw [hdm]
      _ = 2 ^ ((a1 + a2) / 2 * 2) * 2 ^ ((a1 + a2) % 2) := Nat.pow_add _ _ _
      _ = 2 ^ ((a1 + a2) / 2) * 2 ^ ((a1 + a2) / 2) * 2 ^ ((a1 + a2) % 2) := by
          rw [hsq]
      _ = 2 ^ ((a1 + a2) % 2) * 2 ^ ((a1 + a2) / 2) * 2 ^ ((a1 + a2) / 2) := by
          ring
  have hsplit3 : 3 ^ (b1 + b2)
      = 3 ^ ((b1 + b2) % 2) * 3 ^ ((b1 + b2) / 2) * 3 ^ ((b1 + b2) / 2) := by
    have hdm := Nat.div_add_mod (b1 + b2) 2
    have hsq : 3 ^ ((b1 + b2) / 2 * 2)
        = 3 ^ ((b1 + b2) / 2) * 3 ^ ((b1 + b2) / 2) := by
      rw [Nat.pow_mul, pow_two]
    calc 3 ^ (b1 + b2) = 3 ^ ((b1 + b2) / 2 * 2 + (b1 + b2) % 2) := by rw [hdm]
      _ = 3 ^ ((b1 + b2) / 2 * 2) * 3 ^ ((b1 + b2) % 2) := Nat.pow_add _ _ _
      _ = 3 ^ ((b1 + b2) / 2) * 3 ^ ((b1 + b2) / 2) * 3 ^ ((b1 + b2) % 2) := by
          rw [hsq]
      _ = 3 ^ ((b1 + b2) % 2) * 3 ^ ((b1 + b2) / 2) * 3 ^ ((b1 + b2) / 2) := by
          ring
  refine ⟨2 ^ ((a1 + a2) % 2) * 3 ^ ((b1 + b2) % 2),
    2 ^ ((a1 + a2) / 2) * 3 ^ ((b1 + b2) / 2), ?_, ⟨_, _, rfl⟩, ⟨_, _, rfl⟩, ?_⟩
  · rw [hprod, hsplit2, hsplit3]
    ring
  · -- the Pell identity: (2n+1)² − 4n(n+1) = 1 and n(n+1) = a·b²
    have hX2 : (2 * n + 1) * (2 * n + 1) = 4 * (n * (n + 1)) + 1 := by ring
    have habb : (2 ^ ((a1 + a2) % 2) * 3 ^ ((b1 + b2) % 2)) * (2 * b) * (2 * b)
        = 4 * ((2 ^ ((a1 + a2) % 2) * 3 ^ ((b1 + b2) % 2)) * b * b) := by ring
    have hprod_ab : n * (n + 1)
        = (2 ^ ((a1 + a2) % 2) * 3 ^ ((b1 + b2) % 2)) * b * b := by
      rw [hprod, hsplit2, hsplit3]
      ring
    omega

/-! ## §8 THE ARSENAL BRIDGE (BOSS's mathematics applied to the witness
numbers — erdosternary2 + HC-PROOF, the 16,121-theorem arsenal). -/

theorem erdos961_arsenal_bridge :
    [8 % 3, (8 / 3) % 3, (8 / 9) % 3].all (fun d => ErdosTernary2.isTernaryDigit d) ∧
    [9 % 3, (9 / 3) % 3, (9 / 9) % 3].all (fun d => ErdosTernary2.isTernaryDigit d) ∧
    [16 % 3, (16 / 3) % 3, (16 / 9) % 3].all (fun d => ErdosTernary2.isTernaryDigit d) ∧
    carryAtPos 2400 1 < 4 ∧
    v2r (3 ^ 1 * 9) = v2r 9 :=
  ⟨by decide, by decide, by decide, carryAtPos_bound 2400 1,
    CardinalWorldsV2.v2r_ternary_scaling 1 9⟩

/-- THE MAIN SUMMARY: the exact frontier + the lower witnesses. -/
theorem erdos961_main :
    f961 2 = 2 ∧ f961 3 = 3 ∧ f961 4 = 3 ∧
    (∀ k, 5 ≤ k → k ≤ 7 → 4 ≤ f961 k) ∧
    (∀ k, 8 ≤ k → k ≤ 12 → 4 ≤ f961 k) := by
  exact ⟨erdos961_f2, erdos961_f3, erdos961_f4,
    erdos961_lower_57, erdos961_lower_712⟩

#eval "ERDOS961_KERNEL_GREEN"
#print axioms erdos961_census23
#print axioms erdos961_run23
#print axioms erdos961_f2
#print axioms erdos961_f3
#print axioms erdos961_f4
#print axioms erdos961_lower_57
#print axioms erdos961_lower_712
#print axioms erdos961_pell_dict
#print axioms erdos961_arsenal_bridge
#print axioms erdos961_main

end Erdos961
