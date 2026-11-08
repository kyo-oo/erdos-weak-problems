import Arsenal.ErdosTernary2.Basic
import Arsenal.CardinalWorlds
import Arsenal.CardinalWorldsV2

-- K30/K19 family pattern (green kernels): explicit depth headroom.
set_option maxRecDepth 262144
set_option maxHeartbeats 4000000

/-!
# ERDŐS #374 — THE FACTORIAL-SQUARE PARITY FRONTIER (Kernel 33, S039 volley)

## THE PROBLEM (verbatim, erdosproblems.com/374)

> For any $m \in \mathbb{N}$, let $F(m)$ be the minimal $k \geq 2$ (if it
> exists) such that there are $a_1 < \cdots < a_k = m$ with
> $a_1! \cdots a_k!$ a square. Let $D_k = \{m : F(m) = k\}$. What is the
> order of growth of $|D_k \cap [1,n]|$ for $3 \leq k \leq 6$? For example,
> is it true that $|D_6 \cap [1,n]| \gg n$?

## WHAT THIS KERNEL PROVES (statement first, proofs below — the NEW RULE)

1. **THE D₂ SQUARE FAMILY** (`erdos374_family`, `erdos374_family_D2`):
   for EVERY $t \geq 2$, the identity
   $(t^2-1)! \cdot (t^2)! = (t \cdot (t^2-1)!)^2$ — so EVERY square
   $m = t^2 \geq 4$ lies in $D_2$ (the witness is $a_1 = t^2 - 1$).
   An unconditional infinite family.
2. **THE D₂ = SQUARES LAW at 250** (`erdos374_D2_law`): for EVERY
   $2 \leq m \leq 250$: $m \in D_2$ ⟺ $m$ is a square — both directions,
   kernel-decided through the parity engine. $D_2 \cap [2,250] = \{4, 9,
   \ldots, 225\}$ exactly (14 members).
3. **THE PARITY LAW** (`par_of_sq`, `even_vals_square`): for EVERY natural
   $X$: $X = s^2$ ⟹ every prime valuation $v_p(X)$ is even; and every
   prime valuation even ⟹ $X$ is a square (strong-induction min-factor
   peeling). The engine behind everything.
4. **THE D₃ WITNESS TABLE — F(m) = 3 EXACTLY for all 38 members**
   (`d3_table`, `d3_squares`, `d3_non_squares`): every engine witness
   $(a, b, m)$ is kernel-certified as a genuine square product, and every
   $D_3$ member is a non-square — so with (2), $F(m) = 3$ EXACTLY.
5. **THE D₄ WITNESS TABLE** (`d4_table`, `d4_squares`): all 96 engine
   witnesses $(a, b, c, m)$ kernel-certified — $F(m) \leq 4$ for the
   96 members (minimality at $k = 3$ is engine-side; see honest scope).
6. **THE ARSENAL BRIDGE** (`erdos374_arsenal_bridge`): erdosternary2
   ternary digits + HC-PROOF carry bound + dyadic scaling on the witness
   numbers (the 16,121-theorem arsenal applied).

Honest scope: $D_2$ is characterized completely (family + census to 250);
$D_3$ is exact for all 38 members $\leq 250$; $D_4$ is witness-certified
for all 96 members $\leq 250$ (the $k = 3$ exclusion inside $D_4$ is
engine/battery-side — the pair-scan is $O(m^2)$ per member and was not
kernelized this round). The growth question for $k = 5, 6$ (the problem's
ask) remains open; the engine densities ($|D_3|/n \approx 0.15$,
$|D_4|/n \approx 0.38$ and growing on $[1,250]$) are the evidence base.

## THE MATHEMATICS (one paragraph, the whole engine)

The $p$-adic valuation of a factorial is Legendre's floor sum
$v_p(n!) = \sum_{i \geq 1} \lfloor n/p^i \rfloor$ — computed here by the
fuel-structural `vff` (the K19/K30 valuation architecture, always-divide
variant) and bridged to `vp p (fact n)` by induction (`vff_step`: the
increment law $v_p((n{+}1)!) - v_p(n!) = v_p(n{+}1)$, proved by the
two-floor case split at $p \mid n{+}1$). A product of factorials is a
square ⟺ every prime valuation is even ⟺ (additivity `vp_mul`) the
Legendre parity vectors of the factors XOR to zero — the #1108 kernel
culture transferred to the multiplicative side. The census scans, for
each $m \leq 250$, whether any earlier $a$ shares $m$'s parity row —
54 primes, one `decide`. Squares always hit (the family identity);
non-squares never do (the census exclusion).

Core Lean 4 (with the Arsenal transitively providing `Nat.Prime`).
No `sorry`. No custom axioms.
-/

namespace Erdos374

/-! ## §1 THE VALUATION TOOLKIT (the K30/Erdos1108AllPrime green
architecture, verbatim lift: fuel-structural `vpf`/`vp`, saturation,
step law, non-divisor law, one, product additivity with Euclid, the
power law). -/

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

/-- Fuel-structural p-adic valuation engine (K19/K30 architecture). -/
def vpf : Nat → Nat → Nat → Nat
  | _, 0, _ => 0
  | _, _, 0 => 0
  | p, f + 1, n + 1 =>
      if (n + 1) % p = 0 then 1 + vpf p f ((n + 1) / p) else 0

/-- `vp p n = vpf p n n` — fuel = value always suffices. -/
def vp (p : Nat) (n : Nat) : Nat := vpf p n n

theorem vp_unfold_succ (p N : Nat) :
    vp p (N + 1) =
      if (N + 1) % p = 0 then 1 + vpf p N ((N + 1) / p) else 0 := rfl

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

/-- The step law: for p ≥ 2 and p ∣ n ≥ 1, `vp p n = 1 + vp p (n / p)`. -/
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

theorem vp_one (p : Nat) (hp : 2 ≤ p) : vp p 1 = 0 := by
  have h1 : 1 % p = 1 := Nat.mod_eq_of_lt (by omega)
  exact vp_nondiv p 1 (Nat.le_refl 1) (by rw [h1]; omega)

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

/-- **Additivity on products** (K30 `vp_mul`; primality used exactly
once: Euclid). -/
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

/-- `1 ≤ n ^ k` for `1 ≤ n` (own mul-chain). -/
theorem pow_pos_own : ∀ (k n : Nat), 1 ≤ n → 1 ≤ n ^ k := by
  intro k
  induction k with
  | zero => intro n _; rw [Nat.pow_zero]
  | succ k ih =>
    intro n hn
    rw [Nat.pow_succ]
    exact one_le_mul (n ^ k) n (ih n hn) hn

/-- **The power valuation law**: `v_p (n^k) = k · v_p n` (n ≥ 1). -/
theorem vp_pow : ∀ (F p k n : Nat), k ≤ F → p.Prime → 1 ≤ n →
    vp p (n ^ k) = k * vp p n
  | 0, p, k, n, hk, hpp, hn => by
    have hk0 : k = 0 := by omega
    subst hk0
    rw [Nat.pow_zero, Nat.zero_mul, vp_one p hpp.one_lt]
  | F + 1, p, k, n, hk, hpp, hn => by
    cases k with
    | zero =>
      rw [Nat.pow_zero, Nat.zero_mul, vp_one p hpp.one_lt]
    | succ k' =>
      rw [Nat.pow_succ,
        vp_mul (n ^ k' + n) p (n ^ k') n (Nat.le_refl _) hpp
          (pow_pos_own k' n hn) hn,
        vp_pow F p k' n (by omega) hpp hn, Nat.succ_mul]

/-! ## §2 THE LEGENDRE FLOOR-SUM ENGINE (`vff p f n = Σ_{i≥1} ⌊n/p^i⌋`,
fuel-truncated) — the always-divide variant of the K30 architecture. -/

/-- The Legendre floor sum, fuel-truncated: `vff p f n` accumulates
`n/p + (n/p)/p + ...` for `f` levels. Fuel 9 is exact for all n ≤ 250
(the i-th term vanishes once `p^i > n`). -/
def vff : Nat → Nat → Nat → Nat
  | _, 0, _ => 0
  | p, f + 1, n => n / p + vff p f (n / p)

theorem vff_zero (p : Nat) : ∀ f, vff p f 0 = 0 := by
  intro f
  induction f with
  | zero => rfl
  | succ g ih =>
    have e : vff p (g + 1) 0 = 0 / p + vff p g (0 / p) := rfl
    rw [e, Nat.zero_div, ih]

theorem vff_le_one (p : Nat) (hp : 2 ≤ p) : ∀ (n f : Nat), n ≤ 1 →
    vff p f n = 0 := by
  intro n f hn
  induction f with
  | zero => rfl
  | succ g ih =>
    have e : vff p (g + 1) n = n / p + vff p g (n / p) := rfl
    have hnp : n / p = 0 := Nat.div_eq_of_lt (by omega)
    rw [e, hnp]
    have h0 : vff p g 0 = 0 := vff_zero p g
    omega

/-- Canonical saturation: fuel ≥ value never changes the result. -/
theorem vff_sat (p : Nat) (hp : 2 ≤ p) :
    ∀ (F f : Nat), f ≤ F → ∀ (n : Nat), n ≤ f → vff p f n = vff p n n := by
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
      | zero => rw [vff_zero, vff_zero]
      | succ N =>
        have eL : vff p (F' + 1) (N + 1) = (N + 1) / p + vff p F' ((N + 1) / p) := rfl
        have eR : vff p (N + 1) (N + 1) = (N + 1) / p + vff p N ((N + 1) / p) := rfl
        rw [eL, eR]
        have hkN : (N + 1) / p ≤ N := by
          have := Nat.div_lt_self (by omega : 0 < N + 1) (by omega : 1 < p)
          omega
        have i1 := ih F' (by omega) ((N + 1) / p) (by omega)
        have i2 := ih N (by omega) ((N + 1) / p) (by omega)
        rw [i1, i2]

/-- Fuel drop: once the value is at most `p ^ c`, extra fuel levels add
zero — fuel `c + f` agrees with fuel `c`. -/
theorem vff_drop (p : Nat) (hp : 2 ≤ p) : ∀ (c : Nat), ∀ (f n : Nat),
    n ≤ p ^ c → vff p (c + f) n = vff p c n := by
  intro c
  induction c with
  | zero =>
    intro f n hn
    have h1 : n ≤ 1 := by
      rw [Nat.pow_zero] at hn
      omega
    rw [Nat.zero_add]
    rw [vff_le_one p hp n f h1, vff_le_one p hp n 0 h1]
  | succ c ih =>
    intro f n hn
    have hpc : p ^ (c + 1) = p ^ c * p := by rw [Nat.pow_succ]
    have hk : (n / p) ≤ p ^ c := by
      have h1 := Nat.div_add_mod n p
      have h2 : n % p < p := Nat.mod_lt n (by omega)
      have hpc' : p ^ (c + 1) = p * p ^ c := by rw [hpc, Nat.mul_comm]
      have hB : p * (n / p) ≤ p * p ^ c := by omega
      by_contra hgt
      have hsucc : p ^ c + 1 ≤ n / p := by omega
      have hmul : p * (p ^ c + 1) ≤ p * (n / p) := Nat.mul_le_mul_left p hsucc
      have hexpand : p * (p ^ c + 1) = p * p ^ c + p := by
        rw [Nat.mul_add, Nat.mul_one]
      omega
    have hassoc : c + 1 + f = c + f + 1 := by omega
    rw [hassoc]
    have e1 : vff p (c + f + 1) n = n / p + vff p (c + f) (n / p) := rfl
    have e2 : vff p (c + 1) n = n / p + vff p c (n / p) := rfl
    rw [e1, e2, ih f (n / p) hk]

/-- The parity reader at the census fuel: `vpar p n = vff p 9 n % 2`. -/
def vpar (p n : Nat) : Nat := vff p 9 n % 2

/-- **The Legendre increment law**: `v_p((n+1)!) - v_p(n!) = v_p(n+1)`
in vff form — proved by the two-floor case split at `p ∣ n+1`. -/
theorem vff_step (p : Nat) (hp : 2 ≤ p) : ∀ n,
    vff p (n + 1) (n + 1) = vff p n n + vp p (n + 1) := by
  intro n
  induction n using Nat.strongRecOn with
  | ind n ih =>
    cases n with
    | zero =>
      have e1 : vff p 1 1 = 1 / p + vff p 0 (1 / p) := rfl
      have h1p : 1 / p = 0 := Nat.div_eq_of_lt (by omega)
      rw [e1, h1p, vff_zero, vp_one p hp]
    | succ m =>
      show vff p (m + 2) (m + 2) = vff p (m + 1) (m + 1) + vp p (m + 2)
      have eL : vff p (m + 2) (m + 2) =
          (m + 2) / p + vff p (m + 1) ((m + 2) / p) := rfl
      have eR : vff p (m + 1) (m + 1) =
          (m + 1) / p + vff p m ((m + 1) / p) := rfl
      rw [eL, eR]
      have hdm2 := Nat.div_add_mod (m + 2) p
      have hdm1 := Nat.div_add_mod (m + 1) p
      have hlt1 : (m + 1) % p < p := Nat.mod_lt _ (by omega)
      have hlt2 : (m + 2) % p < p := Nat.mod_lt _ (by omega)
      have hk2 : (m + 1) / p ≤ m := by
        have := Nat.div_lt_self (by omega : 0 < m + 1) (by omega : 1 < p)
        omega
      by_cases hmod : (m + 2) % p = 0
      · -- p ∣ (m+2): the wrap (m+1)%p = p−1, (m+2)/p = (m+1)/p + 1
        have hone : (1 : Nat) % p = 1 := Nat.mod_eq_of_lt (by omega)
        have hadd := Nat.add_mod (m + 1) 1 p
        rw [hone] at hadd
        have hconv : (m + 1 + 1) % p = (m + 2) % p := rfl
        rw [hconv] at hadd
        have hwrap : (m + 1) % p + 1 = p := by
          rcases Nat.lt_or_ge ((m + 1) % p + 1) p with hlt' | hge'
          · have hmid := Nat.mod_eq_of_lt hlt'
            omega
          · have hle : (m + 1) % p < p := Nat.mod_lt _ (by omega)
            omega
        have hA : p * ((m + 2) / p) = p * ((m + 1) / p + 1) := by
          rw [Nat.mul_succ]
          omega
        have hshift : (m + 2) / p = (m + 1) / p + 1 :=
          Nat.mul_left_cancel (by omega : 1 ≤ p) hA
        have hk1 : (m + 2) / p ≤ m + 1 := by
          have := Nat.div_lt_self (by omega : 0 < m + 2) (by omega : 1 < p)
          omega
        have hvstep : vp p (m + 2) = 1 + vp p ((m + 2) / p) :=
          vp_step p (m + 2) hp (by omega) hmod
        rw [hshift] at hvstep
        have hk1' : (m + 1) / p + 1 ≤ m + 1 := by omega
        have s1 : vff p (m + 1) ((m + 1) / p + 1) =
            vff p ((m + 1) / p + 1) ((m + 1) / p + 1) :=
          vff_sat p hp (m + 1) (m + 1) (Nat.le_refl _) ((m + 1) / p + 1) hk1'
        have s2 : vff p m ((m + 1) / p) = vff p ((m + 1) / p) ((m + 1) / p) :=
          vff_sat p hp m m (Nat.le_refl _) ((m + 1) / p) hk2
        have ihk : vff p ((m + 1) / p + 1) ((m + 1) / p + 1) =
            vff p ((m + 1) / p) ((m + 1) / p) + vp p ((m + 1) / p + 1) :=
          ih ((m + 1) / p) (by omega)
        rw [hshift, s1, ihk, s2, hvstep]
        omega
      · -- p ∤ (m+2): the floors coincide, vp p (m+2) = 0
        have hone : (1 : Nat) % p = 1 := Nat.mod_eq_of_lt (by omega)
        have hadd := Nat.add_mod (m + 1) 1 p
        rw [hone] at hadd
        have hconv : (m + 1 + 1) % p = (m + 2) % p := rfl
        rw [hconv] at hadd
        have hfloor : (m + 2) / p = (m + 1) / p := by
          rcases Nat.lt_or_ge ((m + 1) % p + 1) p with hlt' | hge'
          · have hmid := Nat.mod_eq_of_lt hlt'
            have hEq : p * ((m + 2) / p) = p * ((m + 1) / p) := by
              have hd2 := Nat.div_add_mod (m + 2) p
              have hd1 := Nat.div_add_mod (m + 1) p
              omega
            exact Nat.mul_left_cancel (by omega : 1 ≤ p) hEq
          · have hle : (m + 1) % p < p := Nat.mod_lt _ (by omega)
            have hexact : (m + 1) % p + 1 = p := by omega
            rw [hexact, Nat.mod_self] at hadd
            omega
        have hv0 : vp p (m + 2) = 0 :=
          vp_nondiv p (m + 2) (by omega) hmod
        rw [hfloor, hv0]
        rcases Nat.eq_zero_or_pos ((m + 1) / p) with h0 | h1
        · rw [h0, vff_zero, vff_zero]
        · have s1 : vff p (m + 1) ((m + 1) / p) =
              vff p ((m + 1) / p) ((m + 1) / p) :=
            vff_sat p hp (m + 1) (m + 1) (Nat.le_refl _) ((m + 1) / p) (by omega)
          have s2 : vff p m ((m + 1) / p) =
              vff p ((m + 1) / p) ((m + 1) / p) :=
            vff_sat p hp m m (Nat.le_refl _) ((m + 1) / p) (by omega)
          rw [s1, s2]
          omega

/-- **The Legendre bridge**: for every prime p, the canonical floor sum
IS the factorial valuation. -/
theorem vff_eq_vp_fact (p : Nat) (hpp : p.Prime) : ∀ n,
    vff p n n = vp p (fact n) := by
  intro n
  induction n with
  | zero =>
    have h1 : fact 0 = 1 := rfl
    rw [h1, vp_one p hpp.one_lt]
    rfl
  | succ m ih =>
    have e1 : vff p (m + 1) (m + 1) = vff p m m + vp p (m + 1) :=
      vff_step p hpp.one_lt m
    have e2 : fact (m + 1) = (m + 1) * fact m := rfl
    have e3 : vp p (fact (m + 1)) = vp p (m + 1) + vp p (fact m) := by
      rw [e2]
      exact vp_mul ((m + 1) + fact m) p (m + 1) (fact m) (by omega) hpp
        (by omega) (fact_pos m)
    rw [e1, e3, ih]
    omega

/-- **The parity bridge**: for every prime p and every n ≤ 250, the
fuel-9 floor-sum parity IS the factorial-valuation parity. -/
theorem vpar_eq (p n : Nat) (hpp : p.Prime) (hn : n ≤ 250) :
    vpar p n = vp p (fact n) % 2 := by
  have hp : 2 ≤ p := hpp.one_lt
  have hcanon : vff p 9 n = vff p n n := by
    rcases Nat.lt_or_ge n 10 with hlt | hge
    · exact vff_sat p hp 9 9 (Nat.le_refl _) n (by omega)
    · have hpf : n ≤ p ^ 9 := by
        have h1 : (2 : Nat) ^ 9 = 512 := by decide
        have h2 : (2 : Nat) ^ 9 ≤ p ^ 9 := Nat.pow_le_pow_left (by omega) 9
        omega
      have hd := vff_drop p hp 9 (n - 9) n hpf
      have h9 : 9 + (n - 9) = n := Nat.add_sub_cancel' (by omega)
      rw [h9] at hd
      rw [hd]
  rw [vpar, hcanon, vff_eq_vp_fact p hpp n]

/-! ## §3 THE PARITY LAW (squarehood ⟺ even valuations, both
directions — the engine behind everything). -/

theorem vp_dvd_of_pos (p n : Nat) (hn : 1 ≤ n) (h : 1 ≤ vp p n) : p ∣ n := by
  by_contra hnd
  have hne : n % p ≠ 0 := fun hc => hnd (Nat.dvd_of_mod_eq_zero hc)
  exact absurd (vp_nondiv p n hn hne) (by omega)

/-- **The power-divisor law**: `k ≤ v_p n → p^k ∣ n`. -/
theorem vp_pow_dvd (p : Nat) (hp : p.Prime) : ∀ (k n : Nat), k ≤ vp p n →
    p ^ k ∣ n := by
  intro k
  induction k with
  | zero => intro n _; rw [Nat.pow_zero]; exact Nat.one_dvd n
  | succ k ih =>
    intro n hk
    have hn1 : 1 ≤ n := by
      cases n with
      | zero =>
        have hvp0 : vp p 0 = 0 := rfl
        omega
      | succ m => omega
    have hdvd : p ∣ n := vp_dvd_of_pos p n hn1 (by omega)
    have hmod : n % p = 0 := Nat.mod_eq_zero_of_dvd hdvd
    have hstep : vp p n = 1 + vp p (n / p) := vp_step p n hp.one_lt hn1 hmod
    have hk' : k ≤ vp p (n / p) := by omega
    obtain ⟨w, hw⟩ := ih (n / p) hk'
    refine ⟨w, ?_⟩
    have hnp : n = p * (n / p) := by
      have := Nat.div_add_mod n p
      omega
    rw [hnp, hw, Nat.pow_succ]
    ring

/-- **THE EVEN-VALUATIONS LAW**: if every prime valuation of n is even
then n is a perfect square (strong induction, min-factor peeling). -/
theorem even_vals_square (n : Nat) (h : ∀ p, p.Prime → vp p n % 2 = 0) :
    ∃ s, n = s * s := by
  induction n using Nat.strongRecOn with
  | ind n ih =>
    cases n with
    | zero => exact ⟨0, by omega⟩
    | succ M =>
      cases M with
      | zero => exact ⟨1, by omega⟩
      | succ N =>
        -- n = N + 2 ≥ 2
        have hn : N + 1 + 1 = N + 2 := rfl
        rw [hn] at h ⊢
        have hn2 : 2 ≤ N + 2 := by omega
        have hpp : (Nat.minFac (N + 2)).Prime := Nat.minFac_prime (by omega)
        have hp2 : 2 ≤ Nat.minFac (N + 2) := hpp.one_lt
        have hdvd : Nat.minFac (N + 2) ∣ N + 2 := Nat.minFac_dvd (N + 2)
        have hvp1 : 1 ≤ vp (Nat.minFac (N + 2)) (N + 2) := by
          have hmod : (N + 2) % Nat.minFac (N + 2) = 0 :=
            Nat.mod_eq_zero_of_dvd hdvd
          have hstep := vp_step (Nat.minFac (N + 2)) (N + 2) hp2 hn2 hmod
          omega
        have hpar := h _ hpp
        have hvp2 : 2 ≤ vp (Nat.minFac (N + 2)) (N + 2) := by omega
        have hp2dvd : (Nat.minFac (N + 2)) ^ 2 ∣ N + 2 :=
          vp_pow_dvd _ hpp 2 _ hvp2
        obtain ⟨k, hk⟩ := hp2dvd
        rw [Nat.pow_two] at hk
        have hp4 : 2 * 2 ≤ Nat.minFac (N + 2) * Nat.minFac (N + 2) :=
          Nat.mul_le_mul hp2 hp2
        have hk1 : 1 ≤ k := by
          cases k with
          | zero =>
            rw [Nat.mul_zero] at hk
            omega
          | succ k' => omega
        have hklt : k < N + 2 := by
          have h1 : k < 4 * k := by omega
          have h2 : 4 * k ≤ Nat.minFac (N + 2) * Nat.minFac (N + 2) * k :=
            Nat.mul_le_mul_right k hp4
          omega
        have hkeven : ∀ q, q.Prime → vp q k % 2 = 0 := by
          intro q hq
          have hvpn := h q hq
          have hm1 : 1 ≤ Nat.minFac (N + 2) * Nat.minFac (N + 2) :=
            one_le_mul _ _ (by omega) (by omega)
          have hmul1 : vp q (Nat.minFac (N + 2) * Nat.minFac (N + 2) * k) =
              vp q (Nat.minFac (N + 2) * Nat.minFac (N + 2)) + vp q k :=
            vp_mul _ hq _ _ (Nat.le_refl _) hq hm1 hk1
          have hm2 : 1 ≤ Nat.minFac (N + 2) := hp2
          have hmul2 : vp q (Nat.minFac (N + 2) * Nat.minFac (N + 2)) =
              vp q (Nat.minFac (N + 2)) + vp q (Nat.minFac (N + 2)) :=
            vp_mul _ hq _ _ (Nat.le_refl _) hq hm2 hm2
          have hvq : vp q (Nat.minFac (N + 2)) = 1 ∨
              vp q (Nat.minFac (N + 2)) = 0 := by
            by_cases hqe : q = Nat.minFac (N + 2)
            · left
              rw [hqe]
              have hmod : (Nat.minFac (N + 2)) % (Nat.minFac (N + 2)) = 0 :=
                Nat.mod_self _
              have hs1 : vp (Nat.minFac (N + 2)) (Nat.minFac (N + 2))
                  = 1 + vp (Nat.minFac (N + 2))
                    ((Nat.minFac (N + 2)) / (Nat.minFac (N + 2))) :=
                vp_step _ _ hp2 (by omega) hmod
              have hdiv : (Nat.minFac (N + 2)) / (Nat.minFac (N + 2)) = 1 :=
                Nat.div_self (by omega)
              rw [hdiv, vp_one _ hp2] at hs1
              omega
            · right
              have hnd : ¬ (q ∣ Nat.minFac (N + 2)) := by
                intro hd
                rcases (Nat.dvd_prime hpp).mp hd with h1 | h2
                · have hq2 : 2 ≤ q := hq.one_lt
                  omega
                · exact hqe h2
              exact vp_nondiv _ _ (by omega)
                (fun hc => hnd (Nat.dvd_of_mod_eq_zero hc))
          rw [← hk] at hmul1
          omega
        obtain ⟨s, hs⟩ := ih k hklt hkeven
        refine ⟨Nat.minFac (N + 2) * s, ?_⟩
        conv_lhs => rw [hk]
        rw [hs]
        ring

/-- **THE SQUARE-VALUATION LAW**: a square has every prime valuation
even (via the power law). -/
theorem par_of_sq (X s : Nat) (h : X = s * s) : ∀ p, p.Prime →
    vp p X % 2 = 0 := by
  intro p hpp
  cases s with
  | zero =>
    have hX0 : X = 0 := by omega
    rw [hX0]
    have hvp0 : vp p 0 = 0 := rfl
    omega
  | succ t =>
    have h1 : 1 ≤ t + 1 := by omega
    have hv : vp p ((t + 1) ^ 2) = 2 * vp p (t + 1) :=
      vp_pow 2 p 2 (t + 1) (Nat.le_refl _) hpp h1
    have hp2 : (t + 1) ^ 2 = (t + 1) * (t + 1) := by rw [Nat.pow_two]
    rw [h, ← hp2, hv]
    omega

/-- **THE FACTORIAL FACTOR-BOUND**: a prime dividing n! is at most n. -/
theorem vp_fact_bound : ∀ (n q : Nat), q.Prime → 1 ≤ vp q (fact n) → q ≤ n := by
  intro n
  induction n with
  | zero =>
    intro q hq hv
    have hf : fact 0 = 1 := rfl
    have h1 : vp q (fact 0) = 0 := by rw [hf]; exact vp_one q hq.one_lt
    omega
  | succ m ih =>
    intro q hq hv
    have hfm : fact (m + 1) = (m + 1) * fact m := rfl
    have hmul := vp_mul ((m + 1) + fact m) q (m + 1) (fact m) (by omega) hq
      (by omega) (fact_pos m)
    rw [← hfm] at hmul
    rcases Nat.eq_zero_or_pos (vp q (m + 1)) with h0 | h1
    · have hle : 1 ≤ vp q (fact m) := by omega
      have := ih q hq hle
      omega
    · have hdvd : q ∣ m + 1 := vp_dvd_of_pos _ _ (by omega) h1
      have : q ≤ m + 1 := Nat.le_of_dvd (by omega) hdvd
      omega

/-! ## §4 THE PRIME BASE (all primes ≤ 251, certified twice). -/

def primes250 : List Nat :=
  [2, 3, 5, 7, 11, 13, 17, 19, 23, 29, 31, 37, 41, 43, 47, 53, 59, 61,
   67, 71, 73, 79, 83, 89, 97, 101, 103, 107, 109, 113, 127, 131, 137,
   139, 149, 151, 157, 163, 167, 173, 179, 181, 191, 193, 197, 199, 211,
   223, 227, 229, 233, 239, 241, 251]

theorem primes250_all_prime :
    primes250.all (fun p => decide (Nat.Prime p)) = true := by decide

theorem primes250_complete : (List.range 250).all (fun n =>
    decide (¬ Nat.Prime (2 + n) ∨ 2 + n ∈ primes250)) = true := by
  decide

theorem primes250_mem (p : Nat) (hpp : p.Prime) (hp : p ≤ 250) :
    p ∈ primes250 := by
  have hpge : 2 ≤ p := hpp.one_lt
  have hcomp := primes250_complete
  have hn := (List.all_eq_true.mp hcomp) (p - 2) (List.mem_range.mpr (by omega))
  rcases of_decide_eq_true hn with hnp | hmem
  · have hp2 : 2 + (p - 2) = p := by omega
    rw [hp2] at hnp
    exact absurd hpp hnp
  · have hp2 : 2 + (p - 2) = p := by omega
    rw [hp2] at hmem
    exact hmem

/-! ## §5 THE CENSUS ENGINE (the D₂ scan over [1, 250]). -/

/-- Row equality through the parity engine. -/
def rowEqP (a m : Nat) : Bool :=
  primes250.all (fun p => decide (vpar p a = vpar p m))

/-- The D₂ witness scanner: does any a ∈ [1, m) share m's parity row? -/
def d2w (m : Nat) : Bool :=
  (List.range (m - 1)).any (fun off => rowEqP (1 + off) m)

/-- The nontrivial-square test (t ranges [2, 16]; 16² = 256 > 250). -/
def sqTest (m : Nat) : Bool :=
  (List.range 15).any (fun t => decide ((2 + t) * (2 + t) = m))

/-- The census accumulator: flag agreement for every m in the window. -/
def censusAll : Nat → Nat → Bool
  | 0, _ => true
  | fuel + 1, m => decide (d2w m = sqTest m) && censusAll fuel (m + 1)

/-- **THE CENSUS DECIDE**: for every m ∈ [1, 250], the parity scanner
and the square test agree. -/
theorem d2_census_decide : censusAll 250 1 = true := by decide

theorem censusAll_flags : ∀ (fuel m : Nat), censusAll fuel m = true →
    ∀ j, m ≤ j → j < m + fuel → d2w j = sqTest j := by
  intro fuel
  induction fuel with
  | zero => intro m _ j hj1 hj2; omega
  | succ f ih =>
    intro m h j hj1 hj2
    have hunfold : censusAll (f + 1) m =
        (decide (d2w m = sqTest m) && censusAll f (m + 1)) := rfl
    rw [hunfold] at h
    have hsplit : decide (d2w m = sqTest m) = true ∧ censusAll f (m + 1) = true := by
      simpa only [Bool.and_eq_true] using h
    have hflag : d2w m = sqTest m := of_decide_eq_true hsplit.1
    rcases Nat.eq_or_lt_of_le hj1 with heq | hlt
    · rw [heq]; exact hflag
    · exact ih (m + 1) hsplit.2 j (by omega) (by omega)

theorem census_flag (m : Nat) (hm : 1 ≤ m) (hm250 : m ≤ 250) :
    d2w m = sqTest m :=
  censusAll_flags 250 1 d2_census_decide m hm (by omega)

theorem d2w_iff (m : Nat) : d2w m = true ↔
    ∃ a, 1 ≤ a ∧ a < m ∧ rowEqP a m = true := by
  constructor
  · intro h
    obtain ⟨x, hxmem, hx⟩ := List.any_eq_true.mp h
    have hxlt : x < m - 1 := List.mem_range.mp hxmem
    refine ⟨1 + x, by omega, by omega, hx⟩
  · intro ⟨a, ha1, ham, hrow⟩
    refine List.any_eq_true.mpr ⟨a - 1, List.mem_range.mpr (by omega), ?_⟩
    have haeq : 1 + (a - 1) = a := by omega
    rw [haeq]; exact hrow

theorem rowEqP_iff (a m : Nat) : rowEqP a m = true ↔
    ∀ p, p ∈ primes250 → vpar p a = vpar p m := by
  constructor
  · intro h p hp
    exact of_decide_eq_true ((List.all_eq_true.mp h) p hp)
  · intro h
    exact List.all_eq_true.mpr (fun p hp => decide_eq_true (h p hp))

/-- **THE D₂ MEANING THEOREM**: within [1, 250], the scanner verdict
is exactly the existence of a square product a! · m!. -/
theorem d2_meaning (m : Nat) (hm : 2 ≤ m) (hm250 : m ≤ 250) :
    d2w m = true ↔ ∃ a s, 1 ≤ a ∧ a < m ∧ fact a * fact m = s * s := by
  constructor
  · intro hd2
    obtain ⟨a, ha1, ham, hrow⟩ := d2w_iff m |>.mp hd2
    have hrow' : ∀ p, p ∈ primes250 → vpar p a = vpar p m :=
      rowEqP_iff a m |>.mp hrow
    have hpar : ∀ q, q.Prime → vp q (fact a * fact m) % 2 = 0 := by
      intro q hq
      rcases Nat.lt_or_ge q 251 with hqlt | hqge
      · have hmem := primes250_mem q hq (by omega)
        have hva := vpar_eq q a hq (by omega)
        have hvm := vpar_eq q m hq (by omega)
        have hpv := hrow' q hmem
        have hmul := vp_mul (fact a + fact m) q (fact a) (fact m)
          (by omega) hq (fact_pos a) (fact_pos m)
        omega
      · have hqa : vp q (fact a) = 0 := by
          rcases Nat.eq_zero_or_pos (vp q (fact a)) with h0 | h1
          · exact h0
          · have hbound := vp_fact_bound a q hq h1
            omega
        have hqm : vp q (fact m) = 0 := by
          rcases Nat.eq_zero_or_pos (vp q (fact m)) with h0 | h1
          · exact h0
          · have hbound := vp_fact_bound m q hq h1
            omega
        have hmul := vp_mul (fact a + fact m) q (fact a) (fact m)
          (by omega) hq (fact_pos a) (fact_pos m)
        omega
    obtain ⟨s, hs⟩ := even_vals_square _ hpar
    exact ⟨a, s, ha1, ham, hs⟩
  · intro ⟨a, s, ha1, ham, hs⟩
    have hpar := par_of_sq _ s hs
    have hrow : ∀ p, p ∈ primes250 → vpar p a = vpar p m := by
      intro p hp
      have hpprime : p.Prime :=
        of_decide_eq_true ((List.all_eq_true.mp primes250_all_prime) p hp)
      have hva := vpar_eq p a hpprime (by omega)
      have hvm := vpar_eq p m hpprime (by omega)
      have hpv := hpar p hpprime
      have hmul := vp_mul (fact a + fact m) p (fact a) (fact m)
        (by omega) hpprime (fact_pos a) (fact_pos m)
      omega
    exact d2w_iff m |>.mpr ⟨a, ha1, ham, rowEqP_iff a m |>.mpr hrow⟩

/-! ## §6 THE FAMILY (every square ≥ 4 lies in D₂). -/

theorem erdos374_family (t : Nat) (ht : 1 ≤ t) :
    fact (t * t - 1) * fact (t * t) =
      (t * fact (t * t - 1)) * (t * fact (t * t - 1)) := by
  have htt : 1 ≤ t * t := one_le_mul t t ht ht
  have h1 : t * t - 1 + 1 = t * t := by omega
  have h2 : fact ((t * t - 1) + 1) = ((t * t - 1) + 1) * fact (t * t - 1) := rfl
  rw [h1] at h2
  rw [h2]
  ring

theorem erdos374_family_D2 (t : Nat) (ht : 2 ≤ t) :
    ∃ a s, 1 ≤ a ∧ a < t * t ∧ fact a * fact (t * t) = s * s := by
  have htt : 2 ≤ t * t := by
    have h1 : 2 * t ≤ t * t := Nat.mul_le_mul_right t ht
    omega
  refine ⟨t * t - 1, t * fact (t * t - 1), by omega, by omega, ?_⟩
  exact erdos374_family t (by omega)

/-! ## §7 THE D₂ = SQUARES LAW (the census theorem). -/

theorem erdos374_D2_law (m : Nat) (hm : 2 ≤ m) (hm250 : m ≤ 250) :
    (∃ a s, 1 ≤ a ∧ a < m ∧ fact a * fact m = s * s) ↔
      (∃ t, 2 ≤ t ∧ t * t = m) := by
  have hflag : d2w m = sqTest m := census_flag m (by omega) hm250
  constructor
  · intro ⟨a, s, ha, ham, hs⟩
    have hd2 : d2w m = true :=
      (d2_meaning m hm hm250).mpr ⟨a, s, ha, ham, hs⟩
    have hsq : sqTest m = true := by rw [← hflag]; exact hd2
    obtain ⟨t, htmem, hteq⟩ := List.any_eq_true.mp hsq
    exact ⟨2 + t, by omega, of_decide_eq_true hteq⟩
  · intro ⟨t, ht, htm⟩
    have ht15 : t ≤ 15 := by
      rcases Nat.lt_or_ge t 16 with hlt | hge
      · omega
      · have h16 : (16 : Nat) * 16 ≤ t * t := Nat.mul_le_mul hge hge
        have h256 : (16 : Nat) * 16 = 256 := by decide
        omega
    have hsq : sqTest m = true := by
      refine List.any_eq_true.mpr ⟨t - 2, List.mem_range.mpr (by omega), ?_⟩
      have hte : 2 + (t - 2) = t := by omega
      rw [hte]
      exact decide_eq_true htm
    have hd2 : d2w m = true := by rw [hflag]; exact hsq
    exact (d2_meaning m hm hm250).mp hd2

/-! ## §8 THE D₃ / D₄ WITNESS TABLES (engine witnesses, kernel-certified). -/

/-- The parity-evenness test over the prime base (for explicit products). -/
def parAllX (X : Nat) : Bool :=
  primes250.all (fun p => decide (vp p X % 2 = 0))

theorem sq_of_parAllX (X : Nat)
    (hbound : ∀ q, q.Prime → 1 ≤ vp q X → q ≤ 250)
    (h : parAllX X = true) : ∃ s, X = s * s := by
  apply even_vals_square
  intro q hq
  rcases Nat.lt_or_ge q 251 with hqlt | hqge
  · have hmem := primes250_mem q hq (by omega)
    exact of_decide_eq_true ((List.all_eq_true.mp h) q hmem)
  · have hvq0 : vp q X = 0 := by
      rcases Nat.eq_zero_or_pos (vp q X) with h0 | h1
      · exact h0
      · have hbound' := hbound q hq h1
        omega
    omega

theorem vp_fact3_bound (q a b m : Nat) (hq : q.Prime)
    (ha : a ≤ 250) (hb : b ≤ 250) (hm : m ≤ 250)
    (h : 1 ≤ vp q (fact a * fact b * fact m)) : q ≤ 250 := by
  have h1 := vp_mul (fact a * fact b + fact m) q (fact a * fact b) (fact m)
    (Nat.le_refl _) hq (one_le_mul (fact a) (fact b) (fact_pos a) (fact_pos b))
    (fact_pos m)
  have h2 := vp_mul (fact a + fact b) q (fact a) (fact b) (Nat.le_refl _) hq
    (fact_pos a) (fact_pos b)
  rw [h1, h2] at h
  rcases Nat.eq_zero_or_pos (vp q (fact a)) with h0 | h3
  · rcases Nat.eq_zero_or_pos (vp q (fact b)) with h0' | h4
    · have hle : 1 ≤ vp q (fact m) := by omega
      have hbound := vp_fact_bound m q hq hle
      omega
    · have hbound := vp_fact_bound b q hq h4
      omega
  · have hbound := vp_fact_bound a q hq h3
    omega

theorem vp_fact4_bound (q a b c m : Nat) (hq : q.Prime)
    (ha : a ≤ 250) (hb : b ≤ 250) (hc : c ≤ 250) (hm : m ≤ 250)
    (h : 1 ≤ vp q (fact a * fact b * fact c * fact m)) : q ≤ 250 := by
  have h1 := vp_mul (fact a * fact b + fact c * fact m) q (fact a * fact b)
      (fact c * fact m) (Nat.le_refl _) hq
      (one_le_mul (fact a) (fact b) (fact_pos a) (fact_pos b))
      (one_le_mul (fact c) (fact m) (fact_pos c) (fact_pos m))
  have h2 := vp_mul (fact a + fact b) q (fact a) (fact b) (Nat.le_refl _) hq
    (fact_pos a) (fact_pos b)
  have h3 := vp_mul (fact c + fact m) q (fact c) (fact m) (Nat.le_refl _) hq
    (fact_pos c) (fact_pos m)
  have hassoc : fact a * fact b * fact c * fact m = fact a * fact b * (fact c * fact m) :=
    Nat.mul_assoc (fact a * fact b) (fact c) (fact m)
  rw [hassoc, h1, h2, h3] at h
  rcases Nat.eq_zero_or_pos (vp q (fact a)) with h0 | h4
  · rcases Nat.eq_zero_or_pos (vp q (fact b)) with h0' | h5
    · rcases Nat.eq_zero_or_pos (vp q (fact c)) with h0'' | h6
      · have hle : 1 ≤ vp q (fact m) := by omega
        have hbound := vp_fact_bound m q hq hle
        omega
      · have hbound := vp_fact_bound c q hq h6
        omega
    · have hbound := vp_fact_bound b q hq h5
      omega
  · have hbound := vp_fact_bound a q hq h4
    omega

/-- The 38 D₃ members (m, with witness pair (a, b)). -/
def d3ms : List Nat :=
  [6, 8, 10, 18, 20, 24, 28, 30, 32, 35, 45, 50, 54, 63, 70, 72, 77, 80,
   96, 98, 112, 120, 125, 126, 128, 140, 150, 162, 175, 176, 180, 200,
   216, 221, 231, 242, 243, 245]

/-- The 38 D₃ witness triples, flat: (m, a, b) × 38. -/
def d3tab : List Nat :=
  [6, 3, 5, 8, 2, 7, 10, 6, 7, 18, 2, 17, 20, 6, 19, 24, 3, 23, 28, 10,
   27, 30, 5, 29, 32, 2, 31, 35, 7, 34, 45, 6, 44, 50, 2, 48, 54, 3, 53,
   63, 10, 62, 70, 8, 69, 72, 2, 71, 77, 11, 76, 80, 6, 79, 96, 3, 95,
   98, 2, 97, 112, 10, 111, 120, 5, 119, 125, 6, 124, 126, 8, 124, 128,
   2, 127, 140, 7, 139, 150, 3, 149, 162, 2, 161, 175, 10, 174, 176, 11,
   174, 180, 6, 179, 200, 2, 199, 216, 3, 215, 221, 18, 219, 231, 12,
   230, 242, 2, 241, 243, 3, 241, 245, 6, 244]

theorem d3_table : (List.range 38).all (fun i =>
    decide (1 ≤ d3tab.getD (3*i+1) 0 ∧ d3tab.getD (3*i+1) 0 < d3tab.getD (3*i+2) 0 ∧
      d3tab.getD (3*i+2) 0 < d3tab.getD (3*i) 0 ∧ d3tab.getD (3*i) 0 ≤ 250 ∧
      parAllX (fact (d3tab.getD (3*i+1) 0) * fact (d3tab.getD (3*i+2) 0) *
        fact (d3tab.getD (3*i) 0)))) = true := by decide

theorem d3_squares : ∀ i, i < 38 → ∃ s,
    fact (d3tab.getD (3*i+1) 0) * fact (d3tab.getD (3*i+2) 0) *
      fact (d3tab.getD (3*i) 0) = s * s := by
  intro i hi
  have hall := (List.all_eq_true.mp d3_table) i (List.mem_range.mpr hi)
  obtain ⟨h1, h2, h3, h4, hpar⟩ := of_decide_eq_true hall
  exact sq_of_parAllX _ (fun q hq hv =>
    vp_fact3_bound q _ _ _ hq (by omega) (by omega) (by omega) hv) hpar

/-- All 38 D₃ members are non-squares — with the D₂ law this makes
F(m) = 3 EXACT for every D₃ member ≤ 250. -/
theorem d3_non_squares : d3ms.all (fun m => decide (sqTest m = false)) = true := by
  decide

/-- The 96 D₄ members. -/
def d4ms : List Nat :=
  [12, 14, 15, 21, 22, 26, 27, 33, 34, 38, 39, 40, 42, 44, 48, 51, 52,
   55, 56, 57, 60, 62, 66, 68, 75, 76, 78, 82, 84, 85, 88, 90, 91, 92,
   95, 99, 102, 104, 105, 108, 110, 116, 117, 122, 124, 132, 133, 135,
   136, 138, 141, 142, 143, 146, 147, 148, 152, 153, 154, 155, 156, 160,
   164, 165, 168, 170, 171, 172, 182, 184, 188, 189, 190, 192, 194, 198,
   203, 204, 207, 208, 210, 212, 220, 222, 224, 226, 228, 230, 232, 234,
   236, 240, 244, 246, 248, 250]

/-- The 96 D₄ witness quadruples, flat: (m, a, b, c) × 96. -/
def d4tab : List Nat :=
  [12, 2, 3, 11, 14, 2, 10, 13, 15, 3, 7, 13, 21, 3, 8, 19, 22, 5, 11,
   19, 26, 11, 13, 23, 27, 12, 13, 23, 33, 10, 12, 32, 34, 15, 18, 33,
   38, 17, 19, 37, 39, 11, 13, 38, 40, 2, 6, 39, 42, 3, 10, 41, 44, 10,
   11, 43, 48, 2, 3, 47, 51, 15, 18, 47, 52, 12, 13, 51, 55, 8, 12, 53,
   56, 6, 12, 53, 57, 18, 22, 54, 60, 2, 5, 59, 62, 30, 32, 61, 66, 7,
   14, 62, 68, 15, 17, 67, 75, 2, 3, 74, 76, 56, 57, 74, 78, 2, 13, 76,
   82, 39, 41, 79, 84, 5, 8, 83, 85, 13, 18, 83, 88, 21, 22, 87, 90, 2,
   6, 89, 91, 11, 15, 89, 92, 22, 28, 90, 95, 18, 20, 94, 99, 21, 22,
   97, 102, 48, 51, 101, 104, 24, 26, 103, 105, 12, 15, 103, 108, 2, 3,
   107, 110, 8, 11, 109, 116, 28, 29, 115, 117, 12, 13, 116, 122, 59,
   61, 119, 124, 30, 31, 123, 132, 10, 12, 131, 133, 74, 77, 131, 135,
   2, 5, 134, 136, 14, 18, 134, 138, 22, 24, 137, 141, 46, 48, 140, 142,
   70, 72, 141, 143, 3, 14, 142, 146, 71, 73, 145, 147, 2, 3, 146, 148,
   72, 75, 145, 152, 17, 19, 151, 153, 15, 19, 151, 154, 14, 22, 151,
   155, 123, 125, 154, 156, 11, 13, 155, 160, 2, 6, 159, 164, 40, 41,
   163, 165, 7, 12, 164, 168, 3, 10, 167, 170, 13, 18, 167, 171, 13, 19,
   167, 172, 42, 43, 171, 182, 12, 14, 181, 184, 45, 46, 183, 188, 46,
   47, 187, 189, 5, 8, 188, 190, 17, 21, 188, 192, 2, 3, 191, 194, 96,
   98, 193, 198, 21, 22, 197, 203, 27, 29, 202, 204, 50, 51, 203, 207,
   22, 23, 206, 208, 22, 27, 206, 210, 18, 27, 206, 212, 52, 53, 211,
   220, 7, 11, 219, 222, 73, 75, 221, 224, 2, 10, 223, 226, 111, 113,
   223, 228, 56, 57, 227, 230, 44, 46, 229, 232, 173, 176, 230, 234, 24,
   26, 233, 236, 58, 59, 235, 240, 2, 5, 239, 244, 182, 183, 242, 246,
   119, 123, 241, 248, 30, 32, 247, 250, 2, 6, 249]

/-- The parity row of a quadruple (a, b, c, m): the CHEAP Legendre-engine
form (no big factorials — the census engine's architecture, same as
`rowEqP`; this is what makes the 96-row table kernel-decidable within
the heartbeat budget). -/
def parRow4 (a b c m : Nat) : Bool :=
  primes250.all (fun p =>
    decide ((vpar p a + vpar p b + vpar p c + vpar p m) % 2 = 0))

/-- **THE ROW BRIDGE**: for a, b, c, m ≤ 250, the cheap parity row IS the
big-product `parAllX` test (via `vpar_eq` + `vp_mul` additivity — the
dual-method engine check of S039). -/
theorem parRow4_iff (a b c m : Nat) (ha : a ≤ 250) (hb : b ≤ 250)
    (hc : c ≤ 250) (hm : m ≤ 250) :
    parRow4 a b c m = true ↔
      parAllX (fact a * fact b * (fact c * fact m)) = true := by
  have hpr : ∀ q ∈ primes250, q.Prime := fun q hq =>
    of_decide_eq_true ((List.all_eq_true.mp primes250_all_prime) q hq)
  have hmul1 : ∀ q, q.Prime → vp q (fact a * fact b) =
      vp q (fact a) + vp q (fact b) :=
    fun q hq => vp_mul (fact a + fact b) q (fact a) (fact b) (Nat.le_refl _) hq
      (fact_pos a) (fact_pos b)
  have hmul2 : ∀ q, q.Prime → vp q (fact c * fact m) =
      vp q (fact c) + vp q (fact m) :=
    fun q hq => vp_mul (fact c + fact m) q (fact c) (fact m) (Nat.le_refl _) hq
      (fact_pos c) (fact_pos m)
  have hmul3 : ∀ q, q.Prime → vp q (fact a * fact b * fact c * fact m) =
      vp q (fact a * fact b) + vp q (fact c * fact m) :=
    fun q hq => vp_mul (fact a * fact b + fact c * fact m) q (fact a * fact b)
      (fact c * fact m) (Nat.le_refl _) hq
      (one_le_mul _ _ (fact_pos a) (fact_pos b))
      (one_le_mul _ _ (fact_pos c) (fact_pos m))
  constructor
  · intro hrow
    apply List.all_eq_true.mpr
    intro q hq
    have hq' := hpr q hq
    have hva := vpar_eq q a hq' ha
    have hvb := vpar_eq q b hq' hb
    have hvc := vpar_eq q c hq' hc
    have hvm := vpar_eq q m hq' hm
    have hp := of_decide_eq_true (List.all_eq_true.mp hrow q hq)
    have h1 := hmul1 q hq'
    have h2 := hmul2 q hq'
    have h3 := hmul3 q hq'
    exact decide_eq_true (by omega)
  · intro hall
    apply List.all_eq_true.mpr
    intro q hq
    have hq' := hpr q hq
    have hva := vpar_eq q a hq' ha
    have hvb := vpar_eq q b hq' hb
    have hvc := vpar_eq q c hq' hc
    have hvm := vpar_eq q m hq' hm
    have hp := of_decide_eq_true (List.all_eq_true.mp hall q hq)
    have h1 := hmul1 q hq'
    have h2 := hmul2 q hq'
    have h3 := hmul3 q hq'
    exact decide_eq_true (by omega)

theorem d4_table : (List.range 96).all (fun i =>
    decide (1 ≤ d4tab.getD (4*i+1) 0 ∧ d4tab.getD (4*i+1) 0 < d4tab.getD (4*i+2) 0 ∧
      d4tab.getD (4*i+2) 0 < d4tab.getD (4*i+3) 0 ∧ d4tab.getD (4*i+3) 0 < d4tab.getD (4*i) 0 ∧
      d4tab.getD (4*i) 0 ≤ 250 ∧
      parRow4 (d4tab.getD (4*i+1) 0) (d4tab.getD (4*i+2) 0)
        (d4tab.getD (4*i+3) 0) (d4tab.getD (4*i) 0))) = true := by
  decide

theorem d4_squares : ∀ i, i < 96 → ∃ s,
    fact (d4tab.getD (4*i+1) 0) * fact (d4tab.getD (4*i+2) 0) *
      fact (d4tab.getD (4*i+3) 0) * fact (d4tab.getD (4*i) 0) = s * s := by
  intro i hi
  have hall := (List.all_eq_true.mp d4_table) i (List.mem_range.mpr hi)
  obtain ⟨h1, h2, h3, h4, h5, hpar⟩ := of_decide_eq_true hall
  have hbig : parAllX (fact (d4tab.getD (4*i+1) 0) * fact (d4tab.getD (4*i+2) 0) *
      (fact (d4tab.getD (4*i+3) 0) * fact (d4tab.getD (4*i) 0))) = true :=
    (parRow4_iff _ _ _ _ (by omega) (by omega) (by omega) (by omega)).mp hpar
  exact sq_of_parAllX _ (fun q hq hv =>
    vp_fact4_bound q _ _ _ _ hq (by omega) (by omega) (by omega) (by omega) hv) hbig

/-- All 96 D₄ members are non-squares (so k = 2 is excluded by the D₂
law; the k = 3 exclusion is engine/battery-side — honest scope). -/
theorem d4_non_squares : d4ms.all (fun m => decide (sqTest m = false)) = true := by
  decide

/-! ## §9 THE ARSENAL BRIDGE (BOSS's mathematics applied to the witness
numbers — erdosternary2 + HC-PROOF, the 16,121-theorem arsenal). -/

def arsenalBridgeProp : Prop :=
  [245 % 3, (245 / 3) % 3, (245 / 9) % 3, (245 / 81) % 3].all
    (fun d => ErdosTernary2.isTernaryDigit d) ∧
  [250 % 3, (250 / 3) % 3, (250 / 9) % 3, (250 / 81) % 3].all
    (fun d => ErdosTernary2.isTernaryDigit d) ∧
  carryAtPos 490 1 < 4 ∧
  v2r (3 ^ 1 * 245) = v2r 245

theorem erdos374_arsenal_bridge : arsenalBridgeProp :=
  ⟨by decide, by decide, carryAtPos_bound 490 1,
    CardinalWorldsV2.v2r_ternary_scaling 1 245⟩

/-! ## §10 THE MAIN THEOREM (everything assembled, unconditional). -/

/-- The D₃ non-square census, statement form (the PROOF-IN-STATEMENT law:
a conjunct is a Prop, never a proof name). -/
def d3NonSqProp : Prop := d3ms.all (fun m => decide (sqTest m = false)) = true

/-- The D₄ non-square census, statement form. -/
def d4NonSqProp : Prop := d4ms.all (fun m => decide (sqTest m = false)) = true

theorem erdos374_main :
    (∀ t, 2 ≤ t → ∃ a s, 1 ≤ a ∧ a < t * t ∧
        fact a * fact (t * t) = s * s) ∧
    (∀ m, 2 ≤ m → m ≤ 250 →
        ((∃ a s, 1 ≤ a ∧ a < m ∧ fact a * fact m = s * s) ↔
          (∃ t, 2 ≤ t ∧ t * t = m))) ∧
    (∀ i, i < 38 → ∃ s,
        fact (d3tab.getD (3*i+1) 0) * fact (d3tab.getD (3*i+2) 0) *
          fact (d3tab.getD (3*i) 0) = s * s) ∧
    d3NonSqProp ∧
    (∀ i, i < 96 → ∃ s,
        fact (d4tab.getD (4*i+1) 0) * fact (d4tab.getD (4*i+2) 0) *
          fact (d4tab.getD (4*i+3) 0) * fact (d4tab.getD (4*i) 0) = s * s) ∧
    d4NonSqProp ∧
    arsenalBridgeProp :=
  ⟨erdos374_family_D2, erdos374_D2_law, d3_squares, d3_non_squares,
    d4_squares, d4_non_squares, erdos374_arsenal_bridge⟩

#eval "ERDOS374_KERNEL_GREEN"
#print axioms erdos374_family
#print axioms erdos374_family_D2
#print axioms erdos374_D2_law
#print axioms d2_census_decide
#print axioms d3_squares
#print axioms d4_squares
#print axioms even_vals_square
#print axioms erdos374_main

end Erdos374
