/-
# ERDŐS #404 — THE COMPLETE-PROOF KERNEL (Erdos404Full, S050-A2)

## THE PROBLEM (verbatim, erdosproblems.com/404, accessed 2026-11-02)

> For which integers a ≥ 1 and primes p is there a finite upper bound on
> those k such that there are a = a₁ < ··· < aₙ with
> p^k ∣ (a₁! + ··· + aₙ!)?
> If f(a,p) is the greatest such k, how does this function behave?
> Is there a prime p and an infinite sequence a₁ < a₂ < ··· such that
> if p^{m_k} is the highest power of p dividing Σ_{i ≤ k} aᵢ!
> then m_k → ∞?

## THE IMPORT BASE (the engineering law of this file)

`import ResidualTail` (Kernel 37, CI-green) — brings in, transitively via the
vendored Arsenal (`Arsenal.ErdosTernary2.Basic`, `Arsenal.CardinalWorlds`,
`Arsenal.CardinalWorldsV2` — BOSS's erdosternary2 + HC-PROOF corpus):

* the shared §1 machinery: `fact`, `pt`, `sumF`, `sumP`, `fact_pos`,
  `fact_pt`, `mul_add_split`, `sumF_split` (Theorem A's factorization),
  `one_le_mul_nat`;
* the general-p valuation engine: `vpadf`, `vpad`, `vpadf_sat`,
  `vpad_step`, `vpad_nondiv`, `vpad_mul_nondiv` (the Euclid-powered
  multiplicative law);
* **the residual-tail class law `erdos404_residual_tail` and the
  m = 3 window `erdos404_class_p_minus_3` — CITED, NOT re-proved**
  (Kernel 37's own theorems, re-exported here as master-theorem conjuncts
  and re-printed in the receipts below);
* the Arsenal bridge `erdos404t_arsenal_bridge`.

Engineering record: the repo's standalone green kernels are pairwise
name-incompatible root-level scripts (`fact`/`v2`/`fact_pos` are declared in
PadicReduction, TheoremBGeneral, ResidualTail, ExactF22 AND ExactF62), so at
most ONE of them is importable into a single file; `ResidualTail` is the
strongest import base (class laws + machinery + Arsenal). In particular the
f(2,2) / f(6,2) final theorems (`erdos404_f22_final` in F22All.lean and
`erdos404_f62_final` in F62All.lean) can never be co-imported (they clash with
each other on `fact`, `v2`, `witnessB`, …). Therefore:

* **f(2,2) = 254 and f(6,2) = 133 enter this kernel at the WITNESS level**
  (the doc §5 lower-bound components: the explicit 118-element /
  61-element witnesses, kernel-decided, ported from ExactF22/ExactF62's
  green `erdos404_f22_lower` / `erdos404_f62_lower` architecture);
* the SOUND OBSTRUCTION upper bounds (the class-DP engines:
  `erdos404_f22_final`, CI run 41909053106 GREEN, commit 026c98c;
  `erdos404_f62_final`, CI run 42119256613 GREEN, commit 2498b4f) are
  **CITED** — they remain owned by the green Kernel-10/Kernel-14 chains,
  whose receipts are already CI-grepped in the kills.yml steps
  "Kernel 10" / "Kernel 14".
* Likewise CITED (not re-proved here): Kernel 2 `kernel_law`
  (bulldoze/problem404-padic-kernel), Kernel 5 `erdos404_odd_a` /
  `erdos404_f42` (PadicReduction.lean), Kernel 7 lift/pair/triple laws
  (GadgetSupply.lean), Kernel 9's nine T-families (ObstructionFamilies.lean).

## THE THEOREM BOARD (this file; every statement matches COMPLETE_PROOF.md)

* **THEOREM A — the p-adic reduction law** (doc §1) `erdos404_theoremA`:
  for every prime p, every finite index list B beyond a:
  `a! + Σ_B i! = a!·(1 + Σ_B Pᵢ)` AND
  `v_p(a! + Σ_B i!) = v_p(a!) + v_p(1 + Σ_B Pᵢ)` — the master split
  `f(a,p) = v_p(a!) + g(a,p)` (Corollary A1).  Plus the p = 2 instance
  `erdos404_split` (Kernel 5's own form).
* **THEOREM B — the p ∣ a+1 class** (doc §2, Kernel 11)
  `erdos404_theoremB`: for every p ≥ 2 dividing a+1 and every B beyond a:
  `v_p(a! + Σ_B i!) = v_p(a!)` — the valuation NEVER grows; f(a,p) = v_p(a!)
  on the whole class (e.g. every odd a at p = 2, every (p−1, p)).
* **THE RESIDUAL-TAIL CLASS LAW** (doc §2, Kernel 37): CITED via import —
  `erdos404_residual_tail` (m ≥ 3, (m−1)(m−1)!+1 < p, a ≡ −m mod p) and
  `erdos404_class_p_minus_3` (every prime p ≥ 7, every a ≡ p−3).
* **THE p = 2 STRUCTURE ALGEBRA** (doc §3): the block identities
  `erdos404_block_pair` ([u,u+1] = u!·(u+2)) and `erdos404_block_triple`
  ([u,u+2] = u!·(u+2)²); **the cube identity** `erdos404_cube_identity`
  (1 + P_{a+1} + P_{a+3} = (a+2)³, Theorem CU) and its valuation form
  `erdos404_cube_bound` (v₂(1 + ΣP) = 3·v₂(a+2) — the universal lower
  bound g(a,2) ≥ 3·v₂(a+2), tight on T2/T3).
* **THE EXACT ANCHOR WITNESSES** (doc §5, lower-bound components):
  `erdos404_f22_witness` : v₂(2 + Σ_{i∈B} i!) = 254 for the explicit
  118-element witness B ⊆ [3,254]; `erdos404_f62_witness` :
  v₂(720 + Σ_{i∈B₆} i!) = 133 for the explicit 61-element witness
  B₆ ⊆ [7,135].  (Upper bounds: the cited green finals above.)
* **THE COMPACTNESS Q3-BRIDGE** (doc §1 Theorem A4's engine + §7)
  `erdos404_no_infinite_chain`: if EVERY admissible sum at (a,p) is
  bounded (g(a,p) < ∞ in list form), then NO infinite chain
  a = a₁ < a₂ < ··· with m_k → ∞ exists at (a,p) — the contrapositive
  engine that converts every finite certificate into a negative
  sub-Q3 verdict.
* **THE MASTER THEOREM** `erdos404_full_classification`: the complete
  partial structure theorem of the doc's final section — all of the above
  (including the cited Kernel-37 class laws verbatim) as ONE unconditional
  conjunction, no sub-cases.

Zero sorry, zero admit, zero new axioms: only [propext, Classical.choice,
Quot.sound] may appear in the receipts.  CI compiles this file with
`lake env lean problem404-full/Erdos404Full.lean` after staging
`ResidualTail.olean` (the Kernel-10/14 olean-chain pattern).
-/

import Arsenal.ErdosTernary2.Basic
import Arsenal.CardinalWorlds
import Arsenal.CardinalWorldsV2
import ResidualTail

set_option maxHeartbeats 16000000
set_option maxRecDepth 4096
set_option exponentiation.threshold 1024

namespace Erdos404Full

-- ===========================================================================
-- §1  THE v2 TOOLKIT (fuel-structural, kernel-transparent — the ExactF22
--     architecture, ported so the witness theorems are kernel-decidable;
--     `one_le_mul` is renamed to the imported `one_le_mul_nat` because
--     Mathlib (transitive via the Arsenal) already declares `one_le_mul`)
-- ===========================================================================

/-- Binary valuation — FUEL-STRUCTURAL (well-founded recursion does not
kernel-reduce; the fuel form makes every downstream kernel evaluation
possible). -/
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

/-- Additivity of v2 on products (fuel induction; the campaign's KernelLaw
lemma). -/
theorem v2_mul : ∀ (f a b : Nat), a + b ≤ f → 1 ≤ a → 1 ≤ b →
    v2 (a * b) = v2 a + v2 b
  | 0, a, b, hf, ha, hb => by omega
  | f + 1, a, b, hf, ha, hb => by
    by_cases ha1 : a = 1
    · rw [ha1, Nat.one_mul, v2_odd 1 (by omega)]
      omega
    · by_cases hae : a % 2 = 0
      · have hxy : 1 ≤ a * b := one_le_mul_nat a b (by omega) hb
        have hb2 : (a * b) % 2 = 0 := by rw [Nat.mul_mod, hae]; simp
        have hsplit : a * b / 2 = (a / 2) * b := even_mul_div2 a b hae
        rw [v2_even_pos _ hxy hb2, hsplit]
        rw [v2_mul f (a / 2) b (by omega) (by omega) hb]
        rw [v2_even_pos a (by omega) hae]
        omega
      · by_cases hbe : b % 2 = 0
        · rw [Nat.mul_comm a b]
          have hxy : 1 ≤ b * a := one_le_mul_nat b a hb (by omega)
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

theorem mod_two_lt (n : Nat) : n % 2 < 2 := by omega

theorem mod_two_cases (n : Nat) : n % 2 = 0 ∨ n % 2 = 1 := by omega

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
            exact Nat.mul_left_cancel (by omega : (0:Nat) < 2) hfin
        have hrec := v2_max f (n / 2) d' (by omega) (by
          have hmod := Nat.div_add_mod n 2
          omega) hhalf_dvd
        rw [v2_even_pos n hn heven]
        omega

-- ===========================================================================
-- §2  THEOREM A — THE p-ADIC REDUCTION LAW (doc §1: the master split)
-- ===========================================================================

/-- **The general-p multiplicative law** (the doc's Theorem A engine:
`v_p(xy) = v_p(x) + v_p(y)` for every prime p and positive x, y).
Fuel induction on `x + y ≤ F`; the both-units case is Euclid
(`Nat.Prime.dvd_mul`, the Kernel-37 pattern). -/
theorem vpad_mul_prime (p : Nat) (hp : Nat.Prime p) :
    ∀ (F x y : Nat), x + y ≤ F → 1 ≤ x → 1 ≤ y →
    vpad p (x * y) = vpad p x + vpad p y := by
  intro F
  induction F with
  | zero => intro x y hF hx hy; omega
  | succ F ih =>
    intro x y hF hx hy
    have hp2 : 2 ≤ p := hp.two_le
    by_cases hx0 : x % p = 0
    · -- p ∣ x: step both sides down by one p
      have hmod := Nat.div_add_mod x p
      rw [hx0, Nat.add_zero] at hmod
      have hxdiv : p * (x / p) = x := hmod
      have hxp1 : 1 ≤ x / p := by
        rcases Nat.eq_zero_or_pos (x / p) with h | h
        · rw [h, Nat.mul_zero] at hxdiv; omega
        · exact h
      have hxu0 : (x * y) % p = 0 := by rw [Nat.mul_mod, hx0, Nat.zero_mul, Nat.zero_mod]
      have hxu1 : 1 ≤ x * y := one_le_mul_nat x y hx hy
      have hstep := vpad_step p (x * y) hp2 hxu1 hxu0
      have hdiv : (x * y) / p = (x / p) * y := by
        obtain ⟨m, hm⟩ : ∃ m, x / p = m := ⟨x / p, rfl⟩
        have hdx : p * m = x := by rw [← hm]; exact hxdiv
        rw [hm, ← hdx, Nat.mul_assoc, Nat.mul_div_cancel_left _ (by omega : 0 < p)]
      have hxpF : x / p + y ≤ F := by
        have hle : (x / p) * 2 ≤ (x / p) * p := Nat.mul_le_mul_left _ hp2
        have hsame : (x / p) * p = p * (x / p) := Nat.mul_comm _ _
        rw [hsame, hxdiv] at hle
        omega
      have hstepx := vpad_step p x hp2 hx hx0
      rw [hstep, hdiv, ih (x / p) y hxpF hxp1 hy, hstepx]
      omega
    · by_cases hy0 : y % p = 0
      · -- p ∣ y, p ∤ x: commute and step down through y
        rw [Nat.mul_comm x y]
        have hmod := Nat.div_add_mod y p
        rw [hy0, Nat.add_zero] at hmod
        have hydiv : p * (y / p) = y := hmod
        have hyp1 : 1 ≤ y / p := by
          rcases Nat.eq_zero_or_pos (y / p) with h | h
          · rw [h, Nat.mul_zero] at hydiv; omega
          · exact h
        have hxy1 : 1 ≤ y * x := one_le_mul_nat y x hy hx
        have hxy0 : (y * x) % p = 0 := by rw [Nat.mul_mod, hy0, Nat.zero_mul, Nat.zero_mod]
        have hstep := vpad_step p (y * x) hp2 hxy1 hxy0
        have hdiv : (y * x) / p = (y / p) * x := by
          obtain ⟨m, hm⟩ : ∃ m, y / p = m := ⟨y / p, rfl⟩
          have hdx : p * m = y := by rw [← hm]; exact hydiv
          rw [hm, ← hdx, Nat.mul_assoc, Nat.mul_div_cancel_left _ (by omega : 0 < p)]
        have hypF : y / p + x ≤ F := by
          have hle : (y / p) * 2 ≤ (y / p) * p := Nat.mul_le_mul_left _ hp2
          have hsame : (y / p) * p = p * (y / p) := Nat.mul_comm _ _
          rw [hsame, hydiv] at hle
          omega
        have hstepy := vpad_step p y hp2 hy hy0
        rw [hstep, hdiv, ih (y / p) x hypF hyp1 hx, hstepy]
        omega
      · -- p ∤ x and p ∤ y: Euclid forces p ∤ x·y; all three valuations are 0
        have hxy0 : (x * y) % p ≠ 0 := by
          intro hc
          have hd : p ∣ x * y := Nat.dvd_of_mod_eq_zero hc
          rcases (Nat.Prime.dvd_mul hp).mp hd with h1 | h2
          · obtain ⟨c, hc2⟩ := h1
            have hz := mod_zero_of_dvd x p c hc2
            omega
          · obtain ⟨c, hc2⟩ := h2
            have hz := mod_zero_of_dvd y p c hc2
            omega
        rw [vpad_nondiv p x hx hx0, vpad_nondiv p y hy hy0,
            vpad_nondiv p (x * y) (one_le_mul_nat x y hx hy) hxy0]

/-- **THEOREM A (the p-adic reduction law — doc §1).** For every prime p,
every seed a and every finite index list B beyond a: the sum factors through
the quotient staircase AND the valuation splits:
`v_p(a! + Σ_B i!) = v_p(a!) + v_p(1 + Σ_B Pᵢ)` — the master split
`f(a,p) = v_p(a!) + g(a,p)` of Corollary A1, unconditionally. -/
theorem erdos404_theoremA (a p : Nat) (hp : Nat.Prime p) (B : List Nat)
    (hB : ∀ i ∈ B, a < i) :
    fact a + sumF B = fact a * (1 + sumP a B)
    ∧ vpad p (fact a + sumF B) = vpad p (fact a) + vpad p (1 + sumP a B) := by
  refine ⟨sumF_split a B hB, ?_⟩
  rw [sumF_split a B hB]
  exact vpad_mul_prime p hp (fact a + (1 + sumP a B)) (fact a) (1 + sumP a B)
    (Nat.le_refl _) (fact_pos a) (by omega)

/-- **Theorem A at p = 2** (Kernel 5's `erdos404_split`, the form the doc's
§1 cites): `v₂(a! + Σ_B i!) = v₂(a!) + v₂(1 + Σ_B Pᵢ)`. -/
theorem erdos404_split (a : Nat) (B : List Nat) (hB : ∀ i ∈ B, a < i) :
    v2 (fact a + sumF B) = v2 (fact a) + v2 (1 + sumP a B) := by
  have h1 : 1 ≤ fact a := fact_pos a
  have h2 : 1 ≤ 1 + sumP a B := by omega
  rw [sumF_split a B hB]
  exact v2_mul (fact a + (1 + sumP a B)) (fact a) (1 + sumP a B)
    (Nat.le_refl _) h1 h2

-- ===========================================================================
-- §3  THEOREM B — THE p ∣ a+1 CLASS, EVERY p ≥ 2 (doc §2, Kernel 11)
-- ===========================================================================

/-- **Unit-congruence law** (the engine of the class). If `u ≡ 1 (mod p)` and
x, u ≥ 1 with p ≥ 2, then `v_p (x·u) = v_p (x)`.  Fuel induction on x; needs
NO Euclid lemma — `(x·u) % p = x % p` by mod-arithmetic alone. -/
theorem vpad_congr_unit : ∀ (F p x u : Nat), x ≤ F → 2 ≤ p → 1 ≤ x → 1 ≤ u →
    u % p = 1 → vpad p (x * u) = vpad p x := by
  intro F
  induction F with
  | zero => intro p x u hxF hp hx hu hu1; omega
  | succ F ih =>
    intro p x u hxF hp hx hu hu1
    by_cases hx0 : x % p = 0
    · -- p ∣ x: step both sides down by one p
      have hmod := Nat.div_add_mod x p
      rw [hx0] at hmod
      have hxdiv : p * (x / p) = x := by simpa using hmod
      have hxp1 : 1 ≤ x / p := by
        rcases Nat.eq_zero_or_pos (x / p) with h | h
        · rw [h, Nat.mul_zero] at hxdiv; omega
        · exact h
      have hxdiv' : (x / p) * p = x := by rw [Nat.mul_comm]; exact hxdiv
      have hxpF : x / p ≤ F := by
        have h2 : (x / p) * 2 ≤ (x / p) * p := Nat.mul_le_mul_left _ hp
        omega
      have hxu0 : (x * u) % p = 0 := by
        rw [Nat.mul_mod, hx0, hu1]
        simp
      have hxu1 : 1 ≤ x * u := one_le_mul_nat x u hx hu
      have hstep := vpad_step p (x * u) hp hxu1 hxu0
      have hdiv : (x * u) / p = (x / p) * u := by
        obtain ⟨m, hm⟩ : ∃ m, x / p = m := ⟨x / p, rfl⟩
        have hdx : p * m = x := by rw [← hm]; exact hxdiv
        rw [hm, ← hdx, Nat.mul_assoc, Nat.mul_div_cancel_left _ (by omega : 0 < p)]
      rw [hstep, hdiv, ih p (x / p) u hxpF hp hxp1 hu hu1]
      have hstepx := vpad_step p x hp hx hx0
      omega
    · -- p ∤ x: then p ∤ x·u (congruence!), both valuations are 0
      have hxu0 : (x * u) % p ≠ 0 := by
        rw [Nat.mul_mod, hu1, Nat.mul_one, Nat.mod_mod]
        exact hx0
      rw [vpad_nondiv p (x * u) (one_le_mul_nat x u hx hu) hxu0,
          vpad_nondiv p x hx hx0]

/-- If `p ∣ a + 1` then every staircase term `pt a j = (a+1)···(a+j)`
(with j ≥ 1) is divisible by p. -/
theorem pt_dvd_of_dvd (a p : Nat) (hd : p ∣ a + 1) :
    ∀ (j : Nat), 1 ≤ j → p ∣ pt a j
  | 0, _ => by omega
  | 1, _ => by
    have h1 : pt a 1 = 1 * (a + 1) := rfl
    rw [h1, Nat.one_mul]
    exact hd
  | j + 2, _ => by
    have IH : p ∣ pt a (j + 1) := pt_dvd_of_dvd a p hd (j + 1) (by omega)
    have hstep : pt a (j + 2) = pt a (j + 1) * (a + (j + 1) + 1) := rfl
    rw [hstep]
    exact Nat.dvd_trans IH (Nat.dvd_mul_right _ _)

/-- If `p ∣ a + 1`, the whole staircase sum is ≡ 0 mod p. -/
theorem sumP_mod_zero (a p : Nat) (hd : p ∣ a + 1) :
    ∀ (B : List Nat), (∀ i ∈ B, a < i) → sumP a B % p = 0 := by
  intro B
  induction B with
  | nil => intro _; show (0 : Nat) % p = 0; simp
  | cons i B ih =>
    intro hall
    have hi : a < i := hall i (List.mem_cons_self ..)
    have hrest := ih (by
      intro j hj
      exact hall j (List.mem_cons_of_mem _ hj))
    have hj1 : 1 ≤ i - a := by omega
    have hpt := pt_dvd_of_dvd a p hd (i - a) hj1
    have hptmod : pt a (i - a) % p = 0 := Nat.mod_eq_zero_of_dvd hpt
    have hpu : sumP a (i :: B) = pt a (i - a) + sumP a B := rfl
    show sumP a (i :: B) % p = 0
    rw [hpu, Nat.add_mod, hptmod, hrest, Nat.zero_add, Nat.zero_mod]

/-- If `p ∣ a + 1` (p ≥ 2), then `1 + Σ P ≡ 1 (mod p)`: the unit factor. -/
theorem sumP_unit_mod (a p : Nat) (hp : 2 ≤ p) (hd : p ∣ a + 1)
    (B : List Nat) (hB : ∀ i ∈ B, a < i) :
    (1 + sumP a B) % p = 1 := by
  have h0 := sumP_mod_zero a p hd B hB
  rw [Nat.add_mod, h0, Nat.add_zero, Nat.mod_mod]
  exact Nat.mod_eq_of_lt (by omega)

/-- **THEOREM B (Erdős #404, the `p ∣ a+1` class, every prime p).**
For every p ≥ 2 with `p ∣ a + 1` and every finite index list B beyond a:

    v_p (a! + Σ_{i ∈ B} i!)  =  v_p (a!).

The p-adic valuation NEVER grows.  Consequently
`f(a,p) = v_p(a!)` exactly on the class — e.g. f(p−1, p) for every prime p,
and (at p = 2) every odd a.  Primality is never used: the theorem holds for
every integer p ≥ 2 dividing a+1. -/
theorem erdos404_theoremB (a p : Nat) (hp : 2 ≤ p) (hd : p ∣ a + 1)
    (B : List Nat) (hB : ∀ i ∈ B, a < i) :
    vpad p (fact a + sumF B) = vpad p (fact a) := by
  have hsplit : fact a + sumF B = fact a * (1 + sumP a B) :=
    sumF_split a B hB
  have hu1 : (1 + sumP a B) % p = 1 := sumP_unit_mod a p hp hd B hB
  rw [hsplit, vpad_congr_unit (fact a) p (fact a) (1 + sumP a B)
    (Nat.le_refl (fact a)) hp (fact_pos a) (by omega) hu1]

-- ===========================================================================
-- §4  THE p = 2 STRUCTURE ALGEBRA (doc §3: Theorems BI + CU)
-- ===========================================================================

/-- **Block pair** (doc §3 Theorem BI): `[u, u+1] = u! · (u+2)` — the exact
factorization whose valuation law is the Kill-#4 kernel law (cited). -/
theorem erdos404_block_pair (u : Nat) :
    fact u + fact (u + 1) = fact u * (u + 2) := by
  have h1 : fact (u + 1) = (u + 1) * fact u := rfl
  have h2 : fact u + (u + 1) * fact u = fact u * (1 + (u + 1)) := by
    rw [Nat.mul_comm (u + 1) (fact u), Nat.mul_add (fact u) 1 (u + 1),
        Nat.mul_one (fact u)]
  have h3 : 1 + (u + 1) = u + 2 := by omega
  rw [h1, h2, h3]

/-- **Block triple** (doc §3 Theorem BI): `[u, u+2] = u! · (u+2)²` — the
perfect-square factorization of the 3-block. -/
theorem erdos404_block_triple (u : Nat) :
    fact u + fact (u + 1) + fact (u + 2) = fact u * ((u + 2) * (u + 2)) := by
  have e1 : fact (u + 1) = fact u * pt u 1 := fact_pt 1 u
  have e2 : fact (u + 2) = fact u * pt u 2 := fact_pt 2 u
  have p1 : pt u 1 = u + 1 := by
    have h : pt u 1 = 1 * (u + 1) := rfl
    rw [h, Nat.one_mul]
  have p2 : pt u 2 = (u + 1) * (u + 2) := by
    have h : pt u 2 = pt u 1 * (u + 1 + 1) := rfl
    have hq : u + 1 + 1 = u + 2 := by omega
    rw [h, p1, hq]
  have hexp : (u + 1) * (u + 2) = u * u + 3 * u + 2 := by
    have s1 : (u + 1) * (u + 2) = u * (u + 2) + (u + 2) :=
      Nat.succ_mul u (u + 2)
    have s2 : u * (u + 2) = u * u + u * 2 := Nat.mul_add u u 2
    have s3 : u * 2 = 2 * u := Nat.mul_comm u 2
    rw [s1, s2, s3]
    omega
  have hexp2 : (u + 2) * (u + 2) = u * u + 4 * u + 4 := by
    have s1 : (u + 2) * (u + 2) = u * (u + 2) + 2 * (u + 2) := by
      rw [Nat.mul_add (u + 2) u 2, Nat.mul_comm (u + 2) u,
          Nat.mul_comm (u + 2) 2]
    have s2 : u * (u + 2) = u * u + u * 2 := Nat.mul_add u u 2
    have s3 : u * 2 = 2 * u := Nat.mul_comm u 2
    have s4 : 2 * (u + 2) = 2 * u + 2 * 2 := Nat.mul_add 2 u 2
    rw [s1, s2, s3, s4]
    omega
  have split : fact u + fact (u + 1) + fact (u + 2)
      = fact u * (1 + pt u 1 + pt u 2) := by
    rw [e1, e2,
        Nat.mul_add (fact u) (1 + pt u 1) (pt u 2),
        Nat.mul_add (fact u) 1 (pt u 1),
        Nat.mul_one (fact u)]
  have hbr : 1 + (u + 1) + (u + 1) * (u + 2) = (u + 2) * (u + 2) := by
    rw [hexp, hexp2]
    omega
  rw [split, p1, p2, hbr]

/-- **The cube identity** (doc §3 Theorem CU):
`1 + P_{a+1} + P_{a+3} = 1 + (a+1) + (a+1)(a+2)(a+3) = (a+2)³`. -/
theorem erdos404_cube_identity (a : Nat) :
    1 + pt a 1 + pt a 3 = (a + 2) * (a + 2) * (a + 2) := by
  have p1 : pt a 1 = a + 1 := by
    have h : pt a 1 = 1 * (a + 1) := rfl
    rw [h, Nat.one_mul]
  have p2 : pt a 2 = (a + 1) * (a + 2) := by
    have h : pt a 2 = pt a 1 * (a + 1 + 1) := rfl
    have hq : a + 1 + 1 = a + 2 := by omega
    rw [h, p1, hq]
  have p3 : pt a 3 = (a + 1) * (a + 2) * (a + 3) := by
    have h : pt a 3 = pt a 2 * (a + 2 + 1) := rfl
    have hq : a + 2 + 1 = a + 3 := by omega
    rw [h, p2, hq]
  rw [p1, p3]
  ring

/-- **The cube bound** (doc §3 Theorem CU's valuation form, a §8.4 universal
law): the two-coin subset B = {a+1, a+3} achieves
`v₂(1 + Σ P) = 3 · v₂(a+2)` — i.e. `g(a,2) ≥ 3·v₂(a+2)` for every a. -/
theorem erdos404_cube_bound (a : Nat) :
    v2 (1 + sumP a [a + 1, a + 3]) = 3 * v2 (a + 2) := by
  have e : sumP a [a + 1, a + 3] = pt a 1 + pt a 3 := by
    show pt a (a + 1 - a) + (pt a (a + 3 - a) + 0) = pt a 1 + pt a 3
    have h1 : a + 1 - a = 1 := by omega
    have h3 : a + 3 - a = 3 := by omega
    rw [h1, h3]
    omega
  have hbr : 1 + sumP a [a + 1, a + 3] = 1 + pt a 1 + pt a 3 := by
    rw [e]
    omega
  rw [hbr, erdos404_cube_identity]
  have hpos : 1 ≤ a + 2 := by omega
  have hm1 : v2 ((a + 2) * (a + 2) * (a + 2)) = v2 ((a + 2) * (a + 2)) + v2 (a + 2) :=
    v2_mul ((a + 2) * (a + 2) + (a + 2)) ((a + 2) * (a + 2)) (a + 2)
      (Nat.le_refl _) hpos hpos
  have hm2 : v2 ((a + 2) * (a + 2)) = v2 (a + 2) + v2 (a + 2) :=
    v2_mul ((a + 2) + (a + 2)) (a + 2) (a + 2)
      (Nat.le_refl _) hpos hpos
  omega

-- ===========================================================================
-- §5  THE EXACT ANCHOR WITNESSES (doc §5: f(2,2) = 254 / f(6,2) = 133,
--     the LOWER-BOUND components — the upper bounds are the cited green
--     finals erdos404_f22_final / erdos404_f62_final)
-- ===========================================================================

set_option maxRecDepth 65536

/-- The 118-element witness `B ⊆ [3, 254]` of Kernel 10 (ExactF22.lean). -/
def witnessB22 : List Nat :=
  [3, 5, 6, 7, 11, 12, 15, 16, 19, 21, 22, 24, 25, 27, 31, 33, 34, 36, 39, 41,
   42, 44, 46, 48, 52, 55, 56, 57, 60, 62, 63, 65, 67, 68, 69, 70, 71, 74, 76,
   77, 78, 80, 81, 82, 84, 85, 86, 88, 89, 91, 93, 94, 95, 96, 99, 104, 107,
   110, 111, 117, 118, 121, 123, 126, 129, 130, 134, 136, 139, 141, 143, 144,
   145, 147, 148, 149, 157, 158, 161, 164, 166, 167, 168, 169, 170, 173, 178,
   183, 184, 187, 189, 191, 198, 200, 202, 206, 207, 208, 211, 215, 217, 219,
   221, 222, 223, 224, 225, 226, 227, 235, 237, 240, 241, 244, 245, 249, 250,
   254]

/-- The witness sum at anchor 2 (seed 2! = 2). -/
def sumFacts22 : List Nat → Nat
  | [] => 2
  | i :: is => fact i + sumFacts22 is

theorem sumFacts22_eq (l : List Nat) : sumFacts22 l = 2 + (l.map fact).sum := by
  induction l with
  | nil => rfl
  | cons x xs ih => rw [sumFacts22, List.map_cons, List.sum_cons, ih]; omega

/-- The 61-element witness `B₆ ⊆ [7, 135]` of Kernel 12 (ExactF62.lean). -/
def witnessB62 : List Nat :=
  [7, 8, 13, 16, 19, 22, 28, 30, 31, 34, 35, 36, 38, 40, 41, 45, 46, 48,
   52, 53, 54, 55, 57, 61, 62, 64, 65, 70, 71, 73, 75, 78, 81, 87, 88, 91,
   92, 93, 95, 96, 101, 103, 104, 107, 108, 109, 111, 112, 114, 115, 117,
   118, 119, 120, 125, 127, 128, 129, 130, 132, 135]

/-- The witness sum at anchor 6 (seed 6! = 720). -/
def sumFacts62 : List Nat → Nat
  | [] => 720
  | i :: is => fact i + sumFacts62 is

theorem sumFacts62_eq (l : List Nat) : sumFacts62 l = 720 + (l.map fact).sum := by
  induction l with
  | nil => rfl
  | cons x xs ih => rw [sumFacts62, List.map_cons, List.sum_cons, ih]; omega

/-- **The f(2,2) witness (doc §5, Theorem F22 lower bound).** The explicit
118-element set B ⊆ [3,254] with `v₂(2! + Σ_{i∈B} i!) = 254`, kernel-decided.
(With the cited green upper bound — Kernel 10's `erdos404_f22_final`, CI run
41909053106 — this is exactly f(2,2) = 254.) -/
theorem erdos404_f22_witness : v2 (2 + (witnessB22.map fact).sum) = 254 := by
  rw [← sumFacts22_eq witnessB22]
  have h1 : 2 ^ 254 ∣ sumFacts22 witnessB22 := by decide
  have h2 : ¬ 2 ^ 255 ∣ sumFacts22 witnessB22 := by decide
  have hn : 1 ≤ sumFacts22 witnessB22 := by decide
  have hle : 254 ≤ v2 (sumFacts22 witnessB22) :=
    v2_max (sumFacts22 witnessB22) (sumFacts22 witnessB22) 254 (Nat.le_refl _) hn h1
  have hge : v2 (sumFacts22 witnessB22) ≤ 254 := by
    cases Nat.lt_or_ge (v2 (sumFacts22 witnessB22)) 255 with
    | inl h => omega
    | inr h =>
        exfalso
        have hd0 : 2 ^ (v2 (sumFacts22 witnessB22)) ∣ sumFacts22 witnessB22 :=
          v2_dvd (sumFacts22 witnessB22) (sumFacts22 witnessB22) (v2 (sumFacts22 witnessB22))
            (Nat.le_refl _) hn rfl
        have hd1 : 2 ^ 255 ∣ 2 ^ (v2 (sumFacts22 witnessB22)) := Nat.pow_dvd_pow 2 h
        exact h2 (Nat.dvd_trans hd1 hd0)
  omega

/-- **The f(6,2) witness (doc §5, Theorem F62 lower bound).** The explicit
61-element set B₆ ⊆ [7,135] with `v₂(6! + Σ_{i∈B₆} i!) = 133`, kernel-decided.
(With the cited green upper bound — Kernel 14's `erdos404_f62_final`, CI run
42119256613 — this is exactly f(6,2) = 133.) -/
theorem erdos404_f62_witness : v2 (720 + (witnessB62.map fact).sum) = 133 := by
  rw [← sumFacts62_eq witnessB62]
  have h1 : 2 ^ 133 ∣ sumFacts62 witnessB62 := by decide
  have h2 : ¬ 2 ^ 134 ∣ sumFacts62 witnessB62 := by decide
  have hn : 1 ≤ sumFacts62 witnessB62 := by decide
  have hle : 133 ≤ v2 (sumFacts62 witnessB62) :=
    v2_max (sumFacts62 witnessB62) (sumFacts62 witnessB62) 133 (Nat.le_refl _) hn h1
  have hge : v2 (sumFacts62 witnessB62) ≤ 133 := by
    cases Nat.lt_or_ge (v2 (sumFacts62 witnessB62)) 134 with
    | inl h => omega
    | inr h =>
        exfalso
        have hd0 : 2 ^ (v2 (sumFacts62 witnessB62)) ∣ sumFacts62 witnessB62 :=
          v2_dvd (sumFacts62 witnessB62) (sumFacts62 witnessB62) (v2 (sumFacts62 witnessB62))
            (Nat.le_refl _) hn rfl
        have hd1 : 2 ^ 134 ∣ 2 ^ (v2 (sumFacts62 witnessB62)) := Nat.pow_dvd_pow 2 h
        exact h2 (Nat.dvd_trans hd1 hd0)
  omega

-- ===========================================================================
-- §6  THE COMPACTNESS Q3-BRIDGE (doc §1 Theorem A4's engine + §7)
-- ===========================================================================

/-- The partial sum of the first k+1 chain factorials:
`chainSum s k = Σ_{i ≤ k} (s i)!`. -/
def chainSum (s : Nat → Nat) : Nat → Nat
  | 0 => fact (s 0)
  | k + 1 => fact (s (k + 1)) + chainSum s k

/-- The chain's tail-index list: `chainTail s k = [s k, …, s 1]`. -/
def chainTail (s : Nat → Nat) : Nat → List Nat
  | 0 => []
  | k + 1 => s (k + 1) :: chainTail s k

theorem chainSum_eq (s : Nat → Nat) :
    ∀ (k : Nat), chainSum s k = fact (s 0) + sumF (chainTail s k)
  | 0 => rfl
  | k + 1 => by
      have h1 : chainSum s (k + 1) = fact (s (k + 1)) + chainSum s k := rfl
      have h2 : sumF (chainTail s (k + 1))
          = fact (s (k + 1)) + sumF (chainTail s k) := rfl
      rw [h1, h2, chainSum_eq s k]
      omega

theorem chainTail_mem (s : Nat → Nat) (hmono : ∀ i j, i < j → s i < s j) :
    ∀ (k i : Nat), i ∈ chainTail s k → s 0 < i := by
  intro k
  induction k with
  | zero => intro i hi; simp [chainTail, List.not_mem_nil] at hi
  | succ k ih =>
    intro i hi
    cases List.mem_cons.mp hi with
    | inl heq =>
      rw [heq]
      exact hmono 0 (k + 1) (by omega)
    | inr hmem => exact ih i hmem

/-- **THE COMPACTNESS Q3-BRIDGE** (doc §1 Theorem A4's engine, §7's verdict
mechanism): if EVERY admissible sum at (a, p) has valuation ≤ K (i.e.
g(a,p) < ∞ in list form), then NO infinite chain a = a₁ < a₂ < ··· with
partial-sum valuations m_k → ∞ exists at (a, p) — sub-question 3 is
answered NO at (a, p).  This is the contrapositive engine that converts
every finite certificate into a negative Q3 verdict. -/
theorem erdos404_no_infinite_chain (a p K : Nat) (hp : 2 ≤ p)
    (hbound : ∀ B : List Nat, (∀ i ∈ B, a < i) → vpad p (fact a + sumF B) ≤ K) :
    ¬ ∃ s : Nat → Nat, s 0 = a ∧ (∀ i j, i < j → s i < s j) ∧
      (∀ M, ∃ k0, ∀ k ≥ k0, M ≤ vpad p (chainSum s k)) := by
  intro ⟨s, hs0, hmono, hdiv⟩
  have hle : ∀ k, vpad p (chainSum s k) ≤ K := by
    intro k
    have hsplit : chainSum s k = fact (s 0) + sumF (chainTail s k) :=
      chainSum_eq s k
    have hadm : ∀ i ∈ chainTail s k, a < i := by
      intro i hi
      have hlt : s 0 < i := chainTail_mem s hmono k i hi
      omega
    have hseed : fact (s 0) = fact a := by rw [hs0]
    have hb := hbound (chainTail s k) hadm
    rw [← hseed, ← hsplit] at hb
    exact hb
  obtain ⟨k0, hk0⟩ := hdiv (K + 1)
  have h1 := hle k0
  have h2 := hk0 k0 (Nat.le_refl k0)
  omega

-- ===========================================================================
-- §7  THE MASTER THEOREM (doc §8 + §12: the complete partial structure
--     theorem of f(a,p) — every closed class, every universal law, the
--     exact anchors' witnesses, and the compactness bridge, ONE
--     unconditional conjunction, no sub-cases)
-- ===========================================================================

/-- **THE MASTER CLASSIFICATION THEOREM of Erdős #404** — the doc's final
section, formalized: (1) the master reduction (Theorem A, all primes);
(2) its p = 2 instance; (3) the Theorem-B class (p ∣ a+1, every p ≥ 2);
(4) the residual-tail class law and (5) the m = 3 window (Kernel 37's own
theorems, cited via import, verbatim); (6)–(7) the block-identity structure
theory; (8)–(9) the cube identity and its universal lower bound; (10)–(11)
the exact anchor witnesses f(2,2) = 254, f(6,2) = 133 (upper bounds: the
cited green finals); (12) the compactness Q3-bridge. -/
theorem erdos404_full_classification :
    -- (1) THE MASTER REDUCTION (Theorem A / Corollary A1, every prime p):
    (∀ (a p : Nat), Nat.Prime p → ∀ (B : List Nat), (∀ i ∈ B, a < i) →
        fact a + sumF B = fact a * (1 + sumP a B)
          ∧ vpad p (fact a + sumF B) = vpad p (fact a) + vpad p (1 + sumP a B))
    -- (2) Theorem A at p = 2 (Kernel 5's split):
    ∧ (∀ (a : Nat) (B : List Nat), (∀ i ∈ B, a < i) →
        v2 (fact a + sumF B) = v2 (fact a) + v2 (1 + sumP a B))
    -- (3) THEOREM B: the p ∣ a+1 class (Kernel 11):
    ∧ (∀ (a p : Nat), 2 ≤ p → p ∣ a + 1 → ∀ (B : List Nat), (∀ i ∈ B, a < i) →
        vpad p (fact a + sumF B) = vpad p (fact a))
    -- (4) THE RESIDUAL-TAIL CLASS LAW (Kernel 37, CITED verbatim):
    ∧ (∀ (m p : Nat), 3 ≤ m → Nat.Prime p → (m - 1) * fact (m - 1) + 1 < p →
        ∀ (a : Nat), 1 ≤ a → (a + m) % p = 0 →
        ∀ (B : List Nat), B.Nodup → (∀ i ∈ B, a < i) →
        vpad p (fact a + sumF B) = vpad p (fact a))
    -- (5) THE m = 3 WINDOW (Kernel 37, CITED verbatim):
    ∧ (∀ (p : Nat), Nat.Prime p → 7 ≤ p → ∀ (a : Nat), 1 ≤ a → (a + 3) % p = 0 →
        ∀ (B : List Nat), B.Nodup → (∀ i ∈ B, a < i) →
        vpad p (fact a + sumF B) = vpad p (fact a))
    -- (6) block pair: [u, u+1] = u!·(u+2):
    ∧ (∀ (u : Nat), fact u + fact (u + 1) = fact u * (u + 2))
    -- (7) block triple: [u, u+2] = u!·(u+2)²:
    ∧ (∀ (u : Nat), fact u + fact (u + 1) + fact (u + 2)
        = fact u * ((u + 2) * (u + 2)))
    -- (8) the cube identity: 1 + P_{a+1} + P_{a+3} = (a+2)³:
    ∧ (∀ (a : Nat), 1 + pt a 1 + pt a 3 = (a + 2) * (a + 2) * (a + 2))
    -- (9) the cube bound: g(a,2) ≥ 3·v₂(a+2):
    ∧ (∀ (a : Nat), v2 (1 + sumP a [a + 1, a + 3]) = 3 * v2 (a + 2))
    -- (10) THE EXACT ANCHOR f(2,2) = 254, witness half (upper bound cited
    --     to Kernel 10's erdos404_f22_final, CI 41909053106):
    ∧ v2 (2 + (witnessB22.map fact).sum) = 254
    -- (11) THE EXACT ANCHOR f(6,2) = 133, witness half (upper bound cited
    --     to Kernel 14's erdos404_f62_final, CI 42119256613):
    ∧ v2 (720 + (witnessB62.map fact).sum) = 133
    -- (12) THE COMPACTNESS Q3-BRIDGE (finite g ⟹ NO infinite chain):
    ∧ (∀ (a p K : Nat), 2 ≤ p →
        (∀ B : List Nat, (∀ i ∈ B, a < i) → vpad p (fact a + sumF B) ≤ K) →
        ¬ ∃ s : Nat → Nat, s 0 = a ∧ (∀ i j, i < j → s i < s j) ∧
          (∀ M, ∃ k0, ∀ k ≥ k0, M ≤ vpad p (chainSum s k))) :=
  ⟨erdos404_theoremA, erdos404_split, erdos404_theoremB,
   erdos404_residual_tail, erdos404_class_p_minus_3,
   erdos404_block_pair, erdos404_block_triple,
   erdos404_cube_identity, erdos404_cube_bound,
   erdos404_f22_witness, erdos404_f62_witness,
   erdos404_no_infinite_chain⟩

end Erdos404Full

-- ===========================================================================
-- §8  RECEIPTS (the CI greps these)
-- ===========================================================================

-- The witness receipts (kernel/compiler-evaluated):
#eval Erdos404Full.witnessB22.length                                   -- 118
#eval Erdos404Full.v2 (Erdos404Full.sumFacts22 Erdos404Full.witnessB22) -- 254
#eval Erdos404Full.witnessB62.length                                   -- 61
#eval Erdos404Full.v2 (Erdos404Full.sumFacts62 Erdos404Full.witnessB62) -- 133
-- Theorem A receipts (p = 2): the f(4,2) witness 4!+5!+7! = 5184 = 2⁶·81
-- (Theorem C — cited green in PadicReduction.lean as `erdos404_f42`):
#eval Erdos404Full.v2 (fact 4 + sumF [5, 7])                           -- 6

-- The axiom gates (this file's board):
#print axioms Erdos404Full.erdos404_theoremA
#print axioms Erdos404Full.erdos404_split
#print axioms Erdos404Full.erdos404_theoremB
#print axioms Erdos404Full.erdos404_block_pair
#print axioms Erdos404Full.erdos404_block_triple
#print axioms Erdos404Full.erdos404_cube_identity
#print axioms Erdos404Full.erdos404_cube_bound
#print axioms Erdos404Full.erdos404_f22_witness
#print axioms Erdos404Full.erdos404_f62_witness
#print axioms Erdos404Full.erdos404_no_infinite_chain
#print axioms Erdos404Full.erdos404_full_classification

-- The CITED green kernels (imported from ResidualTail.lean — Kernel 37):
#print axioms erdos404_residual_tail
#print axioms erdos404_class_p_minus_3
#print axioms erdos404t_arsenal_bridge

#eval "ERDOS404_FULL_KERNEL_GREEN"
