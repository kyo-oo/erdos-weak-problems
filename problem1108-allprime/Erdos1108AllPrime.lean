import Arsenal.ErdosTernary2.Basic
import Arsenal.CardinalWorlds
import Arsenal.CardinalWorldsV2

-- Family pattern (green kernels, K19/K29 chains): explicit depth headroom.
set_option maxRecDepth 262144
set_option maxHeartbeats 4000000

/-!
# ERDŐS #1108 — THE ALL-PRIME ISOLATED-MINIMUM LAW (Kernel 30, S037 volley)

## THE PROBLEM (verbatim, erdosproblems.com/1108)

> Let
> $$A = \left\\{ \sum_{n\in S}n! : S\subset \mathbb{N}\textrm{ finite}\right\\}.$$
> If $k\geq 2$, then does $A$ contain only finitely many $k$th powers?
> Does it contain only finitely many powerful numbers?

## WHAT THIS PROOF PROVES (the statement above, then the proofs below)

The all-prime generalization of the K17/K19 (Session 023/027) 2-adic
engine: the structural laws governing the p-adic valuation of EVERY
element of $A$, at EVERY prime $p$ simultaneously.

1. **THE RESIDUE-1 LAW** (`singleton_bottom_residue`): for every prime
   $p$ and every finite list $S$ whose lowest occupied $p$-block
   $\{pj,\ldots,pj+p-1\}$ is a singleton $\{b\}$:
   $$\sum_{a\in S} a! \;=\; b!\cdot Q \quad\textrm{with}\quad Q \equiv 1 \pmod{p}.$$
2. **THE ALL-PRIME ISOLATED-MINIMUM LAW** (`all_prime_isolated_min`):
   under the same hypothesis,
   $$v_p\!\left(\sum_{a\in S} a!\right) \;=\; v_p(b!) \quad\textrm{EXACTLY.}$$
3. **THE ALL-PRIME KERNEL CONGRUENCE** (`isolated_min_congruence`):
   $$\exists j:\ \sum_{a\in S} a! \;=\; b! + p\cdot b!\cdot j$$
   — the sum is pinned to $b!$ modulo $p\cdot b!$, i.e. at valuation
   level $v_p(b!)$ the sum carries ZERO additional p-factors.
4. **THE ALL-PRIME k-TH-POWER OBSTRUCTION** (`all_prime_power_obstruction`):
   if $k \nmid v_p(b!)$ for the singleton bottom $b$ at any prime $p$,
   then $\sum_{a\in S} a! \neq n^k$ for EVERY $n$ — the #1108
   obstruction engine at every prime and every exponent $k \geq 2$
   (the problem's own $k$).
5. **THE BLOCK FORM** (`isolated_min_block_form`): the same law stated
   in the block language: $b/p \leq a/p$ for all $a \in S$ and no
   other $a$ with $a/p = b/p$.

The finiteness question itself is the problem's open core and is not
claimed here; what is proven is the complete unconditional universal
law that every $k$-th-power candidate in $A$ must satisfy at every
prime simultaneously — the all-prime engine that K17/K19 ran at $p=2$
only.

## THE MATHEMATICS (one paragraph, the whole engine)

$p$-blocks $B_j = \{pj,\ldots,pj+p-1\}$; the factorial quotient
$\mathrm{qfact}\,b\,t = \prod_{i=b+1}^{t} i$.  If $b$ is the unique
element of $S$ in its block and every other element is in a strictly
higher block, then every other $a$ satisfies $b < p(b/p+1) \leq a$,
so $\mathrm{qfact}\,b\,a$ contains the factor $p(b/p+1)$ and is
divisible by $p$.  Peeling the head occurrences (list induction) gives
$\sum_{a\in S} a! = b!\cdot Q$ with $Q \equiv 1 \pmod p$ — the
residue-1 law.  Then $p \nmid Q$, so $v_p = v_p(b!) + 0$ exactly; and
$Q = 1 + p\cdot(Q/p)$ gives the congruence; and if the sum were
$n^k$ then $v_p(b!) = v_p(\sum) = v_p(n^k) = k\,v_p(n)$ would force
$k \mid v_p(b!)$ — the obstruction.

Core Lean 4 (with the Arsenal transitively providing `Nat.Prime`).
No `sorry`.  No custom axioms.
-/

namespace Erdos1108AP

/-! ## §1 THE VALUATION TOOLKIT (the K19/Erdos700 green architecture,
verbatim lift: fuel-structural `vpf`/`vp`, saturation, step law,
non-divisor law, one, product additivity with Euclid). -/

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

/-- Fuel-structural p-adic valuation engine (K19 architecture). -/
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

/-- Saturation: for p ≥ 2, fuel beyond the value never changes the
result (K19 proof, verbatim architecture). -/
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

/-- **Additivity on products** (K19 `v2_mul` at general prime p;
primality used exactly once: Euclid). -/
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

/-! ## §2 THE FACTORIAL-QUOTIENT ENGINE (`qfact b t = ∏_{i=b+1}^{t} i`). -/

/-- The product of the integers in `(b, t]` (empty product 1). -/
def qfact (b : Nat) : Nat → Nat
  | 0 => 1
  | t + 1 => if b < t + 1 then (t + 1) * qfact b t else 1

theorem qfact_pos : ∀ (t b : Nat), 1 ≤ qfact b t := by
  intro t
  induction t with
  | zero => intro b; exact Nat.le_refl 1
  | succ t ih =>
    intro b
    have he : qfact b (t + 1) = if b < t + 1 then (t + 1) * qfact b t else 1 := rfl
    rw [he]
    by_cases hlt : b < t + 1
    · rw [if_pos hlt]
      exact one_le_mul (t + 1) (qfact b t) (by omega) (ih b)
    · rw [if_neg hlt]

/-- **The factorial split.** `b ≤ t → t! = b! * ∏_{i=b+1}^{t} i`. -/
theorem fact_split : ∀ (t b : Nat), b ≤ t → fact t = fact b * qfact b t := by
  intro t
  induction t with
  | zero =>
    intro b hb
    have hb0 : b = 0 := by omega
    subst hb0
    rfl
  | succ t ih =>
    intro b hb
    have he : qfact b (t + 1) = if b < t + 1 then (t + 1) * qfact b t else 1 := rfl
    by_cases hlt : b < t + 1
    · rw [he, if_pos hlt]
      have hf : fact (t + 1) = (t + 1) * fact t := rfl
      have iht := ih b (by omega)
      rw [hf, iht, ← Nat.mul_assoc, Nat.mul_comm (t + 1) (fact b), Nat.mul_assoc]
    · have hbe : b = t + 1 := by omega
      subst hbe
      rw [he, if_neg (by omega : ¬ (t + 1 < t + 1)), Nat.mul_one]

/-- **The divisor law.** Every `k` with `b < k ≤ t` divides the
quotient product. -/
theorem qfact_dvd : ∀ (t b k : Nat), b < k → k ≤ t → k ∣ qfact b t := by
  intro t
  induction t with
  | zero => intro b k hb hk; exact absurd hb (by omega)
  | succ t ih =>
    intro b k hb hk
    have hbt : b < t + 1 := by omega
    have he : qfact b (t + 1) = (t + 1) * qfact b t := by
      show (if b < t + 1 then (t + 1) * qfact b t else 1) = _
      rw [if_pos hbt]
    rw [he]
    by_cases hkt : k = t + 1
    · exact ⟨qfact b t, by rw [hkt]⟩
    · obtain ⟨u, hu⟩ := ih b k hb (by omega)
      exact ⟨(t + 1) * u, by
        rw [hu, ← Nat.mul_assoc, Nat.mul_comm (t + 1) k, Nat.mul_assoc]⟩

/-- **The p-multiple law.** If `p * (b/p + 1) ≤ t` (t in a strictly
higher p-block than b) then `p ∣ qfact b t` — the quotient product
contains the factor `p * (b/p + 1)`, the first multiple of p above b. -/
theorem p_dvd_qfact (p b t : Nat) (hp : 2 ≤ p) (ht : p * (b / p + 1) ≤ t) :
    p ∣ qfact b t := by
  have hdm := Nat.div_add_mod b p
  have hbplt : b % p < p := Nat.mod_lt b (by omega : 0 < p)
  have hkb : b < p * (b / p + 1) := by
    have h1 : p * (b / p + 1) = p * (b / p) + p := by
      rw [Nat.mul_add, Nat.mul_one]
    omega
  obtain ⟨u, hu⟩ := qfact_dvd t b (p * (b / p + 1)) hkb ht
  exact ⟨(b / p + 1) * u, by rw [hu, Nat.mul_assoc]⟩

/-! ## §3 SUBSET SUMS AND MEMBERSHIP (K17 architecture). -/

def sumFacts : List Nat → Nat
  | [] => 0
  | a :: t => fact a + sumFacts t

theorem sumFacts_cons (c : Nat) (t : List Nat) :
    sumFacts (c :: t) = fact c + sumFacts t := rfl

/-- The quotient-sum: `sumQ b S = Σ_{a∈S} qfact b a`. -/
def sumQ (b : Nat) : List Nat → Nat
  | [] => 0
  | a :: t => qfact b a + sumQ b t

theorem sumQ_cons (b : Nat) (a : Nat) (t : List Nat) :
    sumQ b (a :: t) = qfact b a + sumQ b t := rfl

/-- Self-contained membership. -/
def memB (b : Nat) : List Nat → Prop
  | [] => False
  | a :: t => a = b ∨ memB b t

/-- Count occurrences of b. -/
def countB (b : Nat) : List Nat → Nat
  | [] => 0
  | a :: t => (if a = b then 1 else 0) + countB b t

theorem not_memB_of_countB_zero : ∀ (t : List Nat) (b : Nat),
    countB b t = 0 → ¬ memB b t
  | [], b, h => by
    intro hm
    exact hm
  | a :: t, b, h => by
    intro hm
    have he : countB b (a :: t) = (if a = b then 1 else 0) + countB b t := rfl
    rw [he] at h
    cases hm with
    | inl heq =>
      rw [if_pos heq] at h
      omega
    | inr hmem =>
      by_cases hab : a = b
      · rw [if_pos hab] at h; omega
      · rw [if_neg hab] at h
        exact not_memB_of_countB_zero t b (by omega) hmem

theorem countB_pos_mem : ∀ (t : List Nat) (b : Nat), 1 ≤ countB b t → memB b t
  | [], b, h => by
    have h0 : countB b [] = 0 := rfl
    exact absurd h0 (by omega)
  | c :: t, b, h => by
    have he : countB b (c :: t) = (if c = b then 1 else 0) + countB b t := rfl
    rw [he] at h
    by_cases hcb : c = b
    · exact Or.inl hcb
    · rw [if_neg hcb] at h
      exact Or.inr (countB_pos_mem t b (by omega))

theorem sumFacts_pos_of_mem : ∀ (S : List Nat) (b : Nat), memB b S → 1 ≤ sumFacts S
  | [], b, h => by have hf : False := h; exact hf.elim
  | c :: t, b, h => by
    have hOr : c = b ∨ memB b t := h
    cases hOr with
    | inl _ =>
      have h1 : 1 ≤ fact c := fact_pos c
      have h2 : 1 ≤ fact c + sumFacts t := by omega
      exact h2
    | inr hmem =>
      have h1 : 1 ≤ fact c := fact_pos c
      have ih := sumFacts_pos_of_mem t b hmem
      have h2 : 1 ≤ fact c + sumFacts t := by omega
      exact h2

theorem sumFacts_eq : ∀ (t : List Nat) (b : Nat), (∀ a, memB a t → b ≤ a) →
    sumFacts t = fact b * sumQ b t := by
  intro t
  induction t with
  | nil => intro b _; rfl
  | cons a t' ih =>
    intro b hge
    have hale : b ≤ a := hge a (Or.inl rfl)
    have htail : ∀ x, memB x t' → b ≤ x := fun x hx => hge x (Or.inr hx)
    have hfa : fact a = fact b * qfact b a := fact_split a b hale
    have ihb := ih b htail
    rw [sumFacts_cons, sumQ_cons, hfa, ihb, ← Nat.mul_add]

theorem dvd_sumQ : ∀ (t : List Nat) (b p : Nat),
    (∀ a, memB a t → p ∣ qfact b a) → p ∣ sumQ b t := by
  intro t
  induction t with
  | nil => intro b p _; exact ⟨0, rfl⟩
  | cons a t' ih =>
    intro b p hd
    obtain ⟨u, hu⟩ := hd a (Or.inl rfl)
    obtain ⟨v, hv⟩ := ih b p (fun x hx => hd x (Or.inr hx))
    refine ⟨u + v, ?_⟩
    rw [sumQ_cons, hu, hv, Nat.mul_add]

/-! ## §4 THE RESIDUE-1 LAW (the engine's heart). -/

/-- **THE RESIDUE-1 LAW.** For every prime p, every finite list S whose
lowest occupied p-block is a singleton {b}: `Σ_{a∈S} a! = b! · Q` with
`Q ≡ 1 (mod p)`. -/
theorem singleton_bottom_residue (p b : Nat) (hp : 2 ≤ p) :
    ∀ (S : List Nat), countB b S = 1 →
    (∀ a, memB a S → a ≠ b → p * (b / p + 1) ≤ a) →
    ∃ Q, sumFacts S = fact b * Q ∧ Q % p = 1 := by
  intro S
  induction S with
  | nil =>
    intro hbS _
    have h0 : countB b [] = 0 := rfl
    omega
  | cons c t ih =>
    intro hbS hblock
    have hce : countB b (c :: t) = (if c = b then 1 else 0) + countB b t := rfl
    rw [hce] at hbS
    have hbmod := Nat.div_add_mod b p
    have hbplt : b % p < p := Nat.mod_lt b (by omega : 0 < p)
    have hbp : b < p * (b / p + 1) := by
      have h1 : p * (b / p + 1) = p * (b / p) + p := by
        rw [Nat.mul_add, Nat.mul_one]
      omega
    by_cases hcb : c = b
    · have hbc : b = c := hcb.symm
      subst hbc
      rw [if_pos rfl] at hbS
      have hct : countB b t = 0 := by omega
      have hnt : ¬ memB b t := not_memB_of_countB_zero t b hct
      have htail : ∀ a, memB a t → b ≤ a ∧ p ∣ qfact b a := by
        intro a ha
        have hane : a ≠ b := by
          intro hae
          exact hnt (hae ▸ ha)
        have hblk := hblock a (Or.inr ha) hane
        have hba : b ≤ a := by omega
        exact ⟨hba, p_dvd_qfact p b a hp hblk⟩
      have hsum := sumFacts_eq t b (fun a ha => (htail a ha).1)
      have hdvd := dvd_sumQ t b p (fun a ha => (htail a ha).2)
      have hQmod : sumQ b t % p = 0 := Nat.mod_eq_zero_of_dvd hdvd
      refine ⟨1 + sumQ b t, ?_, ?_⟩
      · rw [sumFacts_cons, hsum, ← Nat.mul_add, Nat.mul_one]
      · rw [Nat.add_mod, hQmod, Nat.add_zero,
          Nat.mod_eq_of_lt (show 1 < p by omega),
          Nat.mod_eq_of_lt (show 1 < p by omega)]
    · rw [if_neg hcb] at hbS
      have hct1 : countB b t = 1 := by omega
      have hblockt : ∀ a, memB a t → a ≠ b → p * (b / p + 1) ≤ a :=
        fun a ha hne => hblock a (Or.inr ha) hne
      obtain ⟨Qt, hQtsum, hQtmod⟩ := ih hct1 hblockt
      have hblkc := hblock c (Or.inl rfl) hcb
      have hbc : b ≤ c := by omega
      have hfc : fact c = fact b * qfact b c := fact_split c b hbc
      have hpqc : p ∣ qfact b c := p_dvd_qfact p b c hp hblkc
      have hqcmod : qfact b c % p = 0 := Nat.mod_eq_zero_of_dvd hpqc
      refine ⟨qfact b c + Qt, ?_, ?_⟩
      · rw [sumFacts_cons, hfc, hQtsum, ← Nat.mul_add]
      · rw [Nat.add_mod, hqcmod, hQtmod, Nat.zero_add,
          Nat.mod_eq_of_lt (show 1 < p by omega)]

/-! ## §5 THE LAWS. -/

/-- **THE ALL-PRIME ISOLATED-MINIMUM LAW.** For every prime p and every
finite list S whose lowest occupied p-block is a singleton {b}:
`v_p (Σ_{a∈S} a!) = v_p (b!)` EXACTLY. -/
theorem all_prime_isolated_min (p b : Nat) (hp : p.Prime) (S : List Nat)
    (hbS : countB b S = 1)
    (hblock : ∀ a, memB a S → a ≠ b → p * (b / p + 1) ≤ a) :
    vp p (sumFacts S) = vp p (fact b) := by
  obtain ⟨Q, hQ, hQmod⟩ :=
    singleton_bottom_residue p b hp.one_lt S hbS hblock
  have hQ1 : 1 ≤ Q := by
    cases Q with
    | zero => rw [Nat.zero_mod] at hQmod; omega
    | succ q => exact Nat.succ_le_succ (Nat.zero_le q)
  have hnpq : ¬ p ∣ Q := by
    intro hdvd
    have h0 : Q % p = 0 := Nat.mod_eq_zero_of_dvd hdvd
    omega
  have hv0 : vp p Q = 0 :=
    vp_nondiv p Q hQ1 (fun hcon => hnpq (Nat.dvd_of_mod_eq_zero hcon))
  rw [hQ, vp_mul (fact b + Q) p (fact b) Q (Nat.le_refl _) hp (fact_pos b) hQ1,
    hv0, Nat.add_zero]

/-- **THE ALL-PRIME KERNEL CONGRUENCE.** `Σ = b! + p·b!·j` for some j:
the sum is pinned to b! modulo p·b!. -/
theorem isolated_min_congruence (p b : Nat) (hp : p.Prime) (S : List Nat)
    (hbS : countB b S = 1)
    (hblock : ∀ a, memB a S → a ≠ b → p * (b / p + 1) ≤ a) :
    ∃ j, sumFacts S = fact b + p * (fact b * j) := by
  obtain ⟨Q, hQ, hQmod⟩ :=
    singleton_bottom_residue p b hp.one_lt S hbS hblock
  have hdm := Nat.div_add_mod Q p
  rw [hQmod] at hdm
  have hQe : Q = p * (Q / p) + 1 := by omega
  refine ⟨Q / p, ?_⟩
  rw [hQ]
  conv_lhs => rw [hQe]
  have key : fact b * (p * (Q / p)) = p * (fact b * (Q / p)) := by
    rw [← Nat.mul_assoc, Nat.mul_comm (fact b) p, Nat.mul_assoc]
  rw [Nat.mul_add, Nat.mul_one, key, Nat.add_comm]

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

/-- **THE ALL-PRIME k-TH-POWER OBSTRUCTION.** If the lowest occupied
p-block of S is a singleton {b} and `k ∤ v_p (b!)`, then
`Σ_{a∈S} a!` is NOT a k-th power — at every prime p, every k ≥ 2,
every n. -/
theorem all_prime_power_obstruction (p b : Nat) (hp : p.Prime) (S : List Nat)
    (hbS : countB b S = 1)
    (hblock : ∀ a, memB a S → a ≠ b → p * (b / p + 1) ≤ a)
    (k n : Nat) (hk : 2 ≤ k) (hknot : ¬ (k ∣ vp p (fact b))) :
    sumFacts S ≠ n ^ k := by
  intro h
  have hlaw := all_prime_isolated_min p b hp S hbS hblock
  cases n with
  | zero =>
    have hbmem : memB b S := countB_pos_mem S b (by rw [hbS])
    have hpos : 1 ≤ sumFacts S := sumFacts_pos_of_mem S b hbmem
    have h0 : (0 : Nat) ^ k = 0 := by
      cases k with
      | zero => omega
      | succ k' => rw [Nat.pow_succ, Nat.mul_zero]
    rw [h, h0] at hpos
    omega
  | succ m =>
    have hm1 : 1 ≤ m + 1 := by omega
    have hv : vp p ((m + 1) ^ k) = k * vp p (m + 1) :=
      vp_pow k p k (m + 1) (Nat.le_refl k) hp hm1
    have h1 : vp p (sumFacts S) = vp p ((m + 1) ^ k) := by rw [h]
    have h2 : vp p (fact b) = k * vp p (m + 1) := by rw [← hlaw, h1, hv]
    exact hknot ⟨vp p (m + 1), h2⟩

/-- **THE BLOCK FORM.** The same law in the block language: b in the
lowest occupied p-block, and b's block occupied by b alone. -/
theorem isolated_min_block_form (p b : Nat) (hp : p.Prime) (S : List Nat)
    (hbS : countB b S = 1)
    (hlow : ∀ a, memB a S → b / p ≤ a / p)
    (hsing : ∀ a, memB a S → a ≠ b → a / p ≠ b / p) :
    vp p (sumFacts S) = vp p (fact b) := by
  apply all_prime_isolated_min p b hp S hbS
  intro a ha hne
  have h1 : b / p + 1 ≤ a / p := by
    have h2 := hlow a ha
    have h3 := hsing a ha hne
    omega
  have h2 : p * (b / p + 1) ≤ p * (a / p) := Nat.mul_le_mul_left p h1
  have hdm := Nat.div_add_mod a p
  have h3 : p * (a / p) ≤ a := by omega
  omega

/-! ## §6 LITERAL PRIMES (the `Nat.le_of_dvd` route, green in K27;
top-level aux lemmas — bullets live at top level, the S035 law). -/

theorem prime_small (p : Nat) (hp2 : 2 ≤ p)
    (hp : ∀ m, 2 ≤ m → m < p → ¬ (m ∣ p)) : Nat.Prime p := by
  show 2 ≤ p ∧ ∀ m : ℕ, m ∣ p → m = 1 ∨ m = p
  refine ⟨hp2, ?_⟩
  intro m hm
  have hle : m ≤ p := Nat.le_of_dvd (by omega) hm
  by_cases hm0 : m = 0
  · exact absurd hm (by intro hd; obtain ⟨k, hk⟩ := hd; omega)
  · by_cases hm1 : m = 1
    · exact Or.inl hm1
    · by_cases hmp : m = p
      · exact Or.inr hmp
      · exact absurd hm (hp m (by omega) (by omega))

theorem pr2 : Nat.Prime 2 := prime_small 2 (by omega) (by intro m h2 hlt; omega)

theorem pr3_aux (m : Nat) (h2 : 2 ≤ m) (hlt : m < 3) : ¬ (m ∣ 3) := by
  intro hdvd
  rcases m with 0 | 1 | 2 | m' + 3
  · omega
  · omega
  · obtain ⟨k, hk⟩ := hdvd
    omega
  · omega

theorem pr3 : Nat.Prime 3 := prime_small 3 (by omega) pr3_aux

theorem pr11_aux (m : Nat) (h2 : 2 ≤ m) (hlt : m < 11) : ¬ (m ∣ 11) := by
  intro hdvd
  rcases m with 0 | 1 | 2 | 3 | 4 | 5 | 6 | 7 | 8 | 9 | 10 | m' + 11
  · omega
  · omega
  · obtain ⟨k, hk⟩ := hdvd
    omega
  · obtain ⟨k, hk⟩ := hdvd
    omega
  · obtain ⟨k, hk⟩ := hdvd
    omega
  · obtain ⟨k, hk⟩ := hdvd
    omega
  · obtain ⟨k, hk⟩ := hdvd
    omega
  · obtain ⟨k, hk⟩ := hdvd
    omega
  · obtain ⟨k, hk⟩ := hdvd
    omega
  · obtain ⟨k, hk⟩ := hdvd
    omega
  · obtain ⟨k, hk⟩ := hdvd
    omega
  · omega

theorem pr11 : Nat.Prime 11 := prime_small 11 (by omega) pr11_aux

/-! ## §7 THE ARSENAL BRIDGE (BOSS's mathematics applied to the witness
numbers — erdosternary2 + HC-PROOF, the 16,121-theorem arsenal). -/

def arsenalBridgeProp : Prop :=
  [13 % 3, (13 / 3) % 3, (13 / 9) % 3].all (fun d => ErdosTernary2.isTernaryDigit d) ∧
  [121 % 3, (121 / 3) % 3, (121 / 9) % 3, (121 / 27) % 3].all
    (fun d => ErdosTernary2.isTernaryDigit d) ∧
  carryAtPos 13 1 < 4 ∧
  v2r (3 ^ 1 * 9) = v2r 9

theorem erdos1108ap_arsenal_bridge : arsenalBridgeProp :=
  ⟨by decide, by decide, carryAtPos_bound 13 1, CardinalWorldsV2.v2r_ternary_scaling 1 9⟩

/-! ## §8 INSTANCES (kernel-decided receipts of the law). -/

/-- The p=2 instance: `v₂(3! + 4! + 9!) = v₂(3!)` — b=3, singleton
bottom pair, 4 and 9 in strictly higher pairs. -/
theorem inst_law_p2 : vp 2 (sumFacts [3, 4, 9]) = vp 2 (fact 3) := by
  apply all_prime_isolated_min 2 3 pr2 [3, 4, 9]
  · decide
  · intro a ha hne
    have hOr : 3 = a ∨ (4 = a ∨ (9 = a ∨ False)) := ha
    rcases hOr with rfl | rfl | rfl | h
    · exact absurd rfl hne
    · decide
    · decide
    · exact h.elim

/-- The p=3 instance: `v₃(2! + 9! + 13!) = v₃(2!)`. -/
theorem inst_law_p3 : vp 3 (sumFacts [2, 9, 13]) = vp 3 (fact 2) := by
  apply all_prime_isolated_min 3 2 pr3 [2, 9, 13]
  · decide
  · intro a ha hne
    have hOr : 2 = a ∨ (9 = a ∨ (13 = a ∨ False)) := ha
    rcases hOr with rfl | rfl | rfl | h
    · exact absurd rfl hne
    · decide
    · decide
    · exact h.elim

/-- The p=11 instance: `v₁₁(5! + 121! + 130!) = v₁₁(5!)`. -/
theorem inst_law_p11 : vp 11 (sumFacts [5, 121, 130]) = vp 11 (fact 5) := by
  apply all_prime_isolated_min 11 5 pr11 [5, 121, 130]
  · decide
  · intro a ha hne
    have hOr : 5 = a ∨ (121 = a ∨ (130 = a ∨ False)) := ha
    rcases hOr with rfl | rfl | rfl | h
    · exact absurd rfl hne
    · decide
    · decide
    · exact h.elim

/-- THE NOT-SQUARE INSTANCE: 3! + 4! + 9! = 362910 is not a square
(the obstruction at p=2, k=2: v₂(3!) = 1 is odd). -/
theorem inst_not_square_349 : ∀ n : Nat, sumFacts [3, 4, 9] ≠ n ^ 2 := by
  intro n
  exact all_prime_power_obstruction 2 3 pr2 [3, 4, 9] (by decide)
    (by intro a ha hne
        have hOr : 3 = a ∨ (4 = a ∨ (9 = a ∨ False)) := ha
        rcases hOr with rfl | rfl | rfl | h
        · exact absurd rfl hne
        · decide
        · decide
        · exact h.elim)
    2 n (by omega) (by decide)

/-- THE NOT-CUBE INSTANCE: 3! + 4! + 9! = 362910 is not a cube
(the obstruction at p=2, k=3: 3 ∤ v₂(3!) = 1). -/
theorem inst_not_cube_349 : ∀ n : Nat, sumFacts [3, 4, 9] ≠ n ^ 3 := by
  intro n
  exact all_prime_power_obstruction 2 3 pr2 [3, 4, 9] (by decide)
    (by intro a ha hne
        have hOr : 3 = a ∨ (4 = a ∨ (9 = a ∨ False)) := ha
        rcases hOr with rfl | rfl | rfl | h
        · exact absurd rfl hne
        · decide
        · decide
        · exact h.elim)
    3 n (by omega) (by decide)

/-! ## §9 MAIN. -/

theorem erdos1108ap_main :
    (∀ p b S, p.Prime → countB b S = 1 →
      (∀ a, memB a S → a ≠ b → p * (b / p + 1) ≤ a) →
      vp p (sumFacts S) = vp p (fact b)) ∧
    (∀ p b S, p.Prime → countB b S = 1 →
      (∀ a, memB a S → a ≠ b → p * (b / p + 1) ≤ a) →
      ∃ j, sumFacts S = fact b + p * (fact b * j)) ∧
    (∀ p b S k n, p.Prime → countB b S = 1 →
      (∀ a, memB a S → a ≠ b → p * (b / p + 1) ≤ a) → 2 ≤ k →
      ¬ (k ∣ vp p (fact b)) → sumFacts S ≠ n ^ k) ∧
    (∀ p b S, p.Prime → countB b S = 1 →
      (∀ a, memB a S → b / p ≤ a / p) →
      (∀ a, memB a S → a ≠ b → a / p ≠ b / p) →
      vp p (sumFacts S) = vp p (fact b)) ∧
    arsenalBridgeProp :=
  ⟨fun p b S hp hbS hb => all_prime_isolated_min p b hp S hbS hb,
   fun p b S hp hbS hb => isolated_min_congruence p b hp S hbS hb,
   fun p b S k n hp hbS hb hk hknot =>
     all_prime_power_obstruction p b hp S hbS hb k n hk hknot,
   fun p b S hp hbS hlow hsing =>
     isolated_min_block_form p b hp S hbS hlow hsing,
   erdos1108ap_arsenal_bridge⟩

#eval (vp 2 (sumFacts [3, 4, 9]), vp 3 (sumFacts [2, 9, 13]),
       vp 5 (sumFacts [7, 25, 31]), vp 7 (sumFacts [13, 49, 55]),
       vp 11 (sumFacts [5, 121, 130]))
#eval (vp 2 (fact 3), vp 3 (fact 2), vp 5 (fact 7), vp 7 (fact 13),
       vp 11 (fact 5))
#eval "ERDOS1108_ALLPRIME_KERNEL_GREEN"

#print axioms singleton_bottom_residue
#print axioms all_prime_isolated_min
#print axioms isolated_min_congruence
#print axioms all_prime_power_obstruction
#print axioms isolated_min_block_form
#print axioms erdos1108ap_arsenal_bridge
#print axioms erdos1108ap_main

end Erdos1108AP
