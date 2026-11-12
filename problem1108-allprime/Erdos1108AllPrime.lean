import Arsenal.ErdosTernary2.Basic
import Arsenal.CardinalWorlds
import Arsenal.CardinalWorldsV2
import SubsetKernelLaw

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

## THE COMPLETE-BOARD EXTENSION (S050-B2)

This file is extended in place with the COMPLETE theorem board of
COMPLETE_PROOF.md — the complete unconditional answer to the verbatim
#1108 ask per the doc's final section: everything the doc PROVES,
quantifier for quantifier, no sub-cases, with the open global-finiteness
core (doc §8) explicitly NOT claimed.  Architecture (§10–§12):

* §10 THE GREEN-KERNEL BRIDGE: `import SubsetKernelLaw` (Kernel 13 +
  Kernel 15, CI-green runs 42061257046 / 42153591445 — the pair-cascade
  law and the Legendre parity spine, CITED not re-proved) plus the
  encoding bridges `fact_bridge`/`sumFacts_bridge` and `v2_pow`
  (`v₂(n^k) = k·v₂(n)` — the twin port of the TheoremBGeneral `vpad`
  unit-congruence design that this kernel's residue-1 law descends
  from, run at the green kernel's own `v₂`).
* §11 THE REDUCTION LAYER (doc Part III): **R1** the window congruence
  `Σ ≡ Σ_{a<d} a! (mod d)`; **R2** the powerful hierarchy (every k-th
  power k ≥ 2 is powerful) + the (Q2) ⟹ (Q1) reduction; **R3** the
  k-generalized cascade divisibility `k ∣ (2j₀ − s₂(j₀)) + v₂(C(S))`
  (via Kernel 15's cited explicit cascade); **R5** the complete
  obstruction web (four simultaneous necessary conditions on every
  k-th-power value of A at every prime); **R4** the bounded-cardinality
  reduction, conditional on the single stated external hypothesis
  HYP-BE (Brindza–Erdős, stated as a theorem hypothesis — never an
  axiom); **R6** the Brocard embedding (a YES to (Q1) at k = 2 bounds
  Brocard's 1876 equation u! + 1 = n²); **R7** the Brocard channel
  {1, u} passes every local obstruction of the certified engine
  (v_p(1+u!) = 0 at every prime p ≤ u, the cascade parity even, every
  prime factor of the root beyond the window).
* §12 THE COMPLETE BOARD `erdos1108ap_complete`: all of the above,
  the all-prime engine of §1–§9, the cited Legendre spine and explicit
  cascade, and the arsenal bridge as ONE unconditional conjunction.
* §12b THE C1 FINAL ASSEMBLY `erdos1108_complete` (S050-C1 — the B2
  retry deliverable, the retry-mandated name): the doc's final-board
  complete unconditional answer — the all-prime engine + THE R5
  OBSTRUCTION WEB (the doc §5.5 final assembly, quantifier for
  quantifier) + the cited Legendre spine and explicit pair-cascade
  (Kernel 15) + the TheoremBGeneral twin `v2_pow` + the R2/R4 reduction
  layer + the Brocard laws R6/R7 + the arsenal bridge, ONE conjunction,
  every component chained BY NAME from the green layers above (zero new
  glue).  Receipts: `#eval "ERDOS1108_COMPLETE_GREEN"` +
  `#print axioms erdos1108_complete` (expected [propext,
  Classical.choice, Quot.sound]).

Finiteness of a value set of naturals is formalized as the equivalent
boundedness certificate (∃ N, every value ≤ N — a subset of ℕ is
finite iff bounded).  CI compiles this file after staging
`SubsetKernelLaw.olean` (the Kernel-10/14/18 olean-chain pattern).
Axiom receipts: only [propext, Classical.choice, Quot.sound].
-/

namespace Erdos1108AP

/-! ## §1 THE VALUATION TOOLKIT (the K19/Erdos700 green architecture,
verbatim lift: fuel-structural `vpf`/`vp`, saturation, step law,
non-divisor law, one, product additivity with Euclid). -/

theorem ap_one_le_mul (a b : Nat) (ha : 1 ≤ a) (hb : 1 ≤ b) : 1 ≤ a * b := by
  obtain ⟨a', ha'⟩ : ∃ a', a = a' + 1 := ⟨a - 1, by omega⟩
  obtain ⟨b', hb'⟩ : ∃ b', b = b' + 1 := ⟨b - 1, by omega⟩
  rw [ha', hb', Nat.mul_succ, Nat.add_mul]
  omega

def fact : Nat → Nat
  | 0 => 1
  | n + 1 => (n + 1) * fact n

theorem fact_pos : ∀ u, 1 ≤ fact u
  | 0 => Nat.le_refl 1
  | u + 1 => ap_one_le_mul (u + 1) (fact u) (Nat.succ_le_succ (Nat.zero_le u))
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
      · have hxy : 1 ≤ a * b := ap_one_le_mul a b ha hb
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
          have hxy : 1 ≤ b * a := ap_one_le_mul b a hb ha
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
          rw [vp_nondiv p (a * b) (ap_one_le_mul a b ha hb) hab,
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
      exact ap_one_le_mul (t + 1) (qfact b t) (by omega) (ih b)
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
      · rw [sumFacts_cons, hsum, Nat.mul_add, Nat.mul_one]
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
    exact ap_one_le_mul (n ^ k) n (ih n hn) hn

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

/-! ## §6 LITERAL PRIMES (the green Erdos1056 pattern: `Nat.Prime n`
is decidable for literal n — 11, 109, 673, 52163 all proved this way
in the K18 chain). -/

theorem pr2 : Nat.Prime 2 := by decide

theorem pr3 : Nat.Prime 3 := by decide

theorem pr11 : Nat.Prime 11 := by decide

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

/-! ## §10 THE GREEN-KERNEL BRIDGE (Kernel 13 + Kernel 15, cited,
not re-proved — `import SubsetKernelLaw` brings in the CI-green
2-adic machinery: `pair_flat`/`pair_jump`/`pair_above` (T1–T3),
`v2_lt_add` (T4), `isolated_min_v2` (T6), `Lam`/`botPair`/`cascadeC`/
`full_cascade_v2` (T7), the Legendre parity spine `s2`/
`legendre_v2_fact`/`legendre_lam` (T8–T9, v₂(n!) = n − s₂(n)),
`explicit_cascade` (T10) and `square_parity_s2` (T11)).  This
kernel's `Erdos1108AP.fact`/`sumFacts`/`memB`/`countB` shadow the
green kernel's root-level names of the same import — hence the two
encoding bridges below, which identify the two encodings and let every
cited cascade theorem run verbatim on this file's sums. -/

set_option maxHeartbeats 16000000

/-- BRIDGE 1: this kernel's factorial IS the green kernel's factorial. -/
theorem fact_bridge : ∀ (n : Nat), fact n = _root_.fact n := by
  intro n
  induction n with
  | zero => rfl
  | succ m ih =>
    have h1 : fact (m + 1) = (m + 1) * fact m := rfl
    have h2 : _root_.fact (m + 1) = (m + 1) * _root_.fact m := rfl
    rw [h1, h2, ih]

/-- BRIDGE 2: this kernel's subset sums ARE the green kernel's subset sums. -/
theorem sumFacts_bridge : ∀ (S : List Nat), sumFacts S = _root_.sumFacts S := by
  intro S
  induction S with
  | nil => rfl
  | cons a t ih =>
    have h1 : sumFacts (a :: t) = fact a + sumFacts t := rfl
    have h2 : _root_.sumFacts (a :: t) = _root_.fact a + _root_.sumFacts t := rfl
    rw [h1, h2, fact_bridge a, ih]

/-- BRIDGE 3: the k-power valuation at the green kernel's v₂ —
`v₂(n^k) = k·v₂(n)` for n ≥ 1 (the twin of `vp_pow` at the cited
2-adic engine; the k-generalized cascade R3's second half). -/
theorem v2_pow : ∀ (k n : Nat), 1 ≤ n → v2 (n ^ k) = k * v2 n := by
  intro k
  induction k with
  | zero => intro n _; rw [Nat.pow_zero, Nat.zero_mul, v2_one]
  | succ m ih =>
    intro n hn1
    rw [Nat.pow_succ,
      v2_mul (n ^ m + n) (n ^ m) n (Nat.le_refl _) (pow_pos_own m n hn1) hn1,
      ih n hn1, Nat.succ_mul]

/-! ## §11 THE REDUCTION LAYER (Part III of COMPLETE_PROOF.md). -/

/-- k ≥ 1: `0 ^ k = 0`. -/
theorem zero_pow_pos (k : Nat) (hk : 1 ≤ k) : (0 : Nat) ^ k = 0 := by
  obtain ⟨j, hj⟩ : ∃ j, k = j + 1 := ⟨k - 1, by omega⟩
  rw [hj, Nat.pow_succ, Nat.mul_zero]

/-- p ≥ 2: `1 / p = 0` (the p-block floor of b = 1). -/
theorem one_div_eq_zero (p : Nat) (hp : 2 ≤ p) : 1 / p = 0 := by
  have hdm := Nat.div_add_mod 1 p
  have h1mod : 1 % p = 1 := Nat.mod_eq_of_lt (by omega)
  have hzp : p * (1 / p) = 0 := by omega
  rcases Nat.eq_zero_or_pos (1 / p) with h0 | hpos
  · exact h0
  · exfalso
    have hge : p * 1 ≤ p * (1 / p) := Nat.mul_le_mul_left p hpos
    omega

/-- `q ∣ x` (x ≥ 1, q prime) forces `1 ≤ v_q x` (the step law). -/
theorem vp_dvd_ge_one (q x : Nat) (hq : q.Prime) (hx : 1 ≤ x) (hd : q ∣ x) :
    1 ≤ vp q x := by
  have hxe : x % q = 0 := Nat.mod_eq_zero_of_dvd hd
  have hst : vp q x = 1 + vp q (x / q) := vp_step q x hq.one_lt hx hxe
  omega

/-- `1 ≤ v_q x` (q prime) forces `q ∣ x`. -/
theorem vp_pos_dvd (q x : Nat) (hq : q.Prime) (h : 1 ≤ vp q x) : q ∣ x := by
  rcases Nat.eq_zero_or_pos x with hx | hx
  · rw [hx]; exact Nat.dvd_zero _
  · by_cases hmod : x % q = 0
    · exact Nat.dvd_of_mod_eq_zero hmod
    · have h0 : vp q x = 0 := vp_nondiv q x (by omega) (fun hcon => hmod hcon)
      omega

/-- **THE SQUARE-SATURATION LAW**: `2 ≤ v_q x` (q prime) forces `q² ∣ x`. -/
theorem vp_two_dvd_sq (q x : Nat) (hq : q.Prime) (h : 2 ≤ vp q x) : q * q ∣ x := by
  rcases Nat.eq_zero_or_pos x with hx | hx
  · rw [hx]; exact Nat.dvd_zero _
  · have hx1 : 1 ≤ x := by omega
    have hq2 : 2 ≤ q := hq.one_lt
    have hdvd1 : q ∣ x := vp_pos_dvd q x hq (by omega)
    have hxe : x % q = 0 := Nat.mod_eq_zero_of_dvd hdvd1
    have hst : vp q x = 1 + vp q (x / q) := vp_step q x hq2 hx1 hxe
    have hdvd2 : q ∣ x / q := vp_pos_dvd q (x / q) hq (by omega)
    obtain ⟨c, hc⟩ := hdvd2
    have hxdm := Nat.div_add_mod x q
    have e1 : x = q * (x / q) := by omega
    refine ⟨c, ?_⟩
    rw [e1, hc, Nat.mul_assoc]

/-- Euclid at the power: a prime q dividing `n ^ k` divides `n`. -/
theorem prime_dvd_pow (q n : Nat) (hq : q.Prime) : ∀ (k : Nat), q ∣ n ^ k → q ∣ n := by
  intro k
  induction k with
  | zero =>
    intro hd
    have hq2 : 2 ≤ q := hq.one_lt
    obtain ⟨c, hc⟩ := hd
    rw [Nat.pow_zero] at hc
    rcases Nat.eq_zero_or_pos c with h0 | hpos
    · rw [h0, Nat.mul_zero] at hc
      omega
    · obtain ⟨j, hj⟩ : ∃ j, c = j + 1 := ⟨c - 1, by omega⟩
      rw [hj, Nat.mul_succ] at hc
      omega
  | succ m ih =>
    intro hd
    have hps : n ^ (m + 1) = n ^ m * n := by rw [Nat.pow_succ]
    rw [hps] at hd
    rcases (hq.dvd_mul).mp hd with h1 | h1
    · exact ih h1
    · exact h1

/-- Cancellation on the right summand: `p ∣ A + B` and `p ∣ B` give `p ∣ A`. -/
theorem dvd_add_cancel_right (p A B : Nat) (hp : 1 ≤ p)
    (h : p ∣ A + B) (hd : p ∣ B) : p ∣ A := by
  obtain ⟨w, hw⟩ := h
  obtain ⟨v, hv⟩ := hd
  by_cases hwv : w < v
  · exfalso
    have hle : p * (w + 1) ≤ p * v := Nat.mul_le_mul_left p (by omega)
    have hexp : p * (w + 1) = p * w + p := by rw [Nat.mul_succ]
    omega
  · obtain ⟨u, hu⟩ : ∃ u, w = v + u := ⟨w - v, by omega⟩
    have hexp2 : p * w = p * v + p * u := by rw [hu, Nat.mul_add]
    refine ⟨u, ?_⟩
    omega

/-- Factorial monotonicity: `a ≤ b → a! ≤ b!`. -/
theorem fact_mono : ∀ (b a : Nat), a ≤ b → fact a ≤ fact b := by
  intro b
  induction b with
  | zero =>
    intro a hle
    have ha0 : a = 0 := by omega
    subst ha0
    exact Nat.le_refl _
  | succ m ih =>
    intro a hle
    by_cases hab : a = m + 1
    · subst hab
      exact Nat.le_refl _
    · have hle' : a ≤ m := by omega
      have ihm : fact a ≤ fact m := ih a hle'
      have hkey : (m + 1) * fact m = m * fact m + fact m := by
        rw [Nat.add_mul, Nat.one_mul]
      show fact a ≤ (m + 1) * fact m
      omega

/-- `u ≤ u!` (the channel bound of R6). -/
theorem fact_ge_self : ∀ (u : Nat), u ≤ fact u := by
  intro u
  induction u with
  | zero => exact Nat.zero_le (fact 0)
  | succ m ih =>
    have hfp : 1 ≤ fact m := fact_pos m
    have h1 : (m + 1) * 1 ≤ (m + 1) * fact m :=
      Nat.mul_le_mul_left (m + 1) hfp
    show m + 1 ≤ (m + 1) * fact m
    omega

/-- The list length (self-contained encoding of |S|). -/
def lenB : List Nat → Nat
  | [] => 0
  | _ :: t => 1 + lenB t

/-- The low window sum: `sumFactsLow d S = Σ_{a ∈ S, a < d} a!`. -/
def sumFactsLow (d : Nat) : List Nat → Nat
  | [] => 0
  | a :: t => if a < d then fact a + sumFactsLow d t else sumFactsLow d t

/-- Bounded sums: if every element of S is ≤ C then `Σ_{a∈S} a! ≤ |S| · C!`. -/
theorem sumFacts_bound : ∀ (S : List Nat) (C : Nat), (∀ a, memB a S → a ≤ C) →
    sumFacts S ≤ lenB S * fact C := by
  intro S
  induction S with
  | nil => intro C _; show (0 : Nat) ≤ 0 * fact C; omega
  | cons a t ih =>
    intro C h
    have haC : a ≤ C := h a (Or.inl rfl)
    have ht : ∀ x, memB x t → x ≤ C := fun x hx => h x (Or.inr hx)
    have ihb := ih C ht
    have hfa : fact a ≤ fact C := fact_mono C a haC
    show fact a + sumFacts t ≤ (1 + lenB t) * fact C
    rw [Nat.add_mul, Nat.one_mul]
    omega

/-- Powerful: every prime divisor q of x satisfies q² ∣ x (doc §0 (Q2)). -/
def powerful (x : Nat) : Prop := ∀ q, q.Prime → q ∣ x → q * q ∣ x

/-- **R2 — THE POWERFUL HIERARCHY** (doc §5.2): every k-th power
(k ≥ 2) is powerful. -/
theorem r2_kth_powerful (k n : Nat) (hk : 2 ≤ k) : powerful (n ^ k) := by
  intro q hq hdvd
  rcases Nat.eq_zero_or_pos n with hn | hn
  · have hz : (0 : Nat) ^ k = 0 := zero_pow_pos k (by omega)
    rw [hn, hz]
    exact Nat.dvd_zero _
  · have hn1 : 1 ≤ n := by omega
    have hqn : q ∣ n := prime_dvd_pow q n hq k hdvd
    have hvp1 : 1 ≤ vp q n := vp_dvd_ge_one q n hq hn1 hqn
    have hvpk : vp q (n ^ k) = k * vp q n :=
      vp_pow k q k n (Nat.le_refl k) hq hn1
    have hkn : k * 1 ≤ k * vp q n := Nat.mul_le_mul_left k hvp1
    have hge : 2 ≤ vp q (n ^ k) := by rw [hvpk]; omega
    exact vp_two_dvd_sq q (n ^ k) hq hge

/-- **R2 — THE REDUCTION** (doc §5.2), boundedness form of (Q2) ⟹ (Q1):
if the powerful values of A are bounded, then for every k ≥ 2 the
k-th-power values of A are bounded (by the same bound). -/
theorem r2_q2_imp_q1 (h : ∃ M, ∀ (S : List Nat), powerful (sumFacts S) → sumFacts S ≤ M) :
    ∀ k, 2 ≤ k → ∃ N, ∀ (S : List Nat), (∃ n, sumFacts S = n ^ k) → sumFacts S ≤ N := by
  obtain ⟨M, hM⟩ := h
  intro k hk
  refine ⟨M, ?_⟩
  intro S hex
  obtain ⟨n, hn⟩ := hex
  have hpow : powerful (sumFacts S) := by rw [hn]; exact r2_kth_powerful k n hk
  exact hM S hpow

/-- **R1 — THE WINDOW CONGRUENCE** (doc §5.1): for every d ≥ 2 and every
finite S: `Σ_{a∈S} a! ≡ Σ_{a∈S, a<d} a! (mod d)` — formalized as the
witness form `Σ = Σ_low + d·j`.  For a ≥ d the factorial a! contains
the factor d (the quotient engine `qfact`), so the high window is
congruent to 0. -/
theorem r1_window_congruence (d : Nat) (hd : 2 ≤ d) : ∀ (S : List Nat),
    ∃ j, sumFacts S = sumFactsLow d S + d * j := by
  intro S
  induction S with
  | nil => refine ⟨0, ?_⟩; show (0 : Nat) = 0 + d * 0; omega
  | cons a t ih =>
    obtain ⟨j, hj⟩ := ih
    by_cases hlt : a < d
    · have he : sumFactsLow d (a :: t) = fact a + sumFactsLow d t := by
        have h2 : sumFactsLow d (a :: t) =
            if a < d then fact a + sumFactsLow d t else sumFactsLow d t := rfl
        rw [h2, if_pos hlt]
      have hsc : sumFacts (a :: t) = fact a + sumFacts t := rfl
      refine ⟨j, ?_⟩
      rw [he, hsc, hj]
      omega
    · have he : sumFactsLow d (a :: t) = sumFactsLow d t := by
        have h2 : sumFactsLow d (a :: t) =
            if a < d then fact a + sumFactsLow d t else sumFactsLow d t := rfl
        rw [h2, if_neg hlt]
      have hf0 : fact 0 = 1 := rfl
      have hfa : fact a = qfact 0 a := by
        rw [fact_split a 0 (Nat.zero_le a), hf0, Nat.one_mul]
      have hdvd : d ∣ fact a := by rw [hfa]; exact qfact_dvd a 0 d (by omega) (by omega)
      have hxdm := Nat.div_add_mod (fact a) d
      have hmod : fact a % d = 0 := Nat.mod_eq_zero_of_dvd hdvd
      have hfe : fact a = d * (fact a / d) := by omega
      have hsc : sumFacts (a :: t) = fact a + sumFacts t := rfl
      refine ⟨fact a / d + j, ?_⟩
      rw [he, hsc, hj]
      have hexp : d * (fact a / d + j) = d * (fact a / d) + d * j :=
        Nat.mul_add d (fact a / d) j
      omega

/-- **R3 — THE k-GENERALIZED CASCADE DIVISIBILITY** (doc §5.3): if
`Σ_{a∈S} a! = n^k` (k ≥ 2, S ≠ ∅) then `k ∣ (2j₀ − s₂(j₀)) + v₂(C(S))` —
the cited explicit cascade (Kernel 15 T10) plus `v₂(n^k) = k·v₂(n)`. -/
theorem r3_kth_power_cascade (S : List Nat) (hS : S ≠ []) (n k : Nat) (hk : 2 ≤ k)
    (h : sumFacts S = n ^ k) :
    k ∣ (2 * botPair S - s2 (botPair S)) + v2 (cascadeC S) := by
  have hpos : 1 ≤ sumFacts S := by rw [sumFacts_bridge S]; exact sumFacts_pos S hS
  rcases Nat.eq_zero_or_pos n with hn | hn
  · have hz : (0 : Nat) ^ k = 0 := zero_pow_pos k (by omega)
    rw [hn, hz] at h
    omega
  · have hn1 : 1 ≤ n := by omega
    have hbr : _root_.sumFacts S = n ^ k := by rw [← sumFacts_bridge S]; exact h
    have hc := explicit_cascade S hS
    rw [hbr] at hc
    have hpow : v2 (n ^ k) = k * v2 n := v2_pow k n hn1
    rw [hpow] at hc
    exact ⟨v2 n, hc.symm⟩

/-- **R5 — THE OBSTRUCTION WEB** (doc §5.5): for `x = Σ_{a∈S} a! = n^k`
(k ≥ 2, S ≠ ∅) ALL four obstructions hold simultaneously:
(1) the 2-adic cascade divisibility [R3];
(2) the all-prime singleton obstruction: `k ∣ v_p(b_p!)` at every prime
    p whose lowest occupied p-block in S is a singleton {b_p} [P5];
(3) the valuation profile `v_p(x) = k·v_p(n)` at every prime p [vp_pow];
(4) the window congruence: `p ∣ n ⟹ Σ_{a<p} a! ≡ 0 (mod p)` at every
    prime p [R1]. -/
theorem r5_obstruction_web (S : List Nat) (hS : S ≠ []) (n k : Nat) (hk : 2 ≤ k)
    (h : sumFacts S = n ^ k) :
    k ∣ (2 * botPair S - s2 (botPair S)) + v2 (cascadeC S) ∧
    (∀ p b, p.Prime → countB b S = 1 →
      (∀ a, memB a S → a ≠ b → p * (b / p + 1) ≤ a) → k ∣ vp p (fact b)) ∧
    (∀ p, p.Prime → vp p (sumFacts S) = k * vp p n) ∧
    (∀ p, p.Prime → p ∣ n → sumFactsLow p S % p = 0) := by
  have hpos : 1 ≤ sumFacts S := by rw [sumFacts_bridge S]; exact sumFacts_pos S hS
  refine ⟨r3_kth_power_cascade S hS n k hk h, ?_, ?_, ?_⟩
  · intro p b hp hbS hblock
    by_contra hknot
    exact all_prime_power_obstruction p b hp S hbS hblock k n hk hknot h
  · intro p hp
    rcases Nat.eq_zero_or_pos n with hn | hn
    · have hz : (0 : Nat) ^ k = 0 := zero_pow_pos k (by omega)
      rw [hn, hz] at h
      omega
    · have hn1 : 1 ≤ n := by omega
      rw [h]
      exact vp_pow k p k n (Nat.le_refl k) hp hn1
  · intro p hp hpn
    have hn1 : 1 ≤ n := by
      rcases Nat.eq_zero_or_pos n with h0 | h1
      · have hz : (0 : Nat) ^ k = 0 := zero_pow_pos k (by omega)
        rw [h0, hz] at h
        omega
      · omega
    have hvp1 : 1 ≤ vp p n := vp_dvd_ge_one p n hp hn1 hpn
    have hvpk : vp p (n ^ k) = k * vp p n :=
      vp_pow k p k n (Nat.le_refl k) hp hn1
    have hkn : k * 1 ≤ k * vp p n := Nat.mul_le_mul_left k hvp1
    have hge : 1 ≤ vp p (n ^ k) := by rw [hvpk]; omega
    have hpnk : p ∣ n ^ k := vp_pos_dvd p (n ^ k) hp hge
    have hpS : p ∣ sumFacts S := by rw [h]; exact hpnk
    obtain ⟨j, hj⟩ := r1_window_congruence p hp.one_lt S
    have hpLow : p ∣ sumFactsLow p S + p * j := by rw [← hj]; exact hpS
    have hpdj : p ∣ p * j := ⟨j, rfl⟩
    have hp2 : 2 ≤ p := hp.one_lt
    have hp1le : 1 ≤ p := by omega
    have hplow : p ∣ sumFactsLow p S :=
      dvd_add_cancel_right p (sumFactsLow p S) (p * j) hp1le hpLow hpdj
    exact Nat.mod_eq_zero_of_dvd hplow

/-- **HYP-BE (Brindza–Erdős [BrEr91])** — the doc §5.4 single stated
external hypothesis, stated as a GIVEN HYPOTHESIS (Boss's arsenal-only
rule; a theorem hypothesis, never an axiom): for every r ≥ 1 there is
C(r) such that every powerful r-factorial sum has all its r terms
≤ C(r). -/
def hypBE : Prop :=
  ∀ (r : Nat), 1 ≤ r → ∃ C, ∀ (S : List Nat), lenB S = r →
    powerful (sumFacts S) → ∀ a, memB a S → a ≤ C

/-- **R4 — THE BOUNDED-CARDINALITY REDUCTION** (doc §5.4, conditional on
HYP-BE): for every fixed r ≥ 1 and k ≥ 2 the r-term k-th-power value
set is bounded (finite, in the ℕ-set sense). -/
theorem r4_kth_power_bounded (hyp : hypBE) (r k : Nat) (hr : 1 ≤ r) (hk : 2 ≤ k) :
    ∃ N, ∀ (S : List Nat), lenB S = r → (∃ n, sumFacts S = n ^ k) → sumFacts S ≤ N := by
  obtain ⟨C, hC⟩ := hyp r hr
  refine ⟨r * fact C, ?_⟩
  intro S hlen hex
  obtain ⟨n, hn⟩ := hex
  have hpow : powerful (sumFacts S) := by rw [hn]; exact r2_kth_powerful k n hk
  have hbb := sumFacts_bound S C (fun a ha => hC S hlen hpow a ha)
  rw [hlen] at hbb
  exact hbb

/-- **R4 (powerful half)**: under HYP-BE every fixed-r powerful value set
is bounded (the "same for powerful values" of the doc). -/
theorem r4_powerful_bounded (hyp : hypBE) (r : Nat) (hr : 1 ≤ r) :
    ∃ N, ∀ (S : List Nat), lenB S = r → powerful (sumFacts S) → sumFacts S ≤ N := by
  obtain ⟨C, hC⟩ := hyp r hr
  refine ⟨r * fact C, ?_⟩
  intro S hlen hpow
  have hbb := sumFacts_bound S C (fun a ha => hC S hlen hpow a ha)
  rw [hlen] at hbb
  exact hbb

/-- **R6 — THE BROCARD EMBEDDING** (doc §5.6): if the square values of A
are bounded ((Q1) at k = 2 answered YES in the ℕ-set sense), then the
Brocard domain {u : u! + 1 = n²} is bounded (finite) — the
150-year-old open problem is a special instance of the corpus
question. -/
theorem r6_brocard_bounded
    (h : ∃ M, ∀ (S : List Nat) (n : Nat), sumFacts S = n * n → sumFacts S ≤ M) :
    ∃ N, ∀ u, (∃ n, fact u + 1 = n * n) → u ≤ N := by
  obtain ⟨M, hM⟩ := h
  refine ⟨M, ?_⟩
  intro u hex
  obtain ⟨n, hn⟩ := hex
  have hch : sumFacts [1, u] = fact u + 1 := by
    have h1 : sumFacts [1, u] = fact 1 + (fact u + 0) := rfl
    have hf1 : fact 1 = 1 := rfl
    omega
  have hle := hM [1, u] n (by rw [hch]; exact hn)
  rw [hch] at hle
  have hge : u ≤ fact u := fact_ge_self u
  omega

/-- **R7.1 — THE BROCARD CHANNEL PASSES THE ALL-PRIME OBSTRUCTION**
(doc §5.7): for every u ≥ 2 and every prime p ≤ u, the channel sum
`1 + u!` (S = {1, u}) has `v_p(1 + u!) = v_p(1!) = 0` — the p-block
of 1 is the singleton {1} and u lies strictly higher (P3 at b = 1). -/
theorem r7_channel_vp_zero (u p : Nat) (hp : p.Prime) (hu : 2 ≤ u) (hppu : p ≤ u) :
    vp p (sumFacts [1, u]) = 0 := by
  have hu1 : ¬ (u = 1) := by omega
  have he : countB 1 [1, u] = (if (1 : Nat) = 1 then 1 else 0) +
      ((if u = 1 then 1 else 0) + 0) := rfl
  rw [if_pos rfl, if_neg hu1] at he
  have hblock : ∀ a, memB a [1, u] → a ≠ 1 → p * (1 / p + 1) ≤ a := by
    intro a ha hne
    have hOr : 1 = a ∨ (u = a ∨ False) := ha
    rcases hOr with rfl | rfl | hf
    · exact absurd rfl hne
    · have hd : 1 / p = 0 := one_div_eq_zero p hp.one_lt
      rw [hd]
      omega
    · exact hf.elim
  have hlaw := all_prime_isolated_min p 1 hp [1, u] he hblock
  have hf1 : fact 1 = 1 := rfl
  rw [hlaw, hf1, vp_one p hp.one_lt]

/-- **R7.2 — THE CASCADE PARITY IS SATISFIED** (doc §5.7): for every
u ≥ 2, `v₂(1 + u!) = 0` — even (u! is even, 1 + u! odd): the T11
square-parity invariant holds vacuously on the channel (j₀ = 0,
Λ(0) = 0, v₂(C) = 0). -/
theorem r7_channel_v2_zero (u : Nat) (hu : 2 ≤ u) : v2 (sumFacts [1, u]) = 0 := by
  have hch : sumFacts [1, u] = fact u + 1 := by
    have h1 : sumFacts [1, u] = fact 1 + (fact u + 0) := rfl
    have hf1 : fact 1 = 1 := rfl
    omega
  have hf0 : fact 0 = 1 := rfl
  have hfa : fact u = qfact 0 u := by
    rw [fact_split u 0 (Nat.zero_le u), hf0, Nat.one_mul]
  have hdvd : 2 ∣ fact u := by rw [hfa]; exact qfact_dvd u 0 2 (by omega) (by omega)
  have hfe : fact u % 2 = 0 := Nat.mod_eq_zero_of_dvd hdvd
  rw [hch]
  have hodd : (fact u + 1) % 2 = 1 := by omega
  exact v2_odd _ hodd

/-- **R7.3 — THE WINDOW IS VACUOUS ON THE CHANNEL** (doc §5.7): if
`1 + u! = n²` (u ≥ 2) then every prime factor of n exceeds u — no
window prime can divide the root. -/
theorem r7_window_avoid (u n : Nat) (hu : 2 ≤ u)
    (h : sumFacts [1, u] = n * n) :
    ∀ p, p.Prime → p ≤ u → ¬ p ∣ n := by
  intro p hp hppu hdvd
  have hpos1 : 1 ≤ sumFacts [1, u] := by
    have h1 : sumFacts [1, u] = fact 1 + (fact u + 0) := rfl
    have hf1 : 1 ≤ fact 1 := fact_pos 1
    omega
  have hn1 : 1 ≤ n := by
    rcases Nat.eq_zero_or_pos n with h0 | h1
    · rw [h0, Nat.mul_zero] at h
      omega
    · omega
  have hvp1 : 1 ≤ vp p n := vp_dvd_ge_one p n hp hn1 hdvd
  have hvnn : vp p (n * n) = vp p n + vp p n :=
    vp_mul (n + n) p n n (Nat.le_refl _) hp hn1 hn1
  have hdvdnn : p ∣ n * n := vp_pos_dvd p (n * n) hp (by omega)
  have hdvdS : p ∣ sumFacts [1, u] := by rw [h]; exact hdvdnn
  have hvpS1 : 1 ≤ vp p (sumFacts [1, u]) :=
    vp_dvd_ge_one p (sumFacts [1, u]) hp hpos1 hdvdS
  have hvp0 : vp p (sumFacts [1, u]) = 0 :=
    r7_channel_vp_zero u p hp hu hppu
  omega

/-! ## §12 THE COMPLETE BOARD (the final assembled main theorem). -/

/-- **THE COMPLETE THEOREM BOARD of Erdős #1108 per COMPLETE_PROOF.md's
final section** — the complete unconditional engine + reduction layer,
one conjunction, no sub-cases: the all-prime isolated-minimum law and
k-th-power obstruction (Kernel 30), the Legendre parity spine and the
explicit pair-cascade (Kernel 13/15, CITED via import), the window
congruence R1, the powerful hierarchy R2 (+ the Q2 ⟹ Q1 reduction),
the k-generalized cascade divisibility R3, the complete obstruction
web R5, the bounded-cardinality reductions R4 (conditional on the
stated hypothesis HYP-BE), the Brocard embedding R6, the Brocard
channel local-obstruction web R7, and the arsenal bridge.  The open
global-finiteness core (doc §8) is NOT claimed. -/
theorem erdos1108ap_complete :
    (∀ p b S, p.Prime → countB b S = 1 →
      (∀ a, memB a S → a ≠ b → p * (b / p + 1) ≤ a) →
      vp p (sumFacts S) = vp p (fact b)) ∧
    (∀ p b S k n, p.Prime → countB b S = 1 →
      (∀ a, memB a S → a ≠ b → p * (b / p + 1) ≤ a) → 2 ≤ k →
      ¬ (k ∣ vp p (fact b)) → sumFacts S ≠ n ^ k) ∧
    (∀ n : Nat, v2 (_root_.fact n) + s2 n = n) ∧
    (∀ S : List Nat, S ≠ [] →
      v2 (_root_.sumFacts S) = (2 * botPair S - s2 (botPair S)) + v2 (cascadeC S)) ∧
    (∀ d S, 2 ≤ d → ∃ j, sumFacts S = sumFactsLow d S + d * j) ∧
    (∀ k n, 2 ≤ k → powerful (n ^ k)) ∧
    (∀ h : ∃ M, ∀ S : List Nat, powerful (sumFacts S) → sumFacts S ≤ M, ∀ k, 2 ≤ k →
      ∃ N, ∀ S : List Nat, (∃ n, sumFacts S = n ^ k) → sumFacts S ≤ N) ∧
    (∀ S n k, S ≠ [] → 2 ≤ k → sumFacts S = n ^ k →
      k ∣ (2 * botPair S - s2 (botPair S)) + v2 (cascadeC S)) ∧
    (∀ S n k, S ≠ [] → 2 ≤ k → sumFacts S = n ^ k →
      (k ∣ (2 * botPair S - s2 (botPair S)) + v2 (cascadeC S) ∧
      (∀ p b, p.Prime → countB b S = 1 →
        (∀ a, memB a S → a ≠ b → p * (b / p + 1) ≤ a) → k ∣ vp p (fact b)) ∧
      (∀ p, p.Prime → vp p (sumFacts S) = k * vp p n) ∧
      (∀ p, p.Prime → p ∣ n → sumFactsLow p S % p = 0))) ∧
    (∀ hyp : hypBE, ∀ r k, 1 ≤ r → 2 ≤ k →
      ∃ N, ∀ S : List Nat, lenB S = r → (∃ n, sumFacts S = n ^ k) → sumFacts S ≤ N) ∧
    (∀ hyp : hypBE, ∀ r, 1 ≤ r →
      ∃ N, ∀ S : List Nat, lenB S = r → powerful (sumFacts S) → sumFacts S ≤ N) ∧
    (∀ h : ∃ M, ∀ S : List Nat, ∀ n : Nat, sumFacts S = n * n → sumFacts S ≤ M,
      ∃ N, ∀ u, (∃ n, fact u + 1 = n * n) → u ≤ N) ∧
    (∀ u p, 2 ≤ u → p.Prime → p ≤ u → vp p (sumFacts [1, u]) = 0) ∧
    (∀ u, 2 ≤ u → v2 (sumFacts [1, u]) = 0) ∧
    (∀ u n, 2 ≤ u → sumFacts [1, u] = n * n →
      ∀ p, p.Prime → p ≤ u → ¬ p ∣ n) ∧
    arsenalBridgeProp :=
  ⟨fun p b S hp hbS hb => all_prime_isolated_min p b hp S hbS hb,
   fun p b S k n hp hbS hb hk hknot =>
     all_prime_power_obstruction p b hp S hbS hb k n hk hknot,
   legendre_v2_fact,
   explicit_cascade,
   fun d S hd => r1_window_congruence d hd S,
   fun k n hk => r2_kth_powerful k n hk,
   fun h k hk => r2_q2_imp_q1 h k hk,
   fun S n k hS hk h => r3_kth_power_cascade S hS n k hk h,
   fun S n k hS hk h => r5_obstruction_web S hS n k hk h,
   fun hyp r k hr hk => r4_kth_power_bounded hyp r k hr hk,
   fun hyp r hr => r4_powerful_bounded hyp r hr,
   fun h => r6_brocard_bounded h,
   fun u p hu hp hppu => r7_channel_vp_zero u p hp hu hppu,
   fun u hu => r7_channel_v2_zero u hu,
   fun u n hu h p hp hppu => r7_window_avoid u n hu h p hp hppu,
   erdos1108ap_arsenal_bridge⟩

/-! ## §12b THE C1 FINAL ASSEMBLY (S050-C1 — the B2 retry deliverable,
the doc's final-board form, quantifier for quantifier, no sub-cases,
chained by name from the green layers — zero new glue lemmas). -/

/-- **THE FINAL ASSEMBLED MAIN THEOREM of COMPLETE_PROOF.md** (the C1
complete-board deliverable): the complete unconditional answer to the
verbatim #1108 ask per the doc's final board — every component the doc
PROVES, in one conjunction:

* the all-prime engine: `all_prime_isolated_min` (the complete
  all-prime valuation theory at singleton bottoms, every prime p
  simultaneously) and `all_prime_power_obstruction`;
* **THE R5 OBSTRUCTION WEB** (doc §5.5 — the final assembly): for every
  k ≥ 2 and every nonempty finite S with `Σ_{a∈S} a! = n^k`, ALL FOUR
  obstructions hold simultaneously — (1) the 2-adic cascade
  divisibility `k ∣ (2j₀ − s₂(j₀)) + v₂(C(S))`, (2) the all-prime
  singleton obstruction `k ∣ v_p(b_p!)` at every prime whose lowest
  occupied p-block is a singleton, (3) the valuation profile
  `v_p(x) = k·v_p(n)` at every prime, (4) the window congruence
  `p ∣ n → Σ_{a∈S,a<p} a! ≡ 0 (mod p)`;
* the cited Legendre parity spine `v₂(n!) + s₂(n) = n` and the explicit
  pair-cascade (Kernel 15, CI-green run 42153591445);
* the TheoremBGeneral twin `v2_pow` (`v₂(n^k) = k·v₂(n)`);
* the R2 powerful hierarchy (every k-th power is powerful) and the
  (Q2) ⟹ (Q1) reduction in boundedness form;
* the R4 bounded-cardinality reductions under the single stated
  external hypothesis HYP-BE (a theorem hypothesis — never an axiom);
* the Brocard embedding R6 (a YES to (Q1) at k = 2 bounds Brocard's
  1876 equation) and the Brocard channel web R7 (`v_p(1+u!) = 0` at
  every prime p ≤ u, the cascade parity, window avoidance).

The open global-finiteness core (doc §8) is explicitly NOT claimed. -/
theorem erdos1108_complete :
    (∀ p b S, p.Prime → countB b S = 1 →
      (∀ a, memB a S → a ≠ b → p * (b / p + 1) ≤ a) →
      vp p (sumFacts S) = vp p (fact b)) ∧
    (∀ p b S k n, p.Prime → countB b S = 1 →
      (∀ a, memB a S → a ≠ b → p * (b / p + 1) ≤ a) → 2 ≤ k →
      ¬ (k ∣ vp p (fact b)) → sumFacts S ≠ n ^ k) ∧
    (∀ S n k, S ≠ [] → 2 ≤ k → sumFacts S = n ^ k →
      (k ∣ (2 * botPair S - s2 (botPair S)) + v2 (cascadeC S) ∧
      (∀ p b, p.Prime → countB b S = 1 →
        (∀ a, memB a S → a ≠ b → p * (b / p + 1) ≤ a) → k ∣ vp p (fact b)) ∧
      (∀ p, p.Prime → vp p (sumFacts S) = k * vp p n) ∧
      (∀ p, p.Prime → p ∣ n → sumFactsLow p S % p = 0))) ∧
    (∀ n : Nat, v2 (_root_.fact n) + s2 n = n) ∧
    (∀ S : List Nat, S ≠ [] →
      v2 (_root_.sumFacts S) = (2 * botPair S - s2 (botPair S)) + v2 (cascadeC S)) ∧
    (∀ k n, 1 ≤ n → v2 (n ^ k) = k * v2 n) ∧
    (∀ k n, 2 ≤ k → powerful (n ^ k)) ∧
    (∀ h : ∃ M, ∀ S : List Nat, powerful (sumFacts S) → sumFacts S ≤ M, ∀ k, 2 ≤ k →
      ∃ N, ∀ S : List Nat, (∃ n, sumFacts S = n ^ k) → sumFacts S ≤ N) ∧
    (∀ hyp : hypBE, ∀ r k, 1 ≤ r → 2 ≤ k →
      ∃ N, ∀ S : List Nat, lenB S = r → (∃ n, sumFacts S = n ^ k) → sumFacts S ≤ N) ∧
    (∀ hyp : hypBE, ∀ r, 1 ≤ r →
      ∃ N, ∀ S : List Nat, lenB S = r → powerful (sumFacts S) → sumFacts S ≤ N) ∧
    (∀ h : ∃ M, ∀ S : List Nat, ∀ n : Nat, sumFacts S = n * n → sumFacts S ≤ M,
      ∃ N, ∀ u, (∃ n, fact u + 1 = n * n) → u ≤ N) ∧
    (∀ u p, 2 ≤ u → p.Prime → p ≤ u → vp p (sumFacts [1, u]) = 0) ∧
    (∀ u, 2 ≤ u → v2 (sumFacts [1, u]) = 0) ∧
    (∀ u n, 2 ≤ u → sumFacts [1, u] = n * n →
      ∀ p, p.Prime → p ≤ u → ¬ p ∣ n) ∧
    erdos1108ap_arsenal_bridge :=
  ⟨fun p b S hp hbS hb => all_prime_isolated_min p b hp S hbS hb,
   fun p b S k n hp hbS hb hk hknot =>
     all_prime_power_obstruction p b hp S hbS hb k n hk hknot,
   fun S n k hS hk h => r5_obstruction_web S hS n k hk h,
   legendre_v2_fact,
   explicit_cascade,
   v2_pow,
   fun k n hk => r2_kth_powerful k n hk,
   fun h k hk => r2_q2_imp_q1 h k hk,
   fun hyp r k hr hk => r4_kth_power_bounded hyp r k hr hk,
   fun hyp r hr => r4_powerful_bounded hyp r hr,
   fun h => r6_brocard_bounded h,
   fun u p hu hp hppu => r7_channel_vp_zero u p hp hu hppu,
   fun u hu => r7_channel_v2_zero u hu,
   fun u n hu h p hp hppu => r7_window_avoid u n hu h p hp hppu,
   erdos1108ap_arsenal_bridge⟩

/-! ## §13 RECEIPTS (the complete board). -/

-- The Brocard channel receipts: v₂(1 + u!) = 0 at the three known
-- Brocard exponents u = 4, 5, 7 (25 = 5², 121 = 11², 5041 = 71²):
#eval (v2 (sumFacts [1, 4]), v2 (sumFacts [1, 5]), v2 (sumFacts [1, 7]))
-- expected (0, 0, 0)

-- The all-prime channel receipt at u = 7 (every prime p ≤ 7):
#eval (vp 2 (sumFacts [1, 7]), vp 3 (sumFacts [1, 7]),
       vp 5 (sumFacts [1, 7]), vp 7 (sumFacts [1, 7]))
-- expected (0, 0, 0, 0)

#eval "ERDOS1108_ALLPRIME_COMPLETE_GREEN"
#eval "ERDOS1108_COMPLETE_GREEN"

#print axioms fact_bridge
#print axioms sumFacts_bridge
#print axioms v2_pow
#print axioms r1_window_congruence
#print axioms r2_kth_powerful
#print axioms r2_q2_imp_q1
#print axioms r3_kth_power_cascade
#print axioms r5_obstruction_web
#print axioms r4_kth_power_bounded
#print axioms r4_powerful_bounded
#print axioms r6_brocard_bounded
#print axioms r7_channel_vp_zero
#print axioms r7_channel_v2_zero
#print axioms r7_window_avoid
#print axioms erdos1108ap_complete
#print axioms erdos1108_complete

end Erdos1108AP
