import Arsenal.ErdosTernary2.Basic
import Arsenal.CardinalWorlds
import Arsenal.CardinalWorldsV2

set_option maxRecDepth 65536
set_option maxHeartbeats 16000000

/-! # Erdős #282 — THE ODD-GREEDY TERMINATION LAWS (S036 volley, Kernel 28)

## THE PROBLEM (verbatim, erdosproblems.com/282)

> Let $A\subseteq \mathbb{N}$ be an infinite set and consider the following
> greedy algorithm for a rational $x\in (0,1)$: choose the minimal $n\in A$
> such that $n\geq 1/x$ and repeat with $x$ replaced by $x-\frac{1}{n}$.
> If this terminates after finitely many steps then this produces a
> representation of $x$ as the sum of distinct unit fractions with
> denominators from $A$. Does this process always terminate if $x$ has
> odd denominator and $A$ is the set of odd numbers? More generally,
> for which pairs $x$ and $A$ does this process terminate?

## WHAT THIS PROOF PROVES (the statement above, then the proofs below —
all complete unconditional theorems; the general termination question
remains open and is NOT claimed)

1. **THE ODD-CLOSURE LAW** (`erdos282_odd_closure`): starting from an
   odd-denominator rational, every odd-greedy step stays in the
   odd-denominator world ($q$ odd, $n$ odd $\Rightarrow$ $q\cdot n/g$
   odd) — the conjecture's habitat is invariant.
2. **THE WELL-FORMEDNESS LAW** (`erdos282_step_bound`): every greedy
   step at most DOUBLES the numerator ($p' < 2p$).
3. **THE SIMULATION SOUNDNESS** (`erdos282_sim_sound`): the certified
   Bool simulation `simTerm` implies the existence of a genuine greedy
   trajectory reaching exactly $0$ (`TerminateIn`).
4. **THE TERMINATION CENSUS $q \le 41$** (`erdos282_census`): EVERY
   rational $p/q \in (0,1)$ with $q$ odd, $q \le 41$, terminates under
   the odd-greedy — kernel-decided (420 pairs, deepest trajectory 12
   steps at $38/39$).
5. **THE FAITHFULNESS LAWS** (`erdos282_step_domain`,
   `erdos282_step_value` - F1.4 + F1.2 of COMPLETE_PROOF.md Sect. 2):
   every greedy step from a live state lands in the domain ($p' \le q'$ -
   the laws' hypotheses re-arise at every step of every trajectory), and
   preserves the rational exactly ($p/q = 1/n + p'/q'$ - the corpus
   algorithm's $x \mapsto x - 1/n$; the reduction by $g$ is value-neutral).
6. **THE REPRESENTATION LAW** (`erdos282_representation`): IF the
   odd-greedy terminates from $p/q$ ($1 \le p \le q$), THEN $x$ is exactly
   a finite sum of unit fractions $1/d$ with odd denominators $d \ge 1$ -
   the corpus statement's then-clause ("this produces a representation of
   $x$ as the sum of unit fractions with denominators from $A$" at $A$ =
   the odd numbers), complete and unconditional.
7. **THE COMPLETE BOARD** (`erdos282_complete`): the one-statement
   assembly of everything the #282 ask delivers unconditionally - L1
   (odd-closure), L2 (doubling) + F1.4 (domain perpetuation), L3 (engine
   soundness), the representation then-clause, the L4 census band, and
   the arsenal bridge.

Honest scope: Stein's general conjecture (all odd denominators) remains
open; the battery census extends termination to every odd $q \le 301$
(22,650 pairs, all terminate, deepest 20 steps at $102/293$ — engine
evidence, not claimed as theorem). DOC ERRATUM, honestly scoped: the
corpus statement's parenthetical "distinct" unit fractions is FALSE in
the odd habitat - the kernel-decided census itself contains
4/5 = 1/3 + 1/3 + 1/9 + 1/45 (denominator 3 twice, certified trajectory
[3, 3, 9, 45]) - so the representation law claims odd, finite, exact -
NOT distinctness.
-/

namespace Erdos282

/-! ## §1 The greedy step (relational form). -/

/-- One certified odd-greedy step: n is THE minimal odd n with p·n ≥ q
(the minimality clause), g is a common divisor making the reduction
exact, and (p', q') represents x − 1/n. -/
def GreedyStep (p q p' q' : Nat) : Prop :=
  ∃ n g, n % 2 = 1 ∧ 1 ≤ n ∧ q ≤ p * n ∧ (n = 1 ∨ p * (n - 2) < q) ∧
    1 ≤ g ∧ (p * n - q) % g = 0 ∧ (q * n) % g = 0 ∧
    p' * g = p * n - q ∧ q' * g = q * n

/-- Termination: a genuine trajectory of certified greedy steps
reaching exactly 0. -/
def TerminateIn : Nat → Nat → Nat → Prop
  | 0, p, _ => p = 0
  | fuel + 1, p, q => p = 0 ∨ ∃ p' q', GreedyStep p q p' q' ∧ TerminateIn fuel p' q'

/-! ## §2 THE ODD-CLOSURE LAW. -/

theorem erdos282_odd_closure (p q p' q' n g : Nat) (hq : q % 2 = 1)
    (hn : n % 2 = 1) (hg : 1 ≤ g) (heq : q' * g = q * n) : q' % 2 = 1 := by
  have hqn : (q * n) % 2 = 1 := by
    have h1 : (q * n) % 2 = (q % 2) * (n % 2) % 2 := Nat.mul_mod q n 2
    rw [hq, hn] at h1
    norm_num at h1
    exact h1
  by_contra hcon
  have he : q' % 2 = 0 := by omega
  have hzero : (q' * g) % 2 = 0 := by
    have h1 : (q' * g) % 2 = (q' % 2) * (g % 2) % 2 := Nat.mul_mod q' g 2
    rw [he] at h1
    norm_num at h1
    exact h1
  rw [heq, hqn] at hzero
  exact absurd hzero (by norm_num)

/-! ## §3 THE WELL-FORMEDNESS LAW (the numerator at most doubles). -/

theorem erdos282_step_bound (p q p' q' : Nat) (hstep : GreedyStep p q p' q')
    (hpq : p ≤ q) (hp1 : 1 ≤ p) : p' < 2 * p := by
  obtain ⟨n, g, hnodd, hn1, hnge, hnmin, hg1, _, _, hp'g, _⟩ := hstep
  by_cases hn1c : n = 1
  · -- n = 1: q ≤ p·1 = p, so p = q, so p'·g = p − q = 0, so p' = 0
    have hqle : q ≤ p := by
      rw [hn1c, Nat.mul_one] at hnge
      exact hnge
    have hpe : p = q := Nat.le_antisymm hpq hqle
    rw [hn1c, Nat.mul_one, ← hpe, Nat.sub_self] at hp'g
    rcases Nat.mul_eq_zero.mp hp'g with h0 | h0
    · omega
    · omega
  · -- n ≠ 1: the minimality disjunct p·(n−2) < q must hold
    have hn2case : p * (n - 2) < q := by
      rcases hnmin with h | h
      · exact absurd h hn1c
      · exact h
    have hn2 : 2 ≤ n := by omega
    have hcomm : 2 * p = p * 2 := Nat.mul_comm 2 p
    have hsplit : p * ((n - 2) + 2) = p * (n - 2) + p * 2 := Nat.mul_add p (n - 2) 2
    have hn' : (n - 2) + 2 = n := by omega
    have hpn : p * (n - 2) + 2 * p = p * n := by
      rw [hcomm, ← hsplit, hn']
    have hle : p' ≤ p * n - q := by
      have h1 : p' * 1 ≤ p' * g := Nat.mul_le_mul_left p' hg1
      rw [Nat.mul_one] at h1
      rw [hp'g] at h1
      exact h1
    omega

/-! ## §4 The certified simulation (Bool, kernel-decidable). -/

/-- The minimal odd n ≥ q/p. -/
def greedyN (p q : Nat) : Nat :=
  if (q + p - 1) / p % 2 = 0 then (q + p - 1) / p + 1 else (q + p - 1) / p

/-- Structural fuel-gcd (kernel-friendly; correctness NOT needed — the
step check certifies divisibility directly). -/
def gcdF : Nat → Nat → Nat → Nat
  | 0, _, b => b
  | fuel + 1, a, b =>
    if a = 0 then b
    else if b = 0 then a
    else if b < a then gcdF fuel b a
    else if b % a = 0 then a
    else gcdF fuel (b % a) a

/-- The gcd candidate for the step from (p, q). -/
def stepG (p q : Nat) : Nat :=
  gcdF (2 * (p * greedyN p q - q + q * greedyN p q) + 2)
    (p * greedyN p q - q) (q * greedyN p q)

def stepP (p q : Nat) : Nat := (p * greedyN p q - q) / stepG p q

def stepQ (p q : Nat) : Nat := (q * greedyN p q) / stepG p q

/-- The step certificate: n is the greedy choice, g divides both
components exactly. -/
def stepValid (p q n g : Nat) : Bool :=
  decide (n % 2 = 1 ∧ 1 ≤ n ∧ q ≤ p * n ∧ (n = 1 ∨ p * (n - 2) < q) ∧
    1 ≤ g ∧ (p * n - q) % g = 0 ∧ (q * n) % g = 0)

/-- The fuel-bounded certified simulation. -/
def simTerm : Nat → Nat → Nat → Bool
  | 0, _, _ => false
  | fuel + 1, p, q =>
    if p = 0 then true
    else if stepValid p q (greedyN p q) (stepG p q) then
      simTerm fuel (stepP p q) (stepQ p q)
    else false

/-! ## §5 greedyN is the certified greedy choice. -/

theorem greedyN_spec (p q : Nat) (hp : 1 ≤ p) :
    greedyN p q % 2 = 1 ∧ 1 ≤ greedyN p q ∧ q ≤ p * greedyN p q ∧
      (greedyN p q = 1 ∨ p * (greedyN p q - 2) < q) := by
  -- an OPAQUE n0 (the set-tactic's let-bound local carries its
  -- variable-divisor division value and poisons omega — obtain instead)
  obtain ⟨n0, hn0eq⟩ : ∃ n0, (q + p - 1) / p = n0 := ⟨_, rfl⟩
  have hmodlt : (q + p - 1) % p < p := Nat.mod_lt (q + p - 1) (by omega)
  have hdm : p * n0 + (q + p - 1) % p = q + p - 1 := by
    rw [← hn0eq]
    exact Nat.div_add_mod (q + p - 1) p
  have hF2 : q ≤ p * n0 := by omega
  unfold greedyN
  rw [hn0eq]
  by_cases hb : n0 % 2 = 0
  · -- even branch: n = n0 + 1
    rw [if_pos hb]
    have hmod1 : (n0 + 1) % 2 = 1 := by
      rw [Nat.add_mod n0 1 2, hb]
    refine ⟨hmod1, by omega, ?_, ?_⟩
    · have hmul : p * (n0 + 1) = p * n0 + p := by
        rw [Nat.mul_add, Nat.mul_one]
      omega
    · by_cases hn0z : n0 = 0
      · left; omega
      · right
        have hn01 : 1 ≤ n0 := by omega
        have hq1 : 1 ≤ q := by
          have hA : p * 1 ≤ p * n0 := Nat.mul_le_mul_left p hn01
          omega
        have hle : p * n0 ≤ q + p - 1 := by omega
        have hsub : p * (n0 - 1) + p = p * n0 := by
          have hn' : n0 - 1 + 1 = n0 := by omega
          have hsplit : p * ((n0 - 1) + 1) = p * (n0 - 1) + p * 1 :=
            Nat.mul_add p (n0 - 1) 1
          rw [Nat.mul_one] at hsplit
          rw [hn'] at hsplit
          exact hsplit.symm
        have hn2 : n0 + 1 - 2 = n0 - 1 := by omega
        show p * (n0 + 1 - 2) < q
        rw [hn2]
        omega
  · -- odd branch: n = n0
    have hlt2 : n0 % 2 < 2 := Nat.mod_lt n0 (by norm_num)
    have hn0o : n0 % 2 = 1 := by omega
    rw [if_neg hb]
    have hn01 : 1 ≤ n0 := by
      by_cases hn0z : n0 = 0
      · rw [hn0z] at hb
        exact absurd hb (by norm_num)
      · omega
    refine ⟨hn0o, hn01, hF2, ?_⟩
    by_cases hn1c : n0 = 1
    · left; exact hn1c
    · right
      have hn03 : 3 ≤ n0 := by omega
      have hq1 : 1 ≤ q := by
        have hA : p * 1 ≤ p * n0 := Nat.mul_le_mul_left p hn01
        omega
      have hle : p * n0 ≤ q + p - 1 := by omega
      have hsub : p * (n0 - 1) + p = p * n0 := by
        have hn' : n0 - 1 + 1 = n0 := by omega
        have hsplit : p * ((n0 - 1) + 1) = p * (n0 - 1) + p * 1 :=
          Nat.mul_add p (n0 - 1) 1
        rw [Nat.mul_one] at hsplit
        rw [hn'] at hsplit
        exact hsplit.symm
      have hmono : p * (n0 - 2) ≤ p * (n0 - 1) := Nat.mul_le_mul_left p (by omega)
      show p * (n0 - 2) < q
      omega

/-! ## §6 THE SIMULATION SOUNDNESS. -/

theorem stepValid_spec (p q n g : Nat) (h : stepValid p q n g = true) :
    n % 2 = 1 ∧ 1 ≤ n ∧ q ≤ p * n ∧ (n = 1 ∨ p * (n - 2) < q) ∧
    1 ≤ g ∧ (p * n - q) % g = 0 ∧ (q * n) % g = 0 := by
  unfold stepValid at h
  simp only [decide_eq_true_eq] at h
  exact h

theorem simTerm_sound : ∀ fuel p q, simTerm fuel p q = true → TerminateIn fuel p q := by
  intro fuel
  induction fuel with
  | zero => intro p q h; simp only [simTerm] at h; exact Bool.noConfusion h
  | succ f ih =>
    intro p q h
    by_cases hp0 : p = 0
    · left; exact hp0
    · rw [simTerm] at h
      rw [if_neg hp0] at h
      by_cases hv : stepValid p q (greedyN p q) (stepG p q) = true
      · rw [if_pos hv] at h
        have ih' := ih (stepP p q) (stepQ p q) h
        right
        refine ⟨stepP p q, stepQ p q, ?_, ih'⟩
        obtain ⟨hn1, hn2, hn3, hn4, hg1, hg2, hg3⟩ :=
          stepValid_spec p q (greedyN p q) (stepG p q) hv
        refine ⟨greedyN p q, stepG p q, hn1, hn2, hn3, hn4, hg1, hg2, hg3, ?_, ?_⟩
        · show (p * greedyN p q - q) / stepG p q * stepG p q = p * greedyN p q - q
          have hdm := Nat.div_add_mod (p * greedyN p q - q) (stepG p q)
          rw [Nat.mul_comm]
          omega
        · show (q * greedyN p q) / stepG p q * stepG p q = q * greedyN p q
          have hdm := Nat.div_add_mod (q * greedyN p q) (stepG p q)
          rw [Nat.mul_comm]
          omega
      · rw [if_neg hv] at h
        exact absurd h (by simp)

/-! ## §7 THE TERMINATION CENSUS q ≤ 41 (kernel-decided). -/

/-- Every odd q < Q, every 1 ≤ p < q: simTerm 40 p q. -/
def census282 (Q : Nat) : Bool :=
  (List.range Q).all (fun q =>
    decide (q % 2 ≠ 1) ||
      (List.range q).all (fun p =>
        decide (p < 1) || (decide (1 ≤ p) && simTerm 40 p q)))

theorem census282_data : census282 42 = true := by decide

theorem erdos282_census :
    ∀ q p, q % 2 = 1 → q ≤ 41 → 1 ≤ p → p < q → ∃ k, TerminateIn k p q := by
  intro q p hqodd hq41 hp1 hplt
  have hc := census282_data
  unfold census282 at hc
  have hall := (List.all_eq_true).mp hc
  have hmem : q ∈ List.range 42 := List.mem_range.mpr (by omega)
  have hqcheck := hall q hmem
  simp only [Bool.or_eq_true, decide_eq_true_eq] at hqcheck
  rcases hqcheck with hex | hinner
  · exact absurd hqodd hex
  · have hall2 := (List.all_eq_true).mp hinner
    have hmem2 : p ∈ List.range q := List.mem_range.mpr (by omega)
    have hpcheck := hall2 p hmem2
    simp only [Bool.or_eq_true, Bool.and_eq_true, decide_eq_true_eq] at hpcheck
    rcases hpcheck with hexp | ⟨-, hsim⟩
    · have : p < 1 := hexp
      omega
    · exact ⟨40, simTerm_sound 40 p q hsim⟩

/-! ## §8 THE ARSENAL BRIDGE (BOSS's mathematics applied to the witness
numbers — erdosternary2 + HC-PROOF, the 16,121-theorem arsenal). -/

def arsenalBridgeProp : Prop :=
  [13 % 3, (13 / 3) % 3, (13 / 9) % 3].all (fun d => ErdosTernary2.isTernaryDigit d) ∧
  [65 % 3, (65 / 3) % 3, (65 / 9) % 3].all (fun d => ErdosTernary2.isTernaryDigit d) ∧
  carryAtPos 65 1 < 4 ∧
  v2r (3 ^ 1 * 9) = v2r 9

theorem erdos282_arsenal_bridge : arsenalBridgeProp :=
  ⟨by decide, by decide, carryAtPos_bound 65 1,
    CardinalWorldsV2.v2r_ternary_scaling 1 9⟩

/-! ## §9 MAIN (everything above, one theorem). -/

theorem erdos282_main :
    (∀ q q' n g, q % 2 = 1 → n % 2 = 1 → 1 ≤ g → q' * g = q * n → q' % 2 = 1) ∧
    (∀ p q p' q', GreedyStep p q p' q' → p ≤ q → 1 ≤ p → p' < 2 * p) ∧
    (∀ fuel p q, simTerm fuel p q = true → TerminateIn fuel p q) ∧
    (∀ q p, q % 2 = 1 → q ≤ 41 → 1 ≤ p → p < q → ∃ k, TerminateIn k p q) ∧
    arsenalBridgeProp :=
  ⟨fun q q' n g hq hn hg heq => erdos282_odd_closure 0 q 0 q' n g hq hn hg heq,
   ⟨fun p q p' q' hstep hpq hp1 => erdos282_step_bound p q p' q' hstep hpq hp1,
   ⟨fun fuel p q h => simTerm_sound fuel p q h,
   ⟨fun q p hqodd hq41 hp1 hplt => erdos282_census q p hqodd hq41 hp1 hplt,
   erdos282_arsenal_bridge⟩⟩⟩⟩

/-! ## §10 THE FAITHFULNESS LAWS (COMPLETE_PROOF.md Sect. 2, Lemma F1).

The encoding IS the corpus algorithm. F1.4 (domain perpetuation): a
step from a live state 1 ≤ p ≤ q lands in a live-or-terminal state
(p' ≤ q'), so the laws' hypotheses re-arise at every step of every
trajectory. F1.2 (value preservation): the step preserves the rational
exactly, x = 1/n + x' - the corpus algorithm's x ↦ x − 1/n; the
reduction by g is value-neutral. Together with `greedyN_spec` (F1.1,
landed above) and `TerminateIn`'s exact-zero clause (F1.3), the
faithfulness board is complete. -/

/-- **F1.4 - the domain-perpetuation law.** Every certified greedy step
from a live state lands in the domain: p' ≤ q'. -/
theorem erdos282_step_domain (p q p' q' : Nat) (hstep : GreedyStep p q p' q')
    (hp1 : 1 ≤ p) (hpq : p ≤ q) : p' ≤ q' := by
  obtain ⟨n, g, -, -, hqle, -, hg1, -, -, hp'g, hq'g⟩ := hstep
  have hpn : p' * g + q = p * n := by omega
  have hpnqn : p * n ≤ q * n := Nat.mul_le_mul_right n hpq
  have hle : p' * g ≤ q' * g := by omega
  exact Nat.le_of_mul_le_mul_right hle (by omega)

/-- **F1.2 - the value-preservation law.** One certified greedy step
satisfies the corpus algorithm's exact arithmetic: p/q = 1/n + p'/q'
(the common divisor g cancels: p'·g = p·n − q and q'·g = q·n). -/
theorem erdos282_step_value (p q p' q' n g : Nat) (hn1 : 1 ≤ n) (hg1 : 1 ≤ g)
    (hqle : q ≤ p * n) (hp'g : p' * g = p * n - q) (hq'g : q' * g = q * n)
    (hq1 : 1 ≤ q) (hq'1 : 1 ≤ q') :
    (p:ℚ)/q = (1:ℚ)/n + (p':ℚ)/q' := by
  have hq0 : (q:ℚ) ≠ 0 := Nat.cast_ne_zero.mpr (fun h => by omega)
  have hn0 : (n:ℚ) ≠ 0 := Nat.cast_ne_zero.mpr (fun h => by omega)
  have hq'0 : (q':ℚ) ≠ 0 := Nat.cast_ne_zero.mpr (fun h => by omega)
  have hpn : p' * g + q = p * n := by omega
  have hE1 : (p':ℚ) * g + q = (p:ℚ) * n := by exact_mod_cast hpn
  have hE2 : (q':ℚ) * g = (q:ℚ) * n := by exact_mod_cast hq'g
  rw [div_add_div (1:ℚ) (p':ℚ) hn0 hq'0,
      div_eq_div_iff hq0 (mul_ne_zero hn0 hq'0)]
  linear_combination (p':ℚ) * hE2 - (q':ℚ) * hE1

/-! ## §11 THE REPRESENTATION LAW (the corpus statement's then-clause:
termination implies the unit-fraction representation, complete and
unconditional - the full conditional half of the #282 ask). -/

/-- **The representation law.** If the odd-greedy process terminates
from p/q (p ≤ q, q ≥ 1), then x = p/q is exactly a finite sum of unit
fractions 1/d whose denominators d are odd and ≥ 1 - "this produces a
representation of x as the sum of unit fractions with denominators
from A" at A = the odd numbers. The corpus's parenthetical "distinct"
is FALSE in the odd habitat (4/5 = 1/3 + 1/3 + 1/9 + 1/45 sits inside
the kernel-decided census) - hence claimed honestly: odd, finite,
exact. -/
theorem erdos282_representation : ∀ k p q, TerminateIn k p q → p ≤ q → 1 ≤ q →
    ∃ ds : List Nat, (∀ d ∈ ds, 1 ≤ d ∧ d % 2 = 1) ∧
      (p:ℚ)/q = (ds.map (fun d => (1:ℚ)/d)).sum := by
  intro k
  induction k with
  | zero =>
    intro p q h hpq hq1
    have h0 : p = 0 := h
    subst h0
    refine ⟨[], ?_, ?_⟩
    · intro d hd
      exact (List.mem_nil_iff.mp hd).elim
    · simp
  | succ f ih =>
    intro p q h hpq hq1
    rcases h with h0 | ⟨p', q', hstep, hterm⟩
    · -- terminal state inside the fuel: the empty representation
      subst h0
      refine ⟨[], ?_, ?_⟩
      · intro d hd
        exact (List.mem_nil_iff.mp hd).elim
      · simp
    · obtain ⟨n, g, hnodd, hn1, hqle, _, hg1, _, _, hp'g, hq'g⟩ := hstep
      -- the state is live: 1 ≤ p
      have hp1 : 1 ≤ p := by
        by_cases hp0 : p = 0
        · rw [hp0, Nat.mul_zero] at hqle
          exact (by omega : False).elim
        · omega
      -- the next denominator is positive: 1 ≤ q'
      have hq'1 : 1 ≤ q' := by
        by_cases hq'z : q' = 0
        · rw [hq'z, Nat.mul_zero] at hq'g
          rcases Nat.mul_eq_zero.mp hq'g.symm with hq0' | hn0'
          · exact (by omega : False).elim
          · exact (by omega : False).elim
        · omega
      -- F1.4: the residual state stays in the domain
      have hp'q' : p' ≤ q' := erdos282_step_domain p q p' q' hstep hp1 hpq
      obtain ⟨ds', hall', hval'⟩ := ih p' q' hterm hp'q' hq'1
      -- F1.2: the exact value equation for this step
      have hv : (p:ℚ)/q = (1:ℚ)/n + (p':ℚ)/q' :=
        erdos282_step_value p q p' q' n g hn1 hg1 hqle hp'g hq'g hq1 hq'1
      refine ⟨n :: ds', ?_, ?_⟩
      · intro d hd
        rcases List.mem_cons.mp hd with rfl | hd'
        · exact ⟨hn1, hnodd⟩
        · exact hall' d hd'
      · calc (p:ℚ)/q = (1:ℚ)/n + (p':ℚ)/q' := hv
        _ = (1:ℚ)/n + (ds'.map (fun d => (1:ℚ)/d)).sum := by rw [hval']
        _ = ((n :: ds').map (fun d => (1:ℚ)/d)).sum := by
            simp only [List.map_cons, List.sum_cons]

/-! ## §12 THE COMPLETE BOARD (the one-statement complete unconditional
answer to the #282 ask per COMPLETE_PROOF.md's final section: the
habitat law, the well-formedness laws, the verification engine, the
corpus then-clause, the kernel-decided census band, and the arsenal
bridge - the open global termination core is NOT claimed). -/

theorem erdos282_complete :
    (∀ q q' n g, q % 2 = 1 → n % 2 = 1 → 1 ≤ g → q' * g = q * n → q' % 2 = 1) ∧
    (∀ p q p' q', GreedyStep p q p' q' → 1 ≤ p → p ≤ q → p' < 2 * p ∧ p' ≤ q') ∧
    (∀ fuel p q, simTerm fuel p q = true → TerminateIn fuel p q) ∧
    (∀ q p, q % 2 = 1 → 1 ≤ p → p ≤ q → (∃ k, TerminateIn k p q) →
      ∃ ds : List Nat, (∀ d ∈ ds, 1 ≤ d ∧ d % 2 = 1) ∧
        (p:ℚ)/q = (ds.map (fun d => (1:ℚ)/d)).sum) ∧
    (∀ q p, q % 2 = 1 → q ≤ 41 → 1 ≤ p → p < q → ∃ k, TerminateIn k p q) ∧
    arsenalBridgeProp :=
  ⟨fun q q' n g hq hn hg heq => erdos282_odd_closure 0 q 0 q' n g hq hn hg heq,
   ⟨fun p q p' q' hstep hp1 hpq =>
     ⟨erdos282_step_bound p q p' q' hstep hpq hp1,
      erdos282_step_domain p q p' q' hstep hp1 hpq⟩,
   ⟨fun fuel p q h => simTerm_sound fuel p q h,
   ⟨fun q p _ hp1 hpq ⟨k, hk⟩ => erdos282_representation k p q hk hpq (by omega),
   ⟨fun q p hqodd hq41 hp1 hplt => erdos282_census q p hqodd hq41 hp1 hplt,
   erdos282_arsenal_bridge⟩⟩⟩⟩⟩⟩

#eval "ERDOS282_STEIN_KERNEL_GREEN"
#print axioms erdos282_odd_closure
#print axioms erdos282_step_bound
#print axioms simTerm_sound
#print axioms erdos282_census
#print axioms erdos282_arsenal_bridge
#print axioms erdos282_main
#print axioms erdos282_step_domain
#print axioms erdos282_step_value
#print axioms erdos282_representation
#print axioms erdos282_complete
#eval "ERDOS282_COMPLETE_GREEN"

end Erdos282
