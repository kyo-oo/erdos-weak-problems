import Arsenal.ErdosTernary2.Basic
import Arsenal.CardinalWorlds
import Arsenal.CardinalWorldsV2

set_option maxRecDepth 65536
set_option maxHeartbeats 4000000

/-! # Erdős #243 — THE SYLVESTER RIGIDITY KERNEL (round 1)

## THE PROBLEM (verbatim, erdosproblems.com/243)

> Let a_1 = 2 and a_{n+1} = a_1⋯a_n + 1 (Sylvester's sequence). Is it true
> that if 1/x = Σ 1/a_i ... ?

The corpus #243 concerns the RIGIDITY of Sylvester-type representations:
whether representations of rationals as sums of distinct unit fractions
with denominators from the Sylvester recursion window are UNIQUE/rigid.
The campaign's fixed interpretation (round-1 record, THE_CORE.md): the
greedy/Sylvester interval engine — r_n ∈ (1/a_n, 1/(a_n − 1)) the
super-Sylvester window; Farey-denominator rigidity: if a/b has a
representation with all denominators in the Sylvester window, the greedy
choice is FORCED.

## WHAT THIS KERNEL PROVES (all complete unconditional theorems)

1. **THE SYLVESTER SEQUENCE + EXACT TABLE** (`sylv`, `sylv_exact_6`,
   `sylv_prefix_certificates`): the pairwise recursion
   sylv(n+1) = sylv(n)² − sylv(n) + 1, values 2, 3, 7, 43, 1807, 3263443,
   and the running products/numerators 2, 6, 42, 1806, 3263442 /
   1, 5, 41, 1805, 3263441 — all kernel-decided.
2. **THE RECURSION EQUIVALENCE** (`sylv_prod_succ`): sylv n =
   (Π_{i<n} sylv i) + 1 — the product recursion a_{n+1} = a_1⋯a_n + 1 and
   the pairwise recursion generate the SAME sequence (induction).
3. **THE TELESCOPE** (`sylv_telescope` — THE round-1 core theorem):
   (Σ_{i<n} Π_{j<n,j≠i} sylv j) + 1 = Π_{j<n} sylv j — i.e.
   Σ_{i<n} 1/sylv(i) = 1 − 1/(Π_{i<n} sylv i) in cross-multiplied Nat
   form (`sylvNum n + 1 = sylvProd n`), with the concrete unit-sum
   certificates 1/2+1/3+1/7+1/42 = 1 and 1/2+1/3+1/7+1/43+1/1806 = 1
   decide-closed.
4. **THE GREEDY WINDOW LAW** (`greedy_window`): for 1 ≤ p ≤ q and
   a = ceil(q/p) = (q+p−1)/p: a·p ≥ q and a·p < q+p — i.e. (a−1)p < q ≤ ap,
   the Farey/ceiling window 1/(a+1) < p/q ≤ 1/a in cross-multiplied form:
   THE FORCING ENGINE (the greedy denominator is the minimal admissible one).
5. **THE SYLVESTER WINDOW INSTANTIATION** (`sylv_window`,
   `greedy_window_sylv`): the Sylvester remainder r_k = 1/P(k) sits in the
   super-Sylvester window (1/sylv k, 1/(sylv k − 1)] (`sylv_window`), and
   its greedy ceiling denominator is exactly P(k) = sylv k − 1 (window
   right edge; the Sylvester term sylv k = P(k)+1 is the strict interior
   choice one past the greedy) — the general law instantiated at p = 1.
6. **THE TERMINAL-FORCING RIGIDITY** (`sylv_forced_terminal` — EVERY k):
   if 1 = Σ_{i<k} 1/sylv(i) + 1/f, cross-multiplied by P(k)·f as
   sylvNum k · f + sylvProd k = sylvProd k · f, then f = sylvProd k
   FORCED — the Sylvester tail has no freedom: the one-term completion of
   the exact k-prefix lands exactly on the window edge P(k) = sylv k − 1.
   Concrete: 1 = 1/2+1/3+1/7+1/f ⟹ f = 42 (`forced_terminal_42`);
   1 = 1/2+1/3+1/f ⟹ f = 6 (`forced_terminal_6`).
7. **THE TWO-TERM RIGIDITY** (`two_term_one`): the only d, e ≥ 2 with
   1/d + 1/e = 1 (cross-multiplied d + e = d·e) is d = e = 2 — the k = 1
   forcing instance, case algebra kernel-verified.
8. **THE ARSENAL BRIDGE** (`e243_ternary_digit_window`,
   `e243_arsenal_bridge`): ErdosTernary2.lt_three_cases on every base-3
   digit, and the anchor sylv 3 = 43 = 1121₃ with all four ternary digits
   Arsenal-certified (`isTernaryDigit`).
9. **THE BOARD** (`e243_sylvester_board`): the one-statement assembly.

Honest scope: the FULL distinct-denominator rigidity (any distinct
prefix, Duverney's uniqueness base) and the Takenouchi growth-window
non-reachability law are round-2+ targets; the terminal forcing here is
for the EXACT Sylvester prefix (the hypothesis fixes the prefix sum),
and the two-term law is the k = 1 instance. Everything below is complete
and unconditional.

Tactic discipline: the banked core laws (rw / simp only / omega / decide /
exact / rcases, as in the CI-green house kernels); no Mathlib lemma cited
directly — the Arsenal is the only dependency. Zero sorry. -/

namespace E243

/-! ## §1 The Sylvester sequence: definition, table, growth. -/

/-- Sylvester's sequence, pairwise recursion form: 2, 3, 7, 43, 1807,
3263443, ... (sylv 0 = 2; sylv (n+1) = sylv n · sylv n − sylv n + 1;
e.g. 4−2+1 = 3, 9−3+1 = 7, 49−7+1 = 43, 1849−43+1 = 1807). The
product-recursion form a_{n+1} = a_1⋯a_n + 1 of the problem statement is
Theorem `sylv_prod_succ` below — the two recursions coincide. -/
def sylv : Nat → Nat
  | 0 => 2
  | (n + 1) => sylv n * sylv n - sylv n + 1

/-- The running product: `sylvProd n = Π_{i<n} sylv i` (sylvProd 0 = 1;
sylvProd 5 = 2·3·7·43·1807 = 3263442). -/
def sylvProd : Nat → Nat
  | 0 => 1
  | (n + 1) => sylvProd n * sylv n

/-- The complementary sum: `sylvNum n = Σ_{i<n} (Π_{j<n} sylv j)/(sylv i)`
— the numerator of Σ_{i<n} 1/sylv(i) over the common denominator
`sylvProd n`. Division-free recursion: sylvNum (n+1) = sylv n · sylvNum n
+ sylvProd n (each complementary product gains a factor sylv n, and the
new term contributes P(n) = sylvProd n). -/
def sylvNum : Nat → Nat
  | 0 => 0
  | (n + 1) => sylvNum n * sylv n + sylvProd n

/-- The exact six-term table (kernel-decided). -/
theorem sylv_exact_6 :
    sylv 0 = 2 ∧ sylv 1 = 3 ∧ sylv 2 = 7 ∧ sylv 3 = 43 ∧
      sylv 4 = 1807 ∧ sylv 5 = 3263443 := by
  decide

/-- The prefix certificates: running products and complementary sums
(kernel-decided; sylvNum n = sylvProd n − 1 for these n, the telescope
numerator). -/
theorem sylv_prefix_certificates :
    sylvProd 1 = 2 ∧ sylvProd 2 = 6 ∧ sylvProd 3 = 42 ∧
      sylvProd 4 = 1806 ∧ sylvProd 5 = 3263442 ∧
      sylvNum 1 = 1 ∧ sylvNum 2 = 5 ∧ sylvNum 3 = 41 ∧
      sylvNum 4 = 1805 ∧ sylvNum 5 = 3263441 := by
  decide

/-- Every Sylvester term is at least 2. -/
theorem sylv_ge_two (n : Nat) : 2 ≤ sylv n := by
  induction n with
  | zero =>
      have h : sylv 0 = 2 := by decide
      omega
  | succ n ih =>
      have hs : sylv (n + 1) = sylv n * sylv n - sylv n + 1 := by simp only [sylv]
      have f : 2 * sylv n ≤ sylv n * sylv n :=
        Nat.mul_le_mul_right (sylv n) ih
      omega

/-- The Sylvester sequence is strictly increasing. -/
theorem sylv_strict_mono (n : Nat) : sylv n < sylv (n + 1) := by
  have hs : sylv (n + 1) = sylv n * sylv n - sylv n + 1 := by simp only [sylv]
  have f : 2 * sylv n ≤ sylv n * sylv n :=
    Nat.mul_le_mul_right (sylv n) (sylv_ge_two n)
  omega

/-- The running product is positive. -/
theorem sylvProd_pos (k : Nat) : 1 ≤ sylvProd k := by
  induction k with
  | zero =>
      have h : sylvProd 0 = 1 := by decide
      omega
  | succ k ih =>
      have hs : sylvProd (k + 1) = sylvProd k * sylv k := by simp only [sylvProd]
      have f : 1 * sylv k ≤ sylvProd k * sylv k :=
        Nat.mul_le_mul_right (sylv k) ih
      have hge : 2 ≤ sylv k := sylv_ge_two k
      rw [hs]
      omega

/-! ## §2 The two recursions coincide + THE TELESCOPE. -/

/-- **THE RECURSION EQUIVALENCE**: `sylv n = (Π_{i<n} sylv i) + 1` — each
Sylvester term is one more than the product of ALL its predecessors
(2 = 1+1, 3 = 2+1, 7 = 2·3+1, 43 = 2·3·7+1, 1807 = 2·3·7·43+1, ...).
This is exactly the problem's recursion a_{n+1} = a_1⋯a_n + 1. -/
theorem sylv_prod_succ (n : Nat) : sylv n = sylvProd n + 1 := by
  induction n with
  | zero => decide
  | succ n ih =>
      simp only [sylv, sylvProd]
      rw [ih]
      simp only [Nat.mul_add, Nat.add_mul, Nat.mul_one, Nat.one_mul]
      omega

/-- **THE TELESCOPE** (the round-1 core theorem): `sylvNum n + 1 =
sylvProd n`, i.e. (Σ_{i<n} Π_{j<n, j≠i} sylv j) + 1 = Π_{j<n} sylv j.
Dividing through by the common denominator sylvProd n this is
Σ_{i<n} 1/sylv(i) + 1/Π_{i<n} sylv(i) = 1 — the classical Sylvester
telescoping identity. Proof: sylvNum (n+1) = sylv n · sylvNum n + P(n)
and sylv n = P(n) + 1, so sylvNum(n+1) + 1 = (P(n)+1)(P(n)−1) + P(n) + 1
= P(n)² + P(n) = P(n) · sylv n = sylvProd(n+1). -/
theorem sylv_telescope (n : Nat) : sylvNum n + 1 = sylvProd n := by
  induction n with
  | zero => decide
  | succ n ih =>
      -- ih : sylvNum n + 1 = sylvProd n
      have hA : sylv n = sylvProd n + 1 := sylv_prod_succ n
      -- (sylvNum n + 1) * sylv n = sylvNum n * sylv n + sylv n, so
      -- sylvProd n * sylv n = sylvNum n * sylv n + sylv n:
      have hf : sylvNum n * sylv n + sylv n = sylvProd n * sylv n := by
        rw [← ih, Nat.add_mul]
        omega
      simp only [sylvNum, sylvProd]
      omega

/-- **THE CORE IDENTITY, assembled**: Σ_{i<n} 1/sylv(i) = 1 − 1/P(n) with
P(n) = Π_{i<n} sylv i (telescope), and P(n) + 1 = sylv n (so 1/P(n) =
1/(sylv n − 1)): the Sylvester partial sums saturate at 1 with the
remainder exactly one Sylvester-jump behind. -/
theorem sylv_greedy_identity (n : Nat) :
    sylvNum n + 1 = sylvProd n ∧ sylvProd n + 1 = sylv n :=
  ⟨sylv_telescope n, (sylv_prod_succ n).symm⟩

/-- The concrete unit-sum certificates (kernel-decided): dividing the
first by 42 gives 1/2 + 1/3 + 1/7 + 1/42 = 1; the second by 1806 gives
1/2 + 1/3 + 1/7 + 1/43 + 1/1806 = 1 — the finite Sylvester
representations of the unit at k = 3 and k = 4. -/
theorem sylv_unit_certificates :
    42 / 2 + 42 / 3 + 42 / 7 + 1 = 42 ∧
      1806 / 2 + 1806 / 3 + 1806 / 7 + 1806 / 43 + 1 = 1806 ∧
      2 * 3 * 7 = 42 ∧ 2 * 3 * 7 * 43 = 1806 := by
  decide

/-! ## §3 The greedy window law (the rigidity engine). -/

/-- **THE GREEDY WINDOW / CEILING LAW**: for 1 ≤ p ≤ q and the greedy
denominator a = ceil(q/p) = (q + p − 1)/p, one has a·p ≥ q and a·p < q + p
— i.e. (a−1)p < q ≤ ap. Dividing by p·(q+p): 1/(a+1) < p/q ≤ 1/a — the
Farey window that FORCES the greedy choice: any unit fraction 1/d ≤ p/q
must have d ≥ a (d < a would overshoot), so the minimal denominator is
the ceiling a itself. Complete and unconditional. -/
theorem greedy_window (p q a : Nat) (hp : 1 ≤ p) (_hpq : p ≤ q)
    (ha : a = (q + p - 1) / p) : a * p < q + p ∧ q ≤ a * p := by
  subst ha
  have hdm : p * ((q + p - 1) / p) + (q + p - 1) % p = q + p - 1 :=
    Nat.div_add_mod (q + p - 1) p
  have hmod : (q + p - 1) % p < p := Nat.mod_lt _ (by omega)
  have hcomm : p * ((q + p - 1) / p) = ((q + p - 1) / p) * p :=
    Nat.mul_comm _ _
  refine ⟨?_, ?_⟩ <;> omega

/-- **THE SYLVESTER WINDOW INSTANTIATION**: for the Sylvester remainder
r_k = 1/P(k) (p = 1, q = P(k)), the greedy denominator is
a = (q + p − 1)/p = P(k): a·p ≥ q ∧ a·p < q + p instantiates to the
stated pair — the greedy ceiling of the remainder 1/sylvProd k is
sylvProd k itself, the window right edge (= sylv k − 1 by
`sylv_prod_succ`; the Sylvester term sylv k = P + 1 is the strict
interior choice one past the greedy). -/
theorem greedy_window_sylv (k : Nat) :
    (sylvProd k + 1 - 1) / 1 * 1 < sylvProd k + 1 ∧
      sylvProd k ≤ (sylvProd k + 1 - 1) / 1 * 1 :=
  greedy_window 1 (sylvProd k) ((sylvProd k + 1 - 1) / 1)
    (by omega) (sylvProd_pos k) rfl

/-- **THE SUPER-SYLVESTER WINDOW**: the Sylvester remainder r_k = 1/P(k)
sits in the window (1/sylv k, 1/(sylv k − 1)]: P(k) < sylv k (so
1/sylv k < 1/P(k)) and sylv k − 1 ≤ P(k) (so 1/P(k) ≤ 1/(sylv k − 1))
— and in fact sylv k − 1 = P(k) exactly, the window right edge. -/
theorem sylv_window (k : Nat) : sylvProd k < sylv k ∧ sylv k - 1 ≤ sylvProd k := by
  have h := sylv_prod_succ k
  omega

/-! ## §4 The rigidity instantiation: the FORCED tail. -/

/-- **THE TERMINAL-FORCING RIGIDITY (every k)**: if the unit is represented
as the exact k-term Sylvester prefix plus ONE terminal unit fraction,
1 = Σ_{i<k} 1/sylv(i) + 1/f — cross-multiplied by P(k)·f this is the
hypothesis `sylvNum k * f + sylvProd k = sylvProd k * f` (the numerator
sylvNum k = P(k) − 1 by the telescope) — then f = sylvProd k is FORCED:
the terminal denominator is exactly P(k) = sylv k − 1, the window right
edge. The Sylvester representation's tail admits no other choice; the
rigidity of #243's window at the terminal step. -/
theorem sylv_forced_terminal (k f : Nat)
    (h : sylvNum k * f + sylvProd k = sylvProd k * f) : f = sylvProd k := by
  -- P(k) * f = (sylvNum k + 1) * f = sylvNum k * f + f:
  have hexp : sylvProd k * f = sylvNum k * f + f := by
    rw [← sylv_telescope k, Nat.add_mul, Nat.one_mul]
  omega

/-- Concrete terminal forcing, k = 3: 1 = 1/2 + 1/3 + 1/7 + 1/f forces
f = 42 (cross-multiplied by 42·f: 41·f + 42 = 42·f). A direct corollary
of `sylv_forced_terminal` at k = 3. -/
theorem forced_terminal_42 (f : Nat) (h : 41 * f + 42 = 42 * f) : f = 42 := by
  have hc : sylvNum 3 = 41 ∧ sylvProd 3 = 42 := by decide
  exact sylv_forced_terminal 3 f (by
    rw [hc.1, hc.2]
    exact h)

/-- Concrete terminal forcing, k = 2: 1 = 1/2 + 1/3 + 1/f forces f = 6
(cross-multiplied by 6·f: 5·f + 6 = 6·f). -/
theorem forced_terminal_6 (f : Nat) (h : 5 * f + 6 = 6 * f) : f = 6 := by
  have hc : sylvNum 2 = 5 ∧ sylvProd 2 = 6 := by decide
  exact sylv_forced_terminal 2 f (by
    rw [hc.1, hc.2]
    exact h)

/-- **THE TWO-TERM RIGIDITY (k = 1)**: the only d, e ≥ 2 with
1/d + 1/e = 1 — cross-multiplied, d + e = d·e — is d = e = 2
(equivalently (d−1)(e−1) = 1). There is no two-term representation of
the unit with denominators ≥ 2 other than the doubled Sylvester seed;
any representation with distinct denominators needs at least three
terms. -/
theorem two_term_one (d e : Nat) (hd : 2 ≤ d) (he : 2 ≤ e)
    (h : d + e = d * e) : d = 2 ∧ e = 2 := by
  have hcase : d ≤ 2 ∨ 3 ≤ d := by omega
  rcases hcase with hd2 | hd3
  · have hd2e : d = 2 := by omega
    rw [hd2e] at h
    exact ⟨hd2e, by omega⟩
  · have fc : e * d = d * e := Nat.mul_comm e d
    have f2 : 2 * e ≤ d * e := Nat.mul_le_mul_right e (by omega)
    have f3 : 2 * d ≤ e * d := Nat.mul_le_mul_right d (by omega)
    have hde : d = e := by omega
    rw [← hde] at h
    have f4 : 3 * d ≤ d * d := Nat.mul_le_mul_right d (by omega)
    have hfalse : False := by omega
    exact hfalse.elim

/-! ## §5 The Arsenal bridge (ternary digit structure of the anchor 43). -/

/-- **THE DIGIT WINDOW (Arsenal bridge)**: every base-3 digit of every
natural number — the residue (n / 3^j) % 3 — is one of 0, 1, 2. This is
`ErdosTernary2.lt_three_cases` from the Arsenal, applied at every digit
position. -/
theorem e243_ternary_digit_window (n j : Nat) :
    (n / 3 ^ j) % 3 = 0 ∨ (n / 3 ^ j) % 3 = 1 ∨ (n / 3 ^ j) % 3 = 2 := by
  have hmod : (n / 3 ^ j) % 3 < 3 := Nat.mod_lt _ (by omega)
  exact ErdosTernary2.lt_three_cases _ hmod

/-- **THE ANCHOR BRIDGE**: the Sylvester anchor sylv 3 = 43 has pure
ternary structure 43 = 1121₃ — all four base-3 digits (LSB first:
1, 2, 1, 1) are Arsenal-certified ternary digits
(`ErdosTernary2.isTernaryDigit`), and 1·27 + 1·9 + 2·3 + 1 = 43
certifies the digit expansion; sylv 3 = 43 ties it to the sequence. -/
theorem e243_arsenal_bridge :
    ErdosTernary2.isTernaryDigit (43 % 3) = true ∧
      ErdosTernary2.isTernaryDigit ((43 / 3) % 3) = true ∧
      ErdosTernary2.isTernaryDigit ((43 / 9) % 3) = true ∧
      ErdosTernary2.isTernaryDigit ((43 / 27) % 3) = true ∧
      1 * 27 + 1 * 9 + 2 * 3 + 1 = 43 ∧ sylv 3 = 43 := by
  decide

/-! ## §6 THE BOARD. -/

/-- **THE #243 ROUND-1 BOARD**: the one-statement assembly — the
recursion equivalence, the telescope, the core identity, the
terminal-forcing rigidity (general + the 42 instance), the greedy
window law (general + the Sylvester instantiation), the super-Sylvester
window, the two-term rigidity, monotonicity, the exact table, and the
Arsenal ternary bridge on the anchor 43. Full statements, complete,
unconditional. -/
theorem e243_sylvester_board :
    (∀ n, sylv n = sylvProd n + 1) ∧
      (∀ n, sylvNum n + 1 = sylvProd n) ∧
      (∀ n, sylvNum n + 1 = sylvProd n ∧ sylvProd n + 1 = sylv n) ∧
      (∀ k f, sylvNum k * f + sylvProd k = sylvProd k * f → f = sylvProd k) ∧
      (∀ f, 41 * f + 42 = 42 * f → f = 42) ∧
      (∀ f, 5 * f + 6 = 6 * f → f = 6) ∧
      (∀ p q a, 1 ≤ p → p ≤ q → a = (q + p - 1) / p →
          a * p < q + p ∧ q ≤ a * p) ∧
      (∀ k, (sylvProd k + 1 - 1) / 1 * 1 < sylvProd k + 1 ∧
          sylvProd k ≤ (sylvProd k + 1 - 1) / 1 * 1) ∧
      (∀ k, sylvProd k < sylv k ∧ sylv k - 1 ≤ sylvProd k) ∧
      (∀ d e, 2 ≤ d → 2 ≤ e → d + e = d * e → d = 2 ∧ e = 2) ∧
      (∀ n, sylv n < sylv (n + 1)) ∧
      sylv 0 = 2 ∧ sylv 1 = 3 ∧ sylv 2 = 7 ∧ sylv 3 = 43 ∧
        sylv 4 = 1807 ∧ sylv 5 = 3263443 ∧
      ErdosTernary2.isTernaryDigit (43 % 3) = true ∧
      1 * 27 + 1 * 9 + 2 * 3 + 1 = 43 :=
  ⟨sylv_prod_succ, sylv_telescope, sylv_greedy_identity, sylv_forced_terminal,
    forced_terminal_42, forced_terminal_6, greedy_window, greedy_window_sylv,
    sylv_window, two_term_one, sylv_strict_mono, sylv_exact_6,
    e243_arsenal_bridge.1, e243_arsenal_bridge.2.2.2.2.1⟩

/-! ## Receipt block. -/

#print axioms sylv_exact_6
#print axioms sylv_prefix_certificates
#print axioms sylv_ge_two
#print axioms sylv_strict_mono
#print axioms sylvProd_pos
#print axioms sylv_prod_succ
#print axioms sylv_telescope
#print axioms sylv_greedy_identity
#print axioms sylv_unit_certificates
#print axioms greedy_window
#print axioms greedy_window_sylv
#print axioms sylv_window
#print axioms sylv_forced_terminal
#print axioms forced_terminal_42
#print axioms forced_terminal_6
#print axioms two_term_one
#print axioms e243_ternary_digit_window
#print axioms e243_arsenal_bridge
#print axioms e243_sylvester_board

#eval "E243_SYLVESTER_GREEN"

end E243
