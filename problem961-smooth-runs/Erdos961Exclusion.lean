import Erdos961Census_Base
import Arsenal.ErdosTernary2.Basic
import Arsenal.CardinalWorlds
import Arsenal.CardinalWorldsV2

set_option maxRecDepth 65536
set_option maxHeartbeats 4000000

/-! # Erdos961Exclusion — THE EXCLUSION SIDE (Kernel 48, W56-1)

The Størmer–Pell exclusion layers for Erdős #961, built on the GREEN
Kernel-46 machine (`Erdos961Census_Base`, namespace `E961P`):

1. **TOWER ORDERING LAWS** (`pell_tower_X_pos`, `pell_tower_Y_pos`,
   `pell_tower_X_strict_mono`, `pell_tower_Y_strict_mono`): the Pell
   tower `E961P.Pell a X1 Y1 n` (the n-fold Brahmagupta power of the
   fundamental solution (X₁, Y₁)) is strictly increasing in BOTH
   coordinates, for every a ≥ 1, X₁ ≥ 2, Y₁ ≥ 1 — proved by direct
   definitional unfolding of the tower recursion
   `X_{n+1} = X₁·X_n + a·Y₁·Y_n`, `Y_{n+1} = X₁·Y_n + Y₁·X_n`, with
   omega-linear bookkeeping. The L86 atom law is respected throughout:
   every product bound is produced in the EXACT goal spelling via
   `Nat.mul_le_mul_left/right`.
2. **THE GROWTH LAW** (`pell_tower_growth`): the exponential lower
   bound `2^(n+1) ≤ X_{n+1}` — the doubling inequality `2·X_n ≤ X_{n+1}`
   chained through the power induction. Plus the exponential upper
   bound `pell_tower_exp_bound` (`X_n ≤ (X₁ + a·Y₁ + Y₁)^n`). NOTE:
   the naive form `X_n ≤ (X₁+1)^n` is FALSE in general (a = 2 with
   (X₁,Y₁) = (3,2): X₂ = 17 > 16); the corrected M-bound is certified
   here instead.
3. **THE POWER REPRESENTATION LAW** (`pell_tower_sol_all`): every tower
   member of a genuine fundamental solution is itself a Pell solution
   (restated from the base kernel in this namespace).
4. **THE 29-a INSTANTIATION** (the famous hard case): the fundamental
   solution (9801, 1820) of X² − 29·Y² = 1 — decide-certified in both
   the subtraction form (`pell29_fundamental`) and the solution form
   (`pell29_fundamental_sol`) — its tower's growth law instance
   (`pell29_tower_growth`), its solution law (`pell29_tower_sol`),
   and the exact decide-certified tower members 1 and 2
   (`pell29_tower_one`, `pell29_tower_two`).
5. **THE EXCLUSION BOARD** (`e961x_exclusion_board`): the 8-conjunct
   master assembly chaining all of the above — full statements,
   unconditional, zero sorry.

The power stepping stones (`pow2_step`, `powMul_step`) are proven
orientation-blind (`first | rfl | rw [Nat.mul_comm]`), so the file does
not depend on the exact statement orientation of core `Nat.pow`
lemmas. Core-only Lean 4 (Nat, omega, ring, decide) on the Arsenal
import set. No Mathlib tactics beyond that. No sorry. No axiom. No
native_decide. -/
namespace E961X

/-! ## §0 Power stepping stones (r2 repair: the r1 orientation-blind
`first | rfl | rw` failed on the LEFT-multiplied 2-power goal — CI run
43311092381 post-mortem: `rfl` does not close `2 ^ (k+1) = 2 * 2 ^ k`
definitionally, and the rw-reordered goal `2 ^ (k+1) = 2 ^ k * 2` is
EXACTLY the right-orientation step. Fix: prove the right-orientation
step first (rfl — CI-verified in r1), then chain through comm.). -/

/-- The power recursion in the right-multiplied orientation (used for
the M-bound expansion; r1-CI-verified closes by rfl). -/
theorem powMul_step (M k : Nat) : M ^ (k + 1) = M ^ k * M := by
  rfl

/-- The 2-power recursion in the left-multiplied orientation: rw turns
the goal into `2 ^ (k + 1) = 2 ^ k * 2` (the exact r1 CI evidence),
which is `powMul_step 2 k` verbatim. -/
theorem pow2_step : ∀ k : Nat, 2 ^ (k + 1) = 2 * 2 ^ k := by
  intro k
  rw [Nat.mul_comm]
  exact powMul_step 2 k

/-! ## §1 Tower ordering laws (on the Kernel-46 Pell machine). -/

/-- Positivity of the X-column of every tower member — the base of all
the ordering laws (X₀ = 1, X_{n+1} = X₁·X_n + a·Y₁·Y_n ≥ X_n ≥ 1). -/
theorem pell_tower_X_pos : ∀ (a X1 Y1 n : Nat), 2 ≤ X1 →
    1 ≤ (E961P.Pell a X1 Y1 n).1 := by
  intro a X1 Y1 n hX1
  induction n with
  | zero =>
      show 1 ≤ 1
      omega
  | succ m ih =>
      show 1 ≤ X1 * (E961P.Pell a X1 Y1 m).1 + a * Y1 * (E961P.Pell a X1 Y1 m).2
      have h1 : 1 * (E961P.Pell a X1 Y1 m).1 ≤ X1 * (E961P.Pell a X1 Y1 m).1 :=
        Nat.mul_le_mul_right _ (by omega)
      omega

/-- Positivity of the Y-column of every POSITIVE tower member
(Y₀ = 0, so the law is stated at n+1: Y_{n+1} ≥ Y₁·X_n ≥ 1). -/
theorem pell_tower_Y_pos : ∀ (a X1 Y1 n : Nat), 1 ≤ a → 2 ≤ X1 → 1 ≤ Y1 →
    1 ≤ (E961P.Pell a X1 Y1 (n+1)).2 := by
  intro a X1 Y1 n ha hX1 hY1
  show 1 ≤ X1 * (E961P.Pell a X1 Y1 n).2 + Y1 * (E961P.Pell a X1 Y1 n).1
  have hXp : 1 ≤ (E961P.Pell a X1 Y1 n).1 := pell_tower_X_pos a X1 Y1 n hX1
  have hY1X : 1 ≤ Y1 * (E961P.Pell a X1 Y1 n).1 := by
    have h : 1 * 1 ≤ Y1 * (E961P.Pell a X1 Y1 n).1 :=
      Nat.mul_le_mul hY1 hXp
    rw [Nat.mul_one] at h
    exact h
  omega

/-- THE X-ORDERING LAW: the Pell tower is strictly increasing in its
X-column — X_{n+1} = X₁·X_n + a·Y₁·Y_n ≥ 2·X_n > X_n for every n. -/
theorem pell_tower_X_strict_mono : ∀ (a X1 Y1 n : Nat), 1 ≤ a → 2 ≤ X1 → 1 ≤ Y1 →
    (E961P.Pell a X1 Y1 n).1 < (E961P.Pell a X1 Y1 (n+1)).1 := by
  intro a X1 Y1 n ha hX1 hY1
  show (E961P.Pell a X1 Y1 n).1 < X1 * (E961P.Pell a X1 Y1 n).1 + a * Y1 * (E961P.Pell a X1 Y1 n).2
  have hXp : 1 ≤ (E961P.Pell a X1 Y1 n).1 := pell_tower_X_pos a X1 Y1 n hX1
  have h2 : 2 * (E961P.Pell a X1 Y1 n).1 ≤ X1 * (E961P.Pell a X1 Y1 n).1 :=
    Nat.mul_le_mul_right _ hX1
  omega

/-- THE Y-ORDERING LAW: the Pell tower is strictly increasing in its
Y-column — Y_{n+1} = X₁·Y_n + Y₁·X_n ≥ Y_n + 1 (Y₁·X_n ≥ 1) for every
n, including n = 0 (Y₁ ≥ 1 > 0 = Y₀). -/
theorem pell_tower_Y_strict_mono : ∀ (a X1 Y1 n : Nat), 1 ≤ a → 2 ≤ X1 → 1 ≤ Y1 →
    (E961P.Pell a X1 Y1 n).2 < (E961P.Pell a X1 Y1 (n+1)).2 := by
  intro a X1 Y1 n ha hX1 hY1
  show (E961P.Pell a X1 Y1 n).2 < X1 * (E961P.Pell a X1 Y1 n).2 + Y1 * (E961P.Pell a X1 Y1 n).1
  have hXp : 1 ≤ (E961P.Pell a X1 Y1 n).1 := pell_tower_X_pos a X1 Y1 n hX1
  have hY1X : 1 ≤ Y1 * (E961P.Pell a X1 Y1 n).1 := by
    have h : 1 * 1 ≤ Y1 * (E961P.Pell a X1 Y1 n).1 :=
      Nat.mul_le_mul hY1 hXp
    rw [Nat.mul_one] at h
    exact h
  have hX1Y : 1 * (E961P.Pell a X1 Y1 n).2 ≤ X1 * (E961P.Pell a X1 Y1 n).2 :=
    Nat.mul_le_mul_right _ (by omega)
  omega

/-! ## §2 The growth laws. -/

/-- THE GROWTH LAW (exponential lower bound): the Pell tower at least
doubles at every step — 2^(n+1) ≤ X_{n+1}. The doubling inequality
2·X_n ≤ X_{n+1} (from X₁ ≥ 2) is chained through the power induction;
the power step goes through `pow2_step`, and the final chaining is a
pure term-level `Nat.le_trans` cascade (omega never touches a power). -/
theorem pell_tower_growth : ∀ (a X1 Y1 n : Nat), 1 ≤ a → 2 ≤ X1 → 1 ≤ Y1 →
    2^(n+1) ≤ (E961P.Pell a X1 Y1 (n+1)).1 := by
  intro a X1 Y1 n ha hX1 hY1
  induction n with
  | zero =>
      show 2 ≤ X1 * 1 + a * Y1 * 0
      simp only [Nat.mul_one, Nat.mul_zero, Nat.add_zero]
      omega
  | succ m ih =>
      show 2 ^ (m + 1 + 1) ≤ X1 * (E961P.Pell a X1 Y1 (m+1)).1 + a * Y1 * (E961P.Pell a X1 Y1 (m+1)).2
      rw [pow2_step (m + 1)]
      have h1 : 2 * 2 ^ (m + 1) ≤ 2 * (E961P.Pell a X1 Y1 (m+1)).1 :=
        Nat.mul_le_mul_left _ ih
      have h2 : 2 * (E961P.Pell a X1 Y1 (m+1)).1
          ≤ X1 * (E961P.Pell a X1 Y1 (m+1)).1 :=
        Nat.mul_le_mul_right _ hX1
      have h3 : X1 * (E961P.Pell a X1 Y1 (m+1)).1
          ≤ X1 * (E961P.Pell a X1 Y1 (m+1)).1
            + a * Y1 * (E961P.Pell a X1 Y1 (m+1)).2 :=
        Nat.le_add_right _ _
      exact Nat.le_trans h1 (Nat.le_trans h2 h3)

/-- THE EXPONENTIAL UPPER BOUND (corrected form): X_n ≤ M^n with
M := X₁ + a·Y₁ + Y₁. Proved by the simultaneous induction
(X_n ≤ M^n) ∧ (Y_n ≤ M^n): both columns of the tower step
X_{k+1} = X₁·X_k + a·Y₁·Y_k, Y_{k+1} = X₁·Y_k + Y₁·X_k, are bounded
through `Nat.mul_le_mul_left` against the ring-expanded M-step
`powMul_step`. The naive form (X₁+1)^n is FALSE in general
(a = 2, (X₁,Y₁) = (3,2): X₂ = 17 > 16). -/
theorem pell_tower_exp_bound : ∀ (a X1 Y1 n : Nat), 1 ≤ a → 2 ≤ X1 → 1 ≤ Y1 →
    (E961P.Pell a X1 Y1 n).1 ≤ (X1 + a * Y1 + Y1)^n := by
  intro a X1 Y1 n ha hX1 hY1
  have hboth : ∀ k : Nat,
      (E961P.Pell a X1 Y1 k).1 ≤ (X1 + a * Y1 + Y1)^k
      ∧ (E961P.Pell a X1 Y1 k).2 ≤ (X1 + a * Y1 + Y1)^k := by
    intro j
    induction j with
    | zero =>
        constructor
        · show 1 ≤ 1
          omega
        · show 0 ≤ 1
          omega
    | succ k ih =>
        obtain ⟨hXk, hYk⟩ := ih
        have hMM : (X1 + a * Y1 + Y1) ^ k * (X1 + a * Y1 + Y1)
            = X1 * (X1 + a * Y1 + Y1) ^ k + a * Y1 * (X1 + a * Y1 + Y1) ^ k
              + Y1 * (X1 + a * Y1 + Y1) ^ k := by
          ring
        constructor
        · show X1 * (E961P.Pell a X1 Y1 k).1 + a * Y1 * (E961P.Pell a X1 Y1 k).2
              ≤ (X1 + a * Y1 + Y1) ^ (k + 1)
          rw [powMul_step, hMM]
          have i1 : X1 * (E961P.Pell a X1 Y1 k).1
              ≤ X1 * (X1 + a * Y1 + Y1) ^ k :=
            Nat.mul_le_mul_left _ hXk
          have i2 : a * Y1 * (E961P.Pell a X1 Y1 k).2
              ≤ a * Y1 * (X1 + a * Y1 + Y1) ^ k :=
            Nat.mul_le_mul_left _ hYk
          omega
        · show X1 * (E961P.Pell a X1 Y1 k).2 + Y1 * (E961P.Pell a X1 Y1 k).1
              ≤ (X1 + a * Y1 + Y1) ^ (k + 1)
          rw [powMul_step, hMM]
          have i3 : X1 * (E961P.Pell a X1 Y1 k).2
              ≤ X1 * (X1 + a * Y1 + Y1) ^ k :=
            Nat.mul_le_mul_left _ hYk
          have i4 : Y1 * (E961P.Pell a X1 Y1 k).1
              ≤ Y1 * (X1 + a * Y1 + Y1) ^ k :=
            Nat.mul_le_mul_left _ hXk
          omega
  exact (hboth n).1

/-! ## §3 The power-representation law (restated from the base kernel). -/

/-- Every positive tower member of a genuine fundamental solution is
itself a Pell solution — the power representation of the solution set
(`E961P.pell_sol` restated in this namespace). -/
theorem pell_tower_sol_all : ∀ (a X1 Y1 n : Nat), X1 * X1 = a * Y1 * Y1 + 1 →
    (E961P.Pell a X1 Y1 (n+1)).1 * (E961P.Pell a X1 Y1 (n+1)).1
      = a * (E961P.Pell a X1 Y1 (n+1)).2 * (E961P.Pell a X1 Y1 (n+1)).2 + 1 := by
  intro a X1 Y1 n hf
  exact E961P.pell_sol a X1 Y1 hf n

/-! ## §4 THE 29-a INSTANTIATION (the famous hard case). -/

/-- THE FUNDAMENTAL SOLUTION of X² − 29·Y² = 1 is (9801, 1820), in the
subtraction form (decide-certified on the closed numerics:
9801² = 96059601, 29·1820² = 96059600). -/
theorem pell29_fundamental : 9801 * 9801 - 29 * 1820 * 1820 = 1 := by
  decide

/-- The solution form of the 29-a fundamental (decide-certified). -/
theorem pell29_fundamental_sol : 9801 * 9801 = 29 * 1820 * 1820 + 1 := by
  decide

/-- The 29-a tower obeys the growth law: 2^(n+1) ≤ X_{n+1}. -/
theorem pell29_tower_growth : ∀ n : Nat,
    2^(n+1) ≤ (E961P.Pell 29 9801 1820 (n+1)).1 := by
  intro n
  exact pell_tower_growth 29 9801 1820 n (by omega) (by omega) (by omega)

/-- Every 29-a tower member is a 29-a Pell solution (the power
representation at a = 29, on the decide-certified fundamental). -/
theorem pell29_tower_sol : ∀ n : Nat,
    (E961P.Pell 29 9801 1820 (n+1)).1 * (E961P.Pell 29 9801 1820 (n+1)).1
      = 29 * (E961P.Pell 29 9801 1820 (n+1)).2
        * (E961P.Pell 29 9801 1820 (n+1)).2 + 1 := by
  intro n
  exact E961P.pell_sol 29 9801 1820 pell29_fundamental_sol n

/-- Tower member 1, exactly: the fundamental itself (decide-certified). -/
theorem pell29_tower_one : (E961P.Pell 29 9801 1820 1).1 = 9801
    ∧ (E961P.Pell 29 9801 1820 1).2 = 1820 := by
  constructor
  · decide
  · decide

/-- Tower member 2, exactly: (192119201, 35675640) — the Brahmagupta
square of the fundamental (9801² + 29·1820², 2·9801·1820)
(decide-certified). -/
theorem pell29_tower_two : (E961P.Pell 29 9801 1820 2).1 = 192119201
    ∧ (E961P.Pell 29 9801 1820 2).2 = 35675640 := by
  constructor
  · decide
  · decide

/-! ## §5 THE EXCLUSION BOARD (master assembly). -/

/-- THE EXCLUSION KERNEL MASTER BOARD (8 conjuncts, full statements,
unconditional): the X-ordering law + the Y-ordering law + Y-positivity
+ the growth law + the exponential upper bound + the 29-a fundamental
(solution form) + the 29-a growth instance + the 29-a solution law. -/
theorem e961x_exclusion_board :
    (∀ (a X1 Y1 n : Nat), 1 ≤ a → 2 ≤ X1 → 1 ≤ Y1 →
      (E961P.Pell a X1 Y1 n).1 < (E961P.Pell a X1 Y1 (n+1)).1)
    ∧ (∀ (a X1 Y1 n : Nat), 1 ≤ a → 2 ≤ X1 → 1 ≤ Y1 →
      (E961P.Pell a X1 Y1 n).2 < (E961P.Pell a X1 Y1 (n+1)).2)
    ∧ (∀ (a X1 Y1 n : Nat), 1 ≤ a → 2 ≤ X1 → 1 ≤ Y1 →
      1 ≤ (E961P.Pell a X1 Y1 (n+1)).2)
    ∧ (∀ (a X1 Y1 n : Nat), 1 ≤ a → 2 ≤ X1 → 1 ≤ Y1 →
      2^(n+1) ≤ (E961P.Pell a X1 Y1 (n+1)).1)
    ∧ (∀ (a X1 Y1 n : Nat), 1 ≤ a → 2 ≤ X1 → 1 ≤ Y1 →
      (E961P.Pell a X1 Y1 n).1 ≤ (X1 + a * Y1 + Y1)^n)
    ∧ (9801 * 9801 = 29 * 1820 * 1820 + 1)
    ∧ (∀ n : Nat, 2^(n+1) ≤ (E961P.Pell 29 9801 1820 (n+1)).1)
    ∧ (∀ n : Nat,
      (E961P.Pell 29 9801 1820 (n+1)).1 * (E961P.Pell 29 9801 1820 (n+1)).1
        = 29 * (E961P.Pell 29 9801 1820 (n+1)).2
          * (E961P.Pell 29 9801 1820 (n+1)).2 + 1) :=
  ⟨pell_tower_X_strict_mono, pell_tower_Y_strict_mono, pell_tower_Y_pos,
    pell_tower_growth, pell_tower_exp_bound, pell29_fundamental_sol,
    pell29_tower_growth, pell29_tower_sol⟩

#print axioms pow2_step
#print axioms powMul_step
#print axioms pell_tower_X_pos
#print axioms pell_tower_Y_pos
#print axioms pell_tower_X_strict_mono
#print axioms pell_tower_Y_strict_mono
#print axioms pell_tower_growth
#print axioms pell_tower_exp_bound
#print axioms pell_tower_sol_all
#print axioms pell29_fundamental
#print axioms pell29_fundamental_sol
#print axioms pell29_tower_growth
#print axioms pell29_tower_sol
#print axioms pell29_tower_one
#print axioms pell29_tower_two
#print axioms e961x_exclusion_board
#eval "E961X_EXCLUSION_GREEN"
end E961X
