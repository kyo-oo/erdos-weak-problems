import Arsenal.ErdosTernary2.Basic
import Arsenal.CardinalWorlds
import Arsenal.CardinalWorldsV2

set_option maxRecDepth 65536
set_option maxHeartbeats 4000000

/-! # Erdos961Exclusion3 — THE EXCLUSION LAYER 3 (Kernel 66)

The third exclusion layer of the Erdős #961 (Størmer/Pell smooth-run)
machine, on top of the green K46 descent engine and K58 tower-ordering
layer. This kernel is SELF-CONTAINED (the house CI compiles each file
standalone via `lake env lean`; the import law admits ONLY the Arsenal
set), so the K46 Pell machinery is re-carried VERBATIM in the `E961X3`
namespace. Content:

1. **THE BASE MACHINE, RE-CARRIED (§0)**: the Pell tower `Pell` (the
   n-fold Brahmagupta power of the fundamental (X₁, Y₁)), the
   Brahmagupta composition law `pell_compose` ((X₁·Xk + a·Y₁·Yk)² =
   a·(X₁·Yk + Y₁·Xk)² + 1), the solvability law `pell_sol` (every
   positive tower member solves X² = a·Y² + 1), and the explicit
   telescope `pell_compose_full` (the board conjunct form).
2. **THE TOWER-ORDERING ENGINE (§1-§2)**: the one-step definitional
   unfolds `pell_step_X`/`pell_step_Y`, the X-positivity, the linear
   index bound k+1 ≤ X_k, the STRICT X-monotonicity, and the LINEAR
   FUNDAMENTAL BOUND X₁·k ≤ X_k (the K58 §14 layer, restated).
3. **THE POWER-REPRESENTATION AND THE GROWTH LAWS (§3)**: the power
   law `pell_tower_pow_add` (Pell(n+m) = Pell(n) ∘ Pell(m) — the tower
   IS the power map), **THE SUPER-MULTIPLICATIVE GROWTH LAW**
   `pell_tower_X_supermul` (X_n·X_m ≤ X_{n+m}, NEW beyond K58 — every
   tower step composes multiplicatively), and **THE EXPONENTIAL GROWTH
   LAW** `pell_tower_X_ge_pow` (X₁^n ≤ X_n — the fundamental-based
   exponential separation, the multiplicative strengthening of K58's
   linear X₁·n ≤ X_n).
4. **THE GAP CASCADE (§4)**: `pell_tower_gap_mono` — consecutive tower
   gaps STRICTLY increase (X_{n+2} − X_{n+1} > X_{n+1} − X_n), the K58
   gap-monotonicity engine restated for this kernel's families.
5. **THE FIVE NEW PRIME FAMILY ROWS (§5)**: the Pell families
   a ∈ {13, 19, 23, 31, 37} — beyond K58's a = 29 — each delivered as
   one complete row `pell{a}_row`: the fundamental witness (13→(649,180),
   19→(170,39), 23→(24,5), 31→(1520,273), 37→(73,12); decide-certified),
   the exact second tower member (decide), (for the two smallest
   families 23 and 37: the exact THIRD tower member + the numeric gap
   cascade receipt), the Brahmagupta composition row (pell_compose
   instance), the solvability law, the exponential growth corollary,
   and the gap-cascade instance.
6. **THE SCALE RECEIPT (§6)** and **THE MASTER BOARD (§7)**
   `e961x3_exclusion3_board` (11 conjuncts, full statements).

Honest scope: this layer certifies the WITNESS/TOWER/GROWTH side of the
five new families — the fundamentals are certified as SOLUTIONS, and
the growth/gap/ordering laws are fully unconditional (hypothesis
2 ≤ X₁ only). MINIMALITY of the five new fundamentals (no smaller
positive solution) is NOT asserted here; it is the next exclusion layer
(the K58 §9-§10 structural route for a = 29 is the template). All
`decide` uses are on CLOSED numerals (no bounded-∀ sweeps, no
∀ k < N with N > 501 anywhere). Numeric pre-verification: every numeral
in this file (fundamentals, tower members 2 and 3, compose rows, gap
values, power scales) was machine-verified in the kernel session.

Discipline: K46/K58-green patterns only — core Nat lemmas in the exact
goal spellings via `Nat.mul_le_mul_left/right`, omega over
ring-normalized product atoms, `ring` for the bilinear identities,
one-step definitional `show`-unfolds of the Pell recursion, decide on
closed numerals only. No sorry. No axiom. No native_decide. No Mathlib
import (the Arsenal set only). -/
namespace E961X3

/-! ## §0 The base machine: the Pell tower and the Brahmagupta
composition law (re-carried VERBATIM from the green Kernel 46 engine). -/

/-- The n-fold power of the fundamental solution (X₁, Y₁) under the
Brahmagupta composition. -/
def Pell (a X1 Y1 : Nat) : Nat → Nat × Nat
  | 0 => (1, 0)
  | n + 1 => (X1 * (Pell a X1 Y1 n).1 + a * Y1 * (Pell a X1 Y1 n).2,
              X1 * (Pell a X1 Y1 n).2 + Y1 * (Pell a X1 Y1 n).1)

/-- THE BRAHMAGUPTA COMPOSITION LAW: the composition of two Pell
solutions is a solution — (X₁·Xk + a·Y₁·Yk)² = a·(X₁·Yk + Y₁·Xk)² + 1.
The Lagrange identity underneath: u² − a·v² = (X₁² − a·Y₁²)(Xk² − a·Yk²). -/
theorem pell_compose {a X1 Y1 Xk Yk : Nat}
    (hf : X1 * X1 = a * Y1 * Y1 + 1) (hik : Xk * Xk = a * Yk * Yk + 1) :
    (X1 * Xk + a * Y1 * Yk) * (X1 * Xk + a * Y1 * Yk)
      = a * (X1 * Yk + Y1 * Xk) * (X1 * Yk + Y1 * Xk) + 1 := by
  have key : (X1 * Xk + a * Y1 * Yk) * (X1 * Xk + a * Y1 * Yk)
      + a * (X1 * X1) * (Yk * Yk) + a * (Y1 * Y1) * (Xk * Xk)
      = a * (X1 * Yk + Y1 * Xk) * (X1 * Yk + Y1 * Xk)
        + (X1 * X1) * (Xk * Xk) + a * a * (Y1 * Y1) * (Yk * Yk) := by
    ring
  have hP : (X1 * X1) * (Xk * Xk)
      = a * a * (Y1 * Y1) * (Yk * Yk) + a * (Y1 * Y1) + a * (Yk * Yk) + 1 := by
    rw [hf, hik]
    ring
  have mA : a * (X1 * X1) * (Yk * Yk)
      = a * a * (Y1 * Y1) * (Yk * Yk) + a * (Yk * Yk) := by
    rw [hf]
    ring
  have mB : a * (Y1 * Y1) * (Xk * Xk)
      = a * a * (Y1 * Y1) * (Yk * Yk) + a * (Y1 * Y1) := by
    rw [hik]
    ring
  omega

/-- Every positive Pell power is a solution: X_n² = a·Y_n² + 1. -/
theorem pell_sol (a X1 Y1 : Nat)
    (hf : X1 * X1 = a * Y1 * Y1 + 1) (n : Nat) :
    (Pell a X1 Y1 (n+1)).1 * (Pell a X1 Y1 (n+1)).1
      = a * (Pell a X1 Y1 (n+1)).2 * (Pell a X1 Y1 (n+1)).2 + 1 := by
  induction n with
  | zero =>
      show (X1 * 1 + a * Y1 * 0) * (X1 * 1 + a * Y1 * 0)
          = a * (X1 * 0 + Y1 * 1) * (X1 * 0 + Y1 * 1) + 1
      simp only [Nat.mul_one, Nat.mul_zero, Nat.add_zero, Nat.zero_add]
      exact hf
  | succ k ih =>
      show (X1 * (Pell a X1 Y1 (k+1)).1 + a * Y1 * (Pell a X1 Y1 (k+1)).2)
            * (X1 * (Pell a X1 Y1 (k+1)).1 + a * Y1 * (Pell a X1 Y1 (k+1)).2)
          = a * (X1 * (Pell a X1 Y1 (k+1)).2 + Y1 * (Pell a X1 Y1 (k+1)).1)
              * (X1 * (Pell a X1 Y1 (k+1)).2 + Y1 * (Pell a X1 Y1 (k+1)).1) + 1
      exact pell_compose hf ih

/-- THE BRAHMAGUPTA COMPOSITION LAW, explicit-telescope form (the board
conjunct of this layer: any two solutions of X² = a·Y² + 1 compose to a
solution — the closure law under which the tower enumerates). -/
theorem pell_compose_full : ∀ (a X1 Y1 Xk Yk : Nat),
    X1 * X1 = a * Y1 * Y1 + 1 → Xk * Xk = a * Yk * Yk + 1 →
    (X1 * Xk + a * Y1 * Yk) * (X1 * Xk + a * Y1 * Yk)
      = a * (X1 * Yk + Y1 * Xk) * (X1 * Yk + Y1 * Xk) + 1 := by
  intro a X1 Y1 Xk Yk hf hik
  exact pell_compose hf hik

/-! ## §1 The tower-ordering engine (the K58 §14 layer, restated). -/

/-- THE TOWER STEP UNFOLD (X-column): the recursion IS the Brahmagupta
composition with the fundamental (definitional rfl on the equation
compiler's succ-pattern). -/
theorem pell_step_X (a X1 Y1 k : Nat) : (Pell a X1 Y1 (k + 1)).1
    = X1 * (Pell a X1 Y1 k).1 + a * Y1 * (Pell a X1 Y1 k).2 :=
  rfl

/-- THE TOWER STEP UNFOLD (Y-column). -/
theorem pell_step_Y (a X1 Y1 k : Nat) : (Pell a X1 Y1 (k + 1)).2
    = X1 * (Pell a X1 Y1 k).2 + Y1 * (Pell a X1 Y1 k).1 :=
  rfl

/-- THE TOWER X-POSITIVITY: every tower member's X is at least 1. -/
theorem pell_tower_X_pos : ∀ (a X1 Y1 k : Nat), 1 ≤ X1 →
    1 ≤ (Pell a X1 Y1 k).1 := by
  intro a X1 Y1 k hX1
  induction k with
  | zero =>
      show 1 ≤ 1
      omega
  | succ j ih =>
      show 1 ≤ X1 * (Pell a X1 Y1 j).1
          + a * Y1 * (Pell a X1 Y1 j).2
      have h1 : 1 * 1 ≤ X1 * (Pell a X1 Y1 j).1 :=
        Nat.mul_le_mul hX1 ih
      omega

/-- THE LINEAR INDEX BOUND: every tower member's X exceeds its index. -/
theorem pell_tower_X_ge_succ : ∀ (a X1 Y1 k : Nat), 2 ≤ X1 →
    k + 1 ≤ (Pell a X1 Y1 k).1 := by
  intro a X1 Y1 k hX1
  induction k with
  | zero =>
      show 0 + 1 ≤ 1
      omega
  | succ j ih =>
      show j + 1 + 1 ≤ X1 * (Pell a X1 Y1 j).1
          + a * Y1 * (Pell a X1 Y1 j).2
      have h2 : 2 * (Pell a X1 Y1 j).1
          ≤ X1 * (Pell a X1 Y1 j).1 :=
        Nat.mul_le_mul_right _ hX1
      omega

/-- THE STRICT X-MONOTONICITY of the tower: X_k < X_{k+1} for every k. -/
theorem pell_tower_X_strict_mono : ∀ (a X1 Y1 k : Nat), 2 ≤ X1 →
    (Pell a X1 Y1 k).1 < (Pell a X1 Y1 (k + 1)).1 := by
  intro a X1 Y1 k hX1
  induction k with
  | zero =>
      show 1 < X1 * 1 + a * Y1 * 0
      omega
  | succ j ih =>
      show (Pell a X1 Y1 (j + 1)).1
          < X1 * (Pell a X1 Y1 (j + 1)).1
              + a * Y1 * (Pell a X1 Y1 (j + 1)).2
      have h2 : 2 * (Pell a X1 Y1 (j + 1)).1
          ≤ X1 * (Pell a X1 Y1 (j + 1)).1 :=
        Nat.mul_le_mul_right _ hX1
      omega

/-- THE LINEAR FUNDAMENTAL BOUND: X₁·k ≤ X_k for every k. -/
theorem pell_tower_X_ge_X1_mul : ∀ (a X1 Y1 n : Nat), 2 ≤ X1 →
    X1 * n ≤ (Pell a X1 Y1 n).1 := by
  intro a X1 Y1 n hX1
  induction n with
  | zero =>
      show X1 * 0 ≤ 1
      omega
  | succ k ih =>
      show X1 * (k + 1) ≤ X1 * (Pell a X1 Y1 k).1
          + a * Y1 * (Pell a X1 Y1 k).2
      have hksucc : k + 1 ≤ (Pell a X1 Y1 k).1 :=
        pell_tower_X_ge_succ a X1 Y1 k hX1
      have hmul : X1 * (k + 1) ≤ X1 * (Pell a X1 Y1 k).1 :=
        Nat.mul_le_mul_left _ hksucc
      omega

/-! ## §2 The power representation: the tower IS the power map. -/

/-- THE POWER-REPRESENTATION LAW: the Brahmagupta composition of tower
members n and m is the tower member n + m — Pell(n+m) = Pell(n) ∘
Pell(m). Induction on m through the step unfolds; the step case is
the associativity of the bilinear composition (one `ring` per column). -/
theorem pell_tower_pow_add : ∀ (a X1 Y1 n m : Nat),
    (Pell a X1 Y1 (n + m)).1
      = (Pell a X1 Y1 n).1 * (Pell a X1 Y1 m).1
        + a * (Pell a X1 Y1 n).2 * (Pell a X1 Y1 m).2
    ∧ (Pell a X1 Y1 (n + m)).2
      = (Pell a X1 Y1 n).1 * (Pell a X1 Y1 m).2
        + (Pell a X1 Y1 n).2 * (Pell a X1 Y1 m).1 := by
  intro a X1 Y1 n m
  induction m with
  | zero =>
      rw [Nat.add_zero]
      constructor
      · show (Pell a X1 Y1 n).1
            = (Pell a X1 Y1 n).1 * 1
              + a * (Pell a X1 Y1 n).2 * 0
        simp only [Nat.mul_one, Nat.mul_zero, Nat.add_zero]
      · show (Pell a X1 Y1 n).2
            = (Pell a X1 Y1 n).1 * 0
              + (Pell a X1 Y1 n).2 * 1
        simp only [Nat.mul_one, Nat.mul_zero, Nat.add_zero, Nat.zero_add]
  | succ k ih =>
      obtain ⟨ihX, ihY⟩ := ih
      have hn : n + (k + 1) = (n + k) + 1 := by omega
      rw [hn]
      constructor
      · rw [pell_step_X a X1 Y1 (n + k), ihX, ihY,
          pell_step_X a X1 Y1 k, pell_step_Y a X1 Y1 k]
        ring
      · rw [pell_step_Y a X1 Y1 (n + k), ihX, ihY,
          pell_step_X a X1 Y1 k, pell_step_Y a X1 Y1 k]
        ring

/-! ## §3 THE GROWTH LAWS (the exponential separation, layer 3). -/

/-- THE SUPER-MULTIPLICATIVE GROWTH LAW (NEW beyond K58): the tower
members compose multiplicatively — X_n·X_m ≤ X_{n+m}. From the power
law: X_{n+m} = X_n·X_m + a·Y_n·Y_m, and the a·Y_n·Y_m residue is
nonnegative (omega over the product atoms). The X-column of the tower
is super-multiplicative in the indices: every composition step at least
multiplies the coordinates. -/
theorem pell_tower_X_supermul : ∀ (a X1 Y1 n m : Nat),
    (Pell a X1 Y1 n).1 * (Pell a X1 Y1 m).1 ≤ (Pell a X1 Y1 (n + m)).1 := by
  intro a X1 Y1 n m
  have hsum := (pell_tower_pow_add a X1 Y1 n m).1
  omega

/-- The power recursion in the right-multiplied orientation (rfl). -/
theorem powMul_step (M k : Nat) : M ^ (k + 1) = M ^ k * M := by
  rfl

/-- THE EXPONENTIAL GROWTH LAW (the multiplicative strengthening of
K58's linear X₁·n ≤ X_n): X₁^n ≤ X_n for every n — the tower's X-column
dominates the fundamental's own powers. The succ step goes through the
right-multiplied `powMul_step`, the comm bridge `Nat.mul_comm`, and the
pure `Nat.le_trans` cascade (omega never touches a power). -/
theorem pell_tower_X_ge_pow : ∀ (a X1 Y1 n : Nat), 2 ≤ X1 →
    X1 ^ n ≤ (Pell a X1 Y1 n).1 := by
  intro a X1 Y1 n hX1
  induction n with
  | zero =>
      show X1 ^ 0 ≤ 1
      rw [Nat.pow_zero]
  | succ k ih =>
      show X1 ^ (k + 1) ≤ X1 * (Pell a X1 Y1 k).1
          + a * Y1 * (Pell a X1 Y1 k).2
      rw [powMul_step]
      have h1 : X1 ^ k * X1 ≤ (Pell a X1 Y1 k).1 * X1 :=
        Nat.mul_le_mul_right _ ih
      have h2 : (Pell a X1 Y1 k).1 * X1
          ≤ X1 * (Pell a X1 Y1 k).1 :=
        Nat.le_of_eq (Nat.mul_comm _ _)
      have h3 : X1 * (Pell a X1 Y1 k).1
          ≤ X1 * (Pell a X1 Y1 k).1
            + a * Y1 * (Pell a X1 Y1 k).2 :=
        Nat.le_add_right _ _
      exact Nat.le_trans h1 (Nat.le_trans h2 h3)

/-! ## §4 THE GAP CASCADE (consecutive-gap monotonicity). -/

/-- THE GAP MONOTONICITY: the gap between consecutive tower members is
STRICTLY INCREASING — X_{n+1} − X_n < X_{n+2} − X_{n+1}. Via the
one-step composition law: X_{n+2} = X₁·X_{n+1} + a·Y₁·Y_{n+1} ≥
2·X_{n+1} (X₁ ≥ 2), with the strict monotonicity keeping both
subtractions honest. -/
theorem pell_tower_gap_mono : ∀ (a X1 Y1 n : Nat), 2 ≤ X1 →
    (Pell a X1 Y1 (n + 1)).1 - (Pell a X1 Y1 n).1
      < (Pell a X1 Y1 (n + 1 + 1)).1 - (Pell a X1 Y1 (n + 1)).1 := by
  intro a X1 Y1 n hX1
  have hposn : 1 ≤ (Pell a X1 Y1 n).1 :=
    pell_tower_X_pos a X1 Y1 n (by omega)
  have hmono1 : (Pell a X1 Y1 n).1 < (Pell a X1 Y1 (n + 1)).1 :=
    pell_tower_X_strict_mono a X1 Y1 n hX1
  have hmono2 : (Pell a X1 Y1 (n + 1)).1
      < (Pell a X1 Y1 (n + 1 + 1)).1 :=
    pell_tower_X_strict_mono a X1 Y1 (n + 1) hX1
  have hstep : (Pell a X1 Y1 (n + 1 + 1)).1
      = X1 * (Pell a X1 Y1 (n + 1)).1
          + a * Y1 * (Pell a X1 Y1 (n + 1)).2 := pell_step_X a X1 Y1 (n + 1)
  have hdom : 2 * (Pell a X1 Y1 (n + 1)).1
      ≤ X1 * (Pell a X1 Y1 (n + 1)).1 :=
    Nat.mul_le_mul_right _ hX1
  show (Pell a X1 Y1 (n + 1)).1 - (Pell a X1 Y1 n).1
      < (Pell a X1 Y1 (n + 1 + 1)).1 - (Pell a X1 Y1 (n + 1)).1
  omega

/-! ## §5 THE FIVE NEW PRIME FAMILY ROWS (a ∈ {13, 19, 23, 31, 37}).

Each row is one complete theorem: the decide-certified fundamental
witness, the exact second tower member (the Brahmagupta square of the
fundamental), the composition row (the `pell_compose` instance at the
fundamental pair), the solvability law (every positive tower member of
the family solves the family equation), the exponential growth
corollary (X₁^n ≤ X_n), and the gap-cascade instance. For the two
smallest families (a = 23 and a = 37) the row additionally carries the
exact THIRD tower member and the numeric gap-cascade receipt (the
first three gaps, strictly increasing). All numerals are python-
preverified in this session. -/

/-- THE 13-FAMILY ROW: fundamental (649, 180) — 649² = 13·180² + 1;
member 2 = (842401, 233640). -/
theorem pell13_row :
    649 * 649 = 13 * 180 * 180 + 1
    ∧ ((Pell 13 649 180 2).1 = 842401 ∧ (Pell 13 649 180 2).2 = 233640)
    ∧ (649 * 649 + 13 * 180 * 180) * (649 * 649 + 13 * 180 * 180)
        = 13 * (649 * 180 + 180 * 649) * (649 * 180 + 180 * 649) + 1
    ∧ (∀ n : Nat,
        (Pell 13 649 180 (n + 1)).1 * (Pell 13 649 180 (n + 1)).1
          = 13 * (Pell 13 649 180 (n + 1)).2 * (Pell 13 649 180 (n + 1)).2 + 1)
    ∧ (∀ n : Nat, 649 ^ n ≤ (Pell 13 649 180 n).1)
    ∧ (∀ n : Nat,
        (Pell 13 649 180 (n + 1)).1 - (Pell 13 649 180 n).1
          < (Pell 13 649 180 (n + 1 + 1)).1 - (Pell 13 649 180 (n + 1)).1) := by
  have hf : 649 * 649 = 13 * 180 * 180 + 1 := by decide
  refine ⟨hf, ⟨by decide, by decide⟩,
    pell_compose_full 13 649 180 649 180 hf hf,
    fun n => pell_sol 13 649 180 hf n,
    fun n => pell_tower_X_ge_pow 13 649 180 n (by omega),
    fun n => pell_tower_gap_mono 13 649 180 n (by omega)⟩

/-- THE 19-FAMILY ROW: fundamental (170, 39) — 170² = 19·39² + 1;
member 2 = (57799, 13260). -/
theorem pell19_row :
    170 * 170 = 19 * 39 * 39 + 1
    ∧ ((Pell 19 170 39 2).1 = 57799 ∧ (Pell 19 170 39 2).2 = 13260)
    ∧ (170 * 170 + 19 * 39 * 39) * (170 * 170 + 19 * 39 * 39)
        = 19 * (170 * 39 + 39 * 170) * (170 * 39 + 39 * 170) + 1
    ∧ (∀ n : Nat,
        (Pell 19 170 39 (n + 1)).1 * (Pell 19 170 39 (n + 1)).1
          = 19 * (Pell 19 170 39 (n + 1)).2 * (Pell 19 170 39 (n + 1)).2 + 1)
    ∧ (∀ n : Nat, 170 ^ n ≤ (Pell 19 170 39 n).1)
    ∧ (∀ n : Nat,
        (Pell 19 170 39 (n + 1)).1 - (Pell 19 170 39 n).1
          < (Pell 19 170 39 (n + 1 + 1)).1 - (Pell 19 170 39 (n + 1)).1) := by
  have hf : 170 * 170 = 19 * 39 * 39 + 1 := by decide
  refine ⟨hf, ⟨by decide, by decide⟩,
    pell_compose_full 19 170 39 170 39 hf hf,
    fun n => pell_sol 19 170 39 hf n,
    fun n => pell_tower_X_ge_pow 19 170 39 n (by omega),
    fun n => pell_tower_gap_mono 19 170 39 n (by omega)⟩

/-- THE 23-FAMILY ROW (the smallest new family): fundamental (24, 5) —
24² = 23·5² + 1; member 2 = (1151, 240); member 3 = (55224, 11515);
the numeric gap cascade 23 < 1127 < 54073. -/
theorem pell23_row :
    24 * 24 = 23 * 5 * 5 + 1
    ∧ ((Pell 23 24 5 2).1 = 1151 ∧ (Pell 23 24 5 2).2 = 240)
    ∧ ((Pell 23 24 5 3).1 = 55224 ∧ (Pell 23 24 5 3).2 = 11515)
    ∧ (24 * 24 + 23 * 5 * 5) * (24 * 24 + 23 * 5 * 5)
        = 23 * (24 * 5 + 5 * 24) * (24 * 5 + 5 * 24) + 1
    ∧ (∀ n : Nat,
        (Pell 23 24 5 (n + 1)).1 * (Pell 23 24 5 (n + 1)).1
          = 23 * (Pell 23 24 5 (n + 1)).2 * (Pell 23 24 5 (n + 1)).2 + 1)
    ∧ (∀ n : Nat, 24 ^ n ≤ (Pell 23 24 5 n).1)
    ∧ (∀ n : Nat,
        (Pell 23 24 5 (n + 1)).1 - (Pell 23 24 5 n).1
          < (Pell 23 24 5 (n + 1 + 1)).1 - (Pell 23 24 5 (n + 1)).1)
    ∧ ((Pell 23 24 5 1).1 - (Pell 23 24 5 0).1 = 23
        ∧ (Pell 23 24 5 2).1 - (Pell 23 24 5 1).1 = 1127
        ∧ (Pell 23 24 5 3).1 - (Pell 23 24 5 2).1 = 54073) := by
  have hf : 24 * 24 = 23 * 5 * 5 + 1 := by decide
  refine ⟨hf, ⟨by decide, by decide⟩, ⟨by decide, by decide⟩,
    pell_compose_full 23 24 5 24 5 hf hf,
    fun n => pell_sol 23 24 5 hf n,
    fun n => pell_tower_X_ge_pow 23 24 5 n (by omega),
    fun n => pell_tower_gap_mono 23 24 5 n (by omega),
    ⟨by decide, by decide, by decide⟩⟩

/-- THE 31-FAMILY ROW: fundamental (1520, 273) — 1520² = 31·273² + 1;
member 2 = (4620799, 829920). -/
theorem pell31_row :
    1520 * 1520 = 31 * 273 * 273 + 1
    ∧ ((Pell 31 1520 273 2).1 = 4620799 ∧ (Pell 31 1520 273 2).2 = 829920)
    ∧ (1520 * 1520 + 31 * 273 * 273) * (1520 * 1520 + 31 * 273 * 273)
        = 31 * (1520 * 273 + 273 * 1520) * (1520 * 273 + 273 * 1520) + 1
    ∧ (∀ n : Nat,
        (Pell 31 1520 273 (n + 1)).1 * (Pell 31 1520 273 (n + 1)).1
          = 31 * (Pell 31 1520 273 (n + 1)).2 * (Pell 31 1520 273 (n + 1)).2 + 1)
    ∧ (∀ n : Nat, 1520 ^ n ≤ (Pell 31 1520 273 n).1)
    ∧ (∀ n : Nat,
        (Pell 31 1520 273 (n + 1)).1 - (Pell 31 1520 273 n).1
          < (Pell 31 1520 273 (n + 1 + 1)).1 - (Pell 31 1520 273 (n + 1)).1) := by
  have hf : 1520 * 1520 = 31 * 273 * 273 + 1 := by decide
  refine ⟨hf, ⟨by decide, by decide⟩,
    pell_compose_full 31 1520 273 1520 273 hf hf,
    fun n => pell_sol 31 1520 273 hf n,
    fun n => pell_tower_X_ge_pow 31 1520 273 n (by omega),
    fun n => pell_tower_gap_mono 31 1520 273 n (by omega)⟩

/-- THE 37-FAMILY ROW: fundamental (73, 12) — 73² = 37·12² + 1; member
2 = (10657, 1752); member 3 = (1555849, 255780); the numeric gap
cascade 72 < 10584 < 1545192. -/
theorem pell37_row :
    73 * 73 = 37 * 12 * 12 + 1
    ∧ ((Pell 37 73 12 2).1 = 10657 ∧ (Pell 37 73 12 2).2 = 1752)
    ∧ ((Pell 37 73 12 3).1 = 1555849 ∧ (Pell 37 73 12 3).2 = 255780)
    ∧ (73 * 73 + 37 * 12 * 12) * (73 * 73 + 37 * 12 * 12)
        = 37 * (73 * 12 + 12 * 73) * (73 * 12 + 12 * 73) + 1
    ∧ (∀ n : Nat,
        (Pell 37 73 12 (n + 1)).1 * (Pell 37 73 12 (n + 1)).1
          = 37 * (Pell 37 73 12 (n + 1)).2 * (Pell 37 73 12 (n + 1)).2 + 1)
    ∧ (∀ n : Nat, 73 ^ n ≤ (Pell 37 73 12 n).1)
    ∧ (∀ n : Nat,
        (Pell 37 73 12 (n + 1)).1 - (Pell 37 73 12 n).1
          < (Pell 37 73 12 (n + 1 + 1)).1 - (Pell 37 73 12 (n + 1)).1)
    ∧ ((Pell 37 73 12 1).1 - (Pell 37 73 12 0).1 = 72
        ∧ (Pell 37 73 12 2).1 - (Pell 37 73 12 1).1 = 10584
        ∧ (Pell 37 73 12 3).1 - (Pell 37 73 12 2).1 = 1545192) := by
  have hf : 73 * 73 = 37 * 12 * 12 + 1 := by decide
  refine ⟨hf, ⟨by decide, by decide⟩, ⟨by decide, by decide⟩,
    pell_compose_full 37 73 12 73 12 hf hf,
    fun n => pell_sol 37 73 12 hf n,
    fun n => pell_tower_X_ge_pow 37 73 12 n (by omega),
    fun n => pell_tower_gap_mono 37 73 12 n (by omega),
    ⟨by decide, by decide, by decide⟩⟩

/-! ## §6 THE SCALE RECEIPT. -/

/-- THE FAMILY POWER-SCALE RECEIPT: each new fundamental's X₁ sits
above a certified power of 2 (2^4 ≤ 24, 2^7 ≤ 170, 2^9 ≤ 649,
2^10 ≤ 1520, 2^6 ≤ 73 — the exponential growth law therefore beats
the 2^n scale on every new family). -/
theorem e961x3_family_scale_receipt :
    2^4 ≤ 24 ∧ 2^7 ≤ 170 ∧ 2^9 ≤ 649 ∧ 2^10 ≤ 1520 ∧ 2^6 ≤ 73 := by
  refine ⟨by decide, by decide, by decide, by decide, by decide⟩

/-! ## §7 THE MASTER BOARD (the exclusion-layer-3 receipt). -/

/-- THE EXCLUSION-3 MASTER BOARD (11 conjuncts, full statements, flat
anonymous constructor): the Brahmagupta composition law + THE
SUPER-MULTIPLICATIVE GROWTH LAW + THE EXPONENTIAL GROWTH LAW + the
linear fundamental bound + THE GAP CASCADE + the five family rows +
the scale receipt. -/
theorem e961x3_exclusion3_board :
    (∀ (a X1 Y1 Xk Yk : Nat),
        X1 * X1 = a * Y1 * Y1 + 1 → Xk * Xk = a * Yk * Yk + 1 →
        (X1 * Xk + a * Y1 * Yk) * (X1 * Xk + a * Y1 * Yk)
          = a * (X1 * Yk + Y1 * Xk) * (X1 * Yk + Y1 * Xk) + 1)
    ∧ (∀ (a X1 Y1 n m : Nat),
        (Pell a X1 Y1 n).1 * (Pell a X1 Y1 m).1 ≤ (Pell a X1 Y1 (n + m)).1)
    ∧ (∀ (a X1 Y1 n : Nat), 2 ≤ X1 → X1 ^ n ≤ (Pell a X1 Y1 n).1)
    ∧ (∀ (a X1 Y1 n : Nat), 2 ≤ X1 → X1 * n ≤ (Pell a X1 Y1 n).1)
    ∧ (∀ (a X1 Y1 n : Nat), 2 ≤ X1 →
        (Pell a X1 Y1 (n + 1)).1 - (Pell a X1 Y1 n).1
          < (Pell a X1 Y1 (n + 1 + 1)).1 - (Pell a X1 Y1 (n + 1)).1)
    ∧ (649 * 649 = 13 * 180 * 180 + 1
        ∧ ((Pell 13 649 180 2).1 = 842401 ∧ (Pell 13 649 180 2).2 = 233640)
        ∧ (649 * 649 + 13 * 180 * 180) * (649 * 649 + 13 * 180 * 180)
            = 13 * (649 * 180 + 180 * 649) * (649 * 180 + 180 * 649) + 1
        ∧ (∀ n : Nat,
            (Pell 13 649 180 (n + 1)).1 * (Pell 13 649 180 (n + 1)).1
              = 13 * (Pell 13 649 180 (n + 1)).2 * (Pell 13 649 180 (n + 1)).2 + 1)
        ∧ (∀ n : Nat, 649 ^ n ≤ (Pell 13 649 180 n).1)
        ∧ (∀ n : Nat,
            (Pell 13 649 180 (n + 1)).1 - (Pell 13 649 180 n).1
              < (Pell 13 649 180 (n + 1 + 1)).1 - (Pell 13 649 180 (n + 1)).1))
    ∧ (170 * 170 = 19 * 39 * 39 + 1
        ∧ ((Pell 19 170 39 2).1 = 57799 ∧ (Pell 19 170 39 2).2 = 13260)
        ∧ (170 * 170 + 19 * 39 * 39) * (170 * 170 + 19 * 39 * 39)
            = 19 * (170 * 39 + 39 * 170) * (170 * 39 + 39 * 170) + 1
        ∧ (∀ n : Nat,
            (Pell 19 170 39 (n + 1)).1 * (Pell 19 170 39 (n + 1)).1
              = 19 * (Pell 19 170 39 (n + 1)).2 * (Pell 19 170 39 (n + 1)).2 + 1)
        ∧ (∀ n : Nat, 170 ^ n ≤ (Pell 19 170 39 n).1)
        ∧ (∀ n : Nat,
            (Pell 19 170 39 (n + 1)).1 - (Pell 19 170 39 n).1
              < (Pell 19 170 39 (n + 1 + 1)).1 - (Pell 19 170 39 (n + 1)).1))
    ∧ (24 * 24 = 23 * 5 * 5 + 1
        ∧ ((Pell 23 24 5 2).1 = 1151 ∧ (Pell 23 24 5 2).2 = 240)
        ∧ ((Pell 23 24 5 3).1 = 55224 ∧ (Pell 23 24 5 3).2 = 11515)
        ∧ (24 * 24 + 23 * 5 * 5) * (24 * 24 + 23 * 5 * 5)
            = 23 * (24 * 5 + 5 * 24) * (24 * 5 + 5 * 24) + 1
        ∧ (∀ n : Nat,
            (Pell 23 24 5 (n + 1)).1 * (Pell 23 24 5 (n + 1)).1
              = 23 * (Pell 23 24 5 (n + 1)).2 * (Pell 23 24 5 (n + 1)).2 + 1)
        ∧ (∀ n : Nat, 24 ^ n ≤ (Pell 23 24 5 n).1)
        ∧ (∀ n : Nat,
            (Pell 23 24 5 (n + 1)).1 - (Pell 23 24 5 n).1
              < (Pell 23 24 5 (n + 1 + 1)).1 - (Pell 23 24 5 (n + 1)).1)
        ∧ ((Pell 23 24 5 1).1 - (Pell 23 24 5 0).1 = 23
            ∧ (Pell 23 24 5 2).1 - (Pell 23 24 5 1).1 = 1127
            ∧ (Pell 23 24 5 3).1 - (Pell 23 24 5 2).1 = 54073))
    ∧ (1520 * 1520 = 31 * 273 * 273 + 1
        ∧ ((Pell 31 1520 273 2).1 = 4620799 ∧ (Pell 31 1520 273 2).2 = 829920)
        ∧ (1520 * 1520 + 31 * 273 * 273) * (1520 * 1520 + 31 * 273 * 273)
            = 31 * (1520 * 273 + 273 * 1520) * (1520 * 273 + 273 * 1520) + 1
        ∧ (∀ n : Nat,
            (Pell 31 1520 273 (n + 1)).1 * (Pell 31 1520 273 (n + 1)).1
              = 31 * (Pell 31 1520 273 (n + 1)).2 * (Pell 31 1520 273 (n + 1)).2 + 1)
        ∧ (∀ n : Nat, 1520 ^ n ≤ (Pell 31 1520 273 n).1)
        ∧ (∀ n : Nat,
            (Pell 31 1520 273 (n + 1)).1 - (Pell 31 1520 273 n).1
              < (Pell 31 1520 273 (n + 1 + 1)).1 - (Pell 31 1520 273 (n + 1)).1))
    ∧ (73 * 73 = 37 * 12 * 12 + 1
        ∧ ((Pell 37 73 12 2).1 = 10657 ∧ (Pell 37 73 12 2).2 = 1752)
        ∧ ((Pell 37 73 12 3).1 = 1555849 ∧ (Pell 37 73 12 3).2 = 255780)
        ∧ (73 * 73 + 37 * 12 * 12) * (73 * 73 + 37 * 12 * 12)
            = 37 * (73 * 12 + 12 * 73) * (73 * 12 + 12 * 73) + 1
        ∧ (∀ n : Nat,
            (Pell 37 73 12 (n + 1)).1 * (Pell 37 73 12 (n + 1)).1
              = 37 * (Pell 37 73 12 (n + 1)).2 * (Pell 37 73 12 (n + 1)).2 + 1)
        ∧ (∀ n : Nat, 73 ^ n ≤ (Pell 37 73 12 n).1)
        ∧ (∀ n : Nat,
            (Pell 37 73 12 (n + 1)).1 - (Pell 37 73 12 n).1
              < (Pell 37 73 12 (n + 1 + 1)).1 - (Pell 37 73 12 (n + 1)).1)
        ∧ ((Pell 37 73 12 1).1 - (Pell 37 73 12 0).1 = 72
            ∧ (Pell 37 73 12 2).1 - (Pell 37 73 12 1).1 = 10584
            ∧ (Pell 37 73 12 3).1 - (Pell 37 73 12 2).1 = 1545192))
    ∧ (2^4 ≤ 24 ∧ 2^7 ≤ 170 ∧ 2^9 ≤ 649 ∧ 2^10 ≤ 1520 ∧ 2^6 ≤ 73) :=
  ⟨pell_compose_full, pell_tower_X_supermul, pell_tower_X_ge_pow,
    pell_tower_X_ge_X1_mul, pell_tower_gap_mono, pell13_row, pell19_row,
    pell23_row, pell31_row, pell37_row, e961x3_family_scale_receipt⟩

#print axioms E961X3.pell_compose
#print axioms E961X3.pell_sol
#print axioms E961X3.pell_compose_full
#print axioms E961X3.pell_step_X
#print axioms E961X3.pell_step_Y
#print axioms E961X3.pell_tower_X_pos
#print axioms E961X3.pell_tower_X_ge_succ
#print axioms E961X3.pell_tower_X_strict_mono
#print axioms E961X3.pell_tower_X_ge_X1_mul
#print axioms E961X3.pell_tower_pow_add
#print axioms E961X3.pell_tower_X_supermul
#print axioms E961X3.powMul_step
#print axioms E961X3.pell_tower_X_ge_pow
#print axioms E961X3.pell_tower_gap_mono
#print axioms E961X3.pell13_row
#print axioms E961X3.pell19_row
#print axioms E961X3.pell23_row
#print axioms E961X3.pell31_row
#print axioms E961X3.pell37_row
#print axioms E961X3.e961x3_family_scale_receipt
#print axioms E961X3.e961x3_exclusion3_board

#eval "E961X3_EXCLUSION3_GREEN"
end E961X3
