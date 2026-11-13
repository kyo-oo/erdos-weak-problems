import Erdos961Census_Base
import Arsenal.ErdosTernary2.Basic
import Arsenal.CardinalWorlds
import Arsenal.CardinalWorldsV2

set_option maxRecDepth 65536
set_option maxHeartbeats 4000000

/-! # Erdos961Exclusion2 — THE EXCLUSION LAYER 2 (Kernel 58, K58)

The next exclusion layers beyond green Kernel 48 (STATUS_EXCLUSION.md
item 10 — the menu):

1. **GAP-CERTIFIED DESCENT on the 29-tower** (§0-§4): the strict Y-descent
   `descent_w2_lt` (the conjugate's second coordinate is STRICTLY below Y
   — the difference-of-squares identity w2·(X₁·Y + X·Y₁) + Y₁² = Y², new
   beyond K46/K48), the composition identity `descent_compose` (conjugate
   ∘ fundamental = original), and THE DESCENT-TERMINATION / STRUCTURE
   THEOREM `pell_structure` (strong induction on Y: relative to a minimal
   fundamental, EVERY positive solution is a tower member — the descent
   terminates at the fundamental). The a = 29 instances: the fully
   UNCONDITIONAL descent step `pell29_descent_step` (every solution beyond
   the fundamental descends to a strictly-smaller positive solution), the
   conditional structure law `pell29_structure`, and THE GAP LAW
   `pell29_gap` (solutions beyond the fundamental are ≥ the second tower
   member 192119201 — the descent excludes solutions strictly between the
   certified tower members 9801 and 192119201).
2. **S-UNIT CENSUS CLOSURE** (§5): the 40-pair Størmer witness census
   `e961x2_smooth11_dict` (restated from K47's `e961c_smooth11_dict` — the
   house import law admits only `Erdos961Census_Base` + the Arsenal set,
   so the table is re-carried with a local `Smooth11` of the identical
   shape): every certified value n has n and n+1 both 11-smooth, by
   explicit exponent vector.
3. **SMOOTH-RUN TERMINATION** (§6): the certified-frontier run
   enumeration `e961x2_runs11` (the 12-run (1,…,12) + the five 3-runs),
   the nineteen 2-runs `e961x2_runs11_two` (the 2-run layer of the
   certified census), the run-decomposition coverage
   `e961x2_census_run_cover` (the runs cover all 40 census values), and
   the census-terminal Pell bridge `e961x2_census_pell29_terminal` (the
   largest certified pair (9800, 9801): both 11-smooth, and the upper
   element 9801 is exactly the X of the 29-Pell fundamental (9801, 1820)).
4. **THE MASTER BOARD** `e961x2_exclusion2_board` (11 conjuncts, flat
   anonymous constructor, full statements).
5. **THE 70-13 CONJUGATE LAYER** (§8): the −1-fundamental (70, 13)
   (`pell29_neg_fundamental`: 70² + 1 = 29·13²), the conjugate round-trip
   at (9801, 1820) (`pell29_conj_fundamental`: (377·1820 − 70·9801,
   13·9801 − 70·1820) = (70, 13)), and the recomposition
   (`pell29_recompose_fundamental`: (70,13)² = (9801, 1820)) — all
   decide-certified (the §12 numeric pre-verification).
6. **THE MINIMALITY LAYER — HMIN INSIDE LEAN** (§9-§10): the two 12-row
   decide sweeps (`no29plusX`/`no29negX` structural Bool walkers +
   soundness inductions + the closed chunk theorems `no29plus12_dec`/
   `no29neg12_dec` — the E677/E850 chunk architecture), and THE
   STRUCTURAL MINIMALITY THEOREM `pell29_minimal`: every positive
   29-solution has Y ≥ 1820. The 1819-row brute sweep is above the decide
   cap, so the proof is the TOWER-GAP route: for Y ≥ 13 the conjugate
   v = (377·Y − 70·X, 13·X − 70·Y) is a positive −1-solution whose
   second coordinate hits the WALL vY ≤ 13 (vY·(13X + 70Y) = Y² + 169
   against Y ≤ 1819); vY ≤ 12 contradicts the m2 sweep; vY = 13 forces
   vX = 70 and the recomposition forces (X, Y) = (9801, 1820). The two
   K48-conditional laws become UNCONDITIONAL:
   `pell29_structure_min` (every positive solution is a tower member)
   and `pell29_gap_min` (X = 9801 ∨ 192119201 ≤ X) — the descent machine
   of Kernel 46 now fed a Lean-certified minimality.
7. **THE POWER-REP LAYER** (§11): the tower IS the power map —
   `pell_tower_pow_add` (Pell(n+m) = Pell(n) ∘ Pell(m), the
   Brahmagupta associativity by induction), `pell_tower_two_square`
   (member 2 = (X₁² + a·Y₁², 2·X₁·Y₁)), `pell_tower_two_cheb` (X₂ + 1 =
   2·X₁², the Chebyshev double-angle), `pell29_double_angle` (the
   doubling on every even index), the Størmer factorization law
   `pell_factor_law` ((X−1)(X+1) = a·Y²), its 29 instances
   `pell29_factor`/`pell29_factor_law`/`pell29_factor_dict` (9800 =
   2³·5²·7², 9802 = 2·13²·29, 1820 = 2²·5·7·13).
8. **THE GROWTH-LAW STRENGTHENING** (§12): `pell_tower_X_ge_pow`
   (X₁^n ≤ X_n — the fundamental-based exponential separation, strictly
   stronger than K48's 2^n ≤ X_{n+1} at a = 29 where X₁ = 9801 ≥ 2^13),
   `pell_tower_step_mul`, `pell29_exp_scale`, and THE STRENGTHENED GAP
   `pell29_gap3_min` (X = 9801 ∨ X = 192119201 ∨ 9801³ = 941480149401 ≤
   X — the three-wall separation applied inside the unconditional
   structure law). Plus **THE MASTER BOARD 2** `e961x2_exclusion2_board2`
   (15 conjuncts).
9. **THE KERNEL-58 TOWER-ORDERING LAYER** (§14-§15): `pell_tower_X_pos`
   (every member's X positive), `pell_tower_X_ge_succ` (k+1 ≤ X_k — the
   linear index bound), `pell_tower_X_strict_mono` (the tower strictly
   increases in X), `pell_tower_X_ge_X1_mul` (THE LINEAR FUNDAMENTAL BOUND
   X₁·k ≤ X_k — the additive companion of §12's exponential X₁^k ≤ X_k),
   `pell_tower_gap_mono` (THE GAP MONOTONICITY: consecutive tower gaps
   strictly increase — via the one-step composition law `pell_step_X`,
   X_{n+2} ≥ X₁·X_{n+1} ≥ 2·X_{n+1}), the 29-instances
   (`pell29_tower_X_strict_mono`, `pell29_tower_X_ge_X1_mul`,
   `pell29_tower_gap_mono`), the gap receipt `pell29_gap_receipt` (gap₀ =
   9800, gap₁ = 192109400 — decide on the §12-certified members), and THE
   BOUNDED MINIMALITY `pell29_min_Y_lower` (0 < Y < 1820 admits NO solution
   with X ≤ 9801 — the bounded-sweep statement delivered through the
   STRUCTURED route §10 `pell29_minimal`; the 1819-row brute sits above the
   decide cap). Plus **THE MASTER BOARD 3** `e961x2_exclusion2_board3`
   (10 conjuncts).

Discipline (K46/K47/K48-green patterns only): core Nat lemmas in the
EXACT goal spellings via `Nat.mul_le_mul_left/right`, sub-to-add
transformations for every truncated subtraction (the K46 obtain-pattern,
with `E961P.descent_pos` supplying the positivity that keeps the `omega`
sub-facts true), omega over ring-normalized product atoms, decide only on
CLOSED numerics, one-step definitional `show`-unfolds of the Pell tower
recursion (the K46/K48 defeq pattern). No sorry. No axiom. No
native_decide. No decide on bounded ∀-statements. -/
namespace E961X2

/-! ## §0 The strong-induction engine (core-only accumulator form). -/

/-- Strong induction on Nat: if P n holds whenever P m holds for every
m < n, then P holds everywhere. The engine that formalizes the TERMINATION
of the Størmer–Pell descent (§2). -/
theorem nat_strong_ind {P : Nat → Prop}
    (H : ∀ n : Nat, (∀ m : Nat, m < n → P m) → P n) : ∀ n : Nat, P n := by
  have key : ∀ n m : Nat, m < n → P m := by
    intro n
    induction n with
    | zero =>
        intro m hm
        exact absurd hm (by omega)
    | succ k ih =>
        intro m hm
        exact H m (fun j hj => ih j (by omega))
  intro n
  exact H n (key n)

/-! ## §1 The strict descent engine (on the green K46 machine). -/

/-- THE STRICT Y-DESCENT: for any Pell solution (X, Y) strictly beyond the
fundamental (X₁, Y₁), the conjugate's second coordinate
w2 = X₁·Y − X·Y₁ is STRICTLY smaller than Y.

Proof — the difference-of-squares identity, entirely in the K46 sub-to-add
pattern: with X₁·Y = X·Y₁ + w2 (K46's descent_XY1_lt keeps the
subtraction truncated-free),

  w2·(X₁·Y + X·Y₁) + Y₁² = Y²

((X₁·Y)² − (X·Y₁)² = (a·Y₁²+1)·Y² − (a·Y²+1)·Y₁², ring-normalized into
product atoms). Since X₁·Y + X·Y₁ ≥ Y + Y₁ (X₁ ≥ 1, X ≥ 1), if w2 ≥ Y
then Y·(Y+Y₁) + Y₁² ≤ w2·(Y+Y₁) + Y₁² ≤ Y² = Y·(Y+Y₁) − Y·Y₁ + Y₁² —
forcing Y·Y₁ ≤ 0 against Y ≥ 1, Y₁ ≥ 1. Contradiction: w2 < Y. -/
theorem descent_w2_lt : ∀ (a X1 Y1 X Y : Nat),
    X1 * X1 = a * Y1 * Y1 + 1 → X * X = a * Y * Y + 1 →
    1 ≤ X1 → 1 ≤ Y1 → X1 < X → X1 * Y - X * Y1 < Y := by
  intro a X1 Y1 X Y hf hX hX1 hY1 hgt
  have hXY1 : X * Y1 < X1 * Y := E961P.descent_XY1_lt hf hX hgt
  have hYY1 : Y1 < Y := E961P.descent_Y1_lt_Y hf hX hgt
  obtain ⟨w2, hH⟩ : ∃ w2, X1 * Y = X * Y1 + w2 :=
    ⟨X1 * Y - X * Y1, by omega⟩
  -- THE SQUARE IDENTITY: w2·(X1·Y + X·Y1) + Y1² = Y²
  have hkey : w2 * (X1 * Y + X * Y1) + Y1 * Y1 = Y * Y := by
    have e1 : w2 * (X1 * Y + X * Y1) + (X * Y1) * (X * Y1)
        = (X1 * Y) * (X1 * Y) := by
      rw [hH]
      ring
    have e2 : (X1 * Y) * (X1 * Y) = (X1 * X1) * (Y * Y) := by ring
    have e3 : (X * Y1) * (X * Y1) = (X * X) * (Y1 * Y1) := by ring
    have e4 : (X1 * X1) * (Y * Y) = a * (Y1 * Y1) * (Y * Y) + Y * Y := by
      rw [hf]
      ring
    have e5 : (X * X) * (Y1 * Y1) = a * (Y * Y) * (Y1 * Y1) + Y1 * Y1 := by
      rw [hX]
      ring
    have e6 : a * (Y1 * Y1) * (Y * Y) = a * (Y * Y) * (Y1 * Y1) := by ring
    omega
  -- the final contradiction: w2 ≥ Y is impossible
  by_contra hcon
  have hw2ge : Y ≤ w2 := by omega
  have hge : Y + Y1 ≤ X1 * Y + X * Y1 := by
    have g1 : 1 * Y ≤ X1 * Y := Nat.mul_le_mul_right Y hX1
    have g2 : 1 * Y1 ≤ X * Y1 := Nat.mul_le_mul_right Y1 (by omega)
    omega
  have h7 : w2 * (Y + Y1) ≤ w2 * (X1 * Y + X * Y1) :=
    Nat.mul_le_mul_left w2 hge
  have h8 : Y * (Y + Y1) ≤ w2 * (Y + Y1) :=
    Nat.mul_le_mul_right (Y + Y1) hw2ge
  have h9 : Y * (Y + Y1) = Y * Y + Y * Y1 := by ring
  -- (the K48-green `1 * 1` spelling: a literal LHS does not unify against
  -- `?m * ?k`, the product spelling does; omega folds 1 * 1 back to 1)
  have h10 : 1 * 1 ≤ Y * Y1 := Nat.mul_le_mul (by omega) (by omega)
  omega

/-- THE COMPOSITION IDENTITY: the conjugate (w1, w2) composed with the
fundamental (X₁, Y₁) returns the original solution —

  X = X₁·w1 + a·Y₁·w2   and   Y = Y₁·w1 + X₁·w2

(with w1 = X₁·X − a·Y·Y₁, w2 = X₁·Y − X·Y₁). Pure algebra from the two
Pell equations, in the K46 sub-to-add pattern (the conjugate is the
Brahmagupta inverse-composition, so recomposing cancels it). -/
theorem descent_compose : ∀ (a X1 Y1 X Y : Nat),
    X1 * X1 = a * Y1 * Y1 + 1 → X * X = a * Y * Y + 1 →
    1 ≤ X1 → 1 ≤ Y1 → X1 < X →
    X = X1 * (X1 * X - a * Y * Y1) + a * Y1 * (X1 * Y - X * Y1)
      ∧ Y = Y1 * (X1 * X - a * Y * Y1) + X1 * (X1 * Y - X * Y1) := by
  intro a X1 Y1 X Y hf hX hX1 hY1 hgt
  have hYY1 : Y1 < Y := E961P.descent_Y1_lt_Y hf hX hgt
  have hpos : 0 < X ∧ 0 < Y ∧ 0 < X1 ∧ 0 < Y1 := by omega
  obtain ⟨hE, hG⟩ := E961P.descent_pos hpos hf hX hgt
  obtain ⟨w1, hF⟩ : ∃ w1, X1 * X = a * Y * Y1 + w1 :=
    ⟨X1 * X - a * Y * Y1, by omega⟩
  obtain ⟨w2, hH⟩ : ∃ w2, X1 * Y = X * Y1 + w2 :=
    ⟨X1 * Y - X * Y1, by omega⟩
  have hw1 : w1 = X1 * X - a * Y * Y1 := by omega
  have hw2 : w2 = X1 * Y - X * Y1 := by omega
  rw [← hw1, ← hw2]
  -- first conjunct: X = X1*w1 + a*Y1*w2
  have r1 : a * (X1 * Y) * Y1 + X1 * w1 = X * (a * (Y1 * Y1)) + X := by
    have p1 : X1 * (a * Y * Y1 + w1) = X1 * (X1 * X) := by rw [← hF]
    have p2 : X1 * (a * Y * Y1 + w1) = a * (X1 * Y) * Y1 + X1 * w1 := by
      ring
    have p3 : X1 * (X1 * X) = (X1 * X1) * X := by ring
    rw [hf] at p3
    have p4 : (a * Y1 * Y1 + 1) * X = X * (a * (Y1 * Y1)) + X := by ring
    omega
  have r2 : a * (X1 * Y) * Y1 = a * (X * Y1) * Y1 + a * Y1 * w2 := by
    rw [hH]
    ring
  have r3 : a * (X * Y1) * Y1 = X * (a * (Y1 * Y1)) := by ring
  -- second conjunct: Y = Y1*w1 + X1*w2
  have s1 : X1 * (X1 * Y) = X1 * (X * Y1 + w2) := by rw [hH]
  have s2 : X1 * (X * Y1 + w2) = X1 * (X * Y1) + X1 * w2 := by ring
  have s3 : X1 * (X * Y1) = (X1 * X) * Y1 := by ring
  have s4 : (X1 * X) * Y1 = (a * Y * Y1 + w1) * Y1 := by rw [← hF]
  have s5 : (a * Y * Y1 + w1) * Y1 = a * (Y1 * Y1) * Y + Y1 * w1 := by ring
  have s6 : X1 * (X1 * Y) = (X1 * X1) * Y := by ring
  rw [hf] at s6
  have s7 : (a * Y1 * Y1 + 1) * Y = a * (Y1 * Y1) * Y + Y := by ring
  omega

/-! ## §2 THE DESCENT-TERMINATION / STRUCTURE THEOREM. -/

/-- THE STRUCTURE THEOREM (the descent terminates at the fundamental):
relative to a minimal fundamental solution (X₁, Y₁) — minimality
delivered as the hypothesis `HMIN` — EVERY positive solution (X, Y) of
X² = a·Y² + 1 is a tower member: ∃ n, (X, Y) = (Pell a X1 Y1 (n+1)).1/.2.

Proof: strong induction on Y (§0). If X ≤ X₁ then X = X₁ and Y = Y₁
(HMIN + the (X+1)² strict-square trick, K46-pattern) — the fundamental
itself, tower member 1. If X₁ < X, the K46 descent fires: the conjugate
(w1, w2) is a positive solution (descent_sol) with w2 < Y (§1) — the
induction hypothesis makes it a tower member, and the composition
identity (§1) recomposes (X, Y) as the NEXT tower member (the Pell
recursion IS the Brahmagupta step with the fundamental). -/
theorem pell_structure (a X1 Y1 : Nat) (ha : 2 ≤ a) (hX1 : 2 ≤ X1)
    (hY1 : 1 ≤ Y1) (hf : X1 * X1 = a * Y1 * Y1 + 1)
    (HMIN : ∀ X Y : Nat, X * X = a * Y * Y + 1 → 1 ≤ Y → Y1 ≤ Y) :
    ∀ Y : Nat, 1 ≤ Y → ∀ X : Nat, X * X = a * Y * Y + 1 →
      ∃ n : Nat, X = (E961P.Pell a X1 Y1 (n + 1)).1
        ∧ Y = (E961P.Pell a X1 Y1 (n + 1)).2 := by
  intro Y
  refine nat_strong_ind (P := fun y => 1 ≤ y → ∀ X : Nat,
      X * X = a * y * y + 1 →
      ∃ n : Nat, X = (E961P.Pell a X1 Y1 (n + 1)).1
        ∧ y = (E961P.Pell a X1 Y1 (n + 1)).2) ?_ Y
  intro y ih hy X hXeq
  rcases Nat.lt_or_ge X1 X with hgt | hle
  · -- THE DESCENT STEP: X₁ < X
    have hYY1 : Y1 < y := E961P.descent_Y1_lt_Y hf hXeq hgt
    have hpos : 0 < X ∧ 0 < y ∧ 0 < X1 ∧ 0 < Y1 := by omega
    obtain ⟨hE, hG⟩ := E961P.descent_pos hpos hf hXeq hgt
    have hsolw : (X1 * X - a * y * Y1) * (X1 * X - a * y * Y1)
        = a * (X1 * y - X * Y1) * (X1 * y - X * Y1) + 1 :=
      E961P.descent_sol ha hf hXeq hpos hgt
    have hw2lt : X1 * y - X * Y1 < y :=
      descent_w2_lt a X1 Y1 X y hf hXeq (by omega) hY1 hgt
    obtain ⟨w1, hF⟩ : ∃ w1, X1 * X = a * y * Y1 + w1 :=
      ⟨X1 * X - a * y * Y1, by omega⟩
    obtain ⟨w2, hH⟩ : ∃ w2, X1 * y = X * Y1 + w2 :=
      ⟨X1 * y - X * Y1, by omega⟩
    have hw1 : w1 = X1 * X - a * y * Y1 := by omega
    have hw2 : w2 = X1 * y - X * Y1 := by omega
    have hsol1 : w1 * w1 = a * w2 * w2 + 1 := by
      rw [hw1, hw2]
      exact hsolw
    -- the conjugate is a strictly-smaller positive solution: apply IH at w2
    -- (all four explicit binders of P w2: the w2< y proof, 1 ≤ w2, X := w1,
    -- and the solution equation hsol1 — X is an EXPLICIT binder)
    obtain ⟨k, hkX, hkY⟩ := ih w2 (by omega) (by omega) w1 hsol1
    -- recompose: (X, y) = fundamental ∗ conjugate = next tower member
    obtain ⟨hcX, hcY⟩ :=
      descent_compose a X1 Y1 X y hf hXeq (by omega) hY1 hgt
    rw [← hw1, ← hw2] at hcX hcY
    refine ⟨k + 1, ?_, ?_⟩
    · show X = X1 * (E961P.Pell a X1 Y1 (k + 1)).1
          + a * Y1 * (E961P.Pell a X1 Y1 (k + 1)).2
      rw [← hkX, ← hkY]
      exact hcX
    · show y = X1 * (E961P.Pell a X1 Y1 (k + 1)).2
          + Y1 * (E961P.Pell a X1 Y1 (k + 1)).1
      rw [← hkY, ← hkX]
      have hcomm : X1 * w2 + Y1 * w1 = Y1 * w1 + X1 * w2 := by ring
      omega
  · -- X ≤ X₁: the fundamental itself
    have hYmin : Y1 ≤ y := HMIN X y hXeq hy
    have hyy : Y1 * Y1 ≤ y * y := Nat.mul_le_mul hYmin hYmin
    have h1 : a * (Y1 * Y1) ≤ a * (y * y) := Nat.mul_le_mul_left a hyy
    have h2 : a * Y1 * Y1 = a * (Y1 * Y1) := by ring
    have h3 : a * y * y = a * (y * y) := by ring
    have hsq : X * X ≤ X1 * X1 := Nat.mul_le_mul hle hle
    have hX1sq : X1 * X1 ≤ X * X := by omega
    have hXX1sq : X * X = X1 * X1 := by omega
    have hEq : a * y * y = a * Y1 * Y1 := by omega
    have hXX1 : X = X1 := by
      by_contra hcon
      have hlt : X < X1 := by omega
      have hs : (X + 1) * (X + 1) ≤ X1 * X1 :=
        Nat.mul_le_mul (by omega) (by omega)
      have he : (X + 1) * (X + 1) = X * X + 2 * X + 1 := by ring
      omega
    have hyY1 : y = Y1 := by
      by_contra hcon
      have hgt : Y1 < y := by omega
      have hs : (Y1 + 1) * (Y1 + 1) ≤ y * y :=
        Nat.mul_le_mul (by omega) (by omega)
      have he : (Y1 + 1) * (Y1 + 1) = Y1 * Y1 + 2 * Y1 + 1 := by ring
      have h4 : a * ((Y1 + 1) * (Y1 + 1)) ≤ a * (y * y) :=
        Nat.mul_le_mul_left a hs
      have h5 : a * ((Y1 + 1) * (Y1 + 1))
          = a * (Y1 * Y1) + a * (2 * Y1 + 1) := by ring
      -- (the K48-green product-LHS spelling: `2 * ?k` unifies against `2 * 1`,
      -- a literal `1` does not; omega folds 2 * 1 back to 2)
      have h6 : 2 * 1 ≤ a * (2 * Y1 + 1) := Nat.mul_le_mul ha (by omega)
      omega
    refine ⟨0, ?_, ?_⟩
    · show X = X1 * 1 + a * Y1 * 0
      rw [hXX1]
      omega
    · show y = X1 * 0 + Y1 * 1
      rw [hyY1]
      omega

/-! ## §3 Tower bounds (the certified-member certification engine). -/

/-- Every positive tower member's X is at least the fundamental's X
(one-step definitional unfolds + K48-style mul bounds). -/
theorem pell_tower_X_ge_X1 : ∀ (a X1 Y1 m : Nat), 2 ≤ X1 →
    X1 ≤ (E961P.Pell a X1 Y1 (m + 1)).1 := by
  intro a X1 Y1 m hX1
  induction m with
  | zero =>
      show X1 ≤ X1 * 1 + a * Y1 * 0
      omega
  | succ k ih =>
      show X1 ≤ X1 * (E961P.Pell a X1 Y1 (k + 1)).1
          + a * Y1 * (E961P.Pell a X1 Y1 (k + 1)).2
      have hpx : 1 ≤ (E961P.Pell a X1 Y1 (k + 1)).1 := by omega
      have h1 : X1 * 1 ≤ X1 * (E961P.Pell a X1 Y1 (k + 1)).1 :=
        Nat.mul_le_mul_left _ hpx
      have h2 : X1 * 1 = X1 := by omega
      omega

/-- Every positive tower member's Y is at least the fundamental's Y. -/
theorem pell_tower_Y_ge_Y1 : ∀ (a X1 Y1 m : Nat), 2 ≤ X1 → 1 ≤ Y1 →
    Y1 ≤ (E961P.Pell a X1 Y1 (m + 1)).2 := by
  intro a X1 Y1 m hX1 hY1
  induction m with
  | zero =>
      show Y1 ≤ X1 * 0 + Y1 * 1
      omega
  | succ k ih =>
      show Y1 ≤ X1 * (E961P.Pell a X1 Y1 (k + 1)).2
          + Y1 * (E961P.Pell a X1 Y1 (k + 1)).1
      have hXk : X1 ≤ (E961P.Pell a X1 Y1 (k + 1)).1 :=
        pell_tower_X_ge_X1 a X1 Y1 k hX1
      have hpx : 1 ≤ (E961P.Pell a X1 Y1 (k + 1)).1 := by omega
      have h1 : Y1 * 1 ≤ Y1 * (E961P.Pell a X1 Y1 (k + 1)).1 :=
        Nat.mul_le_mul_left _ hpx
      have h2 : Y1 * 1 = Y1 := by omega
      omega

/-! ## §4 THE 29-a INSTANTIATION (the famous hard case).

The 29-fundamental identity, the exact tower members, the descent step,
and the two gap laws. NOTE (honest scope): the minimality of (9801, 1820)
— no solution with 0 < Y < 1820 — is certified OUTSIDE Lean by a direct
brute sweep (all 0 < Y < 1820: 29·Y²+1 is never a square, 1819 checks —
re-verified numerically in this kernel session; `stormer961_output.txt`
carries the census engine's own 6874-check minimality sweep over the
S-unit a-parameters); the structure/gap laws therefore take minimality as
an explicit HYPOTHESIS (complete conditional theorems — never fake glue),
while the descent step itself is fully unconditional. -/

/-- The 29-fundamental solution form (decide-certified; restated from
K48 since the house import law does not admit `Erdos961Exclusion`). -/
theorem pell29_fundamental_sol : 9801 * 9801 = 29 * 1820 * 1820 + 1 := by
  decide

/-- Tower member 1, exactly: the fundamental itself (decide-certified). -/
theorem pell29_tower_one : (E961P.Pell 29 9801 1820 1).1 = 9801
    ∧ (E961P.Pell 29 9801 1820 1).2 = 1820 := by
  constructor
  · decide
  · decide

/-- Tower member 2, exactly: (192119201, 35675640) — the Brahmagupta
square of the fundamental (decide-certified). -/
theorem pell29_tower_two : (E961P.Pell 29 9801 1820 2).1 = 192119201
    ∧ (E961P.Pell 29 9801 1820 2).2 = 35675640 := by
  constructor
  · decide
  · decide

/-- THE 29-DESCENT STEP (fully UNCONDITIONAL): every solution of
X² = 29·Y² + 1 strictly beyond the fundamental (9801, 1820) descends —
its K46 conjugate (9801·X − 29·Y·1820, 9801·Y − X·1820) is a strictly
smaller positive solution:
* 1820 < Y and X·1820 < 9801·Y (K46's ordering lemmas),
* the conjugate is strictly positive (K46's descent_pos),
* the conjugate SOLVES the equation (K46's descent_sol),
* the conjugate's second coordinate is STRICTLY below Y (§1) — the
  descent strictly decreases and cannot cycle. -/
theorem pell29_descent_step : ∀ (X Y : Nat),
    X * X = 29 * Y * Y + 1 → 1 ≤ Y → 9801 < X →
    1820 < Y ∧ X * 1820 < 9801 * Y ∧ 0 < 9801 * X - 29 * Y * 1820
      ∧ 0 < 9801 * Y - X * 1820
      ∧ (9801 * X - 29 * Y * 1820) * (9801 * X - 29 * Y * 1820)
        = 29 * (9801 * Y - X * 1820) * (9801 * Y - X * 1820) + 1
      ∧ 9801 * Y - X * 1820 < Y := by
  intro X Y hX hY hgt
  have hf : 9801 * 9801 = 29 * 1820 * 1820 + 1 := pell29_fundamental_sol
  have ha29 : 2 ≤ 29 := by omega
  have hYY1 : 1820 < Y := E961P.descent_Y1_lt_Y hf hX hgt
  have hXY1 : X * 1820 < 9801 * Y := E961P.descent_XY1_lt hf hX hgt
  have hpos : 0 < X ∧ 0 < Y ∧ 0 < 9801 ∧ 0 < 1820 := by omega
  obtain ⟨hE, hG⟩ := E961P.descent_pos hpos hf hX hgt
  have hsol := E961P.descent_sol ha29 hf hX hpos hgt
  have hw2lt : 9801 * Y - X * 1820 < Y :=
    descent_w2_lt 29 9801 1820 X Y hf hX (by omega) (by omega) hgt
  exact ⟨hYY1, hXY1, hE, hG, hsol, hw2lt⟩

/-- THE 29-STRUCTURE LAW (conditional on HMIN): every positive 29-solution
is a tower member over (9801, 1820). -/
theorem pell29_structure
    (HMIN : ∀ X Y : Nat, X * X = 29 * Y * Y + 1 → 1 ≤ Y → 1820 ≤ Y) :
    ∀ X Y : Nat, X * X = 29 * Y * Y + 1 → 1 ≤ Y →
      ∃ n : Nat, X = (E961P.Pell 29 9801 1820 (n + 1)).1
        ∧ Y = (E961P.Pell 29 9801 1820 (n + 1)).2 := by
  intro X Y hX hY
  exact pell_structure 29 9801 1820 (by omega) (by omega) (by omega)
    pell29_fundamental_sol HMIN Y hY X hX

/-- THE 29-GAP LAW (conditional on HMIN): every positive solution is
either the fundamental itself (X = 9801) or at least the SECOND TOWER
MEMBER (X ≥ 192119201 = 9801² + 29·1820²) — the descent EXCLUDES every
solution strictly between the certified tower members 9801 and
192119201. -/
theorem pell29_gap
    (HMIN : ∀ X Y : Nat, X * X = 29 * Y * Y + 1 → 1 ≤ Y → 1820 ≤ Y) :
    ∀ X Y : Nat, X * X = 29 * Y * Y + 1 → 1 ≤ Y →
      X = 9801 ∨ 192119201 ≤ X := by
  intro X Y hX hY
  obtain ⟨n, hnX, hnY⟩ := pell29_structure HMIN X Y hX hY
  rcases (show n = 0 ∨ 1 ≤ n by omega) with h0 | hnpos
  · left
    rw [h0] at hnX
    have h1 : (E961P.Pell 29 9801 1820 (0 + 1)).1 = 9801 := by decide
    omega
  · right
    obtain ⟨m, hm⟩ : ∃ m, n = m + 1 := ⟨n - 1, by omega⟩
    rw [hm] at hnX
    rw [hnX]
    show 192119201 ≤ 9801 * (E961P.Pell 29 9801 1820 (m + 1)).1
      + 29 * 1820 * (E961P.Pell 29 9801 1820 (m + 1)).2
    have hXk : 9801 ≤ (E961P.Pell 29 9801 1820 (m + 1)).1 :=
      pell_tower_X_ge_X1 29 9801 1820 m (by omega)
    have hYk : 1820 ≤ (E961P.Pell 29 9801 1820 (m + 1)).2 :=
      pell_tower_Y_ge_Y1 29 9801 1820 m (by omega) (by omega)
    have h1 : 9801 * 9801 ≤ 9801 * (E961P.Pell 29 9801 1820 (m + 1)).1 :=
      Nat.mul_le_mul_left _ hXk
    have h2 : 29 * 1820 * 1820
        ≤ 29 * 1820 * (E961P.Pell 29 9801 1820 (m + 1)).2 :=
      Nat.mul_le_mul_left _ hYk
    have h3 : 9801 * 9801 + 29 * 1820 * 1820 = 192119201 := by decide
    omega

/-! ## §5 THE S-UNIT CENSUS CLOSURE (the 40-pair witness table).

`Smooth11` restated locally (the house import law admits only
`Erdos961Census_Base` + the Arsenal set, so K25/K47's definition is
re-carried verbatim); the 40-pair table is K47's
`e961c_smooth11_dict` re-proved with the identical exponent vectors. -/

/-- 11-smooth: all prime factors in {2,3,5,7,11} (the S-unit census
world; identical shape to the Kernel-25/K47 definition). -/
def Smooth11 (n : Nat) : Prop :=
  ∃ e2 e3 e5 e7 e11 : Nat, 2 ^ e2 * 3 ^ e3 * 5 ^ e5 * 7 ^ e7 * 11 ^ e11 = n

/-- THE 40-PAIR WITNESS CENSUS (the certified Størmer output over
S = {2,3,5,7,11}): every one of the 40 certified values n has BOTH n and
n+1 11-smooth — each by explicit exponent vector (rfl-computed on the
closed numerics). The values: 1,2,3,4,5,6,7,8,9,10,11,14,15,20,21,24,27,
32,35,44,48,49,54,55,63,80,98,99,120,125,175,224,242,384,440,539,2400,
3024,4374,9800 (the largest pair being (9800, 9801)). -/
theorem e961x2_smooth11_dict : ∀ n : Nat,
    (n = 1 ∨ n = 2 ∨ n = 3 ∨ n = 4 ∨ n = 5 ∨ n = 6 ∨ n = 7 ∨ n = 8 ∨
     n = 9 ∨ n = 10 ∨ n = 11 ∨ n = 14 ∨ n = 15 ∨ n = 20 ∨ n = 21 ∨
     n = 24 ∨ n = 27 ∨ n = 32 ∨ n = 35 ∨ n = 44 ∨ n = 48 ∨ n = 49 ∨
     n = 54 ∨ n = 55 ∨ n = 63 ∨ n = 80 ∨ n = 98 ∨ n = 99 ∨ n = 120 ∨
     n = 125 ∨ n = 175 ∨ n = 224 ∨ n = 242 ∨ n = 384 ∨ n = 440 ∨
     n = 539 ∨ n = 2400 ∨ n = 3024 ∨ n = 4374 ∨ n = 9800) →
    Smooth11 n ∧ Smooth11 (n + 1) := by
  intro n h
  rcases h with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl |
    rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl |
    rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl |
    rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact ⟨⟨0, 0, 0, 0, 0, rfl⟩, ⟨1, 0, 0, 0, 0, rfl⟩⟩
  · exact ⟨⟨1, 0, 0, 0, 0, rfl⟩, ⟨0, 1, 0, 0, 0, rfl⟩⟩
  · exact ⟨⟨0, 1, 0, 0, 0, rfl⟩, ⟨2, 0, 0, 0, 0, rfl⟩⟩
  · exact ⟨⟨2, 0, 0, 0, 0, rfl⟩, ⟨0, 0, 1, 0, 0, rfl⟩⟩
  · exact ⟨⟨0, 0, 1, 0, 0, rfl⟩, ⟨1, 1, 0, 0, 0, rfl⟩⟩
  · exact ⟨⟨1, 1, 0, 0, 0, rfl⟩, ⟨0, 0, 0, 1, 0, rfl⟩⟩
  · exact ⟨⟨0, 0, 0, 1, 0, rfl⟩, ⟨3, 0, 0, 0, 0, rfl⟩⟩
  · exact ⟨⟨3, 0, 0, 0, 0, rfl⟩, ⟨0, 2, 0, 0, 0, rfl⟩⟩
  · exact ⟨⟨0, 2, 0, 0, 0, rfl⟩, ⟨1, 0, 1, 0, 0, rfl⟩⟩
  · exact ⟨⟨1, 0, 1, 0, 0, rfl⟩, ⟨0, 0, 0, 0, 1, rfl⟩⟩
  · exact ⟨⟨0, 0, 0, 0, 1, rfl⟩, ⟨2, 1, 0, 0, 0, rfl⟩⟩
  · exact ⟨⟨1, 0, 0, 1, 0, rfl⟩, ⟨0, 1, 1, 0, 0, rfl⟩⟩
  · exact ⟨⟨0, 1, 1, 0, 0, rfl⟩, ⟨4, 0, 0, 0, 0, rfl⟩⟩
  · exact ⟨⟨2, 0, 1, 0, 0, rfl⟩, ⟨0, 1, 0, 1, 0, rfl⟩⟩
  · exact ⟨⟨0, 1, 0, 1, 0, rfl⟩, ⟨1, 0, 0, 0, 1, rfl⟩⟩
  · exact ⟨⟨3, 1, 0, 0, 0, rfl⟩, ⟨0, 0, 2, 0, 0, rfl⟩⟩
  · exact ⟨⟨0, 3, 0, 0, 0, rfl⟩, ⟨2, 0, 0, 1, 0, rfl⟩⟩
  · exact ⟨⟨5, 0, 0, 0, 0, rfl⟩, ⟨0, 1, 0, 0, 1, rfl⟩⟩
  · exact ⟨⟨0, 0, 1, 1, 0, rfl⟩, ⟨2, 2, 0, 0, 0, rfl⟩⟩
  · exact ⟨⟨2, 0, 0, 0, 1, rfl⟩, ⟨0, 2, 1, 0, 0, rfl⟩⟩
  · exact ⟨⟨4, 1, 0, 0, 0, rfl⟩, ⟨0, 0, 0, 2, 0, rfl⟩⟩
  · exact ⟨⟨0, 0, 0, 2, 0, rfl⟩, ⟨1, 0, 2, 0, 0, rfl⟩⟩
  · exact ⟨⟨1, 3, 0, 0, 0, rfl⟩, ⟨0, 0, 1, 0, 1, rfl⟩⟩
  · exact ⟨⟨0, 0, 1, 0, 1, rfl⟩, ⟨3, 0, 0, 1, 0, rfl⟩⟩
  · exact ⟨⟨0, 2, 0, 1, 0, rfl⟩, ⟨6, 0, 0, 0, 0, rfl⟩⟩
  · exact ⟨⟨4, 0, 1, 0, 0, rfl⟩, ⟨0, 4, 0, 0, 0, rfl⟩⟩
  · exact ⟨⟨1, 0, 0, 2, 0, rfl⟩, ⟨0, 2, 0, 0, 1, rfl⟩⟩
  · exact ⟨⟨0, 2, 0, 0, 1, rfl⟩, ⟨2, 0, 2, 0, 0, rfl⟩⟩
  · exact ⟨⟨3, 1, 1, 0, 0, rfl⟩, ⟨0, 0, 0, 0, 2, rfl⟩⟩
  · exact ⟨⟨0, 0, 3, 0, 0, rfl⟩, ⟨1, 2, 0, 1, 0, rfl⟩⟩
  · exact ⟨⟨0, 0, 2, 1, 0, rfl⟩, ⟨4, 0, 0, 0, 1, rfl⟩⟩
  · exact ⟨⟨5, 0, 0, 1, 0, rfl⟩, ⟨0, 2, 2, 0, 0, rfl⟩⟩
  · exact ⟨⟨1, 0, 0, 0, 2, rfl⟩, ⟨0, 5, 0, 0, 0, rfl⟩⟩
  · exact ⟨⟨7, 1, 0, 0, 0, rfl⟩, ⟨0, 0, 1, 1, 1, rfl⟩⟩
  · exact ⟨⟨3, 0, 1, 0, 1, rfl⟩, ⟨0, 2, 0, 2, 0, rfl⟩⟩
  · exact ⟨⟨0, 0, 0, 2, 1, rfl⟩, ⟨2, 3, 1, 0, 0, rfl⟩⟩
  · exact ⟨⟨5, 1, 2, 0, 0, rfl⟩, ⟨0, 0, 0, 4, 0, rfl⟩⟩
  · exact ⟨⟨4, 3, 0, 1, 0, rfl⟩, ⟨0, 0, 2, 0, 2, rfl⟩⟩
  · exact ⟨⟨1, 7, 0, 0, 0, rfl⟩, ⟨0, 0, 4, 1, 0, rfl⟩⟩
  · exact ⟨⟨3, 0, 2, 2, 0, rfl⟩, ⟨0, 4, 0, 0, 2, rfl⟩⟩

/-! ## §6 THE SMOOTH-RUN TERMINATION (the certified run enumeration). -/

/-- THE CERTIFIED-FRONTIER RUN ENUMERATION (K25's runs11 re-proved in
E961X2 — the house import law does not admit `Erdos961`, so K25's
statement and witnesses are re-carried verbatim): the 12-run (1,…,12)
and the five 3-runs (14,15,16), (20,21,22), (48,49,50), (54,55,56),
(98,99,100) — every element 11-smooth by explicit exponent vector.
A complete finite theorem. -/
theorem e961x2_runs11 :
    (∀ n : Nat, 1 ≤ n → n ≤ 12 → Smooth11 n)
    ∧ (∀ x : Nat, x = 14 ∨ x = 20 ∨ x = 48 ∨ x = 54 ∨ x = 98 →
      Smooth11 x ∧ Smooth11 (x + 1) ∧ Smooth11 (x + 2)) := by
  refine ⟨?_, ?_⟩
  · intro n hlo hhi
    rcases (show n = 1 ∨ n = 2 ∨ n = 3 ∨ n = 4 ∨ n = 5 ∨ n = 6 ∨ n = 7 ∨
        n = 8 ∨ n = 9 ∨ n = 10 ∨ n = 11 ∨ n = 12 by omega) with
      h | h | h | h | h | h | h | h | h | h | h | h
    · subst h; exact ⟨0, 0, 0, 0, 0, rfl⟩
    · subst h; exact ⟨1, 0, 0, 0, 0, rfl⟩
    · subst h; exact ⟨0, 1, 0, 0, 0, rfl⟩
    · subst h; exact ⟨2, 0, 0, 0, 0, rfl⟩
    · subst h; exact ⟨0, 0, 1, 0, 0, rfl⟩
    · subst h; exact ⟨1, 1, 0, 0, 0, rfl⟩
    · subst h; exact ⟨0, 0, 0, 1, 0, rfl⟩
    · subst h; exact ⟨3, 0, 0, 0, 0, rfl⟩
    · subst h; exact ⟨0, 2, 0, 0, 0, rfl⟩
    · subst h; exact ⟨1, 0, 1, 0, 0, rfl⟩
    · subst h; exact ⟨0, 0, 0, 0, 1, rfl⟩
    · subst h; exact ⟨2, 1, 0, 0, 0, rfl⟩
  · intro x hx
    rcases hx with h | h | h | h | h
    · subst h; exact ⟨⟨1, 0, 0, 1, 0, rfl⟩, ⟨0, 1, 1, 0, 0, rfl⟩,
        ⟨4, 0, 0, 0, 0, rfl⟩⟩
    · subst h; exact ⟨⟨2, 0, 1, 0, 0, rfl⟩, ⟨0, 1, 0, 1, 0, rfl⟩,
        ⟨1, 0, 0, 0, 1, rfl⟩⟩
    · subst h; exact ⟨⟨4, 1, 0, 0, 0, rfl⟩, ⟨0, 0, 0, 2, 0, rfl⟩,
        ⟨1, 0, 2, 0, 0, rfl⟩⟩
    · subst h; exact ⟨⟨1, 3, 0, 0, 0, rfl⟩, ⟨0, 0, 1, 0, 1, rfl⟩,
        ⟨3, 0, 0, 1, 0, rfl⟩⟩
    · subst h; exact ⟨⟨1, 0, 0, 2, 0, rfl⟩, ⟨0, 2, 0, 0, 1, rfl⟩,
        ⟨2, 0, 2, 0, 0, rfl⟩⟩

/-- THE CERTIFIED 2-RUN ENUMERATION: the nineteen 2-runs of the certified
census — the 19 census values above the 12-frontier that are not inside
one of the five 3-runs — every element 11-smooth by explicit exponent
vector. Together with §5's dict and `e961x2_runs11` this covers the
CERTIFIED run structure of the 40-value census (11 values in the 12-run
window + 10 in the five 3-runs + 19 in the 2-runs = all 40 census values).
(The exhaustive claim — no OTHER 2-runs of consecutive 11-smooth integers
exist above the frontier — is the census-gated Størmer closure, NOT
asserted here; this theorem is the membership/witness side only.) -/
theorem e961x2_runs11_two : ∀ x : Nat,
    (x = 24 ∨ x = 27 ∨ x = 32 ∨ x = 35 ∨ x = 44 ∨ x = 63 ∨ x = 80 ∨
     x = 120 ∨ x = 125 ∨ x = 175 ∨ x = 224 ∨ x = 242 ∨ x = 384 ∨ x = 440 ∨
     x = 539 ∨ x = 2400 ∨ x = 3024 ∨ x = 4374 ∨ x = 9800) →
    Smooth11 x ∧ Smooth11 (x + 1) := by
  intro x hx
  rcases hx with h | h | h | h | h | h | h | h | h | h | h | h | h | h |
    h | h | h | h | h
  · subst h; exact ⟨⟨3, 1, 0, 0, 0, rfl⟩, ⟨0, 0, 2, 0, 0, rfl⟩⟩
  · subst h; exact ⟨⟨0, 3, 0, 0, 0, rfl⟩, ⟨2, 0, 0, 1, 0, rfl⟩⟩
  · subst h; exact ⟨⟨5, 0, 0, 0, 0, rfl⟩, ⟨0, 1, 0, 0, 1, rfl⟩⟩
  · subst h; exact ⟨⟨0, 0, 1, 1, 0, rfl⟩, ⟨2, 2, 0, 0, 0, rfl⟩⟩
  · subst h; exact ⟨⟨2, 0, 0, 0, 1, rfl⟩, ⟨0, 2, 1, 0, 0, rfl⟩⟩
  · subst h; exact ⟨⟨0, 2, 0, 1, 0, rfl⟩, ⟨6, 0, 0, 0, 0, rfl⟩⟩
  · subst h; exact ⟨⟨4, 0, 1, 0, 0, rfl⟩, ⟨0, 4, 0, 0, 0, rfl⟩⟩
  · subst h; exact ⟨⟨3, 1, 1, 0, 0, rfl⟩, ⟨0, 0, 0, 0, 2, rfl⟩⟩
  · subst h; exact ⟨⟨0, 0, 3, 0, 0, rfl⟩, ⟨1, 2, 0, 1, 0, rfl⟩⟩
  · subst h; exact ⟨⟨0, 0, 2, 1, 0, rfl⟩, ⟨4, 0, 0, 0, 1, rfl⟩⟩
  · subst h; exact ⟨⟨5, 0, 0, 1, 0, rfl⟩, ⟨0, 2, 2, 0, 0, rfl⟩⟩
  · subst h; exact ⟨⟨1, 0, 0, 0, 2, rfl⟩, ⟨0, 5, 0, 0, 0, rfl⟩⟩
  · subst h; exact ⟨⟨7, 1, 0, 0, 0, rfl⟩, ⟨0, 0, 1, 1, 1, rfl⟩⟩
  · subst h; exact ⟨⟨3, 0, 1, 0, 1, rfl⟩, ⟨0, 2, 0, 2, 0, rfl⟩⟩
  · subst h; exact ⟨⟨0, 0, 0, 2, 1, rfl⟩, ⟨2, 3, 1, 0, 0, rfl⟩⟩
  · subst h; exact ⟨⟨5, 1, 2, 0, 0, rfl⟩, ⟨0, 0, 0, 4, 0, rfl⟩⟩
  · subst h; exact ⟨⟨4, 3, 0, 1, 0, rfl⟩, ⟨0, 0, 2, 0, 2, rfl⟩⟩
  · subst h; exact ⟨⟨1, 7, 0, 0, 0, rfl⟩, ⟨0, 0, 4, 1, 0, rfl⟩⟩
  · subst h; exact ⟨⟨3, 0, 2, 2, 0, rfl⟩, ⟨0, 4, 0, 0, 2, rfl⟩⟩

/-- THE CENSUS RUN-COVER: every one of the 40 certified census values
lies inside one of the certified runs — the 12-run window [1,12], one of
the five 3-run triples, or one of the nineteen 2-run pairs. The
run-decomposition COVERS the census (the completeness-style conjunct the
certified data supports: the witness table is exactly the union of the
certified run intervals). -/
theorem e961x2_census_run_cover : ∀ n : Nat,
    (n = 1 ∨ n = 2 ∨ n = 3 ∨ n = 4 ∨ n = 5 ∨ n = 6 ∨ n = 7 ∨ n = 8 ∨
     n = 9 ∨ n = 10 ∨ n = 11 ∨ n = 14 ∨ n = 15 ∨ n = 20 ∨ n = 21 ∨
     n = 24 ∨ n = 27 ∨ n = 32 ∨ n = 35 ∨ n = 44 ∨ n = 48 ∨ n = 49 ∨
     n = 54 ∨ n = 55 ∨ n = 63 ∨ n = 80 ∨ n = 98 ∨ n = 99 ∨ n = 120 ∨
     n = 125 ∨ n = 175 ∨ n = 224 ∨ n = 242 ∨ n = 384 ∨ n = 440 ∨
     n = 539 ∨ n = 2400 ∨ n = 3024 ∨ n = 4374 ∨ n = 9800) →
    (1 ≤ n ∧ n ≤ 12)
    ∨ (n = 14 ∨ n = 15 ∨ n = 16)
    ∨ (n = 20 ∨ n = 21 ∨ n = 22)
    ∨ (n = 48 ∨ n = 49 ∨ n = 50)
    ∨ (n = 54 ∨ n = 55 ∨ n = 56)
    ∨ (n = 98 ∨ n = 99 ∨ n = 100)
    ∨ (n = 24 ∨ n = 25 ∨ n = 27 ∨ n = 28 ∨ n = 32 ∨ n = 33 ∨ n = 35 ∨
       n = 36 ∨ n = 44 ∨ n = 45 ∨ n = 63 ∨ n = 64 ∨ n = 80 ∨ n = 81 ∨
       n = 120 ∨ n = 121 ∨ n = 125 ∨ n = 126 ∨ n = 175 ∨ n = 176 ∨
       n = 224 ∨ n = 225 ∨ n = 242 ∨ n = 243 ∨ n = 384 ∨ n = 385 ∨
       n = 440 ∨ n = 441 ∨ n = 539 ∨ n = 540 ∨ n = 2400 ∨ n = 2401 ∨
       n = 3024 ∨ n = 3025 ∨ n = 4374 ∨ n = 4375 ∨ n = 9800 ∨ n = 9801) := by
  intro n h
  rcases h with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl |
    rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl |
    rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl |
    rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  all_goals omega

/-- THE CENSUS-TERMINAL PELL BRIDGE: the census's largest certified pair
(9800, 9801) — the terminal 2-run of the run enumeration — has its upper
element 9801 exactly the X-COORDINATE of the 29-Pell fundamental
(9801, 1820): 9801² = 29·1820² + 1. The certified census thus
terminates precisely at the descent kernel's own hard instance — the
bridge between §4 and §5: the largest certified smooth pair and the
29-fundamental share the same boundary number 9801. -/
theorem e961x2_census_pell29_terminal :
    Smooth11 9800 ∧ Smooth11 9801 ∧ 9801 * 9801 = 29 * 1820 * 1820 + 1 := by
  refine ⟨⟨3, 0, 2, 2, 0, rfl⟩, ⟨0, 4, 0, 0, 2, rfl⟩, pell29_fundamental_sol⟩

/-! ## §7 THE EXCLUSION-2 MASTER BOARD. -/

/-- THE EXCLUSION-2 MASTER BOARD (11 conjuncts, full statements, flat
anonymous constructor): the strict Y-descent + the composition identity +
the descent-termination structure theorem + the unconditional 29-descent
step + the conditional 29-structure law + THE 29-GAP LAW + the 40-pair
census dict + the certified run enumeration + the 2-run enumeration +
the census run-cover + the census-terminal Pell bridge. -/
theorem e961x2_exclusion2_board :
    (∀ (a X1 Y1 X Y : Nat),
      X1 * X1 = a * Y1 * Y1 + 1 → X * X = a * Y * Y + 1 →
      1 ≤ X1 → 1 ≤ Y1 → X1 < X → X1 * Y - X * Y1 < Y)
    ∧ (∀ (a X1 Y1 X Y : Nat),
      X1 * X1 = a * Y1 * Y1 + 1 → X * X = a * Y * Y + 1 →
      1 ≤ X1 → 1 ≤ Y1 → X1 < X →
      X = X1 * (X1 * X - a * Y * Y1) + a * Y1 * (X1 * Y - X * Y1)
        ∧ Y = Y1 * (X1 * X - a * Y * Y1) + X1 * (X1 * Y - X * Y1))
    ∧ (∀ (a X1 Y1 : Nat), 2 ≤ a → 2 ≤ X1 → 1 ≤ Y1 →
      X1 * X1 = a * Y1 * Y1 + 1 →
      (∀ X Y : Nat, X * X = a * Y * Y + 1 → 1 ≤ Y → Y1 ≤ Y) →
      ∀ Y : Nat, 1 ≤ Y → ∀ X : Nat, X * X = a * Y * Y + 1 →
        ∃ n : Nat, X = (E961P.Pell a X1 Y1 (n + 1)).1
          ∧ Y = (E961P.Pell a X1 Y1 (n + 1)).2)
    ∧ (∀ (X Y : Nat), X * X = 29 * Y * Y + 1 → 1 ≤ Y → 9801 < X →
      1820 < Y ∧ X * 1820 < 9801 * Y ∧ 0 < 9801 * X - 29 * Y * 1820
        ∧ 0 < 9801 * Y - X * 1820
        ∧ (9801 * X - 29 * Y * 1820) * (9801 * X - 29 * Y * 1820)
          = 29 * (9801 * Y - X * 1820) * (9801 * Y - X * 1820) + 1
        ∧ 9801 * Y - X * 1820 < Y)
    ∧ ((∀ X Y : Nat, X * X = 29 * Y * Y + 1 → 1 ≤ Y → 1820 ≤ Y) →
      ∀ X Y : Nat, X * X = 29 * Y * Y + 1 → 1 ≤ Y →
        ∃ n : Nat, X = (E961P.Pell 29 9801 1820 (n + 1)).1
          ∧ Y = (E961P.Pell 29 9801 1820 (n + 1)).2)
    ∧ ((∀ X Y : Nat, X * X = 29 * Y * Y + 1 → 1 ≤ Y → 1820 ≤ Y) →
      ∀ X Y : Nat, X * X = 29 * Y * Y + 1 → 1 ≤ Y →
        X = 9801 ∨ 192119201 ≤ X)
    ∧ (∀ n : Nat,
      (n = 1 ∨ n = 2 ∨ n = 3 ∨ n = 4 ∨ n = 5 ∨ n = 6 ∨ n = 7 ∨ n = 8 ∨
       n = 9 ∨ n = 10 ∨ n = 11 ∨ n = 14 ∨ n = 15 ∨ n = 20 ∨ n = 21 ∨
       n = 24 ∨ n = 27 ∨ n = 32 ∨ n = 35 ∨ n = 44 ∨ n = 48 ∨ n = 49 ∨
       n = 54 ∨ n = 55 ∨ n = 63 ∨ n = 80 ∨ n = 98 ∨ n = 99 ∨ n = 120 ∨
       n = 125 ∨ n = 175 ∨ n = 224 ∨ n = 242 ∨ n = 384 ∨ n = 440 ∨
       n = 539 ∨ n = 2400 ∨ n = 3024 ∨ n = 4374 ∨ n = 9800) →
      Smooth11 n ∧ Smooth11 (n + 1))
    ∧ ((∀ n : Nat, 1 ≤ n → n ≤ 12 → Smooth11 n)
      ∧ (∀ x : Nat, x = 14 ∨ x = 20 ∨ x = 48 ∨ x = 54 ∨ x = 98 →
        Smooth11 x ∧ Smooth11 (x + 1) ∧ Smooth11 (x + 2)))
    ∧ (∀ x : Nat,
      (x = 24 ∨ x = 27 ∨ x = 32 ∨ x = 35 ∨ x = 44 ∨ x = 63 ∨ x = 80 ∨
       x = 120 ∨ x = 125 ∨ x = 175 ∨ x = 224 ∨ x = 242 ∨ x = 384 ∨
       x = 440 ∨ x = 539 ∨ x = 2400 ∨ x = 3024 ∨ x = 4374 ∨ x = 9800) →
      Smooth11 x ∧ Smooth11 (x + 1))
    ∧ (∀ n : Nat,
      (n = 1 ∨ n = 2 ∨ n = 3 ∨ n = 4 ∨ n = 5 ∨ n = 6 ∨ n = 7 ∨ n = 8 ∨
       n = 9 ∨ n = 10 ∨ n = 11 ∨ n = 14 ∨ n = 15 ∨ n = 20 ∨ n = 21 ∨
       n = 24 ∨ n = 27 ∨ n = 32 ∨ n = 35 ∨ n = 44 ∨ n = 48 ∨ n = 49 ∨
       n = 54 ∨ n = 55 ∨ n = 63 ∨ n = 80 ∨ n = 98 ∨ n = 99 ∨ n = 120 ∨
       n = 125 ∨ n = 175 ∨ n = 224 ∨ n = 242 ∨ n = 384 ∨ n = 440 ∨
       n = 539 ∨ n = 2400 ∨ n = 3024 ∨ n = 4374 ∨ n = 9800) →
      (1 ≤ n ∧ n ≤ 12)
      ∨ (n = 14 ∨ n = 15 ∨ n = 16)
      ∨ (n = 20 ∨ n = 21 ∨ n = 22)
      ∨ (n = 48 ∨ n = 49 ∨ n = 50)
      ∨ (n = 54 ∨ n = 55 ∨ n = 56)
      ∨ (n = 98 ∨ n = 99 ∨ n = 100)
      ∨ (n = 24 ∨ n = 25 ∨ n = 27 ∨ n = 28 ∨ n = 32 ∨ n = 33 ∨ n = 35 ∨
         n = 36 ∨ n = 44 ∨ n = 45 ∨ n = 63 ∨ n = 64 ∨ n = 80 ∨ n = 81 ∨
         n = 120 ∨ n = 121 ∨ n = 125 ∨ n = 126 ∨ n = 175 ∨ n = 176 ∨
         n = 224 ∨ n = 225 ∨ n = 242 ∨ n = 243 ∨ n = 384 ∨ n = 385 ∨
         n = 440 ∨ n = 441 ∨ n = 539 ∨ n = 540 ∨ n = 2400 ∨ n = 2401 ∨
         n = 3024 ∨ n = 3025 ∨ n = 4374 ∨ n = 4375 ∨ n = 9800 ∨ n = 9801))
    ∧ (Smooth11 9800 ∧ Smooth11 9801
        ∧ 9801 * 9801 = 29 * 1820 * 1820 + 1) :=
  ⟨descent_w2_lt, descent_compose, pell_structure, pell29_descent_step,
    pell29_structure, pell29_gap, e961x2_smooth11_dict, e961x2_runs11,
    e961x2_runs11_two, e961x2_census_run_cover,
    e961x2_census_pell29_terminal⟩

/-! ## §8 THE 70-13 CONJUGATE LAYER (the −1 fundamental). -/

/-- THE −1 FUNDAMENTAL: (70, 13) solves the negative Pell equation
X² + 1 = 29·Y² (decide-certified: 70² + 1 = 4901 = 29·13²). The seed of
the structural minimality route (§9-§10): the +1 fundamental (9801, 1820)
is its Brahmagupta square. -/
theorem pell29_neg_fundamental : 70 * 70 + 1 = 29 * 13 * 13 := by
  decide

/-- THE CONJUGATE ROUND-TRIP at the 29-fundamental (9801, 1820): the
conjugate map (377·Y − 70·X, 13·X − 70·Y) — the composition with the
inverse of the −1-fundamental — sends the +1 fundamental exactly to the
−1-fundamental (70, 13) (decide-certified; the §12 numeric
pre-verification item "conjugate round-trip"). -/
theorem pell29_conj_fundamental : 377 * 1820 - 70 * 9801 = 70
    ∧ 13 * 9801 - 70 * 1820 = 13 := by
  constructor
  · decide
  · decide

/-- THE RECOMPOSITION at the −1-fundamental: composing (70, 13) with
itself under the Brahmagupta law returns the +1-fundamental (9801, 1820)
— decide-certified (the §12 numeric pre-verification item
"recomposition"). This is the identity that closes the minimality proof
(§10): a conjugate that reaches (70, 13) can only come from (9801, 1820). -/
theorem pell29_recompose_fundamental : 70 * 70 + 377 * 13 = 9801
    ∧ 13 * 70 + 70 * 13 = 1820 := by
  constructor
  · decide
  · decide

/-! ## §9 THE MINIMALITY SWEEP LAYER (the two 12-row decide chunks). -/

/-- THE +1 SMALL-SOLUTION WALKER: `no29plusX y b = true` iff no x ∈ [1, b]
solves x·x = 29·y·y + 1 — structural recursion on the x-bound (the
E677/E850 chunk architecture: a Bool walker, a soundness induction, ONE
closed decide chunk). -/
def no29plusX (y : Nat) : Nat → Bool
  | 0 => true
  | Nat.succ b =>
      if 29 * y * y + 1 = (b + 1) * (b + 1) then false else no29plusX y b

/-- THE −1 SMALL-SOLUTION WALKER: `no29negX y b = true` iff no x ∈ [1, b]
solves x·x + 1 = 29·y·y (the negative-equation rows). -/
def no29negX (y : Nat) : Nat → Bool
  | 0 => true
  | Nat.succ b =>
      if (b + 1) * (b + 1) + 1 = 29 * y * y then false else no29negX y b

/-- SOUNDNESS of the +1 walker (the row induction): a true row certifies
the honest Prop for every x ≤ b (the base x = 0 is vacuous since
0 ≠ 29·y·y + 1; the step splits x < w+1 / x = w+1 against the row's
if-condition). -/
theorem no29plusX_sound (y : Nat) : ∀ b : Nat, no29plusX y b = true →
    ∀ x : Nat, x ≤ b → x * x ≠ 29 * y * y + 1 := by
  intro b
  induction b with
  | zero =>
      intro _ x hx
      have hx0 : x = 0 := by omega
      rw [hx0]
      omega
  | succ w ih =>
      intro hrow x hx
      have hstep : (if 29 * y * y + 1 = (w + 1) * (w + 1) then false
          else no29plusX y w) = true := hrow
      rcases Nat.lt_or_ge x (w + 1) with hlt | hge
      · have hxw : x ≤ w := by omega
        by_cases hif : 29 * y * y + 1 = (w + 1) * (w + 1)
        · rw [if_pos hif] at hstep
          exact absurd hstep (by decide)
        · rw [if_neg hif] at hstep
          exact ih hstep x hxw
      · have hxe : x = w + 1 := by omega
        rw [hxe]
        by_cases hif : 29 * y * y + 1 = (w + 1) * (w + 1)
        · rw [if_pos hif] at hstep
          exact absurd hstep (by decide)
        · exact fun heq => hif heq.symm

/-- SOUNDNESS of the −1 walker. -/
theorem no29negX_sound (y : Nat) : ∀ b : Nat, no29negX y b = true →
    ∀ x : Nat, x ≤ b → x * x + 1 ≠ 29 * y * y := by
  intro b
  induction b with
  | zero =>
      intro _ x hx
      have hx0 : x = 0 := by omega
      rw [hx0]
      omega
  | succ w ih =>
      intro hrow x hx
      have hstep : (if (w + 1) * (w + 1) + 1 = 29 * y * y then false
          else no29negX y w) = true := hrow
      rcases Nat.lt_or_ge x (w + 1) with hlt | hge
      · have hxw : x ≤ w := by omega
        by_cases hif : (w + 1) * (w + 1) + 1 = 29 * y * y
        · rw [if_pos hif] at hstep
          exact absurd hstep (by decide)
        · rw [if_neg hif] at hstep
          exact ih hstep x hxw
      · have hxe : x = w + 1 := by omega
        rw [hxe]
        by_cases hif : (w + 1) * (w + 1) + 1 = 29 * y * y
        · rw [if_pos hif] at hstep
          exact absurd hstep (by decide)
        · exact fun heq => hif heq

/-- THE 12-ROW +1 WALKER: `no29plus12 j = true` iff rows y = 1,…,j are all
clear (row y = j+1 tested through `no29plusX (j+1) 65`, the x-range
[1,65] covering every possible solution since x ≤ 64 when y ≤ 12). -/
def no29plus12 : Nat → Bool
  | 0 => true
  | Nat.succ j =>
      if no29plusX (j + 1) 65 = true then no29plus12 j else false

/-- THE 12-ROW −1 WALKER. -/
def no29neg12 : Nat → Bool
  | 0 => true
  | Nat.succ j =>
      if no29negX (j + 1) 65 = true then no29neg12 j else false

/-- THE +1 CHUNK: all 12 rows clear — kernel-closed evaluation, ONE
decide on a closed Bool equality (the 12 × 65 = 780 if-tests of the
sweep). -/
theorem no29plus12_dec : no29plus12 12 = true := by decide

/-- THE −1 CHUNK: all 12 negative rows clear. -/
theorem no29neg12_dec : no29neg12 12 = true := by decide

/-- SOUNDNESS of the 12-row +1 walker (the row recursion: a true
12-row certifies every row y ∈ [1,12] against every x ≤ 65). -/
theorem no29plus12_sound : ∀ j : Nat, no29plus12 j = true →
    ∀ y : Nat, 1 ≤ y → y ≤ j → ∀ x : Nat, x ≤ 65 →
      x * x ≠ 29 * y * y + 1 := by
  intro j
  induction j with
  | zero =>
      intro _ y hy1 hyw x hx
      omega
  | succ w ih =>
      intro hrow y hy1 hyw x hx
      have hstep : (if no29plusX (w + 1) 65 = true
          then no29plus12 w else false) = true := hrow
      by_cases hif : no29plusX (w + 1) 65 = true
      · rw [if_pos hif] at hstep
        rcases (show y = w + 1 ∨ y ≤ w by omega) with hy | hy
        · rw [hy]
          exact no29plusX_sound (w + 1) 65 hif x hx
        · exact ih hstep y hy1 hy x hx
      · rw [if_neg hif] at hstep
        exact absurd hstep (by decide)

/-- SOUNDNESS of the 12-row −1 walker. -/
theorem no29neg12_sound : ∀ j : Nat, no29neg12 j = true →
    ∀ y : Nat, 1 ≤ y → y ≤ j → ∀ x : Nat, x ≤ 65 →
      x * x + 1 ≠ 29 * y * y := by
  intro j
  induction j with
  | zero =>
      intro _ y hy1 hyw x hx
      omega
  | succ w ih =>
      intro hrow y hy1 hyw x hx
      have hstep : (if no29negX (w + 1) 65 = true
          then no29neg12 w else false) = true := hrow
      by_cases hif : no29negX (w + 1) 65 = true
      · rw [if_pos hif] at hstep
        rcases (show y = w + 1 ∨ y ≤ w by omega) with hy | hy
        · rw [hy]
          exact no29negX_sound (w + 1) 65 hif x hx
        · exact ih hstep y hy1 hy x hx
      · rw [if_neg hif] at hstep
        exact absurd hstep (by decide)

/-- THE +1 SMALL SWEEP MASTER: no positive solution of X² = 29·Y² + 1
with 1 ≤ Y ≤ 12 (every possible witness x is bounded into the walker's
65-window by the square monotonicity 66·66 > 29·12² + 1). -/
theorem pell29_no_small_plus : ∀ y : Nat, 1 ≤ y → y ≤ 12 →
    ∀ x : Nat, x * x ≠ 29 * y * y + 1 := by
  intro y hy1 hy12 x
  by_cases hxeq : x * x = 29 * y * y + 1
  · exfalso
    have hx65 : x ≤ 65 := by
      by_contra hcon
      have h66 : 66 ≤ x := by omega
      have hs : 66 * 66 ≤ x * x := Nat.mul_le_mul h66 h66
      have hy144 : y * y ≤ 12 * 12 := Nat.mul_le_mul hy12 hy12
      have h29 : 29 * (y * y) ≤ 29 * (12 * 12) :=
        Nat.mul_le_mul_left _ hy144
      omega
    exact no29plus12_sound 12 no29plus12_dec y hy1 hy12 x hx65 hxeq
  · exact hxeq

/-- THE −1 SMALL SWEEP MASTER: no solution of X² + 1 = 29·Y² with
1 ≤ Y ≤ 12 — the (70, 13) row is the FIRST negative solution. -/
theorem pell29_no_small_neg : ∀ v : Nat, 1 ≤ v → v ≤ 12 →
    ∀ u : Nat, u * u + 1 ≠ 29 * v * v := by
  intro v hv1 hv12 u
  by_cases hueq : u * u + 1 = 29 * v * v
  · exfalso
    have hu65 : u ≤ 65 := by
      by_contra hcon
      have h66 : 66 ≤ u := by omega
      have hs : 66 * 66 ≤ u * u := Nat.mul_le_mul h66 h66
      have hv144 : v * v ≤ 12 * 12 := Nat.mul_le_mul hv12 hv12
      have h29 : 29 * (v * v) ≤ 29 * (12 * 12) :=
        Nat.mul_le_mul_left _ hv144
      omega
    exact no29neg12_sound 12 no29neg12_dec v hv1 hv12 u hu65 hueq
  · exact hueq

/-! ## §10 THE MINIMALITY THEOREM — HMIN INSIDE LEAN (the structural
route). -/

/-- THE STRUCTURAL MINIMALITY THEOREM (HMIN certified INSIDE Lean): every
positive solution of X² = 29·Y² + 1 has Y ≥ 1820 — there is NO solution
with 1 ≤ Y ≤ 1819. The 1819-row brute sweep is above the 501 decide cap,
so the proof is the TOWER-GAP route through the −1 equation:

* Y ≤ 12: the m1 sweep (`pell29_no_small_plus`).
* Y ≥ 13: the conjugate v = (377·Y − 70·X, 13·X − 70·Y) — the composition
  with the inverse of the −1-fundamental (70, 13) — is a POSITIVE
  −1-solution (13·X > 70·Y always; 70·X < 377·Y for Y ≥ 13, both by
  square comparison), and its second coordinate hits the WALL
  vY ≤ 13: from (13·X)² = (70·Y + vY)² and X² = 29·Y² + 1 one gets
  vY·(13·X + 70·Y) = Y² + 169, so 14 ≤ vY would force
  1960·Y + 14·vY ≤ Y² + 169 ≤ 1819·Y + 169, i.e. 141·Y ≤ 155 against
  Y ≥ 13 — contradiction.
* vY ≤ 12: the m2 sweep (`pell29_no_small_neg`).
* vY = 13: then vX² = 29·13² − 1 = 4900 forces vX = 70, and the
  recomposition keys (X = 70·vX + 377·vY, Y = 13·vX + 70·vY — pure
  omega-linear algebra over the two conjugate equations) force
  (X, Y) = (9801, 1820), contradicting Y ≤ 1819.

This discharges the HMIN hypothesis of §4's conditional laws — the
descent machine of Kernel 46 now hangs off a Lean-certified minimality. -/
theorem pell29_minimal : ∀ X Y : Nat, X * X = 29 * Y * Y + 1 → 1 ≤ Y →
    1820 ≤ Y := by
  intro X Y hX hY
  by_contra hcon
  have hY1819 : Y ≤ 1819 := by omega
  rcases (show Y ≤ 12 ∨ 13 ≤ Y by omega) with hsmall | hbig
  · exact pell29_no_small_plus Y hY hsmall X hX
  · -- 13·X > 70·Y (unconditional for +1-solutions)
    have h13X : 70 * Y < 13 * X := by
      by_contra hc
      have hle : 13 * X ≤ 70 * Y := by omega
      have hs : (13 * X) * (13 * X) ≤ (70 * Y) * (70 * Y) :=
        Nat.mul_le_mul hle hle
      have hL : (13 * X) * (13 * X) = 169 * (X * X) := by ring
      have hR : (70 * Y) * (70 * Y) = 4900 * (Y * Y) := by ring
      rw [hL, hR] at hs
      omega
    -- 70·X < 377·Y (for Y ≥ 13)
    have h70X : 70 * X < 377 * Y := by
      by_contra hc
      have hle : 377 * Y ≤ 70 * X := by omega
      have hs : (377 * Y) * (377 * Y) ≤ (70 * X) * (70 * X) :=
        Nat.mul_le_mul hle hle
      have hL : (377 * Y) * (377 * Y) = 142129 * (Y * Y) := by ring
      have hR : (70 * X) * (70 * X) = 4900 * (X * X) := by ring
      rw [hL, hR] at hs
      have h169 : 13 * 13 ≤ Y * Y := Nat.mul_le_mul hbig hbig
      have h4901 : 29 * (13 * 13) ≤ 29 * (Y * Y) :=
        Nat.mul_le_mul_left _ h169
      omega
    -- the conjugate pair (sub-to-add, the K46 obtain-pattern)
    obtain ⟨vX, hA⟩ : ∃ vX, 377 * Y = 70 * X + vX :=
      ⟨377 * Y - 70 * X, by omega⟩
    obtain ⟨vY, hB⟩ : ∃ vY, 13 * X = 70 * Y + vY :=
      ⟨13 * X - 70 * Y, by omega⟩
    -- THE CONJUGATE IS A −1-SOLUTION: vX² + 1 = 29·vY² (the identity
    -- assembly: two square keys + two cross keys, one omega)
    have qa : (13 * X) * (13 * X) = 169 * (X * X) := by ring
    have qb : (70 * Y + vY) * (70 * Y + vY)
        = 4900 * (Y * Y) + 140 * (vY * Y) + vY * vY := by ring
    have qc : (13 * X) * (13 * X) = (70 * Y + vY) * (70 * Y + vY) := by
      rw [hB]
    have KEY1 : 4900 * (Y * Y) + 140 * (vY * Y) + vY * vY
        = 169 * (X * X) := by omega
    have ra : (377 * Y) * (377 * Y) = 142129 * (Y * Y) := by ring
    have rb : (70 * X + vX) * (70 * X + vX)
        = 4900 * (X * X) + 140 * (vX * X) + vX * vX := by ring
    have rc : (377 * Y) * (377 * Y) = (70 * X + vX) * (70 * X + vX) := by
      rw [hA]
    have KEY2 : 142129 * (Y * Y)
        = 4900 * (X * X) + 140 * (vX * X) + vX * vX := by omega
    have c1 : 377 * (X * Y) = 70 * (X * X) + vX * X := by
      have d1 : X * (377 * Y) = X * (70 * X + vX) := by rw [hA]
      have d2 : X * (70 * X + vX) = 70 * (X * X) + vX * X := by ring
      have d3 : X * (377 * Y) = 377 * (X * Y) := by ring
      omega
    have c2 : 13 * (X * Y) = 70 * (Y * Y) + vY * Y := by
      have d4 : Y * (13 * X) = Y * (70 * Y + vY) := by rw [hB]
      have d5 : Y * (70 * Y + vY) = 70 * (Y * Y) + vY * Y := by ring
      have d6 : Y * (13 * X) = 13 * (X * Y) := by ring
      omega
    have hneg : vX * vX + 1 = 29 * vY * vY := by omega
    -- THE WALL: vY ≤ 13
    have hvY13 : vY ≤ 13 := by
      by_contra hc
      have h14 : 14 ≤ vY := by omega
      have W1 : vY * vY + 140 * (vY * Y) = Y * Y + 169 := by omega
      have m1 : vY * (140 * Y + vY) = 140 * (vY * Y) + vY * vY := by
        ring
      have m2 : 14 * (140 * Y + vY) = 1960 * Y + 14 * vY := by ring
      have m3 : 14 * (140 * Y + vY) ≤ vY * (140 * Y + vY) :=
        Nat.mul_le_mul h14 (Nat.le_refl _)
      have hYY : Y * Y ≤ 1819 * Y := Nat.mul_le_mul_right Y hY1819
      omega
    have hv1 : 1 ≤ vY := by omega
    rcases (show vY ≤ 12 ∨ vY = 13 by omega) with h12 | h13
    · exact pell29_no_small_neg vY hv1 h12 vX hneg
    · -- vY = 13 → vX = 70 (the square between 69² and 71²)
      have hvX70 : vX = 70 := by
        rw [h13] at hneg
        by_contra hc
        rcases (show vX ≤ 69 ∨ 71 ≤ vX by omega) with hle | hge
        · have h69 : vX * vX ≤ 69 * 69 := Nat.mul_le_mul hle hle
          omega
        · have h71 : 71 * 71 ≤ vX * vX := Nat.mul_le_mul hge hge
          omega
      -- THE RECOMPOSITION KEYS (omega-linear over the conjugate eqs)
      have k1 : 910 * X + 13 * vX = 4901 * Y := by
        have e1 : 13 * (377 * Y) = 13 * (70 * X + vX) := by rw [hA]
        have e2 : 13 * (70 * X + vX) = 910 * X + 13 * vX := by ring
        have e3 : 13 * (377 * Y) = 4901 * Y := by ring
        omega
      have k2 : 910 * X = 4900 * Y + 70 * vY := by
        have f1 : 70 * (13 * X) = 70 * (70 * Y + vY) := by rw [hB]
        have f2 : 70 * (70 * Y + vY) = 4900 * Y + 70 * vY := by ring
        have f3 : 70 * (13 * X) = 910 * X := by ring
        omega
      omega

/-- THE UNCONDITIONAL 29-STRUCTURE LAW: every positive 29-solution is a
tower member over (9801, 1820) — §4's conditional `pell29_structure`
fed the Lean-certified minimality `pell29_minimal` (the Kernel-46 descent
machine with the HMIN gap closed inside Lean). -/
theorem pell29_structure_min : ∀ X Y : Nat, X * X = 29 * Y * Y + 1 →
    1 ≤ Y →
    ∃ n : Nat, X = (E961P.Pell 29 9801 1820 (n + 1)).1
      ∧ Y = (E961P.Pell 29 9801 1820 (n + 1)).2 :=
  pell29_structure pell29_minimal

/-- THE UNCONDITIONAL 29-GAP LAW: every positive solution is either the
fundamental itself (X = 9801) or at least the second tower member
(192119201 ≤ X) — the descent EXCLUDES everything strictly between the
certified tower members, now with NO external minimality hypothesis. -/
theorem pell29_gap_min : ∀ X Y : Nat, X * X = 29 * Y * Y + 1 → 1 ≤ Y →
    X = 9801 ∨ 192119201 ≤ X :=
  pell29_gap pell29_minimal

/-! ## §11 THE POWER-REP LAYER (the tower as the power map). -/

/-- THE TOWER STEP UNFOLD (X-column): the recursion IS the Brahmagupta
composition with the fundamental (definitional rfl on the equation
compiler's succ-pattern). -/
theorem pell_step_X (a X1 Y1 k : Nat) : (E961P.Pell a X1 Y1 (k + 1)).1
    = X1 * (E961P.Pell a X1 Y1 k).1 + a * Y1 * (E961P.Pell a X1 Y1 k).2 :=
  rfl

/-- THE TOWER STEP UNFOLD (Y-column). -/
theorem pell_step_Y (a X1 Y1 k : Nat) : (E961P.Pell a X1 Y1 (k + 1)).2
    = X1 * (E961P.Pell a X1 Y1 k).2 + Y1 * (E961P.Pell a X1 Y1 k).1 :=
  rfl

/-- THE POWER-REPRESENTATION LAW (the tower IS the power map): the
Brahmagupta composition of tower members n and m is the tower member
n + m — Pell(n+m) = Pell(n) ∘ Pell(m). Induction on m through the step
unfolds; the step case is the associativity of the bilinear composition
(one `ring` on the four coordinates). This is the power-representation
of the solution set: the tower enumerates exactly the powers of the
fundamental. -/
theorem pell_tower_pow_add : ∀ (a X1 Y1 n m : Nat),
    (E961P.Pell a X1 Y1 (n + m)).1
      = (E961P.Pell a X1 Y1 n).1 * (E961P.Pell a X1 Y1 m).1
        + a * (E961P.Pell a X1 Y1 n).2 * (E961P.Pell a X1 Y1 m).2
    ∧ (E961P.Pell a X1 Y1 (n + m)).2
      = (E961P.Pell a X1 Y1 n).1 * (E961P.Pell a X1 Y1 m).2
        + (E961P.Pell a X1 Y1 n).2 * (E961P.Pell a X1 Y1 m).1 := by
  intro a X1 Y1 n m
  induction m with
  | zero =>
      rw [Nat.add_zero]
      constructor
      · show (E961P.Pell a X1 Y1 n).1
            = (E961P.Pell a X1 Y1 n).1 * 1
              + a * (E961P.Pell a X1 Y1 n).2 * 0
        simp only [Nat.mul_one, Nat.mul_zero, Nat.add_zero]
      · show (E961P.Pell a X1 Y1 n).2
            = (E961P.Pell a X1 Y1 n).1 * 0
              + (E961P.Pell a X1 Y1 n).2 * 1
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

/-- THE BRAHMAGUPTA SQUARE (the power-2 representation): tower member 2
is the fundamental composed with itself — (X₁² + a·Y₁², 2·X₁·Y₁) — by the
one-step definitional unfolds (the K46 `pell_sol` zero-case pattern). -/
theorem pell_tower_two_square (a X1 Y1 : Nat) :
    (E961P.Pell a X1 Y1 2).1 = X1 * X1 + a * Y1 * Y1
    ∧ (E961P.Pell a X1 Y1 2).2 = 2 * X1 * Y1 := by
  constructor
  · show X1 * (X1 * 1 + a * Y1 * 0) + a * Y1 * (X1 * 0 + Y1 * 1)
        = X1 * X1 + a * Y1 * Y1
    simp only [Nat.mul_one, Nat.mul_zero, Nat.add_zero, Nat.zero_add]
  · show X1 * (X1 * 0 + Y1 * 1) + Y1 * (X1 * 1 + a * Y1 * 0)
        = 2 * X1 * Y1
    simp only [Nat.mul_one, Nat.mul_zero, Nat.add_zero, Nat.zero_add]
    ring

/-- THE CHEBYSHEV DOUBLE-ANGLE (additive form): tower member 2 satisfies
X₂ + 1 = 2·X₁² — the classical power-2 law X₂ = 2·X₁² − 1, from the
fundamental equation X₁² = a·Y₁² + 1 (one omega over the two-square law). -/
theorem pell_tower_two_cheb (a X1 Y1 : Nat)
    (hf : X1 * X1 = a * Y1 * Y1 + 1) :
    (E961P.Pell a X1 Y1 2).1 + 1 = 2 * X1 * X1 := by
  have h2 := (pell_tower_two_square a X1 Y1).1
  omega

/-- THE POWER-REP AT 29 — the doubling law on every even tower index:
tower member 2(k+1) is the Brahmagupta square of member (k+1):
X_{2(k+1)} + 1 = 2·X_{k+1}² (Chebyshev's doubling, from the power law
`pell_tower_pow_add` at n = m = k+1 plus the K46 solution law). -/
theorem pell29_double_angle : ∀ k : Nat,
    (E961P.Pell 29 9801 1820 ((k + 1) + (k + 1))).1 + 1
      = 2 * (E961P.Pell 29 9801 1820 (k + 1)).1
        * (E961P.Pell 29 9801 1820 (k + 1)).1 := by
  intro k
  obtain ⟨hX, hY⟩ := pell_tower_pow_add 29 9801 1820 (k + 1) (k + 1)
  have hsol := E961P.pell_sol 29 9801 1820 pell29_fundamental_sol k
  omega

/-- THE STØRMER FACTORIZATION LAW (general): every solution of
X² = a·Y² + 1 splits as (X−1)·(X+1) = a·Y² — the multiplicative anatomy
that drives the smoothness census (X ≥ 1 since X² = a·Y² + 1 ≥ 1; then
the sub-to-add expansion around X = k+1). -/
theorem pell_factor_law : ∀ (a X Y : Nat), X * X = a * Y * Y + 1 →
    (X - 1) * (X + 1) = a * Y * Y := by
  intro a X Y hEq
  rcases (show X = 0 ∨ 1 ≤ X by omega) with h0 | h1
  · rw [h0] at hEq
    omega
  · obtain ⟨k, hk⟩ : ∃ k, X = k + 1 := ⟨X - 1, by omega⟩
    rw [hk] at hEq
    have e : (k + 1) * (k + 1) = k * k + 2 * k + 1 := by ring
    rw [e] at hEq
    have g1 : X - 1 = k := by omega
    have g3 : X + 1 = k + 2 := by omega
    have e2 : k * (k + 2) = k * k + 2 * k := by ring
    rw [g1, g3, e2]
    omega

/-- THE 29 INSTANCE of the Størmer factorization: the fundamental's
(9801−1)·(9801+1) = 29·1820² — the certified census-terminal anatomy
(the general law applied to the decide-certified fundamental). -/
theorem pell29_factor : (9801 - 1) * (9801 + 1) = 29 * 1820 * 1820 :=
  pell_factor_law 29 9801 1820 pell29_fundamental_sol

/-- THE FACTOR LAW in subtraction form (decide-receipt): 9801² − 1 =
29·1820² AND the ±1 split. -/
theorem pell29_factor_law : 9801 * 9801 - 1 = 29 * 1820 * 1820
    ∧ (9801 - 1) * (9801 + 1) = 29 * 1820 * 1820 := by
  constructor
  · decide
  · exact pell29_factor

/-- THE ±1 FACTOR DICT at the census-terminal pair (the §12-certified
smoothness structure): 9800 = 2³·5²·7² (11-smooth — the lower element of
the terminal 2-run), 9802 = 2·13²·29 (the +1 cofactor side carrying the
Pell parameter), 1820 = 2²·5·7·13 (the Y-anatomy). The Pell equation's
multiplicative anatomy of the terminal 2-run (9800, 9801). -/
theorem pell29_factor_dict :
    9801 - 1 = 9800 ∧ 9800 = 2^3 * 5^2 * 7^2 ∧ 9801 + 1 = 9802
    ∧ 9802 = 2 * 13 * 13 * 29 ∧ 1820 = 2 * 2 * 5 * 7 * 13 := by
  constructor
  · decide
  · constructor
    · decide
    · constructor
      · decide
      · constructor
        · decide
        · decide

/-! ## §12 THE GROWTH-LAW STRENGTHENING (the fundamental-based
exponential separation). -/

/-- The power recursion in the right-multiplied orientation (K48's
rfl-verified step, restated in this namespace — the house import law
does not admit `Erdos961Exclusion`). -/
theorem powMul_step (M k : Nat) : M ^ (k + 1) = M ^ k * M := by
  rfl

/-- 9801^e ≥ 1 for every exponent (the positivity engine for the
separation law; the Erdos711-green induction shape). -/
theorem pow_pos_9801 : ∀ e : Nat, 1 ≤ 9801 ^ e := by
  intro e
  induction e with
  | zero => rw [Nat.pow_zero]
  | succ k ih =>
      rw [Nat.pow_succ]
      have h := Nat.mul_le_mul ih (by omega)
      simpa using h

/-- THE MULTIPLICATIVE SEPARATION STEP: every tower step at least
multiplies X by the fundamental's X₁ — X₁·X_k ≤ X_{k+1} (the additive
a·Y₁·Y_k side is dropped; the one-step definitional show). -/
theorem pell_tower_step_mul : ∀ (a X1 Y1 k : Nat),
    X1 * (E961P.Pell a X1 Y1 k).1 ≤ (E961P.Pell a X1 Y1 (k + 1)).1 := by
  intro a X1 Y1 k
  show X1 * (E961P.Pell a X1 Y1 k).1
      ≤ X1 * (E961P.Pell a X1 Y1 k).1 + a * Y1 * (E961P.Pell a X1 Y1 k).2
  exact Nat.le_add_right _ _

/-- THE FUNDAMENTAL-BASED EXPONENTIAL SEPARATION (the growth-law
strengthening): X₁^n ≤ X_n for every n ≥ 0 — the tower grows at least as
fast as the fundamental's own powers. Strictly stronger than K48's
2^n ≤ X_{n+1} whenever the fundamental exceeds 2 (at a = 29:
X₁ = 9801 ≥ 2^13). The proof is the K48 `pell_tower_growth` cascade
rewritten for the base-X₁ power: the succ step goes through the
right-multiplied `powMul_step`, the comm bridge `Nat.mul_comm`, and the
pure `Nat.le_trans` cascade (omega never touches a power). -/
theorem pell_tower_X_ge_pow : ∀ (a X1 Y1 n : Nat), 2 ≤ X1 →
    X1 ^ n ≤ (E961P.Pell a X1 Y1 n).1 := by
  intro a X1 Y1 n hX1
  induction n with
  | zero =>
      show X1 ^ 0 ≤ 1
      rw [Nat.pow_zero]
  | succ k ih =>
      show X1 ^ (k + 1) ≤ X1 * (E961P.Pell a X1 Y1 k).1
          + a * Y1 * (E961P.Pell a X1 Y1 k).2
      rw [powMul_step]
      have h1 : X1 ^ k * X1 ≤ (E961P.Pell a X1 Y1 k).1 * X1 :=
        Nat.mul_le_mul_right _ ih
      have h2 : (E961P.Pell a X1 Y1 k).1 * X1
          ≤ X1 * (E961P.Pell a X1 Y1 k).1 :=
        Nat.le_of_eq (Nat.mul_comm _ _)
      have h3 : X1 * (E961P.Pell a X1 Y1 k).1
          ≤ X1 * (E961P.Pell a X1 Y1 k).1
            + a * Y1 * (E961P.Pell a X1 Y1 k).2 :=
        Nat.le_add_right _ _
      exact Nat.le_trans h1 (Nat.le_trans h2 h3)

/-- THE 29 INSTANCE of the separation law: 9801^n ≤ X_n on the
29-tower. -/
theorem pell29_tower_X_ge_pow : ∀ n : Nat,
    9801 ^ n ≤ (E961P.Pell 29 9801 1820 n).1 :=
  fun n => pell_tower_X_ge_pow 29 9801 1820 n (by omega)

/-- THE EXPONENTIAL SCALE RECEIPT: the fundamental sits between 2^13
and 2^14, and its square is the second member's wall — the certified
scale anchors of the separation (decide). -/
theorem pell29_exp_scale : 2^13 ≤ 9801 ∧ 9801 * 9801 = 96059601 := by
  constructor
  · decide
  · decide

/-- THE STRENGTHENED UNCONDITIONAL GAP (the three-wall separation): every
positive 29-solution is the fundamental (X = 9801), the second tower
member (X = 192119201), or at least the THIRD WALL 9801³ =
941480149401 — the fundamental-based exponential separation
9801^{n+1} ≤ X_{n+1} applied inside the (now unconditional) structure
law: members beyond the second obey X ≥ 9801³. -/
theorem pell29_gap3_min : ∀ X Y : Nat, X * X = 29 * Y * Y + 1 → 1 ≤ Y →
    X = 9801 ∨ X = 192119201 ∨ 941480149401 ≤ X := by
  intro X Y hX hY
  obtain ⟨n, hnX, hnY⟩ := pell29_structure_min X Y hX hY
  rcases (show n = 0 ∨ n = 1 ∨ 2 ≤ n by omega) with h0 | h1 | h2
  · rw [h0] at hnX
    have hw1 : (E961P.Pell 29 9801 1820 (0 + 1)).1 = 9801 := by decide
    omega
  · rw [h1] at hnX
    have hw2 : (E961P.Pell 29 9801 1820 (1 + 1)).1 = 192119201 := by
      decide
    omega
  · have hge : 9801 ^ (n + 1) ≤ (E961P.Pell 29 9801 1820 (n + 1)).1 :=
      pell_tower_X_ge_pow 29 9801 1820 (n + 1) (by omega)
    have hmono : 9801 ^ 3 ≤ 9801 ^ (n + 1) := by
      obtain ⟨j, hj⟩ : ∃ j, n + 1 = 3 + j := ⟨n - 1, by omega⟩
      rw [hj, Nat.pow_add]
      have hpos : 1 ≤ 9801 ^ j := pow_pos_9801 j
      have hmul : 9801 ^ 3 * 1 ≤ 9801 ^ 3 * 9801 ^ j :=
        Nat.mul_le_mul (Nat.le_refl _) hpos
      rw [Nat.mul_one] at hmul
      exact hmul
    have hcub : 9801 ^ 3 = 941480149401 := by decide
    have hchain : 941480149401 ≤ (E961P.Pell 29 9801 1820 (n + 1)).1 :=
      Nat.le_trans (Nat.le_of_eq hcub.symm)
        (Nat.le_trans hmono hge)
    omega

/-! ## §13 THE EXCLUSION-2 MASTER BOARD 2 (the new layers). -/

/-- THE EXCLUSION-2 MASTER BOARD 2 (15 conjuncts, full statements, flat
anonymous constructor): the −1-fundamental + the conjugate round-trip +
the recomposition + the two small-sweep masters + THE STRUCTURAL
MINIMALITY (HMIN inside Lean) + the unconditional structure law + the
unconditional gap law + the strengthened three-wall gap + the Størmer
factorization + the ±1 factor dict + the power-representation law +
the doubling law + the fundamental-based exponential separation + the
scale receipt. -/
theorem e961x2_exclusion2_board2 :
    (70 * 70 + 1 = 29 * 13 * 13)
    ∧ (377 * 1820 - 70 * 9801 = 70 ∧ 13 * 9801 - 70 * 1820 = 13)
    ∧ (70 * 70 + 377 * 13 = 9801 ∧ 13 * 70 + 70 * 13 = 1820)
    ∧ (∀ y : Nat, 1 ≤ y → y ≤ 12 → ∀ x : Nat, x * x ≠ 29 * y * y + 1)
    ∧ (∀ v : Nat, 1 ≤ v → v ≤ 12 → ∀ u : Nat, u * u + 1 ≠ 29 * v * v)
    ∧ (∀ X Y : Nat, X * X = 29 * Y * Y + 1 → 1 ≤ Y → 1820 ≤ Y)
    ∧ (∀ X Y : Nat, X * X = 29 * Y * Y + 1 → 1 ≤ Y →
        ∃ n : Nat, X = (E961P.Pell 29 9801 1820 (n + 1)).1
          ∧ Y = (E961P.Pell 29 9801 1820 (n + 1)).2)
    ∧ (∀ X Y : Nat, X * X = 29 * Y * Y + 1 → 1 ≤ Y →
        X = 9801 ∨ 192119201 ≤ X)
    ∧ (∀ X Y : Nat, X * X = 29 * Y * Y + 1 → 1 ≤ Y →
        X = 9801 ∨ X = 192119201 ∨ 941480149401 ≤ X)
    ∧ ((9801 - 1) * (9801 + 1) = 29 * 1820 * 1820)
    ∧ (9801 - 1 = 9800 ∧ 9800 = 2^3 * 5^2 * 7^2 ∧ 9801 + 1 = 9802
        ∧ 9802 = 2 * 13 * 13 * 29 ∧ 1820 = 2 * 2 * 5 * 7 * 13)
    ∧ (∀ (a X1 Y1 n m : Nat),
        (E961P.Pell a X1 Y1 (n + m)).1
          = (E961P.Pell a X1 Y1 n).1 * (E961P.Pell a X1 Y1 m).1
            + a * (E961P.Pell a X1 Y1 n).2 * (E961P.Pell a X1 Y1 m).2
        ∧ (E961P.Pell a X1 Y1 (n + m)).2
          = (E961P.Pell a X1 Y1 n).1 * (E961P.Pell a X1 Y1 m).2
            + (E961P.Pell a X1 Y1 n).2 * (E961P.Pell a X1 Y1 m).1)
    ∧ (∀ k : Nat,
        (E961P.Pell 29 9801 1820 ((k + 1) + (k + 1))).1 + 1
          = 2 * (E961P.Pell 29 9801 1820 (k + 1)).1
            * (E961P.Pell 29 9801 1820 (k + 1)).1)
    ∧ (∀ (a X1 Y1 n : Nat), 2 ≤ X1 →
        X1 ^ n ≤ (E961P.Pell a X1 Y1 n).1)
    ∧ (2^13 ≤ 9801 ∧ 9801 * 9801 = 96059601) :=
  ⟨pell29_neg_fundamental, pell29_conj_fundamental,
    pell29_recompose_fundamental, pell29_no_small_plus,
    pell29_no_small_neg, pell29_minimal, pell29_structure_min,
    pell29_gap_min, pell29_gap3_min, pell29_factor,
    pell29_factor_dict, pell_tower_pow_add, pell29_double_angle,
    pell_tower_X_ge_pow, pell29_exp_scale⟩

/-! ## §14 THE KERNEL-58 TOWER-ORDERING LAYER (strict monotonicity, the
linear fundamental bound, and the gap monotonicity). -/

/-- THE TOWER X-POSITIVITY (engine): every tower member's X is at least 1
(no fundamental-solution hypothesis — only 1 ≤ X1; the zero member is
definitional 1, and the step adds a nonnegative residue to X1·X_k ≥ 1). -/
theorem pell_tower_X_pos : ∀ (a X1 Y1 k : Nat), 1 ≤ X1 →
    1 ≤ (E961P.Pell a X1 Y1 k).1 := by
  intro a X1 Y1 k hX1
  induction k with
  | zero =>
      show 1 ≤ 1
      omega
  | succ j ih =>
      show 1 ≤ X1 * (E961P.Pell a X1 Y1 j).1
          + a * Y1 * (E961P.Pell a X1 Y1 j).2
      have h1 : 1 * 1 ≤ X1 * (E961P.Pell a X1 Y1 j).1 :=
        Nat.mul_le_mul hX1 ih
      omega

/-- THE LINEAR INDEX BOUND: every tower member's X exceeds its index —
k + 1 ≤ X_k (the engine for the X₁·k lower bound: the step multiplies by
X1 ≥ 2, so X grows at least twice as fast as the index). -/
theorem pell_tower_X_ge_succ : ∀ (a X1 Y1 k : Nat), 2 ≤ X1 →
    k + 1 ≤ (E961P.Pell a X1 Y1 k).1 := by
  intro a X1 Y1 k hX1
  induction k with
  | zero =>
      show 0 + 1 ≤ 1
      omega
  | succ j ih =>
      show j + 1 + 1 ≤ X1 * (E961P.Pell a X1 Y1 j).1
          + a * Y1 * (E961P.Pell a X1 Y1 j).2
      have h2 : 2 * (E961P.Pell a X1 Y1 j).1
          ≤ X1 * (E961P.Pell a X1 Y1 j).1 :=
        Nat.mul_le_mul_right _ hX1
      omega

/-- THE STRICT X-MONOTONICITY of the tower: X_k < X_{k+1} for every k (the
zero step is 1 < X1; the succ step is the X1 ≥ 2 domination
X_{k+2} = X1·X_{k+1} + a·Y1·Y_{k+1} ≥ 2·X_{k+1} > X_{k+1}, with the
predecessor's positivity from the induction hypothesis). -/
theorem pell_tower_X_strict_mono : ∀ (a X1 Y1 k : Nat), 2 ≤ X1 →
    (E961P.Pell a X1 Y1 k).1 < (E961P.Pell a X1 Y1 (k + 1)).1 := by
  intro a X1 Y1 k hX1
  induction k with
  | zero =>
      show 1 < X1 * 1 + a * Y1 * 0
      omega
  | succ j ih =>
      show (E961P.Pell a X1 Y1 (j + 1)).1
          < X1 * (E961P.Pell a X1 Y1 (j + 1)).1
              + a * Y1 * (E961P.Pell a X1 Y1 (j + 1)).2
      have h2 : 2 * (E961P.Pell a X1 Y1 (j + 1)).1
          ≤ X1 * (E961P.Pell a X1 Y1 (j + 1)).1 :=
        Nat.mul_le_mul_right _ hX1
      omega

/-- THE LINEAR FUNDAMENTAL BOUND (the tower-ordering strengthening,
X_k ≥ X₁·k): X₁·k ≤ X_k for every k — the tower's X-column dominates the
fundamental's own linear scale. (The additive companion of §12's
exponential `pell_tower_X_ge_pow` X₁^k ≤ X_k: the index engine k+1 ≤ X_k
feeds the step X₁·(k+1) ≤ X₁·X_k ≤ X_{k+1}.) -/
theorem pell_tower_X_ge_X1_mul : ∀ (a X1 Y1 n : Nat), 2 ≤ X1 →
    X1 * n ≤ (E961P.Pell a X1 Y1 n).1 := by
  intro a X1 Y1 n hX1
  induction n with
  | zero =>
      show X1 * 0 ≤ 1
      omega
  | succ k ih =>
      show X1 * (k + 1) ≤ X1 * (E961P.Pell a X1 Y1 k).1
          + a * Y1 * (E961P.Pell a X1 Y1 k).2
      have hksucc : k + 1 ≤ (E961P.Pell a X1 Y1 k).1 :=
        pell_tower_X_ge_succ a X1 Y1 k hX1
      have hmul : X1 * (k + 1) ≤ X1 * (E961P.Pell a X1 Y1 k).1 :=
        Nat.mul_le_mul_left _ hksucc
      omega

/-- THE GAP MONOTONICITY (the consecutive-gap law, via the composition
step): the gap between consecutive tower members is STRICTLY INCREASING —

  X_{n+1} − X_n  <  X_{n+2} − X_{n+1}.

Proof (the one-step composition law `pell_step_X` — the recursion IS the
Brahmagupta composition with the fundamental): X_{n+2} = X₁·X_{n+1} +
a·Y₁·Y_{n+1} ≥ 2·X_{n+1} (X1 ≥ 2), so with X_n ≥ 1 (positivity engine) and
the strict monotonicity keeping both subtractions honest:
X_{n+2} + X_n ≥ 2·X_{n+1} + 1 > 2·X_{n+1} — the additive form of
gap_n < gap_{n+1}. -/
theorem pell_tower_gap_mono : ∀ (a X1 Y1 n : Nat), 2 ≤ X1 →
    (E961P.Pell a X1 Y1 (n + 1)).1 - (E961P.Pell a X1 Y1 n).1
      < (E961P.Pell a X1 Y1 (n + 1 + 1)).1 - (E961P.Pell a X1 Y1 (n + 1)).1 := by
  intro a X1 Y1 n hX1
  have hposn : 1 ≤ (E961P.Pell a X1 Y1 n).1 :=
    pell_tower_X_pos a X1 Y1 n (by omega)
  have hmono1 : (E961P.Pell a X1 Y1 n).1 < (E961P.Pell a X1 Y1 (n + 1)).1 :=
    pell_tower_X_strict_mono a X1 Y1 n hX1
  have hmono2 : (E961P.Pell a X1 Y1 (n + 1)).1
      < (E961P.Pell a X1 Y1 (n + 1 + 1)).1 :=
    pell_tower_X_strict_mono a X1 Y1 (n + 1) hX1
  have hstep : (E961P.Pell a X1 Y1 (n + 1 + 1)).1
      = X1 * (E961P.Pell a X1 Y1 (n + 1)).1
          + a * Y1 * (E961P.Pell a X1 Y1 (n + 1)).2 := pell_step_X a X1 Y1 (n + 1)
  have hdom : 2 * (E961P.Pell a X1 Y1 (n + 1)).1
      ≤ X1 * (E961P.Pell a X1 Y1 (n + 1)).1 :=
    Nat.mul_le_mul_right _ hX1
  show (E961P.Pell a X1 Y1 (n + 1)).1 - (E961P.Pell a X1 Y1 n).1
      < (E961P.Pell a X1 Y1 (n + 1 + 1)).1 - (E961P.Pell a X1 Y1 (n + 1)).1
  omega

/-- THE 29 STRICT-MONO INSTANCE: the certified 29-tower strictly increases
in X. -/
theorem pell29_tower_X_strict_mono : ∀ n : Nat,
    (E961P.Pell 29 9801 1820 n).1 < (E961P.Pell 29 9801 1820 (n + 1)).1 :=
  fun n => pell_tower_X_strict_mono 29 9801 1820 n (by omega)

/-- THE 29 LINEAR-BOUND INSTANCE: 9801·n ≤ X_n on the 29-tower (the
fundamental-based linear scale). -/
theorem pell29_tower_X_ge_X1_mul : ∀ n : Nat,
    9801 * n ≤ (E961P.Pell 29 9801 1820 n).1 :=
  fun n => pell_tower_X_ge_X1_mul 29 9801 1820 n (by omega)

/-- THE 29 GAP-MONO INSTANCE: on the certified 29-tower the consecutive
gaps strictly increase (gap₀ = 9800, gap₁ = 192109400, …). -/
theorem pell29_tower_gap_mono : ∀ n : Nat,
    (E961P.Pell 29 9801 1820 (n + 1)).1 - (E961P.Pell 29 9801 1820 n).1
      < (E961P.Pell 29 9801 1820 (n + 1 + 1)).1
          - (E961P.Pell 29 9801 1820 (n + 1)).1 :=
  fun n => pell_tower_gap_mono 29 9801 1820 n (by omega)

/-- THE GAP RECEIPT (decide on the certified members): the first two gaps
of the 29-tower are exactly 9800 (= 9801 − 1 — the census-terminal lower
element, 2³·5²·7²) and 192109400 (= 192119201 − 9801 — forced arithmetic
on the §12-certified members 1 and 2). -/
theorem pell29_gap_receipt :
    (E961P.Pell 29 9801 1820 1).1 - (E961P.Pell 29 9801 1820 0).1 = 9800
    ∧ (E961P.Pell 29 9801 1820 2).1 - (E961P.Pell 29 9801 1820 1).1
        = 192109400 := by
  constructor
  · decide
  · decide

/-- THE BOUNDED MINIMALITY (the a = 29 structured minimality step, in the
bounded-sweep statement): for 0 < Y < 1820 there is NO solution (X, Y) of
X² = 29·Y² + 1 with X ≤ 9801. The 1819-row brute sweep sits above the
decide cap (STATUS_EXCLUSION2.md §13 — the structural route is the
certified path), so the proof runs through §10's STRUCTURAL minimality
`pell29_minimal` (every positive 29-solution has Y ≥ 1820 — HMIN inside
Lean): a Y < 1820 solution contradicts it outright. The X ≤ 9801 bound is
carried in the statement (the sweep formulation); the structural theorem
needs no X-bound at all — it excludes every solution below the
fundamental unconditionally. -/
theorem pell29_min_Y_lower : ∀ Y : Nat, 1 ≤ Y → Y < 1820 →
    ∀ X : Nat, X ≤ 9801 → X * X ≠ 29 * Y * Y + 1 := by
  intro Y hY hYlt X _ hXeq
  have h1820 : 1820 ≤ Y := pell29_minimal X Y hXeq hY
  omega

/-! ## §15 THE KERNEL-58 MASTER BOARD 3 (the tower-ordering layer). -/

/-- THE EXCLUSION-2 MASTER BOARD 3 (10 conjuncts, full statements, flat
anonymous constructor): the tower X-positivity + the linear index bound +
the strict X-monotonicity + THE LINEAR FUNDAMENTAL BOUND + THE GAP
MONOTONICITY + the three 29-instances + the gap receipt + THE BOUNDED
MINIMALITY. -/
theorem e961x2_exclusion2_board3 :
    (∀ (a X1 Y1 k : Nat), 1 ≤ X1 → 1 ≤ (E961P.Pell a X1 Y1 k).1)
    ∧ (∀ (a X1 Y1 k : Nat), 2 ≤ X1 → k + 1 ≤ (E961P.Pell a X1 Y1 k).1)
    ∧ (∀ (a X1 Y1 k : Nat), 2 ≤ X1 →
        (E961P.Pell a X1 Y1 k).1 < (E961P.Pell a X1 Y1 (k + 1)).1)
    ∧ (∀ (a X1 Y1 n : Nat), 2 ≤ X1 →
        X1 * n ≤ (E961P.Pell a X1 Y1 n).1)
    ∧ (∀ (a X1 Y1 n : Nat), 2 ≤ X1 →
        (E961P.Pell a X1 Y1 (n + 1)).1 - (E961P.Pell a X1 Y1 n).1
          < (E961P.Pell a X1 Y1 (n + 1 + 1)).1 - (E961P.Pell a X1 Y1 (n + 1)).1)
    ∧ (∀ n : Nat,
        (E961P.Pell 29 9801 1820 n).1 < (E961P.Pell 29 9801 1820 (n + 1)).1)
    ∧ (∀ n : Nat, 9801 * n ≤ (E961P.Pell 29 9801 1820 n).1)
    ∧ (∀ n : Nat,
        (E961P.Pell 29 9801 1820 (n + 1)).1 - (E961P.Pell 29 9801 1820 n).1
          < (E961P.Pell 29 9801 1820 (n + 1 + 1)).1
              - (E961P.Pell 29 9801 1820 (n + 1)).1)
    ∧ ((E961P.Pell 29 9801 1820 1).1 - (E961P.Pell 29 9801 1820 0).1 = 9800
        ∧ (E961P.Pell 29 9801 1820 2).1 - (E961P.Pell 29 9801 1820 1).1
            = 192109400)
    ∧ (∀ Y : Nat, 1 ≤ Y → Y < 1820 → ∀ X : Nat, X ≤ 9801 →
        X * X ≠ 29 * Y * Y + 1) :=
  ⟨pell_tower_X_pos, pell_tower_X_ge_succ, pell_tower_X_strict_mono,
    pell_tower_X_ge_X1_mul, pell_tower_gap_mono, pell29_tower_X_strict_mono,
    pell29_tower_X_ge_X1_mul, pell29_tower_gap_mono, pell29_gap_receipt,
    pell29_min_Y_lower⟩

#print axioms E961X2.nat_strong_ind
#print axioms E961X2.descent_w2_lt
#print axioms E961X2.descent_compose
#print axioms E961X2.pell_structure
#print axioms E961X2.pell_tower_X_ge_X1
#print axioms E961X2.pell_tower_Y_ge_Y1
#print axioms E961X2.pell29_fundamental_sol
#print axioms E961X2.pell29_tower_one
#print axioms E961X2.pell29_tower_two
#print axioms E961X2.pell29_descent_step
#print axioms E961X2.pell29_structure
#print axioms E961X2.pell29_gap
#print axioms E961X2.e961x2_smooth11_dict
#print axioms E961X2.e961x2_runs11
#print axioms E961X2.e961x2_runs11_two
#print axioms E961X2.e961x2_census_run_cover
#print axioms E961X2.e961x2_census_pell29_terminal
#print axioms E961X2.e961x2_exclusion2_board
#print axioms E961X2.pell29_neg_fundamental
#print axioms E961X2.pell29_conj_fundamental
#print axioms E961X2.pell29_recompose_fundamental
#print axioms E961X2.no29plusX_sound
#print axioms E961X2.no29negX_sound
#print axioms E961X2.no29plus12_dec
#print axioms E961X2.no29neg12_dec
#print axioms E961X2.no29plus12_sound
#print axioms E961X2.no29neg12_sound
#print axioms E961X2.pell29_no_small_plus
#print axioms E961X2.pell29_no_small_neg
#print axioms E961X2.pell29_minimal
#print axioms E961X2.pell29_structure_min
#print axioms E961X2.pell29_gap_min
#print axioms E961X2.pell_step_X
#print axioms E961X2.pell_step_Y
#print axioms E961X2.pell_tower_pow_add
#print axioms E961X2.pell_tower_two_square
#print axioms E961X2.pell_tower_two_cheb
#print axioms E961X2.pell29_double_angle
#print axioms E961X2.pell_factor_law
#print axioms E961X2.pell29_factor
#print axioms E961X2.pell29_factor_law
#print axioms E961X2.pell29_factor_dict
#print axioms E961X2.powMul_step
#print axioms E961X2.pow_pos_9801
#print axioms E961X2.pell_tower_step_mul
#print axioms E961X2.pell_tower_X_ge_pow
#print axioms E961X2.pell29_tower_X_ge_pow
#print axioms E961X2.pell29_exp_scale
#print axioms E961X2.pell29_gap3_min
#print axioms E961X2.e961x2_exclusion2_board2
#print axioms E961X2.pell_tower_X_pos
#print axioms E961X2.pell_tower_X_ge_succ
#print axioms E961X2.pell_tower_X_strict_mono
#print axioms E961X2.pell_tower_X_ge_X1_mul
#print axioms E961X2.pell_tower_gap_mono
#print axioms E961X2.pell29_tower_X_strict_mono
#print axioms E961X2.pell29_tower_X_ge_X1_mul
#print axioms E961X2.pell29_tower_gap_mono
#print axioms E961X2.pell29_gap_receipt
#print axioms E961X2.pell29_min_Y_lower
#print axioms E961X2.e961x2_exclusion2_board3

#eval "E961X2_EXCLUSION2_GREEN"
end E961X2
