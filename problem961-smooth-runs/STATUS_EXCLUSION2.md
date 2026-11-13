# STATUS — K58 Kernel 58 (Erdos961Exclusion2, THE EXCLUSION LAYER 2, namespace `E961X2`)

1. FILE: `problem961-smooth-runs/Erdos961Exclusion2.lean` (717 lines, namespace `E961X2`,
   imports `Erdos961Census_Base` FIRST + `Arsenal.ErdosTernary2.Basic` +
   `Arsenal.CardinalWorlds` + `Arsenal.CardinalWorldsV2` only; `maxRecDepth 65536` +
   `maxHeartbeats 4000000`). ZERO sorry / admit / native_decide / Mathlib.
   All 18 theorems are complete propositions with complete proofs; no fake glue.

2. §0 ENGINE — `nat_strong_ind` (strong induction on Nat, core-only accumulator
   form: the `key : ∀ n m, m < n → P m` accumulator by plain induction; final
   discharge `exact H n (key n)`). The termination engine for the descent.

3. §1 STRICT DESCENT (new beyond K46/K48) — `descent_w2_lt`: the conjugate's
   second coordinate w2 = X₁·Y − X·Y₁ is STRICTLY below Y. Method: the
   difference-of-squares identity `w2·(X₁·Y + X·Y₁) + Y₁² = Y²` (ring-normalized
   product atoms over the K46 sub-to-add pattern), then by_contra with the
   `Nat.mul_le_mul_left/right` product bounds in EXACT goal spellings
   (`w2·(Y+Y₁) ≤ w2·(X₁·Y+X·Y₁)` etc.) and the K48-green `1 * 1 ≤ Y * Y1`
   mul_le_mul spelling (literal LHS does not unify against `?m * ?k`).
   — `descent_compose`: the conjugate recomposed with the fundamental returns
   the original (X = X₁·w1 + a·Y₁·w2 ∧ Y = Y₁·w1 + X₁·w2); pure ring algebra
   over bridged product atoms, K46 descent_pos supplying sub-positivity.

4. §2 THE DESCENT-TERMINATION / STRUCTURE THEOREM — `pell_structure` (conditional
   on HMIN minimality): relative to a minimal fundamental (X₁, Y₁) EVERY positive
   solution (X, Y) of X² = a·Y² + 1 is a tower member (∃ n, (X, Y) =
   (Pell a X1 Y1 (n+1)).1/.2). Method: strong induction on Y (§0); X ≤ X₁ branch
   forces (X, Y) = (X₁, Y₁) via HMIN + the (X+1)² strict-square trick; X₁ < X
   branch fires the K46 descent (descent_sol gives the conjugate as a solution,
   §1 gives w2 < Y), applies the IH at w2 (all four explicit binders: w2, w2 < y,
   1 ≤ w2, X := w1, hsol1), and recomposes via descent_compose as the NEXT tower
   member (one-step definitional `show`-unfolds of the Pell recursion, K46/K48
   defeq pattern). Tower-member certification engine: `pell_tower_X_ge_X1`,
   `pell_tower_Y_ge_Y1` (every positive member ≥ the fundamental, by induction +
   `Nat.mul_le_mul_left` exact spellings).

5. §4 THE 29-a INSTANTIATION — `pell29_fundamental_sol` (9801² = 29·1820² + 1,
   decide), `pell29_tower_one` (= (9801, 1820)), `pell29_tower_two`
   (= (192119201, 35675640)), both decide; `pell29_descent_step` — FULLY
   UNCONDITIONAL: every 29-solution beyond the fundamental descends to a
   strictly-smaller positive solution (six conjuncts: 1820 < Y, X·1820 < 9801·Y,
   conjugate positivity ×2, conjugate solves the equation, w2 < Y);
   `pell29_structure` (conditional on HMIN); `pell29_gap` — THE GAP LAW
   (conditional on HMIN): every positive solution has X = 9801 or
   192119201 ≤ X — the descent EXCLUDES everything strictly between the
   certified tower members 9801 and 192119201.

6. §5 S-UNIT CENSUS CLOSURE — `e961x2_smooth11_dict`: the 40-pair Størmer
   witness table re-carried from K47 (the import law admits only
   Erdos961Census_Base + Arsenal, so a local `Smooth11` of the IDENTICAL shape
   is defined and the table re-proved with the identical exponent vectors —
   every one of the 40 certified values n has n and n+1 both 11-smooth, each
   witness rfl-computed on closed numerics).

7. §6 SMOOTH-RUN TERMINATION — `e961x2_runs11` (K25's runs11 re-proved: the
   12-run (1..12) + the five 3-runs (14,15,16), (20,21,22), (48,49,50),
   (54,55,56), (98,99,100) — complete finite theorem); `e961x2_runs11_two`
   (the nineteen 2-runs of the certified census, the 19 census values outside
   the 12-run and the five 3-runs); `e961x2_census_run_cover` (run-decomposition
   coverage: all 40 census values lie in the certified runs);
   `e961x2_census_pell29_terminal` (the census-terminal Pell bridge: the largest
   certified pair (9800, 9801) — both 11-smooth — with the upper element 9801
   exactly the X of the 29-Pell fundamental: 9801² = 29·1820² + 1).

8. §7 MASTER BOARD — `e961x2_exclusion2_board`: the 11-conjunct master assembly
   (descent_w2_lt + descent_compose + pell_structure + pell29_descent_step +
   pell29_structure + pell29_gap + e961x2_smooth11_dict + e961x2_runs11 +
   e961x2_runs11_two + e961x2_census_run_cover + e961x2_census_pell29_terminal),
   flat anonymous constructor, full unconditional statements (the two HMIN
   conditionals carried as implications inside the board).

9. Receipt block: 18 `#print axioms` lines (one per theorem, exact names) +
   `#eval "E961X2_EXCLUSION2_GREEN"`, inside the namespace. Expected axiom
   status: `[propext, Classical.choice, Quot.sound]`-only or cleaner (the proofs
   are by_contra/omega/ring/decide/rfl/Nat-lemmas + the green E961P machine).
   Commander wires the `Erdos961Census_Base` olean staging (import is the first
   line, exactly as required — same shape as green K48).

10. DEVIATIONS (honest scope, all deliberate):
   (a) pell29_structure / pell29_gap are CONDITIONAL on HMIN (minimality of
       (9801, 1820): no 0 < Y < 1820 solution). Minimality is certified OUTSIDE
       Lean (brute sweep over 0 < Y < 1820: 29·Y²+1 is never a square — 1819
       checks, re-verified numerically this session; stormer961_output.txt's
       6874-check sweep is the engine's own minimality certification over the
       S-unit a-parameters). Never faked inside Lean.
   (b) The mission's "1 < X satisfies X ≥ second tower member" is delivered in
       the precise form `9801 < X → X = 9801 ∨ 192119201 ≤ X` (conditional on
       HMIN) — the unconditional layer is the descent step itself.
   (c) The witness census/runs use rfl-computed exponent vectors (the K47-green
       method) — `decide` is not applicable to unbounded ∃-witness statements;
       "decide-certified checks" in the mission read as the closed-numeric
       decide checks (fundamental, tower members, gap numerics), which ARE
       decide.
   (d) The exhaustive "no other 2-runs exist" closure is census-gated (Størmer
       closure) and is NOT asserted; e961x2_runs11_two is the
       membership/witness side only.
   (e) This session repaired 7 latent defects in the draft file (see item 11).

11. REPAIR LEDGER (draft → final; all fixes verified against K46/K48-green
   patterns, no lake/lean run — CI-only per mission):
   (1) nat_strong_ind's final discharge `exact key n n (by omega)` proved the
       FALSE `n < n` → `exact H n (key n)`;
   (2) descent_w2_lt's `h10 : 1 ≤ Y * Y1 := Nat.mul_le_mul (by omega) (by omega)`
       — literal LHS does not unify against `?m * ?k` (K48-green evidence:
       Erdos961Exclusion.lean lines 98-101 use `1 * 1 ≤ ...`) → the `1 * 1 ≤
       Y * Y1` spelling;
   (3) pell_structure's `h6 : 1 ≤ a * (2 * Y1 + 1) := Nat.mul_le_mul ha (…)`
       — same literal-LHS unification gap (`2 * ?k =?= 1`) → `2 * 1 ≤
       a * (2 * Y1 + 1)` (omega folds 2 * 1 → 2);
   (4) pell_structure's IH application `ih w2 (by omega) (by omega) hsol1` —
       the explicit ∀-X binder was missing → `ih w2 (by omega) (by omega) w1
       hsol1`;
   (5) pell29_gap's `pell_tower_X_ge_X1 29 9801 1820 (by omega) m` — the
       (by omega) sat in the m-slot (Nat) and m in the 2 ≤ X1 slot (Prop) →
       `pell_tower_X_ge_X1 29 9801 1820 m (by omega)`;
   (6) same for `pell_tower_Y_ge_Y1 29 9801 1820 m (by omega) (by omega)`;
   (7) receipt line `#print axioms E961x2.census_run_cover` (case-typo + wrong
       name — unknown identifier at CI) → `#print axioms
       E961X2.e961x2_census_run_cover`.
   Plus docstring honesty repairs (§4 minimality note made accurate — the 6874
   sweep is over the S-unit a-parameters, the a=29 sweep is the 1819-check
   brute; §6 "complete 2-run layer" scoped to the certified census; the
   terminal-bridge phrasing "upper element = the X of the fundamental").

12. NUMERIC PRE-VERIFICATION (this session, python): the 29-fundamental
   (9801² = 29·1820²+1 ✓), tower member 2 = (192119201, 35675640) ✓, the gap
   identity 9801² + 29·1820² = 192119201 ✓, all 40 dict vectors and all
   n+1 vectors ✓, the 12-run/3-run/2-run vectors ✓, run-cover of the 40 values ✓,
   9800 = 2³·5²·7², 9801 = 3⁴·11² ✓, conjugate round-trip + recomposition +
   w2-identity at the 29-fundamental/tower members ✓, a=29 minimality brute
   (0 < Y < 1820) ✓.

13. Next exclusion layers (Kernel 59+): bring HMIN inside Lean (the minimality
   as a decide-certiﬁed bounded sweep would need a bounded-∀ over 1819 values —
   above the 501 decide cap, so a structural route (Lucas/CF bounds) is the
   natural next layer); the full Størmer closure (every consecutive 11-smooth
   pair is one of the 40) off pell29_structure-style machinery over all 31
   surviving a-parameters; the f961 frontier beyond 97.
