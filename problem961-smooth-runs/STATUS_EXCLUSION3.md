# STATUS — K66 Kernel 66 (Erdos961Exclusion3, THE EXCLUSION LAYER 3, namespace `E961X3`)

1. FILE: `problem961-smooth-runs/Erdos961Exclusion3.lean` (574 lines, namespace
   `E961X3`, imports `Arsenal.ErdosTernary2.Basic` + `Arsenal.CardinalWorlds` +
   `Arsenal.CardinalWorldsV2` ONLY — SELF-CONTAINED, per the house CI rule that
   each kernel compiles standalone via `lake env lean`; the K46 base machinery
   (`Pell`, `pell_compose`, `pell_sol`) is re-carried VERBATIM in `E961X3` since
   `Erdos961Census_Base` is not an admissible import for this kernel).
   `maxRecDepth 65536` + `maxHeartbeats 4000000` (both under the campaign caps).
   ZERO sorry / admit / axiom / native_decide / Mathlib-import. 21 theorems +
   1 def, all complete propositions with complete proofs; no fake glue.

2. §0 BASE MACHINE (K46-verbatim re-carried) — `Pell` (the n-fold Brahmagupta
   power of the fundamental), `pell_compose` (THE composition law:
   (X₁·Xk + a·Y₁·Yk)² = a·(X₁·Yk + Y₁·Xk)² + 1, the K46 ring+omega assembly),
   `pell_sol` (every positive tower member solves X² = a·Y² + 1, the K46
   induction with `exact pell_compose hf ih`), `pell_compose_full` (the
   explicit-telescope form for the board; one `intro` + `exact pell_compose`).

3. §1 TOWER-ORDERING ENGINE (K58 §14-verbatim restated) — `pell_step_X` /
   `pell_step_Y` (rfl step unfolds), `pell_tower_X_pos` (the `1 * 1` mul
   spelling), `pell_tower_X_ge_succ` (linear index bound), 
   `pell_tower_X_strict_mono` (strict X-monotonicity), 
   `pell_tower_X_ge_X1_mul` (THE LINEAR FUNDAMENTAL BOUND X₁·n ≤ X_n).

4. §2-§3 THE POWER REPRESENTATION AND THE GROWTH LAWS (the layer-3 core) —
   `pell_tower_pow_add` (K58 §11-verbatim: Pell(n+m) = Pell(n) ∘ Pell(m), the
   tower IS the power map; induction on m, the succ case one `ring` per column
   through the step unfolds), **`pell_tower_X_supermul` — NEW beyond K58**:
   X_n·X_m ≤ X_{n+m} (the super-multiplicative growth law; one omega over the
   power law's first conjunct, the product atoms `X_n·X_m` and `a·Y_n·Y_m`
   atomized — the campaign's K46 `pell_compose`-final-omega idiom),
   `powMul_step` (rfl power step) + **`pell_tower_X_ge_pow`** (K58 §12-verbatim:
   THE EXPONENTIAL GROWTH LAW X₁^n ≤ X_n — the multiplicative strengthening of
   the linear bound; the right-multiplied powMul_step orientation, the
   `Nat.mul_comm` bridge, the pure `Nat.le_trans` cascade, omega never touching
   a power).

5. §4 THE GAP CASCADE — `pell_tower_gap_mono` (K58 §14-verbatim: consecutive
   tower gaps strictly increase, X_{n+1} − X_n < X_{n+2} − X_{n+1}; the
   positivity + double strict-monotonicity + one-step composition + `2·X ≤
   X₁·X` domination, final omega over the truncated subtractions).

6. §5 THE FIVE NEW PRIME FAMILY ROWS (a ∈ {13, 19, 23, 31, 37} — beyond
   K58's a = 29): `pell13_row`, `pell19_row`, `pell23_row`, `pell31_row`,
   `pell37_row` — each ONE complete theorem (6 conjuncts; 8 for the two
   smallest families):
   * the fundamental witness, decide-certified: 13→(649,180), 19→(170,39),
     23→(24,5), 31→(1520,273), 37→(73,12);
   * the exact second tower member, decide: 13→(842401,233640),
     19→(57799,13260), 23→(1151,240), 31→(4620799,829920), 37→(10657,1752);
   * (a = 23, 37 only) the exact THIRD tower member, decide: 23→(55224,11515),
     37→(1555849,255780);
   * the Brahmagupta composition row — the `pell_compose_full` instance at the
     fundamental pair (explicit telescope application `pell_compose_full a X1
     Y1 X1 Y1 hf hf`, fully-applied, zero unification risk);
   * the solvability law ∀n (pell_sol instance: every positive tower member of
     the family solves the family equation);
   * the exponential growth corollary ∀n (X₁^n ≤ X_n instance);
   * the gap-cascade instance ∀n (pell_tower_gap_mono instance);
   * (a = 23, 37 only) the numeric gap-cascade receipt, decide: gaps
     23 < 1127 < 54073 (a = 23) and 72 < 10584 < 1545192 (a = 37).

7. §6 THE SCALE RECEIPT — `e961x3_family_scale_receipt`: 2^4 ≤ 24, 2^7 ≤ 170,
   2^9 ≤ 649, 2^10 ≤ 1520, 2^6 ≤ 73 (the exponential law therefore beats the
   2^n scale on every new family; all decide).

8. §7 THE MASTER BOARD — `e961x3_exclusion3_board`: the 11-conjunct master
   receipt (pell_compose_full + pell_tower_X_supermul + pell_tower_X_ge_pow +
   pell_tower_X_ge_X1_mul + pell_tower_gap_mono + the five family rows + the
   scale receipt), flat anonymous constructor, full unconditional statements
   (the only hypotheses anywhere are the equation hypotheses and 2 ≤ X₁).

9. Receipt block: 21 `#print axioms` lines (one per theorem, exact names,
   full `E961X3.` paths) + `#eval "E961X3_EXCLUSION3_GREEN"`, inside the
   namespace (the K58 receipt placement). Expected axiom status:
   `[propext, Classical.choice, Quot.sound]`-only or cleaner (the proofs are
   ring/omega/decide/rfl/simp-only + core Nat lemmas).

10. DEVIATIONS (honest scope, all deliberate):
    (a) MINIMALITY of the five new fundamentals (no smaller positive solution)
        is NOT asserted — this layer certifies the witness/tower/growth side;
        the a=29 template for minimality is K58 §9-§10 (the structural route);
        a=13's minimality sweep (0 < Y < 180, 179 checks) is UNDER the 501
        decide cap and is the natural next layer, with 23 (4 checks) and 37
        (11 checks) even cheaper.
    (b) The family rows prove the fundamentals are SOLUTIONS (decide) and the
        towers' growth/gap structure; the structure-theorem side (every
        solution is a tower member) remains conditional-on-minimality and is
        not re-carried here (it needs the descent engine + HMIN, the K58
        pattern — next layer once minimality lands).
    (c) The board's generic laws are spelled with the EXACT binder telescopes
        of their referenced theorems (the K58 board pattern — no implicit-
        binder references; pell_compose_full exists precisely to give the
        composition law an explicit telescope).
    (d) `pell_sol`'s type carries a named hypothesis binder, so it is NOT
        referenced as a bare board conjunct (binder-shape risk, per the K59
        r2 repair lesson); its instances appear inside the family rows only.

11. CONSTRUCTION DISCIPLINE (blind-write safeguards, all mirrored on green):
    * every conjunct pair in the family rows/board is parenthesized
      `((...).1 = A ∧ (...).2 = B)` — the K58 board2 grouping style; the
      refine's nested anonymous constructors align slot-for-slot with the
      top-level conjuncts (6/6, 6/6, 8/8, 6/6, 8/8 — machine-audited this
      session);
    * board arity machine-audited: 11 top-level conjuncts ↔ 11 proof terms,
      and each family row's statement appears VERBATIM in the board
      (string-equality audit, this session);
    * no `cases`-with-binder patterns anywhere (binder law moot); no Bool
      equations (L92/L93 moot); no `set_option` above the caps; decide only
      on closed numerals (L-NO-OOM clean: no bounded-∀ sweeps at all).

12. NUMERIC PRE-VERIFICATION (this session, python): all five fundamentals
    (649² = 421201 = 13·180²+1, 170² = 28900 = 19·39²+1, 24² = 576 =
    23·5²+1, 1520² = 2310400 = 31·273²+1, 73² = 5329 = 37·12²+1), all five
    second members, both third members, all five compose-row identities
    ((X₁²+a·Y₁²)² = a·(2X₁Y₁)²+1 — e.g. 13: 709639444801 both sides), the
    gap cascades (23 < 1127 < 54073; 72 < 10584 < 1545192), the five power
    scales (16≤24<32, 128≤170<256, 512≤649<1024, 1024≤1520<2048, 64≤73<128),
    and every tower member re-verified as a solution (X_k² = a·Y_k² + 1).
    ALL PASSED.

13. CI-RISK FLAGS (honest, for the commander's root-repair kit):
    (a) `pell_tower_X_supermul`'s single `omega` over product atoms — the
        campaign-idiomatic route (K46 pell_compose's final omega is the green
        precedent, over MORE complex atoms); if omega balks at atomizing, the
        fallback is `rw [hsum]; exact Nat.le_add_right _ _`.
    (b) `pell_compose_full a X1 Y1 Xk Yk hf hf` instances — fully explicit
        applications (no implicit unification), the lowest-risk shape; the
        family rows' compose conjuncts are spelled in the exact conclusion
        shape of the telescope.
    (c) `powMul_step := rfl` — verbatim K58 §12 (green evidence); relies on
        core Nat.pow's right-multiplied recursion exactly as K58 does.
    (d) `refine ⟨hf, ⟨by decide, by decide⟩, …⟩` nested anonymous
        constructors — arity-audited against the parenthesized conjunct
        groups; the flat board constructor (11 terms) is the K58-board
        pattern verbatim.
    (e) The unused `ih` in `pell_tower_X_strict_mono`'s succ case — verbatim
        K58 (linter warning at most, never an error).

14. Next exclusion layers (Kernel 67+): minimality inside Lean for the small
    families (a = 23: 4-check sweep; a = 37: 11 checks; a = 19: 38 checks; all
    far under the 501 cap — the E677/E850 chunk architecture not even
    needed); the structure theorem + gap laws per new family off the K58
    §9-§10 template; the Størmer closure over the surviving a-parameters;
    f961 frontier beyond 97.
