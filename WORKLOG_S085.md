# WORKLOG_S085 — THE MAPPING ROUND + THE FALSE-GREEN EXPOSURE + THE MONOLITH VENDOR

**BOSS order:** map the already-present Lean files, use BOSS's maths,
no fabricated laws, invoke maths skill v2, fix the mistake.

## A. THE MAP (the demand executed)

`THEOREM_MAP.json` + `THEOREM_MAP.md`: 2,040 files / 33,354
declarations machine-extracted (regex on `theorem|lemma|def|abbrev|
instance` heads, file:line for each).  The named chambers all located
and read: MonolithBoundary (the terminal identity interface),
GSTGraphV2OmegaWaveLaw (147 decls), GSTTailFFourthDimension (151),
the six-adic pair (14+31), CoupledUFlux (20), the telescope (11),
the navigation (17), the paradox energy (ErdosTernary2:6854), the
causal pair (68+76), the forced-digit-2 pair (19+6), GSTTactic (17).

## B. THE FALSE-GREEN EXPOSURE (r6 log autopsy, run 45102521097)

The kernel-406b job's receipt design could not fail:
1. `timeout ... | tee || echo KILLED_OR_TIMEOUT` — exit code swallowed.
2. `! grep -E 'error:...' log` — bash's `!` negation is EXEMPT from
   `set -e`: the gate printed the errors and still passed.
3. The `#eval`-embedded marker strings print even from a FAILING
   compile (Lean elaborates past errors).
The r6 log held the proof: 5 real errors + 4 sorryAx-infected decls in
PiCollapse406.lean.  The S084 "slim certified" claim is RETRACTED.

## C. THE FIVE DEFECTS (the repair, all four 406 kernel files)

| # | Site | Defect | Fix |
|---|---|---|---|
| A | hcube block | dead `simp only` + `try ring` after the rw auto-closed (rfl) | deleted |
| B | h2 pow_add | `rw [← Nat.pow_add]` pattern miss (parenthesized product ≠ pow*pow) | the K73 GREEN VERBATIM route: `hsplit` (congr 1; omega) + witness `rw [hsplit]; ring` |
| C | hsum obtain | `obtain ⟨q, rfl⟩` subst trap (non-variable equality) | the K73 GREEN route: `add_mod_of_dvd` peeling (hd2 then hd1) |
| D | hgd3 | `rw [hcancel]; ring` — rw auto-closed, ring dead | `⟨e, hcancel.symm⟩` |
| E | hmul calc | the rw-hu LOOP trap (hu's RHS contains u; rewrites inside `u - u'` diverge) | compound rewrite `hsplit : u' + (u - u') = u` |

The sorryAx cascade (lteCoeff_stable, ghost_residue_shape,
ghost_congruence, ghost_congruent_all_depths) dissolves with its
sources.  ghost_head_not_three was already clean.

## D. THE MONOLITH VENDOR (the fabrication fix)

`Monolith/` = the 39-file mission closure (GSTTailFFourthDimension +
Ω-wave + boundary + six-adic + telescope + u-jump + navigation + no22 +
tactic + CardinalWorlds), 53 import rewrites, `lean_lib Monolith`.
Toolchain EXACT (v4.33.0-rc2 both sides).  CI job `kernel-monolith`
(the first exposure, REAL gates).  Next round: the kernels import and
cite the Monolith theorems directly (the serial-build law).

## E. THE JOB SPLITS

kernel-406b (control+74) / 406d (74b) / 406e (75) / 406f (76) — fresh
runners, minute-zero compiles, REAL gates everywhere
(RC=PIPESTATUS[0] + grep-exit negative gates).  Batteries preserved
(406f/g/h per job).

## F. THE HONEST BOARD

The two primitives stand as the named remaining content (row + tower),
the terminal identity's proof lives in erdosternary2 @
sol/kyo-gate-universe-wire (cb29501) — the vendor of that branch is the
named next strike, together with the kernel citations of the Monolith.

The engine never stops; it never lies.
