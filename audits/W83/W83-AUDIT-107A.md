# W83-AUDIT-107A — Regression audit of DM107_Proof_A (Erdős #107, official `nonempty_cardSet`)

**Target:** `problem107-happy-ending/DM107_Proof_A.lean` (1515 lines, HEAD = 9a29c0e4, branch `campaign`, clean tree)
**Prior green:** CI run 44968437049, job 137042629607, commit 1fc89c1 (recorded in commit 9da5243:
`'Erdos107.nonempty_cardSet' depends on axioms [propext, Classical.choice, Quot.sound]`, no sorryAx).
**Auditor:** W83 adversarial auditor, static analysis only (no local Lean, per campaign law).

---

## VERDICT: **GREEN-EXPECT** (for the Kernel 107DM-A step and its receipts)

Regression risk is **LOW**. The kernel and every one of its compile inputs are **byte-identical**
to the commit that went green; the only change in the cone is a CI-workflow reorganization that
preserved the 107DM-A step verbatim and moved it to the **first** step of the merged `kernel-dm-w82`
job. Lean compilation is deterministic given identical sources + toolchain + pinned Mathlib, so
the step must reproduce the green result.

---

## 1. Git-diff evidence (the core of the verdict)

| Path (compile cone) | `git diff 1fc89c1 HEAD` | Meaning |
|---|---|---|
| `problem107-happy-ending/DM107_Proof_A.lean` | **EMPTY** | kernel byte-identical to the green run |
| `FC/` (entire vendor pack incl. `FC/Geometry/TwoD.lean`, `FC/Data/Set/Triplewise.lean`, `FC/Combinatorics/AP/Basic.lean`) | **EMPTY** | all vendored official defs unchanged |
| `Arsenal/` (entire) | **EMPTY** | `ErdosTernary2.Basic`, `CardinalWorlds` unchanged |
| `lakefile*`, `lean-toolchain`, `lake-manifest.json` | **EMPTY** | same toolchain v4.33.0-rc2, same pinned Mathlib |

The only change in the whole repo between 1fc89c1 and HEAD that touches the CI path of this
kernel is `.github/workflows/kills.yml` (+80/−1), analyzed in §3. Changes under
`problem107-happy-ending/` are **additions only** (`DM107_Proof_B.lean`, worklogs, an audit md) —
none is imported by Proof_A.

## 2. Kernel receipts and hygiene

* Line 1509: `#eval "DM107A_NONEMPTY_CARDSET_GREEN"` — feeds `grep -F "DM107A_NONEMPTY_CARDSET_GREEN"`. ✔
* Line 1512: `#print axioms Erdos107.nonempty_cardSet` — at 1fc89c1 this printed
  `'Erdos107.nonempty_cardSet' depends on axioms [propext, Classical.choice, Quot.sound]`,
  which matches the job's `grep -E "'Erdos107.nonempty_cardSet' (does not depend on any axioms|depends on axioms)"`. ✔
* Zero `sorry` / `admit` in proof position (only occurrence is the header docstring, line 58). ✔
* Zero `native_decide`, zero `axiom`/`opaque`/`unsafe`/`extern`/`partial def` declarations. ✔
* Statement at line 1504 is byte-identical to the official target spec
  (`DM107_Official.lean:57`): `theorem nonempty_cardSet : ∀ n ≥ 3, (cardSet n).Nonempty`. ✔
* In-kernel `cardSet` (82–83) and `f` (86–87) are byte-identical to `DM107_Official.lean:42–47`. ✔
* Arsenal citations verified at source: `lt_three_cases` (Arsenal/ErdosTernary2/Basic.lean:16),
  `two_pow_pos` (:420), `two_pow_factored` (:425), `two_pow_ge2` (:431);
  `two_pow_ge_succ` is proved in-kernel (line 1458) — no unresolved identifiers. ✔

## 3. CI wiring (`.github/workflows/kills.yml`, current HEAD)

The job was renamed `kernel-107dm-a` → `kernel-dm-w82` (commit 9a29c0e, the null-job-key repair
that had zero jobs starting since run 44967816376). Verified at HEAD:

* **The "Kernel 107DM-A" step body is unchanged** from the green run (same
  `lake build FC` → `lake build Arsenal.ErdosTernary2.Basic` → `lake build Arsenal.CardinalWorlds`
  → `lake env lean problem107-happy-ending/DM107_Proof_A.lean` pipeline, same negative grep
  `! grep -E 'error:|sorryAx|unknown identifier|unsolved goals|declaration uses .sorry.'`,
  same two receipt greps, same `echo KERNEL_107DM_A_GREEN=1`).
* It is **step 0 of the kernel steps** (runs before 61DM-A/61DM-B/142DM-A/142DM-B), so no sibling
  step can interfere with it.
* Workflow YAML machine-validated: 19 jobs, **zero null job keys**, every step has `run`/`uses`.
  The class of board-killing defect fixed in 9a29c0e is not present.

## 4. Risk notes (NOT defects of the target)

* **R1 — job-level coupling.** `kernel-dm-w82`'s overall green now also requires the four sibling
  steps (61DM-A, 61DM-B, 142DM-A, 142DM-B) appended after 107DM-A. Commit 015c1ab records
  DM142_Proof_B as "awaits its CI verdict", so the 142DM-B step has the weakest prior evidence.
  If a sibling step fails, the **job** is red overall even though the 107DM-A step passes and its
  log contains `KERNEL_107DM_A_GREEN=1`. This is a board-readability risk, not a 107A regression.
* **R2 — no confirmed run on HEAD.** Between 6da275b and 9a29c0e the workflow was rejected
  wholesale; whether a completed run exists on 9a29c0e could not be checked from this sandbox
  (no `gh` CLI). Static determinism (§1) covers this: identical inputs → identical output.
* Cosmetic only: the grep alternative `depends on axioms` would also match a sorryAx leak if the
  negative grep were ever removed — but the negative grep runs first in the same `set -euo pipefail`
  block, so the pipeline is sound.

## 5. MATH-FIDELITY

**Does `nonempty_cardSet` as stated actually follow, over the vendored official defs, without
hidden hypotheses or vacuity? YES.**

1. **Official packaging.** `cardSet n = {N | ∀ pts : Finset ℝ², pts.card = N → NonTrilinear ↑pts → HasConvexNGon n pts}`
   (kernel 82–83 = `DM107_Official.lean:42–43` verbatim), over the vendored official
   `NonTrilinear` (FC/Geometry/TwoD.lean:66–67), `ConvexIndep` (:83–84),
   `HasConvexNGon` (:88–89) — the DeepMind formal-conjectures definitions @ 2207c54d.
2. **Definitional bridge is sound.** `nonTrilinear_iff … := Iff.rfl` (kernel 162–165) holds by
   definitional unfolding: `Set.Triplewise` (FC/Data/Set/Triplewise.lean:41–42) *is* the
   six-binder ∀-statement used by the port. No content is smuggled.
3. **The proof is the real ES-1935 chain** (the `formal_proof using lean4` cited upstream,
   linrock @ cd3cf0b1): witness `N = erdosSzekeresUpper n = C(2n−4, n−2) + 1` (565–566);
   membership `erdosSzekeresUpper_mem_cardSet` (1395–1398) is the genuine *universal* statement
   over **all** N-point NonTrilinear Finsets; the unconditional form
   `hasConvexNGon_of_nonTrilinear_and_card_ge` (1369–1391) drops the x-distinctness hypothesis
   via an honest perturbation (`goodShearSlope` 1270 avoids finitely many forbidden slopes,
   `nonTrilinear_image_shearPt` 1193, `hasConvexNGon_image_shearPt_iff` 1231 transports both ways
   through the inverse shear); the x-sorted bridge `hasConvexNGon_of_x_injOn_and_nonTrilinear`
   (1127) feeds `erdos_szekeres_cup_cap_theorem_on` (519–522), the exact ES-1935
   Pascal-splitting statement (`C(m+k,m)+1 ≤ |S| → cup m ∨ cap k` on x-monotone sequences).
4. **No vacuity.** The hypothesis `NonTrilinear` is satisfiable (e.g. points on a parabola), so
   membership in `cardSet n` is not a vacuous universal; and `HasConvexNGon n pts` demands an
   n-point `ConvexIndep` subset — nontrivial (it fails, e.g., for 4 points with one inside the
   hull of the other three). `ConvexIndep` (all points extremal) is the standard
   "convex position" characterization, so the official reading of "contains a convex n-gon" is
   faithfully captured.
5. **Honest strength.** The kill `nonempty_cardSet_all` (1492–1498) additionally proves the
   n<3 cases (via `self_mem_cardSet_of_le_three` 1346 / `convexIndep_of_card_le_two` 1300) —
   extra strength beyond the official `∀ n ≥ 3` target, harmless. The open core
   (`f n = 2^(n−2)+1`) is not claimed anywhere in this kernel, as the official decomposition
   requires.
6. **Axiom profile.** propext, Classical.choice, Quot.sound only (per the green-run record);
   no `sorryAx`, no custom `axiom` (grep-verified), so the kernel is a complete classical proof.

## 6. Defects found

**None.** No compile-breaking change, no receipt mismatch, no sorry/native_decide/axiom leak,
no math-fidelity gap. No repair patches needed.

---

### Bottom line

The 107DM-A step of `kernel-dm-w82` will compile and print
`DM107A_NONEMPTY_CARDSET_GREEN` + `'Erdos107.nonempty_cardSet' depends on axioms …` +
`KERNEL_107DM_A_GREEN=1` exactly as it did on run 44968437049 — its inputs are byte-identical.
Watch the four sibling steps (esp. 142DM-B) for job-level reds that do not implicate 107A.
