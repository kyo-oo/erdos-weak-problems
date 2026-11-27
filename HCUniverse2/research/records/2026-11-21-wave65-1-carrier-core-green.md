# Wave 65.1 — THE CARRIER CORE GREEN: the six-defect repair of `GSTFiniteLineWorldCarrier`

Date: 2026-11-21. Author: the wave-65.1 round (the recon-and-repair round that
opened with the dead session's two failed runs on the table).

## The state at entry (live-verified this round)

* Branch `research/gpt6-gst-hypothesis-part1-chow-square-20261110`, pushed HEAD
  `2e64aa9` (the ARK auto-vault of wave 65's `f825795`).
* The carrier lane `gst-finite-line-world-carrier.yml` had FAILED twice:
  run `44889957020` (at `f825795`) and run `44896233358` (at `2e64aa9`) —
  the prior session died mid-adjudication, leaving wave 65's module wounded on
  the battlefield with its repair drafts staged (`repairs/wave65_1_A..D.lean`)
  but never designed.
* The full failure log (artifact 14704122110) yielded the exact six-defect
  ledger (below); the `sorryAx` in the three headline receipts was diagnosed
  as Lean's error-recovery sorries cascading from the defect sites (NOT real
  sorries — the module text has none).

## THE KILL OF THIS WAVE — the six defects, their root causes, the repairs

1. **The two quotient-roundtrip `ext`-shows (lines 333, 355).** Root cause:
   `ext t` on the polynomial-source AlgHom equality fires the MvPolynomial
   GENERATOR ext — the actual goal is `f (X t) = g (X t)` with
   `t : Fin (2 * M)`, not `f t = g t` with a polynomial `t`. The original shows
   spelled a general polynomial and died at defeq. Repair: the shows now carry
   `X t` and close through `renameEquiv_apply` + `rename_X` + `Equiv.apply_symm_apply`
   (resp. `Equiv.symm_apply_apply`) — every lemma pin-verified green in this
   very build (`rename_X` at the original line 216, `renameEquiv_apply` at 209,
   the Equiv lemmas in eight CI-green corpus files).
2. **`lineFinEquiv`'s Bijective-constructor (line 567) + the surplus bracket
   (line 570).** Root cause: `Fin.val_injective (congrArg Fin.val h)` — the
   elaborator unified `congrArg`'s equality type backwards from
   `Fin.val_injective`'s conclusion (a = b), so `h` was expected at type
   `a = b` instead of its actual `embed a = embed b`; and the anonymous
   constructor nested one bracket too deep, breaking the parser and cascading
   into the `Invalid end` pair at 679/681. Repair: the whole equiv rebuilt in
   `where`-syntax — `toFun`/`invFun` as bare constructor pairs (the original
   proofs kept verbatim — they had elaborated green), `left_inv`/`right_inv`
   closed by `apply Fin.ext; rfl` (iota on the constructor pairs).
3. **`ambientQuotient_surjective`'s show (line 602).** Root cause: `z` was
   eliminated by the `obtain ⟨t, rfl⟩` substitution — the show still named it.
   Repair: `z` → `lineQuotientMap M t` (the substituted form). The rest of the
   proof — the double-`show` + `rename_rename, Equiv.self_comp_symm,
   rename_id_apply` chain — was ALREADY pin-verified green (the mirror bullet
   at the original lines 637–642 elaborated clean in the failed run).
4. **`line_irrelevant_le`'s `mem_irrelevant_of_mem` call (line 634).** Root
   cause: the pin's signature takes the grading family as an EXPLICIT FIRST
   argument — `(𝒜) (h : 0 < i) (h' : x ∈ 𝒜 i)` — as transcribed from the
   CI-green finite-point carrier (`mem_irrelevant_of_mem grading zero_lt_one
   (...)`). The original two-argument call put `hi` in the grading slot and
   the membership proof in the `0 < i` slot. Repair: the explicit grading
   argument `(ProjectiveGrading (2 * M - 1))` inserted.
5. **The stray `end` pair (lines 679/681).** The parse break at 570 cost the
   scope tracker its balance; the file carried a duplicated `end` pair. Repair:
   deleted (the module ends with the namespace close + the section close, in
   the correct order).
6. **The error-recovery `sorryAx` receipts.** Cascade artifacts of (1)–(5):
   `lineRotateHom_bijective` consumed the two wounded roundtrips, so
   `lineRotateGraded_surjective` → `lineRotate_irrelevant_le` →
   `finiteLineCycle` (resp. `ambientQuotient_surjective` →
   `line_irrelevant_le` → `finiteLineEmbedding`) all inherited the recovery
   sorries. With (1)–(5) repaired the receipts clean themselves.

## THE VERDICT

* **Run `44899187702` at `99f6366` — GREEN** (completed successfully):
  `LEAN PASSED: the finite-line world carrier module`; zero errors; the
  sorryAx gate silent; the three headline receipts
  `finiteLineCycle` / `finiteLineCycle_isIso` / `finiteLineEmbedding`
  depend only on `[propext, Classical.choice, Quot.sound]`.
* One push, one green run — the six-defect repair landed in a single
  adjudication round.

## What this certifies (unchanged statements, all now kernel-checked)

* `finiteLineScheme M := Proj (lineGrading M)` with its structure map
  `finiteLineStructureMap M` to `Spec(ℂ)`;
* **THE M-CYCLE AUTOMORPHISM** `finiteLineCycle M` — an isomorphism whose
  graded M-th power is the identity (`lineRotateGraded_pow`) — the geometric
  input of the wave-64 cyclic word's realization gate;
* the closed-embedding presentation `finiteLineEmbedding M` into
  `ℙ^{2M-1}` (its closed-immersion CERTIFICATION remains the next wave's
  chartwise battle, per the frozen Route-A order).

## The verification battery (re-run live this round, two-method law)

* The owner's twelve-cell certificate: `det[Krylov] = −1,149,656,584,000`,
  Fraction-Gauss + Bareiss exact agreement (`battery.py`).
* The M-cycle certificate at every M 1..24: det = 1, orbit rank M/M, weight-0
  machine rank M/M (`mcycle.py`) — ALL CHECKS PASS.

## What remains (the frozen order, unchanged)

1. **F2**: the closed-immersion certification of `finiteLineEmbedding`
   (chartwise `IsZariskiLocalAtTarget.of_iSup_eq_top`, transposed from the
   green finite-point carrier's five-stage cancel cascade — new design
   needed: the finite-line embedding is `Proj.map` of a graded quotient, not
   `fromOfGlobalSections`).
2. **F3**: smoothness + projectivity → the `finiteLineWorld M :
   SmoothProjectiveComplexScheme` package.
3. The ℂ-points classification + the analytification receipt + the gate
   discharges (letters as graphs of `finiteLineCycle`, seeds as the honest
   point/component cycles) → the law landing composes with the wave-64
   general-M cyclic word and the wave-60 law module.
4. The ω-core (liveness-only) — the campaign's fenced frontier.

## Audit trail

* Every repair lemma spelling pin-verified against evidence from the failed
  run's own log (the green-elaborated line numbers above) — no unverified
  lemma name entered the module this round except `AlgHom.comp_id` /
  `AlgHom.id_comp` (lines 342/364, unreached in the failed run; standard
  Mathlib names; validated by this round's green run).
* Static battery: zero sorry/admit/native_decide; brackets balanced
  (28⟨/28⟩, 547(/547)); no superscript identifiers; receipts unchanged.
* The staged repair drafts (`repairs/wave65_1_A..D.lean`) are superseded by
  this round's in-place repair (kept as history).
