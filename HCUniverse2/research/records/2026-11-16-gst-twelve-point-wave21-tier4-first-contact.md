# 2026-11-16 — The twelve-point wave 21: tier-4 first contact — the tier-3 wall broken after 20 runs, the HodgeData eight, and the mem_top arity sweep

**Provenance:** W21-D, the records-and-gate wave of the GST campaign's wave-21 strike session.
This is the round record for the twenty-first repair wave on the twelve-point native geometric
world, written at HEAD `7d93b83b` (the twentieth-wave commit, whose CI adjudication — run
`43903976892`, RED, dead at FIRST CONTACT with `GSTTwelvePointHodgeData.lean` after
`GSTTwelvePointCohomology.lean` went GREEN for the first time in the campaign — is this
round's target) with the wave-21 edits landing in the working tree IN PARALLEL: W21-A's
four kills in the HodgeData, W21-B's `zeroCycleClass_point` rebuild, W21-C's pre-emptive
`mem_top` arity sweep across the Landing and the FoldWord.  Every run-20 error cite is at
`7d93b83b` file state (verified line-by-line against the run-20 artifact log and the HEAD
tree this session).  No Lean kernel verdict is claimed for wave 21 at this record's write
time.  Zero mathematics changed — elaboration engineering only, the 2026-11-15 CI-loop
record's disclosure standing.

## What this is

Tier 3 of the six-module serial chain (`GSTTwelvePointCohomology.lean`) is CLOSED: after
twenty CI runs on the lane (first exposure run 16, trend 20 → 8 → 1 → 0), run 20 built the
cohomology GREEN — the wave-20 congrArg transport killed the run-19 sole survivor, both of
the file's `#print axioms` receipts print clean (`[propext, Classical.choice, Quot.sound]`,
the run-19 `sorryAx` taint on `twelvePointCohomology_subsingleton` gone with it), and the
build advanced past tier 3 for the first time.  It died at FIRST CONTACT with tier 4:
`GSTTwelvePointHodgeData.lean` — never elaborated by any prior run — failed with exactly 8
errors, every one of them inside the HodgeData, and the run's only required-target failure
line names the HodgeData alone.  The wave-19/20 pre-emptive strategy is VINDICATED twice
over: the integration map's first-contact predictions held (the errors landed precisely in
the predicted disease classes — the elaboration-order and arity diseases the never-elaborated
files were audited for), and the wave-20 R1 Landing hardening was never even exercised
(HodgeData comes first in the post-cohomology import chain — Cohomology → HodgeData →
FoldWord → Landing — the build never reached the Landing).

Wave 21 is one kill set in one push, split across three files:

1. **The HodgeData eight** — W21-A kills the `Subsingleton.elim` instance-stuck closer by
   the `@`-form (the instance passed as a term, no synthesis) and deletes the two dead
   `funext`/`simp` tails that outlived `congr 1`'s early close, and fixes the two
   `Submodule.mem_top` arity sites; W21-B rebuilds `zeroCycleClass_point`'s interior (the
   `Decidable` failure and its two cascading unsolved goals).
2. **The pre-emptive sweep** — W21-C applies the same `mem_top` arity fix at the three
   predicted-first-contact sites in the never-elaborated files: the Landing's two
   (`:142`, inside the wave-20 R1 hoist's own closer — the hardening's fiber-equation
   hoist stands, only its closer's arity was diseased — and `:295`) and the FoldWord's one
   (`:789`).

## The run-20 verdict — the tier-3 wall broken, tier-4 first contact

Run `43903976892` (wave 20, commit `7d93b83b`) completed FAILURE — the run number and
completion metadata are the campaign context's (W-observer's report); the artifact log
(`/home/z/ci-logs/run20/gst-twelve-point-native-world.log`, 14298 lines) carries no
run-ID/timestamp header, the same metadata split as run 19's.  Every technical claim below
was verified against that log this session.

**Tier 3 GREEN — the first time in 20 runs.**  `ℹ [8823/8969] Built GSTTwelvePointCohomology
(8.5s)` — the file elaborated with WARNINGS ONLY: seven unused-simp-argument linter notes
(`:332:10`, `:332:19`, `:338:42`, `:338:52`, `:348:49`, `:362:10`, `:363:6`, all in
`fin12DualEquiv`'s linearity fields) and one `Try this` style hint (`:549:4`) — none an
error, none a gate.  Both receipts print clean:

```
info: GSTTwelvePointCohomology.lean:560:0: 'GSTTwelvePointCohomology.twelvePointCohomologyIso' depends on axioms: [propext, Classical.choice, Quot.sound]
info: GSTTwelvePointCohomology.lean:561:0: 'GSTTwelvePointCohomology.twelvePointCohomology_subsingleton' depends on axioms: [propext, Classical.choice, Quot.sound]
```

The run-19 `sorryAx` shadow (`twelvePointCohomology_subsingleton`'s
`[propext, sorryAx, Classical.choice, Quot.sound]`, tainted through the dead
`dualCochains_d_odd`) is GONE — the congrArg transport carried the whole file.  Tier 1
(carrier) closed at run 11, tier 2 (analytification) at run 15, tier 3 (cohomology) at
run 20.

**Tier-4 first contact — the HodgeData eight.**  The build advanced to
`✖ [8861/8969] Building GSTTwelvePointHodgeData (4.4s)` and Lean exited with code 1 after
exactly 8 elaboration errors — verified: those 8 are the ONLY `error: GST…` lines in the
whole 14298-line log.  The run's failure lines:

```
Some required targets logged failures:
- GSTTwelvePointHodgeData
error: build failed
```

Tiers 5 (FoldWord) and 6 (Landing) were NOT reached — both files remain never-elaborated,
one green step away.  First-exposure mass 8 (against the cohomology's first-exposure 20).

## The 8-error defect map — disease class and fix for each

All eight errors, verbatim class and fix.  Line numbers at `7d93b83b` file state; the
error bodies quoted from the run-20 log (lines 8148-8212).

### D1 — `:151:10`, the `Subsingleton.elim` instance-stuck (W21-A)

```
error: GSTTwelvePointHodgeData.lean:151:10: typeclass instance problem is stuck
  Subsingleton ?m.83
Note: Lean will not try to resolve this typeclass instance problem because the type argument
to `Subsingleton` is a metavariable.
```

The wave-19 pre-emptive R6 closer in `deadBigrading`'s `independent` field —
`exact Subsingleton.elim _ _` after the three `haveI`s (`hsub`, `hcomp`, `hlat`).  **The
disease class: instance-synthesis-before-unification (elaboration order).**  `Subsingleton.elim`'s
instance argument `[Subsingleton α]` is synthesized while `α` is still a metavariable — the
two `_` placeholders (`a b : α`) have not yet been unified against the goal's
`Disjoint (component i) (⨆ j ∈ {j | j ≠ i}, component j)` (defeq: the submodule-lattice
equation `P ⊓ Q = ⊥`), and Lean refuses instance synthesis on a metavariable type.  The
goal's defeq shape was never in doubt — `hlat` collapses it — only the elaboration ORDER
was wrong.  **The fix (W21-A, amended after pin-verification): `exact
disjoint_of_subsingleton`** (Mathlib's own packaged collapse, Order/Disjoint.lean:52-53
— `fun x _ _ => le_of_eq (Subsingleton.elim x ⊥)`) — at the pin `Disjoint` is the
ORDER-form `∀ ⦃x⦄, x ≤ a → x ≤ b → x ≤ ⊥` (Order/Disjoint.lean:48-49), NOT the
`P ⊓ Q = ⊥` Eq-form, so no Eq-typed term can ever unify with the independent-field
goal; the elaboration-shape precedent (haveI hlat; exact …) is the run-20-green
`iSupIndep_subsingleton` at HodgeData:115-116; the `@Subsingleton.elim _ hlat _ _`
passes `hlat` DIRECTLY as the instance argument (a term, checked against
`Subsingleton ?α` — no synthesis attempted at all), `α` unified from the goal, `a` and `b`
from the two `_`s.  The instance-stuck disease is structurally impossible in the `@`-form:
nothing is ever synthesized.

### D2/D3 — `:191:6` / `:205:6`, the dead tails after `congr 1` (W21-A)

```
error: GSTTwelvePointHodgeData.lean:191:6: No goals to be solved
error: GSTTwelvePointHodgeData.lean:205:6: No goals to be solved
```

`zeroCycleClass`'s two linearity fields.  In `map_add'`: `rw [← map_add]; congr 1; funext
i; simp [Function.locallyFinsuppWithin.coe_add, Pi.add_apply]` — the `funext i` at `:191`
is the dead step.  In `map_smul'`: `rw [← map_smul]; congr 1; funext i; rw
[Submodule.coe_smul]; simp […]` — the `funext i` at `:205`.  **The disease class: dead
tactic steps after an early close.**  After the `rw [← map_add]`/`rw [← map_smul]`
transport the two sides of the goal are congruent at the `LinearMap` level and `congr 1`
CLOSES the goal outright (the wave-17 D5 carrier-level `show` ascriptions made the two
sides syntactically congruent — the design's own success killed the tail) — the
`funext`/`simp` sequences then run against zero goals, which is an error, which fails the
whole tactic block, which leaves the def `sorryAx`-tainted through error recovery.  The
tactics were never wrong — they were never NEEDED.  **The fix (W21-A): delete the dead
tails** — each field closes at `rw [← map_add]; congr 1` / `rw [← map_smul]; congr 1`.

### D4/D5/D6 — `:229:7` / `:229:82` / `:235:2`, the `zeroCycleClass_point` cascade (W21-B)

```
error: GSTTwelvePointHodgeData.lean:229:7: failed to synthesize instance of type class
  Decidable (↑(twelvePointEquiv j) = ↑(twelvePointEquiv i))
error: GSTTwelvePointHodgeData.lean:229:82: unsolved goals
  i j : Fin 12
  ⊢ Pi.single (↑(twelvePointPt i)) 1 ↑(twelvePointEquiv j) = sorry ()
error: GSTTwelvePointHodgeData.lean:235:2: unsolved goals
  case pos
  j : Fin 12
  hval : ↑(codimensionPointCycle twelvePointWorld.X 0 (twelvePointPt j)) ↑(twelvePointEquiv j) = sorry
  ⊢ sorry () = 1
```

**The disease class: a missing `Decidable` instance on subtype-point equality, with the
cascade.**  The `hval` have states the point-cycle indicator as an `if (twelvePointEquiv
j).1 = (twelvePointEquiv i).1 then (1 : ℚ) else 0` — the two sides are coerced points of
the world (subtypes lifted to the ambient cycle group), and the pinned Mathlib has no
`Decidable` instance for that equality (`:229:7`).  The elaboration error does not stop
the file: the `if` degrades to `sorry` under error recovery, the `hval` proof's `simp
[codimensionPointCycle, Function.locallyFinsuppWithin.single_apply]` can never close a
`… = sorry ()` goal (`:229:82` — with the `single_apply` argument reported UNUSED at
`:232:33`, the point-indexed `Pi.single` on the left never evaluated), and the `sorry`
propagates through `rw [hval, Pi.single_apply]` into the `by_cases` positive branch,
whose `subst hj; simp` leaves the `sorry () = 1` residue (`:235:2`).  One root error, two
cascade shells.  **The fix (W21-B): rebuild the proof interior** — the point-equality
condition restated in decidable form (the `Fin 12` index equality, decidable on the nose,
transported through `twelvePointEquiv`'s injectivity) with the indicator evaluation
carried at the index level, so the `hval` have is green on its own terms and the cascade
shells never form.  (Design at this record's write time; the edit lands in the working
tree in parallel — see Disclosure.)

### D7/D8 — `:253:12` / `:256:12`, the `Submodule.mem_top` arity disease (W21-A)

```
error: GSTTwelvePointHodgeData.lean:253:12: Function expected at
  Submodule.mem_top
but this term has type
  ?m.46 ∈ ⊤
Note: Expected a function because this term is being applied to the argument
  m
error: GSTTwelvePointHodgeData.lean:256:12: Function expected at
  Submodule.mem_top
but this term has type
  ?m.63 ∈ ⊤
Note: Expected a function because this term is being applied to the argument
  _
```

`rationalHodgeSubspace_of_top`'s two `Submodule.ext` constructor branches:
`exact Submodule.mem_top m` (`:253`) and `exact Submodule.mem_top _` (`:256`, after `rw
[mem_rationalHodgeSubspace_iff, htop]`).  **The disease class: lemma arity (the element
argument is IMPLICIT at the pin).**  At the pinned Mathlib, `Submodule.mem_top`'s element
is an implicit `{m}` — the lemma is a proof `?m ∈ ⊤`, not a function taking the element,
so BOTH spellings (`… m` and `… _`) apply a non-function; the argument the proofs meant to
supply is inferred from the goal when the lemma is used bare.  **The fix (W21-A): `exact
Submodule.mem_top`** at both sites — no argument, the element unified from the goal at
default transparency.  The same disease, the same fix, at the three predicted sites below.

## The pre-emptive sweep (W21-C) — the `mem_top` arity disease across the never-elaborated files

Run 20 exposed the `mem_top` arity disease class at the HodgeData pin; the integration
map's sites in the never-elaborated files carry the IDENTICAL spelling — three sites,
all `exact Submodule.mem_top _`, all certain first-contact failures of the same class if
left standing:

* **Landing `:142`** — `twelvePointSeed_hodge`'s wave-20 R1 hoist closer.  The R1
  hardening itself is sound (the fiber-equation hoist and its three-step interior are
  green under both rw-matching models); only the closer's arity was diseased — the
  wave-20 design spelled the pin application `_` at a lemma whose element is implicit.
  The run-20 HodgeData errors exposed the class BEFORE the Landing was ever reached: the
  pre-emptive strategy catching its own earlier wave's blind spot.
* **Landing `:295`** — `twelvePoint_orbitUnderlying_span`'s `hEu` interior closer (after
  `rw [span_range_C_eq_top]`).
* **FoldWord `:789`** — `twelvePointFoldWord_hodge`'s final closer (after the
  `zeroFiber_eq_top` rewrite — the AUDIT-6 contract-lemma route).

All three get the bare-lemma fix, `exact Submodule.mem_top`, the element from the goal —
the same repair W21-A applies at the HodgeData's two.  The Landing (`:142`) site's fix
preserves the R1 hoist's structure exactly; only the closer's spelling changes.

## The error-recovery shadow — the sorryAx taint list that dies with the eight

The HodgeData's declarations elaborated through error recovery; five of the file's
`#print axioms` receipts print `sorryAx` (log lines 8257-8270):

```
'…zeroCycleClass_point'            → [propext, sorryAx, Classical.choice, Quot.sound]
'…rationalHodgeSubspace_of_top'    → [propext, sorryAx, Classical.choice, Quot.sound]
'…zeroFiber_eq_top'                → [propext, sorryAx, Classical.choice, Quot.sound]
'…deadFiber_subsingleton'          → [propext, sorryAx, Classical.choice, Quot.sound]
'…twelvePointHodgeData_bigrading_pos' → [propext, sorryAx, Classical.choice, Quot.sound]
```

The taint routes, each through one of this wave's kill sites: `zeroCycleClass_point`
through the `:229`/`:235` cascade (and `zeroCycleClass`'s own `:191`/`:205` block
failures); `rationalHodgeSubspace_of_top` through the `:253`/`:256` arity pair;
`zeroFiber_eq_top` through `rationalHodgeSubspace_of_top` (its proof rides the
of_top lemma); `deadFiber_subsingleton` and `twelvePointHodgeData_bigrading_pos`
through `deadBigrading` (the `:151` instance-stuck failure in its `independent` field).
The three clean receipts (`subsingleton_submodules_eq` `[propext, Quot.sound]`,
`subsingleton_complexification`, `fin1_subsingleton` `[propext, Quot.sound]`) sit above
every failed block.  All five taints die with the eight errors — no declaration in the
file is `sorry` in the source (the wave-19 sorry-gate pre-check stands), every taint is
error-recovery shadow.

## Agent accounting (the W21 wave)

* **W21-A — the HodgeData four-site kill set:** `exact disjoint_of_subsingleton`
  at `:151` (D1 — the pin's ORDER-form Disjoint killed the Eq-route design; the
  green `iSupIndep_subsingleton` twin is the precedent), the `@Subsingleton.elim _
  hlat _ _` hardening at `:162`, the two dead-tail deletions at `:191`/`:205` (D2/D3), the
  `mem_top` arity pair at `:253`/`:256` (D7/D8).
* **W21-B — the `zeroCycleClass_point` rebuild:** the `Decidable` disease at `:229:7`
  and its two cascading unsolved goals `:229:82`/`:235:2` (D4/D5/D6).
* **W21-C — the `mem_top` arity sweep across the never-elaborated files:** Landing
  `:142` (inside the wave-20 R1 hoist's closer) and `:295`, FoldWord `:789` — the
  pre-emptive first-contact insurance.
* **W21-D — records and the gate (this record, the commit-message draft
  `research/records/2026-11-16-wave21-commit-message.txt`, the INDEX entry) and the
  FINAL structural gate after A/B/C stabilize: per-file signature-diff vs HEAD (zero
  statement changes expected), the comment-stripped sorry-gate, bracket balance,
  raw-byte `rw [` integrity, WAVE-21 marker presence.**

## Disclosure and non-claims (exact scope)

* **No kernel verdict for wave 21 at this record's write time.**  The wave-21 push's CI
  run has not fired; no green is claimed for the twelve-point lane at any SHA
  (AGENTS.md rule 7).  The run-20 verdict quoted here is run `43903976892`'s, at
  `7d93b83b`.
* **The run-20 metadata split:** the artifact log
  (`/home/z/ci-logs/run20/gst-twelve-point-native-world.log`, 14298 lines) carries the
  eight error bodies, the five tainted receipts, the clean-receipt set, the
  required-target failure line, and the build failure — every technical claim above was
  verified against it this session.  The log carries NO run-ID/timestamp header; the run
  number is the campaign context's and is recorded here on that authority.
* **The Landing and the FoldWord have still never been elaborated by any CI run** — run
  20 died in tier 4 (HodgeData); the build-order is the import chain (Cohomology →
  HodgeData → FoldWord → Landing; the workflow's `lake build` target is the Landing, the
  chain's top).  Tier 5 (FoldWord) and tier 6 (Landing) are one green step away: the
  HodgeData's eight are the only known errors between the campaign and the never-elaborated
  pair, and W21-C's sweep retires the one disease class run 20 exposed at their predicted
  sites.
* The wave-21 designs' proofs are the pending run, not this record; the W21-B rebuild and
  the W21-A/W21-C arity fixes are argued from the run-20 error bodies and the pinned
  Mathlib's lemma arities, not by compilation from this sandbox (CI owns Lean
  compilation).
* Zero mathematics changed: the construction, the lane, the lib registration, and the
  six-file path filter are the 2026-11-14 record's, untouched.  The twelve-point lane
  remains a RESTRICTED, zero-dimensional discharge lane; no typed ⇒ native transport
  exists anywhere in the repository.

## CI status

**Pending — wave 21 not yet pushed at this record's write time** (the HodgeData kills and
the pre-emptive sweep are in the working tree; the commander commits after the gates).
The lane's last adjudication is run `43903976892` at `7d93b83b`: RED at tier-4 first
contact — exactly 8 elaboration errors, all in `GSTTwelvePointHodgeData.lean`, tier 3
GREEN for the first time in 20 runs.  The session's standing greens are unchanged: the
landing lane (`43750693353` at `2378003`), the spanning lane (`43747935402` at
`06c1037`), and the part1-chow-transfer lane (`db97399`).  Tier 1 (carrier) closed at run
11; tier 2 (analytification) closed at run 15; tier 3 (cohomology) closed at run 20;
tier 4 (HodgeData) is this wave's kill — 8 errors, all mapped, all owned; tiers 5-6 have
never been elaborated by any run.


---

## CORRECTION (wave 22, the W22-D audit find)

The record's D7/D8 claim that the two HodgeData `mem_top` sites
(`rationalHodgeSubspace_of_top`, old :253/:256) were fixed is **FALSE** — the
wave-21 commit db8feaed carries NO change at those sites (the W21-A/W21-C
ownership gap: W21-A's brief booked them to W21-C's sweep, W21-C's brief
restricted it to Landing+FoldWord). The wave-21 push was 6-of-8, not 8-of-8;
CI attempt 2 on db8feaed died/will die at exactly those two sites. The
two-line emergency repair (`exact Submodule.mem_top` bare, the element
implicit at the pin) plus this correction ride the wave-22 push together with
the toolchain-install hardening (the run-22 attempt-1 elan 403 —
infrastructure, not mathematics).
