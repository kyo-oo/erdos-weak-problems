# 2026-11-16 — The twelve-point wave 20: the congrArg transport — the run-19 seven-of-eight, the sole survivor's spelling lock, and the Landing ceiling hoists

**Provenance:** W5-B, the records wave of the GST campaign's wave-20 strike session.  This
is the round record for the twentieth repair wave on the twelve-point native geometric
world, written at HEAD `1417c495` (the nineteenth-wave commit, whose CI adjudication —
run `43893556892`, RED, exactly ONE elaboration error, at `GSTTwelvePointCohomology.lean:
256:6` — is this round's target) with the wave-20 edits landing in the working tree IN
PARALLEL: the congrArg kill in the cohomology (`dualCochains_d_odd`) and the W4-B R1
hardening in the Landing (`twelvePointSeed_hodge` + the certificate's `.mpr` block).
Every lemma name and line number cited below is the pinned Mathlib's (`mathlib4` @
`51e6992efd06126df61a496bebf8f49482a4e129`); every run-19 error cite is at `1417c495`
file state (verified line-by-line against the run-19 artifact log and the HEAD tree this
session).  No Lean kernel verdict is claimed for wave 20 at this record's write time.
Zero mathematics changed — elaboration engineering only, the 2026-11-15 CI-loop record's
disclosure standing.

## What this is

Tier 3 of the six-module serial chain (`GSTTwelvePointCohomology.lean`, first exposed run
16 with 20 errors) is one error from closed: waves 17 and 18 each killed their adjudicated
target lists, wave 19 (run `43871161014`'s eight → the wave-19 alias-seam kill) went
**7-for-8**, and run `43893556892` at `1417c495` closed with **exactly one elaboration
error in the whole build** — `GSTTwelvePointCohomology.lean:256:6`, the `rw [hid]` step
inside `dualCochains_d_odd`.  The cohomology-internal trend reads 20 (run 16, first
exposure) → the wave-17/18 kill lists → 8 (run 18) → 1 (run 19) → wave 20 targets 0.

Wave 20 is two edits in one push:

1. **The kill** — the sole survivor dies by `congrArg` transport: the equation is moved
   on the hypothesis's OWN spelling and the goal is closed by unification at default
   transparency, so no `kabstract` occurrence search ever has to bridge the two
   type-spellings that killed the `rw`.
2. **The hardening** — the two conditional `zeroFiber_eq_top` rewrite pairs in the
   Landing file (W4-B's audit ceiling, exactly 2) are hoisted into ground haves whose
   every step is green under BOTH rw-matching models — the R1 conditional risk
   eliminated before it can become a first-contact adjudication.

## The run-19 verdict — 7-for-8, and the one that lived

Run `43893556892` (wave 19, commit `1417c495`) completed FAILURE at 15:27:42Z after
17m04s (W4-D's report; the artifact log carries the error body, the receipts, and the
build failure — see Disclosure for the metadata split).  Of run 18's eight errors, seven
are now CI-GREEN — zero errors at those sites in the run-19 log:

* **Cluster A-even — `dualCochains_d_even`, GREEN.**  The rebuilt closer
  (`have h0` at the d-slot type, `rw [h0]`, `exact ModuleCat.ofHom_zero`) elaborated
  clean.
* **Cluster B — all four exacts GREEN.**  `exact ModuleCat.hom_zero` /
  `exact ModuleCat.hom_id` closed all four `dualSc_exact_odd`/`_even` interiors after
  the two CI-proven rewrites — the default-transparency unification discipline this
  round now reuses.
* **Cluster C — both `Eq.trans` chains GREEN.**  `exact LinearMap.range_zero.trans
  LinearMap.ker_id.symm` (odd) / `exact LinearMap.range_id.trans
  LinearMap.ker_zero.symm` (even) closed with every implicit assigned from the goal.

The file's only other diagnostics are non-fatal linter notes (unused simp arguments at
`:321/:327/:337/:351/:352` in `fin12DualEquiv`'s linearity fields, the `haveI` style
hint at `:538`) — none an error, none a gate.

**The sole survivor — `:256:6`, the `rw [hid]` in `dualCochains_d_odd`, quoted from the
run-19 log:**

```
error: GSTTwelvePointCohomology.lean:256:6: Tactic `rewrite` failed: Did not find an occurrence of the pattern
  Linear.leftComp ℚ rationalCoefficient (𝟙 twelvePointE)
in the target expression
  ModuleCat.ofHom (Linear.leftComp ℚ rationalCoefficient (𝟙 twelvePointE)) = 𝟙 (twelvePointDualCochains.X (2 * k + 1))
```

with the transparency note ("The target expression is not type-correct under the
`implicit` transparency level, which may have triggered the failure…") and the full
error underneath it:

```
Application type mismatch: The argument
  𝟙 twelvePointE
has type
  @Quiver.Hom (ModuleCat ℚ) (ModuleCat.moduleCategory ℚ).toQuiver twelvePointE twelvePointE
but is expected to have type
  @Quiver.Hom (ModuleCat ℚ) (ModuleCat.moduleCategory ℚ).toQuiver
    ((ChainComplex.alternatingConst.obj twelvePointE).X (2 * k + 2))
    ((ChainComplex.alternatingConst.obj twelvePointE).X (2 * k + 1))
in the application
  Linear.leftComp ℚ rationalCoefficient (𝟙 twelvePointE)
```

*(Both blocks quoted verbatim from `/home/z/ci-logs/run19/gst-twelve-point-native-world.log`
lines 5955-5980, whitespace collapsed to the visible column structure.)*

**The diagnosis — a one-character elaboration-order asymmetry.**  The delaborated display
shows pattern and goal-occurrence IDENTICALLY (`Linear.leftComp ℚ rationalCoefficient
(𝟙 twelvePointE)` — the delaborator prints both spellings the same), but the underlying
terms differ in `leftComp`'s implicit object arguments:

* In `hid`'s LHS, the `𝟙 twelvePointE` argument's OWN type fixes its hom-type as
  `twelvePointE ⟶ twelvePointE` BEFORE the ascription can act — `𝟙` takes the object as
  an explicit argument, so the term is fully elaborated at the BARE
  `{twelvePointE, twelvePointE}` spelling, and the type-ascription `(… : X (2*k+2) ⟶
  X (2*k+1))` is then only CHECKED against it (defeq at default transparency — it
  succeeds, but it does not re-elaborate or re-pin the term).  `leftComp`'s implicits
  therefore land bare.
* The goal's occurrence — deposited by `rw [hd, altChain_d_even k]` — carries hd's
  d-slot spelling `{X (2*k+2), X (2*k+1)}` (the `alternatingConst` X-projections).
* `rw`'s occurrence search (`kabstract`) matches at sub-default transparency;
  `alternatingConst` is a plain `def`, so the two spellings are only
  DEFAULT-transparency defeq.  No occurrence is found — and the "full error" type
  mismatch is exactly the bare-vs-d-slot hom-type clash surfacing when the pattern is
  re-elaborated against the target's spelling.

**Why the even twin lived.**  `h0`'s transported term is a literal `0` ascribed at the
d-slot type — a literal elaborates WITH the expected type from the ascription, so its
`leftComp` implicits land at the goal's d-slot spelling and `rw [h0]` matched cleanly.
The odd twin's `𝟙 twelvePointE` carries its own type-determining explicit argument, which
the ascription cannot re-pin.  Same proof shape, one survivor — the wave-19 design's
single blind spot, now this round's kill.

**The error-recovery shadow (the receipts).**  The failed tactic block left
`dualCochains_d_odd` in the environment with `sorryAx` (Lean's error recovery), and the
taint propagated exactly one receipt deep: `twelvePointCohomology_subsingleton` prints
`[propext, sorryAx, Classical.choice, Quot.sound]` (the route
`dualCochains_d_odd` → `dualSc_exact_odd` → `exactAt` → `isZero` → subsingleton), while
`twelvePointCohomologyIso` prints CLEAN `[propext, Classical.choice, Quot.sound]` — its
chain routes through the EVEN case (`dualCochains_d_even 0`, green this run).  The
`sorryAx` token in the log would independently trip the workflow's sorry-gate grep
(`.github/workflows/gst-twelve-point-native-world.yml:69-70`); the build error already
fails the run — "Some required targets logged failures: - GSTTwelvePointCohomology",
"error: build failed".  **Tiers 4–6 were NOT reached again**: they remain
never-elaborated, the wave-19 pre-emptive bundle still waiting behind the one dying
step.

## The kill (Wave 20) — the congrArg transport, live in the working tree

`dualCochains_d_odd`'s closer pair

```
  rw [hid]
  exact ModuleCat.ofHom_id
```

becomes

```
  exact (congrArg ModuleCat.ofHom hid).trans ModuleCat.ofHom_id
```

The defeq trace, step by step:

1. **`congrArg ModuleCat.ofHom hid`** builds `ModuleCat.ofHom (Linear.leftComp ℚ
   rationalCoefficient (𝟙 twelvePointE)) = ModuleCat.ofHom LinearMap.id` — elaborated
   at HID'S OWN spelling (the bare `{twelvePointE, twelvePointE}` implicits), because
   `congrArg` applies `ModuleCat.ofHom` to the two sides of `hid` as they are.  No goal
   search, no `kabstract`, no cross-spelling bridge at sub-default transparency — the
   equation is transported on the hypothesis's own terms.
2. **`.trans ModuleCat.ofHom_id`** (`ModuleCat/Basic.lean:176`, an `rfl`-lemma) appends
   `ModuleCat.ofHom LinearMap.id = 𝟙 …`, composing the two equations.
3. **The final `exact`** unifies the composite against the goal
   `ModuleCat.ofHom (Linear.leftComp ℚ rationalCoefficient (𝟙 twelvePointE)) = 𝟙
   (twelvePointDualCochains.X (2 * k + 1))` at DEFAULT transparency — the LHS
   bare-vs-d-slot spelling clash and the RHS identity-object unification are both the
   default-defeq class through `alternatingConst`'s constant X-projection — **the same
   discipline run 19 just validated GREEN at all four Cluster-B sites** (`exact
   ModuleCat.hom_zero`/`hom_id` bridging raw d-slot `0`/`𝟙` against `sc'`-typed goals)
   and at the Cluster-A-even `exact ModuleCat.ofHom_zero`.

The `rw`'s job is gone entirely: nothing is searched for in the goal, the spelling
mismatch that killed `kabstract` never meets a matching decision, and the whole burden
moves to the one unification mode — `exact` at default transparency — that run 19 just
exercised green at all seven of the file's surviving exact closers (the Cluster-A-even
`ofHom_zero`, the four Cluster-B `hom_zero`/`hom_id`, the two Cluster-C `Eq.trans`
chains).

## The hardening (W4-B R1) — the Landing ceiling hoists

W4-B's Landing audit (delivered this session): the whole file CLEAN with conditional
ceiling EXACTLY 2 — the two `rw [twelvePointHodgeData_bigrading_zero,
zeroFiber_eq_top]` pairs, each green or dead depending on which rw-matching model the
elaborator actually runs (the projection↔constant spelling across
`twelvePointHodgeData.hodgeBigrading 0` vs `zeroBigrading`).  The pre-designed hoist
repair is wave 20's second edit, landed at both sites:

* **Site 1 — `twelvePointSeed_hodge` (`:124-142`).**  The fiber equation is hoisted as
  a ground have at the goal's own projection spelling:
  `have hfib : rationalHodgeSubspace (twelvePointHodgeData.hodgeBigrading 0) = ⊤ := by
  rw [twelvePointHodgeData_bigrading_zero]; exact zeroFiber_eq_top`, then `rw [hfib]`
  and `exact Submodule.mem_top _`.
* **Site 2 — `twelvePointCertificate_isKrylovCyclic`'s `.mpr` block (`:325-344`).**  The
  identical hoist — same three-step interior, closing on
  `twelvePoint_orbitUnderlying_span`.

**Why every step is green under BOTH rw-matching models.**  The interior `rw
[twelvePointHodgeData_bigrading_zero]` is SYNTACTIC in either model — the have's LHS is
stated at the projection spelling and the bridge lemma's LHS (`HodgeData:293`, `=
zeroBigrading` by `rfl`) is the same projection spelling; no seam is crossed.  The
constant-spelling burden (the fiber lemma `zeroFiber_eq_top` is stated over
`zeroBigrading`, `HodgeData:248`) is carried by `exact` at DEFAULT transparency.  The
outer `rw [hfib]` is purely syntactic — `hfib`'s LHS spelling IS the goal's occurrence
spelling (both the projection, as stated in the theorems).  Under the model where rw
matches across the projection↔constant seam the old pair was green anyway; under the
model where it does not, the old pair died at the second rewrite — the hoist is green in
both.  The conditional ceiling is gone: no step's greenness in the Landing file depends
on an rw-matching transparency question anymore.

## Agent accounting (the W4 wave, then W5)

* **W4-A — died at the deadline** (the cohomology diagnosis work it was carrying was
  absorbed by W4-D's verdict).
* **W4-B — delivered the Landing audit:** whole-file CLEAN, conditional ceiling exactly
  2 (the two `zeroFiber_eq_top` rw-pairs), the pre-designed hoist repair — landed as
  wave 20's hardening.
* **W4-C — died at the deadline.**
* **W4-D — delivered the CI verdict** (run 19's 7-for-8 + the sole survivor's full
  diagnosis), **the response matrix**, **the battery re-run PASS** (the 294-query Z3
  battery reproducible — byte-identical to the 2026-11-16 verdict JSON except the
  timestamp), **and fixed the app's CI-status route rate-limit**.
* **W5-B — records (this record, the commit-message draft
  `research/records/2026-11-16-wave20-commit-message.txt`, the INDEX entry).**

## Disclosure and non-claims (exact scope)

* **No kernel verdict for wave 20 at this record's write time.**  The wave-20 push's CI
  run has not fired; no green is claimed for the twelve-point lane at any SHA
  (AGENTS.md rule 7).  The run-19 verdict quoted here is run `43893556892`'s, at
  `1417c495`.
* **The run-19 metadata split:** the artifact log
  (`/home/z/ci-logs/run19/gst-twelve-point-native-world.log`, 14171 lines) carries the
  error body, the transparency note, the full-error type mismatch, the two receipts,
  the required-target failure line, and the build failure — every technical claim above
  was verified against it this session.  The log carries NO run-ID/timestamp header;
  the run number, the 15:27:42Z completion, and the 17m04s duration are W4-D's report's
  and are recorded here on that authority.
* **Tiers 4–6 have still never been elaborated by any CI run** — run 19 died in tier 3
  again (build-order: the failure line names `GSTTwelvePointCohomology` alone).  The
  wave-19 pre-emptive bundle's first-contact exposure remains one green step away.
* The wave-20 design's proof is the pending run, not this record; the congrArg
  transport's final-unification burden is argued by analogy to the five run-19-green
  default-transparency sites, not by compilation from this sandbox.
* Zero mathematics changed: the construction, the lane, the lib registration, and the
  six-file path filter are the 2026-11-14 record's, untouched.  The twelve-point lane
  remains a RESTRICTED, zero-dimensional discharge lane; no typed ⇒ native transport
  exists anywhere in the repository.

## CI status

**Pending — wave 20 not yet pushed at this record's write time** (the congrArg kill and
the two R1 hoists are in the working tree; the commander commits after the gates).  The
lane's last adjudication is run `43893556892` at `1417c495`: RED, exactly one
elaboration error (`GSTTwelvePointCohomology.lean:256:6`), one receipt tainted
(`twelvePointCohomology_subsingleton`), one clean (`twelvePointCohomologyIso`).  The
session's standing greens are unchanged: the landing lane (`43750693353` at `2378003`),
the spanning lane (`43747935402` at `06c1037`), and the part1-chow-transfer lane
(`db97399`).  Tier 1 (carrier) closed at run 11; tier 2 (analytification) closed at run
15; tier 3 (cohomology) is this wave's kill — one step from closed; tiers 4–6 have
never been elaborated by any run.
