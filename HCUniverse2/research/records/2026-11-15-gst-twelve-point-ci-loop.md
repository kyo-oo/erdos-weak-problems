# 2026-11-15 — The twelve-point CI loop: six runs, one root cause, the systemic kill

**Provenance:** W4-B, the records-keeper wave of the GST campaign's CI-loop session.  This
is the round record for the six-run repair loop on the twelve-point native geometric world
(repair waves 4–8 of the 2026-11-15 session; agent waves W1–W4), written at HEAD `e3693d8`
with the loop's closing CI run 43778820813 in progress.  The construction under repair is
the 2026-11-14 world of `2026-11-14-gst-twelve-point-native-geometric-world.md` (V₀ =
Spec(ℂ¹²), the 26-letter fold word, the live rank-12 discharge); this round changed ZERO
mathematics — every commit in the loop is an elaboration-engineering repair to
`GSTTwelvePointWorldCarrier.lean` (and, in wave 5, to the landing file).  Every lemma name
and line number cited below is the pinned Mathlib's (`mathlib4` @
`51e6992efd06126df61a496bebf8f49482a4e129`).  No Lean kernel verdict is claimed for the
loop's closing run at this record's write time.

## What this is

The twelve-point lane (`.github/workflows/gst-twelve-point-native-world.yml`, registered by
the 2026-11-14 record) had been red since the six modules first landed: the session opened
at run#4 (the wave-3-state baseline, its log the carrier's chart/Lagrange/over_base error
set), and the session then logged eight adjudicated runs on the twelve-point lane (runs
#4–#11 complete, #11 the loop's last at this supplement's write time) plus the landing
lane's green interlude.  The loop's shape is the point of this record, and it now reads
in TWO views: **whole-run error counts went 5 → 12 → 9 → 2 → 1 → 1 → 20** —
non-monotonic by construction, because each repair wave that fixed an elaboration seam
unmasked the cascades hiding behind it — while the **carrier-internal counts went
5 → 12 → 9 → 2 → 1 → 1 → 0**: the eighth wave stopped patching symptoms and killed the
loop's single dominant root cause (run 43778820813 owns that kill's verdict), the ninth
through eleventh killed the three surviving transcription defects one apiece, and run 11
closed the carrier entirely — the twenty new errors living one module DOWNSTREAM, in a
file no run had ever reached.

The loop's runs, in order:

| # | wave / SHA (UTC) | lane | verdict |
|---|---|---|---|
| 1 | run#4 — wave-3 state (baseline) | twelve-point | RED (the error set wave 4 addressed) |
| 2 | wave 4 — `ddce112` 19:06 | twelve-point | RED — 5 errors |
| 3 | wave 5 — `2378003` 19:08 | landing | **GREEN — run 43750693353** |
| 4 | wave 6 — `dfa1488` 21:39 | twelve-point | RED — 12 errors (cascade unmasking) |
| 5 | wave 7 — `fa20777` 22:11 | twelve-point | RED — 9 errors (run 43767848609) |
| 6 | wave 8 — `e3693d8` ~23:50 | twelve-point | **RED — 2 errors — run 43778820813** (the Run 8 verdict below) |
| 7 | wave 9 — `21937ce` 01:31Z | twelve-point | **RED — 1 error — run 43786807104** (the Run 9 verdict below) |
| 8 | wave 10 — `de5541c` 02:07Z | twelve-point | **RED — 1 error — run 43790217021** (the Run 10 verdict below) |
| 9 | wave 11 — `a5f1c5b` 02:42Z | twelve-point | **RED — 0 carrier errors / 20 downstream on first exposure — run 43793762987** (the Run 11 verdict below — the carrier-clean cascade) |

## The loop, wave by wave

**Wave 4 (`ddce112`, 19:06Z) — the carrier, first contact.**  `chartRingMap` gets the
intermediate-ring type ascription (unsticks the map's source), the fraction decomposition
moves to generic `j` before the two-chart dispatch (kills the embedded-literal instance
mismatch), the Lagrange degree bridge rewrites in the correct direction, the chart
cancellation uses the `.inv` form with the pinned argument order, `over_base` drops the
regrouping in its new staged form, the coheight `rw` self-closes.  → **run#5 RED, 5
errors.**

**Wave 5 (`2378003`, 19:08Z) — the landing file.**  `mem_bot` takes the ring explicit,
`mem_top` needs no element argument (both pinned-Mathlib signature facts), the `certFold`
orbit-class equality restated in the goal's field-projection shape, a dead `le_rfl`
dropped.  → **the landing lane GREEN: run 43750693353** — `GSTNativeSingleFoldOrbitLawLanding.lean`
kernel-checked at `2378003` (the session's only landed green; the cheap-class discharge,
the no-free-lunch boundary, and the native⇒typed bridge of the 2026-11-14 records are
now kernel facts, independent of the twelve-point lane's fate).

**Wave 6 (`dfa1488`, 21:39Z) — the spine rewrite.**  Five kills: `chartRingMap` rides
Mathlib's goal-driven `refine` spine (kills the stuck away-localization instance search),
`chartRingMap_apply` exposes the composite by a definitional `rfl` and closes by `map_eq`,
the fraction destructure splits the `Subtype` before the power subst (kills the
non-substitutable coercion) with both chart tails rebuilt on `Subtype.coe_mk`
normalization and correct merge directions, the iso-peeling chain rides the `.mpr`
direction of the cancel lemmas (definitional factor matches instead of syntactic),
`over_base` bridges the degree-zero algebra map through `IsScalarTower` with the
definitional route first.  → **run#6 RED, 12 errors — the cascade unmasking:** the spine
repair made elaboration honest, and every seam the stuck spine had been hiding surfaced
at once.  An error count that rises from 5 to 12 in a repair loop is progress, not
regression.

**Wave 7 (`fa20777`, 22:11Z) — twelve claimed kills.**  The side-condition `rw`
self-closes (dead `simp` dropped), the chart `algebraMap` gets its explicit source ring
(unsticks the `refine`), the composite-exposure `rfl` gains unfold/`simp` fallbacks, the
node-zero branch drops the mismatched `zero_pow` arg and the else-branch rides a
definitional `show` for the `ite`, the `hΓ` transport uses `rfl`-exposed `e1`/`e2` lemmas
with corrected merge order, BOTH chart `refine`s flip `.mp` to `.mpr` (the implicant is
the B-side), the `j = 1` `hΓ` rewrite flips to `← hy'`,
`Scheme.toSpecΓ_preimage_basicOpen` takes its explicit scheme argument, the bare
`cancel_left` peels take `_ _` arguments, the adjunction `show` rewrites `hcomp` directly.
→ **run#7 RED — run 43767848609, 9 errors, all in `GSTTwelvePointWorldCarrier.lean`**
(the five sibling modules un-reached — the original write's parenthetical "clean" is
CORRECTED by the Run 11 verdict below: the build stopped at the carrier, so no sibling
had any verdict at all; never-reached ≠ clean); the run took **23.9 min with a corpus
cache miss**.
Twelve kills claimed, three landed — the remaining nine share a cause no symptom patch
can touch.

**The run#7 error inventory** (line numbers at `fa20777`):

* **E1** `283:61` and **E2** `305:30` — stuck `CommSemiring ?R` metavariables inside
  `Localization.Away (MvPolynomial.X j)`: `MvPolynomial.X`'s implicit `CommSemiring`
  argument never unified, because the away/powers instance search ran against an alias it
  could not see through.
* **E3** `406:31` — `rw` pattern failure plus a Γ-type mismatch in the `hΓ` transport.
* **E4** `413:12` — stuck `CommSemiring S✝` at the `IsLocalization.eq_iff_exists`
  application (the localization-data metavariable).
* **E5** `417:4` — no-goals cascade, downstream of E4's failed `refine`.
* **E6** `498:11` — missing `IsIso (toSpecΓ ∣_ basicOpen)` at the fourth peel of
  `chart_closed`.
* **E7** `500:2` — `cancel_left` type mismatch, the same peel's side condition.
* **E8** `580:8` — `RingHom` codomain mismatch in `over_base`'s STAGE 4 adjunction.
* **E9** `589:4` — `rw` pattern `?f ≫ ?g ≫ ?h` failure, same STAGE.
* Plus **sorryAx contamination in the receipts** of `twelvePoint_closedImmersion`,
  `twelvePoint_over_base`, `twelvePointWorld` — not real sorries: a red declaration
  elaborates as `sorryAx`, and every downstream receipt inherits the taint.  The lane's
  sorryAx hard-fail is therefore expected to lift with the nine errors themselves.

## The root cause

Five of the nine — E1, E2, E4, E6, E7 — share **one root cause: the
`twelvePointScheme` def-alias boundary.**  `rw` pattern matching and instance synthesis
run at `.instances` transparency, where a plain `def` is opaque.  The world's carrier had
been declared `def twelvePointScheme : Scheme := Spec (CommRingCat.of (Fin 12 → ℂ))`, so
every proof step that needed to identify `Γ(twelvePointScheme, ⊤)` with
`Γ(Spec (CommRingCat.of (Fin 12 → ℂ)), ⊤)` — the global-sections ring as Mathlib's
localization and restriction lemmas see it — hit an invisible wall:

* E1/E2: the `Localization.Away`/`Submonoid.powers` instance search around
  `MvPolynomial.X j` could not resolve its `CommSemiring` argument against the aliased
  section ring, so `X`'s implicit coefficient ring stayed a metavariable.
* E4: `IsLocalization.eq_iff_exists`'s `S` (the localization-data instance) met the same
  wall.
* E6/E7: the restriction instance `IsIso (f ∣_ U)` for `IsIso f`
  (`Mathlib/AlgebraicGeometry/Morphisms/Restrict.lean:639`) had to be found for
  `twelvePointScheme.toSpecΓ ∣_ basicOpen`, and synthesis could not see the affine
  structure through the alias.

E5 is the no-goals cascade of E4's failed `refine`; E3 is a localized shape defect in
the `hΓ` transport (the `rw` pattern + Γ-type mismatch at 406:31); E8/E9 are localized
shape defects at `over_base`'s STAGE 4 composite (the `Spec.map`/adjunction regrouping).
So the loop's honest accounting is: **one seam behind five errors, two sites behind the
other four.**
The corpus has precedent — `complexBase` and `ProjectiveGrading` are `abbrev`s for
exactly this reason; the twelve-point carrier had been the exception.

## The systemic kill (wave 8)

**Wave 8 (`e3693d8`, ~23:50Z by the session clock; commit-stamped 00:10 UTC 2026-11-16)** —
one surgical repair per root cause, **+70/−41 lines in `GSTTwelvePointWorldCarrier.lean`
only**, no sibling file touched:

1. **`def` → `abbrev twelvePointScheme`** (now `GSTTwelvePointWorldCarrier.lean:55`) —
   the alias dies: pattern matching and instance synthesis unfold it at `.instances`
   transparency, so the Γ-seam ceases to exist.  This one word kills the root cause
   behind E1/E2/E4/E6/E7.
2. **`chartRingMap` term-mode, fully explicit `R S M P T Q`** (`:280-293`) — the
   pinned `toBasicOpenOfGlobalSections` composite
   (`ProjectiveSpectrum/Basic.lean:369-377`) transcribed verbatim, every type argument
   given so each instance resolves against a concrete ring, and every `MvPolynomial.X j`
   feeding an `Away`/`powers` head carries a coefficient-ring ascription pinning the
   `CommSemiring` to `ℂ` (E1/E2).
3. **`eq_iff_exists` explicit `M` and `S`** (`:431`) — the localization submonoid and
   data instance supplied, no metavariable left to guess (E4, and with it E3/E5).
4. **`chart_closed`'s explicit `haveI` chain before the fourth peel** (`:525-531`) —
   `IsAffine twelvePointScheme` by `inferInstanceAs` through the (now transparent) alias,
   `IsIso twelvePointScheme.toSpecΓ` by `IsAffine.affine` (`AffineScheme.lean:59`), the
   restriction instance by `inferInstance` — the chain supplied explicitly, independent
   of the alias's reducibility (E6/E7).
5. **`over_base`'s STAGE 4 via `CommRingCat.ofHom_comp` + the unit triangle
   `toSpecΓ_SpecMap_ΓSpecIso_inv`** (`:607-613`) with a single `show`-level alias bridge
   (E8/E9): the degree-zero algebra map's composite is regrouped at the `CommRingCat`
   level, the adjunction unit triangle closes it, and one `show` bridges the remaining
   `Scheme.toSpecΓ` identification.

## The verification wave (W3) and the numerics (W1-F)

The kill was verified before push by the W3 seven-agent verification wave:

* **Regression sweep GREEN for all five sibling files** — no site in
  `GSTTwelvePointAnalytification.lean`, `GSTTwelvePointCohomology.lean`,
  `GSTTwelvePointHodgeData.lean`, `GSTTwelvePointFoldWord.lean`,
  `GSTTwelvePointLawLanding.lean` depended on the `def`'s opacity; every reference to
  `twelvePointScheme`, `chartRingMap`, and `over_base` remains well-typed under the
  `abbrev`.
* **Peel trace verified against the pinned Mathlib tree** — every cancel/restriction/
  localization lemma's direction, argument order, and side condition in the wave-8 file
  audited against the pinned source lines it cites.
* **Syntax gate PASS** — the wave-8 file parses clean.

The recon wave's numeric agent (W1-F) re-verified the world's arithmetic, **ALL PASS**:

* `det K = −1149656584000 ≠ 0` — the twelve-point Krylov determinant, by **4 independent
  algorithms** (the exact Wolfram orbit computations, the independent SymPy rebuild,
  the fraction-free Bareiss elimination, and the Z3 re-derivation).
* **577/577 Z3 queries UNSAT** — the full certificate-contradiction batch.
* **26 letters reconstruct Twave** — the fold word's point-pair letters rebuild the
  owner's wave matrix exactly.
* `U` order 5 (`U⁵ = I`), `J² = −I`, `UJ = JU` — the operator algebra intact.
* **144/144 `certRow` fractions** verified; largest-magnitude coefficient
  `1495609060489/114965658400` (row 4, column 5); LCM of all denominators
  `574828292000 = |det|/2` (the adjugate/Cramer consistency law).

## Agent-wave accounting

* **W1 — recon, 7 agents** (A–G): the run#7 log triage, the root-cause isolation (the
  def-alias seam), the pinned-Mathlib API audit, and the W1-F numeric re-verification
  above.
* **W2 — kill design, 7 agents**: the five repairs of wave 8 designed against the root
  cause (the abbrev flip, the term-mode `chartRingMap`, the explicit `eq_iff_exists`
  arguments, the `haveI` instance chain, the `over_base` STAGE 4 rewrite), each checked
  against the pinned tree before writing.
* **W3 — verification, 7 agents**: the regression sweep, the peel trace, the syntax gate
  (above).
* **W4 — records** (this record, W4-B): the round record and the INDEX entry; the
  commander commits after the CI verdict.

## Disclosure

* This round's content is **Lean engineering, not mathematics**: the construction is
  byte-for-byte the 2026-11-14 record's (the world, the fold, the certificate); the
  loop's commits change elaboration shape and declaration transparency only.  The
  mathematical claims and their scope are unchanged and governed by the 2026-11-14
  record's disclosure and non-claims.
* The loop's error-count trajectory (5 → 12 → 9) records cascade unmasking, and the
  wave-7 "twelve claimed kills" landed three — the record states this plainly: symptom
  patches in a transparency-bug loop under-deliver by construction, which is why wave 8
  changed strategy from patching the nine symptoms to killing the one seam.
* The wave-8 verification (W3) is **static** — name resolution, peel-trace audit against
  the pinned source, syntax gate, sibling regression sweep.  No Lean compilation is
  claimed from this sandbox; the kernel verdict belongs to run 43778820813 alone.
* The W1-F numerics are external exact evidence (Wolfram/SymPy/Bareiss/Z3), not Lean
  proofs; the in-Lean certificate remains the Gauss-Jordan inverse table of the 2026-11-14
  record.

## Non-claims (exact scope)

* **No kernel verdict for run 43778820813 at this record's write time** — the run is in
  progress; no green is claimed for the twelve-point lane at any SHA of this session.
  Per AGENTS.md rule 7, no green run is cited until the run exists at the pushed SHA.
* The landing lane's green (run 43750693353 at `2378003`) covers
  `GSTNativeSingleFoldOrbitLawLanding.lean`'s closure only; it does not imply the
  twelve-point lane (a different module closure and a different lane).
* The root-cause analysis is an engineering diagnosis; its proof is the pending run, not
  the static verification.  If run#8 remains red, the residual errors are expected at the
  two non-alias sites (the `hΓ` transport and `over_base`'s composite), not a new seam.
* No new mathematics, no new modules, no registration changes this round: the lane, the
  `GSTTwelvePointNativeWorldUpgrade` lib, and the six-file path filter are the 2026-11-14
  record's, untouched by all five commits of the loop.

## CI status

**Verdict pending — run 43778820813 at `e3693d8`, in progress at this record's write
time.**  The session's only landed green is the landing lane's run 43750693353
(`GSTNativeSingleFoldOrbitLawLanding.lean` at `2378003`).  The twelve-point lane's kernel
verdict at HEAD belongs to GitHub CI; this record will be supplemented by the commander's
commit round once the run lands.

*(Superseded by the supplements below: run 43778820813 resolved FAILURE — 2 errors, the
Run 8 verdict; run 43786807104 FAILURE — 1 error, the Run 9 verdict; run 43790217021
FAILURE — 1 error, the Run 10 verdict; run 43793762987 at `a5f1c5b` FAILURE — 0 carrier
errors / 20 downstream first-exposure errors, the Run 11 verdict.  This section stands
as the original write-time status.)*

---

## Run 8 verdict (W6-E supplement, 2026-11-16 ~01:40Z, written at HEAD `21937ce`)

**Run 43778820813 FAILED** — job 133011134386, fired 00:10:44Z, completed 00:26:12Z
(**15m28s**, the fastest lane adjudication yet, on a corpus cache hit).  The loop's error
trend closes its fourth point: **5 → 12 → 9 → 2**.  Seven of the nine wave-7 errors are
dead — the `abbrev` flip, both explicit `chartRingMap` spines, the `eq_iff_exists` explicit
`M`/`S`, and the `over_base` STAGE 4 rewrite all elaborated clean, and BOTH W3-flagged
residual-risk zones (the `IsLocalization.map` named-args elaboration and the show-bridge
defeq) PASSED.  The two survivors both sit in `chart_closed`, the wave-8 patch-5 region (the
W2-D site) — the evolved forms of wave-7 E6/E7:

* **R1** `531:4` — `failed to synthesize instance of type class IsIso
  (twelvePointScheme.toSpecΓ ∣_ PrimeSpectrum.basicOpen (sectionRingHom (MvPolynomial.X j)))`:
  the `haveI` chain's own closing `inferInstance` — the `Restrict.lean:639` instance still
  unfound, even through the now-transparent alias.
* **R2** `536:2` — `Type mismatch` at the post-peel `exact IsClosedImmersion.spec_of_surjective
  (CommRingCat.ofHom (chartRingMap j)) (chartRingMap_surjective j)` — and the mismatch's
  expected side is the round's payload.  (The `sorryAx` taint on the
  `twelvePoint_closedImmersion`/`twelvePointWorld` receipts is the known error-recovery
  fallout; it lifts with the two errors.)

**The domain revelation (R2).**  The goal `chart_closed` was actually asking for, verbatim
from the job log (`:1104-1110`):

```lean
IsClosedImmersion
    (Spec.map
      (CommRingCat.ofHom
        ((IsLocalization.map (Localization.Away (sectionRingHom (MvPolynomial.X j))) sectionRingHom ⋯).comp
          (algebraMap (HomogeneousLocalization.Away grading (MvPolynomial.X j))
            (Localization.Away (MvPolynomial.X j))))))
```

The exposed composite names its own source ring.  The chart ring map's FIRST-APPLIED factor
is `algebraMap (HomogeneousLocalization.Away grading (MvPolynomial.X j)) (Localization.Away …)`
— the `homogeneousLocalizationAlgebra` structure map (definitionally
`HomogeneousLocalization.val`, `GradedAlgebra/HomogeneousLocalization.lean:477-490`) — NOT
the polynomial ring's `algebraMap (MvPolynomial (Fin 2) ℂ) (Localization.Away …)` that
waves 4, 6, 7, and 8 all transcribed there.  **The chart ring map's domain is the degree-`0`
homogeneous localization `HomogeneousLocalization.Away grading (MvPolynomial.X j)` — the
`D₊(X j)` chart ring** (what `basicOpenIsoSpec` targets on the Proj side), not
`MvPolynomial (Fin 2) ℂ`.  The wrong domain was born in the world's original authoring
(the 2026-11-14 modules, merged at `f6a435d`: `chartRingMap : MvPolynomial (Fin 2) ℂ →+* …`
from its first line) and survived every repair since — reading the pinned
`toBasicOpenOfGlobalSections` composite (`ProjectiveSpectrum/Basic.lean:369-377`), every
wave elaborated the innermost `algebraMap _ (Localization.Away t)` against the wrong
expected type.  A wrong-domain transcription is well-typed in isolation, so it was invisible
to every static gate: W3's peel trace verified each rewrite against the pinned source lines,
but both sides of R2's mismatch were elaborations of the wrong domain.  Only the
kernel-adjacent elaborator, holding the true goal — a goal made honest by the wave-8
`abbrev` kill unmasking E6/E7 — could expose it.  (The worklog's run-8 postscript first
guessed R2 was "likely fallout" of R1's shape; wrong — R2 was the revelation, and this
supplement records the correction.)

## Wave 9 (`21937ce`, committed 2026-11-16 01:31:53Z) — the true-domain repair

**+114/−88 lines in `GSTTwelvePointWorldCarrier.lean` only** (722 → 748 lines; the commit
also carried this round record — as committed, it documents the loop through the wave-8
verdict-pending state — and its INDEX entry; the present supplement rides the working tree
for the commander's post-verdict commit).  Four repairs, every one sourced from the W5-B
dossier:

1. **`chartRingMap` retyped to the verbatim composite** (`:282`) — the signature is now
   `HomogeneousLocalization.Away grading (MvPolynomial.X j) →+*
   Localization.Away (sectionRingHom (MvPolynomial.X j))`, and the body is the pinned
   `toBasicOpenOfGlobalSections` inner composite transcribed VERBATIM: first the
   `homogeneousLocalizationAlgebra` `algebraMap` (definitionally `val`), then
   `IsLocalization.map` with fully explicit `R S M P T Q` — the wave-8 explicitness
   discipline kept, now pointed at the true domain.
2. **`chartRingMap_apply` rides Mathlib's own computation spine** (`:315`) — restated on the
   constructor form `HomogeneousLocalization.Away.mk grading hXj k p hp`; the proof is the
   pinned chain of `fromOfGlobalSections_preimage_basicOpen`
   (`ProjectiveSpectrum/Basic.lean:481-484`): `HomogeneousLocalization.algebraMap_apply` →
   `HomogeneousLocalization.Away.val_mk` → `Localization.mk_eq_mk'_apply` →
   `IsLocalization.map_mk'` (+ `map_pow` for the denominator power), closed by `rfl` (the
   two `mk'`-denominator membership proofs agree by proof irrelevance).
3. **`chartRingMap_surjective` on the CLEARED Lagrange identities** (`:388`) —
   `chart_core_zero` REVIVED (dead code at `e3693d8`: wave 8's `j = 0` branch had inlined a
   node-split division `w i = y' i / (nodeValues i)^N` that could never survive the
   homogeneous-fraction bookkeeping): for every value vector `y` and exponent `N`, a form
   `p` homogeneous of degree `M` with the pointwise CLEARED identity
   `p(v i) · (v i)^N = y i · (v i)^M`.  The witnesses are homogeneous fractions
   `Away.mk grading hXj M p hp`; the `j = 0` clearing multiplier is ONE MORE FACTOR of
   `f₀ = sectionRingHom (MvPolynomial.X 0)`, never a division — node `0` makes `f₀` a zero
   divisor (`nodeValues 0 = 0` in the pointwise ring `Fin 12 → ℂ`), so
   `IsLocalization.eq_iff_exists`'s witness `⟨f₀, mem_powers⟩` does the clearing and the
   transported identity `hΓ` closes it; chart `j = 1` rides the unit (`section_X_one`).
   The `mk'`-bookkeeping rides `IsLocalization.mk'_eq_iff_eq'` +
   `IsLocalization.eq_iff_exists`, both with explicit `M` and `S`.
4. **R1 dies by Mathlib's own instance body** (`:552-560`) — the
   `IsIso (toSpecΓ ∣_ basicOpen …)` hop is now `by delta AlgebraicGeometry.morphismRestrict;
   infer_instance`: the restriction unfolds to its pullback composite (the
   `Restrict.lean:639-640` instance's own body) BEFORE instance synthesis — the direct
   `inferInstance` on the restriction form got stuck at the `Opens`-type seam; the
   post-`delta` search runs on the already-elaborated composite.

**The W5/W6 agent accounting.**

* **W5 — recon, 7 agents**: the run-8 CI dossier (`gst-recovery/w5d/` — the full
  job-133011134386 log, the raw job log, the artifact zip, and the Lean-core
  instance-synthesis sources `SynthInstance.lean`/`SyntheticMVars.lean` themselves,
  fetched to dissect R1's stuck search); and **W5-B's `HomogeneousLocalization` dossier**
  (`gst-recovery/w2f/HOMLOC_API.md`, 571 lines, plus the full pinned-file snapshots) — the
  file-layout discovery (the whole `ProjectiveSpectrum/HomogeneousLocalization/` folder
  moved+merged into `RingTheory/GradedAlgebra/HomogeneousLocalization.lean`, 1129 lines at
  the pin; **no `DegreeZeroLocalization` exists** — the element constructor is `Away.mk`
  `:609`, the algebra instance `homogeneousLocalizationAlgebra` `:477`, `algebraMap_apply`
  an `rfl` `:489`), the pinned composite and Mathlib's computation spine verbatim, the
  degree bookkeeping (`nsmul_one` for the `k • 1` side condition;
  `MvPolynomial.isHomogeneous_X` `R`-explicit), and the §10 verdicts (no one-shot lemma
  exists — the four-step chain IS the repair).
* **W6 — kill design, 7 agents**: two design agents hit context deadlines at exactly the
  two load-bearing sites — the surjectivity rebuild (`chartRingMap_surjective`) and the
  instance hop (`IsIso (toSpecΓ ∣_ basicOpen)`) — and the commander took both sites over
  (the wave-8 W2-C pattern), designing and applying the four repairs directly.  **W6-E —
  records** (this supplement, and the worklog's postscript-2 / ninth-wave-round sections).

## Run 9 verdict (W7-D supplement, 2026-11-16 ~02:15Z, written at HEAD `de5541c` with run 10 in flight)

**Run 43786807104 FAILED** — job 133036185341, fired 01:31:57Z, job start 01:32:00Z,
completed 01:47:44Z (**15m44s**, on a corpus cache hit).  **Exactly ONE error** — the
loop's trend closes its fifth point: **5 → 12 → 9 → 2 → 1**.  Both wave-8 survivors are
dead and the entire wave-9 repair elaborated clean except one line:

* **The error** — `GSTTwelvePointWorldCarrier.lean:319:6`, verbatim from the artifact
  body (`w7d/gst-twelve-point-native-world.log:1094`): `failed to synthesize instance of
  type class IsLocalization (Submonoid.powers (sectionRingHom (MvPolynomial.X j) ^ k))
  (Localization.Away (sectionRingHom (MvPolynomial.X j)))` — in `chartRingMap_apply`'s
  STATEMENT, not its proof.
* **The root cause** — a one-line elaboration-order defect in the wave-9 rewrite
  itself: the statement's `mk'`-denominator membership witness `⟨sectionRingHom
  (MvPolynomial.X j) ^ k, Submonoid.mem_powers _⟩`.  The `_`'s expected type was
  inferred from the ELEMENT `f ^ k`, so `mem_powers`'s implicit generator unified with
  `f ^ k` — typing the Subtype as `powers (f ^ k)` where the localization's own submonoid
  is `powers f` — and the elaborator was sent hunting for `IsLocalization (powers
  (f ^ k)) (Away f)`, which does not exist.  The proof body (Mathlib's computation
  spine) was never reached.  The wave-8 explicitness discipline — `M`/`S` pinned on
  every `mk'`-adjacent lemma in the PROOF (`mk'_eq_iff_eq'`, `eq_iff_exists`) — was
  applied everywhere except the one `mk'` the wave-9 rewrite itself introduced, in the
  statement.
* **What died** (all of the wave-9 repair but that line): the domain retyping
  (`chartRingMap`'s `HomogeneousLocalization.Away` signature and the verbatim
  composite), every link of the computation spine (`algebraMap_apply` → `Away.val_mk` →
  `mk_eq_mk'_apply` → `map_mk'` + `map_pow`), the surjectivity rebuild's `j = 0`
  cleared-identity machinery (`chart_core_zero`, the `eq_iff_exists` witness, the `hΓ`
  transport), and **BOTH wave-8 survivors** — R1's delta-instance hop and R2's
  post-peel `spec_of_surjective` are gone from the error set; `chart_closed` raised no
  error.
* **The receipts at `21937ce`**: `twelvePoint_over_base` (`:744`) and
  `twelvePoint_coheight` (`:745`) CLEAN (no `sorryAx`); the taint is exactly the two
  known error-recovery receipts — `twelvePoint_closedImmersion` (`:743`) and
  `twelvePointWorld` (`:746`), both downstream of `chartRingMap_surjective` (`:388`,
  whose `declaration uses sorry` warning is the direct taint).  The seven `this tactic
  is never executed` warnings (`:431`–`:468`) are the failed statement's proof-progress
  fallout.  All of it lifts with the one error.

The trajectory 5 → 12 → 9 → 2 → 1 now reads as the loop's designed convergence — every
wave since 8 killed exactly its targeted seam — and the last error is a one-line
witness-typing defect: the surgical-est possible target.

## Wave 10 (`de5541c`, committed 2026-11-16 02:07:16Z) — the one-line denominator fix

**+10/−6 lines in `GSTTwelvePointWorldCarrier.lean` only** (748 → 752 lines; no sibling
touched, zero mathematics changed).  Two repairs, both aimed at run 9's single error:

1. **`chartRingMap_apply`'s statement pins the `mk'` denominator's submonoid**
   (`:319-324`) — `IsLocalization.mk'` now takes `(M := Submonoid.powers
   (sectionRingHom (MvPolynomial.X j)))` and `(S := Localization.Away (sectionRingHom
   (MvPolynomial.X j)))` by name, and the membership witness is
   `(Submonoid.mem_powers_iff _ _).mpr ⟨k, rfl⟩` — **Mathlib's own `Away`-fraction
   idiom** (the pinned `RingTheory/GradedAlgebra/HomogeneousLocalization.lean:795/854`
   writes exactly `Localization.mk _ ⟨x ^ i, (Submonoid.mem_powers_iff _ _).mpr
   ⟨i, rfl⟩⟩`): the witness carries the EXPONENT `k` with `rfl`, so `mem_powers`'s
   implicit generator unifies with `f` itself, the Subtype elaborates as `powers f`,
   and the instance search that killed run 9 never starts.
2. **The `j = 1` branch restructure** (`:466-480`) — `section_X_one`'s rewrite moves
   AFTER the `eq_iff_exists` witness (the early `rw [section_X_one, one_pow, one_pow]`
   would clash with the now-explicit `S :=` before the iff); the `mk'_eq_iff_eq'` and
   `eq_iff_exists` witnesses carry the unit multiplier explicitly (`x := sectionRingHom
   p * f₁ ^ N`, `y := y * f₁ ^ M`), and one `simp only [Subtype.coe_mk, section_X_one,
   one_pow, one_mul, mul_one]` collapses the multiplier at the end.

Every region that runs 8 and 9 left dead stays untouched — the fix is surgical by
construction: one statement retyped, one branch reordered.  **Run 10: verdict pending —
run 43790217021 at `de5541c`** (the workflow's run_number 10, API-confirmed), fired
2026-11-16T02:07:19Z, job 133046701984 (started 02:07:22Z), corpus cache restored, the
compile step in progress at this supplement's write time; on the run-8/9 cache-hit
profile (~15.5 min) the verdict is expected ~02:22–02:25Z.  AGENTS.md rule 7 stands: no
green claimed for the twelve-point lane until the run lands at the pushed SHA.

## Run 10 verdict (the W7-D dossier, adjudicated 02:23:54Z)

**Run 43790217021 FAILED** — job 133046701984, fired 02:07:19Z, completed 02:23:54Z
(**16m32s**, corpus cache hit; dossier `gst-recovery/w10d/`, durable log copy
`gst-recovery/w8f/run10_gst-twelve-point-native-world.log`).  **Exactly ONE error** —
the loop's whole-run trend closes its sixth point: **5 → 12 → 9 → 2 → 1 → 1** — a
second consecutive single-error run, and the error moved INSIDE the wave-10 statement's
own proof: the wave-10 statement fix itself elaborated clean, and everything else in the
wave-9/10 repair held.

* **The error** — `GSTTwelvePointWorldCarrier.lean:347:4`, `Tactic 'rewrite' failed:
  motive is not type correct`: the `rw […, Subtype.coe_mk, map_pow]` tail of
  `chartRingMap_apply`'s proof — the file's last never-elaborated tactic sequence.
* **W7-C's prediction — made while the run was in flight, hit EXACTLY.**  The static
  audit of the wave-10 patch forecast with 85% confidence that the lane's residual
  would land at exactly `347:4`, and named the mechanism: the transported
  `mk'`-denominator's membership proof mentions the coerced constructor `↑⟨X j ^ k, ⋯⟩`,
  so `rw`'s kabstract cannot abstract the occurrence without breaking the motive.
  Location AND mechanism called before CI spoke — the static-audit + pinned-atlas
  discipline of waves 8–11 now PREDICTS the elaborator, not just explains it.
* **The `j = 0` / `j = 1` clearance** — the wave-9 surjectivity rebuild's two chart
  branches (the round's designated prime suspects, never before elaborated) passed
  CLEAN on first exposure; their only signals are four cosmetic `simp argument is
  unused: Subtype.coe_mk` linter warnings (`:433/:441/:470/:479`) — an incidental
  in-run CI proof that the `simp only` idiom discharges exactly the coercion shape
  wave 11 would need.
* **The receipts at `de5541c`** — `twelvePoint_smooth` (:744), `section_hf` (:745),
  `span_cover` (:746), `twelvePoint_over_base` (:748), `twelvePoint_coheight` (:749)
  clean; the `sorryAx` taint exactly the two known error-recovery receipts
  `twelvePoint_closedImmersion` (:747) and `twelvePointWorld` (:750), both downstream
  of the one error.

## Wave 11 (`a5f1c5b`, committed 2026-11-16 02:42:10Z) — the proof-dependent tail rides simp's congruence

**+14/−8 lines in `GSTTwelvePointWorldCarrier.lean` only** (752 → 758 lines; no sibling
touched, zero mathematics changed; commander-executed on the 18-minute turnaround after
the run-10 verdict — the W2-C/W6 takeover pattern, now standing practice; the design
seeded by W7-C's static audit).  The one-idiom kill:

1. **The spine SPLIT** — the five PROOF-INDEPENDENT rewrites (`h1`,
   `HomogeneousLocalization.algebraMap_apply`, `HomogeneousLocalization.Away.val_mk`,
   `Localization.mk_eq_mk'_apply`, `IsLocalization.map_mk'` — every one CI-proven in
   run 10) stay `rw`; the PROOF-DEPENDENT pair (`Subtype.coe_mk`, `map_pow`) moves to
   `simp only […]` — simp's congruence machinery REBUILDS the Subtype and discharges
   the proof difference by proof irrelevance, exactly where `rw`'s motive check must
   fail.  The precedent, twice over: the same idiom carried the four `Subtype.coe_mk`
   simp-normalizations in the chart branches (CI-proven in run 10 itself), and it is
   Mathlib's own endgame for exactly this composite
   (`ProjectiveSpectrum/Basic.lean:483-485`, the W5-B dossier's pinned lines).
2. **The zero-goal-safe closer** — `all_goals rfl`, vacuous if the `simp only` already
   closed the goal by proof irrelevance.

Run 11 — **43793762987**, the workflow's run_number 11 — fired 02:42:13Z; its verdict is
the W9-G supplement at this record's end.

## The PREPARED green verdict — VOIDED (run 10 RED; retired by this supplement)

W6-D's prepared green-verdict paragraph — placeholder-gated (`[RUN_ID]`/`[SHA]`/
`[VERDICT-TIME]`, nothing claimed, finalize-on-green / void-on-red by its own banner
rule — W7-D's placeholder discipline) — was VOIDED by the run-10 RED: run 43790217021
did not close the loop, and run 11's verdict moved the lane's residual one module
downstream.  The draft is retired from this record rather than left banner-gated in
place: a stale green-verdict paragraph is a finalization hazard, and its
"5 → 12 → 9 → 2 → 1 → 0" trajectory now belongs to the CARRIER-INTERNAL view — the
loop run 11 actually closed — while the whole-run count moved to 20.  The discipline
stands for the NEXT green path, whenever the downstream chain closes: a FRESH prepared
paragraph from that round's records wave, its receipts pulled from the artifact bodies
(`twelvePoint_law`, `twelvePointCertificate`, `twelvePointCertificate_isKrylovCyclic`,
`twelvePoint_FS`, `twelvePoint_everyHodge`, `the_twelve_point_native_world_package` —
none of which exist in any run to date), never from a draft.  (The dashboard's emerald
path — the mechanical side of the green path — was dry-run-proven by W8-G and stands
ready; the honest-scope paragraph the draft carried is governed by the 2026-11-14
record's disclosure and non-claims, unchanged.)

---

## Run 11 verdict (W9-G supplement, 2026-11-16, written at HEAD `a5f1c5b` from the W8 dossiers) — the carrier-clean cascade

**Run 43793762987 FAILED — the best red of the campaign.**  Job 133057820846, fired
02:42:13Z (job start 02:42:16Z), completed 02:59:02Z — **16m46s** wall (the compile step
02:43:55→02:58:57, 15m02s across the full ~8969-target graph, the corpus cache
restored; artifact 14194495768).  The two views close together:

* **Whole-run trend: 5 → 12 → 9 → 2 → 1 → 1 → 20.**
* **Carrier-internal trend: 5 → 12 → 9 → 2 → 1 → 1 → 0 — the eleven-wave carrier
  repair loop is CLOSED**, and the build advanced past the carrier for the first time
  in eleven runs (tier 1 of 6 closed; the tier table below).

### The carrier is clean — the first clean elaboration in the lane's history

`GSTTwelvePointWorldCarrier.lean` BUILT (`[8728/8969]`, 7.6s) with **zero errors and
zero `sorryAx`**, and all seven receipts print the three standard axioms only —
`[propext, Classical.choice, Quot.sound]` (run-11 log `:1215-1221`):
`twelvePoint_smooth` :750, `section_hf` :751, `span_cover` :752,
`twelvePoint_closedImmersion` :753, `twelvePoint_over_base` :754,
`twelvePoint_coheight` :755, `twelvePointWorld` :756.  The runs-8-10 `sorryAx` taint
(the `twelvePoint_closedImmersion`/`twelvePointWorld` error-recovery receipts) is GONE.
The wave-11 design held to the letter, and its own linter receipts are the proof:
`:348:2` `'all_goals rfl' tactic does nothing` — the closer VACUOUS, because the
`simp only [Subtype.coe_mk, map_pow]` had already closed everything by proof
irrelevance, exactly as designed — and `:347:13` the `Subtype.coe_mk` simp argument
unused (only `map_pow` was needed).  The module's remaining signals are cosmetic lints
only (unused simp args, never-executed `first` fallbacks, a `haveI`→`have` hint).

### The cascade moved one module deeper — first exposure, twenty authoring defects

The build then advanced, for the first time in the lane's eleven runs, PAST the
carrier: `GSTTwelvePointAnalytification.lean` at `[8817/8969]` — the file's
**FIRST-EVER elaboration** (run 10's log carries zero mentions of it; every prior run
died in the carrier at `[8727/8728]`) — and died there in 5.5s with **20 errors**,
every one a 2026-11-14 authoring defect that had waited, masked, behind four sessions
of carrier bleeding.  It is the carrier's only importer.  Downstream
`GSTTwelvePointCohomology`, `GSTTwelvePointHodgeData`, `GSTTwelvePointFoldWord`,
`GSTTwelvePointLawLanding`: zero mentions — never attempted, still never CI-proven.
The capstone receipts (`twelvePoint_law`, `twelvePointCertificate`,
`twelvePointCertificate_isKrylovCyclic`, `twelvePoint_FS`, `twelvePoint_everyHodge`,
`the_twelve_point_native_world_package`) DO NOT EXIST in this run, and the `sorryAx`
hard-fail gate was never reached (the build exited 1 first).

### The 20 errors — five clusters (wave 12's target list)

All sites at `a5f1c5b`, all in `GSTTwelvePointAnalytification.lean` (full bodies:
`gst-recovery/w8f/run11_gst-twelve-point-native-world.log` and the `w8a`/`w8d`/`w8e`/
`w11b` dossier copies).  The disjoint receipt partition (W8-D's census): 6
ghost-cascade + 8 `Pi.single` seams + 1 instance + 1 rw-motive + 1 unsolved-goals
cascade + 1 flipped `Ne` + 1 function-application + 1 misapplied-`Injective` = 20.  The
five attack clusters (the wave-12 framing, overlapping in sites):

1. **The `Pi.single` family — ~14 sites, one idiom.**  The ghost pair
   `single_mul_single_self`/`single_mul_single_ne`: declared at `:217`/`:225`, but
   their STATEMENTS die in the implicit-β seam, so neither ever materializes as a
   constant — and the six-site cascade follows (`:253:35`/`:268:10` unknown
   identifier in `pi_decomp`'s support proofs; `:408:7`/`:409:7` the `#check`
   receipts; `:423:14`/`:424:14` the `#print axioms` receipts).  Plus the eight
   implicit-β seams proper (`:131:69`, `:133:14`, `:136:8`, `:218:60`, `:226:38`,
   `:295:54`, `:361:22`, `:365:9`): `Pi.single k (1 : ℂ)` elaborating against a
   function-typed metavariable (`1 : ℂ` expected `?m k`) because the statements carry
   no expected function type.  **The kill:** statement-level type ascriptions (the
   `(Pi.single k (1 : ℂ) : Fin 12 → ℂ)` shapes) + the REAL pinned `Pi.single`
   arithmetic API in place of the guessed names (`Pi.single_apply`,
   `one_mul`/`zero_mul`, the `Finset.sum_apply` family) — a NEW `w2f`-style pinned
   dossier for `Pi.single`/`Finset.sum_apply`/`Fintype` ground truth; the real lemmas
   exist at the pin, the authoring guessed wrong names.
2. **The `pi_decomp` elaboration — ~8 sites (six shared with cluster 1, one with
   cluster 5).**  The standard-basis identity `pi_decomp : ∑ k : Fin 12,
   algebraMap ℂ (Fin 12 → ℂ) (x k) * Pi.single k (1 : ℂ) = x` (`:130-136`) does not
   elaborate as written, and every pointwise re-elaboration of it inherits the
   breakage: the `hsum` re-elaboration (`:133/:136`), the two `single_mul_single_*`
   statements (`:218/:226`), `sum_single_eq_one` (`:241`), `complexPoint_eq`
   (`:295:35` — the ext-depth break, `x : Fin 12` applied at `k` — and `:295:54`).
   **The kill:** restate on the pinned `Finset.sum_apply` spine with explicit
   `funext`/`RingHom.ext` depth; never re-elaborate the decomp identity bare.
3. **The `:184:12` rw motive — the wave-11 disease class, one site.**  The
   proof-dependent `rw [hs, Spec.preimage_map]` in `section_h_algebraMap` (the `↑f`
   Subtype-coercion seam: `Spec.preimage ↑f` vs `Spec.preimage (f ≫ _)`) — the same
   proof-dependent-rewrite class as the carrier's `:347:4`, now in the analytic
   direction.  **The kill:** the wave-11 idiom (the proof-dependent pair to
   `simp only`), CI-proven five times over (the four chart-branch normalizations in
   run 10 + the carrier tail in run 11).
4. **The `:66:2` `TotallyDisconnectedSpace ↥twelvePointSpace` instance — one site.**
   The instance declaration EXISTS — it is its own `inferInstance` proof that fails
   (the docstring's claimed `TopCat.str → DiscreteTopology → TotallySeparatedSpace →
   TotallyDisconnectedSpace` chain does not fire at the pin; the `#check` receipt at
   `:397` is one of the cascade's casualties).  An instance-form defect, not a
   missing fact.  **The kill:** prove it explicitly (the discrete-`Fin 12` route) or
   `haveI` it at the use site.
5. **The trivial shapes — three sites.**  `:241:2` the `Pi.one` shape (`∑ x,
   Pi.single x 1 = fun x => 1` against the goal's `= 1` — kill by `funext`/
   `Pi.one_def`); `:284:21` the flipped `Ne` (`hkj : ¬j = k₀` passed where `k₀ ≠ j`
   is expected — kill by `ne_comm`/`Ne.symm`); `:379:39` the misapplied
   `pointSection_injective` (a `Function.Injective` Prop applied as a function, in
   the `Equiv.ofBijective` witness — kill by `fun i j hij => pointSection_injective
   hij`).

### The receipts census (W8-D, the deep verify)

The full 1,801-receipt census of the run-11 artifact: **1,793 clean** (1,484
`[propext, Classical.choice, Quot.sound]` + 245 `[propext, Quot.sound]` + 61
`[propext]` + 2 `[Quot.sound]` + 1 `[Classical.choice]`) and **exactly 8 `sorryAx` —
ALL in `GSTTwelvePointAnalytification.lean`**, every one the known error-recovery
fallout of the 20 errors: `pi_decomp` :419, `section_h_algebraMap` :420,
`sectionRingHom_comp_algebraMap` :421, `sectionRingHom_algebraMap_apply` :422,
`sum_single_eq_one` :425, `sectionRingHom_single_one` :426, `complexPoint_eq` :427,
`pointSection_injective` :428 — the taint lifts with the errors.  The module's clean
receipts: `eval_comp_algebraMap` :417, `pointSection_section` :418.  The green corpus
re-verified clean in the same run (every `GSTNativeSingleFoldOrbitLawLanding` receipt,
`gst_FS_of_native_law` at :633 included).  Zero `declaration uses 'sorry'` warnings —
the 8 taints are elaboration-recovery, not literal `sorry` tactics.

### The structural finding (W8-E's claim audit): a serial build graph, six tiers, five never elaborated

The lane's build target is `lake build GSTTwelvePointLawLanding`, and the six modules
form a strict serial import chain (verified on disk at `a5f1c5b` — each module imports
only its predecessor):

| tier | module | lines | status after run 11 |
|---|---|---|---|
| 1 | `GSTTwelvePointWorldCarrier.lean` | 758 | **CLOSED — clean, 7/7 receipts green** |
| 2 | `GSTTwelvePointAnalytification.lean` | 432 | **first exposure run 11 — 20 errors** |
| 3 | `GSTTwelvePointCohomology.lean` | 378 | never elaborated (zero log mentions, all 11 runs) |
| 4 | `GSTTwelvePointHodgeData.lean` | 349 | never elaborated |
| 5 | `GSTTwelvePointFoldWord.lean` | 722 | never elaborated |
| 6 | `GSTTwelvePointLawLanding.lean` | 384 | never elaborated — the build root and the law-discharge site |

Two corrections to the record's earlier framing follow:

* **Never-reached ≠ clean.**  This record's wave-7 parenthetical "(the five sibling
  modules clean)" — corrected in place above — was wrong: the run-7 build stopped at
  the carrier, so no sibling ever received a verdict.  W8-E's run-7 baseline
  comparison (`gst-recovery/w8e/run7/`) confirmed zero log mentions for all five
  siblings in the wave-7 log, and run 11 proved the point the moment the first
  sibling was reached: twenty authoring defects on first exposure.  The same
  correction governs every "the sibling modules are clean" reading of runs 4–10:
  the siblings were UN-REACHED, full stop.
* **The lane's green is four first-exposure waves away, not one fix away.**  Run 11
  closed tier 1 of 6.  Tiers 3–6 have never been elaborated by any run — the
  2026-11-14 authoring was never CI-compiled end-to-end — so each is expected to
  surface its own first-exposure mass.  Budget a wave per MODULE, not a wave per
  lane; the law's first live-weight kernel discharge (`NativeGSTSingleFoldOrbitLaw
  twelvePointWorld twelvePointHodgeData`) is downstream of all four.

### The W8 agent accounting (the verdict round; corrected by this pass)

Seven agents; five delivered, two died at context deadlines — the dead agents' owed
record deliveries are completed by this W9-G supplement and the worklog's W9 section:

* **W8-A — verdict watch: DELIVERED** — run 11 located, polled to completion
  (02:59:02Z), the artifact pulled (14194495768) and the error dossier compiled
  (`gst-recovery/w8a/`: the 20-error table with clusters, the receipts, the
  lanes-at-`a5f1c5b`, the wave-12 proposal).
* **W8-B — records finalizer: DEAD (context deadline)** — its dossier copy landed
  (`gst-recovery/w11b/`), but the owed deliverable — this record's Run-10-verdict /
  Wave-11 / Run-11 supplements — was never written; the worklog's W8-round claim
  that they "ride the working tree" was false (the working tree's record ended at
  the W7-D supplements, verified against `git status` by this pass).  This
  supplement completes the delivery.
* **W8-C — data + dashboard: DELIVERED** — `campaign-data/campaign.json` closed at
  the run-11 verdict (the wave-10 `ciOutcome`, the wave-11 row with the verdict,
  `liveStatus` RED at `a5f1c5b`; scripts `gst-recovery/w11d/w8c_phase{1,2}.py`),
  re-verified sound by this pass (the wave row and liveStatus match the artifact
  receipts exactly; no fix needed); the dashboard verified end-to-end with the red
  banner.
* **W8-D — receipts deep-verify: DELIVERED** — the full 1,801-receipt census
  (`gst-recovery/w8d/W8D_VERDICT.md` + the independent artifact pull): the carrier
  7/7 clean, the 8 `sorryAx` all in the analytification, the capstone receipts
  nonexistent, the whole-corpus axiom-set table.
* **W8-E — final claim audit: DELIVERED** — the honest state: THREE standing green
  fronts (spanning `06c1037` run 43747935402, landing `2378003` run 43750693353,
  part1-chow-transfer `db97399`) and the twelve-point's honest label —
  **tier-1-clean, NOT green** (per AGENTS.md rule 7 the carrier compiled clean
  within a FAILED run; only the artifact receipts attest it, no green run is
  cited); plus the independent artifact pull and the run-7 baseline comparison
  (`w8e/run7/`) that grounded the serial-tier finding and the never-reached ≠
  clean correction.
* **W8-F — worklog finalizer: DEAD (context deadline, mid-pass)** — its bulk landed
  before death (the worklog's run-10/wave-11 round accounting, the W8 round and
  FINAL STATE sections, `RECOVERY.md`'s final asset map, the durable log copies
  `gst-recovery/w8f/` — all verified on disk by this pass), but the pass never
  closed: its sibling-agent accounting asserted W8-B's delivery unverified (false),
  and the owed wave-12 cluster plan was never written.  The worklog's W9 section
  corrects the one and completes the other.
* **W8-G — final surface verifier: DELIVERED** — the dashboard verified end-to-end
  against the verdict (the red banner for run #11 / 43793762987, the emerald path
  inert and dry-run-proven, the responsive/interactive matrices PASS,
  `bun run lint` PASS), plus the one mobile-overflow fix (the header meta line).

### Wave 12 prepared — the attack plan

From the artifact bodies (`gst-recovery/w8f/`, the `w8a`/`w8d`/`w8e`/`w11b`
dossiers), not from guesses.  Order of attack: **(1)** the ghost pair first — the new
`w2f`-style pinned dossier for the `Pi.single`/`Finset.sum_apply`/`Fintype` API, the
two lemmas restated on the real pinned names with statement-level ascriptions (kills
cluster 1's six-site cascade + its eight seams, and un-blocks cluster 2's
re-elaborations); **(2)** the `pi_decomp` spine rebuild on `Finset.sum_apply` with
explicit funext depth; **(3)** the `:184:12` proof-dependent `rw` → the wave-11
`simp only` idiom; **(4)** the `:66` instance proved explicitly; **(5)** the three
trivial shapes (one-liners).  Then expect tier 3 (`GSTTwelvePointCohomology`) as the
next first-exposure mass — the cadence continues until the chain closes, and the
carrier's own history is the planning law: on the first big mass, expect a
root-cause kill (a `w2f`-style dossier + a transcription repair), not a symptom
patch.

**Scope unchanged (AGENTS.md):** the twelve-point lane remains a RESTRICTED,
zero-dimensional discharge lane — on a 0-dimensional space
`EveryHodgeClassIsRationalAlgebraic` carries no transcendental content; native ⇒ typed
only (no typed ⇒ native transport exists anywhere in the repository); and the law's
first live-weight kernel discharge remains kernel-unadjudicated until
`GSTTwelvePointLawLanding` compiles green in a run at its own pushed SHA.  No green is
claimed for the twelve-point lane at any SHA; the carrier's clean compilation is
attested by run 11's receipts alone.
