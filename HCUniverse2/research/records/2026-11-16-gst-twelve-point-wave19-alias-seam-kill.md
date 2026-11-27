# 2026-11-16 — The twelve-point wave 19: the alias-seam kill — exact at default transparency, the cohomology's eight, and the first-contact insurance below

**Provenance:** W2-D, the records + verification-gates wave of the GST campaign's wave-19
strike session.  This is the round record for the nineteenth repair wave on the
twelve-point native geometric world, written at HEAD `8cb5b391` (the eighteenth-wave
commit, whose CI adjudication — run `43871161014`, RED, 8 errors, all in
`GSTTwelvePointCohomology.lean` — is this round's target) with the wave-19 edits landing
in the working tree IN PARALLEL: W2-A on the cohomology patch (the four theorems
`dualCochains_d_even`/`_odd`, `dualSc_exact_odd`/`_even`), W2-B on the pre-emptive bundle
(`GSTTwelvePointHodgeData`/`FoldWord`/`LawLanding`), W2-C on the Z3 re-certification
battery.  Every lemma name and line number cited below is the pinned Mathlib's
(`mathlib4` @ `51e6992efd06126df61a496bebf8f49482a4e129`); every run-18 error cite is at
`8cb5b391` file state.  No Lean kernel verdict is claimed for wave 19 at this record's
write time.  Zero mathematics changed — elaboration engineering only, the 2026-11-15
CI-loop record's disclosure standing.

## What this is

Tier 3 of the six-module serial chain (`GSTTwelvePointCohomology.lean`, first exposed run
16 with 20 errors) is mid-flight: waves 17 and 18 each killed their adjudicated target
lists (wave 17 the run-16 fifteen plus the tier-4 pre-exposure strike; wave 18 the seven
cited run-17 sites — `:171/:194`, `:213/:220`, `:324`, `:409`, `:432`), and run
`43871161014` at `8cb5b391` closed with **8 errors, all in the cohomology file, all in
the four d/dualSc theorems, all one disease class: rewrites asked to bridge type-spellings
that are only default-transparency defeq**.  The cohomology-internal trend reads
20 (run 16, first exposure) → the wave-17/18 kill lists → 8 (run 18) → wave 19 targets 0.

Wave 19 is two strikes in one push:

1. **The kill** — the eight run-18 errors die at the ROOT (an alias seam inside Mathlib's
   own `ModuleCat` API, plus the transparency class of every closer re-picked from `rw`
   to `exact`), not at the symptoms.
2. **The pre-emptive strike** — the first-contact insurance bundle for tiers 4–6
   (`GSTTwelvePointHodgeData`, `GSTTwelvePointFoldWord`, `GSTTwelvePointLawLanding`),
   which NO CI run has ever elaborated (they have sat behind the never-green cohomology
   since `1700138f`; run 18 never reached them — build-order verified from the run-18
   log).  The 2026-11-15 record's planning law governs: on the next first-exposure mass,
   expect authoring defects; the Wave-1 integration map of this session enumerated them;
   W2-B's bundle kills the certain ones before CI ever sees them.

## The run-18 error set — the eight, three clusters

All sites at `8cb5b391`, all in `GSTTwelvePointCohomology.lean` (CI run `43871161014`):

* **Cluster A — `:215/:241` — the `ModuleCat` alias seam, the round's root cause.**
  Both `dualCochains_d_even`/`_odd` proofs closed with `refine ModuleCat.Hom.ext (by rw
  [ModuleCat.hom_ofHom, ModuleCat.hom_zero/hom_id, …])`.  The `@[ext]` lemma
  `ModuleCat.Hom.ext` abstracts the PRIMED field `hom'` (`ModuleCat/Basic.lean:91-95` —
  the one-field structure's raw projection), while `ModuleCat.hom_ofHom`,
  `ModuleCat.hom_zero`, `ModuleCat.hom_id` are all stated through the UNPRIMED
  `Hom.hom` abbrev (`ModuleCat/Basic.lean:114-127` — the `ConcreteCategory`-level
  coercion alias).  The `rw` therefore never sees a lemma-pattern/goal-slot match at
  `rw`'s sub-default matching transparency; the semi-match it does get produces
  ill-typed motives — the run-18 "not type-correct under implicit transparency" notes.
  No `rw` discipline can bridge a primed/unprimed alias seam: the two spellings meet only
  at default transparency.
* **Cluster B — `:420/:424/:452/:457` — the transported `0`/`𝟙` carry the wrong
  hom-type spelling.**  In both `dualSc_exact_odd`/`_even`, the `hf`/`hg` haves rewrite
  with `dualCochains_d_even`/`_odd` then `ModuleCat.hom_zero`/`hom_id`.  The `rw`
  transport succeeds, but the `0`/`𝟙` it deposits carry the RAW d-slot hom-types
  (`X i ⟶ X j`, the alternating-complex object projections) while the `ModuleCat.Hom.hom`
  application's implicit object arguments are the `sc'`-projection types —
  `shortComplexFunctor'` is a plain `def`, so the two spellings are only
  DEFAULT-transparency defeq.  Dead for `rw`, alive for `exact`.
* **Cluster C — `:399/:431` — the `simp` closers' residue.**  The final closers
  `simp [LinearMap.range_zero, LinearMap.ker_id]` / `simp [LinearMap.range_id,
  LinearMap.ker_zero]` report `ker_id`/`range_id` UNUSED by the simp linter — the same
  instance mismatch at simp's matching transparency — leaving the residues
  `⊥ = LinearMap.id.ker` / `LinearMap.id.range = ⊤` unsolved.

## The kill (Wave 19) — W2-A's patch, live in the working tree

One transparency discipline, applied at every closer: **`exact` unifies at default
transparency — the same defeq class the CI-green `linearYonedaObj_d` `exact` haves
already exercised in runs 16–18 — and every `rw` whose pattern lives across an alias or
a plain-`def` projection is gone.**

1. **Cluster A rebuilt at the morphism level.**  The zero/identity is transported
   INSIDE `ModuleCat.ofHom`, at the `LinearMap` level: a self-contained `have` proves
   `Linear.leftComp ℚ rationalCoefficient 0 = 0` / `… (𝟙 …) = LinearMap.id` by
   `LinearMap.ext` + `Linear.leftComp_apply` (with `CategoryTheory.Limits.zero_comp` and
   `LinearMap.zero_apply` — `Linear.leftComp_zero` DOES NOT EXIST at the pin; the
   exhaustive `Linear/Basic.lean` read settled it, so the zero case is built, not
   named).  `ModuleCat.Hom.ext` is abandoned entirely — the alias seam is never entered.
   The closers: `exact ModuleCat.ofHom_zero` (`ModuleCat/Basic.lean:390`, an `rfl`
   lemma) / `exact ModuleCat.ofHom_id` (`:176`, `rfl`).
2. **Cluster B — the `.hom`-level haves KEPT, their interiors re-closed.**  The `have`
   statements were CI-typechecked at run 18 (their `shortComplexFunctor'_obj_f/g` +
   d-lemma rewrites are proven); only the closing `ModuleCat.hom_zero`/`hom_id` rewrites
   died.  They are now `exact ModuleCat.hom_zero` (`ModuleCat/Basic.lean:326`, `rfl`) /
   `exact ModuleCat.hom_id` (`:134`, `rfl`) after the two CI-proven rewrites — the
   transported `0`/`𝟙` unifies with the lemma pattern's `sc'`-typed spelling at default
   transparency.
3. **Cluster C — the `Eq.trans` chains.**  The final closers are
   `exact LinearMap.range_zero.trans LinearMap.ker_id.symm` (odd) /
   `exact LinearMap.range_id.trans LinearMap.ker_zero.symm` (even) —
   `LinearMap.range_zero` (`LinearMap/Range.lean:181`), `LinearMap.range_id`
   (`Range.lean:79`), `LinearMap.ker_id` (`LinearMap/Ker.lean:67`),
   `LinearMap.ker_zero` (`Ker.lean:130`), every implicit argument assigned FROM THE
   GOAL at default transparency.  The odd complex's chain is fully syntactic (range's
   codomain and ker's domain are both the `sc'` `X₂`-projection); the even complex's two
   `⊤`-sides meet at `↥(X (2*k+1)) =?= ↥(X (2*k+2))`, default-defeq through the
   alternating dual complex's degree-constant `X` — the same defeq run 18 already
   exercised when typechecking the `hf` statement.

## The pre-emptive strike (W2-B) — first-contact insurance, tiers 4–6

From the Wave-1 integration map: `GSTTwelvePointHodgeData.lean`,
`GSTTwelvePointFoldWord.lean`, `GSTTwelvePointLawLanding.lean` have NEVER been
elaborated by any CI run — they landed at `1700138f`, sat behind the never-green
cohomology through eighteen runs, and run 18 never reached them (build-order verified
from the run-18 log: the build died in tier 3; zero log mentions for all three).
First contact is therefore NOW one green tier away, and the 2026-11-15 record's
planning law — each first exposure surfaces its own authoring mass — applies.  The
bundle kills the enumerated certain failures before CI sees them:

* **`FoldWord:455` — the direction bug (certain failure):**
  `rw [LinearEquiv.symm_apply_apply]` where the goal shape wants
  `apply_symm_apply` (`e (e.symm x) = x`, not `e.symm (e x) = x`) — the rewrite can
  never match as written.
* **The `twelvePointPt` def/abbrev seam bridges — `FoldWord:466/:496/:673`:**
  `GSTTwelvePointHodgeData.lean:213` declares `def twelvePointPt` while
  `FoldWord.lean:80` and `LawLanding.lean:113` declare `abbrev twelvePointPt` — the
  wave-8 `twelvePointScheme` disease class, cross-file.  The bridge idiom (already
  CI-green in the landing file's own `seed` step): `show … from …` ground haves whose
  LHS elaborates in the USING file's `abbrev` scope — elaborator-level defeq on the
  from-term, syntactic match on the rewrite, no `kabstract` key mismatch.
* **The analytification-`(2*0)`-vs-`0` spelling-seam ground-have hoists — the
  LANDED sites `Landing:162` (hiso/hpt in `twelvePointSeed_coords`),
  `Landing:189` (hz in `twelvePointSeed_class_ne_zero`), `FoldWord:637`
  (hiso/hisosmul/hletter in `wordOp_pointClass`'s cons case), plus
  `module_decomp`'s own hsummap/hsmulmap/hpt hoists:** the ground lemmas
  (`zeroCycleClass_point` et al.) are stated at the literal-`0` spelling while
  the use sites carry the `2*0`/`(2*p)`-indexed analytification spelling — not
  syntactic, dead for `rw`; the hoisted haves pin the spelling at defeq before
  the rewrite.  (W3-B/W3-C audit verdict on the remaining register sites:
  `FoldWord:465/:494/:527` and `Landing:243/:291` were register
  FALSE-POSITIVES — metavar-headed rewrites inside author-stated goals that
  cross no seam — correctly left untouched.)
* **The `HodgeData:145-154` iSup-spelling bypass:** the `⨆ j ≠ i, (fun _ => ⊥)` iSup
  restatement of the pairwise-disjointness fact is a spelling the pin's iSup lemmas
  do not carry; the bypass closes it by `Subsingleton.elim` directly at the
  submodule level.

## Z3 re-certification

The battery ran in-session (agent W2-C); its verdict JSON
(`research/computations/gst_twelve_point_krylov_z3_battery_20261116_VERDICT.json`, Z3
5.4.1, timestamp `2026-11-16T14:19:40Z`) is the canonical artifact — the numbers
below are quoted from its final state.  **294 Z3 queries total: 293 core queries
ALL UNSAT + 1 SAT (the mod-5 divisor-witness probe — see below).  `overall_pass`
TRUE, `discrepancies` EMPTY.**

* **The determinant re-confirmed exactly** — `det K = −1149656584000` by three
  algorithms in the battery (fraction-free Bareiss on K and on Kᵀ, fraction Gaussian),
  all agreeing with the canonical constant (the 2026-11-15 record's four-algorithm
  W1-F verification stands).
* **The rational kernel is trivial** — the over-ℚ kernel-contradiction query is UNSAT,
  and **288/288 adjugate-identity queries UNSAT** (144 `adj·K = det·I` + 144
  `K·adj = det·I` contradiction probes, with the Python exact pre-check green).
* **The mod-p sweep: 12 primes, value-agreement at ALL twelve** — `det mod p` matches
  the canonical constant's reduction at every probe prime (3, 5, 7, 11, 13, 17, 19,
  23, 29, 31, 37, 41 — exact Python arithmetic); the Z3 mod-p kernel-UNSAT queries
  ran at the four primes 3/7/11/13 (all UNSAT).  Prime 5 is EXCLUDED from the kernel
  set: 5 | det (5³ exactly), so a nonzero mod-5 annihilator exists by mathematical
  necessity.
* **The one SAT — p = 5, and it is a divisibility CERTIFICATE, not a discrepancy:**
  the battery exhibits the nonzero mod-5 annihilator c = (0,0,1,1,3,3,1,1,4,3,1,0)
  of Kᵀ and Z3-VERIFIES it (verdict sat — the expected witness), positively
  certifying 5 | det with v₅(det) = 3, exactly as the canonical constant factors
  (−1)·2⁶·5³·149²·6473.  A prime dividing the determinant cannot certify
  invertibility — the battery excludes it from the kernel-UNSAT set and turns it
  into a divisor witness instead.  The claim under re-certification —
  `det K ≠ 0` over ℚ, the twelve orbit vectors span — is untouched; every
  kernel-queried prime returns UNSAT.
* **All table agreements PASS** — Twave vs the semantic operator, the owner-source
  table, the seed tables, the orbit-route matvec vs both the semantic action and the
  matrix powers, the orbit tables vs the Lean `Kvec`/`Cvec` tables, and the
  eleven-step lemma data (8/8 checks true); the supplementary certificate PASS
  (`certRowOf · Kᵀ = I`, the `ownerSource` null/max cell certificates).  Data sources
  pinned to the corpus lines in the JSON's `data_sources` block.

## The sorry-gate pre-check (W2-D, this record's own deliverable)

The lane's sorry gate is the workflow's own log grep
(`.github/workflows/gst-twelve-point-native-world.yml:69-70`: `declaration uses
'sorry'|sorryAx` in the CI log → hard fail).  The pre-check, run at `8cb5b391` + the
live W2-A patch in the working tree:

* **The six chain files — ZERO real `sorry`/`admit`/`native_decide`.**  Targeted grep
  of `GSTTwelvePointCohomology`, `GSTTwelvePointHodgeData`, `GSTTwelvePointFoldWord`,
  `GSTTwelvePointLawLanding`, `GSTTwelvePointWorldCarrier`,
  `GSTTwelvePointAnalytification`: the ONLY whole-word `sorry` hits are the files' own
  header disclaimers — `Cohomology:23`, `HodgeData:34`, `Analytification:32`,
  `Landing:72`, all prose inside comment blocks ("No `sorry`, no new axioms…");
  `FoldWord` and `WorldCarrier` have zero matches of any kind.  No `admit`, no
  `native_decide`, no `sorryAx` token anywhere in the six.
* **The sandbox gate (`scripts/sorry_check.sh`) reports 99 whole-word hits, exit 1 —
  ALL of them outside the twelve-point chain**: 67 genuine tactic `sorry`s, every one
  in the ten unregistered `GSTLawStackRound39`–`Round50` draft/shape-record files
  (the corpus's standing draft face, unchanged by this round), plus 32 prose mentions
  of the word inside comment/docstring headers.  This is the pre-existing repo state,
  not a wave-19 regression; the twelve-point lane's gate is the CI log grep, and the
  chain is clean under it.
* **The 19 receipts that go live when the eight die.**  Once the cohomology errors are
  dead and the build advances, the `#print axioms` receipts across the three receipted
  files become live gates for the workflow's grep: `Cohomology` 2
  (`twelvePointCohomologyIso`, `twelvePointCohomology_subsingleton`), `HodgeData` 8
  (`subsingleton_submodules_eq` … `twelvePointHodgeData_bigrading_pos`), `LawLanding`
  9 (`twelvePointSeed_coords` … `the_twelve_point_native_world_package` — the four
  capstones `twelvePoint_law`/`twelvePoint_FS`/`twelvePoint_everyHodge`/
  `the_twelve_point_native_world_package` among them).  Expected: all clean —
  `[propext, Classical.choice, Quot.sound]` — the same three-axiom set the carrier's
  seven receipts printed at run 11.  (`FoldWord` carries no receipts; `WorldCarrier`'s
  7 and `Analytification`'s 14 are already live and green since runs 11/15.)

## Agent accounting (the W2 wave)

* **W2-A — the cohomology patch:** the four-theorem rebuild (Clusters A/B/C), every
  closer re-picked to `exact` at default transparency, every pin verified against the
  pinned tree (the `ModuleCat/Basic.lean` primed/unprimed seam, `ofHom_zero`/`ofHom_id`
  at `:390`/`:176`, `hom_zero`/`hom_id` at `:326`/`:134`, the exhaustive
  `Linear/Basic.lean` read that killed the `leftComp_zero` guess).
* **W2-B — the pre-emptive bundle:** the four fix classes across
  `HodgeData`/`FoldWord`/`Landing` (above), from the Wave-1 integration map's
  first-contact enumeration.  (The agent hit the context deadline before its
  report; the edits landed complete and were audited post-hoc by W3-B/W3-C.)
* **W2-C — the Z3 re-certification battery:** in-session execution; the verdict
  JSON (final timestamp `14:19:40Z`) is quoted in full in the section above
  (294 queries: 293 UNSAT + 1 SAT-the-divisor-witness-at-prime-5).
* **W2-D — records + gates (this record):** the round record, the sorry-gate
  pre-check, the commit-message draft
  (`research/records/2026-11-16-wave19-commit-message.txt`), the INDEX entry.

## The W3 audit wave and its two kills

The four-agent adversarial audit wave (W3-A cohomology, W3-B FoldWord, W3-C
Landing+HodgeData, W3-D structural gate) ran over the full bundle.  Verdicts:
W3-A **SHIP** (zero blockers; every `exact` closer's defeq burden traced to
run-18-green code), W3-C **SHIP** (zero blockers; the R6/R2/R3 kills verified
forced-defeq or pure-syntax), W3-D **HOLD** on the record artifacts only (the
stale Z3 quote and the phantom site lists — both repaired in this record),
W3-B **FIX-FIRST** — and its two findings were killed before the push:

* **F1 (BLOCKER-class, pre-existing, first contact): `twelvePointFoldWord_op`.**
  The old script's `rw [module_decomp u]` rewrote `u` on BOTH sides of the goal,
  leaving the RHS's `iso (∑ …)` never sum-pulled — the single `map_sum` fired
  inside the LHS (`f := wordOp`), `foldWord_op_pointClass`'s pattern never
  appeared on the un-pulled RHS, and `Finset.sum_apply` could not match a
  coe-application: a certain first-contact CI error that both W2-B's register
  and W1-D's map missed.  **Killed:** the `conv_lhs` transport keeps the RHS
  intact (`M.mulVec (iso u)` — no sum on that side to pull); the LHS then runs
  module_decomp → map_sum → map_smul → foldWord_op_pointClass exactly as
  `module_decomp`'s own proof does.
* **F2 (RISK, pre-existing): `pointPairGeometry_realizes`, calc step 2.**  After
  `rw [key]` the two sides agree only by default-transparency defeq (the
  cycleClass-0 match-iota to `zeroCycleClass`) — rw's auto-rfl runs at reducible
  and would leave the step open.  **Killed:** the explicit `rfl` closes at
  default transparency.
* The audit also CONFIRMED the register's un-landed sites
  (`FoldWord:465/:494/:527`, `Landing:243/:291`) were false-positives
  (metavar-headed rewrites inside author-stated goals that cross no seam) —
  correctly left untouched.

## Disclosure and non-claims (exact scope)

* **No kernel verdict for wave 19 at this record's write time.**  The wave-19 push's CI
  run has not fired; no green is claimed for the twelve-point lane at any SHA
  (AGENTS.md rule 7).  The run-18 error inventory is run `43871161014`'s, at
  `8cb5b391`.
* The pre-check is STATIC — greps over the working tree, no Lean compilation claimed
  from this sandbox.  The wave-19 design's proof is the pending run, not this record.
* The pre-emptive bundle is insurance against the Wave-1 integration map's
  enumeration, not a claim that tiers 4–6 will elaborate clean on first contact —
  the map's own accounting expects an unenumerated residue.
* The Z3 battery's `overall_pass` flag is TRUE with empty `discrepancies` — the one
  SAT is the mod-5 divisor-witness probe, a prime dividing the canonical
  determinant (5³ | 1149656584000), positively certifying the divisibility — a
  divisor certificate, not a defect in the claim under re-certification.  The
  external evidence is not a Lean proof; the in-Lean certificate remains the
  Gauss-Jordan inverse table of the 2026-11-14 record.
* Zero mathematics changed: the construction, the lane, the lib registration, and the
  six-file path filter are the 2026-11-14 record's, untouched.  The twelve-point lane
  remains a RESTRICTED, zero-dimensional discharge lane; no typed ⇒ native transport
  exists anywhere in the repository.

## CI status

**Pending — wave 19 not yet pushed at this record's write time** (W2-A's cohomology
patch and W2-B's bundle are landing in the working tree in parallel; the commander
commits after the gates).  The lane's last adjudication is run `43871161014` at
`8cb5b391`: RED, 8 errors, all in `GSTTwelvePointCohomology.lean` — this record's
target list.  The session's standing greens are unchanged: the landing lane
(`43750693353` at `2378003`), the spanning lane (`43747935402` at `06c1037`), and the
part1-chow-transfer lane (`db97399`).  Tier 1 (carrier) closed at run 11; tier 2
(analytification) closed at run 15; tier 3 (cohomology) is this wave's kill; tiers 4–6
have never been elaborated by any run.
