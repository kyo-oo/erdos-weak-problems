# 2026-11-23 — WAVE 5: THE HODGE-DATA UNBLOCK — the import cascade, the honest-data rebuild, the Riemann nine-site kill

Written by W2-D (the record + audit agent) at HEAD 8e4d01b, branch
`research/gpt6-gst-hypothesis-part1-chow-square-20261110`. Three commits
landed this session — f8afaa9 (5-A, 00:10Z), 35aa0dc (5-B, 00:39Z),
8e4d01b (5-C, 00:46Z) — all `fix(gst)` waves of the unconditional round's
Task 1-6 assault (Wave 2 of the assault). Static verification only from
this sandbox (the ARSENAL law: no local Lean); the kernel verdict belongs
to CI at the pushed SHAs.

## What this is

The unblock round for the three red lanes of the finite-line assault:

* **GSTFiniteLineHonestHodgeData** (wave 4-B's module, never yet green):
  the 52-error import cascade killed at the root (5-A), then the 21-error
  type-mismatch family killed at the root by the concrete-world rebuild (5-B);
* **GSTFiniteLineWorldDischarge** (wave 3-H's module): the three missing
  `open`s that a runner death had masked (5-B);
* **GSTFiniteLineRiemann** (wave 3-A/3-B's module): the 12-error residue of
  run 45016808298 killed across nine sites (5-C);
* plus the lane-filter repairs (the analytification lane in 5-C; the
  unconditional-source lane repair riding the working tree).

## The run ledger (the wave's CI receipts)

* **The pre-wave-5 state** (the 8d9db2e era → the 22:xx pushes of Nov 22):
  the honest-hodge-data and cycle-correspondence lanes both died at the
  52-error cascade (`unknown namespace GSTFiniteLineOverBase` at :54:5, the
  `singularCohomologyOf` unknown-identifier family — the artifact logs at
  /home/z/ci-logs/hodge and /home/z/ci-logs/cycle carry 52 error lines each,
  50 of them in GSTFiniteLineHonestHodgeData.lean itself; every
  CycleCorrespondence-lane error was the import cascade).
* **The world-discharge lane's first run** (the 8d9db2e push, the wd
  artifact at /home/z/ci-logs/wd): the runner received a shutdown signal at
  13:49:42Z — exit code 143 — after 1h44m. The death MASKED a guaranteed
  red: the module never opened `GSTSingularCohomologyMaps`,
  `GSTSphereCycleLegs`, `GSTHodgeSingleHypothesisConditional`
  (`singularCohomologyOf`/`cyclicPred`/`NativeGSTSingleFoldOrbitLaw` were
  unresolved). Wave-5-A's defect class recurring — the masked-defect lesson
  is now in the campaign law: a lane that dies of infrastructure is NEVER
  assumed clean.
* **The Riemann lane history**: run 44969885834 (the 3-A draft, ~35
  errors) → wave 3-B (c5f198f) → **run 45016808298 failed at c5f198f**
  (the riem artifact at /home/z/ci-logs/riem — 12 error lines, 10 in
  GSTFiniteLineRiemann.lean, across the nine 5-C sites). The Riemann lane
  had never been green.
* **The f8afaa9 batch (wave 5-A's push)**: runs **45087184771 /
  45087184817 / 45087184755 all failed at f8afaa9** — the three lanes
  whose path filters carry `GSTFiniteLineHonestHodgeData.lean`
  (honest-hodge-data, cycle-correspondence, unconditional-source). All
  three died on the same 19-line error family in the module (the hodge2
  artifact at /home/z/ci-logs/hodge2 — the wave-5-B commit's ledger says
  21, the two extra being the sorry-recovery shadows on the two seed
  statements).
* **The 35aa0dc batch (wave 5-B's push) — IN FLIGHT** at the record's
  write time: honest-hodge-data, cycle-correspondence, world-discharge
  (re-triggered by its own module's `open` repair), unconditional-source.
* **The 8e4d01b push (wave 5-C) — IN FLIGHT**: the riemann and
  analytification lanes (the analytification lane fired on its own
  workflow-file change plus the Riemann path entry).

## Wave 5-A — the 52-error cascade root (f8afaa9)

One import + two opens, zero content changes: the module never imported
`GSTFiniteLineOverBase` (`finiteLineWorld` and its namespace were unknown —
every 'Function expected at' error of the 52-family was the cascade) and
never opened `GSTSingularCohomologyMaps`/`GSTPositiveDimensionalLiveCoreKit`
(`singularCohomologyOf`, `stashBigrading`, `spanBigrading` unknown — the
local instance bridges and the assembled bigrading could not elaborate).
The CycleCorrespondence lane's own module was already clean — all 50 of
its errors were this import's cascade.

## Wave 5-B — the honest-data rebuild + the discharge's masked defect (35aa0dc)

### The 19-error family at f8afaa9 (the hodge2 artifact, verbatim diagnosis)

* `:122:9` / `:174:9` — `failed to synthesize DecidableEq ↥(finiteLineWorld
  M).X` — the old atom proofs' `Finsupp.ext` route;
* `:129:4` / `:181:4` — `rewrite failed: pattern (Finsupp.linearCombination
  ?R ?v) fun₀ | ?a => ?c` not found in `((honestComponentLinear …) fun₀ | η
  => 1)` — the semireducible-def visibility disease (the rw could never see
  through `honestComponentLinear`), with the underlying
  `lineIndexOfGeneric M η` implicit-transparency note;
* `:201:11` / `:202:11` — THE ROOT: `honestCycleClassZero` is typed at the
  CONCRETE world (`codimensionCycles (finiteLineWorld M).X 0`) while the
  polymorphic-`V` field demanded `codimensionCycles V.X 0` — the
  type-mismatch family (the honest maps live at the actual world);
* `:237:4` / `:250:4` — the bridge applications: `lineHonestSeedZero M :
  codimensionCycles (finiteLineScheme M) 0` vs the expected `V.X`-typed slot
  (unifiable with nothing while `V` is a theorem-bound variable);
* `:260:8` / `:280:8` — the seed statements' `cycleClass` applications (the
  same `V.X`-vs-world root);
* `:281:11`/`:281:30`/`:286:5`/`:286:24`/`:288:7`/`:288:26`/`:292:26`/
  `:292:45` — `lineClosedPoint`/`lineClosedPoint_coheight` as autoImplicit
  poisons, and `:290:4` `Unknown identifier lineClosedPoint_component` —
  the wave-4-A renamed At-family (`lineClosedPointAt`/`_coheight`/
  `_component`) never propagated into this module.

### The rebuild (the root kills)

1. **The concrete-world restatement**: `finiteLineHodgeDataHonest` and every
   downstream theorem restated at `A : AnalytificationData (finiteLineWorld
   M)` (the `V` parameter deleted everywhere) — kills :201/:202/:260/:280/
   :237/:250 at the root (the seed-type unification now closes by the
   `rfl` receipt `finiteLineWorld_hWX` — `(finiteLineWorld M).X ≡
   finiteLineScheme M`, GSTFiniteLineOverBase.lean:339-340);
2. **The atom proofs rebuilt on the green `presentationOfNativeCycle_point`
   receipt** (GSTCompactNativeCyclePresentation.lean:61-79 — built green in
   the f8afaa9 run itself): the `Finsupp.ext` DecidableEq disease killed by
   `rw [presentationOfNativeCycleLinear_apply]; exact
   presentationOfNativeCycle_point …`, and the rw-visibility disease killed
   by the two defeq `show`-bridges that unfold `honestCycleClassZero` →
   `LinearMap.comp …` and `honestComponentLinear`/`honestPointLinear` →
   `Finsupp.linearCombination ℚ …` syntactically before the
   `rw [Finsupp.linearCombination_single, one_smul]` chain;
3. **The seed theorems restated on the At-family** (`lineClosedPointAt`,
   `lineClosedPointAt_coheight`, `lineClosedPointAt_component` — the
   wave-4-A renamed closed-point family) with the
   `⟨0, Nat.pos_of_neZero ‹_›⟩` Fin-literal discipline throughout.

### The discharge's masked defect

`GSTFiniteLineWorldDischarge.lean`: the three missing opens added
(`GSTSingularCohomologyMaps`, `GSTSphereCycleLegs`,
`GSTHodgeSingleHypothesisConditional`) — the exit-143 runner death had
masked this guaranteed red since the 8d9db2e landing. The module consumes
`finiteLineHodgeData` (the general-M choice-based data), NOT the honest
data — the rebuild's signature change touches nothing downstream.

## Wave 5-C — the Riemann nine-site kill (8e4d01b)

The 12-error residue of run 45016808298 (at c5f198f), every site one
family:

* `:186:8`/`:189:8`/`:192:8` — **the eq_northPole bullets**: the rw pattern
  `(↑v).ofLp 0` (the OfNat-literal spelling) could never match the goal's
  `(↑v).ofLp ⟨0, ⋯⟩` (the Fin-mk spelling) — the Fin-mk-vs-OfNat-literal
  mismatch killed by term-mode DEFEQ closes (`exact h0'` / `exact h1'` /
  `exact hv`);
* `:204:10`/`:218:10` — **the stale-Decidable-instance disease**: the
  first cancellation's `rw [if_pos/if_neg]` patterns could never match the
  def-elaborated ite instance — the theorem rebuilt on `split` (case-1 the
  pole-coordinate receipt, case-2 the congr-chain);
* `:270:6` — the `hd` nonvanishing rebuilt on the hfrac-route (the
  numerator-positivity by `nlinarith`, then `div_ne_zero`);
* `:273:17`/`:279:17`/`:286:18` — the three `coordToSphere`-application
  ascriptions parenthesized (`coordToSphere (some ⟨…⟩)` — the
  over-application parse: the bare `coordToSphere ⟨…⟩` elaborated the
  anonymous constructor against the codomain subtype);
* `:301:4` — the `riemannSphereEquiv` constructor's inverse-lemma ORDER
  corrected (`left_inv` is `coordToSphere_sphereToCoord`).

Plus the lane-filter repair: `gst-finite-line-analytification.yml`'s path
filter gained its own direct imports (`GSTFiniteLineRiemann.lean`,
`GSTGeometricRealizationStage2F.lean`) — a Riemann repair had never
re-triggered the analytification lane. The SAME repair for the
unconditional-source lane (+5 path entries: Riemann, Stage2F,
CompleteSingleFoldOrbitLaw, HodgeSingleHypothesisConditional, GeneralMLaw)
rides the working tree uncommitted at the record's write time — commit it
with the next push (the lane's stub imports exactly those five chains).

## The W2-D adversarial audit of the rebuilt GSTFiniteLineHonestHodgeData.lean

The full file at HEAD 8e4d01b audited against the seven mission points.
**VERDICT: PASS** (no predicted red found; five watch-items below).

1. **Claim-match — PASS.** Every docstring promise is present with the
   promised form: the honest maps (`honestComponentLinear` :100,
   `honestCycleClassZero` :110, `honestPointLinear` :147,
   `honestCycleClassOne` :159), the atom formulas (:120, :170), the
   assembled data (:202), the analytification/hone receipts (:220, :230),
   the world-bridges (:241, :255), the seed equations (:269, :296), the
   dead weights (:331), the six `#check` + three `#print axioms` receipts.
   The WAVE-5-B docstring addendum describes exactly the landed diff.
2. **The hone `rfl` — PASS.** `(finiteLineHodgeDataHonest …).hodgeBigrading
   1` iota-reduces to the match's 1-arm `spanBigrading (finiteLinePointClass
   M (finiteLineWorld M) A hspace ω) 1 (by omega)`; the theorem's RHS family
   `spherePointClassWorld (V := finiteLineWorld M) (H := …) M hspace ω`
   (GSTPositiveDimensionalLawLanding.lean:136-141) unfolds to
   `(Equiv.cast (rationalSingularCohomology_two_eq M hspace)).symm ∘
   spherePointClass M ω` while the arm's family unfolds to
   `(Equiv.cast (singularCohomologyOf_two_eq_of_hspace hspace)).symm ∘
   spherePointClass M ω` — the two cast-equations are proofs of
   defeq propositions (`RationalSingularCohomology A 2 ≡
   singularCohomologyOf A.space 2`: both are abbrevs — Stage2F:96-99,
   SingularCohomologyMaps:66-67, the `rfl` receipt
   `singularCohomologyOf_eq` at :79-81), so the casts are defeq by proof
   irrelevance; the `(by omega)` proofs are irrelevant; the `H` enters only
   through `H.analytification ≡ A`. The verbatim green receipt is
   `finiteLinePointClass_eq_world … := rfl` (GSTFiniteLineGeneralMLaw.lean:
   604-613, CI-green in the wave-68 run 44928010015). Supporting run
   receipt: the hone theorem elaborated clean even in the broken f8afaa9
   state (the hodge2 log's info receipt at :323).
3. **The seed theorems' `rw [hatom, hidx]` — PASS.** `hatom`'s LHS and the
   post-`show` goal are written with byte-identical anonymous-constructor
   spellings (the `⟨lineGenericPoint M ⟨0, Nat.pos_of_neZero ‹_›⟩,
   lineGenericPoint_coheight M ⟨0, …⟩⟩` and the `lineClosedPointAt` twin),
   elaborated in the same context with the same instance fvars — the rw
   pattern match is syntactic. The final `exact (honest_componentClass_eq_world
   … ⟨0, Nat.pos_of_neZero ‹_›⟩)` closes by defeq (the Fin-mk-vs-OfNat
   distinction is irrelevant to `exact`; the `hidx` RHS from
   `lineIndexOfGeneric_lineGenericPoint` (PointAlgebra:1326-1328) is the
   mk-form itself). The seed_one's `hcomp` is exactly
   `lineClosedPointAt_component` (PointAlgebra:1392-1395) at the 0-th line.
4. **The deadWeights match-on-p — PASS.** The tactic-level `match p with |
   0 | 1 | (q + 2)` inside the `have hbot … := by` generalizes the
   dependent `hp` correctly — the f8afaa9 run reported ZERO errors in the
   deadWeights region (the proof body is unchanged by the rebuild; the last
   module error of that run was :292:45, and the receipts' `info` lines ran
   to the file's end). The show-bridge `rationalHodgeSubspace (stashBigrading
   _ (2 * (q + 2))) = ⊥` elaborates: `stashBigrading`'s `VQ` slot is
   EXPLICIT (LiveCoreKit:216-218) — the `_` fills it by unification against
   the goal's `RationalSingularCohomology A (2*(q+2))`; the match arm's
   scrutinee `q + 2` whnf's through the offset-pattern iota to the third
   arm verbatim; `rationalHodgeSubspace_stash_eq_bot (q + 2) (by omega)`
   (LiveCoreKit:239-240, `VQ` implicit from the section variable) unifies
   against the show-form; `subsingleton_hodgeFiber_of_eq_bot hbot`
   (GSTNativeSingleFoldOrbitLawLanding.lean:173-175, `{V} {H} {p}` section
   variables) consumes `hbot` with V/H/p inferred from the goal.
5. **The atom show-cascades — PASS.** `Finsupp.linearCombination_single`
   EXISTS at the pin: the f8afaa9 error message at :129:4 displays the
   lemma's elaborated LHS pattern `(Finsupp.linearCombination ?R ?v) fun₀ |
   ?a => ?c` — the name resolved and elaborated as a rewrite rule (the
   failure was the pattern's semireducible-def invisibility, not
   resolution). The second `show` makes the goal's head syntactically
   `Finsupp.linearCombination ℚ (fun ξ => …)` applied to
   `Finsupp.single η 1`, so the `rw [Finsupp.linearCombination_single,
   one_smul]` chain now sees its pattern (the `one_smul` close is
   beta-defeq-safe for the rw's rfl-closer).
6. **The bridge applications — PASS.** The lemma signatures verified
   first-hand: `finiteLinePointClass_eq_world` / `finiteLineComponentClass_
   eq_world` (GSTFiniteLineGeneralMLaw.lean:604-627) take `(M) [NeZero M]
   (V) (A) (hspace) (ω) (Z₀) (hZ₀) (Z₁) (hZ₁) (j)` — the rebuild's
   term-mode applications `(M := M) (V := finiteLineWorld M) A hspace ω
   (lineHonestSeedZero M) (lineHonestSeedZero_ne M) (lineHonestSeedOne M)
   (lineHonestSeedOne_ne M) j` match the order and the implicit/explicit
   status exactly; the seed-type unification (`codimensionCycles
   (finiteLineScheme M) 0` vs `codimensionCycles (finiteLineWorld M).X 0`)
   closes by the `rfl` receipt `finiteLineWorld_hWX` (the world is the
   constructor `⟨finiteLineScheme M, …⟩` — the projection iota-reduces).
   The one place the rebuild relies on the elaborator's
   unfold-on-failure defeq rather than a verbatim green receipt: the
   lemma's conclusion carries `H := finiteLineHodgeData …` while the goal
   carries `H := finiteLineHodgeDataHonest …` — the two Hodge-data terms
   are NOT pairwise defeq (their `cycleClass` fields are the choice-based
   vs presentation-based maps), but the defeq check on the two
   `spherePointClassWorld`/`sphereComponentClass` applications unfolds the
   head constant on structural failure (Lean's lazy-delta defeq), where
   the H-dependence reduces to `H.analytification ≡ A` on both sides (and
   the cast-equations are proof-irrelevant at the defeq propositions) —
   the unfolded bodies coincide. Analysis-backed PASS (watch-item W2).
7. **CycleCorrespondence — PASS.** The module's §0-§1 residue receipts
   (the M-cycle endomorphism, the roundtrips, the residue-field-map
   bijectivity, the residue-weight-one) consume NO HonestHodgeData names
   (the import/open of the rebuilt module resolve — the namespace exists;
   the rebuild changed only signatures of names the correspondence module
   never mentions). The future GATE-L sections will consume the honest
   data at the new concrete-world signature — the first consumer of the
   changed type, flagged for the next wave.

### The watch-items (no predicted red; each with its adjudicator)

* **W1 (LOW-MEDIUM, wave 5-C)**: `Matrix.head_finqueue` at
  GSTFiniteLineRiemann.lean:203 — zero corpus-green receipts (its only
  occurrence in the 824-file corpus). If the name is absent at
  Mathlib v4.33.0-rc2: CI dies at :203 with `unknown identifier
  'Matrix.head_finqueue'` inside the `simp` set, killing
  `sphereToCoord_coordToSphere` and the Riemann lane. The adjudicator is
  the 8e4d01b riemann run (in flight). The wave-3-B receipt for the same
  evaluation (`Matrix.cons_val_two` + `Matrix.head_cons`, northPole's
  membership proof, no error in run 45016808298) suggests the name is
  redundant-but-harmless if it exists.
* **W2 (LOW, wave 5-B)**: the bridge theorems' H-mismatch defeq (point 6
  above) — analysis-backed, no verbatim receipt for the
  two-different-H-through-a-projection shape; adjudicated by the 35aa0dc
  honest-hodge-data run.
* **W3 (LOW, timing)**: the in-flight 35aa0dc runs check out the branch
  HEAD at checkout time (the workflows pin `ref: <branch>`, not a SHA) —
  if the unconditional-source run started before the 8e4d01b push, it
  builds 35aa0dc and dies on the still-broken Riemann import chain (the
  12-error family) — a timing artifact, not a repair defect; re-dispatch
  the lane at HEAD if it fires.
* **W4 (LOW, wave 5-B)**: the seed theorems' bare `= 0` RHS (the
  OfNat-(Fin M) literal) — synthesis is receipted (the f8afaa9 old
  seed_zero proof elaborated clean) but the literal is rw-blind; the
  rebuild consumes it only through `exact`-defeq, never through `rw` — no
  risk at the current shape.
* **W5 (INFO)**: the uncommitted `gst-finite-line-unconditional-source.yml`
  lane-filter repair (+5 paths) rides the working tree — commit with the
  next push.

## Registration (already in place — no changes this wave)

* `lakefile.toml`: `GSTFiniteLineHonestHodgeDataLib` (:1651),
  `GSTFiniteLineCycleCorrespondenceLib` (:1657),
  `GSTFiniteLineWorldDischargeLib` (:1592), `GSTFiniteLineRiemannLib`
  (:1639), `GSTFiniteLineAnalytificationLib` (:1663) — all registered with
  the right roots;
* CI lanes: `gst-finite-line-honest-hodge-data.yml`,
  `gst-finite-line-cycle-correspondence.yml`,
  `gst-finite-line-world-discharge.yml`,
  `gst-finite-line-riemann.yml`,
  `gst-finite-line-analytification.yml`,
  `gst-finite-line-unconditional-source.yml` — elan-v4.33.0-rc2 + Mathlib
  cache + `lake build` + sorryAx hard-fail + artifact upload.

## CI status — PENDING (the kernel verdict belongs to CI)

The 35aa0dc batch (honest-hodge-data, cycle-correspondence,
world-discharge, unconditional-source) and the 8e4d01b push (riemann,
analytification) are in flight at the record's write time. Expected
receipts if the batch lands green: `finiteLineHodgeDataHonest` +
`finiteLineHodgeDataHonest_seed_zero` + `finiteLineHodgeDataHonest_seed_one`
→ `[propext, Classical.choice, Quot.sound]` (the f8afaa9 run's
sorry-tainted receipts must turn clean); `riemannSphereEquiv`'s axiom
receipt on the Riemann lane; the discharge's
`native_GST_single_fold_orbit_law_finiteLineWorld` receipt. No green is
claimed for any lane at any SHA by this record (the AGENTS discipline).
