# 2026-11-22 — The complete single-fold orbit law: the final composition capstone

## What this is

The four certified discharge routes of `NativeGSTSingleFoldOrbitLaw`
(`GSTHodgeSingleHypothesisConditional.lean:50`) merged into ONE complete
law, ONE complete consequence chain, and ONE master package.

New artifact: **`GSTCompleteSingleFoldOrbitLaw.lean`** (360 lines, 8
theorems, 2 proposition defs, zero sorry) — the final composition capstone.
Every proof is an exact composition of kernel-certified corpus theorems
(the Wave-62 discipline); no new mathematics below the composition itself.

## The four routes (the complete-domain ledger)

1. **ROUTE 1 — the unified native world family** (`complete_route_one_family`):
   the Wave-62 capstone `native_gst_unified_world_family_orbit_law` verbatim
   — every member of `NativeGSTWorld` (the `n+1`-point world at every `n`,
   run 44290094898; the twelve-point fold world, run 44182950667; unified
   run 44756915591 at 4188c31).  Unconditional, infinite family.
2. **ROUTE 2 — the live-core extension** (`complete_route_two_live_core`):
   the Wave-46 merged law through the Wave-62 restatement — ANY world with
   two Krylov-cyclic live certificates (weights 0, 1) and the stash
   bigrading at `p ≥ 2` (run 44545624743).
3. **ROUTE 3 — the one-line positive-dimensional world**
   (`complete_route_three_one_line`): the Wave-63 law verbatim (run
   44844378079 at 1cfb58f) — the honest one-sphere analytification with
   the honest sphere class and seeds assembles a genuine Hodge datum with
   the FULL law, the live weight-one witness, and exact Hodge.
4. **ROUTE 4 — the general-M finite-line world**
   (`complete_route_four_general_M`): the Wave-68 capstone body verbatim
   (run 44928010015 at dc31a62) — the FULL law at every `M ≥ 1` on the
   finite-line world with its frozen plug-in gates (world carrier,
   analytification receipt, honest seeds, M-cycle letters).

## The new theorem family

* `complete_route_one_family` / `complete_route_two_live_core` /
  `complete_route_three_one_line` / `complete_route_four_general_M` — the
  four routes as standalone theorems (Routes 2-4 with explicit named
  binders; Route 4 keeps the green module's `[NeZero M]` instance
  discipline and the `‹_›` assumption-resolution spelling verbatim);
* `NativeGSTCompleteLawDomain` / `NativeGSTCompleteConsequence` — the
  complete-domain propositions (each giant stated exactly once; the def
  architecture avoids transcription duplication);
* `native_gst_single_fold_orbit_law_complete` — THE COMPLETE LAW: all four
  routes in one theorem (Route 4's conjunct carries `hM : NeZero M`
  explicitly, discharged into the green theorem's instance binder by
  `haveI`);
* `native_gst_single_fold_orbit_law_complete_consequences` — the complete
  consequence chain: exact Hodge + finite rational combination for ANY
  world carrying the law (the repository's conditional chain), exact Hodge
  family-wide, the native⇒typed FS bridge at every member and weight, and
  the no-free-lunch nonzero algebraic seed at every member (all Wave-62
  theorems consumed verbatim);
* `the_complete_single_fold_orbit_law_package` — the master receipt: the
  complete law ∧ the complete consequences ∧ the family's infinitude.

## The citation ledger (every consumed name, kernel-verified home)

* `native_gst_unified_world_family_orbit_law`, `_exactHodge`, `_FS`,
  `_nonzero_seed`, `native_gst_unified_family_live_core_extension`,
  `NativeGSTWorld_fin_injective`, `NativeGSTWorld` (+carrier/hodgeData) —
  GSTUnifiedNativeWorldFamilyLaw.lean (CI-green run 44756915591);
* `positive_dimensional_live_weight_law` —
  GSTPositiveDimensionalLiveWeightLaw.lean (CI-green run 44844378079);
* `native_GST_single_fold_orbit_law_finiteLine`, `finiteLineHodgeData` —
  GSTFiniteLineGeneralMLaw.lean (CI-green run 44928010015 at dc31a62);
* `finiteLineScheme` (abbrev :65) / `finiteLineStructureMap` —
  GSTFiniteLineWorldCarrier.lean;
* `spherePointClassWorld` / `sphereComponentClass` —
  GSTPositiveDimensionalLawLanding.lean;
* `cyclicPred` — GSTSphereCycleLegs.lean;
* `sphereUnionSpace` / `unitSphereType` (abbrevs :169/:161) —
  GSTSphereUnionComponents.lean;
* `singularCohomologyOf` (abbrev :66) — GSTSingularCohomologyMaps.lean;
* `codimensionCycles` (Stage2D :42) — GSTGeometricRealizationStage2D.lean;
* `AnalytificationData` / `RationalSingularCohomology` —
  GSTGeometricRealizationStage2F.lean;
* `RealizedFiniteClosedCorrespondence` —
  GSTClassicalHodgeRealizedClosedCorrespondenceAlgebra.lean;
* `RealizedCorrespondenceKrylovCertificate` —
  GSTClassicalHodgeRealizedCorrespondenceKrylovFinale.lean;
* `stashBigrading` — GSTPositiveDimensionalLiveCoreKit.lean;
* `NativeGSTSingleFoldOrbitLaw` / `exactHodge_of_one_GST_fold_orbit` /
  `finiteRationalCombination_of_one_GST_fold_orbit` —
  GSTHodgeSingleHypothesisConditional.lean;
* `EveryHodgeClassIsRationalAlgebraic` /
  `EveryHodgeClassIsFiniteRationalCombination` —
  GSTClassicalHodgeExactClayStatement.lean;
* `GSTHypothesisComplete.GSTHypothesisData` —
  GSTHypothesisSpanningCompilerFace.lean (transitively).

## The open-list discipline

The module's opens are the Wave-68 module's CI-green-proven-compatible
list PLUS `GSTNativeCodimensionCyclePresentation` (Wave-62's own open)
and `GSTUnifiedNativeWorldFamilyLaw` (unique names only) — a superset of
a green combination; no two-namespace ambiguity is consumed anywhere
(the Wave-62 `deadFiber_subsingleton` ambiguity is never named).

## Static verification battery (this sandbox; kernel verdict at CI)

* Every consumed name point-verified in its home file (the battery log:
  30+ names, all resolve);
* Zero `sorry`/`admit`/`native_decide`/new axioms (the docstring mentions
  are the honesty ledger, not code);
* Brackets balanced; namespace/end and section pairing exact; every
  `#check`/`#print axioms` receipt target declared in-file;
* The four route signatures copied VERBATIM from the green modules
  (extraction pass against the source files before authoring);
* Route 4's `‹_›` spellings sit under the same binder discipline as the
  green module (instance binder at the theorem; explicit `hM` +
  assumption-resolution at the def conjunct).

## Registration

* `lakefile.toml`: new `[[lean_lib]]` block `GSTCompleteSingleFoldOrbitLawLib`
  (roots: the capstone + the four lane modules + the two wave-68.2 roots);
* CI lane: `.github/workflows/gst-complete-single-fold-orbit-law.yml`
  (elan v4.33.0-rc2, `lake exe cache get`, incremental-cache chain seeded
  from the general-M lane's key, `timeout 16800 lake build` of the six
  roots, sorryAx hard-fail, artifact upload; triggers on push to `main`
  and `research/gpt6-gst-hypothesis-part1-chow-square-20261110` plus
  manual dispatch; job timeout 300 min).

## CI status — THE KERNEL VERDICT: GREEN

**Run 44943810713 — completed success at 0399f08: `Build completed
successfully (8992 jobs)`** — zero errors, the sorry-gate silent, every
step green (checkout → toolchain → Mathlib cache → corpus restore →
THE COMPILE → artifact upload).  A second run (44943817514, the manual
dispatch at the same SHA) followed per the concurrency group.

The seven axiom receipts, verbatim from the kernel log (all the Lean
standard three — the corpus convention):

* `complete_route_one_family` → `[propext, Classical.choice, Quot.sound]`;
* `complete_route_two_live_core` → `[propext, Classical.choice,
  Quot.sound]`;
* `complete_route_three_one_line` → `[propext, Classical.choice,
  Quot.sound]`;
* `complete_route_four_general_M` → `[propext, Classical.choice,
  Quot.sound]`;
* `native_gst_single_fold_orbit_law_complete` → `[propext,
  Classical.choice, Quot.sound]`;
* `native_gst_single_fold_orbit_law_complete_consequences` → `[propext,
  Classical.choice, Quot.sound]`;
* `the_complete_single_fold_orbit_law_package` → `[propext,
  Classical.choice, Quot.sound]`.

THE COMPLETE SINGLE-FOLD ORBIT LAW IS KERNEL-CERTIFIED.
