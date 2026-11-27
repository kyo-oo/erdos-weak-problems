# 2026-11-24 — WAVES 9-F..9-I: THE RUNNER-KILL CAMPAIGN — THE TIMEOUT LAW, THE MODULE-SPLIT LAW, THE IMPORT-LOAD CALIBRATION

Written by the commander (the round after BOSS's Task 3/4/6 completion
order), branch `research/gpt6-gst-hypothesis-part1-chow-square-20261110`,
SHAs `8605064` (9-F) → `50c6f19` (9-G) → `8dcb746` (9-H) → `58cb939f`
(9-I).  Static verification only from this sandbox (the ARSENAL law: no
local Lean); the kernel verdict belongs to CI at the pushed SHAs.

## What this is

The infrastructure campaign that un-stuck the three red lanes (Tasks 3+4,
6, 7 — written zero-sorry since `827f88b`, but never kernel-checked: every
CI run since `aec2180` died with logs lost).  BOSS's order: complete Tasks
3/4/6 unconditionally; verify all Tasks 1-6 against the original order.

## The diagnosis chain (each wave's receipts)

* **THE LOST-LOG ERA (`aec2180`)**: six re-dispatches, all jobs reaped at
  62-63 min with the compile step never concluding, logs `BlobNotFound`,
  ZERO banks saved since 01:05.  Root cause: `timeout 1200` without
  `--kill-after` — when lake resists SIGTERM (the real-compile state after
  the 9-E fixes), the timeout blocks forever; the runner's zombie-reaper
  force-fails the job at 62 min and nothing survives.
* **WAVE 9-F (`8605064`) — THE KILL-AFTER LAW**: `--kill-after=30s`, the
  window raised 1200→2400, live `tee` output, the else-branch orphan sweep
  (`pkill -KILL -x lean`).  RESULT: all four lanes MURDERED by the runner
  shutdown signal at 18:06/18:17/20:06/24:56 job-time — **the shutdown
  signal SKIPS `if: always()` steps** (GitHub law: a runner shutdown does
  not run remaining steps) — zero banks, zero artifacts, but the receipts
  landed in the job logs (the tee): the exit-143 deaths at 16-24 min of
  compile, mid-module, nothing banked.
* **THE MEASURED PHASES** (the corpus lanes' 7-minute greens vs the ratchet
  lanes' 22-minute timeouts): validate+replay ≈ 5-6 min; then each piece's
  elaboration is dominated by THE COLD IMPORT LOAD — every module imports
  the full `Mathlib` (~5 GB of oleans); the page-in on a cold 16 GB runner
  costs ~10-15 min BEFORE any proof checking starts.
* **WAVE 9-G (`50c6f19`) — THE MODULE-SPLIT LAW**: the four oversized top
  modules split into thirteen pieces (the module is lake's atomic banking
  unit — a mid-flight module banks nothing):
  `GSTFiniteLineCycleCorrespondence` (987) → Basic/Action/Operators/Letters;
  `GSTFiniteLinePointsGateCore` (807) → CoreBasic/CoreTransport/Core;
  `GSTFiniteLinePointsGateDischarge` (976) → Bridges/InverseA/InverseB/
  Discharge; `GSTFiniteLinePrimitiveXSource` (643) → Families/Source.
  Same namespace in every piece — the public API unchanged, the downstream
  importers untouched.  One docstring orphan at the InverseA/InverseB
  boundary repaired.  Nine piece libs registered; the four lanes' path
  filters carry the pieces.  RESULT: the four corpus lanes (point-algebra,
  analytification, honest-hodge-data, points-gate) re-certified GREEN at
  `50c6f19` — the split broke nothing; all four ratchet lanes concluded
  cleanly at ~12 min with banks landed (the first clean conclusions since
  `aec2180`) — but at 600s the pieces got zero seconds (the validate phase
  ate the window).
* **WAVE 9-H (`8dcb746`) — THE REPLAY-WINDOW RECALIBRATION**: 600→1200s.
  RESULT: three lanes concluded at ~22 min (banks landed), the pieces still
  incomplete — the cold import load exceeds the post-validate remainder.
* **WAVE 9-I (`58cb939f`) — THE IMPORT-LOAD CALIBRATION**: 1200→1800s, the
  page-cache law deployed: piece 1 pays the cold load, pieces 2+ ride the
  warm cache (~1-3 min each), lake's `-j4` elaborates the independent
  subchains concurrently.  The ratchet: each surviving cycle banks 1-4
  pieces; murdered cycles cost only wall-clock (the previous banks stand).

## The static verification of the wave-9-E fix sites (BOSS's own-maths audit)

* **Site 1 (`chartLeg_awayι`'s hstep, the old :257 calc-Trans disease)**:
  the have-chain's rw-sequence (`chartLeg` unfold → `←
  Proj.basicOpenIsoSpec_inv_ι` → the forward `Category.assoc` →
  `Iso.hom_inv_id_assoc`) is verbatim the chain that compiled CLEAN inside
  the 9-D calc's middle step (run 45285705894's receipts); the calc-step
  boundary — the only place the `Trans` instance was ever synthesized — is
  gone by construction; the finisher consumes §1's own green
  `sectionInto_ι` (the pin receipts `Restrict.lean:788-789`, `:445-447`).
* **Site 2 (the h3 preimage conversion, the old :558 unknown-identifier
  disease)**: the `← SetLike.mem_coe, ← Set.mem_preimage, ←
  TopologicalSpace.Opens.map_coe` chain at hq is VERBATIM the pin's own
  `Basic.lean:472-474` idiom (the `toSpecZero` region's membership dance —
  the pinned Mathlib has NO `Opens.mem_preimage` lemma; the phantom name is
  dead and the pin's own rewrites do the conversion).

## The task audit (BOSS's accuracy order — Tasks 1-6 vs the original)

The original order as transcribed at the assault's birth (commit `47972b6`,
the wave-4-0 scaffolding, 2026-11-22): *the honest prime lattice, the
canonical cycle-class maps, the chart classification, the two M-cycle
letters, the gate-free law* — plus the honest-Hodge-data lane as the data
backbone.  The executed ledger maps every component: Task 1 = the prime
lattice (`GSTFiniteLinePointAlgebra`, CI-GREEN `45225257813` @ `c37bd9a`,
re-certified at `50c6f19`); Task 2 = the chart classification
(`GSTFiniteLineRiemann` + `GSTFiniteLineAnalytification`, CI-GREEN
`45225257888` @ `c37bd9a`, re-certified at `50c6f19`); Task 3 = the
canonical cycle-class maps (`GSTFiniteLineCycleCorrespondence` §0-§2, the
Basic/Action pieces); Task 4 = the two M-cycle letters (§3, the
Operators/Letters pieces); Task 5 = the honest Hodge data
(`GSTFiniteLineHonestHodgeData`, CI-GREEN `45225257718` @ `c37bd9a`,
re-certified at `50c6f19`); Task 6 = the gate-free law
(`GSTFiniteLinePointsGateCore` + `GSTFiniteLinePointsGateDischarge`, the
Core/Discharge pieces); Task 7 = the universal primitive-X source (BOSS's
wave-9 addition).  **Verdict: all six original components present, none
dropped, none smuggled; the numbering reflects the module consolidation
(Tasks 3+4 share one module) rather than the blueprint's prose order; the
substance is faithful throughout.**

## The state at this record's write

The 1800s cycles are riding the ratchet at `58cb939f`.  The banks grow
monotonically; the chains (cycle-corr: 4 pieces; discharge: 6; primitive-x:
10; unconditional: 4 + its own 296-line module) converge as surviving
cycles bank.  No green is claimed for any ratchet lane at any SHA by this
record (the AGENTS discipline); the sorryAx hard-fail stands in every lane.
