# GST Global Hodge Defect-Extinction Implementation Plan

> **For agentic workers:** REQUIRED SUB-SKILL: Use superpowers:subagent-driven-development (recommended) or superpowers:executing-plans to implement this plan task-by-task. Steps use checkbox (`- [ ]`) syntax for tracking.

**Goal:** Build the GST-first global sheet-cosmos, use the existing limitless matrix-unit/Poincare/recoordination machinery to saturate the genuine Hodge fibers from the canonical algebraic spine, extinguish every basis separator, and land on the exact finite-rational-cycle Hodge statement.

**Architecture:** Reuse the existing `FiberedHodgeIndex`/`FiberedHodgeAddress` as the total `(weight,basis-sheet)` cosmos instead of inventing a second carrier. Add same-weight global read/write operators and prove they intertwine with the existing classical Hodge matrix units. Then combine the canonical algebraic spine, genuine graded geometric programs, GST coordinate probes, and basis-separator contradiction so the final theorem produces the exact Clay-style finite rational combination statement.

**Tech Stack:** Lean 4, Mathlib, existing HC-PROOF GST modules.

**Spec:** `docs/superpowers/specs/2026-10-03-gst-global-hodge-defect-extinction-design.md`

## Global Constraints

- The final target is `GSTClassicalHodgeExactClayStatement.EveryHodgeClassIsFiniteRationalCombination H`.
- Reuse `FiberedHodgeIndex`/`FiberedHodgeAddress`; do not create a parallel total-sheet type.
- Do not assume Hodge surjectivity, basis-cycle representatives, universal sheet reachability, arbitrary matrix-unit naturality, or separator nonexistence.
- Preserve the existing theorem that arbitrary multiplicity matrix units do not descend globally through the native projection; use source-specific synchronized execution instead.
- Every new mathematical capstone gets `#check` and targeted `#print axioms` lines.
- Do not claim compilation green without an actual compiler/CI result.

## Review Focus

- Empty Hodge fibers: global sheet operations must remain well-defined and the final theorem must discharge zero fibers without requesting a source.
- Multiple basis sheets at one weight: the global cosmos must keep them distinct rather than collapsing them to the old `(p,p)` GST base address.
- Cross-weight sheet confusion: same-weight matrix units must never move between different `p` values.
- Native descent obstruction: no theorem may silently factor a nontrivial multiplicity matrix unit through `toNativeCycle`.
- Circularity: no source-specific geometric program constructor may contain the target basis algebraicity/reachability conclusion as a field.

---

### Task 1: Global Fibered Sheet Cosmos

**Files:**
- Create: `GSTClassicalHodgeGlobalSheetCosmos.lean`

**Interfaces:**
- Consumes: `FiberedHodgeIndex`, `FiberedHodgeAddress`, `fiberedWeightCoordinates`, `fiberedSheetGenerator`, `classicalHodgeBasis`, `world/cosmic Poincare probe` ideas.
- Produces: `sheetProbe`, `sheetMatrixUnit`, exact basis/probe formulas, same-weight support theorem, and the intertwining theorem from a fixed Hodge fiber to its global sheet coordinates.

- [ ] Define `sheetProbe s : FiberedHodgeAddress V H ->ₗ[ℚ] ℚ` by exact coordinate read.
- [ ] Define `sheetMatrixUnit s t : Module.End ℚ (FiberedHodgeAddress V H)` by `phi ↦ phi s • fiberedSheetGenerator V H t`.
- [ ] Prove exact application, source-basis, other-basis, and composition laws.
- [ ] Prove fixed-weight coordinate read: `sheetProbe ⟨p,i⟩ (fiberedWeightCoordinates ... alpha) = repr alpha i`.
- [ ] Prove fixed-weight intertwining: applying global `sheetMatrixUnit ⟨p,i⟩ ⟨p,j⟩` to `fiberedWeightCoordinates alpha` equals coordinates of `hodgeMatrixUnit i j alpha`.
- [ ] Add `#check`/`#print axioms` receipts.

### Task 2: Global GST Sheet Saturation

**Files:**
- Create: `GSTClassicalHodgeGlobalSheetSaturation.lean`

**Interfaces:**
- Consumes: Task 1 matrix units; existing `rationalCosmic_invariant_eq_top`, basis/separator algebra.
- Produces: a direct fixed-weight irreducibility theorem on `FiberedHodgeAddress` and a basis-extraction theorem from one nonzero fixed-weight algebraic source whose global sheet images are algebraic.

- [ ] Define the fixed-weight global sheet submodule inside `FiberedHodgeAddress`.
- [ ] Prove it is linearly equivalent to the fixed-weight Hodge fiber coordinates.
- [ ] Prove a nonzero submodule of a fixed-weight sheet space stable under all same-weight `sheetMatrixUnit`s is the whole fixed-weight sheet space.
- [ ] Derive a source-to-all-target saturation theorem from one nonzero source coordinate.
- [ ] Add audit receipts.

### Task 3: Canonical Spine Source in the Global Sheet Cosmos

**Files:**
- Create: `GSTClassicalHodgeGSTSpineGlobalSource.lean`

**Interfaces:**
- Consumes: `spineNativeTower`, `spineHodgeSeed`, `NativeMassCycleClassBridge`, Task 1 probes.
- Produces: `GlobalSpineSource` containing the synchronized native cycle/Hodge state, a selected live basis coordinate, and its nonzero coordinate proof, all derived from the existing spine/nonvanishing machinery.

- [ ] Define the global sheet coordinates of `spineHodgeSeed G p`.
- [ ] Use basis representation of a nonzero spine seed to choose a live sheet index.
- [ ] Prove the selected `sheetProbe` is nonzero.
- [ ] Package `GlobalSpineSource` without adding new algebraicity assumptions.
- [ ] Prove its native class equals its Hodge source and its global address has the selected nonzero coordinate.
- [ ] Add audit receipts.

### Task 4: GST Source-Specific Geometric Program Compiler

**Files:**
- Create: `GSTClassicalHodgeGSTSourceProgramCompiler.lean`

**Interfaces:**
- Consumes: Task 3 source, `GradedGeometricProgram`, `ProjectiveOperatorWord`, `ProjectiveTwoGenerator`/word compiler, Task 1 global matrix units.
- Produces: a source-specific certificate type and theorem turning any genuine geometric program with the GST-computed source action into an actual target basis cycle.

- [ ] Define `GSTSourceTargetProgram G S j` with only a genuine `GradedGeometricProgram V p p` and a source-action equality; do not store target algebraicity.
- [ ] Define the normalized target native cycle from program execution on `S.cycle`.
- [ ] Prove its cycle class is exactly basis sheet `j` using program naturality and source coefficient nonvanishing.
- [ ] Add constructors from existing `ProjectiveWordLiveSourceTarget` and `ProjectiveTwoGenerator` routes so old geometry compiles into the new GST-global interface.
- [ ] Add audit receipts.

### Task 5: GST Defect Extinction

**Files:**
- Create: `GSTClassicalHodgeGSTDefectExtinction.lean`

**Interfaces:**
- Consumes: basis separators, Task 1 probes/matrix units, Task 3 global source, Task 4 source-target programs.
- Produces: separator contradiction and exact basis algebraicity from source-target geometric programs.

- [ ] Define the separator's finite GST defect address by its values on basis sheets at one weight.
- [ ] Prove a separator seeing basis `j` yields a nonzero defect coordinate at `j`.
- [ ] Prove every source-target geometric program output is annihilated by the separator because it is an actual cycle class.
- [ ] Combine with the source-action equality to derive contradiction for each target sheet.
- [ ] Prove `IsEmpty (BasisAtomicSeparator V H p j)` for every target supplied by a source-specific program.
- [ ] Prove every basis sheet lies in the actual cycle-class range.
- [ ] Add audit receipts.

### Task 6: Exact GST Hodge Finale

**Files:**
- Create: `GSTClassicalHodgeGSTExactFinale.lean`

**Interfaces:**
- Consumes: Task 3 global spine source, Task 5 separator extinction, `GSTClassicalHodgeExactClayStatement`.
- Produces: exact finite-rational-combination theorem.

- [ ] State the minimal remaining genuine geometry family as source-specific `GSTSourceTargetProgram`s generated from the canonical spine source; no universal reachability predicate.
- [ ] Prove `BigradedBettiHodgeStatement V H` by separator extinction/basis saturation.
- [ ] Convert with `exact_rational_hodge_conjecture_finite_sum` to `EveryHodgeClassIsFiniteRationalCombination H`.
- [ ] Add an elementwise theorem returning an actual `FiniteCodimensionPresentation` for any rational Hodge class.
- [ ] Add `#check`/`#print axioms` receipts.

### Task 7: Integration Audit

**Files:**
- Modify only as needed: imports in the new finale or one aggregator file; do not rewrite green legacy mathematics.

**Interfaces:**
- Consumes: all prior tasks.
- Produces: one auditable dependency chain from GST cosmology to the exact Hodge statement.

- [ ] Search the new files for banned conclusion-shaped inputs: `BigradedBettiHodgeStatement`, `EveryHodgeClassIsRationalAlgebraic`, `EveryHodgeClassIsFiniteRationalCombination`, `ClosedCorrespondenceHitsSheet`, universal reachability, basis-cycle bridge fields.
- [ ] Verify such names occur only in theorem conclusions or imported conversion theorems, never as assumptions/structure fields.
- [ ] Run/hand off Lean compilation for each new file in dependency order.
- [ ] Audit `#print axioms` outputs for unexpected custom axioms/sorryAx.
- [ ] Record exact compiler status; if GLM repairs syntax/API, preserve theorem signatures and mathematical hypotheses.
