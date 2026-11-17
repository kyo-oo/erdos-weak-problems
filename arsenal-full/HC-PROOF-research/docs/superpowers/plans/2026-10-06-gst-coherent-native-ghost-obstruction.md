# GST Coherent-Native Ghost Obstruction Implementation Plan

> **For agentic workers:** REQUIRED SUB-SKILL: Use superpowers:executing-plans to implement this plan task-by-task. Steps use checkbox (`- [ ]`) syntax for tracking. Do not dispatch subagents for this plan.

**Goal:** Prove, inside the repository's GST native omniverse, that every cycle-class-descending coherent native action has an explicit nonzero mismatch with the ghost-selected branch target.

**Architecture:** A new focused Lean module first proves a general obstruction for any labelled native operator and any ambient action satisfying the actual cycle-class commuting square. It then removes that ambient-action premise by constructing the action from the existing two-obstruction coherent-descent theorem, and specializes the result to routed lifts and finite tensor blocks. The existing discovery note records the mathematical consequence, while `lakefile.toml` and `HCProof.lean` register the module.

**Tech Stack:** Lean 4, Mathlib linear algebra and algebraic geometry, the repository's Stage-2G cycle-class spine, omniversal separator ghost, fibered native address universe, and coherent native descent modules.

**Spec:** `docs/superpowers/specs/2026-10-06-gst-coherent-native-ghost-obstruction-design.md`

## Global Constraints

- Work on `sol/gst-plane-completeness-8408fd0`; do not create another branch or worktree.
- Do not use subagents or internet search.
- Use only the repository's GST/native mathematics for the proof.
- Do not assume a target cycle representative, strict relation packet, common-plane packet, desired source-to-target action equation, Hodge completeness, or a new carrier-existence axiom.
- Do not add `axiom`, `sorry`, or `admit`.
- The main coherent theorem must construct its ambient action from post-cycle-class column agreement and native class-kernel stability.
- The nonzero result must use the seed's live source coefficient and the ghost detector's nonzero basis reading.
- Compiler repair belongs to GLM by user instruction; attempt bounded local checks but report them honestly if the branch environment prevents a green build.

## Review Focus

- **Native source rewriting:** `S.class_eq` may orient the equality as `H.cycleClass _ S.cycle = S.hodge`; the proof must verify the direction used when evaluating the commuting square.
- **Ambient extension freedom:** conclusions may concern `T` only on the genuine seed class in the cycle-class range; do not claim uniqueness or geometric meaning outside that range.
- **Label cancellation:** the general theorem must quantify over arbitrary labelled `U`, so routing or cancellation among labels cannot evade it.
- **Finite tensor scope:** tensor-block corollaries must live under the exact existing `Fintype (ClassicalHodgeBasisIndex V H p)` assumption and use column sums, not isolated tensor-word assumptions.
- **Import/circularity boundary:** the new module may use ghost and seed definitions but must not prove the obstruction by invoking strict-packet emptiness or a Hodge equivalence.

---

### Task 1: General descending-action ghost obstruction

**Files:**
- Create: `GSTClassicalHodgeCoherentNativeGhostObstruction.lean`

**Interfaces:**
- Consumes: `GSTClassicalHodgeCoherentNativeDescent.nativeSection`, `toNativeCycle_nativeSection`, `GSTClassicalHodgeNativePointRelationDescent.nativeAmbientAction`, `NativeHodgeOrbitSeed.class_eq`, `NativeHodgeOrbitSeed.sourceCoefficient_ne_zero`, `hodgeMatrixUnit_apply`, `OmniversalSeparatorGhost.kills_all_native_programs`, and `BasisAtomicSeparator.detects_basis`.
- Produces: `ghost_kills_nativeCycleClass`, `ghost_kills_descendingAction_on_seed`, `ghostSeedTarget_descendingAction_mismatch_formula`, `ghostSeedTarget_descendingAction_mismatch_ne_zero`, `ghostSeedTarget_descendingAction_ne_target`, and `no_descendingAction_realizes_ghostSeedTarget`.

- [ ] **Step 1: Create the module boundary and the native-range theorem signature**

Import `GSTClassicalHodgeCoherentNativeDescent` and `GSTClassicalHodgeCommonClassPlaneReduction`; open the same Stage-2G, fibered-native, coherent-descent, ghost, and graded-program namespaces used by those modules. Add this exact public signature:

```lean
theorem ghost_kills_nativeCycleClass
    (G : GeometricCycleClassSpine V H)
    (E : OmniversalSeparatorGhost G)
    (Z : codimensionCycles V.X E.weight) :
    E.separator.detector (H.cycleClass E.weight Z) = 0
```

Prove it by specializing `E.kills_all_native_programs` to `E.weight`, `GradedGeometricProgram.id E.weight`, and `Z`, then simplify only the identity-program definitions already used in `GhostCommonClassPlaneStrike.contradiction`.

- [ ] **Step 2: Run the focused parser/type check for the native-range theorem**

Run: `lake env lean GSTClassicalHodgeCoherentNativeGhostObstruction.lean`

Expected: the new theorem elaborates; if imports outside this file fail first, capture the first external error without weakening the theorem.

- [ ] **Step 3: Add the general commuting-square invisibility theorem**

Add the exact parameters `i₀`, `U`, `T`, and

```lean
hT :
  (((H.cycleClass E.weight).comp
      (toNativeCycle V H E.weight)).comp U) =
    T.comp ((H.cycleClass E.weight).comp
      (toNativeCycle V H E.weight))
```

and prove:

```lean
theorem ghost_kills_descendingAction_on_seed ... :
    E.separator.detector (T S.hodge.1) = 0
```

Evaluate `hT` at `nativeSection i₀ S.cycle`. Rewrite its input with `toNativeCycle_nativeSection`, rewrite the seed class with `S.class_eq`, and apply `ghost_kills_nativeCycleClass` to the native output `toNativeCycle ... (U (nativeSection i₀ S.cycle))`.

- [ ] **Step 4: Add the exact defect formula and its nonzero consequences**

Using the same parameters and `hT`, add:

```lean
theorem ghostSeedTarget_descendingAction_mismatch_formula ... :
    E.separator.detector
        (T S.hodge.1 -
          (hodgeMatrixUnit S.sourceIndex E.sheet S.hodge).1) =
      -(hodgeCoordinate S.sourceIndex S.hodge *
        E.separator.detector
          (classicalHodgeBasis V H E.weight E.sheet).1)
```

Then add the corresponding `_mismatch_ne_zero`, `_ne_target`, and
`no_descendingAction_realizes_ghostSeedTarget` theorems. The final theorem must negate an existential package containing `T`, its commuting square, and the target equality. Prove nonzeroness from `S.sourceCoefficient_ne_zero` and `E.separator.detects_basis`; prove target inequality by rewriting a hypothetical equality into a zero defect.

- [ ] **Step 5: Add receipts and check the entire general theorem family**

Add `#check` lines for all six public declarations and `#print axioms` for the native-range theorem, the exact mismatch formula, the nonzero mismatch, and the existential no-realization theorem.

Run: `lake env lean GSTClassicalHodgeCoherentNativeGhostObstruction.lean`

Expected: no unsolved goals and no custom axioms in the printed receipts.

- [ ] **Step 6: Commit the general obstruction**

```powershell
git add -- GSTClassicalHodgeCoherentNativeGhostObstruction.lean
git commit -m "math: prove coherent native ghost target obstruction"
```

### Task 2: Constructed coherent action and exhaustive specializations

**Files:**
- Modify: `GSTClassicalHodgeCoherentNativeGhostObstruction.lean`

**Interfaces:**
- Consumes: Task 1's general obstruction theorems; `nativeColumn`, `cycleClass_descent_iff`, `nativeAmbientAction`, `nativeAmbientAction_natural`, `routedNativeOperator`, `routedNativeOperator_descends`, `finiteTensorBlock`, `tensorColumnSum`, and `finiteTensorBlock_nativeColumn`.
- Produces: `coherentNativeAmbientAction_descends`, `ghostSeedTarget_coherentNativeAction_mismatch_formula`, `ghostSeedTarget_coherentNativeAction_ne_target`, `ghostSeedTarget_routedNativeAction_ne_target`, and `ghostSeedTarget_finiteTensorBlockAction_ne_target`.

- [ ] **Step 1: State and prove the exact constructed-action commuting square**

For arbitrary anchor `i₀` and labelled operator `U`, take:

```lean
hcolumns : ∀ i,
  (H.cycleClass p).comp (nativeColumn i U) =
    (H.cycleClass p).comp (nativeColumn i₀ U)
hkernel : NativeClassKernelStable
  (H.cycleClass p) (nativeColumn i₀ U)
```

Add:

```lean
theorem coherentNativeAmbientAction_descends ... :
    (((H.cycleClass p).comp (toNativeCycle V H p)).comp U) =
      (nativeAmbientAction (H.cycleClass p)
        (nativeColumn i₀ U) hkernel).comp
          ((H.cycleClass p).comp (toNativeCycle V H p))
```

Prove equality on labelled point atoms using `labelledLinearMap_ext`, the
post-cycle-class column equality, and `nativeAmbientAction_natural`. This is
the constructive direction of `cycleClass_descent_iff`, exposed with the exact
chosen action rather than an existential witness.

- [ ] **Step 2: Check the constructed-action lemma independently**

Run: `lake env lean GSTClassicalHodgeCoherentNativeGhostObstruction.lean`

Expected: the exact `nativeAmbientAction` expression elaborates, including the anchor-column kernel witness.

- [ ] **Step 3: Derive the main premise-free coherent obstruction**

At `p := E.weight`, define no additional structure. Apply
`ghostSeedTarget_descendingAction_mismatch_formula` with
`T := nativeAmbientAction ...` and
`hT := coherentNativeAmbientAction_descends ...` to prove:

```lean
theorem ghostSeedTarget_coherentNativeAction_mismatch_formula ...
theorem ghostSeedTarget_coherentNativeAction_mismatch_ne_zero ...
theorem ghostSeedTarget_coherentNativeAction_ne_target ...
```

The hypotheses are exactly `hcolumns` and `hkernel`; there is no ambient `T`, target action equation, carrier, or target cycle hypothesis.

- [ ] **Step 4: Add routed-lift specialization**

For any routing `ρ` and native action `A` satisfying
`NativeClassKernelStable (H.cycleClass E.weight) A`, prove that the constructed
ambient action `nativeAmbientAction (H.cycleClass E.weight) A` does not send
`S.hodge.1` to the GST matrix-unit target. Use
`routedNativeOperator_descends`/`native_factorization_iff_columns` to discharge
column agreement; do not add injectivity, surjectivity, or finiteness assumptions on `ρ`.

- [ ] **Step 5: Add complete finite-tensor-block specialization**

Inside a section with

```lean
[Fintype (ClassicalHodgeBasisIndex V H E.weight)]
```

take a coefficient block `A`, post-cycle-class column-sum agreement, and
`NativeClassKernelStable` for the anchor column sum. Prove that the constructed
ambient action based on `tensorColumnSum A i₀` misses the target. Rewrite with
`finiteTensorBlock_nativeColumn` and apply the general coherent result. This
must permit cancellation between tensor words.

- [ ] **Step 6: Add receipts and perform forbidden-premise scan**

Add `#check` for all five produced interfaces and `#print axioms` for the
constructed commuting square, the main coherent mismatch formula, and both
specializations.

Run:

```powershell
rg -n "\baxiom\b|\bsorry\b|\badmit\b|StrictRelationEdgePacket|CommonClassPlanePacket|targetCycle" GSTClassicalHodgeCoherentNativeGhostObstruction.lean
lake env lean GSTClassicalHodgeCoherentNativeGhostObstruction.lean
```

Expected: search returns no forbidden declaration or premise; Lean check reaches no error in the new file.

- [ ] **Step 7: Commit the exhaustive coherent specializations**

```powershell
git add -- GSTClassicalHodgeCoherentNativeGhostObstruction.lean
git commit -m "math: exhaust coherent GST routes to the ghost target"
```

### Task 3: Document, register, and audit the theorem frontier

**Files:**
- Modify: `docs/GST_NATIVE_COHERENCE_DISCOVERIES_20261006.md`
- Modify: `lakefile.toml`
- Modify: `HCProof.lean`

**Interfaces:**
- Consumes: all theorem names from Tasks 1 and 2.
- Produces: registered build target, umbrella import, mathematical handoff section, and final trust/audit evidence.

- [ ] **Step 1: Add the coherent-native ghost-obstruction derivation**

Append a section `## 7. Coherent-native ghost obstruction` before the current
`What this contributes toward D` section. State the exact displayed defect
equation, derive it from the constructed commuting square on the genuine seed,
and record the routed and finite-tensor consequences. Explicitly say that the
theorem closes the native-operator route to D and leaves strict geometric
carrier synthesis as the positive missing construction.

- [ ] **Step 2: Register the module**

Add `GSTClassicalHodgeCoherentNativeGhostObstruction` immediately after
`GSTClassicalHodgeCoherentNativeDescent` in `lakefile.toml` and import it
immediately after the coherent-descent import in `HCProof.lean`.

- [ ] **Step 3: Run structural and whitespace checks**

Run:

```powershell
git diff --check
rg -n "GSTClassicalHodgeCoherentNativeGhostObstruction" lakefile.toml HCProof.lean
rg -n "\baxiom\b|\bsorry\b|\badmit\b" GSTClassicalHodgeCoherentNativeGhostObstruction.lean
```

Expected: no whitespace errors, exactly one registration and one umbrella import, and no forbidden proof escape.

- [ ] **Step 4: Run bounded Lean verification**

Run:

```powershell
lake build GSTClassicalHodgeCoherentNativeGhostObstruction
```

If successful, also run:

```powershell
lake env lean HCProof.lean
```

Expected: the focused module builds. If a pre-existing branch failure blocks
the umbrella check, preserve the focused evidence and record the external
failure rather than editing unrelated modules.

- [ ] **Step 5: Audit the final dependency and premise surface**

Run:

```powershell
git diff 27a06aa717eca3eee3ed8b355f9c83c7a865fd1f --stat
git diff 27a06aa717eca3eee3ed8b355f9c83c7a865fd1f -- GSTClassicalHodgeCoherentNativeGhostObstruction.lean docs/GST_NATIVE_COHERENCE_DISCOVERIES_20261006.md lakefile.toml HCProof.lean
rg -n "ghostSeedTargetStrictPacket_isEmpty|survival_and_targetStrictClosure_iff_hodge|hodge_of_|BigradedBettiHodgeStatement" GSTClassicalHodgeCoherentNativeGhostObstruction.lean
```

Expected: the implementation diff is confined to the designed files and does
not invoke a strict-packet emptiness or Hodge-equivalence theorem in any proof.

- [ ] **Step 6: Commit documentation and registration**

```powershell
git add -- docs/GST_NATIVE_COHERENCE_DISCOVERIES_20261006.md lakefile.toml HCProof.lean
git commit -m "docs: record coherent native obstruction to plane realization"
```

- [ ] **Step 7: Record final branch evidence**

Run:

```powershell
git status --short --branch
git log -5 --pretty=format:'%H%x09%s'
```

Expected: clean worktree, local branch ahead only by the design, plan, theorem, and documentation commits created for this task.
