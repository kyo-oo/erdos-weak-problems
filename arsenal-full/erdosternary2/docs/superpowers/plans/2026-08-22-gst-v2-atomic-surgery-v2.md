# GST V2 Atomic Surgery V2 Implementation Plan

> **For agentic workers:** REQUIRED SUB-SKILL: Use superpowers:executing-plans to implement this plan task-by-task.

**Goal:** Replace the prefix-one production seam with one canonical infinite GST V2 graph whose full-energy slices realize both the child and seed-one parent, then close the collision and run the pinned comparator.

**Architecture:** `GSTGraphV2InfiniteControl.lean` owns the all-depth `Nat × Nat` canonical sheet and exposes every already-green local/rectangle observable as coordinates of one orbit. Generic prefix-slice projection theorems connect a full energy `prefix + 3^b * tail` to the tail digit and seeded x4 carry at `b+q`. The production surgery specializes those projections to the exact perfect-power phase-zero and phase-one decompositions, so no tail-only surrogate remains.

**Tech Stack:** Lean 4.33.0-rc2, Mathlib, GitHub Actions pinned CI.

**Spec:** user-directed GST Graph V2 / canonical seven-axis / three-space infinite integration in the current conversation.

## Global Constraints

- No `sorry`, `admit`, custom axiom, `native_decide`, or `gst_end` escape.
- No residual Omega termination theorem or finite-support/horizon proof of the final collision.
- Keep the vertical Omega direction live at arbitrary `K : Nat`.
- Do not claim completion until the transformed production monolith and final comparator are GREEN.

---

### Task 1: Main Infinite Graph

**Files:**
- Create: `GSTGraphV2InfiniteControl.lean`
- Create: `GSTGraphV2InfiniteControlSmoke.lean`
- Modify: `.github/workflows/gpt56-u2d-atomic-ci.yml`

**Interfaces:**
- Consumes: `GSTCanonicalSevenAxisBridge.vertex`, `canonical_cell_exact`, `GSTU2DExactCrossingCharge.reverseCrossRectangle_exact`, mixed/U modules.
- Produces: `InfiniteCell`, `graph`, `graph_cell_exact`, `graph_happy_iff_event_eight`, `graph_cross_rectangle_exact`.

- [ ] Define one enriched cell containing the canonical seven-axis vertex plus event, U charge, mixed density, crossing density and survive indicator.
- [ ] Define `graph E : Nat -> Nat -> InfiniteCell`.
- [ ] Lift the exact local cell law and Happy/event/crossing equivalences.
- [ ] Instantiate the arbitrary-width/arbitrary-depth crossing rectangle theorem on `graph E`.
- [ ] Compile with pinned Lean and audit axioms/source.

### Task 2: Prefix-Slice Projection

**Files:**
- Modify: `GSTGraphV2InfiniteControl.lean`
- Modify: `GSTGraphV2InfiniteControlSmoke.lean`

**Interfaces:**
- Produces generic theorems projecting `E = prefix + 3^b * tail` at `b+q` to the tail digit and an x4 seeded carry determined by the low prefix.

- [ ] Prove exact shifted quotient/digit projection.
- [ ] Prove exact seeded carry projection while retaining the low-prefix carry seed.
- [ ] Add seed-zero and seed-one corollaries.
- [ ] Compile GREEN before any production edit.

### Task 3: Atomic Surgery V2

**Files:**
- Modify: `scripts/apply_u2d_atomic_replacement.py`
- Modify: `.github/workflows/gpt56-u2d-atomic-ci.yml`

**Interfaces:**
- Consumes the generic prefix-slice theorems and existing monolith perfect-power decompositions.
- Produces a replacement theorem using the actual full-energy graph instead of `gstCarry (4^t*T) q` / `gstDigit (4^t*T) q`.

- [ ] Import the integrated main graph in the transformed monolith.
- [ ] Establish literal child slice from phase-zero full energy.
- [ ] Establish literal seed-one parent slice from the phase-one full energy.
- [ ] Feed child Happy and parent badness into the same canonical orbit.
- [ ] Reduce the proof to the exact remaining event-8 transport collision.

### Task 4: Final Comparator

**Files:**
- Modify production source only after Task 3 compiles completely.

- [ ] Run pinned production compile after surgery.
- [ ] Run source audit.
- [ ] Run final comparator.
- [ ] Only if all are GREEN, persist the replacement in `ErdosTernary2.lean` and report completion.
