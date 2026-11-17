<!-- ======================================================================
<!-- CHRONOLOGICAL LABEL -- #0703 / 1132
<!--    Path         : branches/sol_physical-phase-crossing-implementation/docs/superpowers/plans/2026-08-17-prefix-one-physical-crossing.md
<!--    Ref          : origin/sol/physical-phase-crossing-implementation
<!--    First-commit : 2026-08-17 00:35:22 +0530  (b21fb53)
<!--    Last-commit  : 2026-08-17 00:51:55 +0530  (c5d1555)
<!--    Total commits: 2
<!-- ======================================================================
<!-- GIT HISTORY (chronological, oldest first)
<!-- ======================================================================
<!-- [01/2] 2026-08-17 00:35:22 +0530  b21fb53  (ker07-dev)
<!--        Plan atomic prefix-one phase crossing implementation
<!-- [02/2] 2026-08-17 00:51:55 +0530  c5d1555  (ker07-dev)
<!--        Record exact physical-trap surgery frontier
<!-- ====================================================================== -->

# Prefix-One Physical Crossing Implementation Plan

> **For agentic workers:** REQUIRED SUB-SKILL: Use superpowers:subagent-driven-development (recommended) or superpowers:executing-plans to implement this plan task-by-task. Steps use checkbox (`- [ ]`) syntax for tracking.

**Goal:** Remove the active residual Ω dependency by proving the canonical prefix-one phase crossing and reach a successful full comparator run.

**Architecture:** Keep the 401,194-byte `d6e948…` monolith frozen until a standalone canonical crossing scratch is green. The crossing is reduced through the exact pure-power residue tower to a physical two-boundary trap; the only remaining mathematical theorem is exclusion of that trap using the real pure-power rectangle. Only after that theorem is kernel-green may a thin adapter replace the residual-termination call in the monolith.

**Tech Stack:** Lean 4.33.0-rc2, pinned Mathlib revision, GitHub Actions `Lean + Comparator`, existing GST scratch modules.

## Global Constraints

- Work from `d6e948c7e13af100210bfbf9956394cde358e743` on `sol/physical-phase-crossing-surgery`.
- No internet or external theorem search.
- Never activate or prove the quarantined residual Ω termination chain.
- No global ALT-minus mirror assumption and no terminal-NULL argument.
- No `sorry`, `admit`, `axiom`, `mkSorry`, or `native_decide` in the final source.
- Preserve the carry-normalization repair already present in `d6e948…`.
- Do not use conservation identities alone as an exclusion theorem.
- No comparator-facing theorem change unless forced by the verified proof dependency.
- Completion means the pinned comparator prints `YOUR SOLUTION IS OKAY`.

---

### Task 1: Isolate the canonical RED target

**Files:**
- Create/modify: `CanonicalPhaseCrossingSurgeryScratch.lean`
- Create: `.github/workflows/phase-crossing-surgery.yml`

- [x] **Step 1:** Create isolated branch `sol/physical-phase-crossing-surgery` at exact checkpoint `d6e948c7e13af100210bfbf9956394cde358e743`.
- [x] **Step 2:** Remove dependency on `GSTPhaseCrossingScratch` / `AtomicPrefixOneReductionScratch` so the surgery scratch does not import the broken monolith.
- [x] **Step 3:** State the target only on the literal prefix-one pure-power orbit: `A = 4^(3^s)`, child energy `4^(3^(s+1)*n)`, parent energy `A * child`, and canonical `Q` certified by `GSTCanonicalOriginEnergyS`.
- [x] **Step 4:** Create a dedicated Actions workflow that compiles only the surgery scratch.
- [ ] **Step 5:** Obtain the RED compiler verdict. BLOCKED externally: GitHub Actions currently starts zero steps because the repository account reports failed payment/spending-limit status. This is not a Lean verdict.

### Task 2: Reduce physical crossing to the exact conserved trap

**Files:**
- Modify: `CanonicalPhaseCrossingSurgeryScratch.lean`

- [x] **Step 1:** Prove the phase-zero exact energy chart from `GSTCanonicalOriginEnergyS`.
- [x] **Step 2:** Prove the phase-one exact energy chart from `gst_prefix_one_pure_power_axisS`.
- [x] **Step 3:** Convert a phase-zero `GSTDoubleJumpS` into a seed-zero child Happy Gate using the existing common-two equivalences.
- [x] **Step 4:** Convert absence of every phase-one double jump into complete seed-one parent badness.
- [x] **Step 5:** Apply `gst_canonical_two_boundary_trapS` at the globally last child gate to obtain two regenerated bad boundaries plus `D + 4 Z = W + A C`, `C ∈ {2,3}`, `W < A`.
- [x] **Step 6:** Attach the exact pure-power rectangle using `gst_shared_state_is_exact_power_rectangleS`; record that the same shared word is the real wide carry across `4^(3^(s+1)n) -> 4^(3^(s+1)n + 3^s + 1)`.
- [x] **Step 7:** Attach the finite bridge coordinate `S / 3^(2*3^s) = 0` using the information-word bound. This is only a coordinate fact, not terminal NULL.

### Task 3: Prove the one remaining separation theorem

**RED theorem:** `gst_canonical_prefix_one_physical_trap_impossible_surgeryS`.

**Exact forbidden object:** a canonical perfect-power physical trap containing:
- regenerated parent bad trace,
- regenerated child bad trace,
- high coordinate `C ∈ {2,3}` inherited from the last child gate,
- one conserved information word `S = D + 4 Z = W + A C`, `W < A`,
- `S` equal to the wide carry of the actual pure-power rectangle,
- the finite bridge coordinate of that same `S`.

- [ ] **Step 1:** Use `CarryWordScratch` to expose every horizontal carry as a base-4 coordinate of the same physical `S`.
- [ ] **Step 2:** Build the missing phase-indexed/regeneration invariant only if it is derivable from the exact rectangle. It must preserve the pure-power certificate; an arbitrary affine trap is known not to be contradictory.
- [ ] **Step 3:** If using natural-origin descent, prove the physical certificate descends together with the two bad boundaries. Do not use finite support until a theorem genuinely forces nonzero origin information past every cutoff.
- [ ] **Step 4:** Close `gst_canonical_prefix_one_physical_trap_impossible_surgeryS` without assuming the desired crossing in disguised form.
- [ ] **Step 5:** When Actions is available, kernel-check the complete scratch and audit it for forbidden proof mechanisms.

### Task 4: Transplant only the green blade into the monolith

**Files:**
- Modify: `ErdosTernary2.lean` only after Task 3 is kernel-green.

- [ ] **Step 1:** Inline/transplant only the minimum physical-crossing/separation lemmas required by the monolith.
- [ ] **Step 2:** Replace the active call through `gst_residual_omega_termination` with child-gate -> canonical physical crossing -> parent-gate contradiction.
- [ ] **Step 3:** Verify no active dependency on `gst_residual_omega_termination` remains.
- [ ] **Step 4:** Build `ErdosTernary2` and require green.

### Task 5: Full verification

- [ ] **Step 1:** Build every active information/pure-power/GST scratch module.
- [ ] **Step 2:** Build `GSTTactic`, comparator smoke modules, `Challenge`, and `Solution`.
- [ ] **Step 3:** Run `scripts/audit.sh`; require zero `sorry`, `admit`, `mkSorry`, custom axiom, and `native_decide` in audited proof sources.
- [ ] **Step 4:** Run pinned comparator with `comparator_config.json`.
- [ ] **Step 5:** Do not declare success unless output contains `YOUR SOLUTION IS OKAY`.
