# Classical Hodge GST Landing Implementation Plan

> **For agentic workers:** REQUIRED SUB-SKILL: use the native execution workflow; do not dispatch subagents. Execute this plan task-by-task and keep every mathematical boundary explicit.

**Goal:** Build `HodgeConjecture.lean` as the strongest non-circular Lean landing from the full limitless GST cosmology to the genuine Stage-2G rational Hodge target for smooth projective complex schemes.

**Architecture:** Reuse the already-green Stage-2F/2G semantic stack for native rational singular cohomology, Hodge bigrading, codimension-p Mathlib algebraic cycles, and the exact final Hodge statement. Reuse the limitless GST compact address, pure-Hodge, transfer, cohomology, Lefschetz, Poincare, recoordination, and cosmic diagonal machinery to construct the internal side. The only acceptable classical closure is an actual construction of the Stage-2G compact realization; if the repository lacks a theorem producing native algebraic cycles on arbitrary `V.X`, isolate that exact bridge as a named open proof obligation instead of assuming the Hodge conclusion.

**Tech Stack:** Lean 4 `v4.33.0-rc2`, pinned Mathlib, GitHub Actions, the HC-PROOF Stage-2 and limitless GST modules.

**Spec:** `docs/superpowers/specs/2026-09-25-classical-hodge-gst-landing-design.md`

## Global Constraints

- Work only on branch `sol/hodge-classical-gst` until validation is complete.
- No `sorry`, `admit`, new mathematical `axiom`, or conclusion-bearing `constant`.
- No hypothesis propositionally equivalent to `BigradedBettiHodgeStatement`, cycle-class surjectivity, or `Stage2GCompactRealizationObligation` in the theorem claimed as the final proof.
- Do not identify arbitrary classical cohomology with the finite twelve-cell GST carrier.
- Treat the old `ClRing = Z[H,V]/(H^3,V^4)` transfer as an internal address model, not as the cohomology ring of every smooth projective complex variety.
- Every capstone theorem must receive `#print axioms` receipts.
- Preserve the current green Stage-2, cosmology, V2, and comparator gates.
- Use the full limitless cosmology when its formal types contribute to encoding, support, transport, grading, duality, cohomology, or cycle construction; do not import modules merely for decoration.

## Review Focus

1. **Arbitrary supplied `cycleClass`:** a `HodgeBigradedBettiData V` permits an arbitrary linear cycle-class map, so no unconditional theorem may quantify over arbitrary `H` and conclude Hodge surjectivity without additional canonical construction.
2. **Finite-carrier leakage:** the twelve-cell ring must never replace arbitrary rational singular cohomology by definitional equality or an unproved equivalence.
3. **Circular cycle witnesses:** `basisCycle` may not be selected using the Hodge conclusion or a pre-existing surjectivity proof.
4. **Semantic versus internal algebra:** GST diagonal/rank-one/pure-Hodge theorems prove facts in GST carriers; crossing into `codimensionCycles V.X p` requires an actual typed map/theorem.
5. **Axiom profile:** any apparent closure must be rejected if `#print axioms` exposes `sorryAx` or a new project axiom.

---

### Task 1: Add the proof target and dedicated CI gate

**Files:**
- Create: `HodgeConjecture.lean`
- Create: `.github/workflows/hodge-conjecture.yml`
- Modify later only if needed: `lakefile.toml`

**Interfaces:**
- Consumes: `GSTGeometricRealizationStage2G.BigradedBettiHodgeStatement`, `Stage2GCompactRealizationObligation`, and the full limitless modules imported by `HCProof.lean`.
- Produces: a stable namespace `HodgeConjecture`, an exact public classical target alias, and a CI target that compiles the new module and audits proof escapes.

- [ ] **Step 1: Create the Lean shell with exact target aliases and checks**

```lean
import GSTGeometricRealizationStage2G
import GSTTransferBridgeV2
import GSTGlobalPureHodgeCosmology
import GSTDimensionFreeHodgeDiagonal
import GSTUniversalAddressBridge
import GSTTruncatedWorldCohomologyRing
import GSTUniversalLefschetzCosmology
import GSTUniversalLefschetzPathFormula
import GSTUniversalLefschetzKernel
import GSTUniversalLefschetzCausalGeometry
import GSTLefschetzPoincareReciprocity
import GSTWorldPoincareDuality
import GSTWorldRecoordinationGroupoid
import GSTGradedWorldAlgebra

noncomputable section

namespace HodgeConjecture

open GSTProjectiveOverC
open GSTGeometricRealizationStage2D
open GSTGeometricRealizationStage2F
open GSTGeometricRealizationStage2G

def ClassicalHodgeTarget
    (V : SmoothProjectiveComplexScheme)
    (H : HodgeBigradedBettiData V) : Prop :=
  BigradedBettiHodgeStatement V H

#check ClassicalHodgeTarget
#check Stage2GCompactRealizationObligation
#check bigraded_betti_hodge_of_stage2g_compact_obligation

end HodgeConjecture
```

- [ ] **Step 2: Add branch CI** that runs `lake env lean HodgeConjecture.lean`, scans the new file for `sorry|admit|axiom`, and prints the capstone axiom profiles.
- [ ] **Step 3: Push and inspect the workflow result.** The shell must compile green before adding proof constructions.

### Task 2: Formalize the semantic firewall

**Files:**
- Modify: `HodgeConjecture.lean`

**Interfaces:**
- Produces: a precise distinction between an arbitrary Stage-2G package and a canonical/classical package supplied by actual geometry. This task must not introduce a proof assumption.

- [ ] **Step 1: Add an elementwise equivalence theorem** using `bigradedBettiHodgeStatement_iff_explicit_witness` so the final target is visibly the actual native-cycle statement.
- [ ] **Step 2: Add a theorem reducing the final target to `Stage2GCompactRealizationObligation`** by direct application of the existing Stage-2G compact landing theorem.
- [ ] **Step 3: `#print axioms` both reduction theorems** and verify only standard Mathlib axioms occur.

### Task 3: Build the limitless GST compact Hodge coordinate engine

**Files:**
- Modify: `HodgeConjecture.lean`
- Read/reuse: `GSTGlobalPureHodgeCosmology.lean`, `GSTDimensionFreeHodgeDiagonal.lean`, `GSTUniversalAddressBridge.lean`, `GSTTransferBridgeV2.lean`, `GSTGradedWorldAlgebra.lean`, `GSTTruncatedWorldCohomologyRing.lean`.

**Interfaces:**
- Consumes the global/cosmic pure-Hodge and compact address equivalences.
- Produces a reusable internal coordinate theorem showing every compact GST pure-Hodge class has finite-support coordinates generated by the diagonal basis at every natural weight.

- [ ] **Step 1: Re-export or strengthen the exact compact pure-Hodge equivalence** needed by the new file without duplicating existing proofs.
- [ ] **Step 2: Prove the diagonal single-coordinate formula** for the weight-`p` cosmic class under the universal address map.
- [ ] **Step 3: Prove finite-support reconstruction** as a Finsupp sum of diagonal generators.
- [ ] **Step 4: Relate the transfer generator `compactClMono p` to the same cosmic diagonal address** using `compactClMono_eq_cosmicDiagonalAddress` or its exact current theorem name.
- [ ] **Step 5: Compile and print axiom profiles.**

### Task 4: Attempt the actual GST-to-classical semantic embedding

**Files:**
- Modify: `HodgeConjecture.lean`
- Surgical modification of an existing limitless module only if a missing lemma naturally belongs there.

**Interfaces:**
- Desired output is a typed, injective rational-linear encoding

```lean
RationalSingularCohomology H.analytification (2 * p)
  →ₗ[ℚ] (ℕ →₀ ℚ)
```

for the relevant classical Hodge fiber, with `(p,p)` classes supported on the GST diagonal address set.

- [ ] **Step 1: Search every existing limitless/Stage-2 theorem for a map from native Betti cohomology to GST addresses.**
- [ ] **Step 2: If such a map exists, compose it and prove injectivity/support using its actual theorems.**
- [ ] **Step 3: If it does not exist, state the smallest missing map-construction theorem as a goal in the new module and attempt to derive it from the available cosmology. Do not replace it by a hypothesis in the final theorem.**
- [ ] **Step 4: Record a machine-checkable boundary theorem showing exactly which fields of `CompactHodgeRealization` are constructible from existing GST data and which field remains.**

### Task 5: Construct native algebraic basis cycles

**Files:**
- Modify: `HodgeConjecture.lean`
- Read/reuse: `GSTGeometricRealizationStage2D.lean`, `GSTProjectiveOverC.lean`, Stage2E/F/G, and any limitless theorem that genuinely produces Mathlib `AlgebraicCycle` values.

**Interfaces:**
- Must produce, without surjectivity assumptions,

```lean
basisCycle : ℕ → codimensionCycles V.X p
```

and on every live address `i` prove

```lean
encode (H.cycleClass p (basisCycle i)) = Finsupp.single i 1
```

- [ ] **Step 1: Search the entire repository for constructors returning `AlgebraicCycle`, `codimensionCycles`, closed immersions, divisors, or explicit projective subvarieties.**
- [ ] **Step 2: Attempt to realize the GST diagonal generator geometrically using those constructors and the projective-over-C layer.**
- [ ] **Step 3: Prove codimension support of each constructed cycle.**
- [ ] **Step 4: Prove its cycle-class coordinate formula.**
- [ ] **Step 5: If any of Steps 2–4 cannot be derived, leave the theorem as an unproved *active goal in development*, not as a committed `sorry`; commit only the strongest closed reduction and report the exact missing type.**

### Task 6: Assemble `Stage2GCompactRealizationObligation`

**Files:**
- Modify: `HodgeConjecture.lean`

**Interfaces:**
- Consumes Tasks 3–5.
- Produces:

```lean
theorem gst_classical_compact_realization
    (V : SmoothProjectiveComplexScheme)
    (H : HodgeBigradedBettiData V) :
    Stage2GCompactRealizationObligation V H
```

**provided and only if** Tasks 4–5 have constructed the required classical semantic maps from existing theorems without conclusion-bearing assumptions.

- [ ] **Step 1: Construct `CompactHodgeRealization ℕ ...` field-by-field.**
- [ ] **Step 2: Wrap it as `Stage2GCompactRealization` and prove `hodge_iff` and `cycleClass_eq`.**
- [ ] **Step 3: Quantify over `p` to close the obligation.**
- [ ] **Step 4: Print the theorem's axioms and reject any proof escape.**

### Task 7: Close the classical target and audit the universe

**Files:**
- Modify: `HodgeConjecture.lean`
- Modify: `HCProof.lean` only after the new module is independently green.
- Modify: `lakefile.toml` only if module registration is necessary for the repo build.

**Interfaces:**
- Produces the final theorem only if Task 6 closes:

```lean
theorem classical_hodge_conjecture
    (V : SmoothProjectiveComplexScheme)
    (H : HodgeBigradedBettiData V) :
    ClassicalHodgeTarget V H :=
  bigraded_betti_hodge_of_stage2g_compact_obligation
    V H (gst_classical_compact_realization V H)
```

- [ ] **Step 1: Close the theorem by the existing Stage-2G landing theorem, with no new mathematics hidden in the last line.**
- [ ] **Step 2: Add `#print axioms classical_hodge_conjecture`.**
- [ ] **Step 3: Build the new module and `HCProof`.**
- [ ] **Step 4: Run proof-escape scans on all changed Lean files.**
- [ ] **Step 5: Run Stage-2 realization, cosmology-upgrade, V2-upgrade, and comparator gates.**
- [ ] **Step 6: Compare branch to main and verify only intended files changed.**

## Completion rule

The branch may be called a proof of the classical Hodge conjecture only if Task 7 closes with no conclusion-bearing assumptions and the axiom audit is clean. If Tasks 4 or 5 expose a missing semantic theorem, the deliverable is instead the strongest green reduction plus the exact Lean type of the missing theorem; do not label that state as a solved Millennium problem.