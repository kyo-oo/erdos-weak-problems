# Classical Hodge Conjecture GST Landing Design

## Goal

Create a new Lean module `HodgeConjecture.lean` whose final theorem is the genuine rational Hodge-conjecture target for smooth projective complex schemes represented by the repository's Stage-2F/2G semantic stack, and whose proof route uses the limitless GST cosmology to construct the missing geometric realization rather than assuming cycle-class surjectivity.

## Ground-truth target

For a smooth projective complex scheme `V`, a Stage-2G package `H : HodgeBigradedBettiData V`, every natural codimension `p`, and every rational Betti class `alpha` whose complexification lies in the `(p,p)` Hodge summand, construct an actual native codimension-`p` algebraic cycle `Z : codimensionCycles V.X p` with

```lean
H.cycleClass p Z = alpha
```

Equivalently, prove `BigradedBettiHodgeStatement V H` for the canonical classical package once the repository has supplied the required genuine Hodge bigrading, analytification, and cycle-class map.

The project must not call a theorem about the finite GST `WaveCoef` carrier a proof of the classical statement merely because it is named `hodge_conjecture` or `clay_hodge_conjecture`.

## Existing verified spine

The new file will reuse the current green stack rather than recreate it:

- `GSTProjectiveOverC`: actual smooth/projective complex-scheme carrier.
- `GSTGeometricRealizationStage2D`: native codimension-`p` algebraic-cycle submodule.
- `GSTGeometricRealizationStage2F`: native rational singular cohomology of the supplied analytification.
- `GSTGeometricRealizationStage2G`: Hodge bigrading, derived rational `(p,p)` subspace, and the exact classical landing theorem from a compact realization family.
- `GSTWorldCosmology`, `GSTUniversalAddressBridge`, `GSTDimensionFreeHodgeDiagonal`, `GSTGlobalPureHodgeCosmology`, `GSTTruncatedWorldCohomologyRing`, `GSTWorldPoincareDuality`, `GSTUniversalLefschetzCosmology`, `GSTUniversalLefschetzDynamics`, `GSTUniversalLefschetzKernel`, `GSTUniversalLefschetzPathFormula`, `GSTTransferBridgeV2`, and related limitless modules: unbounded address, diagonal, grading, transport, cohomology, duality, and operator structure to be used as the constructive source.

No theorem in the above list may be treated as stronger than its formal type.

## Proof architecture

### 1. Public classical target

`HodgeConjecture.lean` will expose a transparent target definition/theorem at the Stage-2G level rather than inventing a weaker surrogate.

The first target will not quantify over an arbitrary fake cycle-class map. It will work with the repository's Stage-2G classical semantic package and will preserve the distinction between supplied semantic data and the theorem being proved.

### 2. Exact missing theorem

The first substantive construction target is the rank-free Stage-2G obligation with no additional conclusion-bearing hypothesis:

```lean
theorem gst_classical_compact_realization
    (V : SmoothProjectiveComplexScheme)
    (H : HodgeBigradedBettiData V) :
    Stage2GCompactRealizationObligation V H := by
  -- constructive proof only
```

This theorem must construct, for every `p`, a `Stage2GCompactRealization V H p`.

If Lean shows that `HodgeBigradedBettiData` still lacks a genuinely canonical geometric datum needed to even state the intended classical object, that missing datum must be introduced in a separate definition/theorem with a precise semantic role. It may not contain cycle-surjectivity, basis-cycle preimages, `Stage2GCompactRealizationObligation`, `BigradedBettiHodgeStatement`, or anything propositionally equivalent to them.

The construction must eventually populate the underlying

```lean
CompactHodgeRealization ℕ
  (RationalSingularCohomology H.analytification (2 * p))
  (codimensionCycles V.X p)
```

without assuming its surjectivity consequence.

### 3. GST encoding side

The unlimited GST address machinery will be used to construct or justify:

- a countable address space;
- a linear `encode` map into a finitely-supported rational address carrier;
- injectivity of the encoding on the relevant Hodge fiber;
- the live Hodge-support predicate;
- exact support of every rational `(p,p)` class after transport into GST coordinates;
- compatibility with grading, Hodge diagonal, recoordination, Lefschetz, and duality where those laws are actually needed.

A finite `Fin 12` chart may be used only as a proved specialization. It may not become the global classical cohomology carrier.

### 4. Geometric basis-cycle side

The decisive field is the genuine basis-cycle constructor:

```lean
basisCycle : ℕ → codimensionCycles V.X p
```

with the exact address law required by `CompactHodgeRealization` on live Hodge coordinates.

The proof must derive these cycles from actual native `AlgebraicCycle` values on `V.X` through a new theorem connecting the GST diagonal/address generator to the supplied classical `cycleClass` map. This is the place where the transformed GST Hodge result must land back in classical geometry.

It is forbidden to satisfy this field by:

- adding an axiom;
- adding a hypothesis equivalent to `BigradedBettiHodgeStatement`;
- adding a hypothesis equivalent to cycle-class surjectivity;
- choosing cycles with `Classical.choose` from the conclusion being proved;
- defining a semantic package that already contains the required basis-cycle preimages;
- identifying arbitrary classical cohomology with `Fin 12 → ℚ` without a proved equivalence.

If existing GST theorems do not yet construct this bridge, the implementation must expose and then attack the smallest missing bridge theorem directly.

### 5. Final closure

After `gst_classical_compact_realization` is proved, the final theorem should close by the already-green landing theorem:

```lean
exact
  GSTGeometricRealizationStage2G
    .bigraded_betti_hodge_of_stage2g_compact_obligation
      V H (gst_classical_compact_realization V H)
```

No additional mathematics should remain after that call except universal quantifier plumbing.

## Module boundaries

### New file

`HodgeConjecture.lean`

Responsibilities:

- state the genuine classical target;
- define only non-circular bridge structures if absolutely required;
- construct the GST-to-classical compact realization;
- prove the final classical Hodge statement;
- print axiom profiles for all capstone theorems.

### Existing files

Existing green modules are initially read-only. Surgical strengthening of an existing module is permitted only when a missing lemma naturally belongs there and doing so avoids duplicating an internal theorem in `HodgeConjecture.lean`.

No broad refactor of the cosmology is part of this proof task.

## Lean safety requirements

The finished proof surface must satisfy all of the following:

- no `sorry`, `admit`, placeholder proof, or `False.elim` from an inconsistent imported assumption;
- no new `axiom` or `constant` used as an unproved mathematical fact;
- no theorem whose hypothesis is propositionally equivalent to its conclusion;
- no hidden `Nonempty` assumption for the realization being constructed;
- no use of the finite GST Hodge classification as a type-level replacement for arbitrary classical cohomology;
- all new capstone theorems receive `#print axioms` receipts;
- compile under the repository-pinned Lean/Mathlib toolchain;
- preserve all pre-existing green workflows.

## Validation strategy

The work proceeds from the narrowest target outward:

1. Compile a minimal `HodgeConjecture.lean` import shell.
2. State the exact classical target and verify it elaborates.
3. State `gst_classical_compact_realization` with no conclusion-bearing assumptions.
4. Build the GST address/diagonal encoding components and compile after each coherent burst.
5. Attack the actual algebraic-cycle basis bridge.
6. Construct `Stage2GCompactRealizationObligation`.
7. Close `BigradedBettiHodgeStatement` through the existing Stage-2G landing theorem.
8. Run `#print axioms` on the new bridge and final theorem.
9. Run the repository's Stage-2 realization, cosmology-upgrade, V2-upgrade, and other relevant existing CI gates.
10. Audit the changed files for `sorry`, `axiom`, circular realization assumptions, and accidental finite-carrier substitutions.

## Failure semantics

A green file is not considered a proof of the classical Hodge conjecture if the algebraic-cycle bridge is merely assumed. If Lean exposes a missing theorem between the limitless GST Hodge generator and genuine codimension-`p` cycles on arbitrary `V.X`, that theorem becomes the active mathematical target. The implementation will strengthen the internal derivation rather than weaken the classical statement.

## Success criterion

Success is a green `HodgeConjecture.lean` in which the final theorem has the genuine Stage-2G classical target, the proof has no custom axioms or conclusion-equivalent assumptions, every rational `(p,p)` class receives an actual native codimension-`p` algebraic-cycle witness, and the repository's relevant CI gates remain green.
