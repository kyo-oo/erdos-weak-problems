# GST Global Hodge Defect-Extinction Design

## Goal

Use the repository's full GST cosmology—not merely classical correspondence theory—to drive the exact rational Hodge target:

> For every smooth projective complex variety `X`, every rational Hodge class in `H^(2p)(X,Q) ∩ H^(p,p)` is the class of a rational algebraic codimension-`p` cycle, equivalently a finite rational combination of algebraic cycle classes.

The implementation must terminate at `GSTClassicalHodgeExactClayStatement.EveryHodgeClassIsFiniteRationalCombination H`, not at a weaker reachability, visibility, or operator-stability proxy.

## Existing GST machinery to use as first-class mathematics

The route must consume the strongest existing GST layers directly:

- `GSTTruncatedWorldCohomologyRing`: the quotient cohomology ring `Z[H,V]/(H^B,V^A)`, its action, and the universal Lefschetz class.
- `GSTUniversalLefschetzCosmology`: native digit/carry endomorphisms, exact commuting binomial calculus, grading, and dimension-free Poincare interface.
- `GSTWorldPoincareDuality`: nondegenerate finite and cosmic pairings and coordinate probes.
- `GSTWorldRecoordinationGroupoid`: exact chart-independent state codes, recoordination, code projectors, and polynomial spectral projectors.
- `GSTDimensionFreeHodgeDiagonal` and `GSTGlobalPureHodgeCosmology`: unbounded pure-Hodge diagonal generators and finite-observation reconstruction.
- `GSTClassicalHodgeLimitlessCosmicMatrixUnits`: exact global read/write matrix units and irreducibility on the rational compact pure cosmos.
- `GSTClassicalHodgeFiberedNativePullback` and `GSTClassicalHodgeFiberedNativeRecoordination`: common refinement between Hodge multiplicity labels, actual projective point cycles, and limitless GST addresses.
- `GSTClassicalHodgeFiberedNativeTensorArsenal`: commuting multiplicity/native factors and the proven obstruction showing arbitrary multiplicity matrix units do not simply descend to native cycles.
- `GSTClassicalHodgeGradedGeometricProgramOrbit` and `GSTClassicalHodgeProjectiveWordOrbit`: the existing genuine geometric program algebra built from projective words and principal cuts.
- `GSTClassicalHodgeLimitlessSpinePropagation`: canonical algebraic origin and recursively generated nonzero projective spine.

## Central architectural correction

The classical Hodge basis currently appears to GST through local two-slot windows. That discards most of the limitless cosmology. Replace that viewpoint with one global sheet cosmos.

For every genuine classical Hodge basis sheet `(p,j)`, construct a canonical injective GST address

`sheetCode : Sigma (fun p => ClassicalHodgeBasisIndex V H p) -> Nat`.

The global Hodge sheet cosmos is the finitely-supported rational module on these addresses. Every classical Hodge fiber embeds coordinatewise into this one global object. Basis sheet `j` at weight `p` maps to the corresponding delta state.

This global representation must preserve:

1. basis coordinates;
2. finite support;
3. the GST read/write matrix-unit action;
4. recoordination invariance of finite observations;
5. Poincare/probe coordinate extraction.

## Global GST operator layer

Construct global sheet matrix units directly on the sheet cosmos:

`E_(p,i),(p,j)` reads the source sheet coordinate and writes it to the target sheet coordinate.

Prove the exact matrix-unit laws, nondegenerate probe laws, and irreducibility of any nonzero submodule stable under all same-weight sheet matrix units.

Relate these global operators to the existing `hodgeMatrixUnit` and `rationalCosmicMatrixUnit` constructions by explicit intertwining theorems. The global layer is not a new unrelated algebra; it is the common parent of the current finite/two-slot shadows.

## Geometry compiler

Do not attempt to descend arbitrary multiplicity matrix units through `toNativeCycle`; the repository already proves that this is generally impossible unless the native part is zero.

Instead compile only programs acting on the canonical synchronized algebraic source. The compiler consumes GST-native operations already justified in the cosmology:

- code/spectral projectors;
- recoordination;
- Poincare read operations;
- Lefschetz/principal-cut movement;
- finite noncommutative projective words;
- rational scaling/addition/composition.

The target is the existing `GradedGeometricProgram` algebra, whose executions preserve the genuine cycle-class range by construction.

The compiler theorem must be source-specific rather than a false global descent theorem:

For the canonical live algebraic source state in weight `p` and every target Hodge basis sheet `j`, compile a finite graded geometric program whose cohomological execution equals a nonzero rational scalar times the target sheet.

## Canonical algebraic origin and spine

Use the codimension-zero fundamental cycle and the normalized projective spine from `GSTClassicalHodgeLimitlessSpinePropagation` as the single genuine algebraic origin.

At every weight with nonzero Hodge fiber, produce a synchronized source:

- an actual native codimension-`p` cycle;
- its genuine Hodge class;
- a nonzero live coordinate selected by the GST probes.

No independent algebraic seed per basis sheet is allowed.

## Defect extinction

Assume one target Hodge sheet is outside the cycle-class range. Use the existing basis-separator machinery to obtain a rational detector annihilating the actual algebraic span and nonzero on that sheet.

Encode the detector's basis evaluations as a finite GST defect state. By nondegenerate GST Poincare/cosmic probing, select a detected coordinate. Use the global GST matrix-unit/spectral program to move the canonical algebraic spine source to that target coordinate.

The compiled geometric program produces an actual algebraic cycle class, so the separator must annihilate it. The GST action computes the same state as a nonzero scalar multiple of the selected target sheet, so the separator evaluates nonzero. Contradiction.

Thus no basis separator exists, every Hodge basis sheet is algebraic, and every rational Hodge class is an algebraic rational combination.

## Exact final theorem

The capstone theorem must have the form

```lean
theorem gst_exact_rational_hodge_conjecture
    (...) :
    GSTClassicalHodgeExactClayStatement.EveryHodgeClassIsFiniteRationalCombination H := by
  ...
```

The theorem may depend only on independently established geometric/topological semantics already required to interpret the genuine cycle-class map and genuine projective/principal-cut operations. It must not take any of the following as assumptions:

- `BigradedBettiHodgeStatement V H`;
- `EveryHodgeClassIsRationalAlgebraic H`;
- a basis-cycle bridge;
- universal sheet reachability;
- `ClosedCorrespondenceHitsSheet` for every sheet;
- arbitrary matrix-unit naturality;
- arbitrary Hodge-basis algebraicity;
- defect-zero / separator nonexistence.

## Files

Create these focused modules:

1. `GSTClassicalHodgeGlobalSheetCosmos.lean`
   - global sheet index/address encoding;
   - Hodge-fiber coordinate embedding;
   - global delta basis and probes;
   - exact relation to existing GST pure/cosmic coordinates.

2. `GSTClassicalHodgeGlobalSheetMatrixUnits.lean`
   - global same-weight matrix units;
   - exact composition/annihilation laws;
   - intertwining with `hodgeMatrixUnit` and GST cosmic read/write;
   - irreducibility/saturation theorem.

3. `GSTClassicalHodgeGSTSpectralProgramCompiler.lean`
   - GST program syntax or compilation lemmas using existing world/cosmic/projective machinery;
   - source-specific compilation to `GradedGeometricProgram`;
   - cycle-class naturality inherited from the geometric-program algebra.

4. `GSTClassicalHodgeGSTSpineOrbitSaturation.lean`
   - canonical synchronized source from the algebraic spine;
   - GST source coordinate selection by probes;
   - target-sheet source-action theorem for compiled programs.

5. `GSTClassicalHodgeGSTDefectExtinction.lean`
   - separator -> GST defect state;
   - probe nonvanishing;
   - contradiction with algebraic-program annihilation;
   - every basis sheet in the cycle-class range.

6. `GSTClassicalHodgeGSTExactFinale.lean`
   - assemble arbitrary Hodge classes from algebraic basis representatives;
   - conclude `EveryHodgeClassIsFiniteRationalCombination H`.

## Verification discipline

- Each new theorem gets `#check` and targeted `#print axioms` audit entries.
- No theorem may be described as green until a compiler/CI result exists.
- GLM may repair Lean syntax/API mismatches, but it must not strengthen theorem hypotheses, replace constructions with assumptions, or reintroduce the Hodge conclusion through a packaged field.
- When a proposed GST operator cannot descend to native cycles globally, preserve the proven obstruction and weaken to source-specific execution rather than postulating descent.
- The exact Clay target remains the final acceptance criterion.