# OpenAI/GST source correction and cubic dressing

Date: 2026-10-28. Branch: `research/gpt6-native-point-primitive-span-20261017`.
Base: `f8d557bb840134cac00a3fb4267aa5bb611501f2`.
Upstream reference: `openai/math@7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a`.

The owner requested mathematical source and Lean upgrades, explicitly leaving
compilation to them. This record reports source changes and mathematical
evidence; it does not turn draft Lean text into a kernel verification claim.

## Concrete results

Six new Lean modules and three modified existing modules add 51 theorem
declarations, strengthen the existing torsion theorem, and replace three
records containing truth-valued descriptions with actual maps/equations.

| File | Stronger statement or construction | Precise scope |
| --- | --- | --- |
| `GSTExactSequenceTorsion.lean` | Actual `a*b` annihilation through exactness; 16-bound; injectivity from zero inflation | Arbitrary abelian groups; actual exactness and torsion equations |
| `GSTLawStackRound29.lean` | `uniform_kill_of_five_term` now concludes `16 • c = 0`; concentration is derived; envelope intertwining and square-zero span are equations | Cohomology specialization remains an explicit input; no `True` stubs |
| `GSTCubicNilpotentDressing.lean` | `1+2x+2x²` integrates commuting spans with vanishing triple products, including nonzero squares; explicit inverse and unit lift | Arbitrary associative rings; genuinely extends the square-zero case |
| Same | Exact Heisenberg central correction and nonzero-scale area-coboundary obstruction | Arbitrary integer inputs; commutativity cannot simply be dropped |
| `GSTFiniteSourceCorrection.lean` | Exact residual after n stages; local nilpotent correction; finite polynomial correction with q(1) nonzero | No finite-dimensional assumption; no pairwise source-return commutation |
| `GSTClassicalHodgeFiniteSourceCorrection.lean` | Actual target-dependent native cycles assembled from heterogeneous solved sources, then corrected by those formulas | Original target and codimension retained; source algebraicity, naturality and a residual certificate are explicit inputs |
| `GSTClassicalHodgeCMNativeRationalDescent.lean` | Explicit rational cycle from finite extension-coefficient cross-carrier images | Removes the unnecessary `GeometricMultiSourceChowBirth.hodgeSpan` input; allows Qbar periods |
| `GSTSplitBoundaryProjection.lean` | Exact projection onto ker d from d h d = d; exact remaining type condition | Linear algebra; class preservation is a separate equation |
| `GSTComplexTangentProjectionChainObstruction.lean` | Explicit repair is closed but loses type; simultaneous closed/type-fixed subspace in the Fourier block is zero | Exact coefficient model of the torus example; no integral-current construction is inferred |
| `GSTOpenAISourceCorrectionUpgrade.lean` | Import and declaration-check entry point for the whole update | Registered as library `GSTOpenAISourceUpgrade` |

### What was previously restricted

The branch's latest square-zero dressing law required every within-span product
to vanish. The new cubic result admits J with J² nonzero and J³ zero, and proves
a multiplication law with integral coefficients. The full multiplication
defect is displayed before hypotheses are imposed. Its alternating term is
exhibited as a genuine obstruction when the realization does not commute.

Earlier exact-retract/multisource interfaces assumed an exact reconstruction
in one step. The new system can leave an error N, build cycles using successive
target residuals, and finish whenever a finite annihilator of that target has
nonzero value at 1. The individual source operators may fail to commute. A
two-dimensional explicit witness verifies that this enlarges the permitted
operator configurations. A diagonal error with eigenvalues 2 and 3 shows that
the polynomial case extends beyond nilpotence.

Earlier CM multisource coefficient descent accepted a packet with a universal
`hodgeSpan` field even though its proof used only one finite expansion. The new
constructor takes only the actual source cycles, transfer naturality, and that
target-specific expansion. It preserves the arbitrary coefficient extension.

## Mathematical derivation and source analysis

The [complete hand derivation](../derivations/GST_projection_correction_and_cubic_dressing_2026_10_28.tex)
precedes the Lean implementation. The [source manifest](openai_gst_sources_20261028.json)
pins the inspected upstream texts and selected formal conclusions by blob SHA.

| OpenAI source | What was inspected | Application verdict |
| --- | --- | --- |
| CM Hodge manuscript | Introduction, surface criterion with its proof, assembly with its proof, comparator statement and solution wrapper | Exact source scope extracted. Applying the upstream result to the repository's supplied semantics is conditional on canonical comparison. No external axiom was introduced. |
| Smooth immersion into four-space | Exact-correction proposition, smoothing construction and iteration setup; formal-scope documentation | Method inspiration only. The finite algebraic correction here is independently derived. No smooth immersion theorem is used to assert algebraicity. |
| Projection moments and cap domination | Projection-density section and its proof mechanism | Real projection measures are distinguished from native cycle-class images. No unsupported Chow bridge is asserted. |
| Petty projection-volume manuscript | Main theorem, definitions, proof structure and selected Lean conclusion | Convex-body inequality and equality scope authenticated. Not a Hodge-source theorem. |
| Smooth local three-space obstruction | Main statement, full-jet restriction, proof structure and selected Lean conclusion | Shows why unrestricted smooth realization cannot be inferred from finite-order/formal information. No inference to an algebraic source is used. |

These are selected-section analyses, not independent audits of every proof in
the five manuscripts or all 721 manuscripts in the upstream catalogue.
The comparator challenge's placeholder is a statement fixture; the inspected
CM solution wrapper points to the actual upstream solution. Neither is copied
into this project as a replacement for a proof or a canonical-semantics bridge.

## Executed routes at arbitrary (X,p,alpha)

1. **CM-source route:** construct source readouts of the prescribed target,
   source representatives when independently supplied by the source theorem,
   and finite cycles Z_n on original X. Their exact class is alpha−N^n alpha.
   The finite/polynomial criterion completes the construction on its stated
   domain. There is no theorem here constructing such a packet for every X.
2. **Multiplicative reconstruction route:** derive the entire noncommutative
   polynomial defect; cubic commuting spans succeed with an integral correction.
   Noncommuting spans can retain the area cocycle at every nonzero scale.
   Thus the old square-zero proof cannot be generalized by discarding its
   product hypothesis. This is a decisive obstruction to that proposed route,
   not an obstruction to every future geometric construction.
3. **Smooth projection route:** repair the boundary with the splitting law,
   then calculate the remaining type defect exactly. The explicit Fourier
   block has no nonzero vector satisfying both demands. Therefore real smooth
   correction alone supplies neither the required type nor an algebraic cycle.

The original universal canonical Hodge source constructor is not established.
The new geometry adapters remain conditional precisely where source coverage,
canonical comparison or a target residual certificate is required. No full-rank
or exact target-span premise is relabeled as an independent discovery.

## Verification and review provenance

Self-review of the displayed hand arguments: **proved as written under their
displayed hypotheses**. Review was performed by the implementing assistant;
there was no independent reviewer. Global novelty was not established; familiar
exact-sequence, resolvent, truncated-exponential and Heisenberg mechanisms are
not presented as newly discovered mathematics. The stronger theorem interfaces
and their integration are new relative to the inspected base revision.

Command:

```sh
python research/experiments/openai_gst_upgrade_checks.py --inventory research/maps/openai_gst_upgrade_inventory_20261028.json
```

Result: **8,472 checks passed, exit 0**. This count includes byte inventory and
source-integrity checks; it is not a count of 8,472 independent mathematical
theorems. Evidence is separated as follows:

- Exact symbolic identities in the free associative polynomial ring verify
  the full dressing multiplication defect, its commuting cubic quotient and
  the inverse polynomial. These identities are universal algebra checks.
- Finite matrix checks cover commuting cubic spans with four coefficients in
  −2…2, the Heisenberg law on six coefficients in −1…1, noncommuting scales
  −8…−1 and 1…8, cyclic extension models 1≤a,b≤10 with every middle element,
  and nilpotent correction orders 1…8. Their finite ranges are not universal
  geometric evidence.
- The original **1,350 tracked files / 17,013,984 bytes**, including all **708
  Lean files**, were read from the pinned base for a complete byte/lexical
  inventory. The [inventory](../maps/openai_gst_upgrade_inventory_20261028.json)
  records hashes and lexical metadata. This is not semantic review of all 708
  proof bodies. Detailed reading concerned the cited foundational, transfer,
  coefficient-descent, obstruction, law-stack and current research records.
- The local Lean import graph is acyclic; every new library root exists;
  the nine changed/new Lean files have no proof-escape declarations or
  truth-valued stubs under the recorded lexical scan. This is not elaboration.
- Two original files, `ComparatorSmokeChallenge.lean` and
  `ComparatorSmokeSolution.lean`, contain unclosed nested header comments.
  They are recorded as pre-existing lexical anomalies and were not edited.
- `git diff --check` passed. No Lean installation, local Lean compilation,
  CI dispatch or kernel-axiom audit was run, honoring the owner's instruction.

The `#print axioms` commands in the Lean files are instructions for the later
owner run, not receipts from this session. Historical green CI runs do not
certify this revision.
