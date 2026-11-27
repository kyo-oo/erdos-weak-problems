# Hodge final integration: two-burst handoff

Target branch: `sol/hodge-conjecture-final-integration`.
Inspected base: `41f20ed3a2b7ed44ed501b1a7c39e58f82f1c752`.
Original failing run: `36317899388`, job `108615974806`.

## Mathematics and scope

This pass continues the existing GST Hodge route. It does not replace the
cosmology, change the Hodge target, or assume the missing conclusion.

The original run reported errors in three modules:
`GSTClassicalHodgeRankFreeArsenalIrreducibility`,
`GSTClassicalHodgeCyclicSpectralGeneration`, and
`GSTClassicalHodgeExplicitArsenalGeneration`.
Their statements have proofs by the already specified coordinate, spectral,
and GST operator calculations. The repairs retain those statements and
hypotheses. The spectral reconstruction uses basis span, which does not need
a finite instance for the unrestricted Hodge basis index.

The final public theorem `HodgeConjecture.unified_hodge_finale` additionally
takes the following inputs. Their presence is independent of compilation:

* `GeometricCycleClassSpine V H`, including actual cycle-class naturality
  and compatibility with the geometry-built principal-cut operator;
* `SpineTowerNonvanishing G`, asserting that the constructed spine seed is
  nonzero whenever the Hodge subspace is nonzero;
* `FullProjectiveCosmicExternalization G`, requiring, for every weight and
  ordered pair of Hodge basis indices, a `ProjectiveNativeKernel` whose
  cohomological action agrees with `canonicalCosmicAmbient` on the Hodge fiber.

The definitions and consumers of these inputs were inspected on the target
branch. This pass did not find or construct a family discharging them.
In particular, the externalization predicate quantifies over every Hodge
vector: the existing tensor commutation theorem alone does not supply its
cycle-class comparison equation. Nonvanishing of a cosmic normalization
coefficient alone does not establish nonvanishing of the resulting geometric
cycle class. These are precise mathematical construction tasks, not Lean
syntax failures. No completion claim for these tasks is made here.

## Burst 1

Published commit: `5619f20932c096b65caa4bb3606fea5a3536a50d`.

* Correct the stale `hki` reference to the actual `hik` hypothesis.
* Define polynomial action with the scalar algebra map (`Polynomial.aeval`).
* Prove monomial action, stability under powers, spectral evaluation, and
  isolator normalization using the pinned API.
* Restore finite-sum unfolding and the missing namespace closure.
* Use the existing native `windowMirror` consistently in Poincare conjugation
  and backward arsenal words; expose normalized forward action before rewriting.

## Burst 2

* Prove polynomial intertwining for an existing linear-map commuting square,
  then use it in `cycleClass_cyclePolyEval`.
* Prove polynomial evaluation on an eigenvector including eigenvalue zero,
  and use it to justify the augmented isolator's annihilation of the complement.
* Correct the dependent finite-support conjugation proof for the source-first
  inequality used by the repaired matrix-unit theorem.
* Isolate the forward-word normalization from the outer coordinate scalar
  before cancelling the nonzero central-binomial coefficient.

## Verification and stopping point

The two bursts add no `sorry`, `admit`, custom axiom, or unsafe implementation.
Source diff whitespace checks pass. New mathematical helpers have explicit
`#print axioms` receipts. Existing final theorem hypotheses are retained.

The existing final-integration workflow is triggered by commits on the target
branch. No local Lean installation/build was started. No green result is
claimed for this pass: use the workflow for the second burst's exact commit
for compiler status. A green result validates the declarations with their
displayed hypotheses; it does not construct the inputs listed above.

Stop after the second source-repair burst as requested. Compiler follow-up
belongs to BOSS/GLM. No subagents were used.
