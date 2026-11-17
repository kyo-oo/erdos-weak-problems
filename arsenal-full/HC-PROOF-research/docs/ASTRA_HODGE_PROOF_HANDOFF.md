# Astra Hodge mathematics handoff

Base: `sol/hodge-pure-math-engine` at `e8fd33125e33fc9bdfe91c55b218b3d50ab07515`.
Proof branch: `astra/hodge-proof-development`.

BOSS assigned Lean compilation to GLM. No Lean or Lake compiler command was
run for these changes. All new proof bodies are written; elaboration and kernel
verification remain to be performed. No existing theorem statement was weakened.

## Mathematical results written

1. `exists_joint_marginals_iff` in `GSTClassicalHodgeFiberedNativePullback`:
   given one anchor label and one anchor native point, finite multiplicity and
   native-point addresses have a common labelled lift exactly when their total
   masses agree. The lift is the explicit formula
   `attachPoint a + attachSheet b - mass(a) • anchor`.
2. `nativeLinearMap_eq_zero_of_points` in `GSTClassicalHodgePointNormalForm`:
   genuine codimension-point cycles detect arbitrary rational-linear maps out
   of the native cycle space, using the existing exact projective point normal
   form.
3. `tensorWord_descends_native_iff_zero` in
   `GSTClassicalHodgeFiberedNativeTensorArsenal`: with distinct source labels
   `i` and `k`, a tensor word `E(i,j) ∘ lift(A)` factors through native-cycle
   realization if and only if `A = 0`.
4. `tensorWord_descends_cycleClass_iff_zero` in the same module: factoring that
   tensor word through actual cycle class is possible if and only if
   `(H.cycleClass p).comp A = 0`.

## The decisive calculation

For a native point `x`, set `delta = atom i x - atom k x`, with `i != k`.
Native realization sends `delta` to zero. The multiplicity matrix unit selects
its first atom. A tensor word then has native image `A(pointCycle x)`.
Consequently any descended operator would have to send zero to that image.
Applying actual cycle class forces `cycleClass(A(pointCycle x)) = 0`.
Point normal form extends this equality from every point to every native cycle.

This is an obstruction to the latest independent-factor externalization route,
not a disproof of the Hodge conjecture. Commutation of the two factors does not
provide the missing geometric cycle-class square.

## Classical target status

The unconditional classical Hodge theorem has not been proved by these commits.
The repo already records `not_classicalHodgeTarget_of_zero_cycleClass` in
`HodgeConjecture.lean`: the supplied semantic package permits arbitrary linear
cycle-class maps. A proof for a genuinely geometric package needs a construction
of the actual cycle-class compatibility, not equality after total-mass projection.
No additional surjectivity, basis-cycle witness, or matrix-unit invariance
assumption has been inserted to claim closure.

## Verification handoff

Compile the three changed modules with their existing dependency closure,
ending with `GSTClassicalHodgeFiberedNativeTensorArsenal`.
Its existing imports include the two other changed modules transitively.
The inherited registry does not yet list every recent Sol proof module; GLM
should include the relevant local import closure in its compilation setup.
Each new capstone has a `#print axioms` receipt. A source-token audit found no
new proof escapes. This audit is not a substitute for Lean verification.
