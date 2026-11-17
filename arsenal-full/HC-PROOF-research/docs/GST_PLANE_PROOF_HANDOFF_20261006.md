# GST plane proof work, 6 October 2026

Requested anchor: `8408fd0bd82444ed9e907aba4266db7674f566ee`.
Branch: `sol/hodge-strict-betti-correspondence-fusion-20261003`.
Edits are based on its later head `04bf4f14efbd8d152397ffd2ffbe8f22479d6125`.

## Actual premise removal

`nativeHodgeSeed_of_principalCut_point_nonzero` and
`principalCut_point_nonzero_gives_nativeHodgeSeed` no longer take
`ProjectiveDegreeTraceSemantics`. The proof uses the existing spine square:

`cl (successorNativeOperator Z) = principalCutPair.cohomologyOperator (cl Z)`.

The right side is already assumed nonzero in these theorems, so the left side
is nonzero directly. The native cut's Hodge type is supplied by the spine's
algebraic-Hodge theorem. Extracting an exact successor and then using positive
degree to reprove the same nonvanishing was unnecessary.

This removal is propagated through `PrincipalCutCorrespondenceGhostStrike`
(source, sheet hit, separator exclusion, word obstruction) and
`PrincipalCutSpectralFusion` (basis-cycle and finite-support target extraction).
Their remaining hypotheses and conclusions retain their original meanings.

This does **not** prove the input cohomological nonvanishing. For the separate
implication from native nonvanishing to cohomological nonvanishing, degree
semantics is still used, explicitly.

## Exact native survival classification

In `PrincipalCutNonzeroForcesExactSuccessor`, native cut nonvanishing is now
equivalent to nonemptiness of the actual exact-successor finset. Native zero
is equivalent to that finset being empty. With positive degree semantics,
native nonvanishing is equivalent to nonzero cycle class and to positive
degree trace. With the spine as well, it is equivalent to nonzero
cohomological principal-cut action.

Both directions have proof bodies using the branch's existing exact-stratum
filter, positive atom count, degree trace and commuting square. No universal
survival premise is introduced by these equivalences.

## Unconditional finite native construction

`CodimensionPointTower` now contains `NativeCutPath`, `NativeCutReached`,
`NativeCutStop`, and `nativeCutSearch`. For any requested finite weight, the
search starts at the actual codimension-zero apex and returns either:

- a point at that weight with a history of exact native cuts; or
- a reached lower-weight point whose exact next-cut locus is empty.

The latter has proved zero native and cohomological cut. This is a classical,
noncomputable construction, consistent with the existing geometric finsets.
A stop concerns the selected path: it does not exclude other paths or other
points at the target weight. No global bound on the GST universe is imposed.

The old uniform tower remains available with its explicit survival premise.
It is not an unconditional survival theorem. A populated codimension stratum
followed by an empty one provably contradicts that uniform premise.

## Intrinsic trace decomposition

For right pullback `R`, normalized trace `N`, and left pullback `L`, the trace
module now constructs `P = R N` and the carrier residual `Q = id - P`.
It proves:

- `omega = R (N omega) + Q omega`, uniquely with `N (Q omega) = 0`;
- `P` is idempotent and `Q omega = 0` exactly on `range R`;
- `BettiRelated alpha beta` iff `Q (L alpha) = 0` and `N (L alpha) = beta`;
- residual zero is equivalent to the existing quotient-obstruction zero;
- any two valid traces agree on every intrinsically transferable source.

`pushPull_eq_of_related` in the ray compiler now uses the direct left-inverse
argument. It no longer detours through the quotient transfer and a second
related target. Total push-pull by itself does not establish strict relation
totality or agreement with a prescribed matrix-unit target.

## Scope of the spine counterinstance

`zeroCycleClassSpine` explicitly satisfies every current spine field after
zeroing the cycle-class map. The native principal-cut operator is unchanged;
its cohomological realization is zero. With a nonzero Hodge state, this gives
a false Hodge statement and false common-class plane completeness despite
having a spine. The corresponding omniversal ghost is obtained from the
existing ghost equivalence.

This refutes a universal plane theorem from the Hodge datum and spine alone.
It does **not** refute the stronger conditional theorem that also assumes
positive projective degree semantics: `no_degreeTrace_for_zeroCycleClass_at_point`
explicitly proves that the zero instance cannot have those semantics at an
inhabited codimension.

## Exact completion status

These edits do not establish unconditional GST plane completeness. The current
uniform-tower route still requires independently supplied degree semantics,
native survival, and the strict source-to-ghost target packet. The original
plane-completeness/Hodge equivalence cannot discharge those premises by using
its own conclusion. No new axiom, `sorry`, `admit`, unsafe escape or
`native_decide` was added.

Compilation and kernel checking are assigned to GLM by the user. No local Lean
installation or build was run in this pass. Static review checked the modified
modules for proof-escape declarations, checked the local import dependency
closures for cycles, checked changed call sites after premise removal, and ran
`git diff --check`. Those checks do not certify Lean elaboration.

Suggested compile order for the changed modules:

1. `GSTClassicalHodgeGeometricCycleClassSpine`
2. `GSTClassicalHodgeStrictCorrespondenceBettiTracePushPull`
3. `GSTClassicalHodgeOmniverseStrictRelationRayCompiler`
4. `GSTClassicalHodgePrincipalCutNonzeroForcesExactSuccessor`
5. `GSTClassicalHodgePrincipalCutCorrespondenceGhostStrike`
6. `GSTClassicalHodgePrincipalCutSpectralFusion`
7. `GSTClassicalHodgeNativePointSeedDegreeUpgrade`
8. `GSTClassicalHodgeCodimensionPointTower`
9. `GSTClassicalHodgeCommonClassPlaneEquivalence`
10. `GSTClassicalHodgeCommonClassPlaneReduction`

The latest point-tower/reduction modules were already missing from the Lake
root registry at the inspected head; GLM should register the required roots as
part of its compilation pass. The mathematical edits add no new Lean module.
Run the included `#print axioms` commands after compilation. Compilation alone
does not remove any explicitly listed premise.
