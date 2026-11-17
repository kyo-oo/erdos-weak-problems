# GST Coherent-Native Ghost Obstruction — Design

## Purpose

The branch-packet plane realization problem asks for a strict geometric
carrier taking a genuine native seed class `a` to the GST matrix-unit target
`c e_j`, without assuming that `e_j` already has an algebraic representative.
The live branch now proves two facts that constrain any honest continuation:

1. `ghostBranchEvent_exists_but_strictPacket_empty` proves that, under a
   hypothetical omniversal separator ghost, the intrinsic GST branch exists
   while the corresponding strict relation packet is empty.
2. `survival_and_targetStrictClosure_iff_hodge` proves that native-seed
   survival together with the requested minimal strict closure is exactly the
   Stage-2G Hodge conclusion.

Consequently, the missing carrier cannot be manufactured by repackaging the
existing branch, recoordination, or native-descent laws. The next legitimate
mathematical step is to determine whether the new coherent-native machinery
can supply the missing action. This design proves that it cannot: every
cycle-class-descending coherent native action has an explicit nonzero defect
against the ghost-selected branch target.

The result is not presented as a proof of Hodge. It is an unconditional GST
theorem identifying the exact obstruction that any future carrier
construction must defeat.

## Mathematical setting

Fix a smooth projective complex scheme `V`, Stage-2G data `H`, a geometric
cycle-class spine `G`, an omniversal separator ghost `E`, and a genuine native
Hodge seed `S` in weight `E.weight`.

Write

- `cl` for `H.cycleClass E.weight`;
- `N` for the projection from the labelled fibered native universe to genuine
  native cycles;
- `U` for an arbitrary labelled native endomorphism;
- `C_i(U)` for its native column at sheet `i`;
- `i₀` for an anchor sheet;
- `A = C_i₀(U)` for the anchor native action;
- `T_A` for the ambient cohomology action constructed by
  `nativeAmbientAction cl A` from preservation of `ker(cl)`.

The already-proved two-obstruction law states that `U` descends through actual
cycle class exactly when

1. all native columns agree after applying `cl`; and
2. the anchor column preserves `ker(cl)`.

Under those two theorems, `T_A` is constructed rather than supplied.

For the seed class `a = cl(S.cycle)`, the commuting square gives

\[
T_A(a)=\operatorname{cl}\bigl(N(U(\operatorname{section}_{i_0}
S.\mathrm{cycle}))\bigr).
\]

The right-hand side is the class of a genuine native cycle. Therefore the
ghost detector kills it. If

\[
\beta=E_{i j}(a)=c e_j,
\]

where `i = S.sourceIndex` and `j = E.sheet`, then the matrix-unit theorem gives

\[
\boxed{
E.\mathrm{detector}\bigl(T_A(a)-\beta\bigr)
=-c\,E.\mathrm{detector}(e_j)\ne 0.}
\]

Thus `T_A(a) != beta`. Column coherence, routing, tensor cancellation, and
finite native relation preservation can construct ambient actions, but none
can turn a genuine native source into the ghost-detected non-native target.

## New module

Create `GSTClassicalHodgeCoherentNativeGhostObstruction.lean`.

It will import:

- `GSTClassicalHodgeCoherentNativeDescent` for native columns, the
  two-obstruction law, routed lifts, and finite tensor blocks;
- `GSTClassicalHodgeCommonClassPlaneReduction` for the exact branch target,
  ghost/seed vocabulary, and the established strict-carrier frontier.

The module must not import a Hodge finale as a proof device, assume a strict
relation packet, assume a target cycle, or introduce a custom axiom.

## Theorem family

### 1. Native-range annihilation

Prove a reusable theorem saying that an omniversal ghost detector annihilates
the actual cycle class of every genuine native cycle at the ghost weight.

Intended form:

```lean
theorem ghost_kills_nativeCycleClass
    (G : GeometricCycleClassSpine V H)
    (E : OmniversalSeparatorGhost G)
    (Z : codimensionCycles V.X E.weight) :
    E.separator.detector (H.cycleClass E.weight Z) = 0
```

The proof specializes `E.kills_all_native_programs` to the identity graded
geometric program. This keeps the argument inside the established GST
omniverse and avoids re-proving point-span normalization.

### 2. Any descending labelled action is invisible on a native seed

For arbitrary `U`, arbitrary ambient `T`, and an explicit commuting-square
proof

```lean
((cl.comp N).comp U) = T.comp (cl.comp N),
```

prove

```lean
E.separator.detector (T S.hodge.1) = 0.
```

Evaluate the commuting square on `nativeSection i₀ S.cycle`, use
`toNativeCycle_nativeSection`, rewrite by `S.class_eq`, and apply the first
theorem to the genuine native output of `U`.

This theorem isolates the only property used by the obstruction: descent
through the actual native cycle-class map.

### 3. Exact coherent-action defect formula

Under the same commuting square, prove

```lean
E.separator.detector
    (T S.hodge.1 -
      (hodgeMatrixUnit S.sourceIndex E.sheet S.hodge).1) =
  -(hodgeCoordinate S.sourceIndex S.hodge *
    E.separator.detector
      (classicalHodgeBasis V H E.weight E.sheet).1)
```

The proof combines native-seed invisibility with
`hodgeMatrixUnit_apply`, linearity, and the live source coefficient.

Then prove:

- the displayed defect is nonzero;
- `T S.hodge.1` is not the matrix-unit target;
- no descending ambient-action witness can realize the requested branch.

The nonzero theorem must use exactly
`S.sourceCoefficient_ne_zero` and `E.separator.detects_basis`; it must not use
the already-proved strict-packet emptiness theorem. This provides an
independent proof at the coherent-native layer.

### 4. Remove the ambient-action premise

Specialize the preceding results to the ambient action constructed by the
two-obstruction theorem. Given

```lean
hcolumns : forall i,
  cl.comp (nativeColumn i U) = cl.comp (nativeColumn i₀ U)
hkernel : NativeClassKernelStable cl (nativeColumn i₀ U)
```

let

```lean
T := nativeAmbientAction cl (nativeColumn i₀ U) hkernel.
```

Prove directly that `T` has the exact nonzero branch defect and misses the
target. The commuting square is derived from `cycleClass_descent_iff`; it is
not accepted as another premise.

This is the main theorem of the module.

### 5. Routed and finite-tensor consequences

Add two corollary families showing that the complete coherent constructions
introduced at the current branch head do not evade the obstruction:

- for `routedNativeOperator rho A`, kernel stability of `A` constructs the
  ambient action, but its value on the native seed cannot be the ghost target;
- for `finiteTensorBlock A`, post-cycle-class column agreement plus anchor
  kernel stability constructs the ambient action, but its value on the seed
  cannot be the ghost target.

The finite-tensor corollary is placed in a section with the existing `Fintype`
assumption. It must use `finiteTensorBlock_cycleClass_descent_iff`, so the
result covers cancellations among tensor words rather than only isolated
words.

## Documentation update

Extend `docs/GST_NATIVE_COHERENCE_DISCOVERIES_20261006.md` with a section titled
`Coherent-native ghost obstruction`.

The section will record:

- the exact defect equation;
- why the action is derived from finite relation/coherence data;
- why the result covers routed lifts and complete finite tensor blocks;
- why it advances D by closing a false route rather than claiming the carrier
  has been constructed;
- the remaining positive requirement: genuinely geometric strict-carrier
  synthesis not factoring solely through an operator on native cycles.

## Registration

Register the module in `lakefile.toml` and import it from `HCProof.lean`, next
to the coherent-native descent modules.

Add `#check` and `#print axioms` receipts for the principal results. Expected
axioms are only Lean/mathlib foundations already present in the branch, such
as propositional extensionality, classical choice, and quotient soundness.
No custom mathematical axiom, `sorry`, or `admit` is permitted.

## Verification

The user explicitly assigned compiler repair to GLM and requested that this
work focus on pure mathematical writing. Accordingly, the acceptance checks
for this contribution are:

1. no `axiom`, `sorry`, or `admit` in the new module;
2. every target theorem derives the ambient action or receives an explicit
   commuting square, never a desired source-to-target action equation;
3. no target cycle representative occurs in any hypothesis;
4. no strict packet or common-plane packet occurs in any hypothesis;
5. the nonzero conclusion is proved from the live source coefficient and the
   ghost detector's basis witness;
6. imports and registration are internally consistent;
7. the branch diff contains only the designed theorem module, its
   documentation, registration, and planning artifacts.

Lean compilation will be attempted if the local environment can build the
module without diverting into unrelated branch repairs. Any compiler failures
will be recorded precisely for GLM; they will not be mislabeled as a green
build.

## Non-goals

This change does not:

- assert unconditional branch-packet plane completeness;
- add a carrier-existence axiom;
- infer an algebraic representative of `e_j` from an ambient linear
  extension;
- identify a labelled/native linear operator with a scheme correspondence;
- claim that the Hodge conjecture has been proved;
- modify unrelated Hodge or Erdős modules.

## Success criterion

The contribution is successful when the repository contains an unconditional
theorem, formulated entirely in the GST native omniverse, that exhausts the
new coherent-native descent route and proves its exact nonzero mismatch with
the missing branch-packet target. After this theorem, any proposed proof of D
must visibly introduce new strict geometric content rather than hiding the
target action inside coherence, routing, tensor cancellation, or ambient
extension.
