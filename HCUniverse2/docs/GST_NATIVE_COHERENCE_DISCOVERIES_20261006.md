# GST native coherence discoveries, 6 October 2026

These are extensions of the repository's own native GST universe and point
normal form. They introduce no target cycle representative, Hodge
completeness premise, or branch-packet realization axiom.

The proofs are written as Lean proof terms. Compilation of the new modules is
delegated to GLM, as requested; they are not being reported as compiled green.

## Verified starting theorems

The existing CI job
[112112392606](https://github.com/kyo-oo/HC-PROOF/actions/runs/37415272309/job/112112392606)
at commit `68302451849ac79965432a10bd1a6c3c2b45e8a7` records successful builds
of `GSTClassicalHodgePointNormalForm` and
`GSTClassicalHodgePointKernelOperatorLift`.

Its trust output for `compactCyclePresentationLinearEquiv` and
`PointClassTransitionKernel.nativeCycleOperator_natural` lists only
`propext`, `Classical.choice`, and `Quot.sound`. The overall integration run
failed in other modules; this is evidence for these specific compiled
theorems, not a claim that the whole branch was green.

The established point-kernel theorem takes a cohomological operator T and
point transitions already satisfying its point action equation. The first
upgrade below constructs T from raw native transitions instead. The other
upgrades classify coherence and ambiguity in the existing labelled native
universe, including coherent operators which isolated tensor words do not
describe.

## 1. Native-first finite-relation action synthesis

Let P be the finite native point presentations, C the genuine native cycle
space, and E:P→C the already-compiled exact point realization equivalence.
Let cl:C→B be the supplied actual cycle-class map.

Start with raw native data only:

\[
\kappa:x\longmapsto\text{a finite native point presentation}.
\]

Extend it to finite presentations by

\[
K(\phi)=\sum_x\phi_x\kappa(x),\qquad
A_\kappa=EKE^{-1}.
\]

The new law is

\[
\boxed{\begin{aligned}
&\exists T:B\to B,\quad \operatorname{cl}A_\kappa=T\operatorname{cl}\\
&\quad\Longleftrightarrow\quad
\forall\phi\in P,\quad
\operatorname{cl}(E\phi)=0\ \Longrightarrow\
\operatorname{cl}(EK\phi)=0.
\end{aligned}}
\]

**Derivation.** The forward direction applies T to a zero native class. For
the reverse direction, exact point normal form identifies the finite-relation
condition with Aκ preserving ker(cl). Define on the actual native class range

\[
\bar A(\operatorname{cl}Z)=\operatorname{cl}(A_\kappa Z).
\]

If cl(Z)=cl(W), the difference Z−W lies in ker(cl); its transformed class is
zero. Hence this definition is independent of the native preimage and is
linear. The repository's rational-linear extension device extends this
derived range action to B. Its native commuting square follows from the
construction.

The output then supplies the old point-kernel interface:

\[
\operatorname{cl}(E\kappa(x))=T(\operatorname{cl}[x]).
\]

T and this equation are derived outputs. Neither is an input field of the raw
kernel. No non-native class is assigned a native preimage by this argument.

Lean: `rawTransition_has_ambientAction_iff`,
`derivedPointClassTransitionKernel` in
`GSTClassicalHodgeNativePointRelationDescent.lean`.

## 2. Exact finite interaction law

Use the existing labelled native space F of finite states on atoms (i,x).
Write πL for `forgetPoint` and πP for `forgetMultiplicity`. Fix one available
label i₀ and one available genuine point x₀. Define

\[
R(i,x)=(i,x)-(i,x_0)-(i_0,x)+(i_0,x_0).
\]

Both marginals of R(i,x) vanish. Conversely,

\[
\boxed{\ker\pi_L\cap\ker\pi_P
=\operatorname{span}_{\mathbb Q}\{R(i,x)\}.}
\]

**Derivation.** For any Φ, reconstruct its marginal part by the existing
explicit gluing formula

\[
G\Phi=\operatorname{attachPoint}_{x_0}(\pi_L\Phi)
+\operatorname{attachSheet}_{i_0}(\pi_P\Phi)
-m(\Phi)(i_0,x_0).
\]

The established marginal mass balance proves that GΦ has exactly the two
marginals of Φ. Define Q=Id−G. Then

\[
Q(i,x)=R(i,x),\qquad
Q\Phi=\sum_{i,x}\Phi_{i,x}R(i,x),\qquad Q^2=Q.
\]

If both marginals of Φ vanish, GΦ=0 and Φ=QΦ, giving the claimed finite
generation. Conversely every generator has both marginals zero.

This upgrades the existing existence of joint marginals to a classification
of **every** joint state with prescribed balanced marginals:

\[
\{\Phi:\pi_L\Phi=a,\ \pi_P\Phi=b\}
=\operatorname{glue}(a,b)+(\ker\pi_L\cap\ker\pi_P).
\]

It also gives an exact test for a linear observable F to depend only on the
two marginals: F must annihilate the explicit rectangles. In that case

\[
F\Phi=F(\operatorname{attachPoint}_{x_0}\pi_L\Phi)
+F(\operatorname{attachSheet}_{i_0}\pi_P\Phi)
-m(\Phi)F(i_0,x_0).
\]

Changing the anchors changes the reconstruction by a joint-kernel state;
it changes none of its observed marginals.

Lean: `jointKernel_eq_rectangleSpan`,
`jointMarginals_iff_interaction_translate`,
`observable_marginal_formula_iff` in
`GSTClassicalHodgeNativeInteractionNormalForm.lean`.

## 3. Complete native-column classification

Let N:F→C be the existing genuine native projection. The green point
equivalence constructs a native section σi:C→F by attaching label i to the
actual point coefficients of a native cycle. Thus Nσi=Id. This is a section
of N; it is not a section of cl.

For an arbitrary labelled operator U, define its native source column

\[
C_i(U)=NU\sigma_i.
\]

Then

\[
\boxed{NU=AN\ \Longleftrightarrow\ \forall i,\ C_i(U)=A.}
\]

**Derivation.** Compose a commuting square with each σi to obtain the forward
implication. Conversely, test the column identities on every genuine point
cycle [x]. They give NU(i,x)=A[x] on every atom. Finite linear extension gives
NU=AN on all of F.

With one available anchor label i₀, existence and uniqueness are exact:

\[
U\text{ descends}\ \Longleftrightarrow\
\forall i,\ C_i(U)=C_{i_0}(U),\qquad A=C_{i_0}(U).
\]

Equivalently, U must annihilate native label differences after projection:

\[
NU\big((i,x)-(i_0,x)\big)=0\quad\text{for all }i,x.
\]

This tests the entire kernel, because the new exact generation law is

\[
\ker N=\operatorname{span}_{\mathbb Q}
\{(i,x)-(i_0,x)\}.
\]

No finiteness assumption on the label set is needed.

Lean: `nativeKernel_eq_sheetDifferenceSpan`,
`native_descent_iff_constant_columns`,
`native_descent_iff_sheetDifferences`, `native_descent_unique`.

## 4. Nonzero coherent routing and the complete freedom in a lift

For any total label routing ρ and any genuine native operator A, construct

\[
U_{\rho,A}(i,x)=\sigma_{\rho(i)}(A[x]).
\]

Its native columns are all A. Therefore

\[
NU_{\rho,A}=AN,
\qquad
U_{\tau,B}U_{\rho,A}=U_{\tau\circ\rho,BA}.
\]

The second identity holds on the whole labelled universe, since the routed
operator sends σi(Z) to σρ(i)(AZ). A total routing can merge labels or send
them all to one label. With an available source label,

\[
U_{\rho,A}=0\ \Longleftrightarrow\ A=0.
\]

This constructs nonzero native descenders despite the failure of individual
selected-source matrix units to descend.

The full classification of lifts of A is

\[
\boxed{NU=AN\ \Longleftrightarrow\
U=U_{\rho,A}+W\text{ for some }NW=0.}
\]

Subtract the explicitly constructed routed lift to obtain W. Conversely,
adding any native-invisible W preserves the native action. Label routing
before and after a coherent operator also preserves its exact native action.

Lean: `routedNativeOperator_descends`, `routedNativeOperator_comp`,
`routedNativeOperator_eq_zero_iff`, `native_lift_normal_form_iff`,
`native_descent_routing_invariant`.

## 5. Coherent finite tensor-block law

Only this specialization requires a finite label set. For a complete block of
native operators Aij, define

\[
U_A=\sum_i\sum_j E_{i\to j}\,\operatorname{lift}(A_{ij}),
\qquad B_i=\sum_j A_{ij}.
\]

The old atom-level tensor theorem computes each native column to be Bi.
The arbitrary-column theorem therefore gives

\[
\boxed{U_A\text{ descends}\ \Longleftrightarrow\
\forall i,\ B_i=B_{i_0}.}
\]

This permits nontrivial cancellations between individually obstructed tensor
words. For two labels, source columns with target contributions

\[
\begin{pmatrix}A+D\\-D\end{pmatrix},\qquad
\begin{pmatrix}E\\A-E\end{pmatrix}
\]

both have native column sum A. The complete block descends to A regardless of
the independent operators D and E.

Even without finitely many labels, cancellation of two target labels gives

\[
N\big(E_{i\to j}\operatorname{lift}(A)
-E_{i\to k}\operatorname{lift}(A)\big)=0.
\]

Lean: `finiteTensorBlock_descends_iff`,
`tensorTargetCancellation_nativeFace`.

## 6. Two-obstruction cycle-class law

Native descent and cycle-class descent have different exact tests. For
J=cl∘N and an arbitrary labelled operator U,

\[
\boxed{\begin{aligned}
\exists T,\ JU=TJ\quad\Longleftrightarrow\quad
&\forall i,\ \operatorname{cl}C_i(U)=\operatorname{cl}C_{i_0}(U),\\
&C_{i_0}(U)(\ker\operatorname{cl})\subseteq\ker\operatorname{cl}.
\end{aligned}}
\]

**Derivation.** A factorization gives both conditions after composing with
the native sections. Conversely, the native-first relation theorem constructs
T for the anchor column. Agreement of the class columns then verifies JU=TJ
on every point atom, hence on every finite state.

Native columns may differ by homologically invisible output. The second
condition remains necessary: agreeing columns alone does not preserve native
cycle-class relations. For a finite tensor block, replace Ci by the explicit
column sums Bi.

Any two ambient actions satisfying the commuting square agree on cl(C). The
proof gives no unique action on classes outside that actual range.

Lean: `cycleClass_descent_iff`,
`routedNativeOperator_cycleClass_descent_iff`,
`finiteTensorBlock_cycleClass_descent_iff`,
`cycleClass_descent_range_unique`.

## 7. Coherent-native ghost obstruction

The two-obstruction law constructs an ambient action, but it cannot by itself
produce the ghost-selected branch target.  Let `E` be an omniversal separator
ghost, let `S` be a genuine nonzero native/Hodge seed at `E.weight`, and put

\[
 a=\operatorname{cl}(S.\mathrm{cycle}),\qquad
 \beta=E_{S.\mathrm{sourceIndex},E.\mathrm{sheet}}(a)=c e_j,
 \qquad c\ne0.
\]

For an arbitrary labelled native operator `U`, assume only the two exact
coherence tests from the preceding section:

\[
 \operatorname{cl}\circ C_i(U)=\operatorname{cl}\circ C_{i_0}(U)
 \quad\text{for every }i,
\]

and

\[
 C_{i_0}(U)(\ker\operatorname{cl})
 \subseteq\ker\operatorname{cl}.
\]

The second law constructs

\[
 T_U:=\texttt{nativeAmbientAction}
   (\operatorname{cl},C_{i_0}(U)),
\]

while the first law proves the whole labelled commuting square

\[
 (\operatorname{cl}\circ N)U=T_U(\operatorname{cl}\circ N).
\]

Evaluate this square on the exact native section of `S.cycle`.  The output is
again the class of a genuine native cycle:

\[
 T_U(a)=\operatorname{cl}
   \bigl(N(U(\operatorname{section}_{i_0}(S.\mathrm{cycle})))\bigr).
\]

The ghost detector kills that class.  The GST matrix-unit identity and the
ghost's nonzero reading on `e_j` therefore give the unconditional formula

\[
 \boxed{
 E.\mathrm{detector}\bigl(T_U(a)-\beta\bigr)
 =-c\,E.\mathrm{detector}(e_j)\ne0.}
\]

Hence `T_U(a) != beta`.  The ambient action is a derived output of finite
relation preservation and column coherence; no ambient action equation,
target cycle, strict packet, or common-class plane is assumed.

This obstruction exhausts both complete coherent constructions proved above.
For every total routing `rho` and every native action preserving the actual
cycle-class kernel, the routed lift misses the detected branch target.  When
the label type is finite, a complete tensor block may contain cancellations
between individually non-descending tensor words, but post-cycle-class
agreement of its column sums and kernel stability still produce an action
with the same nonzero defect.  Thus cancellation and recoordination do not
hide D.

Lean:
`coherentNativeAmbientAction_descends`,
`ghostSeedTarget_coherentNativeAction_mismatch_formula`,
`ghostSeedTarget_coherentNativeAction_mismatch_ne_zero`,
`ghostSeedTarget_routedNativeAction_ne_target`,
`ghostSeedTarget_finiteTensorBlockAction_ne_target`.

## What this contributes toward D

The green point-kernel theorem's pre-existing action equation is now
constructed from native data and finite class-relation coherence. The
labelled universe's hidden ambiguity is generated explicitly, and coherent
collections of operators are classified rather than ruled out by the
single-word obstruction. Routing and recoordination preserve the derived
native action by proved identities.

These are usable construction laws for the native semantic part of a
branch-packet carrier.  The new obstruction proves that this entire native
operator layer, including coherent routing and tensor cancellation, cannot
manufacture the ghost-selected action required by D.  It does not manufacture
a scheme-bi-finite closed carrier from a GST branch.  In particular, a routed
lift is an operator on labelled native cycles; no theorem here identifies it
with an actual strict geometric correspondence.

D still requires construction of the actual carrier and its intrinsic
pullback equality for the detected branch target.  Such a positive
construction must add genuinely strict geometric content which does not
factor solely through an operator on native cycles.  Neither the
finite-relation criterion nor any ambient extension is asserted to prove that
existence.  The new results therefore strengthen the available native
construction machinery, and close a circular escape route, without assuming D
or renaming it as a hypothesis.

## GLM compile entry points

```sh
lake build GSTClassicalHodgeNativePointRelationDescent
lake build GSTClassicalHodgeNativeInteractionNormalForm
lake build GSTClassicalHodgeCoherentNativeDescent
lake build GSTClassicalHodgeCoherentNativeGhostObstruction
```

The generic native-first module imports the confirmed green point-kernel
foundation directly. It does not import the failed
`NativeOperatorCohomologyRealization` module. The interaction and labelled
operator modules additionally use the branch's existing fibered-native
universe. All three modules are registered in `lakefile.toml` and imported by
`HCProof.lean`.
