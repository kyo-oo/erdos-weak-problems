# Mathbox execution: full cochain comparison, selected-block descent and excess

Date: 3 November 2026, Asia/Calcutta. Base checkpoint:
`feb0a99d1e08c4998a01f7239e5bb9e668851354`.
Branch: `research/gpt6-native-point-primitive-span-20261017`.
Owner request: turn the whole-space plan into mathematics, finish its proof,
and leave the Lean side to the owner.

**Result:** completed mathematical subproofs and three executed geometric
route tests. The universal original-X cycle-existence implication is still
unproved. The evidence does not support “mathematics done; only Lean remains.”
There are no Lean changes, builds or CI dispatches in this update.
Primary proof-audit verdict for the original target: **incomplete**, at the
independent algebraic source-existence implication detailed below.

The [complete derivation](../derivations/GST_selected_block_excess_and_integrability_2026_11_03.tex)
contains the actual constructions and proofs. The
[whole-space plan](../GST_WHOLE_SPACE_PROOF_PLAN.md) remains the owner of the
same universal target, with this execution linked at its unresolved step.
No provisional Hodge assumption has been used to assert an unconditional
cycle. No special case has replaced the arbitrary `(X,p,alpha)` target.

## What is now mathematics rather than a plan instruction

### Full filtered cochain realization on every actual projective world

For any smooth projective realized Y, take an actual finite good cover,
retain all its nerve faces, and form

`C^(a,b) = product of smooth b-forms on (a+1)-fold intersections`,
`D = Cech differential + (-1)^a exterior differential`.

The proof expands `D²=0`, gives the partition-of-unity contraction of the
augmented Cech rows, and proves a filtered quasi-isomorphism from global
de Rham forms. The rational constant nerve supplies the rational Betti
structure. The form-type filtration gives the full Hodge filtration on
cohomology. No coordinate amplitudes are discarded.

The actual cochain charge lift is `i Q_harmonic Pi_harmonic`; it commutes
with the differential because harmonic forms are closed and exact forms
have zero harmonic projection. Multiplication by `u-v` on all smooth
`(u,v)` forms would not itself commute with d. The derivation retains this
distinction, the state-specific endpoint defect, every prefix test and
the geometric homotopy operator for two actual homotopic maps.

This proves the comparison for the explicitly constructed nerve model.
It does not identify an arbitrary GST graph with that model merely because
their hole counts agree. Cochain spaces can be infinite dimensional; their
Betti cohomology is finite dimensional. An actual basis comparison is still
needed before a chosen N-coordinate index is used to name that fiber.

### One topological bundle can retain the whole prescribed class

Rational topological K-theory, denominator clearing and a finite-rank
complement construct one actual topological bundle F and complement G with

`ch(F)=r+mu q*alpha`, `ch(G)=m-mu q*alpha`, `F+G=trivial`, `mu>0`.

All other positive Chern-character degrees vanish. The established Stein
and polynomial-approximation construction therefore needs one selected
cluster problem rather than two unrelated projector clusters. This is a
topological/analytic construction, also available for non-Hodge even
classes. It is not called an algebraic bundle.

### A matched global factor now gives a complete actual cycle construction

If the characteristic polynomial of the actual approximating matrix has
a monic function-field factor g matching that analytic cluster, the proof
constructs the sheaf itself:

`M_g = kernel(g(a): O_J^N -> O_J^N)`.

Normality proves that the monic factors have regular coefficients. Away
from their resultant, the explicit Bezout projector proves that this kernel
is the selected bundle. Smoothness of J gives a finite projective resolution
of the coherent kernel on all of J, including the resultant boundary.

Its Chow Chern character returns the actual original-X cycle

`Z_alpha = (1/mu) (q*)^(-1) ch_p^CH(M_g)`.

Canonical comparison on the detecting compact core and injectivity there
prove `cl_X^can(Z_alpha)=alpha`. This removes an unnecessary assumption
that the chosen factor has disjoint roots globally: boundary away from the
core is retained in the perfect complex. It does not construct the matched
factor from Hodge type. Its hypothesis is visible, not renamed an existence
law or passed to a final theorem without proof.

## Three geometric routes executed at their uncertain steps

### 1. Selected components: exact individual returns and monodromy

For ranks r,m, selector rank s and k roots chosen from the first block, the
returned positive-degree character has the explicit integral coefficient

`c_k = C(r-1,k-1) C(m,s-k) - C(r,k) C(m-1,s-k-1)`.

The proof computes the normal derivative and the excess bundle on
`Gr(k,F) x Gr(s-k,G)`. Its correct localized contribution is the top Euler
class of that product's relative tangent bundle, rather than the ordinary
fundamental cycle of a positive-dimensional excess component. A diagonal
endomorphism and the splitting principle prove the all-rank Euler-transfer
formula. For `s=r`, the distinguished coefficient is exactly 1, while
the sum over all feasible k is zero.

For the actual generic regular incidence of the alpha-dependent matrix,
the analytic contour splits it into local pieces Z_k. Cross-block Sylvester
maps are invertible, so the same coefficient formula holds in canonical
Betti cohomology, including internal eigenvalue collisions.

A finite bipartite graph records which global algebraic components meet
which Z_k. Each connected package is an actual union C_A of global
components whose local restriction is the complete union of its indexed
Z_k. Its actual Chow return has canonical class
`mu (sum_{k in A} c_k) q*alpha`.
Any nonzero computed coefficient therefore gives the explicit normalized
cycle on X. This evaluates a specific source, with no hypothetical Gram
column inserted.
This is pushforward of an actual Chow Chern-character cycle, not
`ch(R f_* S)`; no Todd correction from that different operation is omitted.

The first test of existence is decisive: if actual root monodromy is
transitive, all complete-package coefficients are zero. The proof counts
the occurrence of each root label; it does not require full symmetric
monodromy or transitivity on subsets. When within-cluster local monodromy
contains `S_r x S_m`, individual global components are already complete
packages and their degree-2p canonical returns are zero as well.
Finer components cutting a Z_k, nonadditive insertions and other boundary
cycles are outside this conclusion.

The new hostile geometric control has a **nonzero algebraic Hodge input**,
which the October 24 near-constant-projector control did not:

`J0={x²+yz=1} -> P1`,
`P=1/2 [[1+x,y],[z,1-x]]`, `a_eps=P+eps diag(1,-1)`.

The local upper eigenline has the tautological class `-q0*h` on the
detecting Hermitian-projector sphere. For `0<eps<1/2`, the discriminant
`1+4 eps x+4 eps²` has a simple branch divisor outside that sphere and
is not a function-field square. The actual incidence is a connected
smooth double cover, its selected sheet does not descend, and its full
first-character Chow return is zero. At `eps=1/10`, the branch is
`x=-13/5` and the core gap lower bound is `16/25`.

This refutes the proposed arbitrary-X inference “Hodge input plus detecting
contour gap forces selected algebraic descent.” It does not refute Hodge
algebraicity: the target in this control is already a divisor class.
Taking a product preserves the same selection obstruction on the P1
factor over any original X.

### 2. Correlated simultaneous incidence: calculate excess and dimensional fold

For t actual matrices, simultaneous invariant s-subspaces are the zeros
of a section of `T Gr(s,N)^t`. For `t>=2` and `0<s<N`, every complete
virtual tautological return vanishes by degree on the Grassmannian.
An individual excess component is not equated to that complete virtual
class.

For t identical actual projectors and the distinguished F section, the
proof computes its excess contribution exactly as
`c_((t-1)rm)(Hom(F,G)^(t-1))`.
A nonzero pure degree-p encoding forces `r,m>=p`. The unpolarized excess
therefore has codimension greater than p for `p>=2`.

The dimensional fold proposed by the owner was then evaluated rather
than excluded: on `J x P^(rm-p)`, integration of
`c_rm(Hom(F,G) tensor O(1))` gives precisely `c_p(Hom(F,G))`.
Its canonical class is

`(-1)^(p-1) (p-1)! [m(-1)^p-r] mu q*alpha`.

This is nonzero for odd p and for even p with unequal stabilized ranks.
It is a complete polarized Chern-conversion formula **when the bundles
are algebraic**. For a merely analytic selected cluster it is not an
algebraic source. An attempted matrix realization of the O(1) twist must
also retain the auxiliary hyperplane where its scalar section vanishes;
no omitted boundary is treated as harmless. Thus this route computes a
useful return but does not bypass global selection.

### 3. Integrability and deformation: an actual nonlinear obstruction

For every original X, use the actual projective world
`Y=X x E1 x E2` and the trivial rank-two bundle. With independent constant
antiholomorphic one-forms eta1,eta2, take
`theta=U eta1+V eta2`, where U=E12 and V=E21.

It is an integrable first-order deformation. Its second-order equation is

`dbar psi + [U,V] eta1 wedge eta2 = 0`,
`[U,V]=diag(1,-1)`.

The matrix is nonzero and traceless. The wedge class is nonexact, proved
by integrating against a holomorphic volume form on the elliptic surface;
restriction to that surface proves nonexactness on Y. Therefore this
specified first-order direction has no second-order extension, despite
zero topological Chern classes and their Hodge compatibility.

This executes the nonlinear integrability test missing from the purely
cohomological fold equations. It rules out that inference and that
deformation direction; other integrable directions and other geometric
source constructions remain available. It is not a counterexample to
the existence of some holomorphic bundle.

## Focused proof audit

Review provenance: separate adversarial pass by the implementing assistant,
not an independent reviewer. Audited raw proof is the new LaTeX derivation
at base `feb0a99` plus this change; its exact hash is pinned by the manifest.

| Claim / obligation | Verdict | Decisive qualification |
| --- | --- | --- |
| Full filtered nerve--forms realization | Proved as written | Actual good cover and full nerve; not every arbitrary GST graph |
| Pure-degree topological encoding | Proved as written using retained project inputs | Analytic/topological, not algebraic |
| Matched factor to coherent source and canonical original-X cycle | Proved with stated hypothesis | Matched factor must actually exist |
| Individual block and local incidence return | Proved in stated scope | Correct excess Euler factor; positive-degree character |
| Nonzero package to actual target cycle | Proved with stated condition | Finite computed coefficient must be nonzero |
| Root-transitive package cancellation | Proved as written | Does not close finer component/nonadditive routes |
| Nonzero-Hodge-input sheet obstruction | Proved as written | Source target already algebraic; obstructs the proposed method |
| Polarized excess Chern conversion | Proved with stated input | Needs actual algebraic F,G; no implicit global twisted incidence construction |
| Second-order obstruction | Proved as written | One specified first-order direction, not all holomorphic sources |
| Universal canonical Hodge cycle existence | Incomplete | No source-existence implication discharges the selected/nonlinear geometric step |

Dependency chain: actual topological/Stein encoding -> matched factor **or**
nonzero actual component return -> genuine algebraic perfect complex/Chow
class -> affine-bundle original-X return -> canonical Betti equality.
The uncertain source arrow has not been assumed. Hodge-compatible graph
transport and finite native Gram closure do not supply it.

External leaves checked in exact primary pages: Stacks tags
[00OE](https://stacks.math.columbia.edu/tag/00OE) and
[0656](https://stacks.math.columbia.edu/tag/0656) for finite projective
resolution, [037B](https://stacks.math.columbia.edu/tag/037B) for normality,
[02UK](https://stacks.math.columbia.edu/tag/02UK) for splitting, and
[0FA8](https://stacks.math.columbia.edu/tag/0FA8) /
[0FBI](https://stacks.math.columbia.edu/tag/0FBI) for the zero-section and
excess-normal formulas. The proof explicitly supplies their geometric
normal maps. These are rolling Stacks pages checked 3 November 2026; tags
and lemma numbers are recorded, with no local full-text copy retained.
Deligne's [official problem description](https://www.claymath.org/wp-content/uploads/2022/06/hodge.pdf),
Section 1, p.1, was opened for the precise compact-Kahler harmonic-type
identification. The earlier project derivations remain the input for
Jouanolou, topological K-theory and Stein realization. No new OpenAI
attribution or novelty claim is made.

## Exact finite evidence

Command: `python research/experiments/gst_selected_block_run.py`.
Observed: **7,698 Python checks**, **209 Wolfram assertions**, exit 0;
all **96** shared coefficient tables, three branch/gap rows and the
commutator matrix agree after reparsing the raw remote serialization.

Python directly enumerates root subsets for `r,m=1..6`, every selector
rank including 0 and N, and power-sum degrees 1..4. It enumerates all
subgroups of S_n for n=1..4 with counts 1,2,6,30, then forms the actual
orbit/shell package graph for every split and selector. Among the 504
nonvacuous group/split/selector cases, all 154 root-transitive cases have
zero package coefficients. There are 60 nonzero-package cases in the
intransitive controls; these are finite permutation data, not constructed
smooth-projective sources. Sparse quotient-polynomial matrix arithmetic
is implemented independently of Wolfram's PolynomialReduce.

Wolfram checks the coefficient arrays for `r,m=1..4`, the exact symbolic
projector/characteristic/discriminant, three declared rational epsilon
values, the commutator, and Newton's polarized coefficient for
`p=1..6, r,m=1..4`. Kernel version: `15.0.1 for Linux x86 (64-bit)
(July 2, 2026)`. Remote process exit status and kernel runtime are not
exposed and are recorded as null. Arithmetic is exact; no random sampling
or numerical tolerance is used.

The LaTeX environments balance, whitespace checks pass, and the Mathbox v2
validator verifies current input/output hashes. These tests support the
stated finite identities; the geometric theorems have the hand proofs
above, not a finite-computation proof certificate.

[Manifest](../computations/gst_selected_block_20261103.manifest.json),
[independent output](../computations/gst_selected_block_20261103.independent.output.json),
[raw remote evidence](../computations/gst_selected_block_wolfram_20261103.output.json).

## Continuation handoff

The original target remains open. The generic complete-incidence and
root-transitive complete-package recipes are closed in precisely the
scopes proved here. Matched-factor descent and component normalization
are now complete subroutines; repeating them does not prove their input
exists. The unpolarized identical-matrix recipe has the computed degree
obstruction, while polarized conversion retains the selection requirement.
The specific first-order direction above is obstructed, not every
integrable-source route.

Still open, with their resumption conditions: construct a finer actual
component/nonadditive or correlated source whose **full** returned class
has the required alpha coupling, with all discriminant and auxiliary
boundary contributions; or construct an integrable source direction and
solve its nonlinear extension and algebraic-descent equations from the
prescribed input. This update does not leave either route terminally
inconclusive or claim all future mechanisms are impossible. No executable
unconditional construction satisfying those conditions has been established
at this checkpoint.
