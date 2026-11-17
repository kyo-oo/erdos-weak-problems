# GST extension: base-coupled quotients and higher target transgression

Date: 3 November 2026, Asia/Calcutta. Starting checkpoint:
`b2de3bdecf4467211702f5d5118577a014170333`.
Branch: `research/gpt6-native-point-primitive-span-20261017`.

The owner requested an extension of the folding idea beyond the preceding
central-fold construction. This checkpoint changes the geometry: handles
twist **over the original arbitrary X**; quotients change their number;
higher-degree handles take the prescribed Hodge class itself as curvature;
and cup-coefficient substitutions link different cohomological degrees.

The [hand derivation](../derivations/GST_base_coupled_and_higher_transgression_folds_2026_11_03.tex)
was written before the Lean additions. Four existing modules are edited;
**16 theorem drafts** are added directly, with no new wrapper module.
Compilation remains with the owner. The hand analytic/topological
comparisons are not presented as Lean instances.

## General theorems obtained

Statements work componentwise for every smooth projective original X;
no CM, curve, favorable Hodge-group or dimension bound is imposed.

1. **Folds coupled to X.** For genuine line bundles L_a, the space
   P(L)=product_X(L_a^times/q^Z), q=exp(-2pi), is an actual compact complex
   principal elliptic-torus bundle. Its curvature is C:Q^r -> H²(X,Q),
   e_a -> c1(L_a). Its actual first-Hodge opposedness defect is rank C.
   The whole canonical Hodge structure is pure exactly when C=0; an
   explicit closed positive form proves sufficiency by making P Kähler.
2. **The entire cohomology uses the original cup algebra.** The real DGA
   H*(X,R) tensor exterior(u_a,v_a), du_a=c_a, dv_a=0 computes all cup
   cohomology. The proof uses fiber averaging and relative dd^c formality.
   For one handle the complete formula is
   `b_k(P)=b_k+2b_(k-1)+b_(k-2)-r_(k-1)-2r_(k-2)-r_(k-3)`, where r_j
   is the rank of c cup - and out-of-range terms vanish. Equal curvature
   rank can give different higher spectra over the same original X.
3. **An optimal restoring quotient.** Integer-matrix tensor-line maps are
   actual holomorphic torus quotients. Exactly rho=rank C emergent complex
   dimensions must collapse to restore purity in this category; the
   maximal endpoint has dimension dim X+r-rho. Construct it from the
   saturated kernel of Z^r -> H²(X,Z)/torsion. Every other zero-curvature
   integer-matrix quotient factors through it.
4. **Holomorphic memory beyond curvature.** The analytic sheaf sequence
   `0 -> Z -> O_X^* -> E_X -> 0`, n -> q^n, computes the kernel of the
   line-to-elliptic-torsor functor. Principal triviality is measured by
   theta(L) in H¹(X,E_X), not c1 alone. Its relation subgroup R_theta
   may be smaller than the curvature kernel and need not be saturated.
   For every X with h^(1,0)>0, a countability proof supplies L in Pic⁰
   such that P(L) has full Hodge purity but no nonzero integer fiber
   quotient is a trivial principal bundle over X. This asserts no
   nonalgebraic rational Hodge class; it retains the actual gluing data.
5. **The prescribed target as curvature in every codimension.** For alpha
   in Hdg^p(X)_Q, construct the actual homotopy fiber of X -> K(Q,2p),
   with a flat K(Q,2p-1) companion. The model has |u|=|v|=2p-1,
   du=alpha, dv=0. Its explicitly defined conjugate filtration has first
   affected degree **2p-1**, with missing quotient exactly the span of
   the input curvatures. These are actual rational topological spaces
   with a specified model filtration, not asserted compact manifolds.
6. **Cup-coefficient folds between different degrees.** For p_j>=p_i and
   a rational Hodge class a of degree 2(p_j-p_i), the change
   `u_j'=u_j-a u_i`, `v_j'=v_j-a v_i` sends curvature alpha_j to
   alpha_j-a alpha_i. It is an invertible filtered DGA transformation,
   retaining conjugation and every degree. Its coefficient comes from
   the original cup algebra. If alpha_j=a alpha_i, an entire higher
   handle pair becomes closed. Actual homotopy-fiber paths implement
   the substitution by cup products; no nilpotence of pi_1(X) is assumed.

For arbitrary finite mixed codimensions, the least nonzero curvature
determines the first affected degree. Whole model purity holds exactly
when every curvature vanishes. The all-degree higher spectrum is derived
by the full kernel/cokernel sequence, including the flat companion shift.
These are quantified derivations, not extrapolations of finite tables.

## What extends the previous construction

| Previous restriction | Extension |
| --- | --- |
| Independent auxiliary factor beside X | Genuine holomorphic torus bundles twisted over X |
| Auxiliary curvature exterior algebra | Multiplication in the full original-X cup algebra |
| Fixed-count pair fusion | Non-square quotients and a maximal restoring endpoint |
| Curvature as the sole restoration readout | Distinct holomorphic torsor relation subgroup |
| Degree-two curvature | Prescribed alpha transgressed in every degree 2p |
| Scalar changes of equal-degree handles | Cup-coefficient substitutions between different degrees |

This extends the branch's mathematics. Principal bundles, formality,
transgression and triangular substitutions are standard mechanisms.
Worldwide historical novelty has not been established by a literature
comparison; no internet search was performed in this run.

## Actual original-X source attempt

The input is the actual arbitrary triple (X,p,alpha), and alpha chooses
the higher torsor's classifying map. Its exact topological coupling is
computed: alpha transgresses from u and pulls back to zero on that torsor.
Opposite fusion returns the zero classifying map; the history retains
the original transgression. This is target-sensitive rational topology.

For p=1 the integral (1,1) theorem constructs a genuine L_alpha with
c1(L_alpha)=m alpha. The actual algebraic cycle c1^CH(L_alpha)/m has
canonical Betti class alpha on the original X. For higher p, the torsor
does not supply an algebraic cycle. A cycle-bearing algebraic realization
of the higher transgression and its canonical comparison has not been
constructed here or inserted as an assumed source theorem. The universal
cycle conclusion remains the same target; no counterexample is asserted.

## Proof audit

Primary verdict: **proved as written for the specified extended operations**,
by author self-review. The analytic/topological comparisons use displayed
arguments and standard dd^c/Hodge/classification facts at their stated
strengths. There is no independent reviewer or Lean-kernel receipt.

| Obligation | Self-review result |
| --- | --- |
| Compactness and integrable type of P(L) | Passed: holomorphic quotient and line charts |
| Actual first Hodge filtration | Passed: fiber averaging, closed vertical coefficients, base Kähler decomposition |
| Sufficiency at zero real curvature, including torsion | Passed: unitary flat metrics and explicit Kähler form |
| All cup cohomology | Passed: relative dd^c comparison after finite Hirsch extension |
| Saturated kernel gives connected quotient | Passed: torsion-free Chern target and unimodular basis completion |
| Zero curvature means principal product | Rejected and corrected: theta must be retained |
| Clearing a rational basis gives primitive integral relations | Rejected: (2,3,5) gives an index-two hostile control |
| Higher torsor is compact complex | Not asserted; actual object is a rational homotopy fiber |
| Mixed-degree signs and types | Passed: even cup coefficient, odd generators, explicit inverse and path substitution |
| Noncommutative packet coefficients | Passed with stated curvature/shear commutations; hostile controls fail when removed |
| Arbitrary higher canonical Chow source | Not constructed; topological transgression is not relabeled as Chow |

Self-review corrected a preliminary necessity claim that the tensor line
itself must be trivial: principal torsor triviality only requires membership
in the q-power image of H¹(X,Z). A six-entry surface diagnostic was corrected
to its full seven-degree spectrum before evidence publication. Neither
false preliminary statement is a result.

## Lean edits and exact evidence

| Existing file | Added theorem drafts | Content |
| --- | ---: | --- |
| GSTCausalFoldDefect.lean | 5 | Restoring lift, unique factorization, injectivity and relation inclusion |
| GSTGradedWorldAlgebra.lean | 6 | Coupled boundaries, two-odd-generator sign, inverse cup shear and flat-handle exposure over possibly noncommutative rings |
| waves/GSTNCohomologyV3.lean | 5 | Base-valued curvature, prescribed-input detection, fusion and zero criterion |
| GSTSpatialFoldResearch.lean | 0 | Existing integration checks extended |

Reproduction:

```sh
python research/experiments/gst_base_coupled_higher_fold_run.py
python /workspace/scratch/5d57a06b0962/gst_validate_manifest.py research/computations/gst_base_coupled_higher_fold_20261103.manifest.json --root .
```

Observed: **35,044 exact checks**, **94 full spectra**, **12 mixed-degree
cup-shear chain identities on every basis state**, and all **729** small
2x3 curvature matrices. Their rank histogram is (1,104,624). The (2,3,5)
control distinguishes an index-two cleared nullspace from the primitive
integer relation lattice. Matrix-ring packet checks include two deliberate
failures when the required commutations are removed.

Bounds: seven declared products of projective spaces; p=1..min(dim X,3);
all cochain degrees; zero/monomial/sum/dependent/independent curvatures;
twelve declared mixed pairs (1,2),(1,3),(2,3); all 2x3 matrices with entries
-1,0,1 and their stated relation cubes; and all integer (2,3,5)-relations
in [-3,3]^3. Two unit controls include a zero-curvature point base. Tables
are fixtures, not 94 claimed distinct complex geometries.

Bit-mask and signed-word boundaries agree. Sparse rational column
elimination agrees with independently written dense rational row reduction.
One-handle spectra agree with the cup-rank formula. Mixed substitutions
are checked as full chain maps, not merely equal Betti numbers. No random
sampling, floats, external engine, Lean execution or CI dispatch is used.
An optional SymPy probe found it unavailable; actual checks use only the
Python standard library.

The parsed 748-node import graph is acyclic; three preexisting lexical
anomalies are byte-identical to the base. Changed-source escape scans,
LaTeX environment balance, whitespace and the current-hash Mathbox v2
manifest check pass. These are static checks, not a repository-wide
semantic audit or a LaTeX typesetting claim.

[Evidence manifest](../computations/gst_base_coupled_higher_fold_20261103.manifest.json)
and [exact output](../computations/gst_base_coupled_higher_fold_20261103.output.json).

## Continuation handoff

The new operation is the mixed-degree cup-coefficient fold, with actual
path-space realization and full graded comparison. Holomorphic memory is
measured by the separate theta relation subgroup. Further work must retain
both invariants and the original prescribed alpha. The higher algebraic
realization route stays open at its stated source construction; model
purity alone is not used to infer algebraicity.
