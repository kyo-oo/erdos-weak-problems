# Projective algebraization of restored folds: construction and exact return

Date: 3 November 2026, Asia/Calcutta. Base checkpoint:
`e699dbec256fc23d4c5615449bf303df45d0076d`.
Branch: `research/gpt6-native-point-primitive-span-20261017`.

The curvature theorem is established. This continuation executes the
projective-realization subconstruction for genuine principal elliptic-torus
folds over arbitrary original smooth projective X. It gives a necessary
and sufficient criterion, the actual projective model, an actual algebraic
multisection cycle, the maximal projective quotient, and its exact canonical
original-X return. It does not assert that these operations have constructed
a cycle for every prescribed higher-primitive alpha.

[Full hand derivation](../derivations/GST_projective_fold_algebraization_2026_11_03.tex)
was written before the Lean changes. Review provenance is author self-review;
there is no independent referee or Lean-kernel claim.

## Completed subconstruction

For a holomorphic principal A-torsor P -> X, with A a fixed projective
complex torus, let theta be its actual analytic gluing class. Then

`P is projective iff theta is torsion`.

The necessity proof uses an actual ample line on P. Its restrictions to
fibers define a polarization isogeny lambda:A -> A-dual. Local Picard
families show lambda kills theta. An inverse isogeny up to [N] supplies
N theta = 0. Thus no assumption that every pure Hodge manifold is
projective is used.

The sufficiency direction is a construction. A finite A[N]-cocycle gives
an actual finite unramified cover X' -> X, and

`P = (X' x A) / A[N]`.

Pullback of a positive line embeds X' projectively; projective GAGA and the
finite free quotient algebraize the original torsor, its projection and
action. The cover may be disconnected. All multiplicities are retained.
This proves the result for arbitrary original X, with no HC premise.

For A=E^r, the map s:X' -> P induced by the zero point constructs the
actual Chow multisection

`Sigma = s_*[X'] / N^(2r) in CH^r(P)_Q`.

Its original-X pushforward is exactly [X]. The resulting return is

`R(B)=pi_*(Sigma * B)`, with `R pi^*=identity` in actual Chow.

The canonical Betti map commutes with the construction. Thus an actual
cycle B representing pi^*alpha returns the exact prescribed alpha on the
same original X. This is a genuine cycle-return construction; it does not
assume that an unconstructed B has appeared.

The finite-cover presentation also gives the full rational Hodge cup
algebra H*(P,Q) isomorphic to H*(X,Q) tensor H*(A,Q). Translations act
trivially on the second factor, and finite invariants on the first give
H*(X,Q). This uses all cohomological degrees; the splitting depends on
the cover presentation and is not claimed choice-independent or a formula
for the entire Chow ring.

## Sharp projective dimension law

For the actual lines L_i of the base-coupled fold, let

- R0 be the exact integral relations among theta(L_i);
- Ralg be the integral combinations whose theta-class is torsion;
- RC be the rational-curvature-zero integral combinations.

Then `Ralg = saturation(R0)` and `R0 <= Ralg <= RC`.
A primitive basis of Ralg constructs a connected-fiber quotient with the
largest possible projective dimension

`dim X + rank Ralg`.

Every projective integer-matrix quotient factors uniquely through it.
The extra dimension collapse beyond Hodge restoration is exactly
`rank RC - rank Ralg`. This is an optimum in the stated integer-matrix
principal-E quotient category, rather than across every GST realization.
The statement supplies an exact mathematical criterion and witnesses; it
does not claim an algorithm deciding analytic torsion from curvature data.

The already constructed non-torsion theta(L), with L in Pic0(X) and
h^(1,0)(X)>0, now has a decisive geometric interpretation: its fold is
Kahler and has the whole canonical Hodge structure, yet is nonprojective.
Its maximal projective quotient collapses the handle and returns to X.
The original independent central-fold experiment is on the positive
branch: curvature zero gives X times a projective elliptic power with
zero theta. That experiment's proof remains intact.

## Original-target audit

The three executed routes are the explicit finite-cover algebraization,
its ample-line necessity test, and the prescribed-alpha return through the
constructed multisection. The exact normalized claim for the subconstruction
is Theorems 1 and 2 of the derivation, and the maximal quotient theorem
there. Primary verdict: **proved as written**, at self-reviewed hand-proof
level with the displayed standard analytic inputs.

| Obligation | Result |
| --- | --- |
| Actual projective model for every torsion torsor | Passed: explicit finite cover and quotient |
| Projectivity forces torsion | Passed: fiber polarization and local Picard transition calculation |
| Algebraic multisection on that model | Passed, including disconnected-cover multiplicities |
| Actual Chow return, degree and canonical comparison | Passed by proper pushforward and projection formula |
| Sharp largest projective integer-matrix quotient | Passed by the saturated lattice and integral basis factorization |
| Curvature zero alone forces projectivity | Refuted by the existing non-torsion Pic0 construction and the proved criterion |
| Higher rational homotopy torsor is a principal elliptic torsor | Not asserted; the categories and degrees differ |
| Every prescribed higher-primitive alpha has a constructed cycle B | Incomplete; the present construction supplies Sigma, not that B |

The original universal target has primary verdict **incomplete**. Its exact
remaining implication is independent construction of B with canonical
class pi^*alpha, or of a different actual original-X source with class
alpha. The proved two-way image relation is

`alpha algebraic on X iff pi^*alpha algebraic on P`.

Consequently using provisional HC to supply B would retain that premise.
This identifies its exact location instead of dismissing the established
curvature result. The projective-torsor algebraization route is completed
at its stated scope; higher source realization remains open, with resumption
requiring an actual new source construction rather than another curvature
cancellation. No global novelty or impossibility claim is made.

## Lean changes and reproducible evidence

Two existing modules are edited. `GSTCausalFoldDefect.lean` gains **10 theorem
drafts** supporting saturated torsion relations, annihilator transport,
curvature-kernel necessity, isogeny necessity, common cover orders and unique
relation factorization. `GSTSpatialFoldResearch.lean` checks their integration.
The manifold, Picard, finite-cover and Chow comparison arguments remain in
the hand derivation; the group lemmas do not pretend to formalize them.
Compilation remains with the owner; no Lean execution or CI dispatch occurs.

```sh
python research/experiments/gst_projective_fold_run.py
python /workspace/scratch/5d57a06b0962/gst_validate_manifest.py research/computations/gst_projective_fold_20261103.manifest.json --root .
```

Observed exact arithmetic: **42,745 Python assertions**, **40,658 Wolfram
assertions**, with all shared tables matching. These are implementation
checks, not a count of mathematical theorems.

- Every one of 324 declared homomorphisms Z^2 -> Z + Z/6 is tested on all
  25 vectors in [-2,2]^2, with saturation multipliers 2,3,4. Python computes
  finite orders by gcd; Wolfram independently enumerates all annihilators
  from 1 through 6. The nine aggregate rows agree.
- The index-six exact-relation lattice and its saturation are checked on
  all 343 vectors in [-3,3]^3; 49 lie in the saturation and nine in the
  exact lattice. Explicit coordinate reconstructions are checked.
- A non-scalar polarization matrix [[2,1],[1,2]] has adjugate composite
  3I; its kernels modulo every d=2..12 are killed by 3. All eleven kernel
  counts agree.
- Thirty cover-degree/normalization rows cover N=1..6 and r=0..4, including
  the empty-handle case. This is an arithmetic check of the normalization,
  not an experimental test of the geometric multisection theorem.

The Wolfram source passed on its first execution. Kernel: 15.0.1 for Linux
x86 (64-bit), July 2, 2026. Kernel runtime and process exit status are not
exposed and are recorded null. The context lookup supplied no theorem used
here. The exact remote input, full raw response and parsed output are pinned.
The Python process exits zero. Arithmetic is exact; runtime metadata alone
may use floating-point values.

Current-source proof-escape scans, the 748-node parsed import graph, LaTeX
environment balance and whitespace checks pass. Three prior lexical
anomalies are unchanged. This is not a semantic review of 748 Lean modules,
a Lean build or a typeset-PDF verification. Old manifests remain historical.

[Current evidence manifest](../computations/gst_projective_fold_20261103.manifest.json),
[exact output](../computations/gst_projective_fold_20261103.output.json),
[raw remote evidence](../computations/gst_projective_fold_wolfram_20261103.output.json).
