# GST continuation: integral projection correction and singular-branch extraction

Base checkpoint: `02bba4d8a783af62cadc5de85af19070086d8408`.
Branch: `research/gpt6-native-point-primitive-span-20261017`.
Date: 2026-10-28, Asia/Calcutta. Review provenance: implementing assistant's
adversarial **self-review**, with independent Python/Wolfram computations.

This update adds **six Lean modules and 47 theorem declarations** across the
new modules and the strengthened localization module. All are uncompiled proof
drafts, as requested. The strongest constructive addition extracts an actual
singular-stratum Chow cycle from three spectral line-bundle twists, with the
unknown starting eigenline class cancelling exactly. The universal prescribed
Hodge-cycle constructor is not established.

## Exact mathematics and changed restrictions

The fixed input is arbitrary original smooth projective complex `(X,p,alpha)`;
the required output is a rational algebraic cycle on that same X with
**canonical** Betti class alpha. The executed routes use the genuine affine
Jouanolou bundle J over X. No Stage2G cycle map is silently called canonical.

| Addition | Earlier restriction | Result and scope |
| --- | --- | --- |
| Integral exactification | First-order tangent equation, or an assumed exact projector | In every associative ring, `T(a)=a-(2a-1)(a²-a)` has defect `e(T(a))=e(a)²(4e(a)-3)`. If `e(a)^(2^k)=0`, k rounds give an exact idempotent. No inverse of two, no commutative ambient ring |
| All-order image-module comparison | Infinitesimal conjugacy only | Any two idempotents with nilpotent difference are conjugate by an explicit unit; their image modules are isomorphic |
| Smooth-branch calculation | Repeated anti-eigenline powers known zero only on the etale open | For a reduced scalar discriminant, the actual kernel eigenlines have neutral sum and determinant rationally even across its smooth ramification. All repeated powers of their difference vanish there |
| Singular support | The entire discriminant was the possible support | With extensions agreeing with the actual kernels on the smooth-branch region, the returned Chow class is supported over `Sing(D)`. In codimension two it is zero if `codim Sing(D) >= 3` |
| Three-twist source extraction | Unknown horizontal eigenline contribution mixed with exceptional contributions | For a genuine exchanged exceptional pair with `pi_*(D²)=c[S]`, `(Z(1)+Z(-1)-2Z(0))/(8c)` equals the actual original-X return of `[S]` in Chow |
| Connected mixed-source test | Abstract independence and deck neutrality alone allowed a surviving mixed term | On a connected finite etale double cover already descended to projective X, a line complementary to its conjugate has zero canonical rational first Chern class by primitive positivity. Such mixed products have zero Betti class |

[Complete hand derivation](../derivations/GST_integral_projection_and_singular_branch_source_2026_10_28.tex)
was written before the corresponding Lean modules.

For the constructive extraction, let `D=E_i-E_j` for two exceptional divisors
exchanged by the deck involution. In a transverse A_n chain,

`pi_*(D²) = (-4 - 2*epsilon)[S]`,

where epsilon is one for adjacent components and zero otherwise. Let
`a=c1(L_plus)-c1(L_minus)` and construct **actual Chow cycles**

`Z(k) = (q*)^-1 pi_*((a+2kD)^2)`.

The finite difference is `8*pi_*(D²)`. For an exchanged A2 pair, the exact
normalizing coefficient is **-1/48**; for a nonadjacent pair it is **-1/32**.
This requires actual globally defined exchanged exceptional components and
their stated intersection equations. It does not supply them from Hodge type.
No closed-immersion GRR formula is required for this direct Chow construction.

## Executed arbitrary-X source attempts

1. **Nilpotent correction of the alpha-dependent polynomial source equation.**
   Finite correction succeeds when the literal algebraic defect is nilpotent.
   The explicit conjugacy theorem proves that nilpotent changes around an
   existing algebraic projector preserve its K0 class at every finite order.
   A small analytic error on a compact core is not thereby nilpotent. The
   all-order result closes this proposed change-of-class mechanism, while
   retaining the correction algorithm for its valid uses.

2. **Ramification return of the alpha-selected polynomial spectral object.**
   The October 24 near-projector construction and its local target class are
   retained. Its repeated nonlinear anti-source was previously localized to
   the discriminant. The new computation includes smooth branching: there
   the nilpotent rank-one kernel K satisfies `K tensor K = O`; its rational
   K0 class is one, and its pushforward from the principal ramification
   divisor is zero. Therefore only singular branching remains in this
   repeated-source route. A transverse cone pullback has singular locus of
   codimension three and gives zero codimension-two return.

   We then constructed the three-twist exceptional extraction above.
   The explicit candidate `b=[[f,g],[g²,-f]]` has discriminant `f²+g³` and an
   A2 locus `V(f,g)` when the two differentials are independent. Its actual
   stratum is a regular zero locus of the **trivial** rank-two bundle, so
   `[V(f,g)] = c2(O²) = 0` in Chow. Thus this particular global-functions
   recipe also returns zero; the extraction formula itself remains valid.
   Nontrivial singular support or a proved nontrivial component separation
   must be constructed independently for a nonzero prescribed residual.

3. **Independent mixed lines on a connected whole finite cover.**
   If the cover is the base change of a connected finite etale double cover
   X' of projective X, its anti first Chern class l has `l²=0` and zero degree
   against the invariant ample polarization. Divisor Hodge--Riemann positivity
   gives `l=0` in canonical rational Betti cohomology. This is not a Chow or
   Picard-triviality claim. A split cover has two component degrees, so the
   scalar primitive-positivity argument does not apply. The earlier nonzero
   `(P1)^r` mixed-source example is preserved.

These are scoped construction/obstruction results, not a counterexample to
Hodge or a statement that every GST source mechanism fails.

## Lean files and formalization boundary

| File | Added theorem declarations | Encoded content |
| --- | ---: | --- |
| `GSTIntegralProjectionCorrection.lean` | 11 | Defect doubling, finite stopping, complement compatibility |
| `GSTNilpotentProjectionConjugacy.lean` | 5 | Explicit intertwiner, two-sided inverse and conjugation |
| `GSTSpectralBoundaryDefect.lean` | 9 | Exact two-defect formula, ideal containment, repeated powers and surviving abstract mixed term |
| `GSTTorsionLineConservation.lean` | 6 | Integral two-power annihilator, rational rigidity, principal pushforward consequence |
| `GSTConnectedSpectralHodgeRigidity.lean` | 4 | Anti-degree cancellation and the primitive positivity implication |
| `GSTSingularBranchExtraction.lean` | 9 | Three-twist extraction, arbitrary center/step formula, A_n pair coefficients and normalization |
| `GSTFilteredK0SourceConservation.lean` | 3 | Exact localization support and vanishing consequences |

The entry point and explicit Lake library roots are updated. Later owner
verification remains `lake build GSTOpenAISourceUpgrade`.
No Lean installation, compilation, CI dispatch or kernel axiom receipt is
claimed. `#print axioms` lines are future verification commands.

The smooth schemes, line-kernel exact sequence, resolution, Chow localization,
actual exceptional intersection geometry, affine-bundle Chow equivalence and
Hodge--Riemann theorem are **hand-level geometry**, not implemented scheme
instances in these Lean files. The Lean positivity statement takes its precise
positive-definiteness input openly. It is not a replacement Hodge axiom.

## Exact computation evidence

The [Wolfram program](../experiments/gst_projection_branch_wolfram_20261028.wl)
passed **61 assertions**; its raw result and normalized rows are
[preserved together](../computations/gst_projection_branch_wolfram_20261028.output.json).
Kernel: `15.0.1 for Linux x86 (64-bit) (July 2, 2026)`.
Observed kernel runtime: 2.855375 seconds. Remote process exit status is not
exposed and is recorded as null. Mathematical arithmetic was exact; only
runtime measurements use machine reals.

The [independent standard-library Python implementation](../experiments/gst_projection_branch_checks.py)
passed **109,088 checks**, including structural checks. This count is not a
count of independent theorems or new geometric sources.

| Ring | All matrices | Nilpotent-defect matrices | All idempotent pairs | Nilpotent-difference pairs |
| --- | ---: | ---: | ---: | ---: |
| Z/2 | 16 | 14 | 64 | 20 |
| Z/3 | 81 | 30 | 196 | 62 |
| Z/4 | 256 | 224 | 676 | 290 |
| Z/5 | 625 | 80 | 1,024 | 272 |
| Z/8 | 4,096 | 3,584 | 9,604 | 4,610 |
| Z/9 | 6,561 | 2,430 | 12,100 | 4,862 |
| Total | **11,635** | **6,362** | **23,664** | **10,116** |

Every eligible matrix is corrected at the logarithmic round bound. Every
eligible ordered pair has its explicit inverse and conjugacy checked. The
nilpotence enumerator's bound is justified by reduction of Mat2(Z/p^e) modulo
p, not by an unexplained finite cutoff. All six complete row summaries and
nilpotence histograms agree between Wolfram and Python.

Additional checks include exact free associative polynomial identities;
the smooth-ramification cokernel normal form; all 78 reflected exceptional
pairs in A1 through A12; rational normalization; integral torsion controls;
an abstract mixed-product counterexample to overextending repeated-square
vanishing; and a disconnected-cover counterexample to unqualified positivity.
The local import graph is acyclic across 723 parsed modules. Two pre-existing
unclosed-header comparator files remain explicitly recorded and untouched.

Reproduction and evidence validation:

```sh
python research/experiments/gst_projection_branch_run.py
```

[V2 manifest](../computations/gst_projection_branch_20261028.manifest.json),
[independent output](../computations/gst_projection_branch_20261028.independent.output.json).
The actual Mathbox validator passed with root/hash verification; local
verifier process exit status is 0. The manifest pins execution inputs before
and after the run and compares the raw Wolfram result to independent rows.

The first Wolfram run failed an ordered-list comparison of a Groebner basis:
the kernel returned `{z,y,x}`, while the test expected `{x,y,z}`. A minimal
probe confirmed the ideal was correct. The test now reduces each coordinate
by the actual basis; the complete final suite was rerun. The failed raw result
is retained and is not counted as mathematical evidence. The local free-ring
audit also exposed a missing idempotence hypothesis in an early bridge-formula
draft; the hypothesis and a hostile control were added before publication.

## Source checks and overlap

The previously pinned OpenAI research remains method inspiration: approximate
construction and exact correction are distinct; no immersion/projection theorem
is promoted to algebraic source existence. No new OpenAI theorem or axiom was
imported in this continuation.

- [Stacks 00J9](https://stacks.math.columbia.edu/tag/00J9), checked 2026-10-28:
  its second proof uses the same cubic correction in a commutative ring.
  **Known after translation** for that case. Our associative-ring identity is
  proved directly; uniqueness of commutative lifts is not asserted for matrices.
- [Stacks 02RX](https://stacks.math.columbia.edu/tag/02RX), checked 2026-10-28:
  the exact Chow localization sequence supplies the stated singular-support
  implication, with cycle dimension `dim J-p`.
- [Stacks 02RG](https://stacks.math.columbia.edu/tag/02RG) and
  [02RH](https://stacks.math.columbia.edu/tag/02RH), checked 2026-10-28:
  actual proper/flat base change and finite-degree push-pull have the stated
  coefficient and variance conventions.
- [Stacks 42.32, Remark 42.32.3](https://stacks.math.columbia.edu/tag/02TS):
  records affine-bundle Chow invariance, including the general torsor case.
- Christian Schnell, [Class 18, Fall 2024, Theorem 18.15, p. 6](https://www.math.stonybrook.edu/~cschnell/mat545/class18.pdf),
  exact statement/proof checked 2026-10-28. Specializing degree two and type
  (1,1) gives the negative intersection form on the primitive subspace used
  above. The coefficient is rational for an integral ample polarization.

These are primary source checks for exact implications, not a comprehensive
novelty search. No global priority claim is made for idempotent lifting,
conjugacy, finite differences or Hodge index. The new branch contribution is
their precise integration with smooth ramification and singular-stratum return.

## Adversarial proof self-review and continuation

| Obligation | Audit outcome |
| --- | --- |
| Arbitrary associative ring correction | Direct one-element polynomial proof; no hidden commutativity or division |
| Finite stopping and unit inverse | Explicit exponents; zero/exponent-one cases included |
| Smooth-branch K0 relation | Requires reduced discriminant, smooth-branch open, actual kernel eigenlines; rationalization of the two-torsion line is explicit |
| Singular-support refinement | Extensions must agree on the entire smooth-branch open; localization is in actual Chow |
| Three-twist normalization | Exact Chow identity after the actual exceptional intersection equations; 8c is nonzero |
| Connected-cover rigidity | Connected projective cover, invariant ample class; only canonical Betti vanishing concluded |
| Full original-X target | Still open; no source coverage premise is called an independent existence proof |

Continuation checkpoint: the source-bearing branch must supply nontrivial
singular support or a different genuinely target-sensitive geometry, with its
canonical period computed from alpha. Repeated nilpotent frame changes,
smooth branching, the global-functions A2 complete intersection, and connected
whole-cover complementary mixed lines have the obstructions above and should
not be repeated unchanged. Branched mixed constructions, non-complete-intersection
singular supports and selected components remain open; their alpha-matching
existence is not renamed as an easy new lemma.
