# GST Mathbox — cubic minimality of the parity-filtered Weil sixfold projector

- **Date:** 2026-10-20 (IST)
- **Kind:** exact spectral lower bound and geometric-source architecture refinement
- **Program:** full rational Hodge conjecture on arbitrary smooth projective complex original `X`; this is a bounded CM-sixfold subproblem, not the final theorem
- **Base checkpoint:** `b06812cf73bea53adb4720e0a53d3e1811ae914d`
- **Mathematical source:** `GSTUniversalCMArithmeticObstruction.lean`
- **Lean commits:** `66adac99daec70d8200836bacf06efad65624402` (initial insertion, red due to nested comment delimiters), `27cd26d70e68b981abfd71c62c0ce280b0837567` (comment repaired)
- **Exact revision-matched test:** GitHub Actions pinned integration [#39312192867](https://github.com/kyo-oo/HC-PROOF/actions/runs/39312192867) **GREEN**, commit `27cd26d70e68b981abfd71c62c0ce280b0837567`
- **Review:** self-audit; the quadratic interpolation independently checked with Wolfram Language using exact rationals, `Solve` returns `{}` and the cubic values are `1,0`

## Fixed, genuine CM geometry

On the central CM abelian sixfold (A=E^6), use genuine commuting algebraic endomorphisms (T=[2+i]^*), (U=[i]^*). The existing verified ((1-U)/2) projector kills odd K-weight sectors in middle cohomology. The two remaining even conjugate spectral pairs of T are:

- pure Weil: (lambda_p=-117+44i) and its complex conjugate, roots of (t^2+234t+15625);
- mixed: (lambda_m=75+100i) and its conjugate, roots of (t^2-150t+15625).

The existing (Q(t)=(t+234)(t^2-150t+15625)/6000000) equals 1 on both pure roots and 0 on both mixed roots. The parity-filtered projector is (mathcal P(T,U)=(1-U)Q(T)/2).

## New sharp minimal-degree theorem

Suppose a *rational quadratic* (q(t)=a+bt+ct^2) kills the even mixed pair and fixes the pure Weil pair. Because the coefficients are rational, one root condition per conjugate pair suffices.

At (lambda_m=75+100i), the real and imaginary constraints are

[
a+75b-4375c=0,qquad b+150c=0.
]

At (lambda_p=-117+44i), they are

[
a-117b+11753c=1,qquad b-234c=0.
]

Thus (b=-150c=234c), hence (384c=0), (b=c=0), and the first and third equations give (a=0) and (a=1), contradiction. Constants and linears are included as degenerate quadratics. Therefore **degree three is minimal among parity-filtered rational polynomials in T** satisfying both spectral requirements.

Lean declarations:
`cmWeilSixfoldQuadraticComplexEval`,
`cmWeilSixfold_even_eigenpairs_exact`,
`cmWeilSixfoldNoQuadraticEvenWeightIsolator`,
`cmWeilSixfoldEvenWeightCubic_exact_eigenpair_values`.

This is a *lower bound in the specified subalgebra* (mathbf Q[T]) after U-parity; it does not claim global minimality across all algebraic correspondences. The repository separately contains an even cheaper **three-operator** projector in (T,S=[1+i]^*,U), denominator 19,200, and that route remains available.

## Why the lower bound matters for source geometry

The earlier quadratic-or-less T-only attempt cannot separate the exact first-order nonsplit leakage from the pure Weil signal. Any two-operator ((T,U)) rational source construction using this parity filter needs at least four powers (T^0,ldots,T^3). The verified cubic attains that bound; it uses eight signed graph words after the U parities. The independent three-operator ((T,S,U)) construction uses eight graph words at lower word depth and denominator.

This result limits the complexity of a possible derived incidence/sheaf construction, but it does **not** provide a holomorphic deformation of the projected (K_0) class. The prior [Hodge-variation obstruction](2026-10-20-gst-derived-cm-graph-hodge-variation-obstruction.md) shows the unprojected single graph-ideal source has nonzero mixed variation (124); that particular raw object cannot deform unchanged. The next load-bearing operation is an actual coupled object with the projected pure Weil character and vanishing Atiyah/Kodaira–Spencer obstruction, followed by canonical Betti/Chow comparison.

## Evidence and disposition

- **Proved in Lean at pinned revision:** exact rational root arithmetic and no degree-0/1/2 projector in the stated restricted architecture; cubic evaluations.
- **Independent exact check:** Wolfram solved the four rational-linear constraints and evaluated cubic at both nonreal eigenvalues.
- **External geometric interpretation:** eigenpair classification and scheme-level cohomology action are grounded in existing repo derivations; this new Lean theorem itself is a scalar spectral statement.
- **Not claimed:** an all-period semiregular complex, arbitrary-X native source generation, universal Chow surjectivity, or final Hodge conjecture.
- **Route disposition:** bounded spectral-minimality question succeeded; broader original-X source-construction route remains open.
- **Next discriminator:** actual Atiyah obstruction for a nontrivially coupled representative of the three-operator, 19,200-denominator projected central (K_0) class, not for a direct sum of individually obstructed raw graph-ideal objects.

## Source-wide context consulted

The 701-file current branch tree was retrieved without truncation; source bodies were fetched and declaration-level fingerprints inspected for the entire Lean tree across the preceding and current continuation. Full theorem-by-theorem kernel audits of all 701 source files are **not** claimed. The active exact Hodge contract, semantic countermodels, world-birth/native transport, original-X residual/K0 projection, CM/Weil source and incidence, and recent deformation records were examined in greater detail.
