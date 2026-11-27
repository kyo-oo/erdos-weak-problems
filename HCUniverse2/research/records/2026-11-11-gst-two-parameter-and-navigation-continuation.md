# Mathbox research continuation — GST Image-3 exact two-parameter source (11 November 2026)

**Starting checkpoint:** \`research/records/2026-11-11-gst-image3-advanced-curvature-rigidity-checkpoint.md\`.
**This continuation HEAD:** \`77fbcdc454b5a02a2e5d5695724a34e5e024f50d\`.
**Branch:** \`research/gpt6-image3-advanced-curvature-rigidity-20261111\`.
**Provenance:** author research assisted by Mathbox research-program and computation-audit protocols, direct source checking, independent Python finite-field elimination, and exact Wolfram evaluation. Review is a self-audit, not an independent formal referee decision.

## Exact source target contract

The native object is the AUTHOR-ORIGINAL \`WaveSignal = (Fin 4 × Fin 3) → ℚ\`, exact U shuffle, J signed CM mirror, M diagonal Wave-I SURVIVE, C=JM-MJ, mixed seed \`v=e_(0,0)+e_(0,1)\`.
Two parameters \`a,b∈Q\` control the existing source operators via \`F_(a,b)=U+J+aM+bC\`. They are *not* claimed to be original physical Navigation constants; the separate original \`navigationCharge\` is binary.

Exact success for native full cyclicity: \`det [v,Fv,...,F^11v]≠0\` over Q.
Exact geometric success for Hodge would additionally require actual all-X algebraic correspondence inputs and a noncircular canonical Betti Hodge full-rank landing. Native cyclicity alone is not that success.

## Route A: unique permanent curvature resonance (new complete source-level result)

The all-a,b block determinant decomposes as \`D=(2b-1)D10*Res\`.
The **symbolically verified leading coefficients** in a are
\`[a^8]D10=64(b-2)^2\`, \`[a^12]Res=2560\`,
so \`[a^20]D=163840(2b-1)(b-2)^2\`.
For b≠1/2,2, D(·,b) is a nonzero degree-20 Q-polynomial. For b=2,
the original exact determinant \`D(0,2)=-10365615590204736\` is nonzero.
For b=1/2, the original maximum-cell source is inaccessible from the mixed seed and D≡0. Hence the **sole permanently noncyclic rational b is 1/2**; otherwise each rational b has infinitely many good rational a and at most 20 bad a.

**Exact computation:**
\`research/computations/GST_image3_all_rational_curvature_strength_two_parameter_classification_20261111.wl\` returned \`allPassed=True\`.

## Route B: infinite integer curvature progressions uniformly good for ALL rational a

Exact finite-field certificates and the rational-root theorem establish:
\`b≡1 (mod11)\`, or \`b≡9,14,21,27 (mod29)\` implies
\`D(a,b)≠0\` for all rational a and integer b.
Each residue field is enumerated completely; the a^20 leading coefficient is a nonzero residue in the relevant classes, so rational denominators cannot evade the reduction. Wolfram \`allPassed=True\` for the exact four-class mod29 script, and an independently written modular Gaussian-elimination implementation checked the field patterns.

**Exact computations:**
\`research/computations/GST_image3_mod29_curvature_classes_all_rational_source_20261111.wl\`,
\`research/computations/GST_image3_all_rational_direct_strength_CM_curvature_mod11_20261111.wl\`.
**Derivation:**
\`research/derivations/GST_image3_two_parameter_permanent_resonance_and_mod11_20261111.md\`.

## Route C: exact corank-one half-curvature at ALL rational a

At b=1/2, the original maximum coordinate is zero on every source iterate: orbit dimension ≤11 (native Lean previously compiled). The exact 11x11 determinant on its invariant kernel is

\[
\det K_{11}=\frac{P_8(a)\,[69-72a+20a^2]}{512},
\]

with \`P8(a)=11583665+66174720a-44920944a²-19478232a³-1670652a⁴-2895936a⁵+666144a⁶-82944a⁷+36864a⁸\`.

The \`P8\` polynomial has no roots in F13, its leading coefficient is a mod13 unit, so it has no rational root. The quadratic is strictly positive by \`5Q=(10a-18)²+21\`. Therefore the kernel 11x11 determinant never vanishes over Q and the source rank is **EXACTLY 11** for every rational a.

**Exact computation** \`research/computations/GST_image3_half_curvature_exact_rank11_all_rational_20261111.wl\` returned \`allPassed=True\`. The 11x11 structural determinant identity was verified separately from its factor polynomials. **Derivation:** \`research/derivations/GST_image3_half_curvature_exact_rank11_all_a_20261111.md\`.

## Route D: N-cohomology and physical Navigation bridge

The original NShape hole indices are retained in new Lean module
\`GSTImageThreeIndependentNCohoSource.lean\`; source strengths vary
hole-by-hole with exact two-cell recurrence and independently chosen
two-step reconstruction coefficients. This does NOT imply a shared
single Krylov orbit on the full direct sum.

The separately proved SOURCE CRT construction gives shared full
\`12h\` orbit for every finite h and any cyclic pair a,b, with
adaptive rational channel shifts \`S(a,b)=5+4|a|+4|b|\`.

Original physical \`navigationCharge R∈{0,1}\` is connected via
\`GSTImageThreePhysicalNavigationControl.lean\`: half-strength is
physically unreachable, actual Navigation-on has b=1 and hence the
source-level all-rational-a full-rank consequence, canonical tails
preserve the exact physical source. This integration does not
identify arbitrary rational b with the physical charge.

## Formal Lean status and source verification

The following files were edited or added with no intentional sorry:
- \`GSTImageThreeCurvatureResonance.lean\`: repaired historical errors, fixed-pair second-order recurrence, exact determinant, constructive two-step reconstruction and kernel noncyclicity at b=1/2.
- \`GSTImageThreeAdvancedGeometricSource.lean\`: five actual closed correspondences and exact native/Betti composition witnesses; CI exposed two Betti coercion errors subsequently amended in commit \`82626278af4ebaf2caea545f9ce8fdfb099ddf67\`.
- \`GSTImageThreeOriginalXCurvatureLanding.lean\`: corrected strict distinction between abstract operator pairs and actual geometric correspondences; cycle-class-image preservation.
- \`GSTImageThreeFiniteFieldSourceCertificates.lean\`: finite-field F11 Q8/Q12 and F13 half-curvature P8/Q2 no-root checks, rational quadratic positivity. All are claimed only if exact CI passes.
- \`GSTImageThreeIndependentNCohoSource.lean\`: original NShape arbitrary-hole local source laws.
- \`GSTImageThreePhysicalNavigationControl.lean\`: real binary navigation charge and canonical-tail transport.
- \`GSTImageThreeAdvancedResearchKernel.lean\` and workflow: integrated one-target Lean CI.

The parent native module compiled successfully in run 43013771919, then the older workflow failed on a repeated temporary lake library generator call. The duplicate-target workflow issue is repaired. An intermediate geometry run 43028657899 narrowed errors to two Betti coercion normalizations, repaired in the later source commit. As of this checkpoint, exact updated unified CI verification has not yet been promoted to green; do NOT claim full integrated kernel proof until its run succeeds and is inspected.

## Noncircular geometric frontier

The source rank/cyclic analysis is substantially upgraded, with a unique permanent resonance and arithmetic-strength families. The universal Hodge antecedent remains a distinct obligation: build real algebraic X×X correspondences and sources from GST for arbitrary smooth projective X,p, prove compatibility with canonical rational Hodge classes, and achieve full original-X rank without assuming algebraicity of unknown Hodge classes. Neither the finite-source certificates nor an abstract \`CycleClassOperatorPair\` proves that universal existence.

**Continuation boundary:** inspect exact-HEAD Actions job for the unified root, repair only actual errors, then formalize the remaining full 11x11 determinant and rational-root lifting if a deeper Lean kernel claim is needed. Never relabel the arithmetic-source theorem as a universal Hodge proof.
