# GST continuation: uniform CM orbit, finite shear, and the actual object test

- **Program:** the unchanged canonical original-X rational Hodge construction, or an actual smooth projective counterexample.
- **Starting revision:** `a4276f966c427e8f63ff7b9cf4624b4d97d0b6b8` on `research/gpt6-native-point-primitive-span-20261017`.
- **Handoff comparison:** 147 commits and 39 changed paths after `b6ed3ad55e40aaed1d3d5eed8de7ce1aeab14a18` were mapped; all 701 tracked Lean modules received an overview pass. See the [complete module overview](2026-10-20-gst-701-module-overview.md).
- **Proof file:** existing `GSTUniversalCMArithmeticObstruction.lean`, strengthened in place.
- **Repair:** `d037d2fc2e492a1c6a94d4150e638202d0db88b1`, [integration 39380343799](https://github.com/kyo-oo/HC-PROOF/actions/runs/39380343799), successful.
- **New proof revision:** `a1f5671c71d67549a3604a4af243cca25aa12374`, [integration 39380974460](https://github.com/kyo-oo/HC-PROOF/actions/runs/39380974460), successful, 8,966 build jobs. Downloaded artifact 12244898320 contains zero `sorryAx` occurrences; the new declarations use only `propext`, `Classical.choice` where needed, and `Quot.sound`.
- **Review:** Mathbox-guided self-review, Wolfram symbolic cross-check, and a separate exact Python implementation. No independent derived-geometric review is claimed. No public web research, subagents, or local Lean installation.

The universal construction and a genuine Hodge counterexample were not obtained. The new results below remove a finite exponent restriction, upgrade a first-order identity to an exact parameter identity, and identify a specific nonzero object-level obstruction rather than inferring deformation from Chern cancellation.

## 1. The post-handoff mathematics that controls this continuation

| Existing progress | Strongest usable result | Relevant source |
|---|---|---|
| Original-X mixed K0 source birth | Arbitrary finite incidence/Koszul factors, with the correct leading Chow grade and relative Todd correction | `GSTUniversalResolvedSupportHodge.lean` |
| Quadric-center blowup | Actual exceptional surface difference has primitive norm 2; the full Hodge ranks and algebraic ranks are both `(1,2,3,2,1)` | [Blowup audit](2026-10-19-quadric-blowup-rational-hodge-counterexample-audit.md) |
| GST cosmology | Genuine split births preserve missing source directions; codimension-two blowup canonical cycle blocks are onto exactly when their base and center blocks are onto | `GSTGraphV2SelfExpandingCosmology.lean` |
| Actual geometric operators | Bare geometric raising/lowering words cannot rotate a joint middle-primitive vector; projective-degree moments vanish on its invariant primitive orbit | `GSTClassicalHodgeRankFreeLefschetzPoincareGeneration.lean` |
| Secant extraction | A genuine ordinary sheaf with the specified Betti character yields a Chow source on the original fourfold; the relative sheaf construction is a separate input | `GSTWeilFourfoldAuxiliaryExtraction.lean` |
| CM projector and incidence | Three genuine CM operators give the 19,200-denominator frame; opposite-sign bare graph Ext3 has a parity obstruction; neutral auxiliary incidence provides candidate Ext2 arrows | `GSTUniversalCMArithmeticObstruction.lean` |
| Corrected full-kernel incidence | The component-aware capacities are 35 or 120, with connected numerical rank **144**, superseding the older symmetric-35 minimum 150 as the sharper model | `cmWeilSixfoldFullKernelLCI_connected_rank_144` and `_connected_rank_feasible` |
| Smaller integral Weil source | Two explicit four-product integral Chow expressions and pure perfect-K0 lifts at the split CM fibre; full Gram `-32 I2`; a simple pure representative would have Ext2 dimension at least 15 | [Integral source](2026-10-20-gst-four-divisor-integral-weil-k0-source.md), [full lattice](2026-10-20-gst-integral-weil-lattice-gram-and-deformation-no-go.md) |
| Latest mixed tangent test | Both complete first-order Weil variations factor through two exterior-repetition annihilators | `cmWeilCMIntegralMixedLeakFactorization`, `_MixedLeakVanishes` |

This mapping preserves the existing route. In particular, rank 144 is a numerical capacity certificate, not an already constructed semiregular family, and the primitive-integral source should not be confused with the older 4,800-scaled graph numerator.

## 2. A uniform CM channel, replacing the six-offset bound

Write

\[
(2+i)^n=a_n+i b_n,\qquad
(a_{n+1},b_{n+1})=(2a_n-b_n,a_n+2b_n).
\]

The existing definition is `cmTwoPlusIGaussianPower`. For every n, the new induction proves

\[
a_n+2b_n\equiv1\text{ or }4\pmod5.
\]

For every positive exponent,

\[
a_n-2b_n\equiv0\pmod5.
\]

The second assertion follows immediately from
`(2a-b)-2(a+2b)=-5b`; the first follows because the next unit channel is congruent to four times the previous one. If b_n were zero, both channels would coincide, a contradiction. If a_n were zero, the channels would be negatives of one another, again a contradiction. Thus

\[
\boxed{a_n\ne0,\quad b_n\ne0\quad\text{for every }n\ge1.}
\]

The n=0 exclusion is necessary: b_0=0. The formal declarations are:

- `cmTwoPlusIGaussianPower_modFive_unit`;
- `cmTwoPlusIGaussianPower_modFive_zero`;
- `cmTwoPlusIGaussianPower_imag_nonzero`;
- `cmTwoPlusIGaussianPower_real_nonzero`.

The previous `_imag_nonzero_to_six` now follows from the uniform theorem instead of six separate evaluations. `cmWeilAllPositiveWeightOneSourceReconstruction` then reuses the existing exact Cramer compiler with the actual coefficients a_n,b_n; it needs no additional premise `b_n != 0`. For a genuine Weil `(p,p)` plane use its even exterior weight n=2p. It still needs an independently constructed nonzero native source and the true canonical isogeny comparison; arithmetic does not supply that source.

## 3. Exact finite mixed shear, including its quadratic term

Define the two existing four-divisor source expressions by

\[
R=-a_1a_2a_3+a_1b_2b_3+b_1a_2b_3+b_1b_2a_3,
\]
\[
I=b_1a_2a_3+a_1b_2a_3+a_1a_2b_3-b_1b_2b_3.
\]

Use the same mixed shear as the preceding theorem:

\[
a_1(t)=a_1+td_1,\quad b_1(t)=b_1+itd_1,\qquad
a_2(t)=a_2+td_2,\quad b_2(t)=b_2-itd_2.
\]

Keep a_3,b_3 fixed. In **any commutative ring**, with L_R,L_I the complete previously defined first-order variations, the exact identities are

\[
R(t)-R(0)=tL_R-(i^2+1)t^2d_1d_2a_3,
\]
\[
I(t)-I(0)=tL_I+(i^2+1)t^2d_1d_2b_3.
\]

There are no higher terms. The minus sign in the real quadratic term matters and was independently checked in Wolfram. Combining this exact expansion with

\[
i^2=-1,\qquad d_1(a_2-ib_2)=0,\qquad d_2(a_1+ib_1)=0
\]

and the existing complete first-order factorization gives

\[
\boxed{R(t)=R(0),\qquad I(t)=I(0)\quad\text{for every scalar }t.}
\]

Formal declarations: `cmWeilCMIntegralMixedShearExpansion` and `cmWeilCMIntegralMixedShearInvariant`. This is stronger than a vanishing derivative. Its geometric application is to the specified two-form substitution in the complexified even Betti algebra, where the two annihilators come from exterior repetition. It does not assert that the individual factors remain algebraic divisors at moved periods, that every scalar parameter is a positive polarized period, or that a relative perfect object has been constructed.

## 4. Direct check of the actual split representative's obstruction

Let Q_Aj be the previously constructed integral perfect-K0 class

\[
Q_{A_j}=[L_{A_j}]-[\mathcal O_{S_j}]+[\mathcal O_{p_j}].
\]

Consider the **unmodified signed-direct-sum/shift representative** of the real source R. Its term `-Q_A1 tensor Q_A2 tensor Q_A3` contains the actual shifted line bundle

\[
L[1],\qquad
L=L_{A_1}\boxtimes L_{A_2}\boxtimes L_{A_3},
\quad c_1(L)=A_1+A_2+A_3.
\]

With the repository's holomorphic forms u_j,v_j and antiholomorphic forms U_j,V_j,

\[
A_j=(u_j\wedge V_j+U_j\wedge v_j)/2.
\]

Along the named tangent `u1(t)=u1+t V2`, `v2(t)=v2+t U1`, express the fixed class in the moved holomorphic basis. Its `(0,2)` variation is

\[
\delta c_1(L)=-\tfrac12(V_2\wedge V_1+U_2\wedge U_1)
=\tfrac12(V_1\wedge V_2+U_1\wedge U_2)\ne0.
\]

The two displayed exterior monomials are independent in the genuine complex torus's H2(O). The standard line-bundle Atiyah/Kodaira-Spencer identification therefore gives `At(L) contracted with kappa != 0`.

This detects the actual direct-sum object, not merely its Chern trace. If j and p are the inclusion and retraction of its summand L[1], Atiyah naturality gives

\[
p[2]\circ\operatorname{ob}(F_R)\circ j
=\operatorname{ob}(L[1])\ne0.
\]

Hence the **unmodified split direct-sum representative** cannot deform along this tangent, even though its full pure Weil character has the exact cancellation in section 3. Shift conventions can change a sign but cannot make this summand's obstruction zero. A genuinely coupled different representative of the same K0 class is not excluded by this argument.

The exterior coefficients are computed from the forms by the reproducible script, rather than entered as a desired answer. The scheme-level Atiyah comparison and derived naturality in this paragraph are mathematical geometric inputs, not newly instantiated Lean structures. This is a self-audited object-specific derivation, not a Hodge counterexample.

### The complete nine-parameter test: six directions are detected

At the same equally polarized split CM seed, write the entire K-compatible polarized tangent chart as

\[
u_a(t)=u_a+\sum_b t_{ab}V_b,\qquad
v_b(t)=v_b+\sum_a t_{ab}U_a,\quad 1\le a,b\le3.
\]

There are nine independent complex parameters. The real source's direct-sum expansion contains four external line-bundle summands with factor patterns `AAA`, `ABB`, `BAB`, `BBA`. For one such summand, put `(p_j,q_j)=(1,1)` for an A factor and `(i,-i)` for a B factor. Its c1 is `sum_j (p_j u_j wedge V_j + q_j U_j wedge v_j)/2`. For a<b the actual `(0,2)` coordinates of its variation are

\[
[V_a\wedge V_b]\delta c_1=(p_a t_{ab}-p_b t_{ba})/2,
\quad
[U_a\wedge U_b]\delta c_1=(q_b t_{ab}-q_a t_{ba})/2.
\]

The resulting line-summand obstruction matrix has shape **24 by 9** over Q(i). Its ranks after adjoining the four line summands are **3,5,6,6**. Its kernel is exactly the diagonal parameter subspace `span(t11,t22,t33)`.

This rank statement has a direct all-parameter proof. For each unordered pair, the AAA row imposes `t_ab-t_ba=0`. The ABB row separates pairs (1,2) and (1,3); the BAB row separates pair (2,3). In each pair the additional equation is `t_ab-i*t_ba=0`. The coefficient block has determinant `(1-i)/4 != 0`. Taking the three independent pair blocks gives an explicit six-by-six minor

\[
((1-i)/4)^3=-(1+i)/32\ne0.
\]

All diagonal columns are zero, proving rank exactly six without parameter sampling. Python exact Gaussian-Fraction elimination and an independently constructed Wolfram matrix agree on the ranks and kernel. The Python script also checks that the selected six-by-six minor is exactly this block-diagonal matrix.

The scalar argument is also formalized in the same existing Lean module as `cmWeilCMIntegralMixedPairConstraints_iff_zero` and `cmWeilCMIntegralMixedLineConstraints_iff_diagonal`. The latter works for **any linearly ordered index type**, rather than only a three-by-three chart, over every characteristic-zero field with a chosen i satisfying i squared equals -1. The pair detector derives `i != 1` from that equation; no independent determinant or rank hypothesis is supplied. The actual three-pair line-bundle geometry provides these rows for its three unordered pairs. This scalar formalization does not instantiate the scheme-level Atiyah comparison.

**Geometric consequence for this actual representative:** every off-diagonal mixed tangent gives a nonzero obstruction on at least one of the displayed retract line bundles, hence on the unmodified direct-sum perfect object. The diagonal subspace is the kernel of these necessary *line-summand* constraints; no assertion is made here that every diagonal deformation is unobstructed for the full object, or that the same necessary constraints apply to genuinely coupled different representatives. In particular, reducing the pure K0 source from the old 4,800-fold graph numerator to the primitive-integral class removes the numerical Euler inflation but does not remove this explicit direct-object obstruction.

## 5. Executed evidence and next exact construction

The [standard-library exact script](../computations/gst_weil_uniform_power_and_shear.py) multiplies sparse rational polynomials, verifies both full shear remainders are zero, checks the earlier leak factorization independently, compares the linear Gaussian recurrence with binary Gaussian exponentiation for **every n=1,...,512**, checks the norm 5^n and both mod-five channels, computes the line-bundle exterior variation from the stated shear, and exactly reduces the full 24-by-9 Gaussian obstruction matrix with its explicit nonzero six-by-six minor. Its [output](../computations/gst_weil_uniform_power_and_shear.output.json) and [version-2 manifest](../computations/gst_weil_uniform_power_and_shear.manifest.json) pin the inputs and bounds. The finite exponent test supports the implementation; the Lean induction proves the unrestricted statement.

Wolfram independently returned the two quadratic coefficients
`-(1+i^2)*a3*d1*d2` and `+(1+i^2)*b3*d1*d2`, zero corrected polynomial remainders, and the channel identity `a'-2b'=-5b`. An exploratory check initially tested the wrong sign for the real quadratic term; its nonzero remainder identified that mistake before the correct formula was committed. The Lean ring proof and separate Python polynomial arithmetic agree with the corrected signs.

**Nearest unresolved implication:** construct a genuinely coupled perfect object in the smaller integral Weil K0 class and show that its actual `At(F) contracted with kappa` vanishes, with the required canonical Betti comparison. The split direct sum cannot be used for this step. The corrected 144-rank incidence candidate remains an alternative existing constructor whose whole dg differential and Atiyah class require an object-level calculation. A sheaf that is only supplied by a period-spread assumption cannot discharge the obligation.

**Counterexample route:** the existing quadric blowup and smooth known-center blowup decompositions do not create a nonalgebraic Hodge class. On the nonsplit Weil candidate, a true disproof still requires proving that the projected canonical Chow image is zero for **all** algebraic cycles; neither this object's obstruction nor divisor-sector failure proves that.

**Continuation disposition:** arithmetic and finite-shear sub-obligations proved; the explicit direct-sum deformation subroute refuted for the named tangent; genuinely coupled object and arbitrary-original-X source routes remain open. Preserve the all-X target and attack this object-level step rather than repeating the character cancellation or lowering another numerical incidence budget.
