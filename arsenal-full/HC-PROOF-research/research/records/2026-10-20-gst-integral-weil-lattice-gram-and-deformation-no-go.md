# GST Mathbox — integral Weil lattice Gram and nonsplit source no-go

- **Date:** 2026-10-20 (IST)
- **Kind:** structural mathematical finding and scoped deformation obstruction
- **Program:** original-X universal rational Hodge-to-Chow, Gate 3
- **Base checkpoint:** \`56c32b0a5f6b90134d43e772bfbdfd8984327c07\`
- **Exact target:** for every original smooth projective complex X and every rational (p,p) class, independently construct a genuine codimension-p rational Chow cycle with canonical Betti class equal to the target
- **Local test:** split CM sixfold A=E^6 and its smaller integral exceptional Weil source; these results do **not** imply the universal target
- **Nearest prior work:** [four-divisor split integral Weil source](2026-10-20-gst-four-divisor-integral-weil-k0-source.md)
- **Mechanism:** Gaussian orthogonal tensor law, full integral Weil lattice pairing, CY6 Serre constraint, and ample-primitive obstruction to effective/line-bundle-only deformation
- **Review:** Mathbox-guided self-audit, exact exterior enumerator and separate Groebner reduction; not an independent geometric proof audit
- **Evidence:** Lean theorems on ring/linear/integer inputs are *proved as written* at pinned green commits; claimed geometric applications have the explicitly stated additional canonical comparison and positivity hypotheses

## 1. New kernel-checkable full integral intersection theorem

For each actual CM elliptic pair S_j=E_j × E_(j+3), the algebraic divisors are

\[
A_j=e_j\wedge e_{j+3}+f_j\wedge f_{j+3},\qquad
B_j=e_j\wedge f_{j+3}-f_j\wedge e_{j+3}.
\]

They obey \(A_j^2=B_j^2=-2[p_j]\) and \(A_j B_j=0\) in the complex orientation on S_j. The already constructed integral Weil Chow expressions are

\[
\begin{aligned}
W_R&=-A_1A_2A_3+A_1B_2B_3+B_1A_2B_3+B_1B_2A_3,\\
W_I&=B_1A_2A_3+A_1B_2A_3+A_1A_2B_3-B_1B_2B_3.
\end{aligned}
\]

The new theorem \`cmWeilGaussianDivisorPairMul_orthogonal\` proves in any commutative ring that multiplication of two orthogonal equal-square Gaussian pairs retains real/imaginary orthogonality and equal square. Iterating it gives \`cmWeilCMIntegralSixfoldFullGram\`:

\[
W_R^2=W_I^2=-32P,\qquad W_R W_I=0,\qquad
P=[p_1][p_2][p_3].
\]

The new \`cmWeilCMIntegralFullLatticePairing\` then proves, for **every** four integer coefficients, the identity

\[
(mW_R+nW_I)(m'W_R+n'W_I)=-32(mm'+nn')P.
\]

This is now a reusable universally quantified Lean algebraic invariant, not only a finite exterior enumeration. Its interpretation as canonical Betti intersection uses the genuine scheme cohomology comparison, which is not inhabited by the pure commutative-ring theorem itself.

## 2. CY6 numerical pressure for every smaller integral source

If a perfect object F on A has **precisely** pure Chern character

\[
\operatorname{ch}(F)=mW_R+nW_I
\]

with no other positive or rank Chern-character components, standard abelian HRR and complex Serre duality imply

\[
\chi(F,F)=32(m^2+n^2)=2e_0-2e_1+2e_2-e_3,
\quad e_j=\dim\operatorname{Ext}^j(F,F).
\]

The new Lean declarations \`cmWeilCMIntegralLattice_CY6SerrePressure\`, \`cmWeilCMIntegralLattice_simpleExtTwoPressure\` and \`cmWeilCMIntegralBasis_simpleExtTwo_minimum\` certify the exact integer implications

\[
e_0+e_2\ge16(m^2+n^2),\qquad
e_0=1 \Rightarrow e_2\ge 16(m^2+n^2)-1.
\]

Thus a simple basis-class realization must have \(e_2\ge15\), whereas a simple realization of \(W_R+W_I\) must have \(e_2\ge31\). This is **not** the previous enormous 4800-scaled Euler pressure. Both inequalities are compatible with a 495-dimensional raw semiregularity target and do not prove Atiyah-obstruction vanishing.

## 3. Exact exterior primitivity and necessary signed support

Let \(h=\sum_{k=1}^{6}e_k\wedge f_k\), the standard positive product-polarization class on E^6. Each term in W_R and W_I contains one cross divisor from **each** elliptic pair. The local polarization on either elliptic coordinate wedges to zero with either \(A_j\) or \(B_j\). Therefore, directly in the full 12-generator exterior algebra,

\[
h\smile W_R=h\smile W_I=0
\quad\Longrightarrow\quad
h^3\smile(mW_R+nW_I)=0.
\]

Independent exact checks used all 12 wedge symbols \(e_1,\ldots,e_6,f_1,\ldots,f_6\), sign from inversion count, and all 32 nonzero coefficients for each W. They verified: hW_R=0, hW_I=0, W_RW_I=0, and W_R²=W_I²=-32 in *complex* orientation (the e-first orientation differs by a minus sign). A separate exact Groebner reduction modulo the nine surface relations reproduced the full -32/-32/0 Gram.

When \((m,n)\ne(0,0)\), the nonzero self-pairing proves \(mW_R+nW_I\ne0\) over rational cohomology. On a polarized projective sixfold, every nonzero **effective** codimension-three algebraic cycle Z satisfies \(\int_A h^3[Z]>0\). Every nonzero integral Weil class above has degree zero against h³. Hence **no nonzero integral Weil class equals the class of an effective codimension-three cycle**. In particular, a single coherent sheaf with ch_0=ch_1=ch_2=0 cannot have this nonzero ch_3, because its first nonzero support-cycle class in codimension three would be effective.

This excludes an *effective/pure-support ordinary coherent sheaf* realizing the specified character. It does not obstruct signed rational algebraic cycles, virtual K₀ sources, or a genuinely derived complex, and it certainly does not refute the Hodge conjecture.

## 4. Another necessary condition at a nonsplit Weil period

Suppose the nonsplit Weil abelian sixfold has the explicit extra hypothesis \(\mathrm{NS}_{\mathbb Q}(A)=\mathbb Q h\). Then every line bundle L has \(c_1(L)=q_L h\) and hence \(\operatorname{ch}_3(L)=q_L^3 h^3/6\). A skyscraper sheaf has ch_3=0. Therefore every finite K₀ combination of line bundles and skyscraper sheaves has ch_3 in the rational **ample-cubic line** \(\mathbb Q h^3\).

A nonzero primitive W satisfies hW=0, whereas h⁴≠0 for an ample h on a sixfold. Were W=q h³, we would have 0=hW=q h⁴, forcing q=0 and W=0, a contradiction. The abstract fully typed linear-algebra contradiction is now the Lean theorem \`cmWeilCMIntegralPrimitiveNotAmpleCubic\`.

Consequently, a **naive component-by-component deformation** of the original split line-bundle/point recipe to such a rank-one Néron–Severi period cannot produce W. A genuine nonsplit class must be provided by geometrically new sheaves, additional correspondences, or a truly coupled derived complex. The Néron–Severi rank-one premise is not asserted for every period.

## 5. Route status and exact evidence boundary

- **Succeeded:** generalized Gaussian orthogonality, full integral lattice Gram, all-integer Serre pressure and abstract ample-cubic exclusion as Lean theorems
- **Scoped no-go:** single nonzero effective codimension-three carrier, rank-zero ordinary coherent sheaf of precisely pure ch₃, and line-bundle/point-only construction under the stated Picard-rank-one hypothesis
- **Still open:** construct a genuinely coupled perfect object on an actual **nonsplit** Weil sixfold with pure primitive character and prove \(\operatorname{At}(F)\lrcorner\kappa=0\) in genuine derived Ext²; then establish canonical Betti equality and, separately, the universal original-X primitive construction
- **Proof file:** \`GSTUniversalCMArithmeticObstruction.lean\`
- **Exact Lean proof commits and CI:** \`efe5fd7f8befaeaa224667424142b5ffc341911e\` GREEN [#39361657338](https://github.com/kyo-oo/HC-PROOF/actions/runs/39361657338); \`f8bf2a0e89f4531406b8c1218a36253896ee6b52\` GREEN [#39362181323](https://github.com/kyo-oo/HC-PROOF/actions/runs/39362181323); \`772f8c3107fba54705122e453268ad1f2aabe36a\` (revision-matched CI must be checked)
- **First unresolved implication:** geometric existence, Yoneda differentials/coupling, semiregularity of the *specific* Atiyah class, and canonical original-variety cycle-class comparison cannot be inferred from symbolic Gram identities
- **Route disposition:** arithmetic/Gram completed; no-go routes closed only for their stated carrier class; genuine derived-coupled nonsplit route retained as open
