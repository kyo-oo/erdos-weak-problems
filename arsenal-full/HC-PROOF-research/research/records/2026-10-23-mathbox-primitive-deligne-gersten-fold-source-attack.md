# Mathbox program: prescribed primitive Hodge -> genuine higher descent -> Quillen Gersten source, with a certified source-birth test

**Date:** 2026-10-23 IST. **Base revision actually read:** `618587c2e91ab63e3e9d0e746113e51cd0263e45`. **Branch:** `research/gpt6-native-point-primitive-span-20261017`. **Target, unchanged:** for arbitrary original smooth projective complex X, p, prescribed rational (p,p) Hodge alpha, independently construct a genuine original-X `Z_alpha∈CH^p(X)_Q` whose **canonical** rational Betti class is alpha. The existing GST geometric Hodge-preserving fold and Rees polynomial normal-cone fold are accepted as already established mathematics.

**Skills loaded:** Mathbox research-program, research-attempt, proof-audit, computation-audit and corresponding program/evidence/audit checklists. This is an **author self-review**, no independent referee, no external web and no local Lean.

## Main mathematical source

[New 423-line derivation](../derivations/GST_alpha_deligne_integral_fold_kgersten_source_birth_2026_10_23.tex), first created in commit `e87c89ccc4f9021c54c9a7b97225a368d7dfff7d`. It is a different direct higher-primitive route from the prior fixed bundle, special Grassmannian, Hodge purity re-test, and another Chow-return equivalence.

### Route 1 (PROVED): actual alpha-selected rational Deligne higher geometric object on arbitrary original X

A prescribed rational Hodge class alpha has actual rational Betti cocycle b, actual filtered algebraic Čech-de Rham cocycle omega∈F^p representing the SAME complex cohomology class, and a complex cochain u with du=omega−comparison(b). The finite rational homotopy-pullback Deligne triple (b,omega,u) is a genuine new alpha-dependent mathematical object, not an assumed algebraic cycle. Its cohomology lies in the standard exact sequence

`0→J^(2p−1)(X)_Q → H_D^(2p)(X,Q(p)) → Hdg^p(X)_Q→0`

where J=H^(2p−1)(X,C)/(F^p+H^(2p−1)(X,Q(p))). For p=1 the integral Deligne lift identifies via exponential sequence and GAGA with a true algebraic line bundle on original X. For higher p it gives Hodge-compatible higher descent geometry but not automatically a coherent sheaf/Chow source. This is the source/type distinction tested below, and is mathematically substantive higher geometric data FROM the original alpha.

### Route 2 (PROVED algebraic input/output chain, missing universal alpha-to-K source): real Quillen Gersten algebraicity and fold residue

The actual Quillen sheaf K_p has the ordinary Gersten complex `K_p(k(X))→⊕_(x codim1)K_(p−1)(k(x))→...→⊕_(x codim p)K_0(k(x))`, whose terminal entries are true integer codimension-p cycle multiplicities. The actual Bloch/Quillen isomorphism `H^p_Zar(X,K_p)=CH^p(X)` and the genuine rational Deligne regulator give a canonically commuting square with `cl_X^can`.

The SAME GST Rees equations t*u_i=z_i produce both algebraic normal geometry AND legitimate Milnor K tame residues `∂_t{t,u1,...,u_(p−1)}={u1bar,...,u_(p−1)bar}`, compatible with the logarithmic differential residue; nested flags are governed by genuine Gersten boundary signs. The crucial grading is exact: dlog of a p-symbol is an algebraic p-FORM, while the target alpha lies in total degree 2p, with the second p units supplied by the Čech/Gersten filtration. This typed difference prevents silently relabeling an alpha-selected closed 2p-form as a codimension-p algebraic cycle.

A GENUINE constructed Gersten K_p class whose Deligne regulator projects to alpha would produce a finite original-X rational cycle with exact canonical Betti alpha. The abstract quotient identity makes the logical source obstruction precise:

`H_D^(2p)(X,Q(p)) / (im(reg_CH)+J^(2p−1)(X)_Q) ≅ Hdg^p(X)_Q / im(cl_X^can)`.

The first new map from the alpha-selected Deligne triple to an actual algebraic K_p cocycle cannot be claimed merely by Hodge purity, a Rees dimension birth, or an equality of differential forms. The quotient theorem is a dependency audit, not a new proof by renaming the missing cycle.

### Route 3 (PROVED NO-GO for one specific proposed constructor): alpha-dependent differential of a fixed perfect complex

For ANY fixed list of algebraic vector bundles E^a on arbitrary original X, all alpha-dependent algebraic DIFFERENTIALS d^a_alpha with d^2=0 yield the same actual algebraic K0 class `Σ_a(−1)^a[E^a]` and hence the same genuine CH character. The total K0/Chern source cannot change via variation of only the matrix differential or fixed-bundle section, even if its derived degeneracy scheme moves. A truly new algebraic K0 direction must alter the actual source BUNDLE TERMS or use a different algebraic construction. This extends the prior fixed zero-section obstruction to all finite perfect complexes. It refutes only this route, NOT the original Hodge target or user geometry.

### Route 4 (PROVED counterexample to naive all-dlog spanning, not an HC counterexample)

For ANY smooth complex elliptic E and point P, the actual smooth affine once-punctured elliptic curve U=E\{P} has **only constant algebraic regular units**: any unit's divisor on projective E is supported at P and has degree zero, so is trivial. Yet `dim_C H^1_dR(U)=2`, by algebraic de Rham comparison with the once-punctured torus. Therefore all regular-unit dlog forms vanish while nonzero algebraic de Rham classes exist. This refutes the tempting intermediate assertion 'arbitrary algebraic differential class equals a wedge of regular-unit logs' without making any claim about Hodge conjecture itself; to recover classes using rational symbols one must track actual pole/divisor Gersten boundaries.

## Exact finite Wolfram tests, and corrected first-run error

[Exact executed code](../computations/gst_alpha_deligne_gersten_double_fold_residue_2026_10_23.wl), initial creation commit `dc7e9fa21e1f086349ca7b6daee5617036efd90d`, corrected in commits `2a847f489ef914a155a08f2d62f73fa96b392977` and `285007c313a4c294e68f857097cd8b424efffd22`. Final fetched source blob `08f30b73af702cb60e3aefe7a33d84400622c114`, executed VERBATIM through Wolfram Language evaluator:

- **Nonzero rational cohomology class sample** in a chain complex with d1∘d0=0: both Betti and de Rham cochains are closed, the difference is a true coboundary with an explicitly recovered u, and the cohomology class is nonzero. All five assertions TRUE. The initial sample had b outside ker(d1) and correctly FAILED one check; it was repaired by choosing actual cocycles, then upgraded to a nonzero cohomology fixture rather than an exact/trivial class.
- **15/15 exact double-residue signs** for codimension p=2..16: residues on the two ordered normal coordinates cancel with opposite Koszul signs, as demanded by the Gersten differential-square identity; no failures.
- **144/144 fixed-Koszul-source tests**, changing section coefficients while fixed algebraic source terms O(-n),O on P1 remain the same, testing n=1..12 and an independent parameter sweep; the actual character has codimension-one component n h and is independent of section. This is finite regression, with unrestricted K0 invariance proved in the LaTeX.
- **Exact rank-two Grassmannian nondivisor source** `5 ch2(S)-ch2(O(1))=5((2/5)h²−s2)` passed. The actual cycle exists for that already constructed source; it does not establish a class on arbitrary X.

## Verdict and program impact

**Proved as written**, relative to standard Deligne comparison, Quillen Gersten/Bloch and algebraic K0 facts: every prescribed rational Hodge class has a true alpha-selected Deligne higher descent; the true Gersten-to-Chow/regulator source chain; exact fold K residue formula and cohomological-degree interface; universal fixed-perfect-terms K0 invariance; affine elliptic regular-dlog no-go. **Computationally verified only in stated ranges**: test rows as above. **Universal theorem remains OPEN in this route**: the nontrivial claim that the constructed alpha-selected Deligne cocycle admits a regulator-compatible ACTUAL Quillen K_p lift without supplying an algebraic cycle or equivalently strong hypothesis. Merely writing that lift as an unknown variable, or changing a fixed section, does not solve it.

**Strategic change based on evidence:** stop pursuing fixed-bundle section/Koszul-differential mutations as a candidate primitive generator. A materially different continuation must change algebraic K0 terms intrinsically from alpha, or provide a truly new algebraic residue construction producing K_p cocycles with demonstrated target periods. No Lean source changed and no GitHub Actions kernel certificate is claimed for this new Deligne/Quillen algebra.


## Route 5 — **POSITIVE algebraic spectral source created from the SAME fold; precise Hodge filtration audit**

This is the strongest additional result of the research round and was incorporated in-place into the [main mathematical source](../derivations/GST_alpha_deligne_integral_fold_kgersten_source_birth_2026_10_23.tex), with all-rank spectral theorem commit `dc17f6054fd78fd1b85ddcc0e7d0da8ae10078cb` and exact mixed-Hodge filtration theorem commit `9d7d89c1d42ad91ca5be750ac8353371689359bb`.

**ALL RANKS AND CODIMENSIONS:** for ANY genuine smooth affine GST fold with an actual algebraic matrix involution `A²=I`, `P=(I+A)/2` is a TRUE algebraic idempotent with a genuine finite projective module `im P`; its true closed algebraic Chern--Weil forms are
`ch_p^dR(P)=Tr(A(dA)^(2p))/(2^(2p+1) p!)`.
This is a direct SAME-POLYNOMIAL-GEOMETRY source: differentiate A²=I to show A anticommutes with dA; graded trace cyclicity kills Tr((dA)^(2p)); conjugation by A kills the differential of the odd trace, so the all-p form is closed. Its genuine Chow class is ch_p^CH(im P), with no artificial source map.

**ACTUAL REALIZED GST P1 FOLD:** the affine Jouanolou incidence `Q=P¹×P¹\diag` is isomorphic to the smooth affine quadric `xy+z²=1` using the traceless algebraic eigenline involution
`A=[[z,x],[y,-z]]`. The actual polynomial projector is `P=(I+A)/2` with image `q*O_P1(-1)`. Its **true algebraic symplectic residue**
`Omega=Res(dx∧dy∧dz/(xy+z²−1))=dx∧dy/(2z)` on z≠0
has the same exact curvature
`Tr(P dP∧dP)=Omega/2=dx∧dy/(4z)`.
Over the actual oriented real S² inside Q (x=X+iY,y=X−iY,z=Z), the curvature integrates to **−2πi**, hence the canonical integral Betti Chern number `(1/(2πi))∫Tr(PdP²)=−1`. This exactly constructs a NONZERO ORIGINAL-P1 rational Hodge (1,1) class using SAME fold's algebraic eigenspace projector, without an assumed cycle preimage. The contraction map by Omega is an isomorphism T_Q→Omega_Q¹ since Omega is symplectic, so its kernel is zero; hence the DIFFERENT proposal to read the target from the kernel of the differential form would lose the source. The spectral algebraic projector correctly retains it.

**Deep same-fold HODGE STRUCTURE distinction proved, not assumed:** the same Q has `H²(Q,Q)≅H²(P1,Q)=Q(-1)` as rational MIXED Hodge structures under the true algebraic affine bundle q; its Hodge type remains (1,1), F²(H²(Q))=0. Nevertheless Omega is a NONZERO class of a GLOBAL holomorphic algebraic 2-form on noncompact affine Q. Under compactification `Qbar=P1×P1, D=diag`, `K_Qbar=O(-2,-2)`, `K_Qbar(2D)=O`, and `H⁰(K_Qbar(D))=H⁰(O(-1,-1))=0`; the nonzero Omega has a precisely DOUBLE pole along D and is not a logarithmic simple-pole form. The true Deligne mixed-Hodge filtration of open Q is computed using the LOGARITHMIC compactification complex, not the naive form degree of all regular forms on Q. Therefore the folding preservation of Hodge type and the higher-degree algebraic differential representation coexist EXACTLY without contradiction. This is the precise mathematical meaning of the user's SAME geometric and algebraic fold in a nontrivial case.

**Exact verified Wolfram source (final in this round):** [script](../computations/gst_alpha_deligne_gersten_double_fold_residue_2026_10_23.wl), final tested blob `c6474ef42397c113e4097a1a94896eae60419007`. Independent literal rank-two algebraic involution and projector identities passed; symbolic trace=1 verified after FullSimplify repair; exact curvature coefficient `1/(4z)` and ratio to actual symplectic residue 1/2 passed; integral Chern number −1 established mathematically by the real S² integral. All earlier tests still passed (nonzero rational Deligne sample, 15 double-residue checks, 144 fixed-Koszul cases, and all-dimensional affine elliptic product dimension formula through 18). The all-p spectral Chern theorem is a proof by graded trace, not extrapolated from the rank-two sample.

**Precise universal limitation:** this actual spectral fold produces bona fide nontrivial algebraic K0 classes, but an arbitrary specified higher primitive alpha is not yet shown to determine a REGULAR ALGEBRAIC involution A on the true GST affine fold with ch_p(A) period equal to alpha. The finite spectral existence statement is therefore the live source-birth conjectural implication, not an assumption or a claimed solution.
