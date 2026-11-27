# Mathbox: actual GST Plücker–Fitting source algebra, alpha-directed Todd K0 and canonical Chow return

**Date:** 2026-10-23, Asia/Kolkata. **Active branch:** `research/gpt6-native-point-primitive-span-20261017`. **Starting HEAD read:** `c9e265faad8972ab809cfafc670549876af9b441`. **User's exact request:** FORM AND CONSTRUCT THE MISSING ALGEBRA connecting the complete GST all-dimensional spatial fold with actual original-X rational Hodge cycle construction. No public-web research and no local Lean install. **Mathbox skills read:** `research-program`, `research-attempt`, `proof-audit`, `computation-audit`. This is a self-audited mathematical derivation and exact Wolfram computation, not independent peer review.

## Actual constructed ALL-RANK incidence algebra

[Full 1220-line algebraic derivation](../derivations/GST_explicit_plucker_fitting_source_algebra_all_rank_original_X_2026_10_23.tex), first commit `f7fd0a423becf80c51fd1c8469101f6d71ca8af1`, extended with pure rational Chow Fitting theorem `ede47db79a339de4853a8caeef0bab2d9a2c8e1c` and exact original topological/algebraic K0 obstruction `4bb80c23a867af3860dda35879a2521c941b8aa8`.

For the genuine smooth affine GST incidence world `J_G={(S,[phi])∈Gr(r,C^m)×P((Λ^r C^m)^*):phi(Λ^r S)≠0}`, **EXPLICIT rank-r algebraic projection** onto tautological S:

`P_(S,phi)(w) = sum_(i=1)^r u_i phi(u_1∧...∧w_(i)∧...∧u_r)/phi(u_1∧...∧u_r)`,

independent of basis u_i and rescaling phi, regular on J_G and satisfying P²=P, trace(P)=r and im(P)=q^*S for ALL r,m. Cramer's alternating-form identity proves the complete all-rank theorem, independently of finite tests. It is a true finite incidence-pole solution to the existing algebraic projector-scheme equations, not a hypothetical K0 image.

For ANY honest idempotent P∈Mat_M(R), R coordinate ring of ANY smooth affine GST world, rank(P)=r and s=r-p+1, choose genuine constant ambient sections v_1...v_s. The **ACTUAL Fitting ideal**

`I_(M-p+1)([I_M-P | P v_1 | ... | P v_s])`

is scheme-theoretically EXACTLY the rank-drop ideal of the sections of E=im(P): locally the augmented matrix splits into its complement identity and section map. If expected codimension p holds, TRUE Chow Thom–Porteous proves `[Sigma(P,V)]_CH=c_p^CH(E)`; the genuine affine-bundle Chow inverse returns the cycle to ORIGINAL X with canonical Betti class exactly q^-1 c_p(E).

### Stronger all-original-X CHOW completeness of concrete determinantal schemes

For EVERY actual z∈CH^p(X)_Q on ANY original smooth projective X, p≥1, rational Chern-character isomorphism on smooth X produces a pure-grade algebraic rational virtual K0 class with ch=z, and an actual integral signed bundle pair F+-F-=m class. On affine GST J, pullbacks are finitely generated projective modules with REGULAR idempotents P±. Choose generic constant section tuples; their actual Fitting schemes Sigma± have expected codimension p (or empty), with [Sigma±]=c_p(q*F±). Since full ch(F+)-ch(F-)=mz concentrated only in p, Newton identities in ACTUAL Chow yield

`z=(-1)^(p-1)/(m(p-1)!)*(q*)^-1([Sigma+]-[Sigma-])`.

This is a universal **PRESENTATION** of the EXISTING rational Chow ring as actual polynomial degeneracy cycles, not a claim that every rational Hodge class is already Chow. The source-only algebraic projector rank and incidence complexity can be increased arbitrarily without proving the missing algebraicity of a prescribed alpha.

### True ALL-X algebraic bundle -> explicit projector route

For arbitrary genuine algebraic vector bundle F on original X and very ample L, choose k sufficiently positive that Q=F^∨⊗L^k is globally generated and det Q ample. A finite algebraic quotient O_X^m↠Q has genuine kernel K and Grassmannian classifying map. Pull back the tautological Plücker incidence open of its kernel; since det(K)^∨=det(Q) is ample the resulting spatial fold is AFFINE. Its explicit projection P_K and complement I−P_K represent actual pulled-back K and Q. Then the exact ACTUAL original-X Chow source formula is `ch_p^CH(F)=Σ_(j=0)^p (kh)^(p-j)/(p-j)! * (-1)^j ch_j^CH(Q)`. This is a functorial source algebra over all original X, not just Grassmannian X.

### Actual direct nondivisor polynomial source

On G=Gr(2,5) choose fixed w0 in C5. The Plücker affine projector acts on w by `(u phi(w∧v)−v phi(w∧u))/phi(u∧v)`. Its actual projected section P(w0) vanishes precisely when `phi(w0∧u)=phi(w0∧v)=0` on the incidence open; these are TWO genuine independent polynomial conditions over each 2-plane S not containing w0, and no zero over S containing w0. Hence this closed scheme is smooth of pure codim2 with genuine CH class c2(q*S)=q*c2(S^∨). Under the original-X Chow inverse, the same class has actual geometric representative **Gr(2,ker a)⊂Gr(2,5)**, the zero locus of a nonzero tautological dual section. Together with two actual Plücker hyperplane divisors H1,H2, this constructs the prescribed rational Hodge target alpha=(2/5)h²−s₂ as a TRUE original-X rational algebraic cycle `Z_alpha=(2/5)(H1∩H2)−Gr(2,ker a)`. This is an exact scheme and Chow output, not just a period vector.

### Precise GST algebraic obstruction (typed audit)

Any rational target alpha gives a unique rational topological K0 class kappa_alpha with full ch alpha. Its class in `K_top(X)_Q/im(K_alg(X)_Q)` is precisely the rational algebraic Chern-character quotient `H^even(X,Q)/im(cl_X^can)`. The explicit Plücker/Fitting algebra can reproduce alpha from actual projective algebraic classifying maps iff this topological class vanishes in the quotient. This is **equivalent** to original-X rational Hodge algebraicity for the prescribed class, NOT its proof from Hodge type. It prevents accidentally plugging an Oka holomorphic or merely continuous topological classifying map into a polynomial-algebraic Plücker projector.

## Separate ALPHA-dependent new algebraic bridge via GRR/Todd

[Exact target-sensitive all-X support algebra](../derivations/GST_alpha_directed_todd_fitting_source_2026_10_23.tex), source commit `33253d3759e27d02676b6f164aa47d295993f004`. Given prescribed rational (p,p) Hodge alpha that has independent ACTUAL cohomological Gysin support from smooth projective Y_i of dim d-p+1, the rational polarized Hodge kernel-orthogonal lift `beta=(F|_ker(F)^perp)^-1 alpha` gives rational (1,1) beta_i on Y_i. Lefschetz (1,1)/GAGA constructs genuine algebraic line bundles M_i with c1(M_i)=m_i beta_i; set beta_i^CH=c1^CH(M_i)/m_i. Define Todd-corrected actual rational K0 `v_i=ch^-1(beta_i^CH f_i^*td(T_X)/td(T_Yi))`; derived pushforwards `v_X=Σf_i!v_i` satisfy by actual Chow GRR

`ch^CH(v_X)=Σ f_i* beta_i^CH` **PURE grade p**,

and the actual original-X Chow source `Z_alpha=Σf_i* beta_i^CH` has canonical Betti class alpha. On the affine GST J, clear rational denominators, represent v_X as signed actual algebraic projector bundles, choose generic constant sections, and convert to the explicit Fitting minors with the normalized signed-CH difference formula above. This is a COMPLETE **constructive algebraic** pipeline for the verified geometric-support sector in EVERY dimension and codimension, using the prescribed alpha from the FIRST step. The support hypothesis is **not** presumed for arbitrary Hodge alpha; its universal existence would already entail the target.

The codimension-one embedding i:D↪X has exact Todd ratio `td(N)=x/(1−exp(-x))=1+x/2+x²/12−x⁴/720+...`, x=c1(N); the pure codim2 identity `ch(i!ch^-1(beta td(N)))=i*beta` has no leftover higher Chern grades.

## Exact Wolfram computation and independence

[Source](../computations/gst_explicit_allrank_plucker_fitting_source_2026_10_23.wl), final fully rerun blob `0d6153273a84d38c29ad2ac8d754b29f030ed5d7`. Two implementation mistakes were detected and fixed before the successful runs: invalid `Mod` usage left a symbolic `Mod`, and an uppercase frame variable was reserved/undefined in the kernel. The repaired script produced:

- **36/36** exact rational projector idempotence, trace, image-on-frame and frame-change invariance cases for r=1..4, ambient m=r+1..r+3 (bounded by 7), three nontrivial frames per pair; no failures.
- Genuine Gr(2,5) Fitting ideal matrix rank checked on actual exact rational samples: rank=3 when P(w0)=0 and rank=4 when P(w0) is nonzero, exactly the expected augmented rank distinction.
- **10/10** exact formal Todd correction/cancellation checks, grades through 10; **8/8** arbitrary-lower-Chern-background signed Newton grade-p identities.
- **Five exact Schubert intersections** `{5,2,1,0,1/5}` for h6, s2 h4, s2² h², theta h4, theta²h².
- Target-source matrix from ACTUAL hyperplane and Fitting subvariety generators solves alpha=(2/5,-1) with EXACT coefficients (2/5,-1); dual obstruction detects the rank increase 1→2; full target Chow reconstruction verified.
- The unrestricted all-rank, Todd/Chow proofs come from the external established mathematical identities written in the LaTeX, not extrapolation from these finite checks.

## Audit verdict and exact remaining universal implication

- **PROVED subject to standard algebraic-geometric inputs:** universal all-rank Plücker projector and minor ideal, scheme-theoretic rank-drop equality, expected-codimension Thom–Porteous Chow source, all-X algebraic vector bundle presentation and pure Chow Fitting completeness, target-dependent support-sector Todd GRR source.
- **Verified in actual finite tests:** 36 projector cases, explicit Fitting rank distinction, exact original-X target Schubert witness, 10 Todd and 8 Newton computations.
- **Not derived and not asserted:** for EVERY arbitrary original X,p, rational Hodge alpha outside the known supported/algebraic sector, existence of a genuine algebraic classifying map/projective module whose Fitting scheme has prescribed alpha Betti periods. That is precisely the quotient obstruction displayed above and is NOT removed by finite affine-fold rank escalation.
- **No Lean modifications or GitHub Actions compilation in this research pass.** No fabricated kernel verification or completed Clay prize claim. The installed Mathbox skills guided research and proof audit; external theorem literature was not independently source-authenticated because user has requested repo-centric no-web mathematics.

**Takeaway:** This turn created actual polynomial ALGEBRA and genuine algebraic SUBVARIETIES, including the original-X target cycle in a nondivisor worked case, and linked the alpha-guided Gysin-support theorem to a fully explicit signed-Fitting Chow constructor. The problem of constructing sources for arbitrary unsupported primitive Hodge input remains separate and unproved.

## Final strengthened exact symbolic verification (same research turn)

The committed [Wolfram source](../computations/gst_explicit_allrank_plucker_fitting_source_2026_10_23.wl) was strengthened at source commit `6e6aa57c35499348cc24cef7e713e82cb0371e48` and rerun verbatim from **blob `b70b9b2ba029bb95f369449f074618a7d839661e`**. Beyond the earlier 36 rational projector checks, it now independently proves by exact *SYMBOLIC* polynomial simplification for arbitrary skew coefficients (a,b,c) and arbitrary frame coordinates (u1,u2,u3), (v1,v2,v3), on the genuine incidence open of Gr(2,3): `A²=Delta*A` for the explicit Plücker numerator A, `tr A=2Delta`, and `A u=Delta u, A v=Delta v`; **all three symbolic assertions returned TRUE**. All earlier checks still passed: projector 36/36, Fitting augmented matrix ranks {3,4}, Todd 10/10, Newton 8/8, Schubert five exact `{5,2,1,0,1/5}`, prescribed-alpha true Chow coefficient solver `{2/5,-1}` and dual rank jump. No Wolfram kernel failures or warnings in this final run.

Final verified branch HEAD after research index update: `69d3a66c5fe0c7559b492089bbd6786b0e412f86`. Structural file check: the main mathematical source contains 1,220 lines and six matched theorem/proof environments with balanced braces; the target-Gysin Todd source contains 107 lines, matched theorem/lemma/proof environments and balanced braces. This is a LaTeX structural check, **not** a pdflatex compilation and **not** a Lean kernel certificate. No Lean source changed in this turn.
