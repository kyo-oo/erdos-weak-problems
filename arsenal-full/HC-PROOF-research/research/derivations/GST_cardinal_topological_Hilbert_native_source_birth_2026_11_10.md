# GST original-X cardinal–topological Hilbert component source theorem

**Date:** 2026-11-10 (India time). **New independent research branch:** research/gpt6-gst-hilbert-component-source-birth-20261110. **Base:** research/gpt6-gst-cardinal-intent-reconstruction-20261110 at 6cc9b0a899c119f5fd44a57412479704ece728fd. **Source problem:** user's cardinal-connected GST algebraic-source, topology, N-cohomology, Hodge-star, curvature, navigation and original-X universal single-fold hypothesis. **Scope:** any fixed smooth projective complex connected X in its genuine algebraic geometry; not a separate product of examples.

## 1. Source-verified geometric input, and what is / isn't novel

Let X be smooth projective connected complex, d=dim X, choose a projective embedding by a very ample h, and fix 0<=p<=d. For every Hilbert polynomial P corresponding to top-dimensional subschemes of codimension p, Hilb^P(X) is projective finite type over C and represents flat families of actual closed subschemes. It has FINITELY many connected components. There are countably many rational-coefficient Hilbert polynomials, hence the union over all P of connected components is COUNTABLE.

**Standard geometric input (externally established):** the fundamental homology class of the top-dimensional cycle of a subscheme is constant on each connected component of a fixed Hilbert scheme. Source: M. Kapranov, *Chow quotients of Grassmannians I*, section 0.5.2–0.5.4, https://www.math.ucdavis.edu/~deloera/MISC/LA-BIBLIO/trunk/Kapranov1.pdf . Supporting Hilbert representability source: I. Coskun, *The Hilbert Scheme*, Theorem 1.1 https://homepages.math.uic.edu/~coskun/571.lec7.pdf . Algebraic equivalence background: J. Achter, S. Casalaina-Martin, C. Vial, *Parameter Spaces for Algebraic Equivalence*, IMRN 2019 https://academic.oup.com/imrn/article/2019/6/1863/4082263 . The topology/homology constancy is NOT new mathematics and is NOT formalized in the additive Lean module; the independent Lean module proves the exact conditional algebraic consequences.

Define I_{X,p} = disjoint union over all such P of complex Hilbert points (true algebraic subschemes with top-dimensional fundamental cycle of codimension p). Define C_{X,p} as disjoint union of their connected-component sets. Let component:I->C and choose one scheme Z_K for each nonempty K, with true Chow fundamental cycle z_K in CH^p(X)_Q. Put
  beta_K = cl_X(z_K) in W_p(X).
Source constancy makes beta_K INDEPENDENT of chosen Hilbert point within K.

Note important distinction: the cycles z_K themselves need NOT be rationally equivalent within one connected family. Only their canonical Betti/homology classes are constant. For example, two points on a positive-genus curve have the same point-class in cohomology but can differ in CH_0. Therefore no false native Chow equality is assumed.

## 2. Exact unconditional original-X cardinal component span theorem

Let A_p(X)=im[cl_X:CH^p(X)_Q -> W_p(X)] and r=dim_Q W_p(X).

**Theorem (component-native Hodge envelope):**
  A_p(X) = span_Q{beta_K | K in C_{X,p}}.

Proof:
(<=) Every beta_K comes from the explicitly given genuine cycle z_K, so it belongs to A_p(X).
(=>) Every rational Chow class is represented by a FINITE rational linear combination of fundamental cycles of integral codimension-p closed subvarieties. Every such integral subvariety is a complex point of Hilb^P(X) for some Hilbert polynomial P, in some component K. By standard Hilbert constancy its cohomology class equals beta_K. Thus the canonical image of every Chow class lies in the span of the component beta_K. No universal Hodge algebraicity assumption enters.

**Corollary:** There exist finitely many components K_1,...,K_s (s=dim A_p <=r) whose classes form a Q-basis of A_p(X). Because each basis class comes from a finite-type subscheme, one may choose a finite degree cutoff D(X,p) after which the Hodge span of all cycles of degree <=D equals A_p(X). This D is an EXISTENTIAL degree bound depending on X,p and the algebraic image; it is NOT known effectively and does NOT establish A_p=W_p.

**Cardinality conclusion:** The Hilbert PARAMETER set can be uncountable (often C-cardinal) while the indexed COHOMOLOGY component set is countable, and only s finite component classes are needed to span the TRUE algebraic Hodge image. This is a mathematically precise manifestation of the user's enormous cardinal/tau/N-cohomology input compressed to finite original-X Hodge data. It does not make the original Chow group CH^p countable.

## 3. A real connected-topology GST F-function constructs original-X Chow operators

Fix any ample h and q=deg(h^d)>0. Put z0=h^p and the genuine native rational readout
  lambda_h(Z)=(deg(Z*h^(d-p)))/q,
so lambda_h(z0)=1.

For EVERY genuine Hilbert component K, independently of target unknown Hodge alpha, construct

  Gamma_K = q^-1 pr_1^*(h^(d-p)) * pr_2^*(z_K)  in CH^d(X x X)_Q.

The genuine native action and canonical Betti action are
  N_K(Z) = lambda_h(Z) z_K,
  T_K(alpha) = Lambda_h(alpha) beta_K,
  Lambda_h(alpha)= [int_X alpha cup cl(h)^(d-p)]/q.

This gives the exact original-X result
  N_K(z0)=z_K,
  T_K(cl_X(z0))=beta_K,
  cl_X(N_K Z)=T_K(cl_X Z).

Two choices z_K,z'_K in the SAME component have the same beta_K; hence their Betti operators T_K are IDENTICAL on all W_p(X), while the underlying native Chow correspondences may differ by a homologically trivial cycle. Thus the F-function from CONNECTED TOPOLOGICAL COMPONENTS to BETTI ENDOMORPHISMS is well-defined independent of representative, and it admits a genuine Chow lift once a representative is chosen.

Therefore
  span_Q{ T_K(cl_X(z0)) : K in C_{X,p} } = A_p(X).
This is SOURCE COMPLETENESS at the true algebraic-image level on EVERY original X, derived without providing an unknown Hodge target preimage and without substituting an abstract GST matrix.

Exact composition and GST native curvature:
  T_K T_L = Lambda_h(beta_L) T_K
  [T_K,T_L] = Lambda_h(beta_L) T_K - Lambda_h(beta_K) T_L.
The same equations hold natively with lambda_h and Gamma_K; they follow from rank-one source push-pull. The collection of all source operators can make NONZERO curvature between components, but its image lies in A_p(X). This is consistent with the prior universal-source-saturation theorem in research/derivations/GST_connected_cardinal_native_source_full_rank_compiler_2026_11_10.md. The NEW contribution is the topologically canonical component organization and the exact navigation/no-new-rank criterion.

## 4. Exact native-source-birth topology criterion

Take ANY set of already explored connected components C_old and let
 L_old=span_Q{beta_K: K in C_old}.
If a new parameter y lies in ANY previously explored connected component K, then
  cl_X(z_y)=beta_K belongs to L_old.
Hence NO finite or infinite navigation sequence staying entirely within already explored connected components can increase the source rank.

Moving to a different connected component is NECESSARY for rank growth under ordinary flat Hilbert parameter navigation, but is NOT SUFFICIENT: distinct components may have the same homology class. The actual rank test is
  beta_K NOT IN L_old.

This is the precise place where the author's global GST noncommutative topology/navigation and Hodge detectors must do more than input-cardinality growth. Additional geometric operations (actual Chow push-pull/correspondences) can change cycle class and therefore lead to new components, but all resulting classes remain algebraic.

## 5. Exact single-universal-detector reformulation of the remaining Hodge gate

The component theorem converts the user's proposed Hodge-source covering requirement into the EXACT original-X criterion
  A_p(X)=W_p(X)
  iff
  Ann_{W_p(X)^*} {beta_K: K in C_{X,p}} = {0},
where
  Ann = {ell in Hom_Q(W_p,Q): forall K, ell(beta_K)=0}.

Linear-algebra proof: a proper rational subspace A of the finite-dimensional W has a nonzero rational functional ell vanishing on A; conversely if A=W only zero vanishes on all beta_K. The given Hilbert component classes span A exactly. This is an EQUIVALENT reformulation of Hodge in cardinal-topological GST language, NOT an unconditional proof that the annihilator vanishes.

In polarized terms choose a rational positive-definite Hodge-Riemann Q on W. If alpha has positive residual energy after projection to the component source span, then no amount of navigation within its already exhausted Hilbert-component classes can reduce it. A successful new GST source birth must produce some K with a positive Schur-complement norm, or a different true Chow geometric construction whose class equals the new component class.

**Geometric Hodge-star caution:** an abstract rational functional ell from a full cyclic orbit exists automatically. Requiring ell to come from actual complementary Chow cycle Y in CH^(d-p)(X) is an ADDITIONAL algebraic geometry condition. For a finite set of actual source classes beta_i and complementary classes gamma_j, define M_ij=int beta_i cup gamma_j. The ability to construct an algebraic dual detector basis requires det M!=0. Invertibility is not automatic for arbitrary partial algebraic source subspaces; it involves algebraic/homological versus numerical pairing issues. The earlier "step 03 follows from 02" is true only for an ABSTRACT rational detector, not necessarily for a specified genuine algebraic Chow detector.

## 6. Fully geometric model showing why topology matters: X=P1 x P1

Embed the Segre quadric by h=H1+H2. The Hilbert polynomial of a line in either ruling is m+1. The Hilbert scheme of lines has precisely TWO connected components, one parameterized by the first P1 and one by the second. Their rational cohomology classes are distinct H1,H2, with
  H1^2=H2^2=0, integral H1 H2 = 1.
Topological movement WITHIN one ruling has rank one no matter how many line parameter points are traversed. Choosing one genuine line from each ruling yields rank two. The genuine automorphism swapping the P1 factors supplies a genuine algebraic correspondence cycling H1->H2->H1, so the cyclic Krylov determinant and rational Hankel determinant are both 1.

The topology-labelled actual original-X operators have
  q=integral h^2=2,
  Lambda_h(aH1+bH2)=(a+b)/2,
  T_H1 = (1/2)[[1,1],[0,0]],
  T_H2 = (1/2)[[0,0],[1,1]],
  [T_H1,T_H2] = (1/4)[[1,1],[-1,-1]] !=0.
These are TRUE canonical Betti actions of TRUE Chow correspondences, not arbitrary symbolic matrix operators. They map the fixed algebraic seed h to H1 and H2 respectively.

**Exact Wolfram verification:** the committed source research/computations/GST_Hilbert_component_cardinal_topological_source_birth_20261110.wl, fetched AFTER commit and evaluated verbatim, returned
  sampleCount=64; allSampleRankPredictions=True;
  withinFirstComponentRank=1; withinSecondComponentRank=1;
  bothComponentsRank=2; factorSwapOrbitRank=2;
  swapHankelDet=1; actualChowComplementaryPairingRank=2;
  nativeOneSeedHitsRuling1=True; nativeOneSeedHitsRuling2=True;
  genuineChowComponentComposition=True; curvatureNonzero=True;
  allWithGeometricOperatorsPassed=True.
The 64 samples range over 0..7 chosen parameter points in each ruling. The all-parameter result follows from component constancy, NOT extrapolation.

**Formalization:** new additive GSTCardinalHilbertComponentSource.lean assumes the exact geometric constancy on topological components and proves the algebraic span equality, no-new-rank within a component, and freshness necessitates a nonexhausted component. The Hilbert-scheme constancy is independently sourced, not proved by Lean. Check its CI conclusion before labeling kernel-green.

## 7. Strict remaining original Hodge theorem

None of the above proves
  Ann {beta_K}=0
for EVERY original smooth projective complex X and p. This is the exact current condition equivalent to universal algebraicity, and producing all these beta_K as classes of ACTUAL cycles does NOT solve it: the beta_K generate the algebraic image by construction.

The proposed genuine GST research move is to show that its cross-index CM/N-cohomology/Hodge-star/curvature algebra, realized by independent ACTUAL Chow correspondences on a FIXED original X, has NO invariant Hodge subspace containing the ample seed except W. The prior original-X irreducibility criterion in GSTCardinalSimultaneousOriginalXCompiler.lean is Lean verified under that geometric hypothesis. To advance beyond restating it, one must construct and prove such irreducibility for the canonical original-X correspondence operators without assuming Hodge classes' algebraic lifts.

**Research result classification:** source-parametrization and rank-compression on original X PROVED using known Hilbert theorems; topologically canonical Betti source operators and composition PROVED by Chow push-pull; exact two-ruling arithmetic reproduced in Wolfram; arbitrary-X source full rank still open.

**No claim of priority:** Hilbert schemes and class constancy are classical results. Novelty of this particular GST interpretation or associated research framework has NOT been established by a historical novelty audit.
