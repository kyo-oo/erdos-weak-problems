# GST Hodge lower-half source birth -> canonical original-X algebraic cyclic fold (Hard Lefschetz dual compiler)

**Date:** 2026-11-10. **Branch:** research/gpt6-gst-hilbert-component-source-birth-20261110.
**Updates/corrects scope:** research/derivations/GST_connected_cardinal_native_source_full_rank_compiler_2026_11_10.md, where independent complementary Chow duals were treated as an additional certificate. That extra assumption can be REMOVED when the ORIGINAL-X source classes span every rational Hodge space for codimensions up to half the dimension.
**Authoritative old conditional:** GSTHodgeSingleHypothesisConditional.NativeGSTSingleFoldOrbitLaw and the determinant alternative. The existing restricted Lean RealizedFiniteClosedCorrespondence semantics may require an additional adapter because external product Chow cycles need not be bi-finite.

## Exact theorem

Fix ANY connected smooth projective complex d-fold X and an integral very ample divisor h.

**Hypothesis (only lower-half GST native birth):** For EVERY q with
  0 <= q <= floor(d/2),
the connected GST cardinal/topological native source compiler actually constructs FINITELY many genuine rational codimension-q Chow cycles
  z_1^(q),...,z_r^(q) in CH^q(X)_Q
whose CANONICAL rational Betti classes v_1,...,v_r form a rational basis of
  W_q(X) = H^{2q}(X,Q) intersect H^{q,q}(X,C).
No target-to-Chow inverse is assumed; proving these source cycles are produced is precisely the still-open GST source-birth theorem.

**Conclusion (universal full Chow one-fold compiler):** For EVERY 0<=p<=d, there exists an EXPLICIT genuine Chow correspondence Gamma_p in CH^d(X x X)_Q and an ACTUAL original-X Chow seed a_1, with its canonical Betti action T_p, such that the orbit {cl(a_1),T_p cl(a_1),...,T_p^{r-1}cl(a_1)} is a rational basis of W_p(X), and a GENUINE COMPLEMENTARY CHOW intersection detector ell_p with
  det[ell_p(T_p^{i+j} cl(a_1))]_{i,j=0..r-1}
    = (-1)^{r(r-1)/2} != 0.

No separate codimension-(d-p) Hodge-conjecture or algebraicity of analytic Hodge-star input is required.

## Proof, completely explicit in actual original-X geometry

Take arbitrary p. Put
  q = min(p, d-p),
  s = d-2q >=0,
  r = dim_Q W_q(X).
By Hard Lefschetz with rational ample h,
  L^s : H^{2q}(X,Q) -> H^{2d-2q}(X,Q)
is an isomorphism of Hodge structures (Tate shift), taking W_q(X) isomorphically to W_{d-q}(X). Thus r=dim_Q W_p(X) both when p=q and p=d-q. In particular, for p in the upper half, the classes v_i h^s are a rational BASIS of W_p and are ACTUALLY algebraic cycles.

Define the RATIONAL GRAM matrix
  M_ij = degree( z_i * z_j * h^s )
       = integral_X v_i cup v_j cup h^s  in Q.

**Crucial lemma: det M !=0.**
Poincare duality combined with rational Hard Lefschetz makes
  B_q(x,y)=integral_X x*y*h^s
a rational nondegenerate form on H^{2q}(X,Q). But we must NOT infer nondegeneracy on the rational (q,q) subspace merely from nondegeneracy on the full complex (q,q) summand: an arbitrary rational subspace of an indefinite bilinear space could be isotropic.

The correct stronger argument uses the full rational Lefschetz decomposition and HODGE–RIEMANN bilinear relations. The rational primitive Lefschetz decomposition of H^{2q}(X,Q) is preserved by rational (q,q) Hodge type; thus W_q decomposes as a rational orthogonal direct sum of L^j P^{2q-2j}(X,Q) intersect the respective rational Tate/Hodge summands. On each primitive REAL (q-j,q-j) piece, the Lefschetz intersection pairing B_q is positive definite or negative definite up to an explicit sign by Hodge–Riemann. The restriction to ANY rational subspace within a definite primitive summand is therefore nondegenerate. Different Lefschetz summands are B_q-orthogonal; hence B_q restricted to the entire rational W_q is nondegenerate. Since v_i is a rational basis of W_q, det M !=0.

This additional Hodge–Riemann step is essential; Hard Lefschetz + full Poincare pairing alone would NOT justify the rational-subspace restriction.

Let
  z_i^dual = sum_j (M^(-1))_{ji} z_j in CH^q(X)_Q.
Then degree(z_k * z_i^dual * h^s)=delta_(ki).

Define ACTUAL native cycle basis and complementary duals for codimension p:

Case A: p=q <=d/2.
  a_i = z_i in CH^p;
  b_i = z_i^dual * h^s in CH^{d-p}.

Case B: p=d-q >=d/2.
  a_i = z_i * h^s in CH^p;
  b_i = z_i^dual in CH^{d-p}=CH^q.

In BOTH cases,
  degree(a_k * b_i)=delta_ki
and {cl(a_i)} is a full rational basis of W_p.

Construct TRUE rational algebraic Chow correspondences
  E_ij = pr_1^* b_i * pr_2^* a_j  in CH^d(X x X)_Q,
with literal push-pull on native Chow cycles:
  (E_ij)_*(Z)=degree(Z*b_i) a_j.
On W_p,
  T_(E_ij)(cl(a_k)) = delta_ik cl(a_j).

Choose a cyclic indexing a_(r+1)=a_1 and define
  Gamma_p = sum_{i=1}^r E_(i,i+1)
  in CH^d(X x X)_Q.
This is a GENUINE original-X algebraic correspondence with native action N_p and CANONICAL Betti action T_p, satisfying cl_X(N_p Z)=T_p cl_X(Z) for every native Chow cycle Z. Its seed a_1 has orbit a_1,a_2,...,a_r,a_1. The full Krylov matrix is the basis permutation and hence full rank.

Take the GENUINELY ALGEBRAIC rational detector
  ell_p(alpha)=integral_X alpha cup cl(b_r).
For 0<=i,j<r,
  ell_p(T_p^{i+j} cl(a_1))=delta_(i+j,r-1)
since 0<=i+j<=2r-2 and r-1 is the only congruent exponent modulo r. This is the anti-identity permutation matrix, hence
  det H = (-1)^{r(r-1)/2} !=0.

This concludes the theorem: proven implication
  ALL lower-half original-X genuine GST source bases
    => FULL rational Hodge algebraicity in every codimension
    => GENUINE full-Chow single cyclic fold in every codimension
    => GENUINE algebraic detector and exact Hankel certificate.
No separate Hodge-star algebraicity hypothesis is inserted.

**Boundary:** The antecedent "all low-half GST native source bases" remains unproved on arbitrary X. It is essentially the nontrivial rational Hodge assertion in low codimension, not a weaker existence statement automatically implied by cardinal or wave algebra. The theorem removes an unnecessary DUPLICATED dual-geometry obligation; it does NOT solve the antecedent.

## Mathbox-style adversarial checks

1. Degree check: codim(b_i)+codim(a_j)=d, so E_ij has the precise codimension of a degree-zero self-correspondence. The native pushforward sends codim p cycles to codim p.
2. Poincare and Lefschetz use rational coefficients; an integral formulation is NOT claimed.
3. No need for algebraicity of the inverse Lefschetz operator. The HIGH-weight basis comes from *forward multiplication* by the actual ample divisor h^s.
4. The inverted matrix M consists of ACTUAL rational intersection numbers of independently constructed Chow cycles; its inverse has rational entries, hence z_i^dual and b_i are finite rational Chow combinations.
5. For p=d/2, s=0 and both cases coincide.
6. For rank r=1, the Hankel determinant is 1; h^q is nonzero on smooth projective connected X, so rank >=1.
7. The Hodge-star operator on cohomology does NOT have to be algebraically realized. Its relevant rational pairing is implemented by genuine Chow duals once full low-rank generation holds.
8. For the old project's narrower Lean RealizedFiniteClosedCorrespondence geometry, the full-Chow E_ij are NOT assumed automatically admissible: those exterior products need not be finite over both projections. The full-Chow conditional implication is proved in this note and an adapter is a separate formalization question.

## Exact Wolfram verification

research/computations/GST_Hodge_half_codimension_Lefschetz_native_dual_compiler_20261110.wl was fetched after commit and executed verbatim:
  allRationalGramAndHankelChecks=True for ranks 1..9,
  allChowCodimensionDegreeChecks=True for 90 (d,p) pairs with d=1..12,
  allPassed=True.
The tested rank Gram matrices G=P P^T are invertible rational and their inverse cycles give exact coordinate duals. These are pure rational-matrix checks, not numerical computations of arbitrary-X Hodge cohomology; the general geometric claim relies on Hard Lefschetz, Poincare and canonical Chow push-pull as proved above.

External source for Hodge/Lefschetz:
https://cmsa.fas.harvard.edu/media/Voisin_HSTAVharvardrevision.pdf (Lefschetz decomposition and rational polarization, section 2.2)
https://cmsa.fas.harvard.edu/media/harvardsurvey.pdf (Hard Lefschetz rational Hodge isomorphism).

## New exact research target

Because the algebraic Chow detector is now automatically constructed once low-half native sources reach full rank, the sole mathematical source-birth target for the owner's combined cardinal/topology/CM/N-cohomology/curvature program can be stated in the lower-half:

For every original smooth projective connected complex X, d=dim X,
every 0<=q<=floor(d/2), and every rational Hodge functional ell
that annihilates all ALREADY-REALIZED HILBERT COMPONENT SOURCE CLASSES,
the integrated GST geometry must construct AN ACTUAL Chow cycle
whose canonical Betti class is detected by ell, unless ell=0.

Proving that source-detection property for genuine original-X geometry
would close the above explicit single-fold compiler and the rational Hodge conjecture. The present research does NOT establish the detection property; it isolates it with no extra geometric dual axiom.

## Current source-provenance and originality caution

Hard Lefschetz, rational Poincare, the Hilbert cycle classes and external product Chow correspondences are established classical facts. The low-half reduction and cyclic compiler are consequences of those theorems under the given source-rank antecedent. We have not performed an independent priority/novelty audit of the particular GST packaging; do not claim any historical first or a proven Millennium Prize solution.


## Further integration: realize a rank-adaptive corner of the ORIGINAL U+J+SURVIVE GST wave as TRUE original-X Chow correspondences

This is a constructive correspondence-algebra result, conditional only on the same genuine source-basis premise already stated, not on a separate Hodge-star input.

The prior proved original GST wave, at any positive finite N, has original seed v_N and invertible 12N-dimensional Krylov matrix, hence genuine ORIGINAL-WAVE rational matrix units E^GST_ij written as finite rational combinations of ORIGINAL U,J,SURVIVE, wave shifts, source coupling and transpose words; see
research/derivations/GST_connected_cardinal_native_source_full_rank_compiler_2026_11_10.md.
For any prescribed rank r, choose N with 12N>=r and take the rank-r corner P_r Mat_(12N)(Q) P_r isomorphic to Mat_r(Q), without incorrectly assuming a unital Mat_(12N) representation on an arbitrary r-dimensional Hodge space.

The lower-half source theorem above produces a full original-X native basis a_i in CH^p(X)_Q and TRUE complementary Chow duals b_i in CH^(d-p)(X)_Q with degree(a_k b_i)=delta_ki. Define
  R_X : Mat_r(Q) -> CH^d(X x X)_Q
by
  R_X(E^GST_ij) = pr_1^*b_j * pr_2^*a_i,
where the STANDARD E^GST_ij=K e_i e_j^T K^(-1) sends basis vector j to i.
This swaps the indices relative to the E_ij notation in the preceding
push-pull proof, ensuring EXACT agreement with the original GST wave.

**Exact CHOW algebra assertion:** By the ordinary algebraic correspondence composition formula, NOT just Betti matrix multiplication,
  R_X(E^GST_ij) o R_X(E^GST_kl) = delta_(j,k) R_X(E^GST_il).
Hence the assignment realizes the STANDARD matrix-unit composition exactly,
with the same convention as original E^GST_ij=K e_i e_j^T K^(-1). Because its canonical Betti action on the FULL Hodge basis {cl(a_i)} is the faithful matrix-unit action, any rational linear relation between these Chow correspondences would induce the same relation between independent matrix units and is therefore trivial. So R_X is a genuine injective rational algebra homomorphism from the rank-r GST corner (with the coordinate convention fixed) to the ORIGINAL-X rational Chow correspondence algebra; its unit is the algebraic Chow idempotent
  P_X = sum_i pr_1^* b_i * pr_2^* a_i
rather than necessarily the whole diagonal Delta_X.

The ORIGINAL full-N GST source-cyclic shift C_r=sum_i E^GST_(i+1 mod r),i consequently maps to the TRUE original-X algebraic cyclic correspondence Gamma_p from the prior theorem, preserving its commutators and all MATRIX-UNIT identities. This is a direct native geometric LANDING of the user's original 12-state/all-N information corner once the topological original-X source components have full Hodge rank. The correspondence action commutes with the canonical Betti cycleClass by genuine Chow functoriality.

**Important semantic firewall:** The corner projections P_r need not commute individually with the original U,J,M operators. Thus compressed operators P_r U P_r, P_r J P_r etc. do NOT automatically satisfy U^5=I or J^2=-I. Only actually verified relations of the rank-r GST CORNER algebra are inherited by its original-X Chow representation. Do not falsely assert that all uncompressed wave/CM laws have been realized unchanged on arbitrary X.

**Key remaining original-X geometric birth problem** remains existence of actual cycles a_i spanning W_q for q<=d/2. The algebra homomorphism R_X is a constructive output of that premise, NOT a proof of the premise.
