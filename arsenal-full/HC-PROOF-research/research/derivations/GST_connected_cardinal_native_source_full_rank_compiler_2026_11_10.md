# Connected cardinal GST: native-source saturation, rank-adaptive folds, and geometric Hodge-star compiler

**Date:** 2026-11-10. **Authoritative original hypothesis:** GSTHodgeSingleHypothesisConditional.NativeGSTSingleFoldOrbitLaw, with canonical original-X Betti realization still required. **Development branch:** research/gpt6-gst-cardinal-intent-reconstruction-20261110.

This derivation follows the author's three original cardinal/topology images as ONE simultaneous cross-world GST source-producing system, not a detached collection of test varieties. The proof modules and test scripts below are additive. No claim of an unconditional Hodge-conjecture proof is made.

## 1. Precise original-X target and three separate mathematical carriers

Let X be any smooth CONNECTED projective complex d-fold, 0<=p<=d; h is an ample actual divisor. Let

\[
W=W_p(X)=H^{2p}(X,\mathbb Q)\cap H^{p,p}(X,\mathbb C),\quad
A_X=\operatorname{im}\bigl(\operatorname{cl}_X:\operatorname{CH}^{p}(X)_{\mathbb Q}\to W\bigr),\quad r=\dim_{\mathbb Q}W.
\]

The author proposes an arbitrary-cardinal index family of geometrical/topological/CM/N-cohomology/curvature sources, with cross-world navigation and possible limit-stage operations. The actual Hodge result is on a FIXED original X. The distinction is:

- GLOBAL GST information algebra: arbitrary-cardinal indices and wave signals;
- ACTUAL original-X Chow algebra: finite rational combinations of algebraic subvarieties, and genuine codimension-d correspondences on X times X;
- CANONICAL Betti/Hodge target W: finite dimensional over Q at fixed X,p.

An all-cardinal signal input does not become an infinite Chow sum automatically. The following theorem is a genuine new universal geometric statement, not a wave-model analogy.

## 2. Theorem: the full cardinal-indexed Chow operator family is cyclic from one original-X seed

Write q=degree(h^d)>0, z0=h^p and

\[
\lambda_h(Z)=q^{-1}\deg(Z\cdot h^{d-p}),\quad\lambda_h(z_0)=1.
\]

For EVERY actual rational codimension-p cycle Z, construct

\[
\boxed{\Gamma_Z=q^{-1}\operatorname{pr}_1^*(h^{d-p})\cdot\operatorname{pr}_2^*Z
\in\operatorname{CH}^{d}(X\times X)_{\mathbb Q}.}
\tag{1}
\]

**Unconditional theorem (every X,p):** the literal Chow push-pull formula gives

\[
\boxed{(\Gamma_Z)_*(A)=\lambda_h(A)\,Z,\quad(\Gamma_Z)_*(z_0)=Z.}
\tag{2}
\]

The canonical Betti class commutes with the action for every native cycle A because the canonical cycle-class map respects pullback, proper pushforward and intersection product. Therefore

\[
\boxed{\{T_\Gamma\operatorname{cl}_X(z_0):
\Gamma\in\operatorname{CH}^{d}(X\times X)_{\mathbb Q}\}=A_X.}
\tag{3}
\]

**Proof:** projection formula along pr2 gives equation (2); for any Gamma the output is already an actual native cycle, proving subset in A_X. Conversely, given any actual Z, equation (2) realizes cl(Z) as T_Gamma_Z(cl(z0)). Equality follows. The argument does NOT assume algebraicity of unknown Hodge classes. Thus CH^p(X)_Q is a CYCLIC MODULE under its entire genuine Chow correspondence algebra, but the Hodge space W is cyclic under that algebra precisely when A_X=W.

This is a precise mathematical incarnation of the author's cardinal-input intuition: one algebraic seed reaches EVERY already-algebraic direction through a possibly enormous family of REAL geometric operations, not through a numeric aleph substituted into N+N^2.

### Important common-readout obstruction

For any actual Z,Y, the correspondences obey even as Chow compositions

\[
\Gamma_Z\circ\Gamma_Y=\lambda_h(Y)\Gamma_Z,\qquad
[\Gamma_Z,\Gamma_Y]=\lambda_h(Y)\Gamma_Z-\lambda_h(Z)\Gamma_Y.
\tag{4}
\]

Thus every FINITE rational combination of these source operators is another Gamma_Z. A single fixed fold of the form F=a*Id+Gamma_Z maps ANY seed A into the two-dimensional subspace span_Q{A,Z}, which remains invariant under F. Consequently

\[
\boxed{\operatorname{rank}[A,FA,F^2A,\ldots]\le 2.}
\tag{5}
\]

This exact bound is independent of the cardinality of the family used to select Z. Therefore the cardinal proposal needs MORE than many source cycles: it needs geometrically independent readout functionals / Hodge-star duals to compile one single full-rank cyclic fold.

The exact abstract normalized-source saturation and the rank-two orbit firewall are in the new Lean module GSTUniversalChowSourceSaturation.lean; the actual Chow external-product formula (1) is the independent geometric proof above, not encoded in that linear-algebra module.

## 3. The original X dual geometric compiler: where GST Hodge star must act

Suppose the connected GST construction has actually produced native cycles Z_1,...,Z_s in CH^p(X)_Q whose canonical Betti classes v_i are independent. Suppose also it has produced genuine complementary-degree native cycles Y_1,...,Y_s in CH^(d-p)(X)_Q, with the ACTUAL rational intersection matrix

\[
M_{ij}=\deg(Z_i\cdot Y_j)\in\mathbb Q,\qquad\det M\ne0.
\tag{6}
\]

This is a new independent *dual geometric gate*. Merely having nonzero analytic Hodge-star pairings does not prove the corresponding dual cycles are algebraic. The rational Hodge-Riemann polarization can test independence, but its readout is not automatically a genuine Chow correspondence.

Define the normalized algebraic duals

\[
\check Y_i=\sum_k(M^{-1})_{ki}Y_k,\qquad
\int_XZ_j\check Y_i=\delta_{ji}.
\]

Now define genuine original-X correspondences

\[
E_{ij}=\operatorname{pr}_1^*\check Y_i\cdot\operatorname{pr}_2^*Z_j
\in\operatorname{CH}^{d}(X\times X)_{\mathbb Q}.
\tag{7}
\]

Their Betti actions on L=span_Q{v_1,...,v_s} satisfy the full matrix-unit relations E_ij(v_k)=delta_(ik)v_j. Choosing a cyclic order, the actual geometric fold

\[
\boxed{\Gamma_{\mathrm{cyc},L}=\sum_{i=1}^{s}E_{i,i+1\bmod s}}
\tag{8}
\]

has orbit v_1,v_2,...,v_s under the genuine seed Z_1. The actual rational intersection detector ell(alpha)=int_X alpha cup cl(check Y_s) gives exact anti-identity moments:

\[
\boxed{H_{ab}=\ell(T^{a+b}v_1)=\delta_{a+b,s-1},\quad
\det H=(-1)^{s(s-1)/2}\ne0,\quad 0\le a,b<s.}
\tag{9}
\]

**Proof:** the Chow push-pull action gives E_ij(v_k)=delta_(ik)v_j. The cyclic sum rotates sources, the normalized dual reads exactly the last source, and the moment matrix is the reversal permutation. All correspondences are genuine actual cycles, not supplied abstract operators. No unknown target Hodge alpha-cycle inverse is provided.

**Scope:** This construction works on ANY original X as soon as actual primal+dual cycles with det M !=0 are independently available. It proves full GST single-fold for (X,p) only when s equals the WHOLE rational Hodge rank r. In general, finding all s=r cycles is the universal Hodge algebraicity challenge; finding the complementary algebraic duals is an additional serious geometric requirement, not an automatic consequence of formal Hodge star. Its absence is exactly where GST Hodge-star and cardinal-source-birth work must focus.

## 4. Rank-adaptive original GST U+J+M wave, including true native word formulas

The owner's original 12-state information wave is T0=U+J+SURVIVE, with its original seed v0 and nonzero Krylov determinant

\[
\det[v_0,T_0v_0,\ldots,T_0^{11}v_0]=-1149656584000.
\]

The earlier full-N GST theorem gives for every positive integer N a cyclic full original wave T_N and seed v_N on V_N=Q^(12N), with m=12N and invertible Krylov matrix K=[v_N,...,T_N^(m-1)v_N]. The original transpose laws U^T=U^4, J^T=-J, M^T=M and symmetric channel shifts ensure that T_N^T belongs to the algebra of the ORIGINAL GST operators.

Define G=K^T K and rank-one source P=v_N v_N^T. For any 0<=i,j<m,

\[
\boxed{
E^{GST}_{ij}
=K e_i e_j^\mathsf T K^{-1}
=\sum_{k=0}^{m-1}(G^{-1})_{jk} T_N^i P(T_N^\mathsf T)^k.
}
\tag{10}
\]

**Proof:** since K^(-1)=G^(-1)K^T, each row of K^(-1) is a rational combination of the transpose orbit vectors, while T_N^i P (T_N^T)^k=(T_N^i v_N)(T_N^k v_N)^T. Therefore each E^GST_ij is a FINITE rational combination of actual ORIGINAL GST information-operator words, not a convenient unrelated matrix unit.

For every 1<=s<=12N, define

\[
P_s=\sum_{i=0}^{s-1}E^{GST}_{ii},\qquad
C_s=\sum_{i=0}^{s-1}E^{GST}_{(i+1)\bmod s,i}.
\tag{11}
\]

By exact matrix-unit relations,

\[
\boxed{P_s^2=P_s,\ \operatorname{rank}P_s=s,\ C_s^s=P_s,\quad
P_sC_s=C_sP_s=C_s.}
\tag{12}
\]

The original GST seed has full cyclic orbit rank s INSIDE P_s V_N. With exact rational detector ell_s=e_(s-1)^T K^(-1),

\[
\boxed{\det[\ell_s(C_s^{i+j}v_N)]_{0\le i,j<s}
=(-1)^{s(s-1)/2}\ne0.}
\tag{13}
\]

These are ALL-N mathematical theorems from invertibility of K, not extrapolated finite tests. The exact original 12-cell Wolfram source GST_original_wave_all_rank_cardinal_corner_20261110.wl re-fetched and executed verbatim returned allPassed=True for every rank s=1,...,12, including U^5, J^2, the nontrivial Gram-inverse native-word formula and all signed Hankel determinants.

### Why the corner is necessary, not decorative

A nonzero *unital* rational representation of the full matrix algebra Mat_m(Q) on W forces m to divide dim_Q W. Proof: its m diagonal matrix-unit projectors split W into m isomorphic subspaces because off-diagonal units intertwine them. Thus dim W=m*k for k>=1. Arbitrary Hodge rank r need not be divisible by 12N, so the complete GST matrix algebra CANNOT simply be transferred unchanged as a unital algebra to every W.

The rank-s CORNER algebra P_s Mat_m(Q) P_s is canonically Mat_s(Q), fixing this rank obstacle at the information-space level. It remains necessary to prove a real geometric Chow realization of its operators on the original X. A purely chosen linear isomorphism between P_sV and W supplies no new native cycle algebraicity.

## 5. New sufficient geometric original-X criterion requiring operators rather than target cycles

For a given original (X,p), r=dim_Q W>0. Suppose we construct r^2 **genuine algebraic original-X self-correspondences** gamma_ij of codimension d whose Betti restrictions to W satisfy

\[
T_{ij}T_{k\ell}=\delta_{jk}T_{i\ell},\qquad\sum_iT_{ii}=I_W.
\tag{14}
\]

**Theorem (geometric GST matrix-unit Hodge criterion):** These geometry-only operator identities imply A_X=W, hence the rational Hodge conjecture for this (X,p).

**Proof:** the operators make W an r-dimensional nonzero unital module for Mat_r(Q). The matrix-unit decomposition shows it is one copy of the standard simple module, so the operators span End_Q(W). The algebraic image A_X is preserved by every actual Chow correspondence and contains nonzero h^p. The only nonzero End(W)-invariant subspace is all W. Therefore A_X=W. No algebraic inverse of an unknown alpha was supplied. The theorem is a conditional REDUCTION; the universal existence of gamma_ij on actual X is not shown by the original information-space corner.

This route is useful because it offers an alternative to constructing all unknown Hodge cycles one by one: derive geometric algebraic correspondences with the exact GST operator relations and use irreducibility to force full original-X algebraicity.

## 6. Arbitrary-cardinal connected source words, topology and operator certificates

The existing repo GSTGraphV2SelfExpandingCosmology.lean already gives an arbitrary-arity certified world-birth interface and theorem arbitrary_world_birth_constructs_fresh_native_direction, requiring a nonzero independent source readout in the target. The new additive GSTCardinalConnectedNavigation.lean composes native/Betti squares along any finite cross-world route and is LEAN GREEN. It does not assert that arbitrary topological incidence is automatically a Chow correspondence.

The new GSTCardinalSimultaneousOriginalXCompiler.lean is the promised SIMULTANEOUS, same-original-X cardinal interface. It accepts an arbitrary index type I of actual Chow operator pairs (N_i,T_i) satisfying the canonical class square, one actual seed Z0, and proves:
- every arbitrary finite operator word produces an actual native source and matches its Betti word;
- every finite simultaneous rational packet of arbitrary-cardinal indexed operators preserves the canonical class square;
- true noncommutative native curvature has exact corresponding Betti commutator;
- a nonzero geometric detector on a CONSTRUCTED word-cycle or curvature-cycle, vanishing on old algebraic sources, proves that cycle is a genuinely fresh algebraic direction relative to the old frame.
The exact CIs are recorded in the research record.

The all-index cardinal structure DOES NOT prove the independent residual detector is nonzero universally. That is the single true source-birth step needed to complete the Hodge hypothesis. It must be established geometrically on arbitrary X, without a previously chosen unknown target preimage.

## 7. Exact evidence and remaining target

**Proved by original-X intersection geometry:** every smooth connected projective X has one ample algebraic seed generating its WHOLE native Chow module under the cardinal family of true Chow self-correspondences; the single-common-readout fold has rank <=2; an actual paired frame with invertible intersection matrix produces one actual cyclic Chow fold with exact nonzero Hankel determinant.

**Proved inside original GST information algebra:** rank-adaptive idempotent and cyclic fold for all 1<=s<=12N from the existing all-N Krylov theorem. Wolfram exact 12-cell checks all passed, including reconstruction as FINITE original GST operator words.

**Lean kernel formalized:** connected finite cross-world composition, simultaneous native words/packets/curvature/fresh-source detector; universal native source evaluation and common-readout obstruction are separately being kernel checked.

**Unproved, decisive geometric claim:** the upgraded CARDINAL/TOPLOGICAL/HOLOGE-STAR/CM/N-cohomology/GST curvature mechanism can universally construct original-X actual Chow operators that satisfy the rank-s independent-dual gate (6) with s=r, or actual original-X matrix units (14), WITHOUT already assuming the Hodge conjecture. This is the precise remaining antecedent. The above proofs are substantial conditional and unconditional structural results, not an unconditional solution to Hodge.
