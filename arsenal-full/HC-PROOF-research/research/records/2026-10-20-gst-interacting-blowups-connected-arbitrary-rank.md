# GST interacting blowup births: unit feedback and complete connected primitive frames

**Claim family:** `GST-MIXED-EXCEPTIONAL-BIRTHS-20261020`.  
**Research base:** `55cc6f7f943926d38db27875fba2853781681b97`, continuing the original quadric blowup world.  
**Assessment:** 20 October 2026; mathematical derivation and adversarial self-review, Python exact arithmetic, independent Wolfram, and GitHub Lean. No public literature search or subagents used.  
**Target remains:** the [full arbitrary-original-X canonical rational Hodge statement](../ACTIVE_HODGE_PROOF_PLAN.md). This record constructs the combined GST mechanism below; it does not claim that target was reached.

## Scope correction and actual change of mathematical input

The previous continuation concentrated on CM direct-object obstructions and the vanishing of the first blowup's exceptional pushforward. That did not execute the requested combination of blowup families with GST's full birth, incidence, intersection, native Gysin, perfect K0, Gram, and correspondence machinery.

The earlier identity `pi_*(E^k Z)=0` remains valid for its stated single-birth words. Here a **second actual center** creates an exceptional divisor F which is not restricted to those words. Its mixed feedback is nonzero. This is a new constructor addressing the earlier restriction, not a retraction of that correct single-birth calculation.

| Construction | Quantifiers | New exact output |
|---|---|---|
| Two interacting births | Every integer m>=1 | Mixed top push -[point], perfect-source Euler -1, unit primitive readout |
| Complete second world | Every m>=1 geometrically; explicit Lean five-coordinate proof for m=1 | Primitive dimension 2 and genuine algebraic Gram-dual correspondences |
| Parallel second births on one connected fourfold | Every finite integer r>=1 | Complete primitive rank r+1, explicit source basis and positive Gram inverse |
| External products | Every finite arity | Primitive source rank 2^arity and corresponding algebraic matrix units |

## 1. First world and the exact sign convention

Fix m>=1 and set p=m+1. Let B=P^(2p), Y=Q^(2m) contained in a hyperplane, and pi:X=Bl_Y(B)->B. Then N_(Y/B)=O(1)+O(2). Write j:E->X and q:E->Y. Use the **lines convention** on P(N): xi=c1(O_E(1)), j^*E=-xi,

\[
 \xi^2+3h\xi+2h^2=0,\qquad q_*\xi=1,\quad q_*\xi^2=-3h.
\]

For the actual ruling m-planes A,B on Y put eta=(-1)^m,

\[
 a=(1+\eta)/2,\quad b=(1-\eta)/2,\quad
 A^2=B^2=a,\quad AB=b.
\]

The middle primitive difference delta=A-B has h delta=0 and delta^2=2 eta. Define genuine Chow cycles C_A=j_*q^*A, C_B=j_*q^*B and Z=C_A-C_B. The complete middle basis of X is (H^p,C_A,C_B), with

\[
 G_X=\begin{pmatrix}1&0&0\\0&-a&-b\\0&-b&-a\end{pmatrix},
 \quad \det G_X=\eta,\quad Z^2=-2\eta,\quad \pi_*Z=0.
\]

For L=kH-E, cup into the complete next-degree basis (H^(p+1),D), D=j_*q^*(hA), is

\[
 M_k=\begin{pmatrix}k&1&1\\-2&k-3&k-3\end{pmatrix}.
\]

Its two-column minor is (k-1)(k-2); hence for k>=3 the **whole** primitive kernel is QZ. This is derived from the actual cup equations, not a source-span premise.

**Concrete polarization.** I_Y(2) is globally generated. Its blowup embedding into B times projective space uses H and Q=2H-E. Thus L=H+Q=3H-E is very ample, fixing k=3 uniformly.

## 2. A genuine interacting center returns a unit

Let S_A=q^(-1)(A). It is a smooth P^1 bundle over P^m, is an actual subvariety of X with class C_A and codimension p. Blow it up:

\[
 \rho:\widehat X=\operatorname{Bl}_{S_A}X\longrightarrow X,
 \quad F=\text{new exceptional divisor}.
\]

The proper blowup pushforward, with its correct codimension sign, gives

\[
 \rho_*F^p=(-1)^{p-1}[S_A]=\eta C_A.
\]

Consequently the genuine projection formula yields

\[
 \boxed{\deg(\pi\rho)_*(\rho^*Z\,F^p)
    =\eta\,(Z\cdot C_A)=\eta(-\eta)=-1.}
\]

The normalized readout ell(u)=-deg(rho^*u F^p)=-eta(u.C_A) satisfies ell(Z)=1. In old coordinates it is u_A for m even, and -u_B for m odd. It is integral, and needs no division by the primitive norm 2. The actual correspondence

\[
 \Pi=(-\eta C_A)\times Z\in CH^{2p}(X\times X)_\mathbb Q
\]

acts as u->ell(u)Z, is idempotent, and recovers every primitive target on X. This rank-one projector is not asserted to be the orthogonal Lefschetz projector on the entire old middle space.

**Perfect K0 and Todd.** Both S_A and S_B are smooth lci codimension-p subvarieties in smooth X, so F_Z=[O_(S_A)]-[O_(S_B)] is a genuine perfect K0 class, ch_<p(F_Z)=0 and ch_p(F_Z)=Z. Since O_F is a perfect Cartier sheaf,

\[
 \mathcal G_m=L\rho^*\mathcal F_Z\otimes^L
                  \mathcal O_F^{\otimes^L p}
\]

is a genuine virtual perfect source. The character ch(O_F)=1-exp(-F) starts in degree one. Thus ch_<2p(G_m)=0, ch_(2p)(G_m)=rho^*Z F^p, and

\[
 \chi(\mathcal G_m)=\int_{\widehat X}\operatorname{ch}(\mathcal G_m)
                 \operatorname{td}(T\widehat X)=-1.
\]

Todd is **included**: only its constant term contributes because the source character starts in top degree. This does not generalize to dropping Todd for an arbitrary non-pure source.

## 3. The entire second world, in every dimension

On S_A put h=c1(O_(P^m)(1)); then

\[
 CH^*(S_A)=\mathbb Z[h,\xi]/(h^p,\xi^2+3h\xi+2h^2),
 \qquad \int_{S_A}\xi h^{p-1}=1.
\]

The exact normal sequence gives

\[
 c(N_{S_A/X})=(1-\xi)\frac{(1+h)^p}{1+2h}.
\]

For the second exceptional j' and q' write e_i(v)=j'_*(xi'^(i-1) q'^*v), 1<=i<=p-1. The complete middle basis consists of the three old pulls and e_i(CH^(p-i)(S_A)); the next degree consists of two old pulls and e_i(CH^(p+1-i)(S_A)). Their ranks are 2p+1 and 2p-1.

**No unspecified large polarization.** The ideal of S_A is generated by O(-E) and the pullbacks of the linear ideal of A. Twisting by 2L gives the globally generated line bundles 2L-E=3Q and 2L-H=2Q+H. Therefore I_(S_A)(2L) is generated. The associated blowup embedding, together with the very ample L, shows

\[
 \widehat L=3\rho^*L-F
\]

is very ample. Hard Lefschetz and the complete blowup Betti decomposition give primitive dimension (2p+1)-(2p-1)=2 for **every** m>=1. All these bases are algebraic: projective space, smooth split quadric and the displayed projective bundle have explicit Tate/Chow bases, preserved by the blowup decomposition. This identifies their actual canonical Betti classes, rather than supplying an arbitrary map.

The exact computation uses the excess and Segre formulas

\[
 e_p(v)=\rho^*i_*v-\sum_{j=1}^{p-1}e_j(c_{p-j}(N)v),\qquad
 \langle e_i(v),e_j(w)\rangle=-\int_{S_A}s_{i+j-p}(N)vw,
\]

where the latter is zero when i+j<p. Also i_*(Ah+Bxi)=B H^(p+1)+(A-3B)D. These determine the complete matrices checked by Python for m=1..12, with sign (-1)^p positive on the computed primitive plane. Finite testing is separate from the all-m geometric argument above.

## 4. Explicit two-slot geometric operators, with no abstract realization assumption

For m=1 the full middle basis of Xhat is

\[
 (\rho^*H^2,\rho^*C_A,\rho^*C_B,e_1(h),e_1(\xi)).
\]

The complete cup and middle pairing matrices are

\[
 M=\begin{pmatrix}9&3&3&0&1\\-6&0&0&1&-3\\0&0&1&4&-3\end{pmatrix},
 \qquad G=\begin{pmatrix}1&0&0&0&0\\0&0&-1&0&0\\0&-1&0&0&0\\0&0&0&0&-1\\0&0&0&-1&3\end{pmatrix}.
\]

The actual integral cycles U=(1,21,-24,6,0), V=(-3,-11,18,0,6) span ker M over Q. Direct intersection gives

\[
 K=\begin{pmatrix}1009&-681\\-681&513\end{pmatrix},\quad
 \det K=53856,\quad K^{-1}=\frac1{53856}
                  \begin{pmatrix}513&681\\681&1009\end{pmatrix}.
\]

Set U^dual=(513U+681V)/53856, V^dual=(681U+1009V)/53856. These are actual rational primitive Chow cycles. The four actual correspondences

\[
 \Gamma_{ij}=z_j^{\rm dual}\times z_i\in CH^4(\widehat X\times\widehat X)_\mathbb Q
\]

satisfy Gamma_ij Gamma_kl=delta_jk Gamma_il by ordinary intersection and pushforward. They exchange U and V, do not all commute, and their diagonal sum reconstructs every primitive middle target on this world. No arbitrary Hodge sheet switch or assumed Chow inverse is used.

## 5. Arbitrary-rank primitives on one connected fourfold

Choose any finite r>=1 distinct lines A_1,...,A_r in the same ruling of Q^2. They are pairwise disjoint. Their inverse images S_i in the **same old X** are pairwise disjoint smooth ruled surfaces. Blow up their union. The resulting X_r is an irreducible smooth projective fourfold. Its middle and next ranks are 3+2r and 2+r.

Since each I_(S_i)(2L) is globally generated and the disjoint union ideal is the product of these ideals, I_union(2rL) is globally generated. Thus, with t=2r+1,

\[
 L_r=t\rho^*L-\sum_i F_i
\]

is very ample by the blowup embedding. With complete coordinates (x,a,b,s_i,e_i), S=sum s_i and T=sum e_i, its cup equations are

\[
 3t x+t a+t b+T=0,\quad -2t x+S-3T=0,\quad
 b+(t+1)s_i-3e_i=0\quad\text{for every }i.
\]

They explicitly solve to

\[
 x=-S/2-rb/(2t),\qquad
 a=\frac{7t-2}{6t}S+\frac{7r-6t}{6t}b,\qquad
 e_i=\frac{(t+1)s_i+b}{3}.
\]

Therefore **every** primitive target has the actual native representative b w_0+sum s_i w_i, where w_0 is given by b=1, all s_i=0, and w_i by b=0, s_j=delta_ij. This directly proves primitive rank r+1 without a full-rank premise.

The old pairing is x x'-a b'-b a'; each new summand has pairing -s_i e_i'-e_i s_i'+3e_i e_i', and different centers pair to zero. Hence the complete primitive Gram is

\[
 G_r=\begin{pmatrix}A&c\mathbf1^T\\c\mathbf1&dI_r+\tfrac14J_r\end{pmatrix},
\]

\[
 d=(t^2-1)/3,\quad A=r^2/(4t^2)+2-7r/(3t)+r/3,\quad
 c=t/3-7/6+(3r+4)/(12t).
\]

Its determinant is d^(r-1) times

\[
 \boxed{(d+r/4)A-rc^2
 =\frac{r(105+411r+596r^2+384r^3)}{36(1+2r)^2}>0.}
\]

In particular the rational Gram inverse is explicitly constructed. Put B=dI+J/4, D=A-rc^2/(d+r/4)>0. Then

\[
 B^{-1}=d^{-1}I-\frac{1}{4d(d+r/4)}J,
\quad (G_r^{-1})_{00}=D^{-1},\quad
 (G_r^{-1})_{0i}=-\frac{c}{D(d+r/4)},
\]

and the lower block is B^-1+c^2 J/[D(d+r/4)^2]. The true rational cycle duals supply all (r+1)^2 matrix units on X_r itself. This is an arbitrary finite primitive rank in fixed dimension four, not a product or a merely abstract rank construction. Python independently checks all complete cup/source/Gram/inverse identities for r=1..16. The universal formula and positivity are separately proved in Lean; the all-r recovery theorem additionally checks the displayed complete cup solution.

## 6. Finite-arity GST cosmology and exact original-X discriminator

External products of the unit-feedback worlds have normalized readout one, including the empty point-world word. Products of the two primitive cycles and their algebraic duals give 2^a primitive sources and all corresponding matrix units for every finite arity a: cup with the product polarization is a sum of terms, each killed by primitiveness in its factor. Their Gram and dual identities multiply. Lean checks the unrestricted unit-word law; Python checks all 1093 three-dimension words through arity 6 and all 5461 binary tensor dual pairs through arity 6.

**What this achieves for the original research route:** interacting births do overcome the earlier single-exceptional-word vanishing, and actual arbitrary-rank matrix-unit realization is now constructed on a connected blowup world. The counterexample branch of this precise family is settled by its full algebraic Chow/Betti bases, not by a pushforward-kernel heuristic.

**Exact remaining arbitrary-X operation:** construct a genuine target-sensitive center/correspondence on the prescribed original X whose new native output couples to its unresolved primitive residual. Product insertion X times X_r is faithful coding: a target alpha tensored with w_i decodes by intersection with w_i^dual and push to X. It does not itself algebraize alpha. Likewise one must not assume an algebraic correspondence that already sends w_i to alpha. The next discriminating test is an intrinsic Hilbert/incidence center on the original X with a computed nonzero residual intersection, rather than another test of powers of the first exceptional divisor. The general route remains open; no no-go for combined GST births is claimed.

## 7. Evidence, review, and continuation pins

- [Existing Lean module, extended surgically](../../GSTQuadricPrimitiveRulingGeometry.lean): all-m mixed unit and first-world reconstruction; complete five-coordinate second-world primitive reconstruction; four matrix-unit laws; unrestricted parallel-birth Schur positivity and complete parallel-birth recovery.
- [Existing native support module](../../GSTUniversalResolvedSupportHodge.lean), namespace `GSTNativeExceptionalInteraction`: proper birational projection formula specialization, all rings/codimensions; no false multiplicative pushforward or finite-flat substitution.
- [Exact mixed-birth computation](../computations/gst_mixed_blowup_birth.py), [output](../computations/gst_mixed_blowup_birth.output.json), [v2 manifest](../computations/gst_mixed_blowup_birth.manifest.json).
- [Complete second-world and parallel-center computation](../computations/gst_second_blowup_primitive_plane.py), [output](../computations/gst_second_blowup_primitive_plane.output.json), [v2 manifest](../computations/gst_second_blowup_primitive_plane.manifest.json).
- [Independent Wolfram program](../computations/gst_interacting_births_wolfram.wl) and [returned exact output](../computations/gst_interacting_births_wolfram.output.txt): fourfold Gram/inverse, sixfold independently reduced normal/Segre pairing, and the all-r polynomial identity.
- First combined proof commit `5ca8b9e41ff591bc5494fd4fbcefcc1e0c946a39`: pinned integration [39384511727](https://github.com/kyo-oo/HC-PROOF/actions/runs/39384511727) **success**, native K0 [39384511635](https://github.com/kyo-oo/HC-PROOF/actions/runs/39384511635) **success**.
- Complete two-slot proof and executable commit `21046ba9acb036a9102b979bfeda826e9ab1b0e5`: pinned integration [39385786520](https://github.com/kyo-oo/HC-PROOF/actions/runs/39385786520) **success**.
- Connected arbitrary-rank Gram commit `90f3421bf0c6e0abd203ef78dc826ad573d868d2`: pinned integration [39386278251](https://github.com/kyo-oo/HC-PROOF/actions/runs/39386278251) **success**.
- Complete all-r reconstruction commit `ebeecc7b4fd5e5135e46013ed1039fc49bfdd8e5`: pinned integration [39386684493](https://github.com/kyo-oo/HC-PROOF/actions/runs/39386684493) **success**, **8967 jobs**. All nine selected new axiom receipts use only `propext`, `Classical.choice`, `Quot.sound`; complete log contains no `sorryAx`. Both full CI computation JSON outputs equal the recorded local outputs. [Verbatim selected axiom receipts and artifact provenance](../computations/gst_interacting_births_lean.receipt.txt). Both v2 computation manifests pass the Mathbox validator.

**Self-review scope.** The geometric review rederived lines-versus-quotient signs, actual center codimension, normal bundle sequence, proper projection formula, leading Chern character, Todd contribution, complete rather than truncated middle ranks, very ampleness, disjointness and union-ideal generation. Python checks entire matrices; Wolfram supplies an independent exact polynomial implementation. Lean proves coordinate and algebra laws using standard Mathlib. The scheme-level blowups, their canonical comparison and the geometric Hard Lefschetz leaves are not newly instantiated as Mathlib objects by these coordinate declarations. No target preimage, universal coupling hypothesis or final Hodge theorem is hidden in the new laws.

**Continuation handoff.** Continue from the newest code/CI pin below, preserve this combined route, and attack the original-X incidence/residual coupling in section 6. Keep the already verified unit and arbitrary-rank connected constructors available as actual geometric operator sources. Do not restart the 701-module inventory or return to CM direct sums unless their use addresses that same concrete coupling step.
