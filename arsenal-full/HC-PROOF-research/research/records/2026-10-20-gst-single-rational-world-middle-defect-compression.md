# GST single rational middle world: all original-X Hodge defects in one exceptional packet

- **Date:** 2026-10-20
- **Research target:** full rational Hodge conjecture for every original smooth projective complex X and every p.
- **Starting revision:** `a4c84c96eccc2de57b97f02aad3f9730e8b63bb3`.
- **Mathbox route type:** source-first geometric reduction (not abstract GST matrix-unit completion).
- **Mathematical derivation:** `research/derivations/GST_rational_middle_blowup_uniform_Segre_2026-10-20.tex`.
- **Lean bridge:** `GSTGraphV2SelfExpandingCosmology.lean`, commits `f7184b3abc022be4a0dfd89cf74b8572c4496f88`, `92b832449209d69e14dcd5677ac625765f5e7aea`.
- **First Lean checks:** Graph V2 #39462910549 **GREEN**, full pinned integration #39462911079 **GREEN**, both at `f7184b3`; revision `92b8324` Graph V2 #39463484355 and full pinned #39463484304 launched (check final states before promoting).
- **Wolfram source check:** exact symbolic 4x4 Segre matrix inverse, determinant 1 (not a universal proof).
- **Evidence status:** mathematically proved from standard genuine Chow/Betti blowup/projective-bundle identities; Lean code proves middle-channel arithmetic, four-channel Segre polynomial and abstract source/return iff, but NOT the all-X scheme-level geometric theorem as a fully instantiated Lean statement.

## 1. One rational world works SIMULTANEOUSLY for every original codimension

Let X be smooth projective complex dim d, choose X↪P^N0. Take integer M≥d+1 and 2M≥N0, e.g. M=N0+d+2. Let Y=Bl_X(P^(2M)), c=2M−d, E=P(N_X/P), j:E→Y, q:E→X, ξ=c1(O_E(1)). Y is a smooth projective **rational** variety, dim Y=2M.

For each original p=0,...,d, choose i_p=M−p. Its exceptional channel is valid because 1≤i_p≤c−1 and p+i_p=M. A given rational Hodge class alpha_p∈Hdg^p(X)_Q has explicitly formed middle Betti class

\[\beta_p=j_*(\xi^{i_p-1}q^*\alpha_p)\in Hdg^M(Y)_Q.\]

Its algebraicity is **equivalent**, not merely implied, to the original alpha_p algebraicity; the return below gives an honest original-X Chow representative from any born W with canonical class beta_p.

## 2. The full graded all-channel Chern-Segre return

Define the actual exceptional Chow lift I_i(z)=j_*(ξ^(i−1)q^*z). Define the observed Chow class T_a(W)=−q_*(ξ^(c−1−a)j^*W), in the correct codim M−a. The projective bundle formula and j^*j_*=−ξ give T_aI_b=0 for b<a and T_aI_b=s_(b−a)(N)·id for b≥a.

Let C(t)=∑c_k(N)t^k and S(t)=∑s_k(N)t^k=1/C(t) with projective bundle sign convention. Then define

\[R_a(W)=\sum_{k=0}^{c-1-a}c_k(N)\cdot T_{a+k}(W).\]

The convolution identity C(t)S(t)=1 yields **R_aI_b=delta_(a,b) id** in Chow and canonically in rational Hodge. The return commutes with the canonical Betti cycle-class map because every operation is genuine pullback/cap/Gysin/pushforward. The identical method annihilates ambient projective-space pullbacks.

## 3. The resulting exact defect ISOMORPHISM

The middle Chow/Hodge blowup decompositions are diagonal under canonical cycle class. Since the middle projective-space component is algebraic and the shifted center groups are nonzero precisely when M−i is between 0 and d, the only nontrivial exceptional channels are i=M−p, p=0,...,d. Thus

\[\boxed{D_M(Y)\cong\bigoplus_{p=0}^{d}D_p(X)},\quad D_p(X)=Hdg^p(X)_Q/\operatorname{im}(cl_X^p).\]

The maps are induced by the actual exceptional lifts I_(M−p) and the Chern-corrected returns R_(M−p). This is an isomorphism, not just an injection, and it compresses all original-X codimension problems into ONE rational smooth projective even-dimensional middle Hodge fiber.

For d≥4, divisor/Hodge (1,1), top degree and Hard Lefschetz remove p=0,1,d−1,d, giving D_M(Y)≅⊕_(p=2)^(d−2) D_p(X). For a fourfold only D_2(X) contributes. For d≤3 no defects remain.

Global corollary: full rational Hodge for all smooth projective complex varieties **if and only if** the middle rational Hodge classes on all even-dimensional smooth projective rational varieties are algebraic.

## 4. Exact symbolic regression

Use c(t)=1+c1*t+c2*t^2+c3*t^3 and s(t)=Series[1/c(t),{t,0,5}]. The 4-channel upper triangular matrix S has superdiagonals s1, s2, s3 and correction C has superdiagonals c1, c2, c3. Wolfram returned C.S=S.C=IdentityMatrix[4] and Det[S]=1 identically, with rational polynomial parameters; the algebraic proof for all channels uses the full inverse series.

## 5. Adversarial self-audit and non-claims

- All-X quantifier: X is genuinely arbitrary smooth projective complex, p all 0..dim X, M selected from its embedding (no Hodge-rank inputs).
- Hodge grading: beta_p lies in codimension M on dim( Y )=2M; the p-dimension relation is exact.
- Original-X Chow return: all powers nonnegative for valid exceptional indices, classes c_k correct the grade, exceptional j^* does NOT use a target-specific Hodge preimage.
- The middle class is **not asserted primitive** under any ample polarization of Y.
- The full family is not asserted algebraic, and Y being rational does NOT force its middle rational Hodge classes algebraic.
- The source theorem is a major geometric reduction, not a proof of the Hodge conjecture. The first true unproved implication is the native independent algebraic realization of the constructed middle class beta_p on Y.
- Scheme-level Lean realization of Chow/Betti pushforward and the all-grades characteristic inverse remains an unverified formalization task; the committed Lean bridge checks arithmetic and abstract naturality only.

## 6. The resulting focused universal source problem

Instead of separately manufacturing primitive algebraic representatives on all original X and every p, construct actual codim-M algebraic cycles representing the **explicit middle exceptional class** beta_p on the rational Y=Bl_X(P^(2M)); use R_(M−p) to return to X. Complete middle source on a single Y even gives every p at once. The geometric source must be independent of any assumption beta_p or alpha_p already has a Chow preimage. This is the precise new GST proof-side goal.
