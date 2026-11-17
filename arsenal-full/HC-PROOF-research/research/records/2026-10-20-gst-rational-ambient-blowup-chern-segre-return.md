# GST rational ambient blowup: original-X return and Chern–Segre multibirth correction

**Date:** 2026-10-20 (IST).
**Research target:** full rational Hodge conjecture for every original smooth projective complex (X), every codimension (p), and every rational ((p,p))-class; alternatively a genuine counterexample with proof of nonalgebraicity.
**Module extended:** `GSTGraphV2SelfExpandingCosmology.lean`, namespace `NativeGeometryBirth.BlowupRationalHodgeTest`.
**Implementation commit:** `f3117e10db0350a241b7ef207694a5652263a4f9`.
**Base:** live branch `research/gpt6-native-point-primitive-span-20261017`. No public web search, subagents, or local Lean installation.

## 1. New all-original-X implication on a rational world

For any smooth projective (X\subset\mathbb P^N) of codimension (c\ge2), form the honest smooth projective **rational** blowup (Y=\operatorname{Bl}_X(\mathbb P^N)), with exceptional (j:E=\mathbb P(N_{X/\mathbb P^N})\hookrightarrow Y), (q:E\to X), and (\xi=c_1(\mathcal O_E(1))).

For any rational Hodge class (a\in H^{2p}(X,\mathbb Q)\cap H^{p,p}), the exceptional cohomology class is (\gamma_a=j_*(q^*a)\in\operatorname{Hdg}^{p+1}(Y)_\mathbb Q). With the correct geometric comparison identities,
```
j^* j_*(q^*a) = -xi*q^*a,
q_*(xi^(c-1)*q^*a) = a,
```
any actual algebraic (W\in CH^{p+1}(Y)_\mathbb Q) with (\operatorname{cl}_Y(W)=\gamma_a) yields
```
R(W)=-q_*(xi^(c-2)*j^!W) in CH^p(X)_Q,
cl_X(R(W))=a.
```
This is an actual descent construction on the **original** (X). It does NOT require a Chow preimage on (X) as input. The new theorem `exceptional_ambient_complete_forces_original_complete` removes the reverse exceptional Chow-map assumption from the previously established equivalence: full surjectivity of `clY` alone implies full surjectivity of `clX` by the explicit return.

Contrapositively, the theorem `exceptional_missing_original_forces_ambient_missing` shows that if (a\notin\operatorname{cl}_X CH^p(X)_\mathbb Q), the SPECIFIC lifted rational Hodge class (\gamma_a) is absent from the native canonical cycle image upstairs. Therefore a genuine counterexample anywhere would yield a genuine counterexample on a smooth projective **rational** variety. Conversely, proving the rational Hodge conjecture on **all** rational smooth projective varieties would suffice for all smooth projective varieties, by this blowup and descent. The implemented Lean statements are typed as rational linear maps plus explicit Chow/Betti naturality and self-intersection premises. The actual geometric scheme and canonical Betti instantiation is a separate required semantic bridge.

## 2. Uniform graded Chern–Segre inverse for exceptional births

For (1\le i,j\le c-1), define the exceptional channels
```
E_j(a) = j_*(xi^(j-1)*q^*a)
R_i(b) = -q_*(xi^(c-1-i)*j^*b).
```
The source of (E_j) has degree (q-j), the target of (R_i) degree (q-i); these are NOT scalar operators on a single incorrectly unified grade. Their composition is
```
R_i E_j = 0                       (j<i)
R_i E_i = identity
R_i E_j = cup s_(j-i)(N)           (j>i)
```
where (s_k(N)\) is the projective-bundle Segre operation. In the lines convention used by the repo,
```
C(t)=1+c1 t+c2 t^2+...,
S(t)=1+s1 t+s2 t^2+...=1/C(t),
s1=-c1, s2=c1^2-c2,
s3=-c1^3+2*c1*c2-c3.
```
For any purely exceptional class (\gamma=\sum_{j=1}^{c-1} E_j(a_j)), let (r_i=R_i(\gamma)). The full solution is
```
a_i = Sum_{j=i}^{c-1} cup(c_(j-i)(N), r_j).
```
Indeed (r_i=\sum_{j\ge i}s_{j-i}a_j), hence
```
Sum_{j>=i} c_(j-i) r_j
 = Sum_{k>=i} (Sum_{j=i}^k c_(j-i)s_(k-j)) a_k
 = a_i,
```
because the inner convolution coefficient is that of (t^{k-i}) in (C(t)S(t)=1). The sum is finite and all terms have the correct Hodge grading. This is a uniform theorem for arbitrary (c\ge2); it doesn't require a matrix determinant, a Gram inverse, or any conjectured class algebraicity.

**Exact Wolfram run:** use a stateless kernel and compute `CoefficientList[Normal@Series[1/Cpoly,{t,0,5}],t]`, then the 6×6 upper Toeplitz Segre matrix `T` and Chern matrix `K`. The result was `Det[T]=1`, `T.K==I` True, `K.T==I` True, and `Inverse[T]-K` identically zero with independent symbolic (c_1,\ldots,c_5). The uniform formal-series convolution, not the finite test, proves all-`c`.

The Lean theorem `exceptional_three_channel_chern_segre_correction` kernel-checks the first nontrivial three-channel symbolic Chern–Segre correction over an arbitrary commutative ring. This is a rank-three certificate only; the **uniform graded geometric statement** is proved mathematically by the convolution calculation above and awaits its own canonical-scheme typed implementation.

## 3. Exact source-growth discriminator

The return operator is linear and built from actual Chow pull, intersection, and push operations. For any rational algebraic (W) in (Y), (R(W)) is automatically an algebraic class of the original (X). In particular an exceptional class obtained only from hyperplane, exceptional divisor and normal characteristic classes has return in the old characteristic ring on (X); enlarging its tensor-word degree or the number of cosmology births does not by itself ensure nonzero coupling to a residual orthogonal to this ring.

The active construction must produce a **genuine independently born perfect-complex or Chow source (W)** on the rational (Y) such that (Q(r,\operatorname{cl}_X R(W))\ne0) for a specified nonzero primitive rational Hodge residual (r) on the original (X), or else produce an explicit Hodge (a) and prove (\gamma_a\notin\operatorname{im}(\operatorname{cl}_Y)) using all algebraic cycles, not merely tested source families.

## 4. Evidence boundary and continued program

- Mathematical proofs: smooth rational blowup geometry under standard projective bundle/exceptional push identities; all-`c` Chern–Segre inversion via formal series; counterexample transfer via canonical cycle comparison.
- New Lean declarations: `exceptional_ambient_complete_forces_original_complete`, `exceptional_missing_original_forces_ambient_missing`, `exceptional_three_channel_chern_segre_correction`. GitHub Actions Pinned Universal Hodge Geometric Integration [#39407555039](https://github.com/kyo-oo/HC-PROOF/actions/runs/39407555039) and Graph V2 CM NM Geometry Upgrade [#39407555109](https://github.com/kyo-oo/HC-PROOF/actions/runs/39407555109) both **GREEN** on descendant code commit `0cfa18427061fbbe11b420c591ed3a8963f841e3`, which includes the original theorem commit `f3117e10` unchanged. This certifies Lean kernel compilation in both gate scopes, not the scheme-level all-X Hodge theorem.
- Symbolic audit: Wolfram six-channel inverse with five algebraically independent Chern classes; it is not a proof of universal source existence.
- No standalone Hodge counterexample, all-`X` source-birth theorem, or uniform scheme-level Lean realization claimed. The missing implication is the genuine non-split algebraic source on the prescribed original-X blowup world with target-detecting canonical class.
