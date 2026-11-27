# GST: high-coniveau rational middle birth, exact topological K-source, and divisor-support descent

- **Date:** 2026-10-20
- **Original target:** universal rational Hodge algebraicity on every original smooth projective complex X, all p.
- **Starting revision:** `7d194fe601360fcb170597894e095306f3a31603` (green full integration and hetero-channel block).
- **Mathbox portfolio:** (A) geometric support and extra support descent; (B) topological pure-Chern K source and algebraization; (C) cross-channel primitive Gram detection.
- **Main complete derivation:** `research/derivations/GST_high_coniveau_rational_middle_K0_birth_2026-10-20.tex`, committed at `5a7ec5d`, augmented at `94e940d`, `a0ac6ae` and `a498563`.
- **Lean source:** `GSTGraphV2SelfExpandingCosmology.lean`, high-support arithmetic theorem `arbitrary_high_coniveau_middle_world_indices` at `8a51fc69b6699974944996caaf970c8532d1d9e1`.
- **CI:** Graph V2 [#39473651336](https://github.com/kyo-oo/HC-PROOF/actions/runs/39473651336) and full pinned [#39473651392](https://github.com/kyo-oo/HC-PROOF/actions/runs/39473651392) triggered at `8a51fc6`. Must check final results before claiming green.
- **External prerequisites:** genuine Chow/Betti smooth blowup decomposition, Bertini, rational topological Chern character, complex K-theory GRR, rational algebraic K-to-Chow Chern character, semisimple pure rational Hodge structures and divisor (1,1) theorem. These are used in the paper as geometric mathematics; not all are instantiated in Lean.
- **Review provenance:** mathematical self-review, no subagents, no public web browsing.
- **Evidence classification:** proved reduction and unconditional topological source in ordinary geometry; construction of its **algebraic** realization on arbitrary X is OPEN. No claimed full Hodge proof or counterexample.

## Route A: move every arbitrary Hodge target to arbitrarily deep geometric support on ONE rational middle world

For arbitrary original smooth projective X of dim d, any fixed positive integer k and any original codimension p, choose M>=max(d+k,N0,p+1), embed X in P^(2M), let Y=Bl_X(P^(2M)), E=P(N), ξ=c1(O_E(1)), j:E→Y, q:E→X. Then
  beta_{p,alpha}=j_*(ξ^(M-p-1)q^*alpha) ∈ Hdg^M(Y)_Q,
and Y is a smooth rational even-dimensional variety.

N is a quotient of globally generated T_P|X, hence N is globally generated, so O_E(1) is globally generated. Bertini supplies a smooth complete intersection T_r⊂E of r=M-p-1 hyperplanes, and its Gysin push of (q|T_r)^*alpha gives EXACTLY beta. Thus beta has geometric coniveau ≥M-p≥k unconditionally: an ACTUAL algebraic support exists, not an assumed Chow cycle for alpha.

On the same chosen Y all original p occur as separate middle exceptional channels. The middle projective-space component is algebraic with support codimension M≥k. Therefore **EVERY rational middle Hodge class of that Y lies in geometric coniveau N^k** while its full algebraicity defect remains
  D_M(Y) ≅ ⊕_(p=0)^d D_p(X).
For d≥4 only hard original p=2,...,d−2 can contribute; for d≤3 defect zero.

This implies: for every fixed k, full rational Hodge for arbitrary X is equivalent to algebraicity for the restricted middle rational worlds' middle rational Hodge classes of coniveau≥k. It emphatically does NOT establish algebraicity from coniveau.

**First failed shortcut:** Taking more hyperplane cuts multiplies a class and changes its Betti value; it does not necessarily supply a same-class support with H² divisor source.

## Route B: explicit universal topological perfect-K source, with necessary Todd term

On E the complex topological K Chern character ch_top:KU^0(E)_Q ≅ H^even(E,Q) gives unconditionally
  u_alpha=ch_top^{-1}(q^*alpha ξ^(M-p-1) td(O_E(-1))).
The codimension-one GRR/Thom push j_! produces v_alpha=j_!u_alpha on the rational Y, with **PURE** Chern character
  ch_Y(v_alpha)=j_*(ξ^(M-p-1)q^*alpha)=beta_{p,alpha};
all other Chern degrees vanish.

The rational topological K class ALWAYS exists even if alpha is not known algebraic. Its exact algebraization criterion is
  alpha algebraic on original X
  ⇔ u_alpha in image(K0_alg(E)_Q→KU^0(E)_Q)
  ⇔ v_alpha in image(K0_alg(Y)_Q→KU^0(Y)_Q)
  ⇔ beta middle class algebraic on Y.
If u_alpha is algebraic, its degree-(M−1) algebraic Chern character is ξ^(M-p-1)q^*alpha. Multiply by ξ^(M-d+p) and q_* to extract alpha in codimension p on the original X. Conversely an algebraic representative of alpha makes u_alpha algebraic by rational K0–Chow comparison.

**Constructive bundle ring form:** Let a_alpha=ch_X^{-1}(alpha)∈KU^0(X)_Q and λ=[O_E(1)]−1. Because λ nilpotent rationally, define the finite rational polynomial
  Φ_r(λ)=λ^r ( log(1+λ)/λ )^(r+1), r=M-p-1.
Then u_alpha=q^*a_alpha · Φ_r(λ). The polynomial Φ_r is entirely **algebraic** in the actual exceptional line bundle; the sole potentially nonalgebraic input is a_alpha on the original X. This is the exact K0-only GST birth obstruction: multiplication by algebraic Todd/Chern words cannot independently algebraize an unknown target.

**Exact Wolfram checks:** Todd(-ξ)=ξ/(e^ξ−1)=1−ξ/2+ξ²/12−ξ⁴/720+ξ⁶/30240−...; reciprocal cancellation checked through ξ^8. Independently, for r=0,1,2,3 the truncated finite bundle polynomial Φ_r(e^ξ−1) matched ξ^(r+1)/(e^ξ−1) through ξ^7 exactly, with results `{True,True,True,True}`. Finite checks verify formula correctness at that order; uniform proof is the formal log/exponential identity.

## Route C: cross-channel *genuine intersection matrix* inside the rational middle world

For classes alpha∈Hdg^p(X), gamma∈Hdg^q(X), the genuine cup intersection of their middle exceptional lifts equals
  ⟨beta_p(alpha), beta_q(gamma)⟩_Y
  = −∫_X alpha gamma s_(d−p−q)(N) if p+q≤d,
  = 0 if p+q>d.
For p+q=d it is exactly −∫_X alpha gamma: the original complementary Hodge cup pairing is anti-isometrically transported to the rational middle world. The resulting exceptional Gram matrix is anti-triangular by original codimension p. Its anti-diagonal blocks are negative nondegenerate Poincare pairings between rational Hodge-class spaces. Thus it is nondegenerate; normal Segre terms on one side cannot destroy invertibility.

**Concrete existing-native test:** for X=K3×K3 d=4, p=2, primitive diagonal D with D²=21, choose Y=Bl_X(P^10) and beta=j_*(ξ²q^*D). The ACTUAL middle intersection beta²=−21. This is a rational-world native period detector without assuming the algebraicity of any unknown prescribed alpha; D itself is independently algebraic. The detector certifies no global Hodge surjectivity.

## Route D: attempt direct actual smooth support reduction to divisors

A rigorous SUFFICIENT algebraicity gate for beta∈Hdg^M(Y) is to construct a finite algebraic Gysin expression from actual smooth projective T_a of codimension M−1:
  beta=Σ f_{a*} γ_a, γ_a∈H²(T_a,Q).
The map on rational polarizable pure Hodge structures splits onto its image, so if beta is a rational Hodge class one may take the sources to be rational type (1,1). Lefschetz (1,1) yields algebraic divisors D_a whose actual pushforward represents beta. This is a genuine geometric construction if the supports/maps and equality are independently built.

For original p=2, the explicit blowup supplies smooth supports of codimension M−2. The missing higher geometry is a **same-Betti-class** transfer to smooth Gysin supports of codimension M−1 carrying degree-two rational cohomology. Merely cutting another exceptional hyperplane changes beta, so it does not prove this.

## State

The above constructs genuine smooth rational worlds, genuine smooth supports of arbitrarily high absolute codimension, canonical topological K sources, exact GRR/Todd identities, actual rational Chow/Betti extraction formula, and a nondegenerate middle intersection block. It does NOT supply an algebraic K source from arbitrary original rational Hodge alpha. The universal algebraic source remains the unproved conclusion required for Hodge; one cannot assert that the topological K class is algebraic because Y is rational. The route remains OPEN, with precise construction target: a non-circular geometric algebraization of u_alpha (or genuine smooth Gysin divisor-source transfer of beta) on each chosen Y.
