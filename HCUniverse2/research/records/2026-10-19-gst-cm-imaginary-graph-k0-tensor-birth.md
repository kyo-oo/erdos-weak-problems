# GST Mathbox: imaginary-CM algebraic graph sources yield 3^m primitive perfect-complex births

**Date:** 2026-10-19. **Branch starting point:** 6cad83c857237713000b05df8a44a1c1bbdbefbb. **Current theorem file:** GSTCMQuadraticNativeRankForcing.lean. **Original program goal:** construct rational algebraic representatives for every rational (p,p) Hodge class on every original smooth projective complex X. **Here:** a genuinely new source family on CM elliptic products, not a general all-X theorem.

## Genuine geometry on E×E

Let E be a complex elliptic curve with endomorphism i such that i²=-1, e.g. y²=x³−x. On S=E×E write x1=[{o}×E], x2=[E×{o}], delta=[Graph(id)], gamma=[Graph(i)]. All are genuine algebraic Cartier divisors. Their Chow intersection numbers satisfy x1²=x2²=delta²=gamma²=0, x1*x2=xj*delta=xj*gamma=1 and delta*gamma=deg(1−i)=Norm(1−i)=2. The last equality counts actual fixed points of an algebraic automorphism, not an eigenvalue assumption.

Define H=x1+x2, P=x1−x2, D=delta−x1−x2, I=gamma−x1−x2. Direct Chow intersection gives HP=HD=HI=0, and signed primitive Gram
\[
\boxed{Q_S(P,D,I)=2I_3}
\]
where Q_S(u,v)=−deg(u*v). Thus P,D,I are independent algebraic primitive (1,1) classes, with no assumed period detector. The common basepoint intersection ensures the H-multiplication identities hold in rational Chow, not merely numerical intersection.

## Actual algebraic perfect complexes

Let L1,L2 be factor degree-one line bundles and M_D=O(D), M_I=O(I). Define rational algebraic K₀ classes
\[
A=[L_1]-[L_2],\quad
B=\tfrac12([M_D]-[M_D^{-1}]),\quad
C=\tfrac12([M_I]-[M_I^{-1}]).
\]
Their Chern characters are **purely codimension one**:
\(\operatorname{ch}(A)=P\), \(\operatorname{ch}(B)=D\), \(\operatorname{ch}(C)=I\).
The anti-inverse subtraction removes the degree-2 Chern character term; simply taking [M]-[O] would leave a nonzero top-degree term and would not yield the same pure source. Every input is an independently constructed algebraic perfect complex.

For every m≥1 on the ORIGINAL smooth projective X=E^(2m), choose one of A,B,C on each factor pair and tensor them externally. For each word epsilon∈{P,D,I}^m the corresponding rational perfect complex has pure ch_m equal to the actual algebraic Chow cycle Z_epsilon=product of the chosen divisors. It is middle Lefschetz primitive because each factor is primitive. Its signed intersection Gram is, by true Künneth and top-degree integration,
\[
\boxed{Q_X(Z_\epsilon,Z_\eta)
=\prod_{j=1}^m 2\,\mathbf1_{\epsilon_j=\eta_j}
=2^m\mathbf1_{\epsilon=\eta}.}
\]
So there are **3^m pairwise orthogonal nonzero algebraic primitive sources on every such original CM abelian 2m-fold**, not just a formal vector-space model.

The older GST noncrossing Catalan Koszul frame has rank C_m within the pure coordinate divisor-word subspace. Every graph-containing word has cross-factor H¹⊗H¹ Künneth content and is orthogonal to that entire squarefree coordinate-word subspace, while the unique all-P word is already among the old sources. Hence the true primitive algebraic rank is at least \(\boxed{C_m+3^m-1}\).

At m=2, the Catalan Gram [[4,2],[2,4]] joins eight orthogonal new graph-containing source classes, each with self-pairing 4. The combined 10×10 Gram is nondegenerate, with exact determinant 12*4^8=**786432**. At m=1 the three primitive divisors span the full primitive Neron-Severi space for a CM E×E (Picard rank 4, one ample and three primitive).

## Target-sensitive GST native K₀ construction

For any prescribed rational primitive (m,m) class alpha on the SAME original CM X, let a_epsilon=Q_X(alpha,Z_epsilon). The explicit rational algebraic K₀ source E_alpha=(1/2^m)*sum_epsilon a_epsilon E_epsilon has genuine algebraic Chow class Z_alpha=(1/2^m)*sum a_epsilon Z_epsilon. The computed Gram proves the exact target period equalities
\[
Q_X(Z_\alpha,Z_\eta)=a_\eta,\qquad
Q_X(\alpha,Z_\alpha)=\frac1{2^m}\sum_\epsilon a_\epsilon^2\ge0.
\]
There is strict positivity when at least one genuine new source detects alpha, and exact representation if alpha belongs to their rational span. Any combination with the Catalan frame must exclude the duplicate all-P word.

## Evidence / limits / next geometric construction

Exact symbolic Wolfram values: H cup each source is zero; primitive Gram=2I3; determinant 8; m=2 enlarged determinant 786432. All-m rank follows by factorwise intersection, not a finite computation.

The existing Lean GST CM module was edited in place at commit 727d84b64ba6adcd263cbd3b6b5e0b8486817e68 with an exact four-coordinate intersection model and arbitrary-rank CM tensor Gram proof. CI receipt is the GST CM Quadratic Native Rank Forcing workflow; verify its final conclusion before labelling code kernel-verified. The current Lean model checks rational intersection arithmetic, while actual CM schemes, Chern class/GRR, Kunneth and canonical Betti cycle-class instantiation are mathematical geometric inputs yet to be implemented in the full repository.

**Unchanged global acceptance:** construct a true original-X Chow representative for all rational (p,p) alpha on arbitrary smooth projective X. This special CM family increases genuine source rank; the missing arbitrary-X source span and canonical Betti formalization are separate requirements.
