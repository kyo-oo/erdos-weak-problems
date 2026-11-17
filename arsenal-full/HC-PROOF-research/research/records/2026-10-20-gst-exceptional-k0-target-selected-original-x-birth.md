# GST exceptional K₀ target-selected source birth on the original X

- **Date:** 2026-10-20
- **Kind:** native geometric construction and exact original-X source-rank growth
- **Program:** full rational Hodge conjecture, universal primitive source birth
- **Base checkpoint:** `60584dff69d13ebad15400222057d0e0c26f42fd`, followed by construction commit `fa07dc117832ff06dd87a8c23f39aeae1385be5b`
- **Source:** `GSTActualXHodgeResidualProjection.lean`
- **Focus workflow:** [#39408587341](https://github.com/kyo-oo/HC-PROOF/actions/runs/39408587341) at `fa07dc117832` (RUNNING when record was prepared; a passing kernel receipt has not yet been observed)
- **Review:** direct derivation and exact Wolfram check; proof-audit of assumed geometric maps pending full scheme instantiation
- **Evidence:** complete rational algebraic derivation subject to specified Chow/Betti naturality and genuine GRR source inputs; Lean syntax/kernel status not yet confirmed.

## 1. A non-split ambient-world K₀ birth and exact original-X return

Let X be any smooth projective complex variety embedded in projective space with normal codimension c>=2, let Y=Bl_X(P^N), and let E=P(N_{X/P^N}). Write j:E→Y, q:E→X, xi=c1(O_E(1)). The previously established exceptional return is the **actual Chow operation**

[
R_p(W)=-q_*(\xi^{c-2}\cdot j^!W)\in CH^p(X)_\mathbb Q
quad(W\in CH^{p+1}(Y)_\mathbb Q).
]

For an independently geometric perfect-complex class F on Y, set

[
S_p(F)=R_p\Big(\big[\operatorname{ch}(F)\operatorname{td}_{\mathrm{required}}\big]_{p+1}\Big).
]

The Todd term is the correct relative correction for the chosen GRR/K₀ normalization; it must not be deleted or presumed 1 without a specific geometric calculation. Such S_p(F) is an actual algebraic Chow class on **the original X**.

The code constructs the generic typed linear map `exceptionalReturnGRR` as
[
K_0(Y)_\mathbb Q\xrightarrow{\mathrm{GRR}_{p+1}}CH^{p+1}(Y)_\mathbb Q
\xrightarrow{j^!}CH^{p+1}(E)_\mathbb Q
\xrightarrow{-q_*(\xi^{c-2}\cdot -)}CH^p(X)_\mathbb Q.
]
For precise degrees, `jChow` and `qChow` represent the graded Gysin and fiber-integration maps; the Lean type parameters are rational modules and their **actual geometric instantiation remains obligatory**.

## 2. Verified algebraic identity to be kernel-checked

Assume the canonical cycle-class maps satisfy the genuine Gysin and pushforward squares. For every algebraic perfect-complex source F, the checked-by-derivation identity is

[
cl_X(S_p(F))=-q_*\left(\xi^{c-2}\,j^*\,cl_Y(\mathrm{GRR}_{p+1}(F))\right).
]

The source is not obtained by choosing an algebraic preimage of the Hodge target. It is generated from F and the algebraic exceptional geometry.

Fix an actual prescribed original-X rational primitive Hodge class alpha and the old native source span A_old. Let r_alpha be GST's polarized Gram-dual residual. For an independently constructed finite packet F_1,...,F_n on Y, apply the existing normalized finite-flat K₀ projector P_f^K before GRR and set

[
s_i=S_p(P_f^K(F_i)),\qquad t_i=Q(r_\alpha,cl_X(s_i)).
]

Then the new **explicit original-X Chow cycle** is

[
Z_{\alpha,Y}=\sum_{i=1}^n t_i s_i\in CH^p(X)_\mathbb Q.
]

The new finite-family theorem proves, as a formal consequence of linearity,

[
\boxed{Q(r_\alpha,cl_X(Z_{\alpha,Y}))=\sum_{i=1}^n t_i^2.}
]

If at least one independently born source satisfies t_i≠0, the right side is strictly positive over Q; the already existing GST Gram-dual residual annihilates A_old and therefore certifies the STRICT inclusion

[
\operatorname{span}(A_{\mathrm{old}})
\subsetneq \operatorname{span}(A_{\mathrm{old}},cl_X(Z_{\alpha,Y})).
]

This is the mathematical content of
`exceptionalTargetSelectedNative`,
`exceptionalTargetSelectedNative_pairing`,
`exceptionalReturnGRR_class`, and
`exceptional_target_birth_strictly_grows_originalX`.

**Anti-circularity:** The nonzero period t_i is checked on a bona fide **independently constructed** perfect complex. If the old span is already the full algebraic image, such an input can never have nonzero residual pairing. No theorem here postulates that the input exists for EVERY arbitrary nonzero r_alpha.

## 3. Exact non-tautological regression test

Use the existing bona fide K3×K3 native primitive classes T and D=P_delta with rational intersection Gram

[
G=\begin{pmatrix}768&0\\0&21\end{pmatrix},\quad \det G=16128.
]

Let alpha=uT+vD and A_old=span(T). The old projection is uT; the primitive residual is vD. A diagonal-sheaf perfect-complex source with Chow output D gives

[
t_D=Q(vD,D)=21v,\qquad
Z_{\alpha,Y}=21vD,\qquad
Q(r_\alpha,Z_{\alpha,Y})=441v^2.
]

For v≠0 this yields a strict rank increase. Since the source is an explicitly geometric diagonal class on this test variety, the rational correction uT+Z_{alpha,Y}/21 equals alpha EXACTLY. This is a check of the birth-compiler mechanism **on this known algebraic source family**; it is not a claim about arbitrary X.

The exact **Wolfram** input was

```wolfram
Clear[u,v]; g={{768,0},{0,21}}; old={1,0}; diag={0,1};
target={u,v}; proj=((target.g.old)/(old.g.old)) old;
residual=Simplify[target-proj]; detector=Simplify[residual.g.diag];
newborn=detector diag; energy=Simplify[residual.g.newborn];
recovered=Simplify[proj+newborn/21];
{residual,detector,newborn,energy,recovered,
  Simplify[recovered==target],Det[g]}
```

Exact output:
```
{{0,v}, 21*v, {0,21*v}, 441*v^2, {u,v}, True, 16128}
```

## 4. First uncertain implication / next constructor operation

For the arbitrary original smooth projective X, prescribed primitive alpha, and r_alpha≠0, produce an explicit ambient-world PERFECT COMPLEX F_alpha on Bl_X(P^N) from a genuine non-tautological geometric construction such that

[
Q(r_\alpha,cl_X(S_p(F_\alpha)))\ne0.
]

An arbitrary vector in the exceptional Hodge summand is NOT a perfect complex, and no Hodge-to-Chow preimage is available as a starting input. Divisor/exc-divisor K₀ words with filtrations by line bundles remain in the tautological characteristic sector; extensions alone do not alter their K₀ class. Therefore the next candidate must involve independently constructed non-tautological sheaf/support geometry—e.g. diagonal/graph incidence on genuine existing factors, special determinantal sheaves from original equations, or a proven non-split moduli object whose K₀ class escapes the tautological subring.

The exact source-to-Chow calculation and conditional rank theorem are construction progress, not a full-Hodge theorem or a counterexample.

**Route disposition:** open. The new bridge is constructed; the independent universal source-birth step is open.
