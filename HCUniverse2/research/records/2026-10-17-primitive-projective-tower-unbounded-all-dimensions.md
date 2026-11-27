# Mathbox — unbounded primitive algebraic cycles in every complex dimension at least four

- **Date:** 2026-10-17
- **Kind:** constructive theorem and all-dimensional geometric source extension.
- **Target:** Produce arbitrarily many independent primitive rational algebraic codimension-two cycles on explicit original smooth projective varieties of EVERY prescribed complex dimension D≥4. This extends the fixed-fourfold Fermat-surface graph theorem.
- **Hypotheses:** Integer D≥4; let k=D−4. Choose arbitrary prime d≥5 and the smooth degree-d Fermat surface S_d⊂P³. Let X_d=S_d×S_d of complex dimension four and Y_(d,k)=X_d×P^k of complex dimension D. The product h_X of the Fermat surface polarizations defines L_X, and L_Y=pr_X*L_X + pr_P*h is ample.
- **Source algebraic cycles:** From [the Fermat surface cyclotomic graph theorem](2026-10-17-unbounded-fermat-surface-primitive-graph-rank.md), take the r=φ(d)=d−1 explicit native algebraic graph differences Z_i=Γ_(g^i)−Γ_id on X_d for i=1,...,r. Each is primitive in degree four and the rational Betti classes cl_X(Z_i) are independent.
- **Construction on the original D-fold:** Define \(\widetilde Z_i=Z_i\times\mathbb P^k\subset Y_{d,k}\), a genuine rational algebraic codimension-two cycle. Its canonical Betti class is \(\widetilde\alpha_i=\pi_X^*\operatorname{cl}_X(Z_i)=\alpha_i\otimes1\).
- **Exact primitive calculation:** Since X_d has complex dimension four, source primitiveness is L_X∪α_i=0. Since Y_(d,k) has dimension 4+k and α_i has degree four, the required primitive test is \(L_Y^{k+1}\smile\widetilde\alpha_i\). Expand the product:
  
  \[
  (L_X+h)^{k+1}(\alpha_i\otimes1)
    =\sum_{j=0}^{k+1}\binom{k+1}j
      (L_X^j\alpha_i)\otimes h^{k+1-j}.
  \]
  
  Every j≥1 term vanishes because L_X α_i=0. The j=0 term equals α_i⊗h^{k+1}, which vanishes because H^{2k+2}(P^k,Q)=0. Thus every \(\widetilde\alpha_i\) is primitive in codimension two on Y_(d,k).
- **Exact independence:** Rational Künneth identifies cl_Y(\widetilde Z_i)=cl_X(Z_i)⊗1. Since H⁰(P^k,Q)=Q and multiplication by 1 is injective, rational linear independence is preserved. Therefore
  \[
  \boxed{\dim_\mathbb Q\operatorname{span}_\mathbb Q
       \{\operatorname{cl}_{Y_{d,k}}(\widetilde Z_1),\ldots,
         \operatorname{cl}_{Y_{d,k}}(\widetilde Z_{\varphi(d)})\}
         =\varphi(d), \qquad \dim_\mathbb C(Y_{d,k})=D.}
  \]
- **Uniform unbounded conclusion:** For each fixed D≥4 and each integer R≥1, choose a prime d>R+1. Euler phi(d)=d−1>R, so the explicit smooth projective D-fold Y_(d,D−4) has at least R independent non-Lefschetz algebraic primitive rational (2,2) classes.
- **Lean:** The new file GSTPrimitiveProductTowerStabilization.lean proves the complete commutative cup-algebra identity \((L_X+h)^n z=h^n z\) whenever \(L_X z=0\), and consequently \((L_X+h)^{k+1}z=0\) under projective nilpotence. The actual scheme-product/canonical Betti Künneth comparison is the geometric instantiation. The module is compiled together with the graph augmentation and H¹-moment rank theorems by gst-universal-surface-graph-augmentation.yml.
- **Wolfram:** Exact polynomial-ideal remainder checks \((u+v)^{k+1}-v^{k+1}\mod u=0\) for k=0,...,12. The symbolic identity follows immediately for all k by the binomial theorem. All-degree cyclotomic coefficient ranks remain independently verified by [GitHub #39031223354](https://github.com/kyo-oo/HC-PROOF/actions/runs/39031223354), SUCCESS.
- **Verification status:** The new Lean tower module is **kernel-verified** in [GitHub CI #39031358849](https://github.com/kyo-oo/HC-PROOF/actions/runs/39031358849), SUCCESS at commit 589be0673a797961cb1575bd5d7a7d40b826fec6. The job confirms the universal graph H1 moment equivalence, transcendental primitive rank interface, and product-tower binomial theorem; sorryAx audit passed. Evidence artifact 12100775983 (SHA256 efe0145d98ec3d38d88403db8f29b87f56c7cf319cde7e57ffef87be2f39369a).
- **Nearest prior result:** A family of smooth FOURFOLDS with unbounded primitive graph-cycle rank. This step proves the same unbounded result in each fixed ambient complex dimension D≥4 using native projective product cycles and their canonical Betti classes.
- **Route disposition:** Geometric source-construction theorem obtained for every ambient dimension D≥4 and arbitrary rank, with codimension fixed at two. The original all-varieties Hodge target additionally demands algebraic representatives of EVERY rational primitive (p,p) Hodge class for each arbitrary original X and p.
- **Evidence label:** Exact ordinary geometry (Künneth, projective nilpotence, polarization, algebraic external products) plus a generic Lean ring identity and finite exact Wolfram checks. Complete analytic scheme-product comparison remains an independent Lean geometry integration.
- **Next unresolved implication:** Extend primitive source production from explicit product families to arbitrary original smooth projective complex X, in all codimensions p, with a canonical full-rank geometric cycle-class construction.
