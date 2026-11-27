# Mathbox — unbounded independent primitive algebraic graph cycles on smooth fourfolds

- **Date:** 2026-10-17
- **Kind:** constructive theorem, exact computation, and source-family expansion
- **Target:** Construct arbitrarily many genuinely independent primitive rational algebraic codimension-two cycles on original smooth projective fourfolds, including examples carrying nontrivial H^(2,0), as an input to the universal GST primitive-spanning program.
- **Hypotheses and types:** Integer d≥4. Smooth Fermat surface S_d={z_0^d+z_1^d+z_2^d+z_3^d=0}⊂P^3_C, ample hyperplane h, and X_d=S_d×S_d, a smooth projective complex fourfold. Automorphism g_d multiplies coordinate z_0 by a primitive d-th root ζ_d and fixes the other coordinates. Every graph Γ_(g_d^k)⊂X_d is an actual algebraic codimension-two closed subvariety.
- **Active conventions:** Rational singular Betti cohomology and canonical geometric cycle-class map; middle primitive means kernel of L cup:H⁴(X_d,Q)→H⁶(X_d,Q), where L=pr_1*h+pr_2*h. Euler's totient r=φ(d), cyclotomic polynomial Φ_d(x), and a rational cycle difference C_k=[Γ_(g^k)]−[Γ_id] for k=1,...,r.
- **First geometric theorem — direct primitiveness:** S_d is smooth by the projective Jacobian criterion; the simultaneous derivatives d z_i^(d-1)=0 force all homogeneous coordinates to zero. Smooth projective hypersurfaces in P³ have H¹(S_d,Q)=0 by weak Lefschetz. The projective linear automorphism g_d fixes h. Therefore, by the exact graph/Künneth Lefschetz comparison recorded in [the two-moment surface graph theorem](2026-10-17-surface-graph-h1-moment-completeness.md), the Lefschetz images L cup cl(Γ_(g_d^k)) are equal for all k. Every C_k is thus a directly primitive genuine rational algebraic cycle, with NO primitive correction needed.
- **Second geometric theorem — cyclotomic eigenspace:** The canonical Griffiths residue description for a degree-d smooth surface identifies H^(2,0)(S_d) with the degree-(d−4) piece of the Jacobian ring. The monomial z_1^(d−4) is nonzero there. For Ω the standard homogeneous residue 3-form, the holomorphic two-form ω=Res(z_1^(d−4)Ω/F_d) is nonzero. Under g_d, F_d and the numerator polynomial are fixed, while Ω gains det(diag(ζ_d,1,1,1))=ζ_d. Hence g_d*ω=ζ_d ω with ζ_d a PRIMITIVE d-th root of unity.
- **Third theorem — exact rational linear independence:** The graph class Γ_(g^k) acts through its Künneth H²⊗H² component on H²(S_d) as g_d* or its inverse (the sign convention changes k→−k and does not change the rank). Its action on ω is multiplication by ζ_d^k. Suppose Σ_(k=1)^r a_k cl(C_k)=0 with a_k∈Q. The resulting action on ω gives P(ζ_d)=0 with
  \[
  P(x)=\sum_{k=1}^{r}a_k(x^k-1)\in\mathbb Q[x],
  \qquad \deg P\le r=\varphi(d),\quad P(1)=0.
  \]
  Since the minimal polynomial of ζ_d is Φ_d of degree r, P must be either zero or a constant multiple cΦ_d. Evaluate at x=1: 0=cΦ_d(1), and Φ_d(1)>0 for every d≥2. Consequently c=0, hence P=0 and all rational a_k=0. Thus the r classes are linearly independent on the ORIGINAL X_d, and they are all genuine algebraic primitive (2,2) Hodge classes.
- **Unbounded conclusion:**
  \[
  \boxed{\dim_{\mathbb Q}\operatorname{span}_{\mathbb Q}
   \{\operatorname{cl}_{X_d}(C_1),\ldots,
     \operatorname{cl}_{X_d}(C_{\varphi(d)})\}=\varphi(d).}
  \]
  For prime d≥5 this gives d−1 independent primitive codimension-two algebraic classes, while dim_C(X_d)=4 remains constant. As the prime degree increases the rank is UNBOUNDED.
- **Quantitative examples:** (d,φ(d),h^(2,0)(S_d))=(4,2,1),(5,4,4),(7,6,20),(11,10,120),(31,30,4060),(61,60,34220). Wolfram calculated the exact totients and geometric genera.
- **Exact arithmetic certificate:** The matrix whose kth row (1≤k≤r) is the rational coefficient vector of x^k−1 modulo Φ_d(x), expressed in the standard basis of Q[x]/(Φ_d), has integer determinant
  \[
  \det B_d=(-1)^{\varphi(d)}\Phi_d(1)\ne0.
  \]
  This follows by elementary row reduction or the same minimal-polynomial argument. The implementation research/computations/k3_cyclotomic_graph_orbit_rank.py computes cyclotomic polynomials by exact monic integer long division, constructs all coefficient matrices, and verifies their determinants by fraction-free Bareiss elimination. No floating-point arithmetic or random tests.
- **GitHub verification:** [Actions #39030979414](https://github.com/kyo-oo/HC-PROOF/actions/runs/39030979414) is SUCCESS at 0cba9adc57dfa9828622efb854557d6e6d7a44b9, with all 65 orders 2..66 checked and archive digest SHA256 bd443f9224929dcbc6fd3de1a3dacf9514526bb0828602a2c7ffc273d54c249f. The full all-d symbolic proof above is mathematics; this workflow certifies the finite exact determinant sample independently. [The surface-graph Lean gate #39030587546](https://github.com/kyo-oo/HC-PROOF/actions/runs/39030587546) verifies the uniform geometric augmentation and H¹-moment criterion.
- **Nearest prior attempt:** The quartic K3 construction gave only two independent primitive graph directions. Cyclotomic dependence on the hypersurface degree upgrades the output to any prescribed finite rank on smooth fourfolds.
- **Changed input:** Replace degree-four K3 by Fermat hypersurface surface of arbitrary degree d≥4, retain q=h^(1,0)=0, vary the eigenvalue order of the diagonal algebraic automorphism, and exploit cyclotomic minimal polynomials rather than fixed 2×2 rotation matrices.
- **Success criterion:** Construct, on each genuine smooth original fourfold X_d, φ(d) explicitly named non-Lefschetz algebraic cycles whose canonical cohomology classes are primitive and rationally independent, with a uniform proof for all d≥4.
- **Outcome:** Criterion achieved at the level of ordinary scheme/Künneth/residue geometry, exact all-d cyclotomic algebra, and bounded independent Wolfram/Python verification; the graph-CI Lean framework handles primitive native combinations. Full analytic residue and graph-to-Betti instantiation are independent Lean geometry integration tasks.
- **Route disposition:** Succeeded as an unbounded-rank fixed-dimensional original-carrier source family. Continue the all-varieties program with constructions that span EVERY rational primitive Hodge direction on each arbitrary original X, beyond this special source family.
- **Evidence label:** Standard unconditional geometric proof using smoothness, weak Lefschetz, residue eigenforms and canonical graph correspondences; exact symbolic all-d argument; 65 finite exact CI checks and Lean generic primitive algebraic graph interfaces.
- **First unresolved implication:** A general original-X geometric source-generation operation whose canonical primitive images span the entire rational (p,p) Hodge sector on arbitrary smooth projective complex X, not just selected fourfolds.
