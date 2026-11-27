# GST original-X geometric defect and Euler separability — exact LaTeX-first audit

- **Date:** 2026-10-21 IST
- **Base SHA:** `8f59317cced9932a1b1da0fa2fff95eb97310ee5`
- **User target:** for every smooth projective complex X, construct an original-X algebraic representative of every rational Hodge class, and extract a genuinely algebraic one-sided source from the GST positive nonseparable diagonal Euler kernel, without inserting target algebraicity as an input.
- **Verdict:** exact all-X Chow/Hodge retraction plus a complete categorical separability equivalence proved in LaTeX; the two original universal existence claims are NOT established.

## New proofs, same original target

1. [True Chow blowup inverse and Hodge defect](../derivations/GST_exact_blowup_chow_hodge_retraction_2026-10-21.tex). Let Y=Bl_X P^(2M), M≥d+1, E=P_lines(N), c=2M-d, ξ=c1(O_E(1)). The actual Chow/Hodge blowup map is b*γ + Σ_{a=1}^{c-1} j*(ξ^(a-1) q* z_a). The exact ACTUAL Chow inverse, with Segre convention s(N)c(N)=1, is
   `v_a(Γ)=-q_*(ξ^(c-1-a) j*Γ)`, `P_a(Γ)=Σ_{t=a}^{c-1} c_(t-a)(N) v_t(Γ)`.
   The self-intersection formula j*j_*=-ξ and projective bundle q_*(ξ^(c-1+i))=s_i(N) prove P_a(Φ(z))=z_a, not just numerical equality.
   On canonical Hodge quotients, `D^M(Y) ≅ ⊕_{p=0}^d D^p(X)`. This means the middle GST world carries exactly all original-X rational Hodge defects as actual direct summands; the return operator produces a representative on X from any genuine middle Chow witness on Y, but creation of that middle witness is equivalent to original-X algebraicity.
   For a fourfold X, M=5: `D^5(Bl_X P^10) ≅ D^2(X)`, and actual return to CH²(X) is `P_3=v_3+c1(N)v_4+c2(N)v_5`.
2. [Complete algebraic Euler separability criterion](../derivations/GST_exact_separable_Euler_kernel_iff_Hodge_algebraicity_2026-10-21.tex). The rational Hodge-type topological K-sector W_Y has a nondegenerate rational Euler form. Every rational Hodge class in every codimension is algebraic **iff** the diagonal identity on W_Y is represented by a finite algebraic separable Euler coevaluation `K_sep=Σ E_i^vee ⊠ F_i`. Forward implication: pick algebraic Hodge basis and Euler duals via invertible Gram. Reverse: all outputs of a separable kernel are algebraic. For the GST residual kernel `Q=O_Δ−P` with P separable algebraic, Q acts as identity on `W_Y/A_Y` and therefore an algebraic separable replacement of Q acting correctly on ALL rational Hodge inputs is equivalent to zero Hodge defect. A positive quadratic diagonal Euler signal alone supplies no nonzero one-leg source in this quotient.

## Exact Wolfram cross-checks

- 60 embedding coverage tests: d=1..15 and M=d+1..d+4, all codimension indices p=0..d, no failures; general proof from inequalities.
- Seven exact symbolic Chern/Segre upper-triangular inverse matrix tests c=2..8 all true; general proof from c(N)s(N)=1 and Cartier exceptional self-intersection. The initial scratch test had a polynomial-truncation error and was discarded before correction.
- Finite algebra test `Q=diag(2,3,5)`, known algebraic frame e1,e2, residual e3: quadratic Q(e3,e3)=5, all algebraic linear readouts zero. This is abstract linear algebra, NOT a counterexample to Hodge.
- Rational Euler Gram `[[2,1,0],[1,3,1],[0,1,4]]` has determinant 18, exact rational inverse, and coevaluation reconstructs every vector; a two-dimensional algebraic span cannot cover dimension three. This checks only algebraic inversion.

## Dependencies and evidence provenance

Full standard blowup formula for actual Chow groups and rational Hodge cohomology, analytic fundamental-cycle realization, the projective-bundle Chern/Segre pushforward, and rational algebraic/topological K0 Chern character plus HRR. Self-reviewed mathematics, not independent refereeing or a Lean compilation. Both source files exist on the active user-directed branch. No public web search, no local Lean installation or Lean file edit.

## Exactly unresolved universal input

Construct an actual codimension-p Chow cycle on arbitrary original X with given primitive rational Hodge class, without assuming a representative. The positive nonseparable GST Euler identity and Chow retraction do not do so: any purported universally correct finite algebraic separable action already constitutes the full Hodge-surjectivity theorem. This is an explicit exact boundary, not a proposal to close an unproved theorem by renaming it.

**Disposition:** current exact proof package complete; the original broad Hodge research goal remains open and is not presented as solved.
