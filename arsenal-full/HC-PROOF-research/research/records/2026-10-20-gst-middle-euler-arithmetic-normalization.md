# GST middle Euler arithmetic normalization and positive packet detection

- **Date:** 2026-10-20.
- **Base:** `03239e33c1496e8b4ad31d45562567df58000ba7`, following `5317346` and `17fc96a`.
- **Requested scope:** mathematics-first LaTeX derivation from the all-grade pure-middle rational blowup construction; no Lean repair or speculative universal Hodge conclusion.
- **Full proof:** [GST_middle_Euler_arithmetic_normalization_2026-10-20.tex](../derivations/GST_middle_Euler_arithmetic_normalization_2026-10-20.tex), 691 lines.
- **Exact computations:** [Wolfram source](../computations/GST_middle_Euler_arithmetic_normalization_2026-10-20.wl) and [returned output](../computations/GST_middle_Euler_arithmetic_normalization_2026-10-20.output.txt).

## Completed unconditional law

For an arbitrary original smooth projective d-fold X embedded in P^(2M), M>=d+1, let Y=Bl_X(P^(2M)) and let V_alpha be the previously constructed single topological K packet with pure middle Chern character I(alpha). Put S=c(N)^(-1), R=c(N)^(1/2), using finite nilpotent rational binomial series. All coefficients of R and its inverse are actual algebraic Chern-class words.

The exact unnormalized Euler kernel is
  chi_Y(V_alpha,V_gamma)=(-1)^(M+1) integral_X [alpha S gamma]_d.
For the explicit normalized sources Vhat_alpha=V_(R alpha), every normal Segre term cancels:
  chi_Y(Vhat_alpha,Vhat_gamma)=(-1)^(M+1) integral_X [alpha gamma]_d.

In a rational Hodge packet basis of size h, both normalized and unnormalized Euler discriminants are (-1)^((M+1)h) det(P_X), independent of the normal coefficients. Integral topological source representatives multiply this discriminant by the square of the product of their denominators.

## Positive arithmetic detection for EVERY prescribed Hodge packet

The explicit rational Lefschetz operator J reverses each primitive Lefschetz string and multiplies a primitive (q,q) string by (-1)^q. Primitive orthogonality and Hodge–Riemann give P_X(alpha,J alpha)>0 for every nonzero packet. Thus
  (-1)^(M+1) chi_Y(Vhat_alpha,Vhat_(J alpha))>0.
After common denominator clearing this is a positive INTEGER index.

For one original middle primitive class on a 2p-fold, J alpha=(-1)^p alpha. In the dimension-bounded world M=2p+1 its Euler self-index is integral_X alpha^2, with Hodge–Riemann sign (-1)^p. The native K3-product diagonal norm 21 gives exceptional intersection -21 and Euler self-index +21.

J is a rational Hodge operator here; no universal algebraic inverse-Lefschetz correspondence is asserted. Both detector sources are topological K unless separately algebraized.

## Exact arithmetic-to-cycle formula

Given actual native middle Chow sources Gamma_j, normalize their uniform original-X returns:
  A(Gamma_j)=R_Chow^(-1) sum_p Return_(M-p)(Gamma_j).
Pure algebraic K lifts C_j exist for these actual middle cycles. Arbitrary existing algebraic perfect K sources can first be processed by an explicit finite Adams projector onto Chern degree M.

For a rational Hodge basis e_i, t_ij=chi(Vhat_ei,C_j) and b_i=chi(Vhat_ei,Vhat_alpha) satisfy
  t_ij=(-1)^(M+1) P_X(e_i,cl A(Gamma_j)).
Consequently a verified det(t)!=0 gives the ACTUAL original-X cycle packet
  Z_alpha=sum_j (t^(-1)b)_j A(Gamma_j),  cl(Z_alpha)=alpha.
The source matrix rank is exactly the dimension of the returned native span. Existence of a universal full-rank native family is not proved. A topological Gram matrix alone cannot supply those native cycles.

The normalization preserves algebraizability iff original algebraicity and the previous injective Hodge-defect map.

## Additional actual support construction and convention correction

Construct a general surjection N -> (L^a)^(M-d-1). Its kernel K has rank M+1 because the rank-drop incidence codimension M+2 exceeds d. The ONE smooth support T=P_lines(K) in E, of codimension M-d in Y, carries ALL original Hodge degrees as explicit degree-d source classes. A finite inverse-binomial formula gives u_*gamma_alpha=I(alpha). It uses no inverse tautological class and commutes with cycle class on actual Chow inputs.

The preceding high-coniveau LaTeX mixed quotient-line global generation of N with the actual exceptional normal line O_E(-1). We repaired Section 2: on P_lines(N), use A=xi+a q*h and B=a q*h, with N^dual tensor L^a globally generated. The finite identity xi^r=(A-B)^r realizes each individual channel as a signed Gysin sum from genuine smooth complete intersections. The coniveau bound M-p is retained. No Lean-verified law is contradicted.

## Verification and limits

The final Wolfram run returned every check true: one heterogeneous primitive model with graded dimensions (1,2,3,2,1), exact positive polarized eigenvalues, 18 projective-normal cases, 40 support inverse tests and seven Todd/log checks. An initial computational harness used MatrixPower on a singular nilpotent matrix at exponent zero and produced unevaluated results; replacing that evaluation by polynomial Horner multiplication gave the clean final output stored here. The mathematical proof does not rely on finite tests.

Static LaTeX checks: matched environments and display delimiters; 426 inline math dollars in even total; no dangling template interpolation. No LaTeX compiler or local Lean execution was available, and no such verification is claimed.

**Proved mathematically:** normal-free universal middle Euler law; positive integer topological packet detection; discriminant law; exact native certificate and cycle-return formula; genuine single-support construction and repaired individual support.

**Still unproved:** universal algebraic realization of the topological packet, equivalently a universal actual native source family with full arithmetic rank. This work does not claim the rational Hodge conjecture or a counterexample.
