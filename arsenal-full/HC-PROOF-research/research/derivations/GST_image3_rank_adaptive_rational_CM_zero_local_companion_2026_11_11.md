# GST Image-3 rank-adaptive rational companion transport: any prescribed finite native quotient rank

**Date:** 2026-11-11. **Branch:** research/gpt6-native-image3-navigation-cm-star-ncoho-20261111.

**Context:** The original author's GST Hodge antecedent needs full cyclicity for arbitrary rational Hodge space ranks, NOT only multiples of the original 12-state N-wave world. The earlier universal source theorem produces cyclic rank 12h for all h>=2, with zero local original SURVIVE source and a unit Hankel determinant, but its SMALL rational strengths may have no rational linear spectral factors and hence do NOT automatically produce rank-one equivariant quotients.

This result corrects that deficiency WITHOUT importing a classical model: it stays with the ORIGINAL four-carry/three-trit GST U/J/M and original fixed-point source geometry.

## 1. Exact original native GST rational CM fixed-pair spectral factor

The TWO ORIGINAL U-fixed physical information cells are the null cell (carry=0,trit=0) and the maximum cell (carry=3,trit=2). On their rational wave signal subspace in that order, the actual ORIGINAL operators satisfy
  U = [[1,0],[0,1]],
  J = [[0,1],[-1,0]],
  M = [[0,0],[0,2]]
under the same observable coordinates used in GSTGraphV2CMWaveFusion.lean. These follow directly from the existing Lean theorems U_five, J_square, source_on_null_fixed/source_on_positive_fixed and from the original shuffle/mirror definitions; no arbitrary rotation is introduced.

Thus for EVERY rational strength lambda the true original F_lambda=U+J+lambda M has the invariant fixed-pair block
  F_fixed(lambda) = [[1,1],[-1,1+2lambda]]
with exact characteristic factor
  q_lambda(x)=x^2-(2+2lambda)x+(2+2lambda)
and discriminant Delta=4(lambda^2-1).

For lambda=+-t_a, with a a positive integer >=3 and
  t_a=(a+a^(-1))/2 in Q,  t_a>1,
we have
  q_(+t_a)(x)=(x-(1+a))*(x-(1+1/a)),
  q_(-t_a)(x)=(x-(1-a))*(x-(1-1/a)).
Therefore all FOUR native fixed-sector eigenvalues are rational. The full original 12-state Krylov is still cyclic at +/-t_a because the earlier exact rational-strength theorem holds for ALL rational lambda excluding only 0,-1; t_a>1 means neither exclusion occurs.

**Caution:** for lambda=+-1/400 or +-1/2 used in earlier small-strength examples, the fixed-pair q_lambda has negative discriminant, and the exact full 12x12 factorization at those examples has no linear rational factor. The naive assertion "a full cyclic 12h signal automatically has a one-dimensional quotient" would be FALSE for such an operator. This rank-adaptive choice addresses that defect.

## 2. Explicit rank-adaptive zero-local-source all-finite-r theorem

Let r>=1 be ANY integer prescribed native quotient rank. Let h=2r independent ORIGINAL GST N-wave worlds. Choose DISTINCT integers
  a_i=i+2,  i=1,...,r.
Define rational source strengths, in paired order,
  lambda_(2i-1) = (a_i+a_i^(-1))/2,
  lambda_(2i)   = -(a_i+a_i^(-1))/2.
Every strength is nonzero, not -1, rational, pairwise distinct, and their total sum is ZERO.

Define p_h(t)=Product_(k=1)^h (t-lambda_k) and its usual rational Frobenius companion C_h. As in the earlier all-N theorem, its diagonal is identically zero, so every actual original SURVIVE M source term occurs CROSS-WORLD only; no local M term is inserted.

Choose address step L_r=20(r+5) and rational Lagrange polynomial f_h with
  f_h(lambda_k)=L_r*(k-1).
Set B_h=f_h(C_h). Define on the exact original U,J,M the ONE SOURCE F
  T_h = I_h⊗(U+J) + C_h⊗M + B_h⊗I_12,
rooted at ONE original native mixed seed e1⊗v.

Because max_k |lambda_k| < (r+3)/2, we have
  ||U+J+lambda_k M||_infinity <= 2+2|lambda_k| < r+5.
All spectral disks centered at L_r*(k-1) are pairwise disjoint, hence the h original 12-state blocks have coprime minimal polynomials. Each block is cyclic for the old v by the exact original rational-strength determinant, and e1 is cyclic for C_h. Polynomial CRT therefore proves for EVERY r>=1:
  rank_Q [w,T_h w,...,T_h^(12h-1)w] = 12h = 24r.

Now SELECT exactly one original fixed-pair rational eigenvalue from each POSITIVE source block k=2i-1:
  mu_i = L_r*(2i-2) + 1 + a_i
for i=1,...,r.
These are distinct rational numbers, with corresponding rational degree-one factors t-mu_i of the full original 24r-dimensional cyclic minimal polynomial of T_h. Its cyclic module Q[t]/(chi_h(t)) therefore has a canonical surjective Q[t]-module homomorphism
  q_r: Q^(24r) -> DirectSum_(i=1)^r Q[t]/(t-mu_i) == Q^r.
Indeed q_r is polynomial evaluation at the r distinct mu_i after identifying the cyclic module using the original root seed w; Chinese remainder gives surjectivity, and q_r(w)=(1,...,1).

The quotient fold is diagonal T_r=diag(mu_1,...,mu_r), with
  rank_Q[q_r(w),T_r q_r(w),...,T_r^(r-1)q_r(w)] = r
by the ordinary rational Vandermonde determinant Product_(i<j)(mu_j-mu_i) !=0.

In particular there is a **native rank-adaptive, source-generated cyclic quotient for EVERY rational target vector-space rank r**, with no 12-divisibility restriction; all source transport is original GST U/J/M plus rational N-navigation and has zero local M coefficients.

The induced rational detector on Q^r with ℓ(T_r^k q_r(w))=delta_(k,r-1) for k<r exists because its Krylov vectors are a rational basis. The r×r Hankel has determinant (-1)^(r(r-1)/2) !=0. (It equals +1 only when that parity is even; do not mistakenly claim +1 for every r.)

## 3. Exact implementation audits with owner original matrices

Wolfram exact rational computations were executed on the original twelve-cell U/J/M and seed with:
- r=1,h=2, lambdas {5/3,-5/3}, address step120: original full h-wave cyclic 24/24 with Krylov determinant nonzero modulo1009 (residue205); original true fixed-pair quadratic factors rationally in each of the 2 blocks.
- r=2,h=4, lambdas {5/3,-5/3,17/8,-17/8}, address step140: original full h-wave cyclic 48/48 with determinant nonzero mod1009 (residue706); all four original fixed-pair quadratic factors split rationally.
- exact sum lambda=0, diagonal(C)=0, original fixed-pair quadratic divides full original 12x12 block charpoly, and every chosen native lambda distinct. All checks passed.

The all-finite-r result comes from the symbolic proof, not sampling r1/r2. A standalone committed script for these two audited cases accompanies this derivation.

## 4. The exact ORIGINAL-X Hodge firewall

A rational cyclic quotient Q^r for every abstract r does NOT mean the canonical rational Hodge space W_p(X) is automatically that quotient with a *geometrically induced* operator. One may choose a vector-space isomorphism to any rational W of dimension r, but unless that isomorphism is constructed from bona fide projective correspondences and actual original-X cycle-class naturality, it is NOT a proof of a missing algebraic Hodge class.

The formal goal must require a **genuine original-X Chow-to-Betti landing** compatible with the selected rank-r cyclic GST quotient and must prove source-surjectivity on all rational Hodge classes WITHOUT assuming their algebraicity as input. This remains the unproved universal geometric antecedent of the author's existing conditional Hodge theorem.

## 5. New ranked project target

The rank-adaptive native obstruction is now solved algebraically. The most useful next step is to find an original-X realization mechanism whose true rational Betti Hodge space is an equivariant quotient of the GST full root module, with a geometrically constructed cyclic Chow seed. A generic choice of linear equivalence after seeing unknown Hodge classes is not such a mechanism.

This result is an ORIGINAL GST contribution: the rational eigenvalues come from the author's own U-fixed and J-mirrored physical null/max cells plus its exact SURVIVE source multiplicities, not an arbitrary model or classical family.
