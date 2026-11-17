# October 23: GST spectral-fold all-target holomorphic lift and explicit divisor Chow birth

**Target**: every original smooth projective complex X, codimension p, rational (p,p) Hodge alpha, actual CH^p(X)_Q with canonical Betti class alpha. This record links the Oct 22 causal/nonlinear source to the Oct 23 spectral involution.

**Math derivation:** [Updated spectral/Deligne/Gersten paper](../derivations/GST_alpha_deligne_integral_fold_kgersten_source_birth_2026_10_23.tex). Commits: 9653c4d64b045599bc1a59dd979d8a1cace68292 (actual regular algebraic result), 3c973545d6f9f3d46d8d745aeaf1f5a8fb31733e (universal holomorphic result), 8fcc692d1aa91660b27e85409e3c1f1e40df8909 (p=0 trace correction).

## 1. ACTUAL original-X algebraic theorem at every p in the divisor-generated sector

Prescribe any rational divisor Hodge classes beta_1,...,beta_p on any original X. Lefschetz (1,1) gives genuine algebraic lines M_i and positive integers m_i with canonical c1(M_i)=m_i beta_i. Choose the true affine Jouanolou bundle q:J->X. For every subset S of {1,...,p}, pull back the genuine tensor line L_S; its finite projective algebraic R=Gamma(J,O)-module has a split free presentation, hence a regular idempotent P_S and the actual regular algebraic involution A_S=2P_S-I, A_S^2=I. Construct the original Chow cycle:

    Z_alpha=(prod_i m_i)^(-1) (q*)^(-1)
          sum_S (-1)^(p-|S|) ch_p^CH(im P_S).

Its canonical Betti class is exactly alpha=prod_i beta_i, since the universal finite-difference polynomial identity is

    sum_S (-1)^(p-|S|) (sum_(i in S) x_i)^p/p! = prod_i x_i.

The proof cancels every monomial missing one index, leaving exactly p! permutations of prod x_i. Rational linearity handles any divisor-generated class. This is a genuinely alpha-dependent nonconditional algebraic source on arbitrary original X for this whole class. Hard Lefschetz gives all rational Hodge curve classes on all smooth projective X, and all rational Hodge classes for varieties of dimension at most three (adding divisors, degrees zero and top).

## 2. Unrestricted alpha-selected finite HOLOMORPHIC spectral involutions

For any prescribed alpha in H^(2p)(X,Q), p>=1 (indeed whether or not type (p,p)), rational topological K0 Chern character produces an integral multiple represented by topological bundles E+-E-. Pull these to the smooth affine Jouanolou fold J; J^an is Stein. Oka-Grauert produces holomorphic bundles; Cartan-Forster finite generation and Cartan B produce finite global HOLOMORPHIC idempotent matrices P+,P-. Their involutions A+- and A-- satisfy A^2=I, and their holomorphic Chern-Weil forms give exactly q*alpha in Betti cohomology, with normalization 1/[m(2 pi i)^p 2^(2p+1) p!].

This is a rigorous target-dependent same-fold construction on all X, but its matrices are holomorphic rather than necessarily REGULAR ALGEBRAIC.

## 3. Precise original-X criterion

For each fixed X,p,alpha, an original-X canonical rational Chow source exists IF AND ONLY IF finite REGULAR ALGEBRAIC involutions exist on the same affine Jouanolou fold whose rational Chern-character difference maps to q*alpha. Forward uses actual Chow homotopy invariance for affine bundles; reverse uses algebraic K0-to-rational-Chow on smooth X and finite projective module splitting on affine J. This is an exact type-and-existence equivalence, not automatic algebraization of the all-target holomorphic matrices.

## 4. Connection to decisive Oct 22/23 outcomes

The Oct 22 same-dimensional compact worlds exhibit projective pure Hodge versus compact Hopf odd-b1, hence no pure weight-one Hodge. Separately the nonlinear anti-deck signed pushforward constructs a genuine nondivisor primitive original-Q4 algebraic cycle, whose Gram inversion represents every Q4 rational middle Hodge class. The Oct 23 affine P1 fold gives a genuine regular matrix involution and algebraic symplectic two-form with nonzero Chern period, but its inherited mixed Hodge degree-two class remains type (1,1); the regular holomorphic 2-form has a double pole on the projective compactification.

## 5. Evidence and scope

Independent Wolfram symbolic finite-difference checks p=1..5 ALL TRUE, plus 27 exact integer tests across p=1..9 ALL TRUE. Independent Jouanolou P1 matrix idempotent and curvature coefficient 1/(4z) TRUE; Q4 two-source Gram reconstruction TRUE. The first finite-difference Wolfram trial used an unavailable BitCount symbol, was repaired to an explicit binary digit sum, and then rerun correctly. The unrestricted polarization identity has an all-p mathematical proof, not numerical extrapolation.

**No new Lean code or GitHub Actions kernel run is claimed for these LaTeX results; earlier green workflows remain SHA-specific.** The full arbitrary higher-primitive rational Hodge proof is not inferred from the holomorphic source, nor from an unproved regularization step.
