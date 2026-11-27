# GST hypothesis-to-Hodge execution: original full-N wave, native source algebra, and canonical Chow landing

Date 2026-11-10 (IST). Base SHA: \`8d85045980acc09fe6190f7b938bf6234e27f41b\`. Independent research branch: \`research/gpt6-gst-wave-curvature-spectral-birth-20261110\`.

## Immutable theorem and the exact antecedent

\`GSTHodgeSingleHypothesisConditional.NativeGSTSingleFoldOrbitLaw\` is the **antecedent**; \`exactHodge_of_one_GST_fold_orbit\` is the existing (kernel-checked on prior active branch) conditional implication \`X => Y\`, where Y is \`EveryHodgeClassIsRationalAlgebraic H\`. Its determinant alternative is \`NativeGSTSingleFoldDeterminantLaw\` and \`exactHodge_of_one_GST_fold_determinant\`. For a claim about the actual rational Hodge conjecture, the supplied Stage-2G cycleClass must also be identified with the canonical rational Betti cycle-class map of the original X.

The mathematics-first target is a genuine original-X native Chow fold/seed and rational Hodge detector with full nonzero Hankel determinant, **for every smooth projective complex X and all p**, without a supplied algebraic Hodge basis or target-cycle inverse.

## The strongest new unconditional theorem inside the ORIGINAL GST

[Full detailed derivation](../derivations/GST_full_N_original_wave_CRT_Hankel_one_matrix_algebra_2026_11_10.tex).

The pure information carrier is the ORIGINAL twelve-state carry/trit seven-axis GST graph; \`U\` is the x4/base3 information shuffle, \`J\` is the original signed mirror CM operator, \`M\` is Wave-I SURVIVE multiplicity, and \`seed\` has its original two nonzero information cells. NO replacement operators or K3 geometry were used.

Original base operator \`T0=U+J+M\` has exact characteristic polynomial
\`t^12 -6t^11+18t^10-40t^9+69t^8-98t^7+123t^6-104t^5+6t^4+62t^3+20t^2-56t+16\`.
Its exact original-seed Krylov determinant is \`-1149656584000\`, and the exact absolute row sum is bounded by 4.

For **every** existing NShape with N>=1 independent hole channels, the existing shifted operator \`TN = I_N tensor T0 + diag(10 channel_i) tensor I_12\` and uniform seed \`vN=(seed,...,seed)\` have
\`
det Krylov(TN,vN) = det Krylov(T0,seed)^N *
 product_{i<j} Resultant(chi(t-10 channel_i),chi(t-10 channel_j)) != 0.
\`
This is an exact algebraic CRT proof: distinct shifts are at least 10 apart and every base eigenvalue has modulus <=4. There is an explicit lower bound
\`|det Krylov(TN,vN)| >= 1149656584000^N * 2^(144 binomial(N,2))\`.

Set \`r=12N\`, \`ellN=e_r^T Krylov^-1\`. By definition its first r orbit moments are exactly the last-coordinate delta, so the complete Hankel matrix is anti-triangular with all anti-diagonal entries 1, giving the **exact all-N determinant**
\`
det [ellN(TN^(i+j) vN)]_(0<=i,j<r) = 1.
\`
This is an unconditional full-12N information-space theorem and fixes the risk of mistaking the N-hole detector quotient (kernel dimension 11N) for the full signal carrier.

The same *original* GST laws give \`U^T=U^4\`, \`J^T=-J\`, \`M^T=M\`. Adding the NEW rank-one source coupler \`PN=vN vN^T\` to the original Wave-I/CM/N-hole algebra yields
\`
(TN)^i PN (TN^T)^j = (TN^i vN) (TN^j vN)^T
 = Krylov E_ij Krylov^T.
\`
These r^2 words form a rational basis of all \`End_Q(Q^(12N))\`. Thus the full original GST signal/source operator algebra with the rank-one source coupling has scalar commutant and no hidden proper invariant rational signal subspace.

All explicit finite receipts are in the [COMMITTED Wolfram code](../computations/gst_full_N_original_wave_CRT_Hankel_one_matrix_algebra_20261110.wl). The exact committed script was fetched back from GitHub and executed verbatim; the result returned \`allPassed -> True\`, including original U5/J2, transpose identities, base char, 12x12 determinant, 24x24 determinant and resultant, both Hankel=1, the matrix unit identity, and rank 144 of the 12x12 source word operator span. The all-N theorem is from mathematical proof, not finite extrapolation.

## Genuine canonical original-X algebraic geometry actually obtained

[Geometric derivation and commutant proof](../derivations/GST_polarized_adjoint_commutant_native_single_fold_2026_11_10.tex).

For any original smooth projective complex d-fold X, any p, and any ample divisor h, set q=integral h^d>0.
The rank-one source coupler **really exists algebraically**:
\`
Gamma_(h,p)=q^-1 pr_1^*(h^(d-p)) pr_2^*(h^p) in CH^d(X x X)_Q
\`
Its Chow action is \`Z -> (int Z h^(d-p)/q) h^p\`, it is idempotent and fixes \`h^p\`. Its canonical Betti action is exactly the same formula on rational Hodge classes. It is a genuinely original-X realization of one part of the new GST rank-one information source coupling. It does not create primitive algebraic directions by itself.

For any second genuine original-X algebraic correspondence T, its native curvature on the seed is the explicit, exactly algebraic
\`
[T,P_h](h^p) = T(h^p) - P_h(T(h^p)).
\`
This is the user's existing \`GSTGraphV2NativeCurvatureBirth\` logic instantiated on the original X with an independently constructed canonical Chow projector. Its value in the entire algebraic image is automatic, but its nonzero coupling to a previously uncovered primitive direction depends on the real geometric correspondence T.

## Second GST sufficient route without rational Hodge eigenvalue hypotheses

Under rational positive Hodge-Riemann polarization Q on W_p(X), suppose an algebra of **genuine** X-times-X Chow correspondences acts on W, is closed under its Q-adjoints **with those adjoints also genuinely algebraic**, and has rational commutant only scalar operators. Then the entire genuine canonical algebraic image B=im(cl_X) is W. Proof: B contains h^p; it is stable under all actual correspondences and their genuine adjoints; so the positive rational Q-orthogonal projection P_B commutes with the entire algebra. Scalar commutant implies P_B=I; thus B=W. In fact the native word orbit of h^p spans W, so a finite rational basis of Hodge classes is constructed as actual original-X Chow words rather than assumed. Poincare dual algebraic cycles then compile an actual full-Chow single cyclic Hankel fold. Without actual Chow realization and genuine adjoints on every X, this is an honest conditional criterion, not an unconditional Hodge proof.

The accompanying [Wolfram exact commutant script](../computations/gst_polarized_adjoint_commutant_birth_20261110.wl) was independently executed verbatim after correction, returning \`allPassed -> True\`: commutant dimension 1 on the connected N=1..7 information models, dimension 2 on a disconnected four-channel model, and exact rational self-adjoint projection identities. This explicitly avoids the old false converse of Schur: scalar commutant alone is insufficient when the algebra is not adjoint-closed.

## Connected curvature source-birth route and Lean status

The [connected source route](../derivations/GST_all_N_connected_curvature_spectral_birth_2026_11_10.tex) constructs, from ONE actual algebraic seed and two genuinely realized noncommuting original-X correspondences whose rational spectral-curvature graph is strongly connected, a full original-X native Hodge source frame and then a single cyclic fold. Its exact matrix assertions and the rank-vs-connectivity adversarial countermodel passed the [committed Wolfram test](../computations/gst_connected_curvature_spectral_birth_20261110.wl) with \`allPassed -> True\`.

Additive Lean modules on this branch (none changes existing active-branch math):
- \`GSTAllNConnectedCurvatureBirth.lean\`: original NShape neighbor mixer, exact quotient/full-cell commutators, one-step native source propagation
- \`GSTAllNConnectedCurvatureGeometricClosure.lean\`: one-seed rational edge chain, algebraic-source recursion, old cyclic completion interface
- \`GSTFullWaveCyclicSourceCommutant.lean\`: abstract rational source-orbit scalar commutant from a cyclic orbit and one rank-one source operator

The first CI attempts exposed a missing namespace and an unregistered build root; both were corrected on the branch. GitHub Actions current-revision kernel outcomes must be checked at the corresponding exact SHA before any claim of Lean-green status. The exact all-N CRT + Hankel and matrix word spanning theorems remain hand-proved and Wolfram audited, not newly kernel-checked.

## Precise present mathematical boundary

**Proved:** original GST full 12N wave single-orbit and scalar-Hankel determinant for all positive N; original signal/source algebra is full End_Q; genuinely canonical original-X rank-one source Chow projector for every X; and precise adjoint-commutant and connected-curvature source-birth criteria.

**Not proved:** a uniform algorithm which, for every original smooth projective X and codimension p, constructs the OTHER genuine Chow fold operators mixing all previously uncovered primitive rational Hodge directions. A formal linear isomorphism from 12N information space to W_p(X) is NOT a canonical Chow realization. Resolving this exact geometric source birth would allow the already proved \`NativeGSTSingleFoldOrbitLaw => EveryHodgeClassIsRationalAlgebraic\` implication to close. No new algebraic-Hodge basis or surjectivity is inserted as an assumption.

Every finite certificate here is exact; no finite result alone establishes the universal original-X geometric existence condition.

## Pinned formal verification receipts

- **Lean compiled, no sorryAx:** `GSTFullWaveCyclicSourceCommutant.lean` at `445f59254c4a1f1ddb72954c14b0d8c84c2b3eaf`, GitHub Actions [run 42733556685](https://github.com/kyo-oo/HC-PROOF/actions/runs/42733556685), completed SUCCESS. This is the arbitrary rational-module theorem that a cyclic source and its nondegenerate source-rank-one coupling have only scalar common commutant; it is NOT a formalization of the all-N resultant or original-X Chow realization.
- **Connected curvature closure:** one prior root-registered build [run 42729969001](https://github.com/kyo-oo/HC-PROOF/actions/runs/42729969001) found a single Lean function-extensionality reduction failure in `all_channels_have_native_cycles`; code was corrected at `5632c21982ed37ade1d014859ab68185ff60a6be`. Its fresh current-revision run [42733664221](https://github.com/kyo-oo/HC-PROOF/actions/runs/42733664221) was still running at this record update. Do not label it successful without the job conclusion.
