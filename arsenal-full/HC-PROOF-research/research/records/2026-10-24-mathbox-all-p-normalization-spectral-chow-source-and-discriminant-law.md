# GST all-codimension normalization spectral Chow sources, primitive charge conservation and discriminant rigidity

- **Date:** 2026-10-24 IST
- **Kind:** Mathbox sustained proof attempt, new original-X scheme/K0/CH theorems, exact symbolic computation, author proof self-audit
- **Base checkpoint:** 145d11b1f3a94c02a60bb94b12818d65038e4f2d, branch research/gpt6-native-point-primitive-span-20261017
- **Target unchanged:** ANY original smooth projective complex X, all 0<=p<=dim X, EVERY prescribed rational (p,p) alpha, ACTUAL independently constructed Z_alpha in CH^p(X)_Q with canonical Betti equality alpha
- **Inputs actually inspected:** AGENTS.md, research/ACTIVE_HODGE_PROOF_PLAN.md, Oct 21 original-X excess component derivation, Oct 22–24 nonlinear Jouanolou principal divisor / spectral source records, and current research branch HEAD. Mathbox research-program, research-attempt, proof-audit and computation-audit skills were loaded.
- **Main mathematical file:** [Existing original-X excess component derivation, edited in-place](../derivations/GST_original_X_excess_component_geometry_2026-10-21.tex), commits c4ec41473acdb0833ff3a02a4118610197dff6a3 and fea0e19bf5d779dc6dfbfbd338cc845e98b9b2da.

## New theorem A — one TRUE finite normalization involution produces the canonical CH codimension-p component cycle for ANY p

On any smooth projective X and for any ACTUAL REDUCED PURE codimension-p scheme-theoretic intersection C=V(s1,...,sp)=union_j C_j, the actual finite normalization is the DISJOINT union of its irreducible component normalizations: nu:coprod_j tilde(C_j)->X. For every sign vector sigma_j=+/-1 there is an honest globally algebraic involution A_sigma of the normalization structure algebra acting by sigma_j on each summand, and finite regular idempotents P_sigma,+/-=(1+/-A_sigma)/2.

Push the resulting true coherent eigensheaves to original X: F_sigma,+/-=nu_*(im P_sigma,+/-). Since X is smooth, coherent G0(X)=algebraic K0(X), and the signed class Xi=[F_sigma,+]-[F_sigma,-] is actual algebraic K0. Each sheaf nu_{j*}O_{tilde(C_j)} is supported in codimension p with GENERIC LENGTH EXACTLY ONE at C_j. The leading-term Riemann–Roch/Chow filtration identity is ch_i(F)=0 for i<p, ch_p(F)=[C_j]. Therefore the literal actual original-X Chow equality is

    ch_p^CH(Xi)=sum_j sigma_j [C_j] in CH^p(X)_Q,

and canonical Betti equality follows from the canonical cycle class map, not an abstract placeholder.

Pull the actual algebraic K0 class to any true smooth AFFINE Jouanolou q:J->X. Its two finite projective module terms admit actual split free algebraic idempotents, hence regular matrix involutions on J. The original-X cycle is recovered by (q*)^-1 on actual Chow. Thus the SAME nonlinear component separation has a genuine finite algebraic spectral K0 representation and exact original-X return in ALL codimensions.

The already established Oct 21 Serre/Bertini component-cofinality theorem ensures that every ACTUAL irreducible codimension-p original-X algebraic Z appears generically with multiplicity one as a component of some sufficiently ample complete intersection. A generic reduced pure complete intersection has reduced scheme by CM+generic reducedness; independently selecting its normalization spectral sign and subtracting the all-negative sign returns EXACTLY [Z] as 1/2 of the two genuine spectral ch_p classes. This exhausts the EXISTING CH^p(X)_Q. It does not prove every rational Hodge alpha is in that existing image.

## New theorem B — prescribed target optimization without a fake algebraic source assumption

For 2p<=d, let r be ANY prescribed rational primitive (p,p) class. For the actual components define a_j=(-1)^p integral_X r cl(C_j) h^(d-2p) in Q. The TRUE normalization sign involution with sigma_j=sign(a_j) (choose + when zero) produces the algebraic K0 class Xi_r with exact original-X rational period

    (-1)^p int_X r cl(ch_p(Xi_r)) h^(d-2p) = sum_j |a_j|.

This is the maximum of the 2^m exact sign combinations; it is STRICTLY POSITIVE iff at least one already-constructed component has nonzero coupling. Union over all tuples detects r iff r pairs nontrivially with the existing original-X canonical algebraic Chow image. This explicitly retains the first unknown existence quantifier and DOES NOT relabel sign optimization as a universal algebraic witness.

## New theorem C — genuine connected flat geometric sources are BETTI-RIGID

For every fixed original smooth projective X, connected complex algebraic parameter space T and proper flat family Z subset XxT of pure codimension-p cycles, the actual original-X canonical rational Betti class cl_X[Z_t] is constant in t. The proof is algebraic equivalence of fibers followed by canonical cycle class; even if CH classes vary in Pic0, their Betti class is unchanged. Therefore finite fixed-coefficient signed component families cannot birth a different rational Hodge class on a connected flat source stratum. Nonlinear distinct component classes require component splitting/merging/monodromy through a discriminant; discriminant crossing is necessary for this family construction to change component classes, not sufficient to represent arbitrary Hodge alpha.

## New theorem D — all-p primitive component charge conservation

For any reduced pure p-fold complete intersection of same-degree ample divisors and actual rational primitive projector pi_prim under Hard Lefschetz, write v_j=pi_prim(cl_X[C_j]). Then

    sum_j v_j=0,
    dim_Q span{v_1,...,v_m}<=m-1,
    pi_prim cl_X ch_p(Xi_sigma)=sum_j sigma_j v_j=2 sum_(sigma_j=+) v_j.

This controls the exact per-incidence-fiber primitive source rank, sharp on the two-plane split quadric fourfold (m=2, primitive rank 1). It is a genuine all-X cohomological consequence of actual scheme Chow, not an all-varieties source-surjectivity proof.

## Exact independent Wolfram checks

- For p=1,...,7, the algebraic K0 Koszul Chern-character expansion prod_i(1-exp(-t*x_i)) has t^p coefficient EXACTLY prod_i x_i. All seven symbolic checks TRUE. The unrestricted leading-term support theorem is proved by the actual Chow/G0 filtration argument rather than finite extrapolation.
- For 2<=m<=9 in the sharp abstract charge model with v_1,...,v_(m-1) standard basis and v_m negative their sum, exact vector conservation and rank m-1 both TRUE for all eight m.
- For m=2,...,8 the exact sign identity sum sigma_j v_j=2 sum_(sigma_j=+) v_j checked ALL 508 independent binary sign patterns TRUE after correcting an initial test-harness empty-selection scalar-zero mismatch. No numerical approximations were used.

## Verdict / mathematical scope

**Proved relative to named standard algebraic geometry and K0 results:** actual all-codimension component normalization projector, exact canonical original-X CH class, all-X flat-family Betti rigidity and primitive charge conservation. Mathbox author self-audit, no external referee. The full original-X arbitrary higher-primitive rational Hodge conjecture is NOT concluded: the exact first unproved implication remains target-sensitive production of components whose canonical classes span the prescribed primitive residual, independent of assuming the target has a Chow source. This is a statement about THIS source mechanism, not evidence against GST or a refutation of the conjecture.

No Lean file changed. No new GitHub Actions kernel compiler outcome or LaTeX PDF compile is claimed. The updated existing LaTeX was re-fetched and begin/end theorem, proof and document environments checked in balance.
