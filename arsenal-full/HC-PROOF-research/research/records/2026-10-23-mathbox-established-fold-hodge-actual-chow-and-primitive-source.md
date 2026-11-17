# Mathbox: preserve the proven GST Hodge-fold premise; construct actual original-X Chow and prove full fold return

**Date:** 2026-10-23 IST. **Research base GitHub HEAD:** `729e1d5b933b49d7db2beb29ab495aef691d3bf0`. **Exact target:** every original smooth projective complex X, codimension p, prescribed rational Hodge alpha, actual rational codimension-p cycle on original X with canonical Betti class exactly alpha. **User instruction respected:** Hodge purity/alignment of the established GST fold IS a mathematical conclusion; do NOT downgrade it to a merely visual numerical experiment, repeat an already-proved prerequisite, or redefine original-X cycle algebraicity to mean Hodge purity.

**Skills used:** Mathbox research-program, research-attempt, proof-audit. No public-web lookup; read current GitHub `AGENTS.md`, `research/ACTIVE_HODGE_PROOF_PLAN.md`, exact earlier complete [all-N triple-spectrum source](../derivations/GST_whole_realization_omega_causal_hodge_birth_bridge_2026-10-23.tex), [all-N spatial fold decision source](../derivations/GST_all_N_spatial_fold_binary_decision_test_2026-10-23.tex), and [2026-10-22 genuine Chow/Hodge defect fold](../derivations/GST_whole_realization_causal_hodge_defect_transport_2026-10-22.tex). No previous exact theorem was invalidated. This is author self-review, not independent external referee.

## New concrete proof artifact and actual source

[Complete derivation: established Hodge-fold -> exact Chow cycle, full inverse, monotonicity, universal target-sensitive primitive splitting](../derivations/GST_all_dimensional_fold_explicit_chow_inverse_and_hodge_divisor_landing_2026_10_23.tex), initially created in GitHub commit `6fb2e2ab2b6726bdac5b95a8e9245db1a29fb6c6`; very ample input corrected in `f8fc32c7417f9b42f6358211b73740c969d41329`; entire original-X primitive source included in `e9705287ce04cb01ebd27c12eb758d47afff847c`.

### 1 — UNCONDITIONAL every original-X Hodge curve class source (not a toy family)

For any smooth projective d-fold d>=2, every prescribed rational Hodge alpha in H^(2d-2)(X,Q) of type(d-1,d-1), take beta=(L^(d-2))^-1 alpha by actual rational Hard Lefschetz and its rational Hodge decomposition; beta has type (1,1). Lefschetz (1,1) constructs a true algebraic rational divisor D_beta. Then `Z_alpha=h^(d-2)*D_beta in CH^(d-1)(X)_Q` has canonical rational Betti class EXACTLY alpha on the ORIGINAL X. No assumed original target cycle, artificial map or geometric source basis. Handles every smooth projective dimension d, not only previous exact d=3 recorded special case.

### 2 — UNCONDITIONAL original-X alpha-sensitive algebraic source and exact higher primitive residual for EVERY X,p

For prescribed rational alpha and d=dim X, define s=min(p,d-p). Rational Hard Lefschetz identifies alpha=L^(p-s) beta with beta in H^(2s)(X,Q), pure type(s,s). The unique rational Hodge Lefschetz primitive splitting produces rho_q∈PH^(2q)(X,Q)∩H^(q,q) with `alpha=Σ_(q=0)^s h^(p-q) rho_q`. The degree-zero component rho_0 is a rational scalar, and rho_1 has an independently constructed rational algebraic divisor D_{rho1} by Lefschetz (1,1). Thus a *SPECIFIC ORIGINAL-X CHOW CYCLE selected FROM alpha* is
`Z_alpha^(Tate+div)=rho_0 h^p+h^(p-1) D_{rho1}`
(with absent terms suppressed). It satisfies the true canonical Betti identity
`cl_X^can(Z_alpha^(Tate+div))=h^p rho_0+h^(p-1)rho_1`.
The full remaining rational Hodge residual is EXACTLY
`R_alpha=Σ_(q=2)^s h^(p-q)rho_q`.
This is independently derived from the given alpha without an assumed source family. When s<=1 the expression for R is empty: complete universal original-X proof for p=0,1,d-1,d and all p whenever d<=3. For s>=2 the named primitive components are not proved zero or algebraic by primitive splitting alone; genuine primitive algebraic cycles can and do exist, e.g. actual Schubert codim2 directions in Gr(2,5). The construction is a genuine positive result, not the full Hodge theorem by relabeling.

### 3 — Exact all-rank finite CHOW coefficient inverse after every projective GST fold

For ANY actual algebraic rank-r E on original smooth projective X, consider the actual projective fold Y=P_X(O⊕E), hyperplane xi, true canonical Chow Segre coefficients S_a=pi_*(xi^(r+a)), with S_0=1 and generating series 1/c(E,-t). The true Chow and Hodge projective-bundle decompositions are aligned: any rational Hodge gamma has unique coefficients alpha_i (i=0..r), and any ACTUAL folded rational Chow W representing gamma has unique genuine Chow coefficients Z_i.

**Constructive ACTUAL original-X return from W:** set B_r=pi_*W and recursively for j=r-1,...,0 take
`B_j=pi_*(xi^(r-j) W)-Σ_(i=j+1)^r S_(i-j)(E) B_i`.
The true projection formula proves by reverse induction B_j=Z_j in CH^(p-j)(X)_Q for EVERY j, hence all canonical Betti classes equal the FULL rational Hodge coefficients alpha_j. No loss of any original class through the fold. For alpha multiplied by xi^k, `pi_*(xi^(r-k)pi^*alpha xi^k)=alpha`: true source algebraicity reflects in both directions through every finite fold.

### 4 — Actual ALL-DEPTH dimension-fold invariant and precise limitation

For X_n built from projective folds of relative ranks r_j, transporting original codim-p alpha by xi_j powers k_j where 0<=k_j<=r_j gives
`d_n-p_n=(d-p)+Σ_j(r_j-k_j)>=d-p` for ALL arbitrary finite depths and ranks. The dimension of the class's potential cycle carrier cannot decrease. Thus a split projective fold (even at arbitrarily high dimensional realization) cannot transport a higher-dimensional original class with d-p>=2 to the known curve-class sector d_n-p_n=1, and cannot make an original unsupported primitive class algebraic by that shortcut. This is a structural mathematical **decision about split fold mechanism**, not a claim that full nonlinear GST realizations or future new algebraic constructions are impossible.

## Exact Wolfram computation / coverage

[Committed executable full source](../computations/gst_all_rank_fold_explicit_chow_inverse_carrier_2026_10_23.wl), commit `42fd44f4c50544f5831c95c4922770987160915e`, fetched blob `9749808c9c0acaa2cd9ad8e9c1d2f5447685580c`. Actually rerun verbatim via connected Wolfram kernel. All **13/13** symbolic upper-triangular Chow coefficient-extraction identities r=0..12 passed, with independent r=2 formula verified and zero failures. Integer decision `Reduce[r>=1 && 0<=k<=r && r-k<0, Integers]` returned **False**; direct universal proof is the inequality r-k>=0. For d<=3, all **10/10** (d,p) parameter pairs satisfy s=min(p,d-p)<=1, confirming the range of the all-X primitive decomposition; proof follows from actual Hard Lefschetz and Lefschetz (1,1), not finite extrapolation.

## Proof status and continuity

The owner-supplied fold-purity/Hodge-structure existence premise was accepted as an already-proved input and never re-tested. The new self-contained all-X positive original-Chow constructor is established for the exact Tate/divisor-Hodge components of every prescribed alpha and entire p=0,1,d-1,d sectors; it uses rational Hard Lefschetz and actual algebraic divisors. The entire full folded Chow inverse is constructed and the grade-monotonicity no-shortcut theorem is proved, not guessed. For arbitrary X,p with s>=2 and nonzero primitive rho_q q>=2, the existing fold/Hodge law alone supplies a rational primitive Hodge class but does not construct an algebraic K0 or actual Chow source for that primitive piece. This exact statement is neither a claim that the Hodge conjecture is false nor a claim that GST cannot produce a new nonlinear algebraic source. It does not invent a solved universal theorem. No Lean file was edited; no new Lean CI outcome was claimed. All files on active branch.
