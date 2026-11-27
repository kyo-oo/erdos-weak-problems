# GST exact two-center fold from the SAME alpha-topological spatial bundle: remove unnecessary test-map integrability

- **Date:** 2026-10-24 IST; active branch `research/gpt6-native-point-primitive-span-20261017`.
- **Correct continuation of:** [2026-10-24 full causal-Hodge source review and original-X smooth degeneracy theorem](2026-10-24-gst-original-alpha-same-fold-determinantal-rees-return-and-source-review.md).
- **Actual mathematics edited:** [original alpha-exponential spatial-fold manuscript](../derivations/GST_universal_spatial_fold_exponential_geometric_realization_2026-10-23.tex), commit `40542be0cde153f7fba1fcdf237e9fa21f9b059b`; same fold used throughout; not a detached test-variety module.
- **Target remains:** given any original smooth projective X, p, prescribed rational Hodge alpha, independently produce an actual original-X Chow class with canonical Betti alpha, without requiring its Chow representation as input.

## New single-geometry conditional constructor

The FULL original alpha-selected topological spatial fold was already proved: there exists a rank-r complex topological bundle `E_alpha` on original X, r>=p+1, with ch_top(E_alpha)=r+m alpha, and its projectivized spatial fold has `pi_* xi^(r−1+p)=m(p−1)!alpha`. The new same-geometry smooth degeneracy theorem builds from that SAME E_alpha a smooth rank-drop pseudocycle `D_alpha^sm` on original X with PD=(-1)^(p−1)m(p−1)!alpha. This produces the target original-X topological geometric source without ANY Chow assumption.

The earlier first algebraization route required two independently stated properties of an arbitrary chosen smooth test map: `bar∂_E²=0` and `bar∂_E Phi=0`. The new theorem **removes the second assumption completely** and constructs the algebraic determinant map FROM THE SAME E_alpha, once the genuinely central integrability input `bar∂_E²=0` holds.

If SAME E_alpha becomes holomorphic, projective GAGA gives a genuine algebraic vector bundle `E_alpha^alg`. Fix ample H, `h=c1^CH(H)`, and k sufficiently large that `E_alpha^alg⊗H^k` is globally generated. Choose s=r−p+1 general genuine algebraic global sections; their maximal-minor rank-drop scheme `D_(alpha,k)` is pure of complex codim p, and algebraic Thom–Porteous gives `[D_(alpha,k)]=c_p^CH(E_alpha^alg⊗H^k)`. This is an ACTUAL closed algebraic original-X geometry selected from E_alpha, not merely a formal Chern-image compiler.

The EXACT universal Chern-root identity in real Chow is
   c_p^CH(E_alpha^alg⊗H^k)
    = sum_(j=0)^p binom(r−j,p−j) c_j^CH(E_alpha^alg) (k h)^(p−j).
The imposed pure topological ch equation gives `cl^can(c_j(E_alpha^alg))=0` for 1<=j<p, and `cl^can(c_p(E_alpha^alg))=(-1)^(p−1)m(p−1)!alpha`. **Those lower Chern classes need NOT vanish in Chow**, only in canonical rational Betti. Therefore in Betti,
   cl^can[D_(alpha,k)]
   =(-1)^(p−1)m(p−1)!alpha + binom(r,p) k^p cl^can(h^p).
This leads to one explicitly signed actual original-X cycle from TWO genuine algebraic centers:
   Z_alpha = (-1)^(p−1)/(m(p−1)!)
        * ([D_(alpha,k)] − binom(r,p) k^p [H^p]),
where `[H^p]` is an actual p-hyperplane complete-intersection cycle. Then
   cl_X^can(Z_alpha)=alpha EXACTLY.

Both centers have ACTUAL algebraic ideals and actual same-polynomial Rees/normal-cone causal folds. Determinantal ideal need not be local complete intersection, so the simplistic smooth-center exceptional-power pushforward formula is NOT invoked without checking regular embedding.

## Mathematical strengthening and correct unresolved scope

This algebraic construction is now genuinely **only conditional on one substantive analytic-geometric integrability requirement for the SAME alpha-selected E_alpha**, rather than imposing the holomorphicity of a separately chosen smooth section map. It does NOT itself prove that every higher-primitive rational Hodge input automatically supplies such integrability; using this requirement as a new axiom would be circular.

The equality `c_j^{CH}=0` is NEVER assumed for the low grades, only `cl_X^{can}(c_j)=0`, and the correction acts on actual original-X cycles. The approach starts from the full GST pre-dimensional causal and exponential spatial source structure, not disconnected CM, quadric, K3 or other worlds.

## Actual exact symbolic test

Stateless Wolfram exact rational-symbolic audit checked the normalized projective/twisted sign formula for p=1,...,8 and r=p+1,p+2,p+3 (24 rank-grade combinations): every check returned True; e.g., `p=4,r=6` ambient binomial correction is 15 k^4 h^4 and all lower Chern Betti components vanish under the source law. These finite checks only certify the formula implementation in the stated range; the exact general p/r identity follows from the splitting principle and the original Chern character theorem.

## Proof type/provenance

Named standard geometric theorems used: Koszul–Malgrange and projective GAGA, Serre global generation under ample twist, Thom–Porteous expected-codimension degeneracy, rank-degeneracy transversality, splitting-principle Chern-root twisting, canonical Chow-Betti cycle class compatibility, actual deformation-to-normal-cone existence. Mathbox author self-audit, not independent referee. LaTeX theorem/proof source committed; no Lean file changed or GH Actions run claimed. The acceptance target of arbitrary algebraic integrability remains open.
