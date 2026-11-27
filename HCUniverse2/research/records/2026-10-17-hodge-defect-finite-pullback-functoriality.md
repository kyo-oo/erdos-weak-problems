# Mathbox — Hodge-defect functoriality under finite geometric descent

- **Date:** 2026-10-17
- **Kind:** mathematical derivation and exact linear-algebra audit
- **Target:** Build algebraic representatives for all rational primitive Hodge classes on an arbitrary smooth projective complex variety X. This route develops a quantitative, correspondence-stable invariant that identifies exactly how much source geometry a finite-degree transfer must supply.
- **Hypotheses and types:** Genuine proper generically finite f:Y→X of degree d≠0 between smooth projective complex varieties of the same dimension, all codimensions p, rational singular Betti classes and algebraic cycles. Pullback on cohomology and Chow, pushforward on Chow/Betti, and naturality with canonical cycle class. Let V_X^p=H^{2p}(X,ℚ)∩H^{p,p} and A_X^p=im(cl_X:CH^p(X)_ℚ→V_X^p).
- **Active conventions:** The rational defect space D_X^p=V_X^p/A_X^p; similarly D_Y^p. Finite-dimensional rational vector spaces. f^* is type- and Hodge-preserving. The full rational primitive part follows by taking the primitive summand after Lefschetz algebraic correction.
- **Current dependency/evidence status:** New Lean file GSTFiniteDominantAllCodimensionDescent.lean includes constructive degree-descended native cycles, the exact algebraic-iff-pullback-algebraic criterion, and projective-bundle finite-image composition. CI checkpoint #39028790599 was running when this entry was created. Earlier run #39028268013 exposed a typing error in the projective bundle inclusion application, repaired in commit 8940a21d2f0438fdf3f6ec7d4077d868ab935a7c.
- **Nearest prior attempt and first unresolved implication:** Fermat maximal-plane generators produce complete Hodge representatives on the special cubic family. Arbitrary-X extension requires a geometric mechanism supplying actual classes on a source Y with a certified proper map to X. The finite-degree criterion now provides a quantitative test of each proposed Y.
- **Route:** Prove algebraicity is exactly preserved/reflected by finite pullback and derive a rational defect-space injection from that equivalence.
- **Mechanism and derivation:** Projection formula f_*f^*=d id and naturality show
  A_X^p=(f^*)^{-1}(A_Y^p)∩V_X^p.
  Indeed f^*cl_X(Z_X)=cl_Y(f^*Z_X) proves forward inclusion. If f^*α=cl_Y(Z_Y), then α=cl_X(d⁻¹f_*Z_Y). Hence pullback induces a well-defined **injective** rational map
  \[
   \bar f^*:D_X^p=V_X^p/A_X^p\longhookrightarrow
          D_Y^p=V_Y^p/A_Y^p.
  \]
  In particular dim_ℚ D_X^p ≤ dim_ℚ D_Y^p. The same classwise argument handles primitive Hodge directions, provided the primitive comparison uses the genuine chosen polarizations.
- **Holomorphic-source compatibility:** Proper generically finite pullback is injective on H^{k,0}. Wolfram evaluated exact Jacobian-ring Hodge invariants h^{2,0}(smooth cubic surface)=0 and h^{2,0}(smooth quartic K3)=1, and h^{4,0}(smooth sextic fourfold)=1. This identifies the next positive source family: sources with actual holomorphic-form sectors matching the target, e.g. K3 surfaces and their projective bundles rather than only Fano cubic hypersurfaces.
- **Cheapest decisive check:** Exact rational push-pull toy model E=ℚ⁴, E'=ℚ⁶, degree d=5, f^*=inclusion, f_*=5·projection. Algebraic subspaces A_X=span(e₁,e₂), A_Y=span(e₁,e₂,e₅). Wolfram output: push-pull=5Id; rank A_Y=3; rank f_*A_Y=2; defect rank 2 on X, and 2 independent defect classes after pullback. This checks the quotient injection and shows the arithmetic difference between ambient algebraic classes and primitive targets.
- **Success criterion:** Establish the algebraic preimage equality and defect injection in every codimension from actual geometric maps, and identify source invariants needed for extending all-X primitive cycles.
- **Failure/no-go criterion:** Any proposed generic finite transfer that changes rational defect rank in the forbidden direction, or maps from a source with H^{k,0}=0 to a target with nonzero H^{k,0}, cannot instantiate the certified geometric correspondence.
- **Attempt outcome:** Exact mathematical functoriality theorem and usable source-selection criterion, extending the constructive all-p transfer. The source-target map remains a separately supplied genuine geometric morphism; the all-X original theorem requires further native cycle production.
- **Route disposition and scope:** Structural route succeeded; next work is geometric construction of suitable Y/f and verified primitive measurements on arbitrary X.
- **Continuations:** Try K3-derived and Calabi–Yau-derived source families with projective bundles and correspondences; develop actual GST integral geometric replacement on X when dominant source matching is unavailable.
- **Evidence label:** Ordinary exact algebraic proof from canonical Chow/Betti functoriality. Wolfram checks finite test case and Hodge-number examples. Lean all-codimension algebraicity equivalence committed; latest dedicated Actions status to reconcile.
- **Review and freshness status:** Mathbox self-review; source branch research/gpt6-native-point-primitive-span-20261017; recent commit 8940a21d2f0438fdf3f6ec7d4077d868ab935a7c; status of #39028790599 at last observation in progress.
- **First unresolved implication:** Produce certified native algebraic source generators that span each rational primitive Hodge sector on every original X, possibly via a non-dominant GST construction when holomorphic-form invariants rule out Fermat-only source transfer.
- **Strongest surviving statement:** Complete all-p algebraic-image pullback reflection and injective Hodge-defect quotient under finite dominant maps; exact projective bundle/finite-image cycle construction on target.
- **Artifacts and commands:** GSTFiniteDominantAllCodimensionDescent.lean, .github/workflows/gst-finite-dominant-all-codim.yml, Wolfram exact rational matrices and Jacobian-ring coefficient computations.
- **Next unresolved question:** Can GST construct Hodge-compatible source cycles or integral-current surgery directly on arbitrary X, without first assuming its rational primitive Hodge representatives?
