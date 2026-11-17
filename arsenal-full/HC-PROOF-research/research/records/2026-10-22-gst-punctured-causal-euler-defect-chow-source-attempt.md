# GST punctured causal bundle: exact Euler defect and original-X Chow correction

- **Date:** 2026-10-22 IST
- **Kind:** Mathbox research-attempt, proof-audit self-review, exact Wolfram computation
- **Program:** Universal original-X rational Hodge algebraicity.
- **Base checkpoint:** `39846a39cae34cfe0651881b11d01a01c428590f` on `research/gpt6-native-point-primitive-span-20261017`.
- **Exact target:** Given every smooth projective complex original X, every codimension p and rational (p,p) alpha, construct Z_alpha in CH^p(X)_Q with canonical Betti class alpha. The selected route first seeks an actual *independent* algebraic representative of the pulled-back target on a geometric causal fold.
- **Nearest prior record:** [Exact projective-bundle Chow extractor + incidence-source attempt](2026-10-22-gst-projective-fold-native-incidence-chow-residue-source-attempt.md), at HEAD `39846a39`, already proves section return and honest nonambient curve-pair incidence cycles. This attempt deliberately avoids rederiving those results.
- **Distinct geometric input:** Algebraic **punctured total vector bundle** U=Tot(E) minus the zero section, a smooth quasi-projective predecessor of the compact nonalgebraic Hopf quotient. This gives a genuine localization Chow group, unlike the compact Hopf fold.
- **Geometric hypotheses:** Connected smooth projective X, any actual algebraic rank-r bundle E (r>=1); `e=c_r(E)`; p>=0. Disconnected X follows by componentwise direct sums.
- **Mechanism:** Exact Chow closed-open localization plus homotopy-invariance and self-intersection, rational sphere-bundle Gysin, canonical cycle-class functoriality, and semisimplicity of polarizable pure rational Hodge structures.
- **Success criterion:** An algebraic Γ_U with cl_U Γ_U = ρ*alpha produced *independently* for every alpha, followed by explicit native Chow return.
- **Failure/no-go discriminator:** Does the punctured causal fold itself enlarge the algebraic source image enough to supply the prescribed target, or merely quotient it by Euler multiples?
- **Attempt outcome:** The exact all-X structural theorem and explicit correction are proved in mathematics-first LaTeX. The proposed punctured-fold-only source creation does not produce universally new algebraic classes: its Chow group is a quotient of Chow(X), and any first possible missing Hodge class survives in the inherited open quotient.
- **Evidence label:** proved for paired localization, defect exactness, first-defect survival and conditional explicit Chow correction; general prescribed independent Γ_U remains unconstructed.
- **Route disposition:** punctured-fold-only source mechanism closed as insufficient, independent non-split incidence/moduli/algebraization route remains open.

## New exact mathematical identities

Write H_X^p for rational (p,p)-Hodge classes, A_X^p for canonical image of CH^p(X)_Q, D_X^p=H_X^p/A_X^p. For U=Tot(E)\0_X and ρ:U->X, Chow localization and Betti Gysin yield

`CH^(p-r)(X)_Q --c_r(E)*--> CH^p(X)_Q --ρ*--> CH^p(U)_Q -> 0`,

`ker[H^(2p)(X,Q) -> H^(2p)(U,Q)] = c_r(E) cup H^(2p-2r)(X,Q)`,

and the genuine Chow class image on U equals `ρ*A_X^p`.

Define the inherited U defect `D_inh^p(U)=ρ*H_X^p/cl_U CH^p(U)_Q`. A strict rational Hodge-preimage argument using semisimplicity of polarized pure rational Hodge structures proves the **exact** sequence

`D_X^(p-r) --c_r(E)*--> D_X^p --> D_inh^p(U) --> 0`,

so `D_inh^p(U) ≅ D_X^p/(c_r(E)*D_X^(p-r))`.

**First-defect survival:** for the least p with nonzero D_X^p (if any), the map D_X^p -> D_inh^p(U) is an isomorphism for every rank r>0. Also true for every r>=p, since codimension-zero defect vanishes and negative ones are zero. This is a precise geometric invariant of the causal topology mechanism, *not* a universal-algebraicity theorem.

**Actual corrected original-X cycle conditional on independently constructed geometric Γ_U:** If `D_X^(p-r)=0` and an actual Γ_U in CH^p(U)_Q satisfies cl_UΓ_U=ρ*alpha, any Chow lift W from localization obeys `alpha-cl_X W=cl_X(c_r(E)) cup gamma` with gamma a rational (p-r,p-r)-Hodge class. Choose B in CH^(p-r)(X)_Q with cl_X B=gamma, and set `Z_alpha=W+c_r(E)*B`. It is a genuine codimension-p rational algebraic cycle with the exact prescribed canonical Betti class. For r=p, B is a scalar and the output is `W+lambda c_p(E)`, computable from a rational dual functional.

The input Γ_U is **not** obtained from Hodge purity, rational KU, localization, or Hopf parity. Supplying it for arbitrary middle alpha would itself be an original-X universal source theorem. No stronger claim is made.

## Executed exact computation

- [Uniform mathematics-first derivation](../derivations/GST_punctured_bundle_causal_chow_defect_exact_sequence_2026-10-22.tex), source commit `d506a1f7e412cd79aec87a1392c1052f7ac9c77e`.
- [Wolfram stateless exact source](../computations/gst_punctured_causal_euler_defect_exact_2026_10_22.wl), source commit `c4d1d3fea4ff71a89d47fdfa314765168bc1aaa6`, blob `28b1304d7f12e81dbbbb202327685ef215eb6dea`. Source was fetched back verbatim from GitHub and re-executed using WolframLanguageEvaluator.
- **Observed result:** `projectiveSpaceCases=1485`, `projectiveSpacePass=True`, `rationalDefectModels=81`, `rationalModelsPass=True`, `failedModelInputs={}`. The model checks exact dimension/rank identities for maps preserving a stipulated algebraic subspace; they do not test the existence of geometric Γ_U on all X.
- **Verification:** self-reviewed complete mathematical derivation under standard Chow localization, Gysin and Hodge semisimplicity; no Lean files changed, no scheme-level Lean formalization or new GitHub Actions run claimed.
- **Next exact construction input:** a genuine non-split algebraic incidence/moduli/perfect-complex class Γ_U with `cl_UΓ_U=ρ*alpha` or one detecting the original prescribed residual, independently constructed for every arbitrary smooth projective original X. The punctured/Hopf topology alone is demonstrably insufficient.

**Uniform caution:** This is a successful all-X theorem about the defect propagation under *this actual family of folds*. It neither implies absence of rational Hodge counterexamples on smooth projective X nor yields a universal original-X Chow representative without Γ_U.
