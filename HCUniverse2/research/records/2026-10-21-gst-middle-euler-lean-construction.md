# GST middle Euler construction: Lean implementation and remote verification

Date: 2026-10-21 (Asia/Calcutta).
Base: d34b0a248ae9f54500bf7c3e78f1cf612d4c5e18 on research/gpt6-native-point-primitive-span-20261017.

## Exact target and implementation

Continue the 691-line middle-world arithmetic derivation into the existing GST Lean modules, with remote GitHub Actions compilation. The original universal target remains actual rational algebraic cycle representatives of every rational Hodge class on every original smooth projective complex X.

- GSTGraphV2SelfExpandingCosmology.lean: constructive denominator-separated Newton source for the finite normal correction; nilpotent error factorization; exact square-root/Segre cancellation; preservation of the native subalgebra in both directions; signed Euler trace normalization; primitive-coordinate positive polarization; discriminant arithmetic.
- GSTActualXHodgeResidualProjection.lean: measured matrix of ACTUAL original-X source cycle classes, explicit inverse-weighted native cycle, and exact cycleClass correctness from a verified matrix inverse or nonzero determinant.
- GSTK3PrimitiveGram.lean: exact M=5 duality/exceptional sign calculation, native diagonal Euler index 21 and native Euler Gram determinant 63*d^2.

No new Lean files or global axioms; no sorry/admit placeholders. These are proof submissions, with compiler status pending until observed below.

## Constructive mathematical upgrade

Let s be the actual Segre class, with (1-s)^c=0. Define rational denominators d_0=1, d_(n+1)=2*d_n^3 and numerator polynomials r_0=1, r_(n+1)=r_n*(3*d_n^2-s*r_n^2), interpreting rational d_n in the cohomology/Chow algebra. The integral polynomial identity is
  d_(n+1)^2-s*r_(n+1)^2=(d_n^2-s*r_n^2)^2*(3*d_n^2+(d_n^2-s*r_n^2)).
Thus the defect is divisible by (1-s)^(2^n). Since 2^c>=c, R=d_c^(-1)*r_c satisfies s*R^2=1. This CONSTRUCTS the normalizer from nilpotence; it does not hypothesize its existence. When s*c(N)=1, R^2=c(N). Every intermediate numerator and R stay in the native rational characteristic-class algebra. R*a is native iff a is native.

## Audited geometric boundary

Self-review of the implication 'positive middle integer Euler index implies algebraic realization': incomplete, with the exact missing implication being algebraization of the explicit topological K packet. Positive topological pairing has a partner in topological K; that partner is not automatically an algebraic perfect complex. The native inverse-matrix theorem consumes ACTUAL algebraic source columns. It does not supply them universally.

Formalization scope is explicit: the new Graph section proves rational algebra and finite coordinate polarization. The geometric topological KU/Gysin/GRR comparison and full Hodge--Riemann statement are not newly formalized by defining a trace polynomial. The discriminant lemma consumes det(S)=1; its geometric unipotent-grading proof is in the manuscript. The ActualX compiler uses the repository's exact Mathlib cycle type and supplied Stage-2G cycleClass; independent canonical semantic realization remains the existing Gate 1 obligation. A successful build must not be reported as the full Hodge conjecture.

## Computation

Wolfram independently expanded both rational and denominator-separated Newton error identities to zero. Eighteen exact truncated projective-normal models, dimensions 0..8 with M=d+1 and M=2d+3, verified both s*R^2=1 and equality with the finite binomial normalizer. Source/output files are alongside this record under research/computations.

## Compilation

The following revision-matched checks have completed successfully:

| Check | Verified code revision | Result |
|---|---|---|
| Complete Chern–Segre–Newton arithmetic | 4f2cdd7be1a5e9d10108035b501ba399ca95c8a1 | [GREEN #39483532547](https://github.com/kyo-oo/HC-PROOF/actions/runs/39483532547) |
| Full pinned integration, including the actual-X compiler | 4f2cdd7be1a5e9d10108035b501ba399ca95c8a1 | [GREEN #39483532335](https://github.com/kyo-oo/HC-PROOF/actions/runs/39483532335) |
| Standalone original-X native projection and compiler | db37a836047167112598167727833b107a6bce7a | [GREEN #39484913997](https://github.com/kyo-oo/HC-PROOF/actions/runs/39484913997) |
| K3 native Gram and Euler index | 4715410811cb32e2fd83a0d90611d3adf1fb8214 | [GREEN #39482156988](https://github.com/kyo-oo/HC-PROOF/actions/runs/39482156988); K3 source blob unchanged at final code revision |

The standalone ActualX workflow is also **GREEN**: [#39484913997](https://github.com/kyo-oo/HC-PROOF/actions/runs/39484913997), pinned at db37a836047167112598167727833b107a6bce7a. It verifies BOTH the directed-cut prerequisite and the native projection/certificate library, including the final Graph arithmetic. The prior cold standalone run #39482736893 was cancelled and superseded by this successful cache-enabled run. The same ActualX source also passed pinned runs #39482737165 and #39483532335.

The initial pinned run #39482156974 at 4715410 exposed exactly one compiler API mismatch: Matrix.mul_nonsing_inv requires IsUnit(det), whereas hDet supplied det!=0. The minimal repair is isUnit_iff_ne_zero.mpr hDet over Q. The repaired and final full integration runs are GREEN; no mathematical premise or theorem statement was weakened.

Commands: existing Graph and K3 workflows invoke lake build on their named libraries; the pinned gate runs scripts/gst_lean_dependency_roots.py and lake build GSTPinnedHodgeGeometricGate, plus the existing exact arithmetic/geometric computations. Their sorry/sorryAx guards passed. No local Lean installation or local compilation was used.

Verified final code source blobs:

- GSTGraphV2SelfExpandingCosmology.lean: 606cb553e396a27fb3918798682d6e6f3edae529.
- GSTActualXHodgeResidualProjection.lean: 1726886a5cb5d225c299aa6605fdc1543f8f93b9.
- GSTK3PrimitiveGram.lean: 3ea87cd8279b075f55cfc26aea52462b80ff0d74.

The standalone workflow previously lacked incremental GST dependency caching. It now restores the same compatible/legacy cache family used by the pinned gate and saves using the restore action's original primary key, avoiding a key change when generated roots modify lakefile.toml. Its exact Lean commands, target list and both sorry guards are unchanged. The successful run log confirms a real cache restore, two successful Lean targets and a saved stable primary key.

The updated manuscript is 760 lines. LaTeX static checks have balanced braces and 58 display delimiter pairs; no PDF/LaTeX compiler result is claimed.

## Continuation

Arithmetic normalization route: complete constructive algebraic chain kernel-verified GREEN at 4f2cdd7.
Native arithmetic-to-cycle route: actual-cycle inverse-matrix compiler kernel-verified GREEN in full integration; universal actual-source rank remains open.
Universal algebraization route: open; no counterexample or universal source constructor has been proved by these index identities.

## Completed formal input chain

The original nilpotent positive Chern class u=c(N)-1 now directly constructs the finite Segre word s=sum_(k<c)(-u)^k using the existing GST birth-feedback inverse. The proof derives (1-s)^c=0 from u^c=0, constructs the Newton normalizer, proves its square is 1+u, and gives the complete Chern -> Segre -> Newton -> Euler cancellation theorem. No extra Segre-nilpotence premise is needed. This final composition is kernel-verified by the revision-matched Graph and full pinned GREEN runs above.

## Self-review of the proposed final inference

Claim audited: do the nondegenerate normalized Euler form and positive integer detector alone imply that every prescribed original rational Hodge class has a native algebraic representative?

Verdict: incomplete; algebraic realization of the detector partner/source is not supplied. This is not a failed Newton or Euler theorem.

A precise algebraic discriminator is H=Q^2 with ordinary positive dot product and topological source space H itself. Take the unital native subalgebra to be the diagonal {(q,q)} in the coordinatewise Q-algebra Q^2, and take s=1. The normalized arithmetic pairing is already the positive dot product. The vector (1,0) has integer self-index 1 but has no diagonal native preimage. This is a countermodel to an inference from the abstract index/native-algebra interfaces; it is NOT a geometric variety and NOT a counterexample to the Hodge conjecture.

Thus the denominator-separated normalizer gives a new explicit finite native characteristic-class word, while its proved native_iff identity preserves the original algebraization question. The actual native index matrix theorem closes the cycle construction exactly when its actual source columns have full rank. A topological Gram matrix supplies no proof of that native-column condition.

Audit provenance: self-review, manuscript and Lean submissions pinned at d34b0a2, 4715410, b4c7d11 and final code 4f2cdd7. No independent-agent review or geometric KU/GRR formalization is claimed.

## Verified checkpoint

All four relevant compiler checks are GREEN. The complete Chern-to-Euler rational algebra and native actual-cycle certificate compiler are kernel-verified without added global axioms or proof placeholders. The all-varieties universal algebraic-source existence statement is not proved by these results; it remains the exact open geometric target. This checkpoint closes the requested Lean derivation/verification phase and preserves that original target explicitly.

## Minimal continuation handoff

Contemporaneous cutoff/assessment: 2026-10-21 Asia/Calcutta, code and standalone compiler checkpoint db37a836047167112598167727833b107a6bce7a; Graph/full pinned evidence at 4f2cdd7 and unchanged K3 source evidence at 4715410. The original all-X/all-rational-Hodge native cycle target remains open. The Lean derivation/compilation phase is complete.

Active geometric decision: construct an ACTUAL algebraic perfect-complex source with nonzero normalized Euler readout against a prescribed nonzero original-X primitive residual. Apply the existing algebraic Adams middle filter, true exceptional Chow return and native source-gain laws; the new index matrix compiler finishes once actual native columns have full rank. Cheapest discriminator for any proposed source is its exact residual Euler period. The topological companion J_L(alpha) cannot be substituted as an algebraic source without a realization proof. Ordinary Lefschetz/lowering words alone and the Picard-only exceptional sector have the pre-existing documented obstructions; do not repeat them unchanged.

A second open continuation is genuine same-Betti smooth-support descent from codimension M-p to M-1, using the already proved smooth-niveau/divisor-source criterion in the high-coniveau manuscript. For p=2 this is one actual support-codimension unit. Multiplying by hyperplanes changes the class and is not such a descent. Both geometric continuations were outside this focused Lean-arithmetic implementation; neither is declared exhausted or impossible. Resume with a proposed new actual algebraic source or genuine Gysin/support comparison, then test its canonical Betti output on the same original X.

Compiler lifecycle: initial ActualX #39482157074, cold repaired ActualX #39482736893, and intermediate cache workflow #39484740442 are cancelled/superseded. Final standalone #39484913997 is completed SUCCESS; final Graph #39483532547, full pinned #39483532335 and K3 #39482156988 are completed SUCCESS. No active compiler job remains in this phase.
