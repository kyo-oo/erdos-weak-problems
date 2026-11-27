# Mathbox — original-X native Chow image and GST sheet realization boundary

- **Date:** 2026-10-19
- **Kind:** direct all-X theorem strengthening and adversarial proof audit
- **Program/route:** GST Hodge Gate 3; original-X geometric source and native finite-correspondence realization
- **Base checkpoint:** \`8103b076c1b24758aae92458cf63f27d510ca180\` on \`research/gpt6-native-point-primitive-span-20261017\`
- **Target:** For every smooth projective complex original X, every p and every rational (p,p) Hodge alpha, a genuine original-X Chow cycle with exact canonical rational Betti class equal to alpha.
- **Active types:** \`codimensionCycles V.X p\` is the existing native rational cycle space; \`H.cycleClass p\` is the supplied Stage2G rational Betti comparison and is **not automatically certified canonical**. \`G : GeometricCycleClassSpine V H\` supplies algebraic-is-Hodge and functorial naturality; \`NativeMassCycleClassBridge\` is eliminated from the final strengthened theorem.
- **New Lean code:** \`GSTClassicalHodgeGlobalSheetSaturation.lean\`, existing file edited in place.
- **Official GitHub Actions receipts:** first original-X W-image theorem at SHA \`4bd4509455bf1462bf4f551f286fb6cc88b537d1\`, run [39216122736](https://github.com/kyo-oo/HC-PROOF/actions/runs/39216122736) SUCCESS; direct M-free source theorem at SHA \`abd3fdf3d23637e47e7c49af9e9f5a2c95886546\`, run [39216905387](https://github.com/kyo-oo/HC-PROOF/actions/runs/39216905387) SUCCESS. CI was configured with \`.github/workflows/gst-native-algebraic-sheet-realization.yml\`; Lean was not installed locally.

## Actual new mathematical object

Fix a scheme V and Hodge weight p. The original-X **native algebraic GST address subspace** is
\[
A_p=\operatorname{span}_{\mathbb Q}
\{\operatorname{fiberedWeightCoordinates}_p(
   [\,H.\mathrm{cycleClass}_p(Z)\,])
      \ : \ Z\in\mathrm{codimensionCycles}(V.X,p)\}.
\]
The value inside brackets is the Hodge-fiber subtype, justified by G.algebraic_is_hodge. This definition does not select algebraic representatives of an unknown alpha.

The previously constructed canonical projective spine lies in A_p:
\`globalSpineAddress_mem_nativeAlgebraicWeightAddressSpan\`.
The abstract GST same-weight matrix-unit saturation from \`fixedWeight_le_of_spine_and_stable\` now specializes to the ACTUAL algebraic-image subspace:
\`nativeAlgebraicWeightAddress_saturates_of_GST_stability\`.

For a missing basis sheet e_j outside A_p, the explicit source-to-target abstract matrix unit yields c e_j for c nonzero; thus the output is outside A_p:
\`missing_native_sheet_forces_unrealized_GST_move\`.
The essential logical statement is **not** “matrix units are geometric”; it is exactly that IF they preserve the native Chow image, every sheet is algebraic. Any unrepresented Hodge sheet forces a failure of that geometric stability.

## Genuine hypothesis reduction on the all-X branch

Earlier GST sheet saturation used \`NativeMassCycleClassBridge\` to manufacture a nonzero source at each weight. The new constructor \`nativeChowOrbitSeedOfNonzeroClass\` directly takes ANY actual Chow class Z on original X whose supplied Betti class is nonzero, constructs the synchronized \`NativeHodgeOrbitSeed\`, and certifies the exact class equation.

The new theorem \`nativeAlgebraicWeightAddress_saturates_of_GST_stability_and_source\` requires NO NativeMass structure. It proves
\[
  [\exists Z\in \mathrm{CH}^p(X)_{\mathbb Q}:\mathrm{cl}(Z)\ne0]
  \ \land\ [A_p\text{ stable under every same-weight GST matrix unit}]
  \quad\Longrightarrow\quad \mathrm{Hdg}^p(X)_{\mathbb Q}\subseteq A_p .
\]
The nonzero source is independently geometrically available in the hyperplane-power sector for 0≤p≤dim X once the standard ample top-intersection/canonical-class comparison is instantiated; that geometric fact is not silently asserted by the present abstract Lean proof.

## Proof audit / precise remaining mathematical obligation

- **Proved with Lean:** actual native-cycle source-address membership, explicit failure of the particular abstract operator when its destination sheet is missing, exact saturation under a named stability condition, direct M-free source constructor, and resulting all-weight-address inclusion. \`#print axioms\` excludes sorryAx at the listed successful Actions revisions.
- **NOT proved:** for arbitrary original X, arbitrary primitive rational (p,p) Hodge alpha, a nonzero original-X algebraic source pairing with its residual, or the condition that every abstract \`sheetMatrixUnit\` is an ACTUAL correspondence realized on this X. Establishing the latter for all missing directions is essentially the target algebraicity content and cannot be filled in using only a formally constructed rank-one Hodge endomorphism.
- **Canonical comparison:** \`H.cycleClass\` must be identified with the actual geometric point fundamental class map using \`GSTClassicalHodgeGeometricCycleClassPointRigidity\` and a true analytification/Betti fundamental-class construction, not an arbitrary supplied linear map.
- **Evidence status:** **proved** for the stated abstract/native-image implications; **conditional** for the universal-algebraicity corollary; global unconditional Hodge target remains unproved. **Review:** author self-audit of quantifiers, genuine Chow type, operator actions and canonical-map qualification.
- **Next discriminating route:** build one actual geometric incidence/Hilbert/closed-correspondence operation on the arbitrary original X whose verified canonical Chow/Betti action realizes the specific missing sheet/source coupling; do not merely postulate native stability or a target cycle.
- **Route disposition:** OPEN. The present pass strengthens the true all-X bridge and eliminates the NativeMass interface but does not satisfy Gate 3.

## Artifacts

- \`GSTClassicalHodgeGlobalSheetSaturation.lean\`
- \`.github/workflows/gst-native-algebraic-sheet-realization.yml\`
- \`research/ACTIVE_HODGE_PROOF_PLAN.md\` (unmodified immutable target)
- [CI at final Lean revision](https://github.com/kyo-oo/HC-PROOF/actions/runs/39216905387)
