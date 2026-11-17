# AUDIT-39 — the K-transport crossing strike (Round 39)

**Date**: 2026-11-05 (session clock). **Mode**: SKILL V6.2 §36, ONE loop. **Auditor**: one fresh adversarial agent (general-purpose dispatch, the PTS adversarial-auditor role); the agent did not author the round.

## Verdict: PASS_WITH_REPAIRS_REQUIRED → (after one batched repair round) PASS

## Part A — the fresh agent's attack (run + sabotage + static + recompute)

**Run receipts**: exit 0, 569 ok / 0 FAIL (pre-repair), double-run byte-identical (md5 22cf8d5c…), ~14 s.

**Sabotages** (all restored, md5-verified):
- S1 (ŵ_R t=4 coefficient d²→d²+1): exit 1, 398/171 — the spanning, eigen-action, period law, leaf, K-spread, dichotomy, charges, Chern closure all FIRE. The W6/E3 battery stays green (self-consistent — see F6).
- S2 (expected charge 24d²→24d²+1): exit 1, exactly the branch-charge checks at all 9 worlds.
- S3 (branch half-formula (m+2w)/2→(m+w)/2): exit 1, the parity sweeps detect it 9×.
- S4 (period 8d²→8d): exit 1 at 8 of 9 worlds — d=1 blind to d²-scaling (the noted direction).
- S5 (leaf rigging `or True`): the rigged check prints ok — caught ONLY by the built-in vacuity scan.
- **S5b (scan-evading rig `or 1`): the pre-repair certificate PASSED with a can-never-fail leaf check** — the scan's blind spot (F3).
- P1 (t=2 coefficient sign flip): exit 1 — caught by the spanning/eigen layer; the q-family is sign-symmetric (F5).
- P2 (θ-half (b−b′)/2→(b+b′)/2): exit 1 — caught ONLY by the V6 difference identity; the entire parity battery is blind (θ² 2-divisibility) (F4).

**Static findings**: F1 (major) the V7 WITNESS was a bare `check(True,…)` ×9 on the headline "m* = 2 EXACT" — a claim with no computation at its assertion point; F2 (major) the V5 K-freeness layer content-free (tautological Sq's, hardcoded `sym_nonzero = True`, the binomial count labeled as a torsion proof); F3 (major) the vacuity scan evadable (the dead `ok( True` pattern; `or 1` passes; the shipped `check(True` undetected); F4 (major) the parity battery blind to the θ-half formula; F5 (minor) the q-receipt family sign-symmetric; F6 (minor) the W6/E3 battery mutation-blind (self-consistent); F7 (minor) label overstates (Z-SPAN "exactly" from 6 samples, primitivity only /2, LEAF "≠0" unasserted, "full plane" from a 5-point sample with a DUPLICATE direction at 7 of 9 worlds); F8 (minor) the qRI/qRt zeros support-forced (any coefficients); F9 (minor) the H² generation rests on 8 unspanned generators; `res_zero` duplicates `norm_ok`; F10 (minor) the transpose/pullback convention undocumented (the covariant reading fails at d ≥ 2 — all transpose-invariant receipts blind to it); F11 (trivial) unused import; F12 (minor) the c₁²-evenness unfalsifiable on its sampler.

**Independent recompute** (the agent's own code, no certificate imports): the periods INT ŵ_R² = 8d², INT ŵ_I² = 8d, the disjointness INT ŵ_Rθ² = 0, INT θ⁴ = 24 — ALL AGREE at d = 1, 2, 7; the trace identity, the kernel dimensions, the eigen-action (in the committed pullback convention), the invariant-lattice H²(C₂;M) = 0 (by integer lattice arithmetic), and the K-spread at 48 sampled β-directions per world — ALL AGREE. The auditor's first K-spread probe reported "violations" which its own re-examination found to be a bug in ITS solver — corrected and re-run: all translates lie in W.

## Part B — the orchestrator's checks

The orchestrator verified the audit's receipts (the sabotage outputs, the rigging test), accepted the findings, executed the batched repair round, and re-ran the closing checks (below). The different-algorithm discipline was discharged within the fresh agent's own recompute (its compound-matrix/RREF/lattice-arithmetic implementations).

## The repairs (one batched round, strengthen-to-label, ALL findings)

- **F1**: the WITNESS replaced by a bundled genuine predicate (the integral branch pair + the charges (24d², −8d²) + the trace/difference + the Chern closure + the carrier 16d², recomputed in V7) + the leastness receipt (2 = the least positive even scale).
- **F2**: V5 rewritten — the structural constants CITED to the discovery's Layer 3 (discovery_strike_checks.py D0–D2, 270 checks) + a genuine exterior/symmetric discrimination computation (letter² zero in the exterior, nonzero multiset in the symmetric).
- **F3**: the vacuity scan extended to six shapes + the numeric-truthy rigging (`or <digit>`); the audit's S5b evasion re-tested post-repair: **CAUGHT, exit 1** ('or-digit' at the planted line).
- **F4**: the θ-half mutation canary added (the correct formula satisfies the branch difference identity; the mutated formula breaks it at (b,b′)=(1,−1)).
- **F5/F8**: the q-family labels disclose the support structure (the sign-sensitivity lives in the spanning/eigen layer, which fires; the zeros are support-forced — the spectral disjointness cited to Round 38's 2×2 receipt).
- **F6**: the W6 tables relabeled as consistency receipts (the machinery identities at the world).
- **F7**: the Z-span support argument made explicit (the t=0/t=1 coordinate-forcing, a new SUPPORT-DISJOINTNESS check); the gcd-primitivity receipt (the full coefficient gcd = 1); the LEAF nonzero asserted; the K-spread's 5 distinct β-directions (disjoint from α at every world).
- **F9**: the invariant-system rank check (10 independent equations on 18 coordinates → the invariant space has dimension exactly 8 = the generation); the duplicate check removed.
- **F10**: the action-convention note in the header (the pullback/contravariant convention; the covariant reading fails at d ≥ 2 — the committed model's convention, consistent with Round 38's audited receipts).
- **F11**: the unused import removed; the comb import hoisted.
- **F12**: the c₁²-evenness now tests the EVEN coefficients (the 2-form commutativity: the squares vanish, the cross terms carry the 2) — falsifiable content.

## Closing re-check

606 checks, 0 failures, exit 0, deterministic double-run byte-identical (md5 dbbaf7189a75244d84b7f4b08b58e001); the post-repair rigging re-test fired (exit 1). **Loop CLOSED.**

No new ledger entry: the findings are ledger-092/107/109/112-family instances caught PRE-PUSH by the audit — the immune system working (the F1 class — a bare claim-check on the headline — is the 092 signature at its worst; the F3 scan-evasion is the 107 battery's blind spot; both now have standing mechanical coverage).
