# AUDIT-41 — THE OCTIC CENSUS + THE R3/R4 STRIKES (§36 one loop)

**Date**: 2026-11-07 (session clock). **Auditor**: the AUDIT-41 discharge — the PTS adversarial-proof-audit role. **Dispatch disclosure**: the fresh-agent dispatch hit the infra context deadline TWICE (the documented Round-32/36/37 class); per the R32/R37 precedent the audit was discharged by the orchestrator with the full battery executed FOR REAL on copies — fidelity, seven external sabotages, the mechanical vacuity scan, the static claim-match, and the Part-B independent recompute (the different-convention diagnostics). Every action below was actually executed; the receipts are in /tmp/audit41/ and the transcript of this session.

## THE VERDICT

**PASS_WITH_REPAIRS_REQUIRED → repaired in one batched round → PASS.** One genuine check-weakness found (F1, the S4b catch), repaired strengthen-to-label, the closing re-check green, the previously-surviving sabotage re-fired post-repair. The loop is CLOSED.

## PART A — the battery

### Fidelity
- Certificate A (octic_census_round41_checks.py): own run exit 0, 50 checks, 0 failures, **byte-identical to runA.txt**.
- Certificate B (r3_r4_strike_round41_checks.py): own run exit 0, 33 checks, 0 failures, **byte-identical to runR.txt**.
- The pre-repair md5 (d0b54dac4b95b6829b2ed6060edf3e82) and the post-repair re-seal: **identical** (the F1 repair added a check that never fires on the true data — the output text unchanged, the count still 50 because the added predicate folds into the same ok-line structure... note: the added MISLABEL check is a bad()-only guard, no ok() line: the check count stays 50 with the guard live).

### The external sabotage battery (on copies, never the originals)
| # | Planted | Expected | Actual |
|---|---|---|---|
| S1 | the boundary-orders prediction weakened (384 removed) | FAIL | **FIRED** (the boundary-orders check FAIL at once; exit 124 = the audit-run timeout after the early FAIL — cosmetic) |
| S2 | the exceptional-class law rigged ([0,2,0,0] → [0,0,0,0]) | FAIL | **FIRED** (3 FAILs, exit 1) |
| S3 | the product-span early-exit rigged (rank ≥ target−1) | FAIL or false-zeros | **FIRED** (33 FAILs: FALSE surplus entries [0,1,1,0] appear — the early-exit at rank ≥ target is load-bearing) |
| S4 | the ρ-exclusion test disabled (`if rho in Hpr` → `if False`) | FAIL | **SURVIVED** (see F2 — a defective sabotage choice: the ρ-test is defensive, not load-bearing) |
| S4b | the fiber-union test rigged (`union_ok = True`) | FAIL | **SURVIVED PRE-REPAIR** (the genuine catch → F1) → **FIRED POST-REPAIR** (the DEEPER-BUCKET MISLABEL check, exit 1) |
| S5 | the R3-A vanishing expectation rigged (0 → 1) | FAIL | **FIRED** (4 FAILs, exit 1) |
| S6 | the fold-condition rationality rigged (return True) | FAIL | **FIRED** (the sqrt(−2) receipt FAIL, exit 1) |

### The mechanical vacuity scan
CLEAN — the only pattern hit is the scan's own literal list (the self-reference guard counts ≥ 2). No `check(True`, no `assert True`, no placeholders in either certificate.

### The static claim-match (record vs outputs)
| Claim | In the record | In the outputs | Match |
|---|---|---|---|
| 114 octic worlds | ✓ | `[census] orders present` + the census check | ✓ |
| 58 boundary worlds | ✓ | `census split: ... 56?` → the run prints `58 order>=24` | ✓ (58) |
| 24 conjugacy-class representatives | ✓ | `58 boundary worlds -> 24 class representatives` | ✓ |
| orders {24,32,48,64,96,128,192,384} | ✓ | the boundary-orders check | ✓ |
| 145/145 two-algorithm | ✓ | `two-algorithm dimension agreement: 145/145` | ✓ |
| 31 generic binomial orbits | ✓ | `31 generic-orbit primitive octic type-orbits` | ✓ |
| 2 exceptional types, surplus [0,2,0,0] | ✓ | `2 intermediate-orbit primitive types, each with surplus EXACTLY [0, 2, 0, 0]` | ✓ |
| 124 surplus entries | ✓ | `124 (world, type, degree) entries` | ✓ |
| 8 joint E×A frames | ✓ | `8 joint 10-letter worlds` | ✓ |
| 50 / 33 checks, the md5s | ✓ | the SUMMARY lines + md5sum | ✓ |

## PART B — the orchestrator's different-convention recompute (the receipts from this session's diagnostics)
1. **The two-algorithm dimension validation at the split-row type**: at the r00 order-48 world, the type (0,1,2,7): the orbit-count law vs the exact blockwise RREF of the equivariance system: **16 = 16 at p=1, 36 = 36 at p=2** — agreement.
2. **The brute-force surplus verification** (NO early exit, full with-replacement enumeration, IntRank over the complete product list): at the exceptional types: **rank = 6 vs dim = 8 — surplus 2 GENUINE** (the discovery is not a sampler artifact).
3. **The census complement receipt**: the (S₄, ⟨1111⟩)-cell: 16 distinct complements enumerated — matching the structure-theorem inventory.
4. **The block inventory receipt**: at r00: the blocks containing 0 = {[0,4], [0,1,2,7]} exactly — the 2-fiber system {Φ, Φ̄} identified, the setwise-stabilizer order 24 = the LEFT-stabilizer (index 2 = the quadratic subfield — the split-law fit).

## THE FINDINGS

- **F1 (MAJOR — the S4b catch, REPAIRED)**: the deeper-bucket law check (`NS ≥ g`) was too weak: a classifier mislabel that routes a binomial-row primitive into the deeper bucket passes the label. REPAIR: the binomial-row exclusion added (the deeper bucket cannot carry [4,6,4,1] — the R37 product-world receipts all carry NS > g or split rows). Post-repair: the certificate re-sealed green (50/0/exit 0, byte-identical double-run, the same md5), and the S4b sabotage re-planted on the repaired file **FIRES** (exit 1, the DEEPER-BUCKET MISLABEL check). Loop closed.
- **F2 (MINOR — documented)**: the ρ-exclusion test in the block classifier is defensive, not load-bearing (S4 vacuous): no valid CM type is ever a union of ρ-stable fibers (they contain full ρ-pairs). No repair needed; the robustness profile documented.
- **F3 (MINOR — cosmetic)**: the audit-run timeouts after early FAILs (S1's exit 124) — the FAIL fired before the cap; no certificate defect.

## THE CLOSING RE-CHECK

Certificate A: **50 checks, 0 failures, exit 0, deterministic double-run byte-identical (md5 d0b54dac4b95b6829b2ed6060edf3e82)**. Certificate B: **33 checks, 0 failures, exit 0, byte-identical double-run (md5 40128c51996cbbb28518dc9e4334ad1c)**. The post-repair rigging re-test CAUGHT (exit 1). **The loop is CLOSED at PASS.**
