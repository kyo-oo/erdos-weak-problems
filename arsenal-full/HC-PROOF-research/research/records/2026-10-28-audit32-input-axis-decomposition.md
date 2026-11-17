# AUDIT-32 — The independent adversarial audit of Round 32 (the input-axis decomposition)

**Date:** 2026-10-28 (session clock). **Auditor:** a fresh agent (dispatch agent-3af05a58, glm-5.3) that did NOT author the round, plus the orchestrator's different-algorithm recompute for the mathematics findings (the full-scope dispatch hit the agent-infrastructure context deadline twice — the same class as Rounds 29/31's 29-b1/29-b2 dispatches; the certificate-scope dispatch SUCCEEDED and its findings are recorded verbatim below; the mathematics-scope findings were re-derived by the orchestrator with deliberately different formulas and are marked as such).

## Verdict (after the batched repair round): PASS_WITH_REPAIRS_EXECUTED → closing re-check: **PASS**

The certificate re-run after all repairs: **279 checks, 0 failed, exit 0, deterministic double-run byte-identical** (md5 091e2a54deb6fb835d0ee6a3cd8d160a on both runs). The .tex recompiled with tectonic, 0 errors.

## The findings (the audit's, verbatim scope; each with its repair)

### F1 — VACUOUS CHECK CONCEALING A FALSE CLAIM (severity: major; ledger-092 class) — REPAIRED
- **Location:** the certificate, the C1a block.
- **Issue:** the original line `ok(s_p == -s_p * Fr(1) or True, "C1a-info: HR sign factor...")` — the `or True` short-circuits the check (it can never fail), and the concealed comparison `s_p == -s_p` is FALSE for every s_p = ±1: a vacuous check hiding a false claim, exactly the ledger-092/082 class. Runs 4×.
- **Repair:** replaced by three genuine checks per p: the opposite-HR-sign factors (type (p,p−1): +i·(−1)^{p−1} vs type (p−1,p): −i·(−1)^{p−1} — genuine oppositeness), the uniform-exponent identity ((2p−1)(2p−2)/2 ≡ p−1 mod 2 — a genuine arithmetic identity of the uniform HR formula), and the automatic-compensation product ((−1)^{p−1}·(−1)^{p−1} = +1). All three can fail (wrong formulas would fail them).

### F2 — SELF-COMPARISON TAUTOLOGY (severity: major; ledger-092 class) — REPAIRED
- **Location:** the certificate, the C5b block.
- **Issue:** `lhs = span_membership(cols, w)` followed by `ok(lhs == span_membership(cols, w), ...)` — a value compared to itself; the label claimed "model equivalence both directions" but nothing was tested. Runs 20×.
- **Repair:** replaced by the genuine both-directions form: the combined sector columns span the whole space (rank test) ⟺ every test class lies in the combined span (membership test) — two independently computed predicates whose agreement can fail (and whose disagreement would be a genuine finding).

### F3 — NEAR-VACUOUS CHECK (severity: minor) — REPAIRED
- **Location:** the certificate, C1a line 212 (`ok((p * (p - 1) // 2) is not None, ...)`).
- **Issue:** an integer expression is never None — the check cannot fail.
- **Repair:** removed; subsumed by F1's genuine uniform-exponent identity.

### F4 — LOGICAL TAUTOLOGY (severity: minor) — REPAIRED
- **Location:** the certificate, the C5a trichotomy block (`count = sum([inD, inM, (not inD and not inM)]); ok(count >= 1, ...)`).
- **Issue:** one of the three terms is always true — the check is a tautology; the "exhaustiveness" label was untested.
- **Repair:** replaced by the genuine content: all three sector cells are REALIZED on random model data (non-emptiness of each cell — the partition is genuine). Falsifiable: if random data never realizes a cell, the check fails.

### F5 — MATHEMATICAL SIGN-FORMULA DEFECT (severity: major; found by the orchestrator's different-algorithm recompute) — REPAIRED
- **Location:** the derivation §3, the proof of Theorem 1(ii).
- **Issue:** the original sign computation used the per-type exponent (−1)^{p(p−1)/2} for the HR signs and closed with "choosing the overall sign of the polarization" — the exponent formula was not the uniform one, and the "choice" language masked the actual structure (with the wrong exponent the claimed oppositeness pattern is not uniform in p).
- **Repair:** rewritten under the UNIFORM Hodge–Riemann formula i^{a−b}(−1)^{w(w−1)/2}S(v,v̄) > 0 (which reproduces the classical weight-one and weight-two signs — checked against both anchor cases): the two level-one types carry the OPPOSITE factors ±i·(−1)^{p−1} (the exponent w(w−1)/2 = (2p−1)(p−1) ≡ p−1 mod 2 is common to both), and the twist's sign factor (−1)^{p−1} (from i^{2p−2}) EXACTLY cancels the HR sign factor: the weight-one Riemann condition holds with the standard normalization — the compensation is AUTOMATIC, no choice needed. The certificate's C1 now checks the three genuine identities.

### F6 — CLAIM-MATCH CONTAMINATION IN THEOREM 4 (severity: major; the audit's attack surface D) — REPAIRED
- **Location:** the derivation §6, Theorem 4's (a)⟹(b) proof.
- **Issue:** the original (b2) was defined as the mechanism-form (items (i)–(iii) discharged) while the (a)⟹(b) proof delivered only the conclusion-form ("at conclusion-strength... the equivalence of the mechanism-form with the conclusion-form... which (a) supplies wholesale") — a statement/proof mismatch: the proof did not establish the mechanism-form, and the equivalence as stated overclaimed.
- **Repair:** Theorem 4 restated in the airtight form: (b2) = the conclusion-form (every transcendental input is algebraic — the exact residual content), the equivalence proven cleanly in both directions, and the mechanism-form (items (i)–(iii) at the transcendental sector) stated separately as a SUFFICIENT condition for (b2) via the campaign's standing reduction — with the honest two-reading remark (conclusion-form vs mechanism-form, sufficient not necessary). The abstract updated to match.

### F7 — HOSTILE SAMPLING (severity: minor) — REPAIRED
- **Location:** the certificate, C1e.
- **Issue:** the indefinite-form hostile's first sampling window (20 draws, u1,u2 ∈ 1..4) never attained a negative value under the fixed LCG stream — the control did not fire, i.e., it demonstrated nothing on that run.
- **Repair:** the search widened (40 draws, u1 ∈ 1..4, u2 ∈ 1..8): the control now fires on the fixed stream (a genuine negative is found), and the check verifies falsifiability.

## The audit's own runs (verbatim results)

- The certificate executed twice by the auditor: exit 0 both runs, `RESULT: 304 checks passed, 0 failed` (pre-repair), byte-identical diff — the determinism receipt held.
- The vacuity scan (the patterns `ok(True`, `info`, `lhs == span_membership`): two hits — both genuine findings (F1, F2).
- The adjacent near-vacuity observations (F3, F4) — confirmed and repaired.

## The closing re-check (the orchestrator, after the batched repairs)

- The certificate: 279 checks, 0 failed, exit 0, double-run byte-identical (md5 091e2a54deb6fb835d0ee6a3cd8d160a). The count DROPPED from 304 to 279 — the 25 vacuous/tautological checks (F1: 4×, F2: 20×, F3: 4×, minus the repair-restructured C1a/C5a/C5b blocks) were removed and replaced with genuine content; the drop is the receipt that the repairs removed real vacuities.
- The .tex recompiled: tectonic, 0 errors.
- The door-law independent re-derivation (the orchestrator's different-algorithm check): the refined door law im(γ−1)-characterization (γ(e) = −f, γ(f) = e; membership ⟺ m(u+v) ∈ 2L ∧ m(u−v) ∈ 2L) re-derived by direct block algebra in the certificate's C2 with the independent block verification (the constructed (a,b) satisfies the deck equation) — agreement on 400 random instances.
- The claim-match on Theorem 4: statement and proof now match (the conclusion-form equivalence + the mechanism-form sufficiency clause).
- The scope lines: the closing string is not emitted; Q2 is not claimed; the Lean face is DRAFT-NOT-COMPILED — all three hold on every artifact.

## Required repairs before claiming success — ALL EXECUTED

1. [x] F1: the C1a vacuous check replaced with genuine sign identities.
2. [x] F2: the C5b self-comparison replaced with the rank⟺membership equivalence.
3. [x] F3: the near-vacuous exponent check removed (subsumed).
4. [x] F4: the trichotomy tautology replaced with the non-emptiness realization check.
5. [x] F5: the sign computation rewritten under the uniform HR formula with automatic compensation.
6. [x] F6: Theorem 4 restated in the claim-matched form (conclusion-form equivalence + mechanism-form sufficiency).
7. [x] F7: the indefinite-form hostile widened to fire.

## The independent different-algorithm recompute (the receipt)

One of the context-deadline dispatches completed its verification code before the deadline killed its report-back: `adversarial_audit_round32.py` (xorshift64* PRNG — a different family AND seed; a Cramer-rule solver; the door-law membership computed FROM THE DECK DEFINITION as the image lattice, not from the derived formula; validated against brute force 30/30). Its full run (`audit_independent_run.txt`, exit 0):

- **The door law: 600/600 random instances agree, 0 mismatches** — lhs computed by image-lattice membership, rhs by the 2L-divisibility predicate; discrimination receipt: lhs true on 85, rhs true on 85, both-false on 515, mixed 0. The primitive balanced ray: odd m refused, m=2 admitted.
- **The twist factor (2πi)^{2p−2} ~ (−1)^{p−1}: CONFIRMED for p=2..5** (Z[i] repeated multiplication).
- **The HR sign table: the script's standard column (−1)^{w(w−1)/2} — the UNIFORM formula — DISAGREES with the ORIGINAL .tex exponent at p=3 and p=4** — the independent confirmation of finding F5 (the sign-formula defect), matching the repair exactly: the repaired .tex uses the uniform formula the auditor's standard table exhibits; the oppositeness checks (ratio −1 at every p) pass under both.
- **The degree bookkeeping: ALL verified** — 1+2(p+g−1)−2g = 2p−1 for all (p,g) in [1..6]×[1..4]; the p=1 codim = the Albanese graph codim; the Y/W/composite shifts; the (b)⟹(a) pushforward lands in CH^p.

The dispatch's report-back failed; its mathematics did not. The script and its run output are part of the audit record.

**The loop is CLOSED at PASS.** The audit taught a scar: the vacuity classes recur even with the docstring contract in place ("a check that CAN fail") — the pre-commit gate for this round's certificate now includes the vacuity scan patterns (`or True`, self-comparison after direct assignment, `is not None` on total expressions, tautological predicate sums) as a standing item. The ledger entry is appended.
