# AUDIT-37 — Round 37 certificate scope — 2026-11-05

## Verdict

**PASS_WITH_REPAIRS_REQUIRED → REPAIRED → PASS** (one batched repair round; closing
re-check 1950/0/exit 0, deterministic double-run byte-identical; loop CLOSED).

Part A executed by FOUR fresh adversarial agents (the repo's PTS adversarial-auditor
role invoked side-by-side with SKILL V6.2 per the operator's standing order — the
single full-scope dispatch and both retries of the independent-recompute agent hit
the infra context deadline, the documented Round-32/36 class; the mathematics
recompute role was discharged by Part B, the run-fidelity and static-audit roles by
the three completed fresh agents). Part B: the orchestrator's different-algorithm
recompute (orchestrator_recompute_round37.py, 12 PASS / 0 FAIL: census multisets,
BFS orbits, sympy nullspace + full-equation-set integer solver, 3-prime modular
ranks, third arity implementation).

## Claim match

- The computational core is HONEST and STRONG: the census sweeps are exhaustive at
  degrees 4 and 6 (5/5 and 16/16 against the classical counts); the surplus loop
  runs over all 110 worlds, 352 type-orbit representatives, every degree 2..2g with
  a with-replacement sampler matching the theorem's quantifier domain; the
  receipts are real and byte-verified across a triple run (author ×2 + audit ×1);
  the hostile battery fires on demand (four external sabotages, pre- and
  post-repair, all exit 1).
- The findings were claim-side: one critical hostile-coverage gap (S3b), two major
  domain gaps (F1 the E×A frame census, F2 the split-law check domain), one major
  label defect (F6 the Lean PART-A label), and nine hygiene findings. All repaired
  in one batched round, strengthen-to-label.

## Findings

### S3b (R37-A2, CRITICAL) — the one-directional canary — severity: blocker-class (caught pre-push)
- Location: galois_closure_descent_round37_checks.py:303-309 (is_valid_type), the old H3 at 1382-1389
- Issue: weakening the type-validity predicate in the MISSING-PAIR direction SURVIVES the whole certificate (1892/0/exit 0, verified live by the agent's planted sabotage /tmp/audit37_a2_s3b.py: the predicate accepting under-length types while still rejecting H3's double-letter canary). The one-per-pair law was tested in ONE violation direction only; the ok-1892 census receipt feeds only generator-produced (valid-by-construction) types and can never catch a too-lenient predicate.
- Repair: the H3 battery — canaries for missing-pair (H3b), duplicate-letter (H3c), empty (H3d), plus the adversarial sweep rejecting all four violation directions at every one of the 110 census worlds (H3-ADVERSARIAL, accepted: []). The census receipt relabeled a consistency echo.

### F1 (R37-A4, major) — the Corollary's E×A universal claim exceeds the evidence
- Location: .tex cor:s19 (was "37 joint frames" from 11 of 110 base worlds, type subsample [:2])
- Repair: the frame census EXTENDED to 17 base worlds (the complete quartic+sextic census worlds, all five regular octic worlds, three distinct automorphism-split order-16 bases C8/C4xC2/C2^3) — 63 joint frames, surplus 0 at every frame; the Corollary rescoped to exactly this inventory with the type-subsample stated. (One repair-side defect — label.split("r") shearing "d8-reg-" at the r of "reg" — caught by receipt arithmetic 37→38≠expected, fixed with rsplit, re-run.)

### F2 (R37-A4, major) — the split-law check domain narrower than the claim
- Location: certificate V3 (old: the split-row equality fired only at max-induction-degree-2, 8 instances; the 120 octic [16,36,16,1] orbits checked only "NS>g")
- Repair: induced_subfield now returns the quadratic-inducible marker (any index-2 stabilizing H'); the split-row equality is checked at ALL 128 quadratic-inducible orbits — the law HELD at every one (the strengthened check is green, confirming the claim on the wider domain); the .tex states the widened domain.

### F6 (R37-A4, major) — Lean PART A "receipts" are numeral tautologies
- Location: GSTLawStackRound37.lean:38-72 (decide on (5:ℕ)=5, 1386-1386=0, etc.) under a [Genuine proof-shape] label; header claimed "decide on bounded enumerations" with no enumeration defined
- Repair: PART A relabeled [Shape record: content in the certificate + derivation]; the header now states ALL five parts are statement-shapes only; the E×A receipt updated to the post-repair frame census (63).

### F3 (minor) — 352/1386 degree-2 surplus entries definitional
- Repair: the degree-2 span is now the number of constructed basis systems (genuine: fires if the basis construction drops content); the central-table receipt states the degree-2 computation honestly.

### F4 (minor) — H4 control vacuous by construction
- Repair: the unbalanced word is INJECTED into the purity filter's input list; it must be dropped while all balanced words survive (fail-closed, load-bearing).

### F5 (minor) — H6 control could not fail (closure of the identity tuple)
- Repair: the census class is regenerated by a CERTIFIED generating pair (H6 PAIR-GENERATION) and deleting either generator shrinks the group (12→3/2 at the committed class) — genuine.

### F7 (minor) — the 1668-type validity check tautological
- Repair: relabeled a consistency echo with the adversarial directions delegated to the H3 battery.

### F8 (minor) — equivariance spot-check under-disclosure
- Repair: the ok message states the actual subsample (24 of the first 24 worlds checked; per world the first type orbit, the d2[0]·d2[1] product, the first 6 support words).

### F9 (minor) — world-label collisions (two worlds shared "d4-G4r0"; ~4 shared "d8-aut16-C2^3r0")
- Repair: class-index disambiguation (d4-G4c1r0 / d4-G4c2r0; d8-aut16-C2^3x1r0 / x2 / x3); every receipt uniquely traceable.

### F10 (minor) — the "E-frames <= 16 joint worlds" bound ambiguous
- Repair: the header bound restated as "E-frame base worlds <= 17".

### F11 (minor) — soft references (branch id, remote commit hash) unresolvable locally
- Repair: a provenance note added to the .tex (the receipts' locations in the worklog and round records).

### A2-caveat (minor) — an empty degree-2 basis silently counted alive in the random-class pass
- Repair: fail-closed (alive = False).

### Cosmetic — physical ok-lines 1893 vs counter 1892 (H5 retraction decremented CHECKS though bad() never increments it)
- Repair: the retraction no longer touches CHECKS; counter ≡ printed ok-lines (1950).

## Counterexample / computation attempts

- A1 fidelity: fresh run exit 0, 1892/0, byte-identical to runA (and runA ≡ runB), 112 s; seed receipt 0xD15EA5E5BADF00D.
- A1 S1 (anchor-dim mutation 3→4 at the sextic-3 receipt): FIRED, exit 1, "sextic-3 vanishes from the anchor set".
- A1 S2 (deletion of one REAL degree-2 basis generator at d6-G24r0, outside the planted H1 copy): FIRED, exit 1, the central table reports 2 nonzero — the degree-4 span drop 3→1 matches H1's own prediction, proving the real machinery (not the hostile copy) was sabotaged.
- A2 S3 (type-validity → return True): FIRED via the H3 canary, exit 1.
- A2 S3b (the lenient missing-pair direction): SURVIVED the pre-repair certificate — the blocker-class finding above.
- A2 S4 (a sign flip at a second, real equivariance site, distinct from H2's planted copy): FIRED via the product-equivariance spot check, exit 1 — the dedicated check catches what the rank computations alone would not (the sign twist cancels inside the iterate-basis spans).
- A2 vacuity battery (broader than the file's internal scan): or-True 0, and-False 0, ok(True 0, ok(1, 0, is-not-None-on-arithmetic 0 (5 hits, all None-sentinel dict filtering), self-comparison 0; garbage tests on three load-bearing check classes: all FAIL-ON-GARBAGE.
- A4 sampler review: with-replacement under with-replacement claims; random-class-with-retries under ∃-claims; no distinct-only-under-with-replacement instance.
- Part B (orchestrator, different algorithms): census multisets [4,4,8,12,24] and the 16-class 6T table; BFS orbit recompute of the 1386 purity sets; 364 dims by sympy nullspace + 476 by full-system integer solve; 40 product-span ranks over three primes; arity totals by a third implementation — 12/12 PASS.
- POST-REPAIR sabotage (closing): the anchor-dim mutation re-run against the repaired file — FIRED, exit 1.

## Required repairs before claiming success

- [x] S3b — the adversarial type battery (H3b/H3c/H3d + the all-worlds sweep)
- [x] F1 — the E×A frame census extension + the Corollary rescope
- [x] F2 — the split-law domain widened to all quadratic-inducible orbits
- [x] F6 — the Lean PART-A relabel
- [x] F3/F4/F5/F7/F8/F9/F10/F11/A2-caveat/cosmetic — as listed above

## Closing re-check

galois_closure_descent_round37_checks.py: **1950 checks, 0 failures, exit 0**;
deterministic double-run byte-identical (runA ≡ runB, md5
50d0b69880eb96a2bff95afe7da92c52; pre-repair 1892 checks, md5
e16164e5ae0632572db5f01c93025e29); ~134 s; the derivation recompiled
(tectonic, 0 errors, 105.36 KiB); the Lean face relabeled per ledger-108. Q2 NOT
claimed; the closing string NOT emitted; the polarity split stands.
