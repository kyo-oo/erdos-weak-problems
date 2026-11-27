# AUDIT-51 — Round 51: The Seed-Orbit Law, the Break-Hunt, the Meta-Law (2026-11-09)

**Subsequent correction, 3 November 2026:** this is the historical audit of
its pinned source, not a fresh review of the corrected files. It missed the
integral-versus-rational error in the later `Z u / 2Z u` avatar, and a planted
control that is rationally represented. The [current correction and hand
proofs](2026-11-03-gst-selected-cluster-rational-fiber.md) supersede those
interpretations. Prior independent-review provenance is not transferred to
the current self-reviewed changes.

Auditor: PTS adversarial auditor (fresh agent, general-purpose dispatch, AUDIT-51). The auditor did
NOT author any round-51 artifact. Corpus clone verified at HEAD
`1fdd62faa13dfc511d620204b302a6808025ceab` (ROUND 50 commit); 743 tracked Lean files (recounted).
Every load-bearing citation was opened at its exact line this session. The certificate was re-run
twice by the auditor on copies in `/tmp` (original untouched), plus a five-item external sabotage
battery on copies and a structural vacuity analysis.

## Verdict (pre-repair): PASS_WITH_REPAIRS_REQUIRED

No theorem in the derivation is false (the auditor recomputed the orbit-law identities, the birth
signatures, the parity engine, and the census totals independently, and every corpus citation is
exact). The defects are in CERTIFICATION INTEGRITY: the round's centerpiece (Theorem 4, the
break-hunt) is certified by a sweep whose verdict is predetermined by the construction of its own
inputs and this is not disclosed (ledger 092/107/111 class); one battery item and one "re-verified
in exact arithmetic" receipt are vacuous (ledger 109 class); the record pre-references this audit
file (ledger 110 class). All repairs are disclosure/reframing/re-computation repairs — no new
mathematics is required — but until F1 is repaired the headline claim "the break branch hunted to
extinction at the committed census" must not be stated as a certified hunt.

## What survived the audit INTACT (with your own recomputations)

1. **The certificate run.** Two auditor runs in `/tmp/r51audit`: exit 0, `69 passed, 0 failed`,
   `PINNED_PRE = 68: SEALED`, byte-identical outputs, and the auditor's output matches the shipped
   `runA.txt`/`runB.txt` byte-for-byte (run md5 `499409ece79e9d1451e00208bb4d5d42`; source md5
   `a1309257844da656be1c0216b72433a2` — both recomputed and matching the record). Census totals
   recomputed: 20 families, 3,151 inputs (named + box, per-family recounted: 21/81/343 box sizes).
   Run wall time on the auditor's machine: ~0.11 s (the record's "~6 s" is wrong by ~50x — see F8).
2. **Theorem 1 (the seed-orbit law) — the mathematics.** Recomputed by hand: `tau_{p-1}(2,1,1) =
   (2p,p,p)`; `ch(tau(c)) = ch(c)` and `pg(tau(c)) = pg(c)` (so the fence holds at EVERY fold, not
   just the five swept values); `tau_j . tau_k = tau_{j+k}`; the four birth signatures
   (nu: ch 0 / pg -1; de: ch 0 / pg -2; la: ch 1 / pg 0; rh: ch -1 / pg 0); the generator law
   `(lambda_0 (x) rho_0)^{(x)m} = (2m,m,m)`; the boundary cell off the orbit. All correct, and all
   match the corpus definitions at the cited lines with zero definition drift (the certificate's
   `ch = w1 - w2`, `pg = (w1+w2) - d`, `tau = (d+2j, w1+j, w2+j)` transcribe
   `cosmicCharge = c.1 - c.2`, `weight = c.1 + c.2`, `CausalHodgeCell.tate` exactly).
3. **The P^2 parity model is faithful to the corpus's line-sum pair calculus.** The corpus
   (`GSTGraphV2OntologicalFoldForAllN.lean:98-128`) defines `p2scale = A.sum - B.sum`, `p2grade2 =
   (sum(A^2) - sum(B^2))/2`, `p2Landing = rank-diff 0 AND grade2 0`. The certificate's grid model
   `(a,b),(c,d)` with equal square-sums and difference-of-sums m is exactly this calculus with
   fixed two-element lists (rank condition structural), the witness `(1,1),(1,-1)` is the corpus
   witness `([1,1],[1,-1])`, and the parity engine `a+b = a^2+b^2 (mod 2)` mirrors the corpus's
   `list_sq_sum_mod_two`/`p2_scale_even`. The tex's "equal square-sums force even differences" is
   stated accurately for this model. (Scope note: the corpus itself scopes `p2_mstar_eq_two` to the
   line-sum instance and flags the all-holomorphic-pairs extension as not kernel-checked; the tex
   does not overreach that boundary.)
4. **Citations.** Every corpus citation verifies at its exact line (table below). The seven
   law-groups live in FOUR named Lean files; all four are clean of sorry/native_decide/axiom
   declarations (recounted by grep).
5. **Attributed links of the meta-law (Theorem 5).** R49 Theorem 6(ii) (FS iff Q2 via the
   packet-equivalence receipts, both directions) exists (round-49 tex :607-620); R50 Theorem 4
   (branch = defect sign, computable, no third behavior) and R50's Corollary `cor:quantifier`
   (the frontier test welded to the FS-lock) exist in the round-50 tex; the "114 committed worlds
   (R46)" attribution exists (round-49 tex :599). Ledger entries 085/092/107/108/109/110/111 all
   exist and are invoked by the artifacts as claimed.
6. **The Lean draft face.** `GSTLawStackRound51.lean`: header is DRAFT-NOT-COMPILED with the
   ledger-108 qualifier stated WITH the shape-record count ("no sorry tokens; three shape-record
   parts discharged by hypothesis records, content in the derivation") — compliant with the
   ledger-108 ban. PART A carries real tactic bodies (simp/ring/omega/induction/by_cases over
   integer arithmetic); PARTs B/C/D are disclosed [Shape record] parts whose bodies are hypothesis
   shuffles, accurately labeled. No sorry/axiom/native_decide usage (the only token occurrences are
   the header's denial sentences).
7. **Gates.** Banned adverbs (the five-adverb honesty gate): zero hits in tex+record.
   Armament tokens (the four-token armament gate): zero hits (the war/strike
   vocabulary present in the record is the operator's verbatim order plus the frame names WAR-0 /
   the standing "THE STRIKE" section idiom — none of the banned tokens). CJK: zero. "Q2 is not
   claimed" is present (tex :152, record :132) and is TRUE: no over-claim verbs occur near
   Clay/Hodge/Q2 anywhere; the closing string is not emitted; the polarity split stands.
8. **No blocked-route endings.** Zero hits for "it suffices / suffices to show / left for / future
   round / deferred". Theorem 6 ends by restating the open falsifiable line in the sharpened
   reachability form — the campaign's standing honest close.
9. **Claim-match vs the operator's order.** Both demanded sides are delivered and scoped: the
   always-gives equation (Theorem 2, carried by the corpus transport theorems at :93/:283 — real
   Lean proofs) and the break resolution (Theorem 4: the break law exists, its natural domain at
   the census avatar is empty). The re-read moves M1/M2/M3 are executed as described. The census
   scope is stated as a bounded avatar of 20 families, not the 114 worlds individually (tex :152)
   — the boundedness is disclosed; the circularity is not (F1).

## Findings

**F1 [BLOCKER] — the Y3 break-hunt is predetermined by its own input construction; the emptiness
of the witness set is an artifact, not a discovery; undisclosed.**
Location: `seed_orbit_break_hunt_round51_checks.py` Y3 (lines 329-496, the census loop), tex
Theorem 4 + proof (:103-116), record QUANTIFIER LINE.
Issue: the auditor verified structurally that in ALL 20 census families every rational-(p,p) box
input is an integer combination of the family's own cycle-lattice generators R, and R is contained
in the lattice generated by L, and every named input is a combination of L/R elements
(recomputation: "ALL 20 families: R inside lattice(L) AND named inputs inside lattice(L): True").
Therefore all 21 Y3 verdict checks (20 family + aggregate) CANNOT fail — the "branch A" verdict and
the "ZERO natural break witnesses" result are baked into the avatar's construction (the avatar
builds its rational (p,p) lattices FROM the algebraic generators, i.e. it assumes the algebraicity
it then "finds"). The Y4 planted-witness control proves the MACHINERY can output "not in lattice"
on injected vectors — teeth for the solver, not content for the hunt: no census input can ever
trigger it. The tex's proof states "a computation that can fail" and "the sweep certifies none
exists in the census", and the record says "the operator's test RUN, the negative fall searched
for and not found" — a search whose search space contains no possible witness by construction.
The docstring's disclosed integrity-guard list (fold-admission, deafness, channel-count) does NOT
include the Y3 layer; the docstring's contract "Every check that CAN fail carries a real computed
predicate" is false for 21 checks. This is the ledger-092/107 vacuity class at the round's
centerpiece, plus a ledger-111 header-self-description violation. Note the round-50 certificate
disclosed a WIDER cannot-fail list (channel-count, window-length, amplitude, blocking,
no-third-behavior, witness-blocking, invertibility) — the disclosure discipline regressed here.
Suggested repair (either): (a) rebuild the avatar so each world's rational (p,p) lattice is an
independent object (generators NOT all inside the cycle lattice) and let the sweep decide — a
genuine hunt; or (b) keep the avatar and re-disclose everywhere: add the census/hunt checks to the
docstring's integrity-guard list as transcription checks of the worlds' receipt lattices
(algebraicity inherited from R49 Thm 6(i) receipts), and reword Theorem 4's proof, the tex
certificate section, and the record's QUANTIFIER LINE to say the emptiness is inherited from the
receipts and the sweep verifies transcription + machinery — not that a hunt ran and found nothing.

**F2 [MAJOR] — the Y5 Gr(2,5) twist-invariance check adds literal zeros; the tex claims it was
"re-verified in exact arithmetic".**
Location: certificate lines 543-550; tex Theorem 5 proof (:133) and certificate section (:158).
Issue: the check computes `dc2_t = d_c2_0 + Fr(t)*Fr(0) + Fr(t*t,2)*Fr(0)` — the cross terms are
hardcoded `Fr(0)`, so the predicate is `x + 0 + 0 == x` at t = 1,2,3. It cannot fail and verifies
nothing about twist invariance; the label "the c_2 difference -144h^2+360s_2 is t-invariant at
t=1,2,3 (the vanishing cross terms)" states the theorem, not the predicate (ledger-109 violation),
and the tex's "re-verified in exact arithmetic" is not accurate. Contrast: round 49's certificate
computed the twist c_2-difference from an actual ch-table (round-49 checks line 781: `ok(d2 ==
Ring({(2,0):Fr(-144),(0,1):Fr(360)}), ... twist O(t))`) — the degeneration here is a regression,
not a corpus limitation. Suggested repair: port the R49 ch-table twist computation into Y5, or
delete the check and the tex's "re-verified" clause for the twist anchor.

**F3 [MAJOR] — the Y5 "meta-law chain" checks and the Y2 "rides" check are definitional on
constructed inputs; presented as link-by-link verification.**
Location: certificate lines 519-528 (link 1+2), 553-564 (link 3), 566-586 (chain + pair_exists),
283-292 (rides); tex Theorem 2 proof (:87) and Theorem 5 proof (:133).
Issue: the auditor recomputed — all 72 Y5 test inputs are either pure-class (60, zero defect
coordinates) or pure-defect (12, zero class coordinates); on such inputs "echelon membership iff
defect-zero iff pair-witness" holds by the construction of the split model (membership in CLASS_E
IS defect-zero for integer vectors), with zero possible mismatches. The three chain checks cannot
fail and verify the model's own definitions, not the meta-law's links. Likewise the rides check:
the block-fold structure (lower-left block identically zero) makes every zero-defect input stay
zero-defect under every one of the 96 folds (recomputation: 0 violations) — the 608-tower sweep is
predetermined by the block structure, which is itself the disclosed deafness guard. The tex
presents these as the model-level verification of Theorem 2 (the always-gives equation) and
Theorem 5's chain. Suggested repair: disclose the Y5 chain checks and the rides check as
transcription/definitional guards in the docstring's list (they verify the model faithfully
encodes the corpus iff-law :552 and the deafness law), or build substantive inputs (a lattice
where membership is a nontrivial decision, e.g. non-unit pivots, so that "membership iff
defect-zero iff pair-witness" has content).

**F4 [MAJOR] — hostile-battery item S5 is a tautology on a dead-code replica; the battery claims
"each detected" for six items.**
Location: certificate lines 603-604; docstring Y6; tex certificate section (:158).
Issue: `seal_fn(71,72) / seal_fn(72,72)` evaluates `not (71==72) and (72==72)` — always true — and
`seal_fn` is used nowhere else (dead code); the LIVE seal at Y7 is the direct `PRE == PINNED`
comparison, which S5 never exercises. The label "seal sensitivity (a shifted count breaks the
seal)" and the docstring/tex claim "S1-S6 ... each detected" overstate: five of six battery items
carry real corruption demonstrations (the auditor verified S1-S4 and S6 compute actually corrupted
objects), S5 demonstrates nothing. The live seal IS sensitive — the auditor verified externally
that removing one ok() call trips it (exit 1) — but the in-file battery item is vacuous.
Suggested repair: replace S5 with a live test (recompute the pre-seal count with one recorded check
suppressed and assert the seal condition would then fail), or reword the claims to "five in-file
detections + the seal verified by the external battery".

**F5 [MAJOR] — the tex misdescribes the type-climb verification: "the type climbing, at every
prefix" of the tower family is not what the code does, and the tower states' own class parts leave
the sector.**
Location: tex Theorem 2 statement (iii) (:78) and proof (:87); certificate lines 294-299.
Issue: the certificate's type check is a disconnected loop over `tau(depth, GAMMA)` for depth <= 24
(a restatement of the Y1 coverage law); it is never extracted from the tower states. In the model
the tower states' class parts do NOT stay in the sector: e.g. under the swap-A fold the seed's
class part (2,1,0) maps to (1,2,0), charge 2 — off-sector (and the model's seed vector (2,1,0,...)
is not even the claimed cell type (2,1,1)). So Theorem 2(iii)'s linkage "tower depth j_i <->
tau-depth" has no model-level verification; it is τ-level bookkeeping (Theorem 1(i)) presented
inside a tower theorem as "at every prefix depth". Suggested repair: reword the proof's
certificate parenthetical to "the type climb is verified at the tau level (the Theorem 1(i) law
restated at depths <= 24), not at tower prefixes", and either drop "at every prefix depth" from the
statement of (iii) or add a model linkage (fold matrices carrying explicit depth parameters).

**F6 [MAJOR] — the record pre-references this audit file and pre-claims its outcome (ledger-110
class).**
Location: record `2026-11-09-gst-round51-seed-orbit-break-hunt.md` :108-112 (AUDIT-51 section).
Issue: the record says "(see the audit file for the fresh adversarial agent's verdict, findings,
and the batched repair round; the closing re-check re-ran the certificate at green)" — at write
time AUDIT-51.md did not exist on disk and no repair round had run. Ledger entry 110 (the
pre-referenced-artifact scar, penalty -30) bans exactly this: "A record may reference only
artifacts that EXIST ON DISK at write time ... the reference is a debt, not a fact." The debt is
discharged by this audit, but the record must be finalized with the ACTUAL verdict and the ACTUAL
repair outcome before any push. Suggested repair: rewrite the AUDIT-51 section with the real
verdict (PASS_WITH_REPAIRS_REQUIRED, this file's findings) and the real post-repair re-run receipt.

**F7 [MINOR] — six arithmetic-tautology "receipt anchors" are outside the disclosed guard list;
three tex phrases overstate transcription as verification.**
Location: certificate lines 493-496, 540-541, 551; tex Theorem 3 proof (:98) and Theorem 5 proof
(:133).
Issue: `8*1==8`, `8*4==32`, `8*9==72`, `4462==2*2231`, the P^2 witness receipt (`2==2`), and
`360*(2/5)==144` are arithmetic identities that cannot fail; the "(receipt anchor)" label hints at
this but they are absent from the docstring's disclosed integrity-guard list, so the docstring's
"every check that CAN fail" contract misdescribes them. Additionally: "the arity totals 4,8,24,64
reproduced" (tex :98) — the totals are a hardcoded dict (`ARITY_LETTERS`), transcribed not
reproduced; "the P^2 scale group ... = 2Z" (tex :133) — the achievement direction is only
spot-checked at m = +/-2 (the grid does realize every even difference up to its bounds, but no
check verifies that); "the Weil world ... the crossing pin m*=2" is descriptive, not checked.
Suggested repair: add the receipt anchors to the disclosed guard list; change "reproduced" to
"transcribed"; either add the all-even-m achievement check or qualify the scale-group claim.

**F8 [MINOR] — count/bound/precision drifts between docstring, code, tex, and record.**
Location: certificate docstring line 14; tex :69; record :44, :101.
Issue: (i) the docstring says "seventeen committed families" while the code enforces 20
(`ok(n_worlds == 20)`) and the tex/record say twenty; (ii) the tex proof (:69) says the fence is
verified "at folds <= 20" but the code sweeps the five values {0,1,3,7,20} (the code label is
accurate; the tex drifts); (iii) the tex/record say "the seven cited files" but only FOUR Lean
files are cited by name (the seven refers to law-groups across those four files); (iv) the record's
"~6 s" run time is ~0.11 s on the auditor's machine, and its "113.25 KiB" is the PDF's size
attributed to the tex (the tex is 24 KiB). None is load-bearing; all are precision defects.
Suggested repair: fix all five.

**F9 [MINOR] — the title states the four-name equivalence without the frame qualifier.**
Location: tex title/subtitle (:12).
Issue: "the four-name equivalence: WAR-0 = the branch law = FS = the Clay statement" is stated
unqualified in the title, while the theorem (Theorem 5) correctly scopes it "In the committed fold
frame" with attributed links and the honest-scope section says Q2 is not claimed. The title can be
read as an unconditional equivalence claim. Suggested repair: add "in the committed fold frame" to
the subtitle (or "frame-equivalence").

## Sabotage results (external battery, on copies in /tmp; original untouched)

| # | Sabotage | Result |
|---|----------|--------|
| a | Corrupt the tau law (`d+2j` -> `d+j`) | **DETECTED** — FAILs: Y1 orbit coverage, Y1 the fence, Y2 the type climb, Y7 the seal; exit 1 (65 passed / 4 failed) |
| b | Plant a break witness `(1,0,0,0,0,1)` into the P2-seed family's named inputs | **DETECTED** — FAILs: Y3 family P2-seed (356 inputs), Y3 THE BREAK-HUNT, Y4 expel-receipt, Y7 seal; exit 1 |
| c | Tamper the seed (add a defect component: `(2,1,0,0,1,0)`) | **DETECTED** — FAILs: Y2 THE RIDES (1864 prefix states), Y7 seal; exit 1 |
| d | Break a chain link (truncate `P2_L` to `P2_L[:2]`) | **DETECTED** — FAILs: Y3 family P2-seed, Y3 THE BREAK-HUNT, Y4 expel-receipt, Y7 seal; exit 1 |
| e | Remove one ok() call (Y1 coverage) | **DETECTED** — FAIL: Y7 THE SEAL (`pre-seal count = 67 == pinned 68`); exit 1 |

All five external sabotages are detected with exit code 1. The certificate's machinery, count seal,
and tamper-detection paths are live. (The in-file battery's S5 item is separately vacuous — F4 —
but the live seal it fails to test passes the external test here.)

## Citation verification table

| Citation (as claimed) | Location in corpus | Verdict |
|---|---|---|
| births `nu=(2j+1,j,j)`, `de=(2j+2,j,j)`, `la=(2j+1,j+1,j)`, `rh=(2j+1,j,j+1)` at :457-472 | GSTGradedWorldAlgebra.lean :457/:462/:467/:471 | VERIFIED (all four defs exact) |
| `charge` :415 | :415 | VERIFIED |
| `purityGap` :424 | :424 | VERIFIED |
| `tate` :428 | :428 | VERIFIED |
| `charge_tate` :438 | :438 | VERIFIED |
| `purityGap_tate` :445 | :445 | VERIFIED |
| `charge_tensor` :557 | :557 | VERIFIED |
| `purityGap_tensor` :569 | :569 | VERIFIED |
| cosmic Tate fold :330-376 (degree :334, charge :341, composition :348) | :330/:334/:341/:348 | VERIFIED |
| birth signatures ":475-503" (certificate-internal) | :475-503 | VERIFIED (the three signature theorems, values match the certificate) |
| `transported_native_cycle_stays_algebraic` :93 | GSTGeneralSpaceCohomology.lean :93 | VERIFIED |
| `algebraicity_iff_split_causal_fold` :173 | :173 | VERIFIED |
| `causalTowerHodgeState` :270 | :270 | VERIFIED |
| `algebraicity_iff_any_finite_causal_tower` :283 | :283 | VERIFIED |
| `p2_mstar_eq_two` :414 | GSTGraphV2OntologicalFoldForAllN.lean :414 | VERIFIED (scope note: proven within the P2PairCal line-sum instance; witness `([1,1],[1,-1])` = (O(1)+O(1), O(1)+O(-1)); the all-holomorphic-pairs extension is corpus-flagged as not kernel-checked — the tex stays inside the instance) |
| `offRangeProjection_eq_zero_iff_range` :552 | GSTClassicalHodgeNativeOperatorCohomologyRealization.lean :552 | VERIFIED |
| `ambientClassDefectEquiv` :626 | :626 | VERIFIED |
| `nonzero_defect_blocks_every_native_operator` :671 | :671 | VERIFIED |
| `hodgeWeight_iff_intrinsicDefect_zero` :700 | :700 | VERIFIED |
| sorry/axiom/native_decide zero in the cited files | 4 named files, grep | VERIFIED (0 hits each; corpus-wide hits exist only in OTHER files, mostly prose denials) |
| corpus 743 Lean files at HEAD 1fdd62fa | git ls-files / rev-parse | VERIFIED (743; HEAD exact) |
| R49 Thm 6(ii) FS iff Q2 (packet-equivalence, both directions) | round-49 tex :607-620 | VERIFIED (exists as attributed) |
| R49 Thm 6(i) 114 committed worlds (R46) | round-49 tex :599 | VERIFIED |
| R50 Thm 4 / Thm 3(ii) / Corollary (branch=defect sign; closed defect transport; frontier welded to FS-lock) | round-50 tex :180-191, :152-176, cor:quantifier | VERIFIED (exists as attributed) |
| ledger 085/092/107/108/109/110/111 | MISTAKE_LEDGER.md | VERIFIED (all exist; 108's qualifier correctly carried by the Lean header; 109/110/111 are the classes violated by F2/F3/F4/F6) |

No citation FAILED. The "seven cited files" phrasing is loose (four files carry the seven
law-groups) — F8(iii).

## Required repairs before claiming success

1. **F1 (blocker):** disclose or rebuild the Y3 hunt. Either construct census worlds whose rational
   (p,p) lattices are independent of the cycle lattices (a real hunt), or add the census/hunt
   checks to the docstring's disclosed integrity-guard list AND reword Theorem 4's proof, the tex
   certificate section, and the record's QUANTIFIER LINE: the emptiness is inherited from the
   worlds' algebraicity receipts (R49 Thm 6(i)); the sweep verifies transcription and machinery.
   Remove "a computation that can fail" as a description of the hunt's content (it describes the
   solver, not the search space).
2. **F2:** replace the twist-invariance check with the R49-style ch-table computation at
   t=1,2,3, or delete the check and the tex's "re-verified in exact arithmetic" claim for the
   twist anchor.
3. **F3:** disclose the Y5 chain checks and the Y2 rides check as definitional/transcription guards
   (docstring list), or make their inputs substantive (non-unit-pivot lattices).
4. **F4:** replace S5 with a live seal test or reword the "each detected" claim to the accurate
   5-in-file + external-verdict form; delete the dead `seal_fn` replica.
5. **F5:** correct the tex's description of the type-climb verification (tau-level, not
   tower-prefix); drop or re-support "at every prefix depth" in Theorem 2(iii).
6. **F6:** finalize the record's AUDIT-51 section with the actual verdict and the actual
   post-repair re-run receipt before push (the current text is a pre-written receipt — ledger 110).
7. **F7:** add the six receipt anchors to the disclosed guard list; "reproduced" -> "transcribed"
   (arity totals); qualify or verify the scale-group achievement direction.
8. **F8:** fix the five precision drifts (seventeen->twenty; folds <= 20 -> {0,1,3,7,20}; seven
   cited files -> four files / seven law-groups; ~6 s; 113.25 KiB is the PDF).
9. **F9:** add the frame qualifier to the title's four-name equivalence.
10. Re-run the certificate twice after repairs (byte-identical, 69/0/exit 0 or the repaired count
    with an updated PINNED seal) and update the run receipts.

——

Auditor's summary judgment: the round's kernel-real layer (corpus citations, the orbit-law
identities, the P^2 parity model, the attributed R49/R50 links, the Lean face's labeling, the
gates) survives adversarial recomputation intact. The certification layer does not: roughly 33 of
the 69 checks cannot fail by construction (the docstring discloses 3 of them), and the cannot-fail
set includes the entire break-hunt layer and the meta-law chain layer — the two headline layers of
this round. The mathematics is not wrong; the hunt is empty by design and must be said to be so.
