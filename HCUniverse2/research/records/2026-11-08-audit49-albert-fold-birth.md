# AUDIT-49 — The Albert Fold-Birth (Round 49)

**Auditor**: structured self-play audit (the §4 STEP 2 fallback), **INDEPENDENCE
DOWGRADE DISCLOSED**: two fresh-agent dispatches failed on the infra context
deadline (the documented dispatch-failure class). The audit was executed as
structured self-play: the strongest case against each theorem was argued and
ruled on as referee. The mechanical portions (independent recomputations,
sabotage battery) were executed for real, in /tmp/audit49, on mutated copies.

**Artifacts audited**: GST_albert_fold_birth_round49_2026_11_08.tex (v2,
tectonic 0 errors), albert_fold_birth_round49_checks.py (573 checks / 0
failures / exit 0; pre-seal count 572 pinned; deterministic double-run
byte-identical; source md5 49c8f8ddd6ff84264233edc9121834c8; run md5
fa3d8e22fd20c5fd4d97cd4a6a7a5d38), runA.txt ≡ runB.txt.

## The checklist (10 points)

1. **CLAIM MATCH.** Each theorem's statement was read against its proof line
   by line. Thm 5's "derived landing cycles" claim verified structurally: the
   seeds' landings use ONLY the explicit pair + Lemma 4's conduit (Newton
   conductor + twist cancellation + Porteous + GAGA + Serre, all standard or
   certified) — the supplied `FoldProcessOn.landing_cycle` field is NOT
   invoked at the seeds. Thm 6 claims exactly the scope of (i)–(iii). PASS.
2. **HIDDEN STRENGTHENINGS.** Thm 1 claims refutation of (C2) *as a blanket
   modeling claim*, delivered by two rigorous witnesses + the meagreness
   shadow (disclosed as a finite shadow). Thm 3 claims the cancellation law
   at even degree — proven by the pair identity, no smuggled strength. PASS.
3. **CIRCULAR REDUCTIONS.** The FS-lock cites the corpus's packet-equivalence
   receipts as RECEIPTS (not new claims). The seeds' landings do not assume
   algebraicity anywhere: the pair is K^0-data, the conduit is
   conductor/twist/Porteous, the cycle is the degeneracy locus. The one
   strength-equivalence (FS ⟺ Q2) is stated AS the remaining line, not as a
   delivery. PASS.
4. **UNIFORMITY.** The odd-degree obstruction (Remark 2.3) is stated and
   confined to type I centers after the v2 repair (the maximal-subfield
   clause: types II/III carry degree-2e maximal subfields — even at every
   center degree). The mixed real/complex embedding case at Thm 3(iii) is
   covered by the same pair-identity argument (complex pairs and internal
   real pairs each contribute +1). PASS after repair.
5. **DEFINITION DRIFT.** (C1)/(C2) quoted as R48's Definition 3 states them;
   M_mid and the middle extraction as R32's; the pair/letter/cell vocabulary
   as R47/R48's. The round's new objects (Albert cells, orbit law, the FS
   law) are defined in-round. PASS.
6. **COMPUTATIONAL LEAPS.** Load-bearing checks: the Gr(2,5) three-twist
   Porteous difference (S5 sabotage: 3 failures fire), the Newton conductor
   (S1: 48 failures fire), the ch-table against the corpus (S2: fires), the
   pair split (S3: 14 failures fire), the count seal (S4: fires). The
   meagreness model is a disclosed finite shadow (X1). PASS.
7. **CASE LEAKS.** The Lefschetz hyperplane application (H^3(X)≅H^3(P^5) for
   dim X = 4) is correct; the Euler cross-check (c(X) = (1+h)^6/(1+3h) →
   (1,3h,6h²,2h³,9h⁴), χ = 27, b₄ = 23) independently recomputed. The A₁×A₂
   Künneth-level argument is complete with the classical
   Hodge-correspondence citation (v2 repair). PASS after repair.
8. **CITATION ACCURACY.** Thom–Porteous as the 1×1 determinant c_p(F) for
   the rank-drop-by-1 locus of σ: O^s → F, s = r−p+1 (Fulton Thm 14.4(a),
   the partition (f−k)^{e−k} at e = s, k = s−1) — verified against the
   statement's specialization. Serre's 2-adic Hilbert formula — verified
   against the known ramification data ((−1,−1)@{2,∞}, (−1,3)@{2,3},
   (−1,2) split) and the product formula (8 pairs). Albert's
   classification, GAGA, Serre generation, Baire — standard, cited at
   proven scope. PASS.
9. **HOSTILE COUNTEREXAMPLES.** Attempted: (i) mixed embedding fields at
   Thm 3 — the pair identity is per-pair, covered; (ii) the twist
   cancellation needing higher ch's — refuted by the quotient expansion
   (every cross term contains a vanishing e_j, j < p); (iii) sabotage
   battery — all five mutations DETECTED (S1 48 failures, S2 1, S3 14, S4
   seal BROKEN, S5 3). PASS.
10. **BLOCKED-ROUTE SMELL.** The FS-lock is a truthful reduction: it names
    the single missing construction, with the corpus's own equivalence
    receipts, and does not relabel any prior commitment as progress. The
    false hypothesis (C2) is killed, not absorbed. PASS.

## Findings and the repair batch

- **F8 (BLOCKER-presentation)**: Thm 4(ii)'s proof contained drafting
  dialogue ("wait --- ... ?? No: ..."). REPAIRED v2: clean scalar-trace
  statement; the follow-up remark rewritten as the verification remark.
- **F6 (MAJOR)**: Thm 2(b) understated the letter coverage — types II/III
  contain maximal subfields of degree 2e at EVERY center degree, so the
  odd-degree obstruction is confined to type I centers. REPAIRED v2: the
  maximal-subfield clause added; Remark 2.3's scope corrected accordingly.
- **F7 (MINOR)**: the alternating trace law's σ-scope (an involution of K —
  even-degree Galois or CM letters; odd-degree vacuous) now stated in
  Thm 3(vi)(2). REPAIRED v2.
- **F5 (MINOR)**: the cross-Hom vanishing now cites the classical
  Hodge-correspondence theorem for abelian varieties precisely. REPAIRED v2.
- **F10 (MINOR, inherited)**: the R41 h ≤ 2 computed-ranks disclosure
  re-flagged at Thm 6(i). REPAIRED v2.
- **F9-seal (MAJOR, found by the audit's own sabotage run)**: the count-seal
  pinning edit had silently failed to apply (PINNED_PRE was still None —
  the seal was INERT, S4 undetected). REPAIRED: the seal block properly
  installed; S4 now detects (seal BROKEN, exit 1); double-run re-verified
  byte-identical; the pre-seal count re-pinned at 572.
- **F12 (LABEL, disclosed)**: the meagreness model is a finite shadow
  (labeled as such in the certificate); the Baire step itself is standard
  mathematics cited in the derivation.

## Independent recomputations (fresh code, /tmp/audit49)

- Euler characteristic of the cubic fourfold: c(X) = (1+h)^6/(1+3h) mod h^5
  = (1, 3h, 6h², 2h³, 9h⁴); χ = ∫9h⁴ = 27. **MATCHES.**
- Gr(2,5) c₂-difference at a new twist t = 3: −144h² + 360s₂ (and the
  certificate itself covers t ∈ {1,2,3} — the audit's requested "new"
  twist is included in the shipped battery). **MATCHES.**
- N(3 + 2√5) = 9 − 20 = −11. **MATCHES.**
- Hilbert (2,3): (2,3)₂ = −1, (2,3)₃ = −1 (ramified at {2,3}); product
  formula verified on (6,10) and seven further pairs. **MATCHES.**
- Newton conductor at p = 4: e₄ = −6m = (−1)³·3!·m. **MATCHES.**

## Sabotage battery (mutated copies, /tmp/audit49)

| ID | Mutation | Result |
|----|----------|--------|
| S1 | conductor expected sign flipped | **DETECTED** — 48 failures, exit 1 |
| S2 | TABLE entry corrupted (B(2,0) ch₂: 5/2 → 3/2) | **DETECTED** — 1 failure, exit 1 |
| S3 | ξ₃₆₀ coordinate sign swapped (351 → −351) | **DETECTED** — 14 failures, exit 1 |
| S4 | pinned seal broken (572 → 571) | **DETECTED** — seal BROKEN, exit 1 |
| S5 | expected twist difference corrupted (−144 → −145) | **DETECTED** — 3 failures, exit 1 |

## Verdict

**PASS — THE LOOP CLOSED.** One presentation blocker, one coverage
understatement, one inert-seal defect (found and fixed by the audit's own
battery), and four label-level repairs — all repaired in the v2 batch; the
mathematics of all six theorems survived every attack; the certificate is
tamper-sensitive on all five sabotage axes; the double-run is
byte-identical with the seal live. The independence downgrade (self-play
after two failed dispatches) is disclosed in the header and stands as the
round's audit-integrity caveat.
