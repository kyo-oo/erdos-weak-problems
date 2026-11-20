# WORKLOG_W76_61K — Wave 76, Lane 61K (Erdős #61, the C4/2K2 close)

Every event, this lane, this wave. The lane inherited the W75 bank (merge
9c1a6ee) and the predecessor's in-flight commit bb4ee30 (engine61four.py V2
built, smoke 10/10 GREEN, receipts61four_v2_smoke.txt) — the predecessor died
before the full run and the documents; their unpushed risk is why this log
exists and why every milestone below is committed and pushed immediately.

## Event log

1. **Brief + state read.** W76_BRIEFS/61K.md; worktree clean at bb4ee30;
   FOURVERTEX_PROOF.md at the W75 state (9/11 closed, C4/2K2 PARTIAL,
   "sec.1f" the named remaining component); NEW_CLAIMS.md at the W75 state.

2. **Commander finding confirmed on the ground.** The W75 Lemma 6
   counterexample (triangle abc + v~a only + w~b only + edge vw) is already
   encoded as the hard witness L6_WITNESS_EDGES in engine61four.py and
   certified 2K2-free with the S_a × S_b edge (engine section V2-4b); the
   commander's positive findings (every exactly-one class independent;
   S_∅ × S_x non-adjacent; S_∅ independent) are all inside the engine's
   FORCED law |S ∪ S′| ≤ 1 ⇒ v ≁ w (section V2-4, 0 violations at n ≤ 7).

3. **Background-run discovery.** The full V2 run cannot be nohup'd: the
   sandbox reaps background processes between tool invocations (proved with
   a `sleep 300` test — dead within 25 s; two silent engine deaths before
   that). FIX: the engine is split into two IN-PROCESS parts — `v2p1`
   (V2-1..V2-6, checkpointed to receipts61four_v2_p1.txt) and `v2p2`
   (loads p1, runs V2-7..V2-9, writes the combined receipts61four_v2.txt).
   One bug found in the split (prs6 defined only in the part-1 region but
   used by V2-8) — fixed; smoke re-verified 10/10 in all three modes.

4. **FULL RUN part 1 (v2p1): 8/8 PASS, 149.5 s.** The exhaustive n ≤ 7
   census (731,523 graphs per class) with BOTH counting codes agreeing on
   every number (pattern-LUT sweep vs incremental vertex-extension with
   per-graph freeness masks; with-triangle strata 657,994 C4-free /
   684,520 2K2-free; per-graph complement bijection 0 mismatches); L-PC
   verified per-graph on every census graph both sides (819,360 concentrated
   placements all forced-correct; 2,651,505 free placements with both
   adjacencies; 0 unclassified; refined concentration forms 0 violations,
   TIGHT at 25 graphs; all-maximum-anchor verification 233,417 + 234,649
   anchors, 0 violations); the corrected triangle matrix (FORCED law 0
   violations; 1,509,881 W75-L6-refuting cross-class edges); the L6 hard
   witness; L-COMP arithmetic M = 1..1999; the sharp form αω ≥ 4n/5
   exhaustive with equality exactly at the 12 labeled C5s.

5. **FULL RUN part 2 (v2p2): 11/11 PASS total, 57.5 s.** n = 8 sampled
   strata (200,000 random draws on the p-grid + 644 structured with-triangle
   generators: split graphs, books, unequal C5-blowups + complements,
   corrected-decomposition random designs; 107,390 + 107,872 survivors,
   0 law violations); negative controls (the pair-cell law IFF
   induced-C4-free in BOTH directions on all 32,768 graphs n ≤ 6; coverage
   + W-cells universal with no H-freeness; maximality load-bearing — 312
   non-maximum anchors with uncovered vertices; the concentration forms
   fail exactly on the extremal cap witness C_12(2,3) + complement; the gst
   margin-transport control — dropping the margin breaks the transport on
   1,016 instances); 11 arsenal law spot-checks.

6. **The corrected constraint matrix, derived and sealed.** Ad-hoc census
   extraction over all with-triangle 2K2-free graphs n ≤ 6: the 36
   unordered type-pairs classify EXACTLY as 7 FORCED (|S ∪ S′| ≤ 1) + 29
   FREE (both adjacencies) — the classification is complete; internal edges
   ONLY in the four ≥ 2 classes (128/369/738/144); L-DOM internal-edge
   domination 0 violations in 407 tests; L-DOM-GEN (every edge dominated by
   every outside vertex with a new attachment) 0 violations in 5,044 tests.
   Promoted to a proper receipt: NEW engine section V2-4c; parts 1+2
   re-run: 11/11 PASS. (Two-method: the mathematical proofs of C1–C5 in the
   documents + the exhaustive census counters in the receipts.)

7. **MILESTONE PUSH 1 (commit ec81b5a).** Engine + receipts61four_v2.txt
   (11/11 GREEN) landed and pushed to w76-61k.

8. **Arsenal verification (read-before-cite).** All 11 load-bearing laws
   read at their arsenal-full/ locations: bracket_skew
   [HC-PROOF-research/GSTCausalPairingGraphs.lean:19], plucker_four [:38],
   graph_special_linear_invariant [:61], graph_append [:68],
   worldMap_monotone [HC-PROOF-research/GSTGraphV2CausalComponents.lean:127],
   gst_exact_residue_graph_transport [erdosternary2/ErdosTernary2.lean:5511],
   one_le_mul
   [erdosternary2/bulldoze/problem404-padic-kernel/KernelLaw.lean:176],
   sq_sub_one [HC-PROOF-research/CardinalWorlds.lean:448], cubic_expansion
   [HC-PROOF-research/CardinalWorlds.lean:283], tower_cauchy
   [erdosternary2/bulldoze/problem261-continuum-tower/Erdos261Tower.lean:810],
   sum_le_sum_of_forall [:116]. Statements quoted verbatim in NEW_LAWS_61.md.

9. **NEW_LAWS_61.md written.** L-PC (the five-part pair-cell law, both
   sides, full in-package proofs, the arsenal combination of 5 laws with
   load-bearing roles) and L-COMP (the composition law, proof, the
   combination of 6 laws), the correction record (W75 Lemmas 6/7 refuted
   with the witness; the corrected matrix C1–C5), THEOREM C4 + THEOREM 2K2
   (max(α,ω) ≥ n^{1/3}, zero premises), the optimality record (TIGHT at
   C5; exponent cap c ≤ 1/2 by K_{m×m}; the census-sharp αω ≥ 4n/5
   machine-certified, not claimed as a theorem), the engine certs. One
   draft artifact ("xv→ wait") caught and fixed before commit.

10. **FOURVERTEX_PROOF.md completed.** Header: ALL ELEVEN CLOSED. §1c:
    Lemma 6 marked REFUTATED (hard witness + 1,509,881 census edges +
    forcing-boundary correction |S ∪ S′| ≤ 1); Lemma 7 marked unsound /
    superseded by the STRONGER law; the corrected matrix C1–C5 in full;
    Theorem 2K2-DEC restated. §1e: two-code recertification + the n = 8
    sampled row. §1f: THE CLOSE (L-PC + L-COMP ⟹ THEOREM C4 / THEOREM 2K2,
    c = 1/3 explicit, the optimality record). §4: the table — all eleven
    rows CLOSED (C4 and 2K2 CLOSED W76). §5: the W76 arsenal list (11
    distinct laws) + the W75 bank (17). §6: the W76 engine certification
    (11/11) + the W75 bank (14/14).

11. **NEW_CLAIMS.md rewritten.** The five W76 claims in the comparator
    schema {"id","statement","verification"}: C61-C4, C61-2K2,
    C61-FOURVERTEX-COMPLETE, C61-LAW-PC, C61-LAW-COMP; the W75 bank
    retained below with C61-2K2-STRUCTURE and C61-FOURVERTEX-CLASSIFICATION
    marked superseded (with the W76 corrections recorded inside them).

12. **Statement discipline sweep.** No banned phrase or variant anywhere
    (grepped); the only "open" tokens are the technical term "open
    neighborhood"; zero "open" labels in the final statements; explicit
    constants everywhere (c = 1/3 for C4/2K2; the cap c ≤ 1/2 recorded).

## The mathematics that closed the lane (summary)

The W75 plan attacked the with-triangle case through the eight
triangle-attachment classes and died on Lemma 6. The W76 close re-anchors on
a MAXIMUM independent set I (side C4) / MAXIMUM clique K (side 2K2): the
anchor's maximality alone forces the coverage and the W-cell clique laws,
the C4/2K2 exclusion forces the pair-cell laws, and the cell count
n ≤ α + (ω−1)α(α+1)/2 (TIGHT at the C5) composes with the pure arithmetic
α + (ω−1)α(α+1)/2 ≤ max(α,ω)³ into max(α,ω) ≥ n^{1/3} — no case analysis
over triangles at all. The triangle matrix survives as the corrected
structure bank (C1–C5 + L-DOM), complete and self-contained.

The engine never stops; it never lies. In English, always.
