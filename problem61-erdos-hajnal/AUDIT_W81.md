# AUDIT W81 — the independent #61 audit (W81-61B lane, commander-finished)

Engine: `engine61audit_w81.py` — 13/13 PASS (wall 113.4s), fresh code paths
throughout (own canonical-form enumeration, own B&B α/ω, own censuses).
Receipts: `receipts61audit_w81.txt`. The engine's cross-audit battery (A12)
verifies the sibling W81-61A lane's data byte-exactly.

## THE DEFECT LEDGER

Zero defects found in the banked #61 package. Every table, count, h-row, and
structural law re-verified by independent code — exact agreement everywhere:

| audited | audit check | verdict |
|---|---|---|
| Graph canon + class counts | A0-CANON (Bell numbers, self-complements, comp(P5)=house, K2[2K1,2K1]≅C4) | PASS |
| P4-free perfectness (Seinsche) | A1-P4PERFECTNESS (6,039 labeled graphs n≤6: χ=ω, α·ω≥n, max≥⌈√n⌉, SL — 0 violations) | PASS |
| The F7 board (7 H-cases) | A2-F7BOARD | PASS |
| h-tables (C5/P5/house/bull/2K2/C4/P3/3K1/claw) n≤7 | A3-HTABLES (two codes; n=5/n=7 counts exact vs bank: C5-free 1012/1,742,336; P5-free 964/1,019,492; bull-free 964/876,632; corrupted-h detection live) | PASS |
| R(3,3)=6 + the K5 theorem | A4-RAMK5 (32,768 graphs exhaustive; DP R(5,3)=15, R(5,4)=35; 33,694 K5-free n≤6 + 450 sampled n≤12: 0 violations) | PASS |
| The C5 endgame | A5-C5ENDGAME (W8 tower: X_2 EXHAUSTIVE C(64,5)=7,624,512 scan 0 induced C5, α=ω=9=3²; X_3 slot-complete, 27+27 exhibited; cap c=log3/log8; FRESH n=9/n=10 hom-3 witnesses — LADDER-BREAK independently re-certified; n=11 hunt consistent with the open cell) | PASS |
| Substitution + harmonic law | A6-SUBSTEXP (200 blow-ups; formulas 94 exact; 1/f=1/c₁+1/c₂ exact rationals; adversary cap; Theorem 4B min-law 60 instances; ALL edge cases: K2[K1,K1]=K2, P3[K1×3]=P3, single-slot, K1 blocks, empty vacuous, 4C associativity) | PASS |
| INH direction | A7-INH-DIRECTION (18,779 checks; the wrong direction REFUTED: bull-free K3 carries K3) | PASS |
| L-PC + L-COMP | A8-LPC-LCOMP (533 C4-free n≤14 anchors; 75 mirror complements; concentration TIGHT at C5) | PASS |
| P5-domination + BULL-L1 | A9-P5DOM-BULL (19,976 census exact {K1:5244, K2:14240, P3:372, K3:120}; BULL-L1 8,340 pairs 0 violations — superset of the campaign's 4,292) | PASS |
| C5 closure + reduction | A10-C5CLOSURE (800 constructive pairs; the subadditivity spine 500 instances) | PASS |
| Negative controls | A11-NEGCTL (all planted hosts detected; corrupted h-rows rejected; substitution probe live) | PASS |
| The W81-61A cross-audit | A12-61A-CROSS (bull-free labeled [1,2,8,64,964,24248] exact; h-rows exact; C5 cores 420/18,840 exact; X_2/X_3 towers certified P5/bull-free with hom 4/8; the slot lemma for P5 and bull; P5-CROSS 15,960 instances 0 violations + 1,338 planted violations each inducing a verified P5; z-only 372=372; the anchor laws 0-violation censuses) | PASS |

## THE ANCHOR-LAW PROOFS (promised in A12 — complete)

Both C5 anchor laws are corollaries of C5-freeness, by direct induced-subgraph
exhibition:

**C5-2ANCHOR.** In a C5-free G, let T be a triangle, xy an edge of T,
p ∈ N(x)∖N(y), q ∈ N(y)∖N(x), r outside N(x) ∪ N(y). Then p ∼ r ∧ q ∼ r
implies p ∼ q. *Proof:* if p ≁ q, the 5-set {p,x,y,q,r} carries exactly the
edges p-x, x-y, y-q, q-r, r-p (non-edges: p-y, x-q by the cell definitions;
p-q by assumption; x-r, y-r by r's cell) — the induced cycle p-x-y-q-r-p, an
induced C5. Contradiction. ∎

**C5-1ANCHOR.** In a C5-free G, let T be a triangle, a ∈ T, b, e ∈ N(a),
c, d outside N[a]. The configuration b∼c, c∼d, d∼e, b≁d, b≁e, c≁e is
forbidden. *Proof:* the 5-set {b,c,d,e,a} carries exactly the edges b-c,
c-d, d-e, e-a, a-b (non-edges: b-d, b-e, c-e by hypothesis; c-a, d-a by the
cells) — the induced cycle b-c-d-e-a-b. Contradiction. ∎

The A12 mechanics battery plants each configuration on random graphs and
machine-verifies every planted 5-set as an induced C5 (0 failures) — both
laws have teeth, and the 0-violation censuses (11,520 + 16,923 instances on
C5-free graphs) confirm the laws hold exactly on the class.

## VERDICT

The #61 package is CLEAN — zero defects, every claim independently
re-verified, and the W81-61A lane's new theorems (P5-CROSS, C5-1/2-ANCHOR,
TOWER-CAP-P5/BULL) are cross-certified with complete induced-subgraph proofs.
The n=11 C5 cell (h_C5(11) ∈ [3,4]) is measured consistently by both lanes —
the W80 record's exact scope stands.

#BY GST LAW bracket_skew [arsenal-full/HC-PROOF-research/GSTCausalPairingGraphs.lean:18] — the antisymmetry bracket v w = −bracket w v behind the canon's relabel-invariant orientation discipline.

The engine never stops; it never lies.
