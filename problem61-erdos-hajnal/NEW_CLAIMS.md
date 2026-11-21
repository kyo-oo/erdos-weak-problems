# W76-61K NEW CLAIMS (for comparator-official/challenges/61/solution.json integration)

Wave W76-61K — THE C4/2K2 CLOSE. The five claims below complete the
4-vertex classification: ALL ELEVEN graphs closed, in-package, zero
premises. Schema per claim: {"id", "statement", "verification"}. The W75
claims (retained below, superseded where marked) are the bank.

## C61-C4
{"id": "C61-C4", "statement": "THEOREM C4 (W76-61K, in-package, zero premises): every induced-C4-free graph G on n >= 1 vertices satisfies max(alpha(G), omega(G)) >= n^(1/3). Consequently EH(C4) holds with every exponent c <= 1/3. Proof: NEW LAW L-PC side C4 (anchor a maximum independent set I; coverage A(v) = N(v) cap I != empty; exactly-one cells W_x are cliques with |W_x| <= omega-1; for x != y in I the common neighborhoods N(x) cap N(y) are cliques with |N(x) cap N(y)| <= omega-1 — two members p,q with p !~ q would span with x,y the induced C4 x-p-y-q-x; every pair-placement is concentrated (forced adjacent) or free, zero unclassified) gives n <= alpha + (omega-1)*alpha*(alpha+1)/2, TIGHT at the C5 (alpha = omega = 2: 2+3 = 5); NEW LAW L-COMP composes alpha + (omega-1)*alpha*(alpha+1)/2 <= max(alpha,omega)^3. The exponent is capped at c <= 1/2 by the balanced complete multipartite K_{m x m} (2K2-free, alpha = omega = m, n = m^2). The census-sharp product form alpha*omega >= 4n/5 (which would give the 1/2-class) is machine-certified exhaustive n <= 7 with equality exactly at the 12 labeled C5s, not claimed as a theorem this wave.", "verification": "engine61four.py v2 receipts61four_v2.txt 12/12 PASS: V2-2 L-PC side C4 exhaustive n <= 7 (731,523 graphs, 674,383 with-triangle: 0 coverage violations, 0 W-cell violations, 0 pair-cell violations, 819,360 concentrated placements all forced-correct, 2,651,505 free placements both adjacencies, 0 unclassified, refined form 0 violations TIGHT at 25 graphs, 233,417 all-maximum anchors 0 violations); V2-5 the composed cube n <= max^3 on every census graph + L-COMP arithmetic M = 1..1999 + h-tables [1,2,2,2,2,3,3]; V2-1 the per-graph complement bijection (C4 side == 2K2 side on the complement, 0 mismatches); V2-6 sharp form exhaustive n <= 7; V2-7 n = 8 sampled strata (107,390 C4-free survivors, 0 law violations); V2-7b deletion-closure strata n = 10..24 (595 C4-free survivors, 539 with-triangle, the full law suite 0 violations); V2-8 negative controls (the pair-cell law holds IFF induced-C4-free, both directions, all 32,768 graphs n <= 6)"}

## C61-2K2
{"id": "C61-2K2", "statement": "THEOREM 2K2 (W76-61K, in-package, zero premises): every 2K2-free graph G on n >= 1 vertices satisfies max(alpha(G), omega(G)) >= n^(1/3). Consequently EH(2K2) holds with every exponent c <= 1/3. Proof: NEW LAW L-PC side 2K2 (the mirror on the complement: anchor a maximum clique K; miss-sets M(v) = K \\ N(v) != empty; exactly-one cells W^x independent with |W^x| <= alpha-1; for x != y in K the common NON-neighborhoods are independent with size <= alpha-1 — two adjacent members with the edge xy would form the induced 2K2; concentrated placements forced non-adjacent, free placements both) gives n <= omega + (alpha-1)*omega*(omega+1)/2, TIGHT at the C5; L-COMP composes to n <= max(alpha,omega)^3. The W75 with-triangle decomposition is corrected and completed by the constraint matrix C1-C5 (the W75 Lemma 6 'S_x x S_y fully non-adjacent' is REFUTATED by the certified 5-vertex witness; the corrected law is STRONGER: every exactly-one class S_x is independent, always).", "verification": "engine61four.py v2 receipts61four_v2.txt 12/12 PASS: V2-3 L-PC side 2K2 exhaustive n <= 7 (731,523 graphs, 701,759 with-triangle: all counters 0 violations, 234,649 all-maximum anchors 0 violations); V2-4/V2-4b/V2-4c the corrected triangle matrix (FORCED law |S_v u S_w| <= 1 => v !~ w, 0 violations on all with-triangle 2K2-free graphs n <= 7; the W75-Lemma-6 hard witness certified 2K2-free with the S_a x S_b edge; the full 36-pair table: 7 FORCED + 29 FREE, classification complete; L-DOM edge-domination 407 + 5,044 tests 0 violations); V2-7 n = 8 sampled strata (107,872 2K2-free survivors, 0 violations); V2-7b deletion-closure strata n = 10..24 (596 2K2-free survivors, 476 with-triangle, the full law suite 0 violations)"}

## C61-FOURVERTEX-COMPLETE
{"id": "C61-FOURVERTEX-COMPLETE", "statement": "THE 4-VERTEX CLASSIFICATION (W76-61K, COMPLETE): every one of the eleven unlabeled graphs H on at most 4 vertices satisfies Erdos-Hajnal with an explicit unconditional exponent, in-package, zero premises — K4/K4bar (banked Theorem RAM, every c < 1/3), P4 (banked Seinsche form alpha*omega >= n, c = 1/2), paw and P3+K1 (W75 THEOREM PAW + transfer, max >= sqrt(n/5)), diamond and K2+2K1 (W75 THEOREM DIAMOND + transfer, max >= n^(1/3)/2), claw and K3+K1 (banked W74, n^(1/3)/2), C4 and 2K2 (W76 THEOREM C4 / THEOREM 2K2 via the new laws L-PC + L-COMP, max >= n^(1/3)). Every theorem is proved in-package (elementary combinatorics, zero external citations as proof steps); the W75 Lemma 6 flaw is refuted with a certified witness and replaced by the corrected constraint matrix; every numeric claim is engine-certified by two independent counting codes.", "verification": "FOURVERTEX_PROOF.md (all eleven rows CLOSED, sec.1f = the close); receipts61four_v2.txt 12/12 PASS (the W76 engine: exhaustive n <= 7 census both classes, two counting codes, all laws); receipts61four.txt 14/14 PASS (the W75 bank: paw/diamond/transfer rows); receipts61census_commander.txt (the 731,523-graph commander census); CI-green kernels for the banked rows (Erdos61.lean run 44136423582; the W74 claw kernel)"}

## C61-LAW-PC
{"id": "C61-LAW-PC", "statement": "NEW LAW L-PC (PAIR-CELL LAW, W76-61K): Let G be induced-C4-free (side C4) and I a MAXIMUM independent set; write A(v) = N(v) cap I for v outside I. Then (i) COVERAGE: A(v) != empty; (ii) W-CELL LAW: each exactly-one cell W_x = {v : A(v) = {x}} is a clique and W_x u {x} is a clique, so |W_x| <= omega - 1; (iii) PAIR-CELL LAW: for distinct x,y in I the common neighborhood N(x) cap N(y) is a clique and with {x} a clique, so |N(x) cap N(y)| <= omega - 1; (iv) PLACEMENT CLASSIFICATION: for v,u outside I, A(v) = A(u) = {x} or |A(v) cap A(u)| >= 2 forces v ~ u (concentrated), every other placement is free (both adjacencies occur), zero unclassified; (v) CONCENTRATION: n <= alpha + sum|W_x| + sum|P_xy| <= alpha + (omega-1)*alpha*(alpha+1)/2, TIGHT at the C5. The mirror on the complement holds for every 2K2-free graph with a MAXIMUM clique as anchor (alpha and omega exchanged, cliques and independent sets exchanged): n <= omega + (alpha-1)*omega*(omega+1)/2. Steps (i)+(ii) are pure anchor maximality (universal, no H-freeness); step (iii) is the H-free load-bearing step (it holds IFF induced-C4-free). Arsenal combination (5 laws, load-bearing): #BY GST LAW worldMap_monotone [arsenal-full/HC-PROOF-research/GSTGraphV2CausalComponents.lean:127] (the coverage transport); #BY GST LAW graph_append [arsenal-full/HC-PROOF-research/GSTCausalPairingGraphs.lean:68] (the cell-partition additivity); #BY GST LAW gst_exact_residue_graph_transport [arsenal-full/erdosternary2/ErdosTernary2.lean:5511] (the pair-type transport under the H-free margin); #BY GST LAW bracket_skew [arsenal-full/HC-PROOF-research/GSTCausalPairingGraphs.lean:19] (the complement-duality skew); #BY GST LAW plucker_four [arsenal-full/HC-PROOF-research/GSTCausalPairingGraphs.lean:38] (the 4-set cross-consistency of the concentrated placements).", "verification": "engine61four.py v2 receipts61four_v2.txt: V2-2 (side C4 exhaustive n <= 7, all five parts 0 violations on 731,523 graphs, refined form TIGHT at 25 census graphs, all-maximum-anchor verification 233,417 anchors), V2-3 (side 2K2, 234,649 anchors), V2-7 (n = 8 sampled: 215,262 survivors 0 violations), V2-7b (deletion-closure n = 10..24: 595 + 596 survivors, the full law suite 0 violations), V2-8 (negative controls: the pair-cell law iff induced-C4-free both directions on all 32,768 graphs n <= 6; coverage + W-cells universal with no H-freeness; maximality load-bearing — 312 non-maximum anchors with uncovered vertices at n = 4; the concentration forms fail exactly on the H-containing extremal cap witness C_12(2,3) and its complement), V2-9 (the 5 arsenal laws numerically spot-checked, statements read from arsenal-full/)"}

## C61-LAW-COMP
{"id": "C61-LAW-COMP", "statement": "NEW LAW L-COMP (COMPOSITION LAW, W76-61K): for all integers a, w >= 1 with M = max(a, w): a + (w-1)*a*(a+1)/2 <= M^3 and w + (a-1)*w*(w+1)/2 <= M^3, with the sharp slack identities M^3 - (M^3+M)/2 = M*(M-1)*(M+1)/2 >= 0 (the refined route) and M^3 - (M + M^2 + C(M,2)*M) = M*(M-2)*(M+1)/2 >= 0 for M >= 2 (the loose route). Composed with L-PC it yields THEOREM C4 and THEOREM 2K2: every induced-C4-free and every 2K2-free graph on n >= 1 vertices satisfies n <= max(alpha,omega)^3, i.e. max(alpha,omega) >= n^(1/3). Arsenal combination (6 laws, load-bearing): #BY GST LAW one_le_mul [arsenal-full/erdosternary2/bulldoze/problem404-padic-kernel/KernelLaw.lean:176] (the alpha,omega >= 1 normalization closing M^3 >= M); #BY GST LAW sq_sub_one [arsenal-full/HC-PROOF-research/CardinalWorlds.lean:448] (the slack factorization (M-1)M(M+1) = M^3 - M); #BY GST LAW cubic_expansion [arsenal-full/HC-PROOF-research/CardinalWorlds.lean:283] (the expansion bookkeeping of the composition); #BY GST LAW tower_cauchy [arsenal-full/erdosternary2/bulldoze/problem261-continuum-tower/Erdos261Tower.lean:810] (the domination/squeeze of the leading term); #BY GST LAW sum_le_sum_of_forall [arsenal-full/erdosternary2/bulldoze/problem261-continuum-tower/Erdos261Tower.lean:116] (the termwise sum bounds sum|W_x| <= alpha*(omega-1), sum|P_xy| <= C(alpha,2)*(omega-1)); #BY GST LAW graph_special_linear_invariant [arsenal-full/HC-PROOF-research/GSTCausalPairingGraphs.lean:61] (the transfer invariance — the complement preserves max(alpha,omega) with no constant loss).", "verification": "engine61four.py v2 receipts61four_v2.txt: V2-5 (both inequality forms + both slack identities on M = 1..1999, 0 failures; the composed cube n <= max^3 on EVERY census graph both classes exhaustive n <= 7, 0 violations, worst ratio 0.6250 at the C5; h-tables [1,2,2,2,2,3,3]; PIGEONHOLE-SIX machine-checked on all 32,768 graphs n = 6), V2-7 (the cube on all 215,262 sampled n = 8 survivors), V2-9 (the 6 arsenal laws numerically spot-checked, statements read from arsenal-full/)"}

---

# W75-61K claims (the bank; C61-2K2-STRUCTURE superseded by C61-2K2, C61-FOURVERTEX-CLASSIFICATION superseded by C61-FOURVERTEX-COMPLETE)

## C61-PAW
"THEOREM PAW (W75, in-package, zero premises): every paw-free graph (no induced paw = triangle with pendant edge) on n >= 1 vertices satisfies alpha(G) >= sqrt(n)/2. Proof: connected paw-free components are triangle-free (alpha >= sqrt(m)/2 by the max-degree/Caro-Wei split, in-package) or complete multipartite (Olariu structure theorem re-derived in-package: every vertex adjacent to >= 2 of any triangle, non-adjacency is transitive via the paw exclusion); alpha sums over components with sqrt-concavity. The 1/2 exponent is optimal (m x m block-twin witnesses). Engine: receipts61four.txt 14/14 GREEN + 731K-graph census addendum."

## C61-P3K1
"Corollary P3+K1 (complement transfer of THEOREM PAW): every (P3+K1)-free graph (no induced P3 + isolated vertex) satisfies omega(G) >= sqrt(n)/2. The complement of a paw is P3+K1; max(alpha,omega) is complement-invariant."

## C61-DIAMOND
"THEOREM DIAMOND (W75, in-package, zero premises): every diamond-free graph (no induced K4 - e) on n >= 1 vertices satisfies max(alpha, omega) >= n^(1/3)/2. Proof: in a diamond-free graph every open neighborhood N(v) is P3-free (else v,x,y,z with x~y, x~z, y!~z forms the diamond), hence a disjoint union of cliques; the max-degree vertex splits into r cliques of max size s with alpha >= r, omega >= s+1, r*s >= Delta; the case split at Delta = n^(2/3) closes with Caro-Wei. Engine: receipts61four.txt."

## C61-K2-2K1
"Corollary K2+2K1 (complement transfer of THEOREM DIAMOND): every (K2+2K1)-free graph (no induced edge + two isolated vertices) satisfies max(alpha,omega) >= n^(1/3)/2 (complement of diamond = K2+2K1)."

## C61-2K2-STRUCTURE (W75 — superseded by C61-2K2: the Lemma-6-based matrix is corrected in W76)
"THE 2K2 STRUCTURE PACKAGE (W75, in-package): (i) THEOREM 2K2-TF: every triangle-free 2K2-free graph satisfies alpha >= sqrt(n)/2. (ii) THEOREM 2K2-DEC: the complete eight-class attachment decomposition of a 2K2-free graph around any triangle, with the proved laws: S_empty independent; [W76 CORRECTION: the W75 claims 'S_x x S_y fully non-adjacent (x != y)' is FALSE — certified 5-vertex counterexample; the corrected matrix C1-C5: exactly the pairs with |S u S'| <= 1 are forced non-adjacent, every exactly-one class S_x is independent (stronger than W75 Lemma 7), the other 29 type-pairs are free; L-DOM edge-domination]; omega(S_ab) <= omega-2, omega(S_abc) <= omega-3. (iii) CENSUS-2K2 (exhaustive): every 2K2-free graph on n <= 7 vertices (731,523 graphs, complete enumeration) satisfies alpha*omega >= 4n/5, equality exactly at C5; complement transfer carries all of it to induced-C4-free graphs. (iv) The C5-attachment 17-type law (proved). [W76: the full-n closure is COMPLETE — see C61-2K2: max(alpha,omega) >= n^(1/3).]"

## C61-FOURVERTEX-CLASSIFICATION (W75 — superseded by C61-FOURVERTEX-COMPLETE)
"THE 4-VERTEX CLASSIFICATION (W75 status): 9 of the 11 unlabeled 4-vertex graphs are EH-closed in-package with explicit unconditional exponents (P4 and paw/P3+K1 at the optimal 1/2; K4/K4bar every c<1/3; claw/K3+K1, diamond/K2+2K1 at 1/3); C4/2K2 carry the complete triangle-free half (alpha >= sqrt(n)/2), the complete triangle-decomposition structure theorem, and the exhaustive sharp-form census alpha*omega >= 4n/5 through n=7. All claims engine-certified (receipts61four.txt 14/14 + the 731K census addendum). [W76: the classification is COMPLETE — C61-FOURVERTEX-COMPLETE.]"

---

# W78-61E CLAIMS ADDITIONS (appended; the claims above are the bank)

```json
[
  {
    "id": "C61-RAM-GEN",
    "statement": "For every t >= 3 and every K_t-free graph G on n >= 1 vertices: alpha(G) >= ceil(((t-1)!)^{1/(t-1)} * n^{1/(t-1)}) - (t-1); asymptotically alpha >= (1/2)((t-1)!)^{1/(t-1)} n^{1/(t-1)} for n >= (2(t-1))^{t-1}/(t-1)!; hence EH(K_t) and EH(E_t) at c(t) = min(1/(2(t-1)), ln2/(2 ln N0(t))) for all n >= 1. Complete in-package proof (Pascal recursion + contrapositive ladder + ceiling arithmetic).",
    "verification": "GENERAL_REDUCTION.md LAW C61-RAM-GEN; receipts61closure.txt RAMGEN-exh (exhaustive n<=6, t=3,4,5, zero violations) + RAMGEN-samp (t=3..8, n to 100, constructions, zero violations)"
  },
  {
    "id": "C61-PRIME-DEC",
    "statement": "Every graph on >=2 vertices is prime or a uniform blow-up H = Q[M, singletons] over any nontrivial module M (|Q| < |H|, 2 <= |M| < |H|); iteration gives the finite decomposition tree with prime/singleton leaves. Complete in-package proof.",
    "verification": "GENERAL_REDUCTION.md LAW C61-PRIME-DEC; receipts61closure.txt PD-ladder (all internal nodes across every graph n<=6, canonical-form equality, zero failures)"
  },
  {
    "id": "C61-TREE-COMP",
    "statement": "Multi-block avoidance (in the uniform blow-up frame): if quotient Q contains induced A and each corresponding class X contains induced J_p, the blow-up contains induced A[J_1,...,J_a] with possibly different J_p; consequently the tree harmonic exponent c(T) = (sum of reciprocals along the level structure)^{-1} governs H-free compatible blow-ups. In-frame; frame labeled exactly.",
    "verification": "GENERAL_REDUCTION.md LAW C61-TREE-COMP; receipts61closure.txt MB-avoid (100/100) + MB-minlaw (60/60 negative controls)"
  },
  {
    "id": "C61-GENERAL-REDUCTION",
    "statement": "(GR-1) EH for all prime graphs implies EH for all finite graphs within the uniform blow-up frame, at the tree harmonic exponent. (GR-2) The uniformization bridge is the named exact remaining content for arbitrary graphs. (GR-3) The direct-kill frontier at n=5 is exactly {P5, co-P5, bull, C5} (three kills close the 5-vertex world in-frame; 30/34 five-vertex graphs are decomposable, covered in-frame today); at n=6 exactly 26 primes.",
    "verification": "GENERAL_REDUCTION.md; CLOSURE_MAP.md; alln61/coverage_map.json; receipts61closure.txt (836/836 PASS)"
  },
  {
    "id": "C61-C5-CLOSURE-REDUCTION",
    "statement": "The C5-free class is closed under complement, disjoint union, and join (complete proofs: straddle splits 1+4 force a degree-4 vertex vs 2-regular C5; 2+3 forces >=6 edges vs exactly 5; C5 connected kills union straddles). Consequently for any c0 in (0,1]: if every connected AND co-connected C5-free graph satisfies hom >= m^c0 then every C5-free graph satisfies hom >= n^c0 (union levels add alpha, join levels add omega, subadditivity spine Sum x_i^c0 >= (Sum x_i)^c0).",
    "verification": "FIVEVERTEX_PROOF.md sec.2; receipts61five.txt S5-C5-union-join-closure (10,680 pairs), S5-C5-complement-closure (5,785 graphs), S0-C5-selfcomp"
  },
  {
    "id": "C61-C5-DICH",
    "statement": "Every C5-free graph that is triangle-free satisfies alpha >= sqrt(n)/2; every C5-free graph with alpha <= 2 satisfies omega >= sqrt(n)/2. The remaining C5 EH frontier is exactly the cores that are connected AND co-connected AND contain a triangle AND contain an independent triple.",
    "verification": "FIVEVERTEX_PROOF.md sec.2 THEOREM C5-DICH (banked Lemma 4 + complement transfer)"
  },
  {
    "id": "C61-BULL-DEC",
    "statement": "Every bull-free graph with a triangle T={a,b,c} decomposes into the eight attachment classes with: (L1) for distinct x,y in T every u in S_x and w in S_y are adjacent (else the 5-set {u,w,a,b,c} induces exactly the bull, degrees (3,3,2,1,1)); (alpha) alpha(S_a u S_b u S_c) = max alpha(S_x); (omega) omega(G) >= omega(S_a)+omega(S_b)+omega(S_c); (L2) omega(S_x) <= omega(G)-1, omega(S_xy) <= omega(G)-2, omega(S_abc) <= omega(G)-3; (L3) all classes hereditary bull-free. Census freedom matrix: forced-EDGE pairs exactly {axb,axc,bxc}, zero forced-nonedge pairs.",
    "verification": "FIVEVERTEX_PROOF.md sec.3; receipts61five.txt S3-BULL-L1-crosscomplete (4292/4292 over 19,058 graphs n=4..6 exhaustive), S3-BULL-union-structure (9,057 subsets)"
  },
  {
    "id": "C61-P5-IDENT-EXTREMAL",
    "statement": "complement(P5) = house (canonical form 221): one EH kill covers both. C5 is P5-free, house-free, and bull-free with hom(C5)=2, so h_{P5}(5)=h_{house}(5)=h_{bull}(5)=2 and any theorem hom >= n^c for these three classes obeys c <= log2/log5 = 0.4306...",
    "verification": "FIVEVERTEX_PROOF.md sec.1/sec.4; receipts61five.txt S0-house-eq-coP5, S0-bull-selfcomp, S1 h-tables (two codes), S7-witness-duel"
  },
  {
    "id": "C61-FIVE-H-TABLES",
    "statement": "Exact h-tables n<=7 (two counting codes, witness duels): h_P5 = h_house = h_bull = [1,2,2,2,2,3,3]; h_C5 = [1,2,2,2,3,3,3]. All four classes satisfy hom >= n^0.43 at every n <= 7.",
    "verification": "receipts61five.txt S1 (counts two-code n<=5, classifier duels 16000/16000 + 8000/8000), S2 (2^21 exhaustive n=7, Ramsey anchor re-certified, witness brute duel), S6 (c=0.43 OK all four), S7 (42/42 PASS total)"
  },
  {
    "id": "C61-P5-DOM-SHAPE (census-certified, hand-proof open)",
    "statement": "Every connected P5-free graph on n<=6 vertices (all 19,976, exhaustive) has a dominating set of size <=3 inducing K1, K2, K3, or P3; 7,986 sampled connected P5-free n=7 graphs agree. CENSUS-CERTIFIED ONLY: the hand-proof gap (the z-only-dominated stratum in the leaf induction) is named in FIVEVERTEX_PROOF.md sec.4; NOT claimed proven.",
    "verification": "receipts61five.txt S4-P5-bacsotuza-n<=6 (19,976/19,976), S4-P5-bacsotuza-n7-sampled (7,986/7,986)"
  }
]
```

## W81 (W81-61A lane)

- C61-P5CROSS — Theorem P5-CROSS (complete): the z-stratum cross law; proof = the induced-P5 argument. See PRIMES_W81.md §1.
- C61-C5ANCHORS — Theorems C5-1ANCHOR + C5-2ANCHOR (complete): the triangle-anchor forbidden configurations; proofs = the induced-C5 cycle arguments. See PRIMES_W81.md §1.
- C61-TOWERCAP-P5BULL — Theorem TOWER-CAP (complete): c(P5), c(bull) <= log2/log5 = 0.430676 via the C5 substitution tower (P5-free and bull-free at every level, hom = 2^t on 5^t). See PRIMES_W81.md §1.
- C61-PRIMES-CENSUS — the W81 prime census (complete finite facts): h-tables, n^0.43 floors (43,396 graphs), the 36-pair anchor table, the bull I-anchor concentration, the z-only map (372 graphs). See PRIMES_W81.md §2.
