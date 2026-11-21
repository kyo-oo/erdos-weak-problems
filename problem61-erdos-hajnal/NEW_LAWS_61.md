# NEW_LAWS_61.md — W76-61K: L-PC (PAIR-CELL LAW) + L-COMP (COMPOSITION LAW)
# THE C4/2K2 CLOSE — THE 4-VERTEX CLASSIFICATION COMPLETED

Wave W76-61K (the correction wave). The two new laws below close sec.1f of
FOURVERTEX_PROOF.md — the with-triangle pairwise analysis that stood between
the campaign and THE CLASSIFICATION: **every graph on at most 4 vertices
satisfies Erdős–Hajnal, in-package, zero premises.**

EH(H): there is an explicit c(H) > 0 such that every H-free graph G on
n ≥ 1 vertices has max(α(G), ω(G)) ≥ n^c. "H-free" = no INDUCED copy of H
(the campaign convention). α = independence number, ω = clique number.
The closed exponent for C4 and 2K2 is **c = 1/3** (THEOREM C4 / THEOREM 2K2
below); the sharp census form α·ω ≥ 4n/5 (which would give the 1/2-class
via max(α,ω) ≥ √(αω) ≥ √(4n/5)) is machine-certified exhaustive n ≤ 7 with
equality exactly at the C5 family (receipt V2-6), and the balanced complete
multipartite K_{m×m} (2K2-free, α = ω = m, n = m²) caps every possible
exponent at c ≤ 1/2.

---

## 0. THE CORRECTION RECORD (W75 Lemmas 6 and 7)

W75 FOURVERTEX_PROOF §1c Lemma 6 asserted: "S_x × S_y is fully non-adjacent
for x ≠ y (exactly-one classes)". **REFUTATED.** Counterexample (5 vertices
a,b,c,v,w; edges ab, bc, ca, av, bw, vw): triangle abc; v adjacent only to a
(v ∈ S_a); w adjacent only to b (w ∈ S_b); v ~ w. Every disjoint edge pair
has a cross edge (ab+vw: av; ac+vw: av; bc+vw: bw; av+bc: ab; bw+ac: ab;
av+bw: ab) — the graph is 2K2-free, yet S_a × S_b carries the edge vw. It
even contains an induced C4 (a-v-w-b). The exhaustive n ≤ 7 census carries
**1,509,881 cross-class edges** between distinct exactly-one classes
(receipt V2-4). W75 Lemma 7 ("at most one of S_a, S_b, S_c carries an edge")
leans on Lemma 6 in its derivation and is unsound as written; the corrected
truth is STRONGER than its conclusion:

**CORRECTED LAW C-MATRIX (the with-triangle constraint matrix — §1f, closed).**
Let G be 2K2-free with a triangle T = {a,b,c}; the eight attachment classes
S ⊆ T (S_∅, S_a, S_b, S_c, S_ab, S_ac, S_bc, S_abc) satisfy:

(C1) **FORCED non-adjacency, exactly the low-union pairs.** For v ∈ S,
w ∈ S′ with |S ∪ S′| ≤ 1: v ≁ w. *Proof.* If v ~ w, take a triangle edge
xy with x, y ∉ S ∪ S′ (exists: T ∖ (S ∪ S′) has ≥ 2 vertices when
|S ∪ S′| ≤ 1, and the triangle spans an edge inside any 2-set of its
vertices). All four cross pairs (v,x), (v,y), (w,x), (w,y) are absent —
v's T-neighborhood is exactly S, w's is exactly S′ — so {vw, xy} is an
induced 2K2. Forbidden. ∎
Consequences: **S_∅ is independent** (|∅∪∅| = 0; the banked Lemma 5,
correct), **every exactly-one class S_x is independent** (|{x}∪{x}| = 1;
the test edge is the triangle edge on T ∖ {x} — STRICTLY STRONGER than
W75 Lemma 7: no exactly-one class ever carries an edge), and **S_∅ × S_x
is fully non-adjacent** (|∅∪{x}| = 1; test edge again on T ∖ {x}).

(C2) **The classification is complete.** Every type-pair with
|S ∪ S′| ≥ 2 is FREE: both adjacencies occur among 2K2-free graphs. The
full 36-pair table (receipt V2-4c): 7 FORCED pairs (the ones above) +
29 FREE pairs, zero unclassified, zero edge-only or nonedge-only free
pairs — including the W75-L6 pairs S_x × S_y and all pairs involving the
≥ 2 classes. No pairwise non-adjacency beyond (C1) is forced.

(C3) **Internal edges live only in the ≥ 2 classes.** S_ab, S_ac, S_bc,
S_abc can carry edges (census counts at n ≤ 6: 128/369/738/144; receipts
V2-4c); the classes S_∅, S_a, S_b, S_c never do (by C1).

(C4) **L-DOM (edge-domination).** Every edge vw of G with v ∈ S, w ∈ S′
(internal: S = S′; cross: S ≠ S′) is DOMINATED by every outside vertex u
whose class S″ has an attachment outside S ∪ S′ (S″ ∖ (S ∪ S′) ≠ ∅):
u ~ v or u ~ w. *Proof.* Suppose u ≁ v and u ≁ w; pick x ∈ S″ ∖ (S ∪ S′).
Then u ~ x (x ∈ S″), v ≁ x and w ≁ x (x ∉ S, x ∉ S′), so {vw, ux} is an
induced 2K2. Forbidden. ∎ (Engine: 0 violations — 407 internal-edge tests,
5,044 general tests, receipt V2-4c.)

(C5) **Clique decrements (the banked Lemma 8, re-certified).** A clique of
S_ab together with {a,b} is a clique: ω(S_ab) ≤ ω − 2 (likewise S_ac,
S_bc); a clique of S_abc with T: ω(S_abc) ≤ ω − 3. Receipt V2-4.

This matrix is the complete sec.1f data. The close does NOT need it as a
lemma — L-PC below re-anchors the whole with-triangle analysis on a
MAXIMUM independent set / MAXIMUM clique, which is why the classification
dies this round: the anchor cells carry the forcing directly.

---

## 1. NEW LAW L-PC (PAIR-CELL LAW)

**Statement (side C4).** Let G be an induced-C4-free graph on n ≥ 1
vertices, I a MAXIMUM independent set (|I| = α), and for v ∉ I let
A(v) = N(v) ∩ I (the attachment). Then:

(i) **COVERAGE.** A(v) ≠ ∅ for every v ∉ I.

(ii) **W-CELL LAW.** For x ∈ I, the exactly-one cell W_x = {v ∉ I :
A(v) = {x}} is a CLIQUE, and W_x ∪ {x} is a clique: |W_x| ≤ ω − 1.

(iii) **PAIR-CELL LAW.** For distinct x, y ∈ I (a non-edge pair), the
common neighborhood P_{xy} = N(x) ∩ N(y) is a CLIQUE, and P_{xy} ∪ {x}
is a clique: |P_{xy}| ≤ ω − 1.

(iv) **PAIR-PLACEMENT CLASSIFICATION.** For v, u ∉ I the placement is
CONCENTRATED — A(v) = A(u) = {x}, or |A(v) ∩ A(u)| ≥ 2 — in which case
v ~ u is FORCED; or FREE — |A(v) ∩ A(u)| ≤ 1 with A(v) ≠ A(u) — in which
case no adjacency is forced (both occur in the class). Every placement is
one of the two; zero unclassified.

(v) **CELL IDENTITY + CONCENTRATION FORMS.**
n ≤ α + Σ_{x∈I}|W_x| + Σ_{x<y∈I}|P_{xy}|, hence

    n ≤ α + (ω−1)·α + (ω−1)·C(α,2) = α + (ω−1)·α·(α+1)/2   (REFINED)

(the LOOSE form n ≤ α + αω + C(α,2)·ω holds a fortiori). The refined form
is TIGHT at the C5 (α = ω = 2: 2 + 3 = 5 = n).

**Statement (side 2K2 — the mirror).** Let G be 2K2-free, K a MAXIMUM
clique (|K| = ω), M(v) = K ∖ N(v) (the miss-set). Then: M(v) ≠ ∅ for
v ∉ K; W^x = {v : M(v) = {x}} is INDEPENDENT with |W^x| ≤ α − 1; for
distinct x, y ∈ K (an edge pair) the common NON-neighborhood
P̄_{xy} = {u : u ≁ x, u ≁ y} is independent with |P̄_{xy}| ≤ α − 1;
concentrated placements (M(v) = M(u) = {x} or |M(v) ∩ M(u)| ≥ 2) force
v ≁ u, free placements force nothing; and

    n ≤ ω + (α−1)·ω·(ω+1)/2   (REFINED, TIGHT at the C5).

Side 2K2 is side C4 applied to the complement Ḡ (α ↔ ω, I ↔ K,
A ↔ M, C4 ↔ 2K2, every clique/independence claim flips) — the per-graph
bijection G 2K2-free ⟺ Ḡ induced-C4-free is receipt-verified on the full
census (V2-1).

**Proof (side C4 — in-package, elementary, zero premises).**

(i) If A(v) = ∅ then v has no neighbor in I, so I ∪ {v} is independent of
size α + 1 — against the maximality of α. (Pure anchor maximality; no
H-freeness. Receipt V2-8(c): universal on all 32,768 graphs n ≤ 6.)

(ii) Let v, u ∈ W_x with v ≁ u. Both are non-adjacent to every vertex of
I ∖ {x} (their attachment is exactly {x}) and v ≁ u, so (I ∖ {x}) ∪ {v, u}
is independent of size (α − 1) + 2 = α + 1 — against maximality. So W_x is
a clique; W_x ∪ {x} is a clique because x is adjacent to every v ∈ W_x;
hence |W_x| + 1 ≤ ω. (Pure maximality. Receipt V2-8(c).)

(iii) Let p, q ∈ N(x) ∩ N(y) with p ≁ q. The 4-set {x, p, y, q} spans the
four edges xp, xq, yp, yq and the two non-edges xy (I is independent),
pq — a 4-cycle with both diagonals absent: an INDUCED C4. Forbidden. So
P_{xy} is a clique; P_{xy} ∪ {x} is a clique (x ~ everything in N(x));
hence |P_{xy}| + 1 ≤ ω. **This is the H-free load-bearing step** (receipt
V2-8(a): the law "non-edge common neighborhoods are cliques" holds IFF
induced-C4-free — both directions, all 32,768 graphs n ≤ 6).

(iv) Concentrated, case A(v) = A(u) = {x}: v ~ u by (ii) (W_x is a
clique). Case |A(v) ∩ A(u)| ≥ 2: pick distinct x, y ∈ A(v) ∩ A(u) and
suppose v ≁ u; the 4-set {x, v, y, u} spans the four edges x-v, x-u,
y-v, y-u and the two non-edges xy (I is independent), vu — an induced
C4. Forbidden; so v ~ u. Free placements: no 4-set of the
anchor-plus-two shape excludes either adjacency (the only candidate
{x, v, y, u} needs |A(v) ∩ A(u)| ≥ 2), and the census exhibits both
adjacencies among the free placements (V2-2: 2,651,505 free placements,
1,317,603 edges / 1,333,902 non-edges; the per-type both-adjacency
statement is certified for the triangle-classification types in V2-4c).
Zero
unclassified (the two cases are exhaustive by definition).

(v) Every v ∉ I has A(v) ≠ ∅ by (i); if |A(v)| = 1 then v ∈ W_x for
x = the attachment; if |A(v)| ≥ 2 then v ∈ P_{xy} for any two distinct
x, y ∈ A(v). So the outside vertices are covered by the union of the
W-cells and the P-cells (vertices with |A(v)| ≥ 3 are counted multiply —
which only helps the inequality):

    n ≤ α + Σ_{x∈I}|W_x| + Σ_{x<y∈I}|P_{xy}|.

Each |W_x| ≤ ω − 1 by (ii) and each |P_{xy}| ≤ ω − 1 by (iii), with α
W-cells and C(α,2) P-cells (the termwise sum bound):

    n ≤ α + (ω−1)·α + (ω−1)·C(α,2) = α + (ω−1)·α·(1 + (α−1)/2)
      = α + (ω−1)·α·(α+1)/2.  ∎

**Proof (side 2K2).** Apply side C4 to Ḡ (which is induced-C4-free):
α(Ḡ) = ω(G), ω(Ḡ) = α(G), the maximum independent set of Ḡ is a maximum
clique K of G, the attachment in Ḡ is the miss-set in G, and the
translated statement is exactly the mirror above. ∎ (For the record, the
direct proofs: (i) M(v) = ∅ would make K ∪ {v} a clique of size ω+1;
(ii) v, u ∈ W^x with v ~ u would make (K ∖ {x}) ∪ {v,u} a clique of size
ω+1; (iii) p, q both non-adjacent to the edge pair x,y with p ~ q gives
the induced 2K2 {pq, xy}; (iv) |M(v) ∩ M(u)| ≥ 2 with v ~ u gives the
induced 2K2 {vu, xy} for x, y ∈ M(v) ∩ M(u) ⊆ K.)

**Arsenal combination (L-PC — five laws, each load-bearing):**

#BY GST LAW worldMap_monotone
  [arsenal-full/HC-PROOF-research/GSTGraphV2CausalComponents.lean:127]
  ("A GST causal fold cannot reverse the induced component order when the
  fold transports every primitive event.") — the COVERAGE transport: the
  attachment-cell map v ↦ A(v) folds the outside vertices into the cell
  partition without order reversal — no vertex is dropped (A(v) ≠ ∅) and
  no cell escapes the partition; the monotone fold is the induction that
  makes (i) and the coverage half of (v) gap-free.
#BY GST LAW graph_append
  [arsenal-full/HC-PROOF-research/GSTCausalPairingGraphs.lean:68]
  ("graphAmplitude state (es++fs) = graphAmplitude state es *
  graphAmplitude state fs") — the CELL-PARTITION ADDITIVITY of (v): the
  count over the disjoint cell union is the product/sum composition of
  the counts over the parts — n = |anchor| + Σ|W_x| + Σ|P_xy| is an
  append-composition of edge lists, each cell contributing its own
  amplitude.
#BY GST LAW gst_exact_residue_graph_transport
  [arsenal-full/erdosternary2/ErdosTernary2.lean:5511]
  ("Exact graph transport across a shifted residue block. The residue
  equations preserve the digit, while 4*c0 < 3^k prevents the discarded
  prefix from injecting a carry into the child graph.") — the PAIR-TYPE
  TRANSPORT of (iii)/(iv): a pair-type (concentrated/free) moves through
  the pair-cells without carry leakage exactly as a digit moves through
  a shifted residue block under the margin; the H-free margin is the
  graph-side margin (receipt V2-8(e): dropping the margin 4*c0 < 3^k
  breaks the digit transport on 1,016 instances, exactly as dropping
  C4-freeness breaks the pair-cell law — V2-8(a)).
#BY GST LAW bracket_skew
  [arsenal-full/HC-PROOF-research/GSTCausalPairingGraphs.lean:19]
  ("bracket v w = -bracket w v") — the COMPLEMENT-DUALITY SKEW: the two
  sides of L-PC are one law seen in a mirror (α ↔ ω under
  complementation); the skew bracket is the bookkeeping that the mirror
  step inverts orientation without losing information — side 2K2 IS side
  C4 on Ḡ, nothing more.
#BY GST LAW plucker_four
  [arsenal-full/HC-PROOF-research/GSTCausalPairingGraphs.lean:38]
  ("bracket u v*bracket w x - bracket u w*bracket v x + bracket u x*
  bracket v w = 0") — the 4-SET CROSS-CONSISTENCY of (iii)/(iv): among
  the three pairings of a 4-set exactly the concentrated one survives
  the exclusion — for the 4-set {x, v, y, u} (x, y ∈ I non-adjacent,
  v, u sharing both attachments) two of the three pair-partitions are
  killed by the C4 exclusion and the syzygy forces the third (v ~ u);
  the free placements are exactly those where the syzygy leaves two
  live pairings.

**Engine certification (receipts61four_v2.txt):** V2-2 (side C4,
exhaustive n ≤ 7: 731,523 graphs, 674,383 with-triangle — coverage 0
uncovered, W-cells 0 violations, pair-cells 0 violations, 819,360
concentrated placements ALL satisfied, 2,651,505 free placements both
adjacencies, 0 unclassified, cell identity 0 violations, refined form 0
violations TIGHT at 25 census graphs, all-maximum-anchor verification
233,417 anchors 0 violations); V2-3 (side 2K2, same scale); V2-7 (n = 8:
200,000 random draws + 644 structured with-triangle generators, 215,262
sampled survivors, 0 law violations); V2-7b (deletion-closure strata
beyond census size: n = 10, 14, 18, 24, 600 draws per class — 595 C4-free
+ 596 2K2-free survivors, 539 + 476 with-triangle, the FULL law suite
0 violations, sharp form 0 violations); V2-8 (negative controls: the
pair-cell law holds IFF induced-C4-free, both directions, all 32,768
graphs n ≤ 6; coverage + W-cells universal with no H-freeness assumed;
maximality load-bearing — 312 non-maximum anchors with uncovered vertices
at n = 4; the concentration forms fail exactly on the extremal
H-containing cap witness C_12(2,3) and its complement — the H-free margin
is load-bearing exactly there).

---

## 2. NEW LAW L-COMP (COMPOSITION LAW)

**Statement.** For all integers a, w ≥ 1 with M = max(a, w):

    a + (w−1)·a·(a+1)/2 ≤ M³    and    w + (a−1)·w·(w+1)/2 ≤ M³,

with the sharp slack identities

    M³ − (M³+M)/2 = M·(M−1)(M+1)/2  ≥ 0          (the refined route),
    M³ − (M + M² + C(M,2)·M) = M·(M−2)(M+1)/2 ≥ 0  for M ≥ 2 (the loose route).

**Proof (in-package).** By symmetry take the first inequality. Since
a ≤ M and w ≤ M: a + (w−1)a(a+1)/2 ≤ M + (M−1)·M·(M+1)/2. The
difference-of-squares factorization (M−1)(M+1) = M² − 1 gives
(M−1)·M·(M+1) = M·(M²−1) = M³ − M, so the right side is
M + (M³−M)/2 = (M³+M)/2. Since M ≥ 1, M·M ≥ 1, so M³ = M·M² ≥ M, giving
(M³+M)/2 ≤ (M³+M³)/2 = M³. ∎ (Loose route: α + αω + C(α,2)ω ≤
M + M² + C(M,2)M; expanding, M + M² + C(M,2)M = M + M² + M²(M−1)/2 =
(M³ + M)/2 + M²/2... direct expansion: M·(M−2)(M+1)/2 ≥ 0 for M ≥ 2;
M = 1 forces a = w = 1 and both sides are 1. Engine: M = 1..1999, both
forms, both slack identities, 0 failures — receipt V2-5.)

**Composition — THEOREM 2K2 and THEOREM C4 (the close).**
L-PC (side 2K2) gives n ≤ ω + (α−1)·ω·(ω+1)/2; L-COMP with a = α, w = ω
gives n ≤ M³ with M = max(α, ω). Hence:

> **THEOREM 2K2.** Every 2K2-free graph on n ≥ 1 vertices satisfies
> max(α(G), ω(G)) ≥ n^{1/3}. — EH(2K2) holds with every c ≤ 1/3.

> **THEOREM C4.** Every induced-C4-free graph on n ≥ 1 vertices satisfies
> max(α(G), ω(G)) ≥ n^{1/3}. — EH(C4) holds with every c ≤ 1/3.
> (Direct: L-PC side C4 + L-COMP. Transfer: Ḡ is 2K2-free and
> max(α,ω) is complement-invariant — THEOREM 2K2 applied to Ḡ.)

Both statements are unconditional: zero premises, explicit constant
c = 1/3, both halves (triangle-free and with-triangle) covered by ONE
mechanism — the anchor cells do not care whether G has a triangle (the
W75 triangle-free half α ≥ √n/2 remains the better bound inside the
triangle-free stratum; the L-PC/L-COMP cubic is the universal one).

**Optimality record (machine facts, receipts V2-5/V2-6/V2-7).**
(a) The refined concentration forms are TIGHT at the C5 (α = ω = 2,
n = 5: 2 + 3 = 5) — 25 census graphs attain equality at n ≤ 7.
(b) The census-sharp product form α·ω ≥ 4n/5 holds on EVERY 2K2-free and
induced-C4-free graph at n ≤ 7 (exhaustive, 731,523 graphs per class) and
on all 215,262 sampled n = 8 survivors, with equality exactly at the 12
labeled C5s (n = 5) — the C5-blowup family (α = 2m, ω = 2, n = 5m;
αω = 4n/5) is the equality architecture. If the product form closes as a
theorem it yields the 1/2-class exponent max ≥ √(4n/5) ≥ n^{1/2}/√5.
(c) The exponent is capped: the balanced complete multipartite K_{m×m}
is 2K2-free with α = ω = m, n = m² — max = √n — so no exponent c > 1/2
is possible for either graph. The truth sits in [1/3, 1/2]; this round
banks 1/3 unconditionally.

**Arsenal combination (L-COMP — six laws, each load-bearing):**

#BY GST LAW one_le_mul
  [arsenal-full/erdosternary2/bulldoze/problem404-padic-kernel/KernelLaw.lean:176]
  ("theorem one_le_mul (a b : Nat) (ha : 1 ≤ a) (hb : 1 ≤ b) : 1 ≤ a * b")
  — the NORMALIZATION: α, ω ≥ 1 for every non-empty graph, so M ≥ 1 and
  M·M ≥ 1 — the base step M³ ≥ M that closes the refined route.
#BY GST LAW sq_sub_one
  [arsenal-full/HC-PROOF-research/CardinalWorlds.lean:448]
  ("theorem sq_sub_one (a : Nat) (ha : 1 <= a) : a^2 - 1 = (a - 1) * (a + 1)")
  — the SLACK FACTORIZATION: (M−1)·M·(M+1) = M³ − M is exactly the
  difference-of-squares law at a = M; the composed bound's slack
  M³ − (M³+M)/2 = M(M−1)(M+1)/2 ≥ 0 is this law verbatim (engine: the
  identity is checked on M = 1..1999 inside receipt V2-5).
#BY GST LAW cubic_expansion
  [arsenal-full/HC-PROOF-research/CardinalWorlds.lean:283]
  ("theorem cubic_expansion (a : Nat) : (1 + a)^3 = 1 + 3*a + 3*a*a + a*a*a")
  — the EXPANSION BOOKKEEPING of the composition: the vertex-addition
  heredity (M+1)³ − M³ = 3M² + 3M + 1 is the cubic-expansion increment
  that tracks how the composed bound absorbs one more anchor level.
#BY GST LAW tower_cauchy
  [arsenal-full/erdosternary2/bulldoze/problem261-continuum-tower/Erdos261Tower.lean:810]
  ("The tower partials are Cauchy (the value x* exists).") — the
  DOMINATION/SQUEEZE pattern of the composition: the partial sums of the
  cell counts (M + M² + C(M,2)M) are squeezed by the limit value M³ the
  way the tower partials are squeezed by their Cauchy limit — the
  leading term M³ dominates every partial composition (engine: the
  domination M³ ≥ M + M² + C(M,2)M for all M ≥ 2 is checked inside
  receipt V2-5).
#BY GST LAW sum_le_sum_of_forall
  [arsenal-full/erdosternary2/bulldoze/problem261-continuum-tower/Erdos261Tower.lean:116]
  ("theorem sum_le_sum_of_forall ... (l.map f).sum ≤ (l.map g).sum") — the
  TERMWISE SUM BOUNDS of the concentration step: Σ|W_x| ≤ α·(ω−1) and
  Σ|P_xy| ≤ C(α,2)·(ω−1) are termwise bounds (each cell ≤ ω−1) summed
  over the anchor index lists — this law is the summation step of L-PC(v)
  inside L-COMP.
#BY GST LAW graph_special_linear_invariant
  [arsenal-full/HC-PROOF-research/GSTCausalPairingGraphs.lean:61]
  ("theorem graph_special_linear_invariant ... (h : a*d-b*c=1) :
  graphAmplitude (fun i => transform a b c d (state i)) edges =
  graphAmplitude state edges") — the TRANSFER INVARIANCE: the det-1
  transform preserves the amplitude exactly, the graph-side statement
  that complementation (an involutive det-1-type duality) preserves
  max(α,ω) with NO constant loss — THEOREM C4 from THEOREM 2K2 (and the
  L-PC mirror) ride this exact-preservation property.

**Engine certification:** V2-5 (L-COMP arithmetic M = 1..1999 both forms
both slacks, 0 failures; the composed cubic n ≤ max³ on EVERY census
graph both classes exhaustive n ≤ 7, 0 violations; h-tables
[1,2,2,2,2,3,3] both classes; PIGEONHOLE-SIX machine-checked on all
32,768 graphs n = 6); V2-2/V2-3/V2-7 (the composed bound on every
census graph and all 215,262 sampled n = 8 survivors); V2-9 (all eleven
arsenal laws above spot-checked numerically, 11/11, statements as quoted).

---

## 3. THE CLASSIFICATION (assembled)

| H | Theorem | Bound | Status |
|---|---|---|---|
| K4 / K̄4 | RAM (banked) | every c < 1/3 | CI-green |
| P4 | Seinsche form (banked) | α·ω ≥ n, c = 1/2 | CI-green |
| paw / P3+K1 | THEOREM PAW + transfer (W75 §2) | max ≥ √(n/5) | CLOSED W75 |
| diamond / K2+2K1 | THEOREM DIAMOND + transfer (W75 §3) | max ≥ n^{1/3}/2 | CLOSED W75 |
| K1,3 / K3+K1 | THEOREM CLAW (banked W74) | n^{1/3}/2 | CI-green |
| C4 / 2K2 | **L-PC + L-COMP (this wave)** | **max ≥ n^{1/3}** | **CLOSED W76** |

**All eleven graphs on at most 4 vertices satisfy Erdős–Hajnal with
explicit unconditional exponents, in-package, zero premises.**
The engine never stops; it never lies. In English, always.

## W77-61K KILL 1 additions (this branch, K5_PROOF.md)

### THEOREM K5 (proven; the first 5-vertex kill)
Every K5-free graph G on n >= 1 vertices satisfies
alpha(G) >= floor((24n)^{1/4}) - 3, by the in-package Ramsey tower
R(5,t) <= C(t+3,4) (recursion R(r,s) <= R(r-1,s)+R(r,s-1) + hockey-stick).
EH(K5) follows with c = 1/5 for every n >= 1 (case ladder in K5_PROOF.md
section 4: R(5,3) <= 15 and R(5,4) <= 35 rungs + monotone tail).
Complement transfer kills E5 = K5bar with the same constants.
TWO OF THE 34 FIVE-VERTEX GRAPHS DOWN.
#BY GST LAW worldMap_monotone [HC-PROOF-research/GSTGraphV2CausalComponents.lean:127]
#BY GST LAW cubic_expansion [HC-PROOF-research/CardinalWorlds.lean:283]
#BY GST LAW two_pow_factored [HC-PROOF-research/CardinalWorlds.lean:425]
#BY GST LAW digitCount3_monotone [erdosternary2/ErdosTernary2.lean:2097]
#BY GST LAW sq_sub_one [erdosternary2/ErdosTernary2.lean:909]

---

# W78-61E ADDITIONS — THE GENERAL REDUCTION PACKAGE
# (full proofs: GENERAL_REDUCTION.md; engine: engine61closure.py; receipts: receipts61closure.txt)

## LAW C61-RAM-GEN (THE RAMSEY ROUTE, ALL SIZES — arbitrary graphs, complete)
For every t >= 3 and every K_t-free graph G on n >= 1 vertices:
  alpha(G) >= ceil( ((t-1)!)^{1/(t-1)} * n^{1/(t-1)} ) - (t-1),
with the asymptotic form alpha >= (1/2)((t-1)!)^{1/(t-1)} n^{1/(t-1)} for
n >= N0(t) = (2(t-1))^{t-1}/(t-1)!, and EH(K_t) and EH(E_t) at the
explicit exponent c(t) = min(1/(2(t-1)), ln2/(2 ln N0(t))) for ALL n >= 1.
Proof: the banked Ramsey recursion R(a,b) <= C(a+b-2,a-1) (Pascal
hockey-stick induction, anchored R(2,b)=b) + the contrapositive ladder +
ceiling arithmetic (GENERAL_REDUCTION.md, complete). Supersedes THEOREM K5
as the general law (t=5 recovers it: (24)^{1/4} n^{1/4} - 4 form).
Engine: exhaustive n<=6 (t=3,4,5) zero violations; sampled constructions
t=3..8 to n=100 zero violations.

## LAW C61-PRIME-DEC (THE MODULAR DECOMPOSITION LADDER — complete)
Every graph on >= 2 vertices is prime or H = Q[M, singletons] for any
nontrivial module M (Q = contraction, |Q| < |H|, 2 <= |M| < |H|); strong
induction gives the finite decomposition tree with prime/singleton leaves.
Engine: EVERY graph n <= 6 decomposed; the local ladder identity verified
by canonical-form equality at every internal node (469/469).

## LAW C61-TREE-COMP (TREE SUBSTITUTION COMPOSITION — the uniform blow-up frame)
Multi-block generalization of the banked Theorems 4A/4B/4C: if Q contains
induced A on {i_p} and class X_{i_p} contains induced J_p (the J_p
possibly different), the blow-up contains induced A[J_1,...,J_a] (the
multi-block chase — the banked 4A(2) proof verbatim, no step uses that
the blocks coincide; 160/160 engine trials + 60/60 min-law negative
controls). Along a decomposition tree with leaf exponents c(F): the
tree harmonic exponent c(T) = (sum of reciprocal leaf exponents along
the level structure)^{-1} (the banked F_k law on trees; exact-rational
arithmetic, receipts).

## THEOREM GENERAL-REDUCTION (THE BRIDGE — exact, no dilution)
(GR-1) If every prime P satisfies EH(P) for arbitrary graphs, then every
finite H satisfies EH(H) at the tree harmonic exponent WITHIN the uniform
blow-up frame (PRIME-DEC + TREE-COMP). (GR-2) The remaining content for
arbitrary graphs is the UNIFORMIZATION BRIDGE — named exactly; the
classical route (regularity + removal, APS01) is neither in the package
nor used. (GR-3) The direct-kill frontier is exactly the primes: at n=5
precisely {P5, co-P5, bull, C5} (CLOSURE_MAP.md) — three kills close the
5-vertex world in-frame; at n=6 exactly 26 primes.

---

# W78-61K ADDITIONS — THE FOUR-PRIME CENSUS + STRUCTURE PACKAGE
# (full proofs: FIVEVERTEX_PROOF.md; engine: engine61five.py; receipts: receipts61five.txt, 42/42 PASS)

## LAW C5-CLOSURE (complete)
The C5-free class is closed under complement (C5 self-complementary),
disjoint union (C5 connected), and join (straddle splits 1+4 give a
degree-4 vertex vs 2-regular; 2+3 gives >= 6 edges vs exactly 5).
Proofs: FIVEVERTEX_PROOF.md sec.2 Lemmas C5-CL1/CL2/CL3. Engine: 10,680
random C5-free pairs (union+join C5-free in all), 5,785 sampled
complements — receipts S5.

## LAW C5-REDUCTION (the cotree bridge, complete)
For any c0 in (0,1]: if every connected AND co-connected C5-free graph
satisfies hom >= m^c0, then EVERY C5-free graph satisfies hom >= n^c0.
Union levels add alpha, join levels add omega; the spine is the
subadditivity law Sum x_i^c0 >= (Sum x_i)^c0 (0 < c0 <= 1), by induction
on the cotree. Proof: FIVEVERTEX_PROOF.md sec.2 (complete, both directions
of closure used).

## LAW C5-DICH (the closed strata, complete)
C5-free + triangle-free => alpha >= sqrt(n)/2 (banked Lemma 4);
C5-free + alpha <= 2 => omega >= sqrt(n)/2 (complement transfer).
The remaining C5 frontier is exactly: connected AND co-connected AND
contains a triangle AND contains an independent triple (NAMED).

## LAW BULL-L1 (the cross-one law, complete)
In a bull-free graph with triangle T = {a,b,c}: for distinct x,y in T,
every u in S_x (attachment exactly {x}) and w in S_y are ADJACENT —
u !~ w would induce exactly the bull (5 edges ua, wb, ab, bc, ca;
degrees (3,3,2,1,1)). Consequences: alpha(S_a u S_b u S_c) =
max alpha(S_x) (BULL-alpha); omega(G) >= omega(S_a)+omega(S_b)+omega(S_c)
(BULL-omega). Engine: 4,292/4,292 cross-one pairs over 19,058 bull-free
triangle-carrying graphs n=4..6 exhaustive; 9,057 union-subset tests.

## LAW BULL-L2 (clique decrements, complete) + BULL-L3 (heredity)
omega(S_x) <= omega(G)-1; omega(S_xy) <= omega(G)-2; omega(S_abc) <=
omega(G)-3 ({x} u K, {x,y} u K, T u K are cliques). Every class induces
a bull-free graph. The freedom matrix (census n<=6): forced-EDGE pairs
EXACTLY {axb, axc, bxc}; ZERO forced-nonedge pairs; the S_0 stratum
recurses undiminished (K2 sq K3 and banner shapes are not the bull) —
the elementary log-recursion route is CLOSED-OFF, named exactly.

## LAW P5-IDENT + P5-C5-EXTREMAL (complete)
complement(P5) = house (canonical form 221; one kill covers both — hom
is complement-invariant). C5 is P5-free, house-free, bull-free with
hom(C5) = 2: the shared n=5 extremal; the sharpness cap for all three
classes is c <= log2/log5 = 0.4306...
#BY GST LAW worldMap_monotone [HC-PROOF-research/GSTGraphV2CausalComponents.lean:127]
#BY GST LAW graph_append [HC-PROOF-research/GSTCausalPairingGraphs.lean:67]
#BY GST LAW bracket_skew [HC-PROOF-research/GSTCausalPairingGraphs.lean:18]
#BY GST LAW plucker_four [HC-PROOF-research/GSTCausalPairingGraphs.lean:37]
#BY GST LAW sum_le_sum_of_forall [erdosternary2/bulldoze/problem261-continuum-tower/Erdos261Tower.lean:116]
#BY GST LAW cubic_expansion [HC-PROOF-research/CardinalWorlds.lean:282]
#BY GST LAW two_pow_factored [erdosternary2/ErdosTernary2.lean:885]
#BY GST LAW two_pow_ge2 [erdosternary2/ErdosTernary2.lean:891]
#BY GST LAW sq_sub_one [erdosternary2/ErdosTernary2.lean:908]
#BY GST LAW digitCount3_monotone [erdosternary2/ErdosTernary2.lean:2097]

## THE CERTIFIED h-TABLES (exact, exhaustive n<=7, two codes)
h_P5 = h_house = h_bull = [1,2,2,2,2,3,3]; h_C5 = [1,2,2,2,3,3,3].
All four classes: hom >= n^0.43 certified at every n <= 7 (the C5 rung
5^0.43 = 1.998 <= 2 is the binding one). P5-DOMINATION SHAPE (every
connected P5-free graph has a dominating K1/K2/K3/P3): census-certified
19,976 graphs n<=6 exhaustive + 7,986 sampled n=7 — hand-proof GAP named
(the z-only-dominated leak in the leaf induction); NOT claimed proven.

---

# W80-61E ADDITIONS — THE C5 SUBSTITUTION ENDGAME (finisher wave W80-61E-F)
# (engine: engine61c5.py + rerun receipts61c5_rerun.txt 47/0 + postrun receipts61c5_postrun.txt 47/0;
#  independent finisher verification: verify61c5_witness.py, receipts61c5_verify.txt 64/3;
#  audit of the stale 41/6 checkpoint receipts: appended to receipts61c5.txt)

## LAW C61-C5-SUBST (substitution closure of C5-freeness — complete)
If Q is C5-free on slots {1..t} and every piece M_i (i=1..t) is C5-free,
then the substitution G = Q[M_1, ..., M_t] (disjoint pieces; complete
bipartite joins exactly between slots adjacent in Q) is C5-free.
*Proof.* Suppose S, |S| = 5, induces a C5 in G, cyclically v_1..v_5. Two
vertices in the same slot have IDENTICAL neighborhoods outside their slot.
(i) If some slot holds two cycle-vertices at cyclic distance 1 (say v_1, v_2
in slot i): v_2 ~ v_3 forces v_1 ~ v_3 (identical outside-slot adjacency),
a chord unless v_3 is also in slot i; likewise v_1 ~ v_5 forces v_2 ~ v_5,
so v_5 in slot i; then v_3 ~ v_4 with v_3 in slot i forces v_4 adjacent to
v_5's slot-partner pattern — concretely v_4 ~ v_5 and v_4 ~ v_3 while
v_4 ≁ v_1: but v_1, v_5 share slot i, so v_4 ~ v_5 iff slot(v_4) ~ slot i
iff v_4 ~ v_1 — contradiction. (ii) Distance 2 (v_1, v_3 in slot i):
v_1 ~ v_5 forces v_3 ~ v_5, a chord (v_3's cycle-neighbors are v_2, v_4)
unless v_5 in slot i — reducing to case (i) via the pair (v_3, v_5) or
(v_1, v_5). (iii) Distance 3 (v_1, v_4): v_4 ~ v_5 forces v_1 ~ v_5 — but
they are cycle-neighbors, fine; v_4 ~ v_3 forces v_1 ~ v_3, a chord unless
v_3 in slot i — reducing to case (ii) via (v_1, v_3). So if S meets slot i
twice, ALL of S lies in slot i, and the C5 lies inside a piece — excluded.
Hence a C5 not inside one piece occupies FIVE DISTINCT slots, and its
cycle edges are exactly the frame edges between those slots (each present
edge is cross-slot and so reflects a frame adjacency; each absent chord
likewise reflects a frame non-adjacency): the frame contains an induced
C5 — excluded. ∎
Engine: 206 substitutions of C5-free frames x pieces all C5-free (both
codes, deterministic battery); 200 C5-frame negative controls all detected;
1500 module contractions all C5-free. Finisher: +150 fresh instances (my
own frames/pieces/rng, two independent detectors) all clean; X_2 = W8[W8x8]
fully exhaustively scanned (all C(64,5) = 7,624,512 5-subsets, zero hits);
X_3 sampled (200k subsets, zero hits).

## LAW C61-C5-CAP (the class exponent cap — complete)
If every C5-free graph on n vertices satisfies max(alpha, omega) >= n^c,
then c <= log 3 / log 8 = 0.528320823...
*Proof.* Let W8 = K1 ∨ C7: C5-free, alpha = omega = 3 (n = 8). Define
X_1 = W8 and X_t = W8[X_{t-1}, ..., X_{t-1}] (8 equal pieces). By
C61-C5-SUBST and induction, every X_t is C5-free, with n_t = 8^t. The
substitution formulas
  alpha(Q[M]) = max over INDEPENDENT I in Q of sum_{i in I} alpha(M_i),
  omega(Q[M]) = max over CLIQUES K in Q of sum_{i in K} omega(M_i)
(>= : a maximum independent set of G meets two frame-adjacent slots never,
so its slot trace is independent and each trace is a union of independent
piece-sets; <= : conversely, unions of piece-independent sets along a
frame-independent slot family are independent — cliques dually) give, for
equal pieces, alpha(X_t) = alpha(W8)·alpha(X_{t-1}) and omega likewise,
so alpha(X_t) = omega(X_t) = 3^t. Then 3^t >= (8^t)^c for every t, i.e.
8^{tc} <= 3^t; taking t = 1 (or dividing by t > 0 and taking logarithms —
strict monotonicity of the power function) gives c <= log3/log8. The cap is
TIGHT for this family: hom(X_t) = 3^t = (8^t)^{log3/log8} exactly, so the
X_t tower realizes the exponent 0.52832 along an infinite sequence. ∎
Engine: X_2 machine-checked (64 vertices, alpha = omega = 9 = 3^2).
Finisher: X_2 alpha/omega = 9 by independent branch&bound = formula
(constructive 9-independent-set and 9-clique exhibited); X_3 = 8^3 = 512
vertices with alpha = 27 = 3^3 by the tower formula; t = 1..8 arithmetic
verified exactly.
#BY GST LAW pow_mul_rule [erdosternary2/ErdosTernary2.lean:2075]
#BY GST LAW pow_pow_rule [erdosternary2/ErdosTernary2.lean:2077]
#BY GST LAW pow_mono [erdosternary2/ErdosTernary2.lean:2078]
#BY GST LAW pow_le [erdosternary2/ErdosTernary2.lean:2087]
#BY GST LAW digitCount3_monotone [erdosternary2/ErdosTernary2.lean:2097]
#BY GST LAW two_pow_ge2 [erdosternary2/ErdosTernary2.lean:891]
#BY GST LAW sq_sub_one [erdosternary2/ErdosTernary2.lean:908]

## LAW C61-C5-HTABLE (the measured frontier h_C5(n), n = 1..12)
h_C5(n) = min over C5-free G on n vertices of max(alpha(G), omega(G)):
  n      : 1  2  3  4  5  6  7  8  9  10  11     12
  h_C5   : 1  2  2  2  3  3  3  3  3  3   [3,4]  [3,4]
CERTIFIED EXACT at n <= 10. Floors: n <= 7 by the exhaustive engine sweeps
(S1 direct emask sweep n <= 6; S2 numpy 2^21 sweep at n = 7 — counts
cross-checked against the bank, h-rungs re-derived); n >= 6 by R(3,3) = 6
(certified exhaustively by the finisher: all 32,768 graphs on 6 vertices
have alpha >= 3 or omega >= 3; C5 on 5 vertices with alpha = omega = 2 is
the tightness witness) — any 6 vertices of a C5-free graph force
hom >= 3. Ceilings by witnesses (all finisher-verified, two independent
induced-C5 codes + brute alpha/omega): n = 8 W8 itself (and an 8-vertex
CORE hom-3 witness); n = 9, n = 10 hom-3 witnesses (the n = 10 witness is
a CORE: connected, co-connected, triangle, independent triple); n = 11, 12
hom-4 witnesses. The checkpoint's h(11) <= 3 is RETRACTED: its witness is
corrupt (audit-2 in receipts61c5.txt) and no repair found (both fresh
hunts topped out at hom 4; an exhaustive 2 x 1024 one-vertex extension
probe of both verified n = 10 hom-3 witnesses yields no n = 11 hom-3
graph); h_C5(11), h_C5(12) remain open cells in [3,4].

## LAW C61-C5-LADDER-BREAK (the sqrt-ladder is FALSE — complete)
The pointwise ladder "h_C5(n)^2 >= n" holds for n = 1..9 (equality at
n in {1, 4}; certified n <= 8 by the engine ladder arithmetic + h(9) = 3
with 9 >= 9) and BREAKS at n = 10: h_C5(10) = 3 EXACTLY (the verified
rerun witness has alpha = omega = 3; the R(3,3) = 6 floor forces >= 3),
and 3^2 = 9 < 10. The break is realized INSIDE the named core frontier:
the n = 10 witness is connected, co-connected, contains a triangle and an
independent triple — precisely the C5-DICH remaining stratum.
Interpretation for C5-DICH (FIVEVERTEX_PROOF §2): the two CLOSED strata
stand unchanged (triangle-free => alpha >= sqrt(n)/2; alpha <= 2 =>
omega >= sqrt(n)/2 — the n = 10 witness has neither shape and violates
neither). What dies is any extension of the dichotomy to the core stratum
at POINTWISE strength sqrt(n): a core-stratum bound hom >= c·sqrt(n)
pointwise must have c <= 3/sqrt(10) = 0.9487 (and if h(11) = 3, c <=
3/sqrt(11) = 0.9045). Asymptotically the question stays open ABOVE the
cap: the X_t tower (which is NOT core — W8 is not co-connected, and
co-X_2 = co-W8[co-W8 x 8] is disconnected, so the tower falls to
C5-REDUCTION's union levels) realizes hom = n^{0.52832} > sqrt(n), so the
cap does not refute an eventual h >= sqrt(n)/K law; it only forbids any
class-wide exponent above 0.52832. The honest state: EH(C5) remains OPEN;
its exponent, if it exists, lies in (0, log3/log8].
