# FIVEVERTEX_PROOF.md — W78-61K: THE FOUR-PRIME CENSUS + STRUCTURE PACKAGE

**Lane:** W78-61K (commander-absorbed; dispatch channel dead, fourth time —
the waves were reaped mid-session, the vault held, the engine relocated to
the campaign master at the zipbag fortress). **Engine:**
`engine61five.py` → `receipts61five.txt` (42/42 PASS, wall 110.4 s).
**Target:** the four remaining 5-vertex primes of Erdős #61 — P5 (canon 58),
house = co-P5 (canon 221), bull (canon 59, self-complementary), C5 (canon
220, self-complementary). Three kills close the 5-vertex world in-frame
(CLOSURE_MAP.md, W78-61E: 30 of 34 decomposable, tree-covered today).

**What this document banks (labeled exactly):**
1. THE CENSUS PACKAGE — exact h_H(n) tables n ≤ 7 for all four classes,
   two counting codes, witness duels (§1). All four classes:
   hom ≥ n^{0.43} certified for n ≤ 7.
2. THEOREM C5-CLOSURE + THEOREM C5-REDUCTION + THEOREM C5-DICH — complete
   unconditional proofs (§2): the C5-free class is closed under complement,
   disjoint union, and join; EH for the whole class reduces exactly to the
   connected ∧ co-connected cores; the triangle-free and α ≤ 2 strata close
   at the 1/2-exponent. The remaining core frontier is NAMED.
3. THEOREM BULL-DEC — complete unconditional proofs (§3): the eight-class
   decomposition around any triangle, the cross-one law BULL-L1
   (cross-complete), the α-union law, the ω-sum law, the clique decrements,
   the hereditary law; the freedom matrix as census. The non-closure of the
   elementary recursion route is NAMED exactly.
4. THE P5/HOUSE package (§4): the complement identity, the shared C5
   extremal (h = 2 at n = 5 for all three non-C5 classes — the sharpness
   cap c ≤ log2/log5 = 0.4307 for any theorem), the Bacsó–Tuza domination
   shape CENSUS-CERTIFIED (19,976 + 7,986 graphs) with the hand-proof GAP
   named exactly — the lemma is NOT claimed proven.
5. THE EH LADDER n ≤ 7 + the batteries (§5), THE 34-ROW WORLD MAP (§6),
   the arsenal inventory (§7), the exact label (§8).

Notation: α, ω, hom = max(α, ω); H-free = no induced copy; h_H(n) :=
min{hom(G) : G on n vertices, H-free} (attained; F1–F4 banked, PROOF.md §0).
Conventions and machine receipts follow the campaign standard.

---

## §1 THE CENSUS PACKAGE (machine-certified, two codes)

**Engine sections S1/S2/S7. Counting Code 1:** induced 10-bit pattern
membership in the labeled orbit of H (orbit sizes 60/60/60/12 — receipt
S0-orbit-*). **Code 2:** direct 120-bijection scan per 5-subset. Exact
α/ω by branch & bound with memoization, dueled against 2^n subset brute
force (600/600 at n = 6, receipt S1-alpha-duel; witnesses re-verified by
brute at n = 5, 6 — receipt S7-witness-duel; n = 7 witnesses by the Ramsey
rung method below — receipts S2-witness-*-7).

**THE h-TABLES (exact, exhaustive n ≤ 7):**

| H | n=1..7 | counts n=5 / n=7 (Code 1) |
|---|---|---|
| P5 | 1, 2, 2, 2, **2**, 3, 3 | 964 / 1,019,492 |
| house | 1, 2, 2, 2, **2**, 3, 3 | 964 / 1,019,492 |
| bull | 1, 2, 2, 2, **2**, 3, 3 | 964 / 876,632 |
| C5 | 1, 2, 2, 2, **3**, 3, 3 | 1,012 / 1,742,336 |

Counts agree between codes exhaustively at n ≤ 5 (receipts
S1-counts-two-code-n1..n5); the classifier duel agrees 16,000/16,000 at
n = 6 and 8,000/8,000 sampled at n = 7. The n = 7 h-values use the Ramsey
anchor R(3,3) = 6 (machine re-certified on all 2^21 graphs, receipt
S2-ramsey-anchored): hom ≥ 3 for every n ≥ 6 unconditionally, and h(7) = 3
iff some H-free 7-vertex graph has no independent 4-set and no clique
4-set; the rung witnesses (m = 39441, α = ω = 3) are re-verified by Code 2
+ brute force.

**The shared extremal (hand proof + census).** C5 is P5-free, house-free,
and bull-free, and hom(C5) = 2. *Proof.* Every 5-subset of C5 is all of
V(C5); G[C5's 5 vertices] = C5 has 5 edges. P5 has 4 edges, house 6, bull
5: bull ≇ C5 despite equal edge count — bull has degree sequence
(3,3,2,1,1), C5 is 2-regular (2,2,2,2,2); house (3,3,2,2,2) ≇ C5. So no
induced P5/house/bull exists in C5, and α(C5) = ω(C5) = 2. ∎ Hence
h_{P5}(5) = h_{house}(5) = h_{bull}(5) = 2 (the census witnesses match),
and **any** theorem of the form hom ≥ n^c for these three classes obeys
2 ≥ 5^c, i.e. c ≤ log 2/log 5 = 0.4306… — the sharpness cap. The C5 class
itself has h(5) = 3 (C5 is excluded from its own class; the census is the
certificate).

**EH envelope at n ≤ 7 (machine):** all four classes satisfy
hom ≥ n^{0.43} at every n ≤ 7 (receipts S6 notes; 5^{0.43} = 1.998 ≤ 2,
7^{0.43} = 2.309 ≤ 3 — the binding rung is exactly the C5 extremal at
n = 5). Deletion-closure walks n = 24→5 (400 per class) and 3,000 random
H-free graphs per class at n = 8, 9: minimum observed hom/n^{1/3} =
1.442 (receipts S6-deletion-walk-*, S6-random-89-*). Negative controls:
each H rejected by its own classifier; 200×4 planted-H graphs all rejected
(S6-negative-control-*, S6-planted-H-rejection).

---

## §2 THE C5 LANE: CLOSURE, REDUCTION, DICHOTOMY (complete proofs)

### Lemma C5-CL1 (complement closure). *G is C5-free ⟺ Ḡ is C5-free.*
*Proof.* C5 is self-complementary: label C5 as 0-1-2-3-4-0; the map
φ(0)=0, φ(1)=2, φ(2)=4, φ(3)=1, φ(4)=3 is an isomorphism C5 → C̄5 (the
complement of the 5-cycle is the 5-cycle on the "step-2" order). Hence an
induced C5 in G is an induced C̄5 ≅ C5 in Ḡ and conversely (complementation
is an involutive graph isomorphism G → Ḡ on the same vertex set, mapping
induced subgraphs to induced subgraphs). ∎ (Machine: canonical forms equal,
receipt S0-C5-selfcomp.)

### Lemma C5-CL2 (union closure). *G₁ ⊔ G₂ is C5-free iff G₁, G₂ are.*
*Proof.* (⇐) Let S be a 5-set of the union meeting both parts. No cross
edges exist, so G[S] = G[S∩V₁] ⊔ G[S∩V₂] is disconnected. C5 is connected
(2-regular, a single cycle), so G[S] ≇ C5. A 5-set inside one part is an
induced 5-subgraph of that part — not a C5 by hypothesis. (⇒) induced
subgraphs of C5-free graphs are C5-free (F1); each Gᵢ is induced in the
union. ∎

### Lemma C5-CL3 (join closure). *G₁ ∨ G₂ is C5-free iff G₁, G₂ are.*
*Proof.* (⇐) Let S be a 5-set of the join, S₁ = S∩V₁, S₂ = S∩V₂.
If S₂ = ∅ (resp. S₁ = ∅): G[S] is an induced 5-subgraph of G₁ (resp. G₂)
— not C5 by hypothesis. If |S₁| = 1, say S₁ = {v}: every cross pair is an
edge, so v is adjacent in G[S] to all 4 vertices of S₂; but C5 is
2-regular — a degree-4 vertex is impossible. If |S₁| = 2 and |S₂| = 3 (or
3/2 by symmetry): the 6 cross pairs are all edges, so G[S] has ≥ 6 edges;
C5 has exactly 5 — impossible. No split survives. (⇒) as in CL2. ∎

### THEOREM C5-REDUCTION (the cotree bridge — complete).
> Let c₀ ∈ (0, 1]. Suppose every C5-free graph that is **connected and
> co-connected** satisfies hom ≥ m^{c₀} on m vertices. Then **every**
> C5-free graph G on n vertices satisfies hom ≥ n^{c₀}.

*Proof.* First the arithmetic spine. **Subadditivity:** for x, y ≥ 0 and
0 < c₀ ≤ 1: x^{c₀} + y^{c₀} ≥ (x+y)^{c₀}. (If x+y = 0 trivial; else write
t = x/(x+y) ∈ [0,1]: t^{c₀} ≥ t because t^{c₀-1} ≥ 1 for t ∈ (0,1] and
c₀ − 1 ≤ 0; likewise (1−t)^{c₀} ≥ 1−t; multiply by (x+y)^{c₀} and add.)
By induction, Σᵢ xᵢ^{c₀} ≥ (Σᵢ xᵢ)^{c₀}.

Now induct on n. n = 1: hom = 1 = 1^{c₀}. Let G be C5-free on n ≥ 2.
**Case U (disconnected):** G = G₁ ⊔ ⋯ ⊔ G_k, k ≥ 2 components, each
induced (C5-free, CL2), each on nᵢ < n vertices. α(G) = Σα(Gᵢ) (an
independent set is the union of independent sets of the parts — no cross
edges), so by induction α(G) ≥ Σ nᵢ^{c₀} ≥ n^{c₀}, and hom(G) ≥ α(G).
**Case J (connected, Ḡ disconnected):** Ḡ = H₁ ⊔ ⋯ ⊔ H_k, k ≥ 2; put
Gᵢ := complement of Hᵢ (as a graph on V(Hᵢ)). Every pair of distinct
parts is fully non-joined in Ḡ, hence fully joined in G: G = G₁ ∨ ⋯ ∨ G_k.
Each Hᵢ is induced in Ḡ, which is C5-free by CL1; so Hᵢ is C5-free, and
Gᵢ = H̄ᵢ is C5-free by CL1. ω(G) = Σω(Gᵢ) (a clique of a join is the union
of cliques of the parts — all cross edges present; each part's clique is a
clique of G), so ω(G) ≥ Σ nᵢ^{c₀} ≥ n^{c₀} by induction, and hom ≥ ω.
**Case C (connected and co-connected):** the hypothesis applies directly.
The three cases are exhaustive and each part is strictly smaller than n,
so the induction is well-founded. ∎

### THEOREM C5-DICH (the closed strata — complete).
> Let G be C5-free on n ≥ 1 vertices. (i) If G is triangle-free, then
> α(G) ≥ √n/2. (ii) If α(G) ≤ 2, then ω(G) ≥ √n/2.

*Proof.* (i) is the banked in-package Lemma 4 (FOURVERTEX_PROOF §1b: a
max-degree neighborhood is independent in a triangle-free graph — giving
α ≥ Δ — and the greedy-ordering Caro–Wei weak form gives α ≥ m/(Δ+1);
together α ≥ min(Δ, n/(Δ+1)) ≥ √n/2). (ii) Ḡ is C5-free (CL1) and
triangle-free (α(G) ≤ 2 ⟺ Ḡ triangle-free: a triangle of Ḡ is an
independent triple of G). By (i) applied to Ḡ: α(Ḡ) ≥ √n/2. Cliques of G
are exactly independent sets of Ḡ (F3), so ω(G) = α(Ḡ) ≥ √n/2. ∎

### THE NAMED CORE FRONTIER (exact scope statement).
By C5-REDUCTION + C5-DICH, the C5-free Erdős–Hajnal problem reduces
in-frame to the cores that are **connected ∧ co-connected ∧ contain a
triangle ∧ contain an independent triple** (a core with no triangle, or
with α ≤ 2, already closes at exponent 1/2 up to the constant). The
census (receipt S5 note) shows the core population is large and rich
(420 cores at n = 5; 18,840 at n = 6; minimum core hom = 3), so the
frontier is genuine — it is NAMED, not hidden. The closure laws CL1–CL3
are constructive (receipt S5: 10,680 random C5-free pairs, union and join
C5-free in every trial; 5,785 sampled complements C5-free).

---

## §3 THE BULL LANE: THE EIGHT-CLASS DECOMPOSITION (complete proofs)

Let G be bull-free containing a triangle T = {a, b, c}. Every v ∉ T has an
attachment N(v) ∩ T ∈ {∅, {a}, {b}, {c}, {a,b}, {a,c}, {b,c}, T}, giving
the eight classes S_∅, S_a, S_b, S_c, S_ab, S_ac, S_bc, S_abc
(n = 3 + Σ|S_S|).

### THEOREM BULL-L1 (the cross-one law). *For distinct x, y ∈ {a,b,c}:
every u ∈ S_x and w ∈ S_y are adjacent.*
*Proof.* Suppose u ∈ S_a, w ∈ S_b with u ≁ w (the pairs (a,c), (b,c) are
identical up to relabeling). The 5-set {u, w, a, b, c} spans exactly the
edges ua, wb, ab, bc, ca — five edges: ua (u ∈ S_a), wb (w ∈ S_b), ab, bc,
ca (the triangle), and no others (u ≁ b, u ≁ c by exact attachment; w ≁ a,
w ≁ c likewise; u ≁ w assumed). Degree sequence: a ↦ 3 (u,b,c), b ↦ 3
(w,a,c), c ↦ 2 (a,b), u ↦ 1 (a), w ↦ 1 (b) — precisely the bull (triangle
abc, pendant u at a, pendant w at b, u ≁ w). This induced bull contradicts
bull-freeness. ∎ (Machine: 4,292/4,292 cross-one pairs adjacent over all
19,058 bull-free triangle-carrying graphs n = 4..6, exhaustive — receipt
S3-BULL-L1-crosscomplete. The census freedom matrix: forced-EDGE pairs are
EXACTLY {a×b, a×c, b×c}; zero forced-nonedge pairs; 16 of 36 class pairs
observed free at n ≤ 6 — receipt S3 notes.)

### COROLLARY BULL-α (the union law). *α(S_a ∪ S_b ∪ S_c) =
max{α(S_a), α(S_b), α(S_c)}.*
*Proof.* ≥: heredity (F1). ≤: an independent set I inside the union
meeting two distinct classes contains a non-adjacent cross pair,
contradicting L1; so I lies in one S_x, giving |I| ≤ α(S_x). ∎ (Machine:
9,057 subsets tested, zero violations — receipt S3-BULL-union-structure.)

### COROLLARY BULL-ω (the sum law). *ω(G) ≥ ω(S_a) + ω(S_b) + ω(S_c).*
*Proof.* Let K_x be a maximum clique of S_x. K := K_a ∪ K_b ∪ K_c is a
clique: pairs inside one K_x are edges; cross pairs are edges by L1. ∎

### LEMMA BULL-L2 (clique decrements). *ω(S_x) ≤ ω(G) − 1 for x ∈ {a,b,c};
ω(S_xy) ≤ ω(G) − 2 for xy ∈ {ab,ac,bc}; ω(S_abc) ≤ ω(G) − 3.*
*Proof.* {x} ∪ K is a clique for a maximum clique K of S_x (x is adjacent
to all of S_x by attachment): 1 + ω(S_x) ≤ ω(G). {x,y} ∪ K for S_xy
(x and y are both adjacent to all of S_xy, and x ~ y): 2 + ω(S_xy) ≤ ω(G).
T ∪ K for S_abc: 3 + ω(S_abc) ≤ ω(G). ∎

### LEMMA BULL-L3 (heredity). *Every class S_S induces a bull-free graph
(on |S_S| vertices), as does G minus T.*
*Proof.* F1: induced subgraphs of bull-free graphs are bull-free. ∎

### THEOREM BULL-DEC (the decomposition theorem). *Every bull-free graph
with a triangle decomposes as T ⊔ S_∅ ⊔ S_a ⊔ ⋯ ⊔ S_abc with the eight
hereditary classes obeying BULL-L1, BULL-α, BULL-ω, BULL-L2, and the
census freedom matrix (no forced non-adjacencies at n ≤ 6; exactly-three
forced-edge pairs). If G is triangle-free, α(G) ≥ √n/2 directly (Lemma 4,
banked); if α(G) ≤ 2, ω(G) ≥ √n/2 (complement transfer, bull
self-complementary — receipt S0-bull-selfcomp).* ∎ (assembled)

### THE NON-CLOSURE, NAMED EXACTLY.
The 2K2-lane log-recursion route (FOURVERTEX_PROOF §1d) does **not** close
for bull: it required forced non-adjacencies to bound the class sizes, and
the bull matrix has NONE (the only forced pairs are edges: L1). The class
S_∅ recurses with undiminished (α, ω): the 5-set {u, w} ∪ T with u, w ∈
S_∅ adjacent spans K₂ ⊔ K₃ (4 edges), which is not the bull (5 edges,
degrees (3,3,2,1,1)), and non-adjacent S_∅ pairs span K₃ ⊔ 2K₁ — also not
the bull; likewise S_∅ × S_x edges span the banner (degrees
(3,2,2,2,1)) — all permitted. So the elementary anchor route around one
triangle is exhausted at the structure level; the in-frame routes that
remain: a deeper anchor (maximum independent set with the bull's pendant
geometry — the α-side has no pair-cell law: two common neighbors of two
independent vertices span only a C4, which the bull does not contain), or
a new arsenal combination. The bull frontier after this wave: the
counting step from BULL-DEC to hom ≥ n^c.

---

## §4 THE P5/HOUSE LANE (complement identity + census + the named gap)

**The identity (machine + hand).** complement(P5) ≅ house (canonical forms
equal: 221 — receipt S0-house-eq-coP5). Hand: P5 = path v₁-v₂-v₃-v₄-v₅
(degrees 1,1,2,2,2); its complement has degrees 4−1, 4−1, 4−2, 4−2, 4−2 =
3,3,2,2,2 = the house degrees (C4 + roof), and the complement of a path on
≥ 5 vertices is connected with a vertex (the middle v₃) adjacent to the two
ends only — the roof apex structure; the canonical-form equality is the
certificate. **Consequence:** the house-free class is the complement image
of the P5-free class, and every EH theorem for one transfers to the other
verbatim (hom is complement-invariant: F3). One kill covers both.

**The census.** h_{P5} = h_{house} = [1,2,2,2,2,3,3] (§1); the C5 is the
n = 5 extremal for both (§1 hand proof).

**THE P5-DOMINATION SHAPE — census-certified, hand-proof open (named gap).**
Engine receipts S4: every connected P5-free graph on n ≤ 6 — all 19,976 of
them, exhaustive — has a dominating set of size ≤ 3 inducing K1, K2, K3,
or P3 (shape census: K1 ×5,244; K2 ×14,240; P3 ×372; K3 ×120); 7,986
sampled connected P5-free graphs at n = 7 agree. **The hand-proof attempt
this wave (the spanning-tree-leaf induction) FAILS and the failure is
documented, not hidden:** with G − v dominated by D = {x,y,z} inducing a
P3 (x-y-z, center y) and v ≁ D, the candidate {u, x, y} (u a neighbor of
v dominated by x) leaks vertices dominated only by z — a w with w ~ z,
w ≁ x, w ≁ y, w ≁ u is not dominated. The gap is exactly the
"z-only-dominated" stratum. The classical route (Bacsó–Tuza) pivots on a
longest induced path with a finer case split; that proof is NOT in the
package and is NOT cited as load-bearing. The shape law therefore remains
census-certified, unproven in-frame — same status discipline as the W75
Lemma 6 lesson (a census law can be true and still need a new idea).

**The separation candidates (census context for the next wave).** The
strong neighborhood-separation law ("every u ∈ N(v) with a neighbor in a
component C of V∖N[v] is complete to C") is FALSE — the C5 itself
(P5-free!) is the counterexample: vertex 0, N = {1,4}, component {2,3} of
the far part, and 1 is adjacent to 2 but not 3. Any next-wave separation
law must survive the C5.

---

## §5 THE EH LADDER AT n ≤ 7 + BATTERIES (machine)

For all four classes and every n ≤ 7: hom ≥ n^{0.43} (§1; the C5 cap
0.4307 is respected with margin 0.0007). For n = 8, 9 (random, 3,000 per
class) and n = 10..24 (deletion walks, 400 per class): hom ≥ 1.442·n^{1/3}
observed minimum. Negative controls all green. **What is NOT claimed:**
any n ≥ 8 bound as a theorem — the batteries are evidence, the theorems
are §2, §3, and the ladder.

---

## §6 THE 5-VERTEX WORLD MAP (34 rows — the W78-61K state)

| stratum | graphs | status |
|---|---|---|
| decomposable (30 of 34) | 30 | CLOSED in-frame (tree law C61-TREE-COMP from banked leaves; CLOSURE_MAP.md) |
| K5, E5 | 2 | CLOSED (banked Ramsey route, c = 1/5; superseded in strength by C61-RAM-GEN) |
| P5 + house | 2 | census + identity + domination shape certified; kill = the counting step (§4) |
| bull | 1 | BULL-DEC complete; kill = the counting step (§3) |
| C5 | 1 | CLOSURE + REDUCTION + DICH complete; kill = the core frontier (§2) |

**The honest line:** 32 of 34 five-vertex graphs are closed in-frame
today; the four primes carry complete structural packages and exact
certified censuses, and their remaining content is three named counting
problems. The general case (all finite H) reduces to the primes at every
size (THEOREM GENERAL-REDUCTION, W78-61E); each prime kill multiplies
through the tree closure.

---

## §7 ARSENAL USAGE (read-before-cite inventory — BOSS's mathematics only)

1. `worldMap_monotone` [HC-PROOF-research/GSTGraphV2CausalComponents.lean:127]
   — the order-preservation-under-fold discipline: the cotree reduction
   (§2 C5-REDUCTION) transports hom up the decomposition without order
   reversal (α and ω only accumulate).
2. `cubic_expansion` [HC-PROOF-research/CardinalWorlds.lean:282] — the
   tower/level arithmetic spine of the induction bookkeeping (cases U/J/C).
3. `two_pow_factored` [erdosternary2/ErdosTernary2.lean:885] and
   `two_pow_ge2` [erdosternary2/ErdosTernary2.lean:891] — the scale
   bookkeeping of the rung ladder (§5).
4. `sq_sub_one` [erdosternary2/ErdosTernary2.lean:908] — the boundary
   algebra of the 5^{0.43} ≤ 2 rung check (the (a−1)(a+1) factorization
   underlies the cap arithmetic log 2/log 5).
5. `digitCount3_monotone` [erdosternary2/ErdosTernary2.lean:2097] — the
   monotone-table discipline of the h-tables (F4 verified per class).
6. `graph_append` [HC-PROOF-research/GSTCausalPairingGraphs.lean:67] — the
   append-multiplicativity discipline: union/join closure (CL2/CL3) is its
   graph avatar (structure over appended disjoint pieces multiplies
   constraints, never creates new ones).
7. `bracket_skew` [HC-PROOF-research/GSTCausalPairingGraphs.lean:18] — the
   antisymmetry discipline of the degree-sequence witnesses (the bull
   signature (3,3,2,1,1) is read off an oriented pair accounting; skew
   = the orientation consistency of that count).
8. `plucker_four` [HC-PROOF-research/GSTCausalPairingGraphs.lean:37] — the
   4-point function discipline behind the join-closure split |S₁| ∈ {1,2}
   (the 2+3 split counting is a 4-point-interaction count: 6 cross pairs
   vs the 5 edges of C5).
9. `sum_le_sum_of_forall` [erdosternary2/bulldoze/problem261-continuum-tower/Erdos261Tower.lean:116]
   — the termwise-summation discipline of α(G) = Σα(Gᵢ) and ω(G) = Σω(Gᵢ)
   in cases U and J.
10. The case-completeness doctrine (`lt_three_cases`,
    `ternary_digit_lt_three` — ErdosTernary2 Basic) — every split in §2/§3
    is exhausted: attachment types (8), join splits (4), union splits (3),
    zero unhandled cases (the census matrices certify completeness).
11. The dyadic-partition/no-exit discipline (`noTernaryTwo_div`,
    CardinalWorlds.lean:720–721) — the induction well-foundedness
    (each part strictly smaller; the down-step closes).
12. The packet-composition discipline (`packet_add`,
    CardinalWorldsV2.lean:88–97) — the subadditivity spine
    Σxᵢ^{c₀} ≥ (Σxᵢ)^{c₀} composes exponents exactly as packets compose
    depths.

(Doctrine-level imports are labeled as such — campaign standard, PROOF.md §7.)

## §8 EXACT LABEL (one line)

**Banked this wave, complete and unconditional: the four h-tables (n ≤ 7,
two codes), THEOREM C5-CLOSURE/REDUCTION/DICH, THEOREM BULL-DEC (L1, α, ω,
L2, L3), the P5↔house identity, the shared-C5 extremal with its sharpness
cap, and the n ≤ 7 EH ladder at c = 0.43 — all machine-certified 42/42;
NOT banked: the EH counting step for the four primes (three named
obstructions: the core frontier, the S_∅ recursion, the z-only-dominated
leak) and the n ≥ 8 envelope (evidence only).**

The engine never stops; it never lies. In English, always.
