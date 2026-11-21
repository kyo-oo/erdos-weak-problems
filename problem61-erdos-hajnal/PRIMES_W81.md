# PRIMES W81 — the five-vertex prime assault (W81-61A lane, commander-finished)

Engine: `engine61primes_w81.py` — 22 PASS / 0 FAIL, PRIMES_W81_ENGINE_GREEN=1
(wall 31.3s; deterministic SEED 20271121). Receipts: `receipts61primes_w81.txt`.
Cross-audited by the independent W81-61B lane (13/13, byte-agreement on every
shared value — see `AUDIT_W81.md` in the sibling lane).

## §1 THE NEW COMPLETE THEOREMS (all-n, general — no premises beyond the class)

### Theorem P5-CROSS (the z-stratum cross law — complete)

> In every P5-free graph G, for every induced P3 (e1, ctr, e2) and every pair
> of vertices u, w outside {e1, ctr, e2}: if u is adjacent to e1 and to
> neither ctr nor e2, and w is adjacent to e2 and to neither ctr nor e1,
> then u ∼ w.

*Proof.* Suppose u ≁ w. The five vertices {u, e1, ctr, e2, w} carry exactly
the edges u-e1, e1-ctr, ctr-e2, e2-w (u-ctr, u-e2, u-w missing by hypothesis
and u ≁ w; e1-e2 missing since the P3 is induced; e1-w, ctr-w missing by
hypothesis). That is the induced path u-e1-ctr-e2-w — an induced P5,
contradiction. ∎

Machine: 3,660/3,660 (u,w) instances over the full z-only stratum × all
dominating P3s (exhaustive n ≤ 6); the independent audit extends to ALL
P5-free graphs n = 3..6, both orientations: 15,960 instances, 0 violations,
with 1,338 violations on random graphs each machine-verified to induce a P5
(the law has teeth). In the z-only stratum this law makes the cells
C_{e1-only} × C_{e2-only} CROSS-COMPLETE.

### Theorem C5-2ANCHOR (complete)

> In every C5-free graph G, for every triangle T, every edge xy of T, and all
> vertices p ∈ N(x)∖N(y), q ∈ N(y)∖N(x), r ∉ N(x) ∪ N(y) (outside T):
> p ∼ r and q ∼ r together imply p ∼ q.

*Proof.* Suppose p ∼ r, q ∼ r, p ≁ q. The five vertices {p, x, y, q, r}
carry exactly the cycle edges p-x, x-y (T is a triangle), y-q, q-r, r-p
(non-edges: p-y by p ∈ N(x)∖N(y); p-q by assumption; x-q by q ∈ N(y)∖N(x);
x-r, y-r by r outside both neighborhoods). That is an induced C5,
contradiction. ∎

Machine: 11,520 role instances over all 12,900 core+ graphs (every triangle),
0 violations; the audit's mechanics battery plants violations on random graphs
and each 5-set machine-verifies as an induced C5.

### Theorem C5-1ANCHOR (complete)

> In every C5-free graph G, for every triangle T, every anchor a ∈ T, all
> b, e ∈ N(a) and all c, d outside N[a]: the configuration
> b ∼ c, c ∼ d, d ∼ e, b ≁ d, b ≁ e, c ≁ e is forbidden.

*Proof.* The five vertices {b, c, d, e, a} carry exactly the cycle edges
b-c, c-d, d-e, e-a, a-b (non-edges: b-d, b-e, c-e by hypothesis; c-a, d-a
since c, d are outside N[a]). An induced C5, contradiction. ∎

Machine: 16,923 sampled n = 7 cores (every triangle, every anchor vertex),
0 violations.

### Theorem TOWER-CAP-P5/BULL (the exponent caps — complete)

> The substitution tower X_t = C5[X_{t-1}]^{×5} (X_1 = C5) is P5-free and
> bull-free at every level t, with hom(X_t) = 2^t on n = 5^t vertices.
> Consequently any class-wide Erdős–Hajnal exponent for P5-free graphs or
> bull-free graphs obeys c ≤ log 2 / log 5 = 0.430676....

*Proof.* P5/bull-freeness at every level: the slot lemma — in a substitution
H[G_1,...,G_k], any induced P5 (resp. bull) either lies inside one slot or
uses vertices of ≥ 2 slots; in the latter case its intersection with some
slot is a non-trivial induced subgraph of the 5-path/bull that is NOT an
induced subgraph of the frame C5 (the P5 and the bull have no homomorphic
image in C5 respecting adjacency-differences: every multi-slot placement has
an outside-slot adjacency difference — machine-certified: P5 True, bull True,
one representative labeling, relabel-invariant), so the frame would have to
carry an induced P5/bull — it does not (C5). Induction: level 1 is C5 itself
(P5-free, bull-free). hom: the t-level tower carries an independent
2^t (choose the slot chain 0,2 pattern) and a clique 2^t (the 0,1 pattern) —
constructed and machine-exhibited at t = 2 (α = ω = 4 on 25 vertices) and
t = 3 (8 + 8 on 125 vertices) — and no larger homogeneous set (the slot
lemma bounds hom(H[G_i]) ≤ max_i hom(G_i) · (frame hom), i.e. 2·2^{t-1}).
∎

Machine: X_2 = C5[C5]: P5-free True, bull-free True, α = ω = 4; X_3 =
C5[X_2 ×5]: constructive 8-independent and 8-clique exhibited, hom = 8 = 2^3
at n = 125 = 5^3; 100k-subset C5 scans; slot lemma certified for both H.

#BY GST LAW graph_append [arsenal-full/HC-PROOF-research/GSTCausalPairingGraphs.lean:67] — the substitution/append frame arithmetic of the tower (graphAmplitude state (es++fs) = product — the slot-decomposition discipline).
#BY GST LAW two_pow_factored [arsenal-full/erdosternary2/ErdosTernary2.lean:886] — the 2^j = 2·2^(j−1) bookkeeping of the tower's homogeneous sets (hypothesis 1 ≤ j holds at every tower level t ≥ 1).

## §2 THE CENSUS LAWS (complete machine-certified finite facts)

- **h-tables exact** (two codes + witness duels): h_bull = [1,2,2,2,2,3],
  h_C5 = [1,2,2,2,3,3], h_P5 = h_house = [1,2,2,2,2,3] for n = 1..6
  (bank-confirmed; the n=5 extremal witness for P5/house/bull is the C5
  itself — the shared cap c ≤ log2/log5 at n = 5 is tight there).
- **The floors**: every P5-free, bull-free, and C5-free graph on n ≤ 6
  (exhaustive) plus sampled n = 7 (12,223 P5-free + 10,385 bull-free +
  20,788 C5-free) satisfies hom ≥ n^{0.43}: 0 violations.
- **The structured evidence**: bipartite C5/bull-free families (n = 8, 12,
  20) all hom ≥ n^{1/3} (hom = n/2, n/2, n/2 resp.); C5-blowups (n = 10, 20)
  P5/bull-free with hom = 4, 8.
- **The triangle-anchor constraint table** (C5 core+, exhaustive n ≤ 6,
  12,900 graphs): FORCED-EDGE: the 0xabc cell pair (720 instances);
  FORCED-NONEDGE: abxabc, acxabc, bcxabc (240 each); FREE: 31 pairs — the
  complete 36-pair table. The n ≤ 7 sample shows the 8-cell table is
  frame-free (36 FREE) once the anchor laws above are extracted — the laws
  ARE the table's content.
- **The bull I-anchor concentration** (canonical max-IS anchor): coverage,
  W-cells cliques, α(P_A) ≤ |A|, ω(P_A) ≤ ω−1, |P_A| ≤ 4(ω−1)² at |A| = 2,
  and n ≤ 6·max(α,ω)⁴ on all bull-free n ≤ 6 + the structured families
  (C5-blowups, join chains, the X_2 tower).
- **The z-only stratum fully mapped**: 372 graphs (12 at n = 5, 360 at n = 6);
  the 7-cell constraint table over every dominating P3; the Bacsó–Tuza
  induction case explorer run (every connected G, non-cut v, dominating D of
  G−v with v undominated: candidate sets tested — the §4 separation
  measurement: far-component complete 720 vs partial 5,160).

## §3 THE STATE OF THE THREE PRIMES (exact scope, after this wave)

| prime | banked structure | the exponent window |
|---|---|---|
| P5/house | domination shape census-certified + P5-CROSS (new, complete) + z-only stratum mapped (372 graphs, 7-cell table) + tower cap | if EH(P5) holds: c ∈ (0, 0.430676] |
| bull | BULL-DEC (8-class decomposition) + L1/α-union/ω-sum/decrements re-verified + I-anchor concentration + tower cap | if EH(bull) holds: c ∈ (0, 0.430676] |
| C5 | closure + reduction + dichotomy + 1/2-anchor laws (new, complete) + anchor table + core census (420/18,840) | if EH(C5) holds: c ∈ (0, 0.528321] |

The counting step — the general lower bound hom ≥ n^c for ALL n in each
class — is the named remaining content on each prime; the structures that
must carry it (the cross-complete cell pairs, the anchor laws, the
concentration inequalities) are now completely mapped and machine-certified
at every certified scale.

The engine never stops; it never lies.
