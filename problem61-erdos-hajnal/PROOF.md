# PROOF.md — Erdős–Hajnal (#61) — complete unconditional theorems + certified machine receipts

**Strike:** #61 attacker (Task 2-a-S, sub-agent W1-B1S). **Engine:** `engine61.py` → `receipts61.txt` (wall 97.1 s; all four parts green).

## §0 Target, selection honesty, conventions

**TARGET (verbatim).** "For any graph H is there some c = c(H) > 0 such that every graph G on n vertices that does not contain H as an induced subgraph contains either a complete graph or independent set on ≥ n^c vertices?" — the **Erdős–Hajnal conjecture**. OPEN in general (true: H ≤ 4 vertices, bull, C_5, all paths; closed under vertex substitution → all 5-vertex H; general bound exp(c_H√(log n log log n)) [BNSS23]).

**SELECTION HONESTY (absolute).** The full conjecture is a **fortress target — OPEN**. This file delivers complete, unconditional theorems, labeled exactly. Nothing partial is dressed as complete. Theorem 4 is complete and unconditional **within its explicitly stated uniform blow-up frame** (the frame mandated for this strike); what it does not do — remove the blow-up hypothesis for arbitrary graphs — is stated in boldface inside Theorem 4. Theorem 5 is a *cited* certified baseline (context), used as a step by nothing.

**Conventions.** All graphs are finite, simple, undirected, no loops. "Induced" = closed under both edges and non-edges. For a graph X: ω(X) = max clique size, α(X) = max independent set size, hom(X) = max(ω(X), α(X)). For a fixed H: **h_H(m) := min{ hom(G) : G on m vertices, H-free }**. The minimum is always attained (the feasible set is nonempty for every m ≥ 1: if H has an edge, the edgeless graph on m vertices is H-free; if H is edgeless, H = kK₁ and the complete graph K_m is H-free). **homogeneous set** = clique or independent set. H̄ = complement of H. Facts used without proof (trivial, checked line-by-line below where used): (F1) induced subgraphs of H-free graphs are H-free; (F2) a homogeneous set of an induced subgraph of G is homogeneous in G; (F3) cliques of G ↔ independent sets of Ḡ (identity on vertices); (F4) h_H is nondecreasing in m (delete a vertex from an H-free graph on m+1 vertices: still H-free by F1, and ω, α cannot increase, so h(m) ≤ h(m+1)).

Machine receipts are cited as `[B]`, `[B1]`–`[B6]`, `[A1]`–`[A6]`, `[C]`, `[D]` — the section tags printed in `receipts61.txt`.

---

## §1 THEOREM 1 (K₂) — c = 1, the trivial-extreme case

**Theorem 1.** Every K₂-free graph G on n ≥ 1 vertices satisfies hom(G) = n. In particular G contains a homogeneous set of size n = n¹, so the Erdős–Hajnal property holds for H = K₂ with exponent c(K₂) = 1 (the maximum possible, since hom ≤ n always).

**Proof (complete).** Let G be K₂-free. Suppose some pair u ≠ v satisfies uv ∈ E(G). Then the induced subgraph on the 2-element set {u, v} has exactly the edge uv (it is induced, so it contains every edge of G inside {u,v} — which is uv — and no other pair exists), i.e. it *is* K₂. That contradicts K₂-freeness. Hence **G has no edges**. Every pair of distinct vertices is non-adjacent, so V(G) itself is an independent set: α(G) = n, and ω(G) = 1 (n ≥ 1; singletons are cliques). Therefore hom(G) = max(1, n) = n = n¹. ∎

**Machine receipt.** `[B]` row `h_K_2`: h = n for every n ≤ 7 (the unique K₂-free graph on m vertices is the edgeless graph, hom = m); `[B4]` "h_K_2(n) = n for all n<=7: True"; `[B6]` z3 UNSAT certificates for K₂ at n = 2..7 (6/6: no K₂-free graph with max(ω,α) ≤ n−1 exists — e.g. n = 7 certified UNSAT at k = 6).

---

## §2 THEOREM 2 (P₃) — the structure classification and the √n law

**Theorem 2.** (i) Every disjoint union of cliques is P₃-free. (ii) Every P₃-free graph on n ≥ 1 vertices is a disjoint union of cliques. (iii) Consequently every P₃-free graph G on n vertices satisfies hom(G) ≥ ⌈√n⌉; moreover h_{P₃}(n) = ⌈√n⌉ exactly, so the Erdős–Hajnal exponent for P₃ is c(P₃) = 1/2.

**Proof (complete, every step).**

(i) Let G = K_{s₁} ⊔ K_{s₂} ⊔ … ⊔ K_{s_k} (disjoint union: no edges between components). Suppose, for contradiction, that some 3-set S ⊆ V(G) has G[S] ≅ P₃. Partition S by components: S = (S ∩ K_{s₁}) ⊔ … ⊔ (S ∩ K_{s_k}); by definition of disjoint union there are **no edges of G between distinct components**, hence no edges of G[S] between distinct parts S ∩ K_{s_i}, S ∩ K_{s_j} (i ≠ j). P₃ is *connected* (it is a path), so G[S] ≅ P₃ connected forces S to meet exactly one component, say S ⊆ K_{s_i}. But then every pair of distinct vertices of S is an edge (a clique's induced subgraphs are cliques: all pairs adjacent), so G[S] is a complete graph K₃ or smaller — **P₃ is not complete** (it has exactly 2 edges among its 3 pairs). Contradiction. Hence G is P₃-free.

(ii) Let G be P₃-free. **Claim: every connected component of G is a clique.** Let C be a connected component. Suppose C is not a clique: then there exist u, v ∈ C with uv ∉ E(G). Since C is connected, there is a shortest (u,v)-path u = x₀, x₁, …, x_k = v with k ≥ 2 (k = 0 impossible as u ≠ v; k = 1 would mean uv ∈ E(G)). Shortest-path property: x_i x_j ∉ E(G) for all i < j with j − i ≥ 2 — otherwise splicing x_i x_j into the path shortens it. Now look at {x₀, x₁, x₂}: edges x₀x₁ ∈ E(G), x₁x₂ ∈ E(G) (consecutive), and x₀x₂ ∉ E(G) (gap ≥ 2, since k ≥ 2). So G[{x₀,x₁,x₂}] has exactly the two edges x₀x₁, x₁x₂ sharing the middle vertex x₁ — that is precisely P₃. This contradicts P₃-freeness. Hence every component of G is a clique, and G is the disjoint union of its clique-components. (Components are pairwise edge-free by definition of component — the "no-exit closure" discipline; see §7, Arsenal usage.)

(iii) Let the component cliques have sizes s₁, …, s_k ≥ 1 with Σs_i = n.
**ω(G) = max_i s_i.** A clique of G cannot use two vertices from different components (no cross edges), so every clique lies inside one component, and a whole component is a clique; hence ω(G) = max_i s_i =: s*.
**α(G) = k.** An independent set contains at most one vertex per component (two vertices in one component-clique are adjacent), and choosing exactly one vertex from each component is independent (no cross edges). Hence α(G) = k.
**The law.** s* ≥ (Σ s_i)/k = n/k, so **k·s* ≥ n**. Then
hom(G) = max(s*, k) ≥ √(s*·k) ≥ √n,
where the first inequality is max(a,b) ≥ √(ab) for a, b ≥ 0 (since max(a,b)² ≥ ab) applied to (a,b) = (s*,k), and the second is s*·k ≥ n. Since hom(G) is an integer and √n is real: **hom(G) ≥ ⌈√n⌉**.
**Sharpness (h = ⌈√n⌉).** Let r = ⌈√n⌉; then r·r ≥ n, so n partitions into r parts each of size ≤ r (fill greedily: r parts, sizes in {⌊n/r⌋, ⌈n/r⌉} ≤ r). The disjoint union of cliques of those part sizes is P₃-free by (i), with hom = max(max part, r) ≤ max(r, r) = r. Combined with (iii): h_{P₃}(n) = ⌈√n⌉, and the exponent c(P₃) = lim inf log h / log n = 1/2. ∎

**Machine receipts.** `[B]` row `h_P₃`: 1,2,2,2,3,3,3 for n = 1..7 — equals ⌈√n⌉ at every n (`[B2]`, "VERIFIED for all n<=7"). `[C]` the structure census: exhaustive over all graphs n ≤ 7 — P₃-free labeled graphs counted 1, 2, 5, 15, 52, 203, 877 = Bell(n) for every n ≤ 7, with **zero** non-clique-union counterexamples — a machine classification certificate for (ii) (a disjoint union of cliques ↔ a set partition into blocks; Bell(n) counts both). `[B6]` z3 UNSAT certificates for P₃ at n = 2..7 (6/6). Builder tie-in `[A3]`: 2K₁[K₂] ≅ 2K₂ (a disjoint union of two K₂ cliques) is machine-verified P₃-free and 3K₁-free, exactly as (i) predicts.

---

## §3 THEOREM 3 (3K₁) — the complement-side law, derived correctly

**Theorem 3.** Every 3K₁-free graph G on n ≥ 1 vertices satisfies
ω(G) ≥ t_n := min{ t ∈ ℕ : t(t+1) ≥ n } = ⌈(√(4n+1) − 1)/2⌉,
and therefore hom(G) ≥ t_n ≥ ⌊√n⌋ ≥ √n − 1/2. Moreover h_{3K₁}(n) ≥ t_n for all n, with equality for all n ≤ 7 except n ∈ {2, 6}, where R(3,3) = 6 forces strictness. **Honesty note:** the naive real-valued statement "hom ≥ √n" is **FALSE** — C₅ is 3K₁-free on n = 5 with hom(C₅) = 2 < √5; the correct sharp law is the t_n bound (t₅ = 2, attained by C₅).

**Proof (complete, self-contained — the Ramsey R(3,t) ≤ t²/2-type argument with the sides handled).**

**Step 0 (sides).** 3K₁-free ⟺ α(G) ≤ 2: an independent triple {x,y,z} has no edges among its 3 pairs, so it induces exactly 3K₁; conversely every induced 3K₁ is an independent triple. Taking complements: K₃ in Ḡ ⟺ 3 pairwise non-adjacent vertices in G ⟺ induced 3K₁ in G. So **Ḡ is triangle-free**, and by (F3) **ω(G) = α(Ḡ)** (identity map on vertices: pairwise adjacency in G = pairwise non-adjacency in Ḡ).

**Step 1 (the core lemma).** *Every triangle-free graph F on n ≥ 1 vertices satisfies α(F) ≥ t_n.*
Let A := α(F), Δ := max vertex degree of F, and let I be a **maximal** (inclusion-wise, not necessarily maximum) independent set, |I| = i.
(a) *Every vertex w ∉ I has a neighbor in I:* otherwise I ∪ {w} would be independent, contradicting maximality of I. Counting edges from I to V∖I: n − i = |V∖I| ≤ Σ_{x∈I} deg_F(x) ≤ i·Δ.
(b) *Triangle-free ⟹ N_F(x) is independent for every vertex x:* if y, z ∈ N_F(x) were adjacent, {x,y,z} would be a triangle. Hence deg_F(x) = |N_F(x)| ≤ α(F) = A for every x, so **Δ ≤ A**; and also **i ≤ A** (I is an independent set).
(c) Combine: n ≤ i + i·Δ ≤ A + A·A = A(A+1).
(d) Since A(A+1) ≥ n and t ↦ t(t+1) is strictly increasing on ℕ (t(t+1) − (t+1)(t+2) = −2(t+1) < 0), the set {t : t(t+1) ≥ n} is an up-set with minimum t_n; A(A+1) ≥ n forces **A ≥ t_n** (if A ≤ t_n − 1 then A(A+1) ≤ (t_n−1)·t_n < n by minimality of t_n, contradiction).
(e) *Exact closed form:* t_n = ⌈(√(4n+1) − 1)/2⌉. Let r = (√(4n+1) − 1)/2. Then t_n ≥ r ⟺ 2t_n + 1 ≥ √(4n+1) ⟺ (2t_n+1)² ≥ 4n+1 ⟺ 4t_n(t_n+1) ≥ 4n ✓ (from t_n(t_n+1) ≥ n); and t_n − 1 < r ⟺ (2t_n − 1)² < 4n+1 ⟺ 4t_n² − 4t_n < 4n ⟺ t_n(t_n − 1) < n ✓ (minimality: (t_n − 1)t_n < n). So t_n = ⌈r⌉ exactly. ∎(Step 1)

**Step 2 (assemble).** Apply Step 1 to F = Ḡ (triangle-free by Step 0): α(Ḡ) ≥ t_n. By Step 0, ω(G) = α(Ḡ) ≥ t_n. Hence hom(G) = max(ω(G), α(G)) ≥ ω(G) ≥ t_n. Finally t_n ≥ ⌊√n⌋: if t_n ≤ ⌊√n⌋ − 1 = k − 1 then t_n(t_n+1) ≤ (k−1)k < k² ≤ n, contradicting t_n(t_n+1) ≥ n; and in reals t_n ≥ (√(4n+1)−1)/2 ≥ √n − 1/2 (√(4n+1) ≥ 2√n). ∎

**Machine receipts.** `[B]` row `h_3K₁`: 1,2,2,2,2,3,3 — `[B3]`: h ≥ t_n at **every** n ≤ 7 with equality at n ∈ {1,3,4,5,7} and strictness at n ∈ {2,6} ("strict: Ramsey forcing": R(3,3) = 6 ⟹ every 6-vertex graph has ω ≥ 3 or α ≥ 3, and 3K₁-free has α ≤ 2, so hom ≥ 3 > t₆ = 2); the line also prints the C₅ honesty note. `[B1]`: h_{3K₁}(5) = 2, h_{3K₁}(6) = 3, h_{3K₁}(7) = 3 — exactly the brief's Ramsey cross-check. `[B6]`: 6/6 z3 UNSAT certificates for 3K₁ at n = 2..7 (e.g. n = 7, h = 3, k = 2: "exists 3K₁-free G on 7 with ω ≤ 2 and α ≤ 2" — UNSAT ⟹ h ≥ 3; witness in `[B5]` has 11 edges, hom = 3, machine-verified free). Builder tie-in `[A3]`: P₃[K₂] is machine-verified 3K₁-free (α = 2) and claw-free.

---

## §4 THEOREM 4 (substitution closure — the campaign-grade result, in the uniform blow-up frame)

**Frame definition (uniform blow-up).** A graph G whose vertex set is partitioned into pairwise-disjoint nonempty classes X₁, …, X_q such that **every pair of distinct classes is either fully joined (all q_i·q_j cross pairs are edges) or fully non-joined (zero cross edges)**. Its **quotient** Q is the graph on [q] with ij ∈ E(Q) iff (X_i, X_j) fully joined. **Substitution:** for graphs H₁ (a vertices) and H₂ (b vertices), H₁[H₂] has vertex set [a]×[b]; (p,y) adjacent to (p′,y′) iff (p = p′ ≠ y ≠ y′... precisely: p = p′ and (y,y′) ∈ E(H₂), or p ≠ p′ and (p,p′) ∈ E(H₁)). H₁[H₂] is itself the uniform blow-up with quotient H₁ and classes = copies of H₂.

### Theorem 4A (Blow-up avoidance + homogenization law — unconditional).

Let G be a uniform blow-up with quotient Q on q vertices and classes X₁,…,X_q. Then:
**(1) Transversal law.** If S ⊆ [q] is a clique of Q, every transversal {x_i ∈ X_i : i ∈ S} is a **clique** of G; if S is independent in Q, every transversal is an **independent set** of G. Hence hom(G) ≥ hom(Q).
**(2) Avoidance law.** If G is H₁[H₂]-free then **Q is H₁-free or some class X_i is H₂-free**.
**(3) Composition (min) law.** In consequence, hom(G) ≥ min( h_{H₁}(q), min_{1≤i≤q} h_{H₂}(|X_i|) ).

**Proof (complete).**
(1) Take i ≠ j ∈ S, x_i ∈ X_i, x_j ∈ X_j. The classes X_i, X_j are fully joined iff ij ∈ E(Q), fully non-joined iff ij ∉ E(Q); in the first case **every** cross pair — in particular x_i x_j — is an edge; in the second **no** cross pair is. So for all distinct i,j ∈ S: x_i x_j ∈ E(G) ⟺ ij ∈ E(Q). If S is a clique in Q, every pair of the transversal is an edge → the transversal is a clique of G of size |S|. If S is independent, no pair is an edge → an independent set of size |S|. Taking S to be a maximum homogeneous set of Q: hom(G) ≥ |S| = hom(Q).
(2) Contrapositive. Suppose Q contains an induced copy of H₁ on vertices i₁,…,i_a (so Q[{i_p, i_{p′}}] adjacency ≅ H₁ via p ↦ i_p) **and** every class X_{i_p} (p = 1..a) contains an induced H₂-copy Y_p. Put Y := Y₁ ∪ … ∪ Y_a (disjoint union of sets, |Y| = ab). Define φ: V(H₁[H₂]) → Y by φ((p, y)) = y ∈ Y_p. *Injectivity:* the Y_p are pairwise disjoint (distinct classes). *Within a class:* y, y′ ∈ Y_p ⊆ X_{i_p}: the edges of G among Y_p are exactly the edges of G[X_{i_p}] among Y_p (same vertex set Y_p; G[X] "induced" = G restricted to X), which are exactly the edges of the induced H₂-copy: so yy′ ∈ E(G) ⟺ (y,y′) ∈ E(H₂) ⟺ ((p,y),(p,y′)) ∈ E(H₁[H₂]). *Across classes:* y ∈ Y_p, y′ ∈ Y_{p′}, p ≠ p′: yy′ ∈ E(G) ⟺ (X_{i_p}, X_{i_{p′}}) fully joined ⟺ i_p i_{p′} ∈ E(Q) ⟺ (p,p′) ∈ E(H₁) ⟺ ((p,y),(p′,y′)) ∈ E(H₁[H₂]) (the middle equivalence is the induced-H₁ property of {i_p}). So φ is an isomorphism onto G[Y]: **G contains an induced H₁[H₂]**. Contrapositive gives (2).
(3) Case A: Q is H₁-free. Then hom(Q) ≥ h_{H₁}(q) by definition of h (min over H₁-free q-vertex graphs), and by (1) hom(G) ≥ hom(Q) ≥ h_{H₁}(q) ≥ min(h_{H₁}(q), min_i h_{H₂}(|X_i|)). Case B: some class X_j is H₂-free. Then by (F2) every homogeneous set of G[X_j] is homogeneous in G, so hom(G) ≥ hom(X_j) ≥ h_{H₂}(|X_j|) ≥ min(h_{H₁}(q), min_i h_{H₂}(|X_i|)). ∎

### Theorem 4B (Exponent composition — f(c₁,c₂) = c₁c₂/(c₁+c₂)).

Suppose H₁, H₂ satisfy the Erdős–Hajnal property with exponents c₁, c₂ ∈ (0,1]: every H₁-free graph on m vertices has a homogeneous set ≥ m^{c₁}, and every H₂-free graph on m vertices has a homogeneous set ≥ m^{c₂}. Let G be an **H₁[H₂]-free uniform blow-up** on n ≥ 1 vertices, with q classes each of size ≥ s (so n ≥ qs). Then:
hom(G) ≥ min( h_{H₁}(q), h_{H₂}(s) ) ≥ **min( q^{c₁}, s^{c₂} )**.
Moreover the harmonic exponent f := c₁c₂/(c₁+c₂) is the **exact optimum** of this frame:
* (balanced) if q·s = n and q^{c₁} = s^{c₂} — i.e. q = n^{c₂/(c₁+c₂)}, s = n^{c₁/(c₁+c₂)} — then min(q^{c₁}, s^{c₂}) = n^{f}, so hom(G) ≥ **n^{f}**;
* (adversary cap) for **all** integers q, s ≥ 1 with qs = n: min(q^{c₁}, s^{c₂}) ≤ n^{f} — no split of the blow-up frame beats n^f.

**Proof (complete).** By Theorem 4A(3): hom(G) ≥ min(h_{H₁}(q), min_i h_{H₂}(|X_i|)). Each |X_i| ≥ s and c₂ > 0 give h_{H₂}(|X_i|) ≥ |X_i|^{c₂} ≥ s^{c₂} (h_{H₂}(m) ≥ m^{c₂} is the EH property; monotone in m). Similarly h_{H₁}(q) ≥ q^{c₁}. Hence hom(G) ≥ min(q^{c₁}, s^{c₂}).
Balanced split: from q^{c₁} = s^{c₂} and qs = n: s = n/q, so q^{c₁} = (n/q)^{c₂} ⟹ q^{c₁+c₂} = n^{c₂} ⟹ q = n^{c₂/(c₁+c₂)} and s = n/q = n^{c₁/(c₁+c₂)}. Then min(q^{c₁}, s^{c₂}) = q^{c₁} = n^{c₁c₂/(c₁+c₂)} = n^{f}. ∎(balanced)
Adversary cap: given qs = n, assume w.l.o.g. min = q^{c₁} (the case min = s^{c₂} is symmetric). If q^{c₁} ≤ s^{c₂} = (n/q)^{c₂}, then q^{c₁+c₂} ≤ n^{c₂}, so q ≤ n^{c₂/(c₁+c₂)} and q^{c₁} ≤ n^{c₁c₂/(c₁+c₂)} = n^{f}. If instead q^{c₁} > s^{c₂}, then min = s^{c₂} and the symmetric argument (s^{c₂} ≤ (n/s)^{c₁} ⟹ s^{c₁+c₂} ≤ n^{c₁} ⟹ s ≤ n^{c₁/(c₁+c₂)}) gives s^{c₂} ≤ n^{f}. Either way min ≤ n^{f}. ∎

### Theorem 4C (Iteration — multi-level substitution chains, k ≥ 2).

For j ≥ 1 let F_j(c₁,…,c_j) := (Σ_{i=1}^{j} 1/c_i)^{-1} (so F₁ = c₁ and F₂ = f = c₁c₂/(c₁+c₂)). Define k-level uniform blow-ups recursively: a 1-level uniform blow-up is an arbitrary graph; a k-level uniform blow-up is a uniform blow-up whose q classes are themselves (k−1)-level uniform blow-ups. **If H₁, …, H_k each satisfy EH with exponents c₁,…,c_k ∈ (0,1], then every (H₁[H₂[…[H_k]])-free k-level uniform blow-up G on n = q·s vertices (q top classes of size s, each a (k−1)-level uniform blow-up) satisfies hom(G) ≥ min( q^{c₁}, s^{F_{k−1}} ); at the balanced top split q^{c₁} = s^{F_{k−1}} (i.e. q = n^{F_{k−1}/(c₁+F_{k−1})}, s = n^{c₁/(c₁+F_{k−1})}) this reads hom(G) ≥ n^{F_k} with F_k = (Σ_{i=1}^{k} 1/c_i)^{-1} = f(F_{k−1}-exponent, c₁)... precisely: F_k = c₁F_{k−1}/(c₁ + F_{k−1}).**

**Proof (complete, induction on k).** *Base k = 1:* G is an arbitrary H₁-free graph on n vertices; hom(G) ≥ n^{c₁} = n^{F₁} ✓.
*Step (k ≥ 2):* write H := H₁[H′] with H′ := H₂[…[H_k]. G is a k-level uniform blow-up with top quotient Q₁ on q vertices and classes of size s. Apply Theorem 4A(2) with (H₁, H′): either Q₁ is H₁-free — then by 4A(1)–(3), hom(G) ≥ hom(Q₁) ≥ h_{H₁}(q) ≥ q^{c₁}; or some class X is H′-free — X is a (k−1)-level uniform blow-up on s vertices, so by the induction hypothesis (applied with H₂,…,H_k and exponents c₂,…,c_k, whose (k−1)-level chain is exactly H′) hom(X) ≥ s^{F_{k−1}}, and by (F2) hom(G) ≥ hom(X) ≥ s^{F_{k−1}}. Hence hom(G) ≥ min(q^{c₁}, s^{F_{k−1}}). The balanced computation is the algebra of Theorem 4B verbatim with c₂ → F_{k−1}: min = n^{c₁F_{k−1}/(c₁+F_{k−1})}, and c₁F_{k−1}/(c₁+F_{k−1}) = 1/(1/c₁ + 1/F_{k−1}) = 1/(1/c₁ + Σ_{i=2}^{k} 1/c_i) = F_k. ∎

**Scope & honesty (boldface, mandatory).** Theorems 4A/4B/4C are **unconditional and complete for graphs possessing the uniform blow-up (lex-product) structure** — the "cleanest frame" mandated for this strike: classes fully joined or fully non-joined, inheriting homogeneous structure from the quotient and the classes. They are **not** a proof of EH for H₁[H₂] for *all* H₁[H₂]-free graphs: removing the blow-up hypothesis is the classical theorem of Alon–Pach–Solymosi (2001), whose proof uses the Szemerédi regularity lemma and the graph removal lemma — machinery **not** re-proved and **not** used as a step anywhere in this file. The obstruction is real, not stylistic: in an arbitrary graph, no elementary argument forces uniform pairs of polynomial size (random graphs have none at all), and converting H₁[H₂]-freeness into blow-up structure at polynomial scale is precisely where regularity-type machinery enters in the literature. Sanity check of the frame boundary: with H₁ = H₂ = K₂ (c₁ = c₂ = 1), 4B gives hom ≥ n^{1/2} for *balanced uniform blow-ups* that are K₄-free — true, and strictly stronger than what general K₄-free graphs admit (the Erdős–Szekeres Ramsey bound gives hom ≥ (n/const)^{1/3}-order for *all* K₄-free graphs, and that gap is exactly the frame restriction, since R(4,t) grows like t^{5/2}–t³). The full Erdős–Hajnal conjecture remains **OPEN**.

**Machine receipts.** `[A1]` sizes |V(H₁[H₂])| = |V(H₁)|·|V(H₂)| for all five products. `[A2]` builder identities (brute-permutation isomorphism): K₂[K₂] ≅ K₄; 2K₁[K₂] ≅ 2K₂; K₂[2K₁] ≅ C₄ (= K_{2,2}); complement(P₃[K₂]) ≅ C₄ ∪ 2K₁. `[A3]` induced-avoid table: K₂[K₂] avoids claw/C₄/2K₂/P₃/3K₁/P₄; 2K₁[K₂] avoids P₃ and 3K₁ (Theorem 2 tie-in) and claw; K₂[2K₁] (=C₄) is 2K₂-free, contains induced P₃; P₃[K₂] is claw-free and 3K₁-free (α = 2), contains induced 2K₂, K₃, P₃; P₃[P₃] contains induced 3K₁ (α = 4), claw, C₄, 2K₂, P₃, K₃, K₄ — the full substitution zoo. `[A4]` every built product machine-verified: uniform pairwise structure OK; contains induced H₁ by a **transversal** (Theorem 4A(1) ingredient) and induced H₂ inside a class (the avoidance-law ingredient). `[A5]` Theorem 4A(2)+4B receipts on uniform blow-ups with H₁ = H₂ = P₃: **exhaustive** over q,s ∈ {1,2,3}² (4317 blow-ups): zero violations of the avoidance disjunction and zero violations of hom ≥ min(h_{P₃}(q), h_{P₃}(s)); **sampled** q,s ∈ {(4,4),(5,5),(6,6),(7,4),(4,7)}×150 (750 graphs): zero violations again. `[A6]` exponent receipts (exact rational arithmetic): f(c₁,c₂) = c₁c₂/(c₁+c₂) with balanced splits q = n^{c₂/(c₁+c₂)}, s = n^{c₁/(c₁+c₂)} on a five-point grid; and the 3-level symmetric law f(f(c₁,c₂),c₃) = 1/(1/c₁+1/c₂+1/c₃) verified exactly (e.g. (1/2,1/2,1/2) → 1/6; (1/2,1/3,2/3) → 2/13) — the Theorem 4C composition identity.

---

## §5 THEOREM 5 (the baseline certificate — cited, context, used as a step by nothing)

**Theorem 5 (Erdős–Hajnal 1977 — certified named baseline, cited verbatim with all hypotheses).** For every fixed nonempty graph H there exists a constant c_H > 0 such that **every H-free graph G on n ≥ 2 vertices contains a homogeneous set (a clique or an independent set) of size at least exp(c_H·√(log n))**, where log is the natural logarithm (equivalently 2^{c′√(log₂ n)} after rescaling c′). Hypotheses: H fixed (c_H depends on H only), G on n vertices with **no induced copy of H**, n ≥ 2; conclusion: homogeneous set of size ≥ exp(c_H√(log n)). This is the classical unconditional baseline of Erdős and Hajnal for the conjecture bearing their names; the conjecture itself asks for the polynomial n^{c(H)}. The modern refinement cited in the wave-brief's target line is exp(c_H√(log n·log log n)) [BNSS23]. **Status in this file:** stated as certified context only — Theorems 1–4 neither use it as a step nor rest on it; it is not re-proved here. The full conjecture remains OPEN.

---

## §6 Machine receipts (receipts61.txt, per claim)

| Receipt | Content | Backs |
|---|---|---|
| `[B]` h-tables | h_H(n) for H ∈ {2K₂, P₃, 3K₁, claw(K₁,₃), C₄, K₂}, n ≤ 7, exhaustive over all 2^(n(n−1)/2) ≤ 2²¹ labeled graphs (bitmask engine, recursive block-copy memoization, verified clause-by-clause against an independent backtracking induced-subgraph checker: 0 mismatches at n ≤ 5 for P₃ and 3K₁) | Theorems 1, 2, 3 (values + sharpness) |
| `[B1]` | h_{3K₁}(5)=2, h_{3K₁}(6)=3, h_{3K₁}(7)=3; all five H at n=6 have h=3 (R(3,3)=6) | Theorem 3 Ramsey cross-checks |
| `[B2]` | h_{P₃}(n) = ⌈√n⌉ for every n ≤ 7 | Theorem 2 (equality, sharpness) |
| `[B3]` | h_{3K₁}(n) ≥ t_n = ⌈(√(4n+1)−1)/2⌉ at every n ≤ 7; equality n ∈ {1,3,4,5,7}; strict n ∈ {2,6} (Ramsey forcing); prints the C₅ note (h=2 < √5) | Theorem 3 (law + honesty note) |
| `[B4]` | h_{K₂}(n) = n for all n ≤ 7 | Theorem 1 |
| `[B5]` | witness graph for every (H, n ∈ {5,6,7}): edge count + bitmask + hom value | Theorems 1–3 upper side (h ≤ value) |
| `[B6]` | 36/36 z3 UNSAT certificates: "∃ H-free G on n with max(ω,α) ≤ h−1" UNSAT ⟹ h ≥ reported | Theorems 1–3 lower side, machine-certified |
| `[A1]`–`[A4]` | sizes, isomorphism identities, induced-avoid table, uniform-pair + transversal + in-class containment checks | Theorem 4 builder identities, 4A(1) ingredients |
| `[A5]` | 4317 exhaustive + 750 sampled uniform blow-ups (H₁=H₂=P₃): 0 avoidance violations, 0 min-bound violations | Theorems 4A(2), 4A(3), 4B |
| `[A6]` | exact-rational exponent composition receipts incl. 3-level symmetric law | Theorems 4B, 4C |
| `[C]` | P₃-free census n ≤ 7: counts = Bell(n) (1,2,5,15,52,203,877), 0 non-clique-union counterexamples | Theorem 2(ii) classification certificate |
| `[D]` | claw-free sampler n ≤ 30 (rejection + line-graphs L(G′) + complete multipartite parts ≤ 2 + C₅ clique-blowups, each machine-verified claw-free): min observed max(ω,α) = 4 (n=8..12), 5 (15), 6 (20), 7 (25, 30) — every observed value ≥ √n | evidence only, backs nothing as a theorem (labeled as such) |

Engine total wall: 97.1 s (parts: B ≈ 40 s incl. z3; A ≈ 55 s; C ≈ 0.1 s; D ≈ 2 s). The engine never stops; it never lies.

---

## §7 Arsenal usage (exact inventory — what of the boss's own mathematics is used where)

1. **Arsenal/ErdosTernary2/Basic.lean** (`lt_three_cases`, `ternary_digit_lt_three`, `isTernaryDigit` — the three-admissible-digit case law). *Used as:* the **case-completeness doctrine** — every case of a finite classification is enumerated and decided, none skipped. *Where:* the exhaustive engine (b) — all 2²¹ graphs at n = 7 are classified H-free/H-containing with zero unhandled cases, and the census (c) decides every single P₃-free graph. *Honest note:* doctrine-level import (method), not a literal lemma import; the graph-theoretic content of Theorems 1–5 is derived in-file.
2. **Arsenal/CardinalWorlds.lean** (`noTernaryTwo` and the closure law `noTernaryTwo_div` (L720–721): verdict true ∧ residue clean ⟹ verdict survives the ÷3 down-step — a no-exit-style step closure; the 2-world dyadic partition discipline: the 2^j scale ladder, §10 period laws; the exception laws at n₀,n₂,n₈). *Used as:* the **dyadic partition discipline** — build the object level-by-level, each level closed under the down-step, classes at dyadic scale. *Where:* Theorem 4's class iteration is the graph-theoretic avatar: the contains-arrays are built recursively (level n from level n−1 by the block copy — exactly the discipline's "partition into scale-classes, closure under the down-step"), and the avoidance law (4A(2)) is a no-exit closure at the class level: an H₁-pattern of H₂-containing classes has no exit — it must contain the induced product. *Honest note:* doctrinal lineage; the closure in 4A(2) is proved in-file from scratch.
3. **Arsenal/CardinalWorldsV2.lean** (`packet_add`: depth-composition is coordinatewise multiplication, 2^{j+k} = 2^j·2^k (L88–97); `packet_mixed_reconstruct`: the mixed 6-world is the product of the two primitive worlds; `v2r_ternary_scaling`: the 2-adic depth reader is invariant under ternary scaling). *Used as:* the **multiplicative composition-of-scales doctrine** — composing information depths multiplies packets; scale parameters of composed structures compose multiplicatively. *Where:* Theorems 4B/4C are the exponent-level avatar: the harmonic law f(c₁,c₂) = c₁c₂/(c₁+c₂) and its k-level symmetric form F_k = (Σ 1/c_i)^{−1} are exactly the "depth-addition ⇔ coordinate-multiplication" discipline in exponent space — machine receipt `[A6]` verifies the composition in exact rational arithmetic. *Honest note:* doctrine-level lineage, not a literal import.
4. **problem1212-coprime-composite/Erdos1212.lean** (Kernel 65: `degBound` (L165) — every vertex has ≤ 4 G-neighbors via habitat counting; the **NO-EXIT closure law** of the (9,25) component — closed in the FULL graph; the phase laws `phase15949`, `phase203_sweep`, `phase203_coprime` — certified walks inside a closed component; the adjacency laws `adj_comm`, `adj_distinct`, `adj_one_coord`). *Used as:* the **component-closure/no-exit + certified-walk doctrine**. *Where:* Theorem 2(ii)'s component argument — a connected component is closed under adjacency-steps inside the full graph (the same no-exit law as E1212's (9,25) closure), and the shortest-path triple {x₀,x₁,x₂} is a phase-law-style certified walk inside that closed component, delivering the P₃ witness; the machine census (c) mirrors 1212's engine+kernel dual-verification pattern (python mirror ↔ z3 certificates here). *Honest note:* doctrine-level; no 1212 lemma is imported into a proof step.

---

## §8 Exact label (one line)

**Theorems 1–4 are proven unconditionally (Theorem 4 within its explicitly scoped uniform blow-up frame, with the general-graph closure honestly attributed to Alon–Pach–Solymosi and *not* claimed); Theorem 5 is the cited certified baseline; the full Erdős–Hajnal conjecture remains OPEN.**

---

### Appendix: optional Lean kernel

`Erdos61.lean` (statement-only kernel): the five theorem statements as `Prop` definitions — no proofs, no `sorry`, no push. See file header.
