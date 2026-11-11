# P203 — Erdős #203: Sierpiński 2·3-smooth — FULL PROOF CAMPAIGN

**Agent:** W2-P203. **Target:** ∃ m, (m,6)=1, such that 2^k·3^ℓ·m+1 is composite
for ALL k,ℓ ≥ 0. Witness m ⇒ unconditional YES (the FULL problem).

## §0. SUCCESS CONTRACT

COMPLETE = explicit m + finite covering certificate: primes q₁..q_r, and for each
a congruence class (a coset of Λ_{q_i} = {(k,ℓ): 2^k3^ℓ ≡ 1 mod q_i}) such that
(a) the cosets cover ℤ² (hence ℤ²≥0), each certified by the partition-tree
certificate (recursive splits, each step machine-checkable, no enumeration of an
astronomical torus), (b) m from CRT: m ≡ −(2^k3^ℓ)^{−1} mod q_i on the coset,
(m,6)=1, m > max q_i. Then every 2^k3^ℓm+1 is divisible by some q_i < m·2^k3^ℓ+1.

## §1. THE REDUCTION (linear-congruence form)

For prime q ≥ 5: ⟨2,3⟩_q ≤ 𝔽_q^*, h_q := |⟨2,3⟩_q|. The map φ_q: ℤ²→ℤ/h_q,
φ_q(k,ℓ) = Uk+Vℓ mod h_q (U = dlog of 2, V = dlog of 3 in ⟨2,3⟩_q ≅ ℤ/h_q) is
surjective, ker φ_q = Λ_q. For (m,q)=1:
  q | m·2^k3^ℓ+1 ⟺ 2^k3^ℓ ≡ −m^{−1} ⟺ φ_q(k,ℓ) = W_q,
where W_q is determined by m mod q (free choice: bijection cosets ↔ residues
m ∈ −(⟨2,3⟩_q)^{−1}). So: **the problem = cover ℤ² by one coset of Λ_q per
prime q, cosets chosen freely; then CRT gives m.** Budget: Σ 1/h_q ≥ 1 necessary.

## §2. THE COVERING TREE ENGINE (the assembly)

Region = coset c+Λ (lattice Λ, index D). Prime q acts on it:
φ_q(Λ) = ⟨g₁,g₂⟩ ≤ ℤ/h_q, m_q := |φ_q(Λ)| = h_q/gcd(h_q,g₁,g₂).
- m_q = 1 (Λ ⊆ Λ_q): q absorbs the region (choose W_q := φ_q(c)) — happens
  iff q | 2^a3^b−1 for both generators (a,b) of Λ.
- m_q ≥ 2: q splits: cylinder ∩ region = ONE coset of Λ∩Λ_q (1/m_q of region
  covered), residual = m_q−1 coset children.
The tree closes ⇒ covering. Each prime used once (W_q global). Budget
Σ_used 1/h ≥ 1 necessary (cylinder densities).

## §3. STATUS

- [x] BRIEF read; problem folder read (hunt203.py: flat-torus annealing — dies:
      torus M×N ≥ 3960×7920 with budget 0.81 < 1 — the flat lane is dead,
      confirmed by analysis; the tree lane is the attack).
- [ ] Census: palette of gems (p, h, U, V) + grid-absorber table
      (a,b) → primes of gcd(2^a−1, 3^b−1).
- [ ] Tree search: splits + absorptions → closed tree.
- [ ] CRT → m; verification (tree certificate + independent brute checks).
- [ ] PROOF.md final write-up.

## §4. RESULTS

(to be filled)

## §5. THE S043 TREE-ENGINE ROUND (palette + first DFS)

**THE PALETTE (engine203_tree.py, computed):** 1003 primes q ≤ 3·10⁵ with
h_q = lcm(ord_q 2, ord_q 3) ≤ 5000 — **density budget Σ 1/h_q = 2.1444 ≥ 1**
(the flat-lane 0.81 verdict is REVERSED: the palette was too small).
Top rows: (5,4), (7,6), (11,10), (23,11), (13,12), (17,16), (19,18),
(47,23), (29,28), (31,30), (71,35), (37,36), (73,36), (41,40), (43,42),
(431,43), (97,48), (53,52)… — dlogs (U,V) computed for the working set
(generator of S_h via primitive-root powering; palette203.txt + dlog builder
in engine203_search.py). Lattice algebra: kernel_lattice (Smith-form 2×2),
bfs_reps (coset representatives), split_region (Λ′ = Λ ∩ Λ_q), free
re-absorption by used primes' cosets — all implemented and exercised.

**THE FIRST DFS (greedy, negative — the structural lesson):** min-m greedy
splitting with 975 primes: STUCK — all primes consumed, frontier 745,118
regions, density 0.7076 (capacity left 1.58 in unspent coset density).
Zero absorption events: min-m splitting creates misaligned children.
**LAW (the alignment deficit):** a covering needs Λ ∩ Λ_q ⊆ Λ_{q′}
chain-alignment (the 1D covering-system pattern: nested moduli 2, 4, 8…),
not density alone; random-transverse cosets cap at 1 − e^{−Σ1/h} ≈ 0.88
coverage — the tree must PLAN lattice chains (top-down Λ-chain design:
each split's children must land inside earlier/deeper cosets).
The palette (budget 2.14, all machinery green) is BANKED — the
chain-planning search is the next round's strike design.

## §6. THE ROUND-4 DESIGN — THE CHAIN-PLANNING SEARCH (from the alignment law)

The greedy's zero-absorption verdict forces the structured route:

1. **THE CONTAINMENT MATRIX**: over the palette, compute all pairs
   (q, q′) with Λ_q ⊆ Λ_{q′} (a child of a q-split is absorbable by q′
   iff its lattice Λ_q sits inside a single Λ_{q′}-coset ⟸ Λ_q ⊆ Λ_{q′}).
   Test: the basis vectors of Λ_q must satisfy 2^k3^ℓ ≡ 1 mod q′ (the
   basis images vanish). NOT implied by h-divisibility alone (the
   (k,ℓ)=(0,3) witness kills Λ_13 ⊆ Λ_5 despite 4 | 12) — the matrix is
   genuine geometry.
2. **THE CHAIN DAG**: containment edges q → q′ (lattice inclusion);
   absorption depth of a region = its ready-absorber count along the DAG.
3. **THE PLANNER**: split choices ranked by the children's absorption
   depth (children landing deep in the DAG close fast); the budget prune
   stays (frontier density ≤ unspent capacity).
4. **The grid anchor**: primes with (ord_q 2, ord_q 3) = (a, b) have
   Λ_q ⊇ aℤ×bℤ — the (a,b)-shaped splits produce grid-like children that
   the (a′|a, b′|b)-primes can absorb — the 2D nested-moduli pattern
   (the 1D Sierpiński spine 2→4→8→… generalized to the (a,b)-grid).

## §7. THE CONTAINMENT MATRIX (computed, S043 close)

391 palette primes (top-400 with dlogs): **36 containment edges, max
out-degree 1** — single-step lattice chains Λ_q ⊆ Λ_{q′} barely exist
(the geometry warning confirmed: h-divisibility does NOT imply
containment). **THE MULTI-STEP LAW:** absorption in a 2D covering tree
lives at DEEP intersections — Λ_deep = Λ_{q1} ∩ Λ_{q2} ∩ … ⊆ Λ_{q′} —
the joint-kernel forces q′ (CRT-style: all q_i | 2^k3^ℓ−1 ⟹ q′ | it).
THE ROUND-4 SEARCH REFINEMENT: look-ahead-guided DFS — rank split
candidates by the count of siblings with IMMEDIATE absorbers (for each
(region, q, q″): Λ ∩ Λ_q ⊆ Λ_{q″} on the basis vectors — cheap, already
implemented as the m=1 act_on_region check). containment203.txt banked.
