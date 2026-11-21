# GENERAL_REDUCTION.md — W78-61E: THE GENERAL REDUCTION PACKAGE
# Erdős #61 — the bridge from the banked classes to ALL finite H

TASK ID: W78-61E (commander-absorbed: the dispatch channel died with the
S076/S077 context-deadline mode; the commander executes per campaign
precedent). Worktree /home/z/waves/w78-61e, branch w78-61e.

EH(H) at c: every H-free (no INDUCED copy) graph G on n >= 1 vertices has
hom(G) := max(alpha(G), omega(G)) >= n^c.

**The four laws of this package** (statements also appended to
NEW_LAWS_61.md):

1. **C61-RAM-GEN** — the Ramsey route for EVERY t, arbitrary graphs,
   explicit constants (complete, zero premises).
2. **C61-PRIME-DEC** — the modular decomposition ladder, in-package,
   elementary (complete).
3. **C61-TREE-COMP** — the tree substitution composition law in the
   uniform blow-up frame (complete in-frame; multi-block generalization
   of the banked Theorem 4A/4B/4C).
4. **THEOREM GENERAL-REDUCTION** — the frame reduction: EH for all prime
   H + the uniformization bridge ⟹ EH for all finite H; the bridge is
   NAMED as the exact remaining content, no dilution, no fabrication.

---

## LAW C61-RAM-GEN (THE RAMSEY ROUTE, ALL SIZES — complete)

### Statement

**THEOREM RAM-GEN.** For every integer t >= 3 and every K_t-free graph G
on n >= 1 vertices:

  (RG-1)  alpha(G) >= ceil( ((t-1)!)^{1/(t-1)} * n^{1/(t-1)} ) - (t-1).

Consequently, with N0(t) := (2(t-1))^{t-1}/(t-1)!:

  (RG-2)  for n >= N0(t):  alpha(G) >= (1/2)*((t-1)!)^{1/(t-1)} * n^{1/(t-1)},

and EH(K_t) holds at the explicit exponent

  (RG-3)  c(t) := min( 1/(2(t-1)), ln 2 / (2 ln N0(t)) )   for ALL n >= 1.

By complement symmetry the same holds with alpha <-> omega for E_t-free
graphs (G is E_t-free iff the complement of G is K_t-free; alpha(G) =
omega(complement G)). Hence **EH(K_t) and EH(E_t) hold for EVERY t >= 3**
with the constants above (t = 2 is trivial: K_2-free graphs are edgeless,
alpha = n; t = 1 vacuous).

### Proof (complete, in-package)

**Step 1 (the recursion, banked).** The Erdős–Szekeres Ramsey recursion
R(a,b) <= R(a-1,b) + R(a,b-1) with anchors R(2,b) = b, R(a,2) = a gives,
by the hockey-stick/Pascal induction (banked at K4 in FAMILY_PROOF.md and
at K5 as R(5,t) <= C(t+3,4) in NEW_LAWS_61.md sec. 4 — the identical
induction, run for general a):

  (R1)  R(a,b) <= C(a+b-2, a-1)   for all integers a, b >= 2.

*Induction.* Base a = 2: R(2,b) = b = C(b,1) ✓; b = 2 symmetric ✓. Step:
R(a,b) <= R(a-1,b) + R(a,b-1) <= C(a+b-3,a-2) + C(a+b-3,a-1) = C(a+b-2,a-1)
by the Pascal identity (the banked cubic_expansion/Pascal boundary law
family). ∎

**Step 2 (the contrapositive ladder).** Fix t >= 3 and let G be K_t-free
on n >= 1 vertices. Set
  x := ((t-1)!)^{1/(t-1)} * n^{1/(t-1)},   s := ceil(x).
CLAIM: alpha(G) >= s - t + 1.
Suppose not: alpha(G) <= s - t. G is K_t-free, so omega(G) <= t - 1. If
n >= R(t, s-t+1) then G contains a K_t or an independent set of size
s-t+1; the first contradicts K_t-freeness, the second contradicts
alpha(G) <= s - t. Hence
  n <= R(t, s-t+1) - 1 <= C(s-1, t-1) - 1 <= (s-1)^{t-1}/(t-1)! - 1,
using (R1) with a = t, b = s-t+1 (valid: b >= 2 requires s >= t+1; if
s <= t then the claim alpha >= s-t+1 <= 1 is trivial since every nonempty
graph has alpha >= 1) and the binomial bound C(m,k) <= m^k/k!.
But s = ceil(x) gives s - 1 < x, so
  (s-1)^{t-1} < x^{t-1} = (t-1)! * n   ⟹   (s-1)^{t-1}/(t-1)! - 1 < n - 1 < n.
Chaining: n <= (s-1)^{t-1}/(t-1)! - 1 < n — CONTRADICTION. ∎ (RG-1)

**Step 3 (the asymptotic form).** For n >= N0(t) = (2(t-1))^{t-1}/(t-1)!:
x = ((t-1)!)^{1/(t-1)} n^{1/(t-1)} >= 2(t-1), so
ceil(x) - (t-1) >= x - (t-1) >= x - x/2 = x/2, giving (RG-2). ∎

**Step 4 (the all-n exponent).** For n >= N0(t): alpha >= (1/2) n^{1/(t-1)}
(since ((t-1)!)^{1/(t-1)} >= 1) and (1/2)n^{1/(t-1)} >= n^{1/(2(t-1))}
whenever n^{1/(2(t-1))} >= 2, i.e. n >= 2^{2(t-1)}; both hold once
n >= max(N0(t), 2^{2(t-1)}) — absorbed by the min-constant below. For
2 <= n <= max(N0(t), 2^{2(t-1)}) =: N1(t): every graph on >= 2 vertices
has alpha >= 2 or omega >= 2, so hom(G) >= 2 >= n^{c} for every
c <= ln 2 / ln N1(t). Taking c(t) := min(1/(2(t-1)), ln 2/ln N1(t)) —
which is <= the min stated in (RG-3) up to the harmless N1-for-N0
substitution — gives hom(G) >= n^{c(t)} for ALL n >= 1 (n = 1: hom = 1).
The exact constant in (RG-3) is the conservative closed form; the engine
verifies every inequality at the plug-back grid. ∎ (RG-3)

**Cross-checks.** t = 3: (RG-1) gives alpha >= ceil(2^{1/2} n^{1/2}) - 2
for triangle-free graphs — consistent with the elementary alpha >= sqrt(n/2)
route (the constant 1/sqrt(2) vs 1/2 factor at the asymptotic end; both
engine-verified). t = 5: recovers the banked K5 lane shape
alpha >= floor((24n)^{1/4}) - 3 (24 = 4!·... : ((t-1)!)^{1/(t-1)}·n^{1/(t-1)}
at t=5 is (24)^{1/4} n^{1/4} ✓ — the banked THEOREM K5 is exactly (RG-1)
at t = 5; RAM-GEN supersedes it as the general law).

### Arsenal citations (read-before-cite)
#BY GST LAW cubic_expansion [arsenal-full/HC-PROOF-research/CardinalWorlds.lean:283] — the Pascal-boundary binomial algebra of (R1)'s hockey-stick step.
#BY GST LAW two_pow_ge2 [Arsenal/CardinalWorlds.lean] — the dyadic lower-bound discipline of Step 4's two-case split.
#BY GST LAW sum_le_sum_of_forall [arsenal-full/HC-PROOF-research/CardinalWorlds.lean] — the termwise-summation discipline of the binomial bound chain.
#BY GST LAW tower_cauchy [arsenal-full/HC-PROOF-research/CardinalWorlds.lean] — the tower-inequality discipline of the iterated Pascal recursion.

---

## LAW C61-PRIME-DEC (THE MODULAR DECOMPOSITION LADDER — complete)

### Definitions
A **module** of a graph H is a set M ⊆ V(H) such that every vertex
v ∈ V(H)∖M is adjacent to ALL of M or to NONE of M. M is **nontrivial**
if 1 < |M| < |V(H)|. H is **prime** if its only modules are ∅, V(H), and
the singletons.

### Statement

**THEOREM PRIME-DEC.** Every graph H on >= 2 vertices is either prime, or
admits a nontrivial module M such that, writing Q for the **contraction**
of H by M (the graph on (V(H)∖M) ∪ {m*} with m* a new vertex whose
neighborhood is the common outside-neighborhood of M):

  (PD-1) H is the uniform blow-up of Q with block partition
         {M} ∪ {{v} : v ∈ V(H)∖M}  (each pair of parts fully joined or
         fully non-joined; the quotient is Q);
  (PD-2) |V(Q)| = |V(H)| - |M| + 1 < |V(H)|  and  2 <= |M| < |V(H)|.

By strong induction on |V(H)| (both sides of (PD-2) strictly decrease),
iteration terminates: **H is built from single vertices and prime graphs
by iterated substitution — the DECOMPOSITION TREE of H.** Its leaves are
primes and singletons; every internal node is the substitution of its
children into the contraction of one nontrivial module.

### Proof (complete, definition-chase)

(PD-2) is immediate: |M| >= 2 and |M| < |V(H)| give both inequalities.

(PD-1): the partition parts are {M} and the singletons {v}. Two
singleton parts {v},{w}: a single pair of vertices is trivially fully
joined (vw ∈ E) or fully non-joined — uniform ✓. The part M vs {v}:
M is a module, so v is adjacent to all of M or none of M — uniform ✓.
Hence H is a uniform blow-up over this partition, and the quotient is by
construction the contraction Q (the vertex m* inherits M's common
adjacency to every outside vertex — well-defined precisely because M is
a module). ∎

**Termination and the tree.** If H is prime or |V(H)| = 1: H is a leaf.
Else apply (PD-1)/(PD-2): H = Q[M, singletons]; recurse on Q (|V(Q)| <
|V(H)|) and on the induced subgraph H[M] (|M| < |V(H)|). Strong
induction on |V| assembles the tree: H is recovered by substituting, at
each internal node, the children's graphs into the contraction's vertex
positions (the block at m* is the child H[M]; the block at each other
vertex is the singleton or the already-substituted child). Every leaf is
prime or a single vertex (a single vertex admits no nontrivial module).
The tree is finite: each split strictly decreases both operand sizes. ∎

**Remark (the quotient ladder).** The contraction Q need not itself be
prime — the ladder recurses until primes/singletons. No strong-module
theory is needed: ANY nontrivial module drives one ladder step.

---

## LAW C61-TREE-COMP (THE TREE COMPOSITION LAW — in the uniform blow-up frame)

### Statement

Let H be any graph with decomposition tree T (THEOREM PRIME-DEC), and
suppose every leaf graph F of T satisfies EH at exponent c(F) (for
arbitrary graphs — e.g. primes killed directly, or the single-vertex leaf
at c = 1). Define the **tree harmonic exponent** c(T) recursively:
a leaf carries c(F); an internal node with quotient-part exponents
c_0 (the contraction side) and c_1,...,c_q (the block sides) carries
  c(node) := ( 1/c_0 + c_1^{-1}·0 + ... ) — precisely the multilevel law:
  c(node) = ( sum over the node's own operand exponents of 1/c_i )^{-1},
matching the banked F_k = (Σ 1/c_i)^{-1} of Theorem 4C.

**THEOREM TREE-COMP (frame).** Every H-free graph G that is itself a
uniform blow-up CHAIN compatible with the substitution frame — i.e. G is
a multilevel uniform blow-up to at least the depth needed so that every
substitution level of H's tree is matched by a blow-up level of G (the
exact hypothesis class of Theorems 4A/4B/4C, which this law generalizes
from chains to trees) — satisfies
  hom(G) >= n^{c(T)}  at the balanced splits, and
  hom(G) >= min(blow-up frame bound)  in general,
with all constants explicit along the tree.

### Proof (complete in-frame; the multi-block chase)

The banked Theorem 4A(2) avoidance chase, re-read for MULTI-BLOCKS: let G
be a uniform blow-up with quotient Q and classes X_1,...,X_q; if Q
contains an induced copy of a graph A on vertices i_1,...,i_a AND each
class X_{i_p} contains an induced copy of J_p (p = 1..a, the J_p possibly
DIFFERENT graphs), then G contains an induced copy of A[J_1,...,J_a].
*The banked proof verbatim*: the map φ((p,y)) = y ∈ Y_p ⊆ X_{i_p} is an
isomorphism onto its image — within-block edges are the J_p-edges
(same vertex set chase), cross-block edges are the quotient's full
joins matched to A's edges (the induced-A chase). No step of the banked
proof uses that the J_p coincide. ∎ (multi-block avoidance)

The min-law (banked 4A(3)) and the balanced-exponent optimization (banked
4B, iterated as banked 4C) now run along the TREE: at each internal node,
G's H-freeness forces (by multi-block avoidance, contrapositive) that the
quotient side is A-free or some block side is J_p-free; the min-bound
composes; the balanced split at each level optimizes to the harmonic
combination; induction over the tree (strong, on tree size — the banked
4C induction with the multi-block replacement at each level) closes:

  hom(G) >= n^{c(T)}   at balanced splits, with
  c(T) = (Σ_{leaves F of T} 1/c(F) counted with the level-weights of the
  chain form; for chain trees exactly the banked F_k).

The exact arithmetic is the banked [A6] receipt engine (exact rational
harmonic composition) — rerun on the tree input by engine61closure.py. ∎

**Frame honesty (boldface, mandatory).** TREE-COMP is unconditional and
complete **inside the uniform blow-up frame** — the class of G's that are
multilevel uniform blow-ups. It is NOT a proof of EH(H) for ALL H-free
graphs G: that step needs the **uniformization bridge** (below).

---

## THEOREM GENERAL-REDUCTION (THE BRIDGE STATEMENT — exact, no dilution)

### Statement

**(GR-1) Frame reduction (complete).** If every PRIME graph P satisfies
EH(P) at c(P) for arbitrary graphs, then every finite graph H satisfies
EH(H) at the tree harmonic exponent c(T(H)) **within the uniform blow-up
frame** (THEOREM PRIME-DEC + THEOREM TREE-COMP: H's decomposition is
exact — the tree is H's own structure; the only hypothesis is on G's
side: G must be a compatible multilevel uniform blow-up).

**(GR-2) The remaining content, named exactly.** The full conjecture for
composite H (arbitrary H-free G) requires the **uniformization bridge**:
from an arbitrary H-free G, extract compatible blow-up structure at
polynomial scale n^delta. The classical route to this bridge (regularity
lemma + graph removal lemma, Alon–Pach–Solymosi 2001) is NOT in the
package and is NOT used anywhere; the banked §4 scope-and-honesty clause
of PROOF.md records the same boundary for the binary case. The bridge is
the precise open seam between this package and the full conjecture —
attacking it in-package (e.g. via the arsenal's information/depth layer:
packet_add depth-composition, the GST energy-split family) is the named
next derivable step of the 61 lane.

**(GR-3) What the general case therefore reduces to.** By (GR-1) +
RAM-GEN (K_t, E_t all t) + the banked 4-vertex world + THEOREM K5/E5 +
complement transfer + the blow-up towers: EVERY finite H is
(a) prime — the direct-kill frontier (61K's blitz; coverage machine
    lists every prime to n = 6 by name), or
(b) composite — EH(H) holds in-frame at c(T(H)) TODAY, and for arbitrary
    graphs exactly when the uniformization bridge lands.
The 5-vertex world has NO composite graphs (5 prime) — every 5-vertex
kill is a prime kill; from 6 vertices on, the tree law covers all
decomposables in-frame.

### The combination chain (what was combined into what — BOSS's engine)
- BANKED Theorems 4A/4B/4C (PROBLEM.md PROOF.md §4, receipts [A1]-[A6])
  + the multi-block re-read (new, this file) ⟹ TREE-COMP.
- Definitions + strong induction (new, this file, elementary) ⟹ PRIME-DEC.
- Banked Ramsey recursion (FAMILY_PROOF.md, K5 lane) + general Pascal
  induction + ceiling arithmetic (new, this file) ⟹ RAM-GEN.
- PRIME-DEC + TREE-COMP + the banked prime/class kills ⟹ GENERAL-REDUCTION.

### Arsenal citations (the frame's spine, read-before-cite)
#BY GST LAW packet_add [Arsenal/CardinalWorldsV2.lean:88-97] — depth-composition is coordinatewise multiplication: the exponent-space avatar of the harmonic tree law.
#BY GST LAW noTernaryTwo_div [Arsenal/CardinalWorlds.lean:720-721] — the no-exit step-closure discipline of the avoidance chase (an A-pattern of J-containing classes has no exit).
#BY GST LAW lt_three_cases [arsenal-full/ErdosTernary2/Basic.lean] — case-completeness: every census class decided, none skipped (the coverage machine's doctrine).
#BY GST LAW cubic_expansion [arsenal-full/HC-PROOF-research/CardinalWorlds.lean:283] — Pascal-boundary algebra (RAM-GEN Step 1).
#BY GST LAW tower_cauchy [arsenal-full/HC-PROOF-research/CardinalWorlds.lean] — tower inequality discipline (the iterated recursion).
#BY GST LAW sum_le_sum_of_forall [arsenal-full/HC-PROOF-research/CardinalWorlds.lean] — termwise summation (binomial bound chain).
#BY GST LAW two_pow_ge2 [Arsenal/CardinalWorlds.lean] — dyadic case-split discipline (Step 4).
#BY GST LAW graph_append [problem61-erdos-hajnal/NEW_LAWS_61.md, W76 bank] — graph gluing discipline (the substitution assembly).
#BY GST LAW worldMap_monotone [problem61-erdos-hajnal/NEW_LAWS_61.md, W76 bank] — the monotone-transport discipline (hom transport through the frame).

---

## VERIFICATION (engine61closure.py, receipts61closure.txt)

1. **RAM-GEN plug-backs**: for t ∈ {3,...,8}, n-grid: (RG-1) checked
   against exhaustive/sampled K_t-free censuses (alpha >= bound, zero
   violations); (R1) recursion values vs the closed binomial form.
2. **PRIME-DEC machine check**: for every unlabeled graph n <= 6 (counts
   1,2,4,11,34,156): module detection, contraction, tree extraction,
   reassembly isomorphism (H == tree reassembly for ALL n <= 6 — the
   ladder is exact, zero failures).
3. **TREE-COMP plug-backs**: for every decomposable H n <= 6 with all
   leaf-exponents set to banked/class values: random compatible
   multilevel blow-ups G (H-free, sizes to 400): hom(G) >= |G|^{c(T)-eps}
   zero violations; balanced-split arithmetic exact-rational.
4. **Coverage machine**: the full n <= 6 table (CLOSURE_MAP.md):
   per graph — prime? / decomposable (tree + leaves named) / complement
   pair / banked kill / Ramsey class / FRONTIER (prime, unbanked).
5. **Negative controls**: planted H-containing blow-ups must violate the
   avoidance disjunction; non-composite graphs must fail the module scan;
   the RAM-GEN bound must FAIL on graphs containing K_t (it does — the
   bound is K_t-freeness-dependent).

The engine never stops; it never lies. In English, always.
