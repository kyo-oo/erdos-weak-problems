# MISSION W67-61K — Erdős #61 KILLER LANE (Task ID: W67-61K)

## THE FROZEN STATEMENT (verbatim, erdosproblems.com/61)
"For any graph H is there some c=c(H)>0 such that every graph G on n vertices
that does not contain H as an induced subgraph contains either a complete graph
or independent set on ≥ n^c vertices?"
= THE ERDŐS–HAJNAL CONJECTURE (open in general).

## WORKTREE
/home/z/waves/w67-p61k (branch w67-p61k, base = campaign bcf7e9d)

## THE KERNEL TARGETS (Erdos61.lean, folder problem61-erdos-hajnal/, namespace E61)

BOSS's-maths-only lane: the FAMILY KERNEL — the complete unconditional
Erdős–Hajnal theorem for the explicit 8-graph family
F = {K1, K2, K̄2 (2 isolated vertices), P3, P̄3 (K1∪K2), K3, K̄3 (3 isolated), P4}.

**Core law (state this exact form, with ⌈⌉-safe margins):**
`E61.family_bound : ∀ H ∈ F, ∀ G, H-free(G) → max(ω(G), α(G)) ≥ ⌊√n⌋` —
or with the SAFE margin ⌊√n/2⌋ / (n:ℝ)^(1/4) form if the sharp form fights
you — the python mirror decides which is TRUE first (see 4 below).

Proof architecture (fully elementary, core-local):

1. **THE DEGREE LAW (K3-free / triangle-free)**: 
   If Δ(G) ≥ ⌊√n⌋ → some N(v) is an independent set ≥ ⌊√n⌋ (triangle-free:
   neighborhoods are independent). 
   If Δ(G) ≤ ⌊√n⌋−1 → greedy independent set ≥ n/(Δ+1) ≥ n/⌊√n⌋ ≥ ⌊√n⌋ 
   (Turán-style greedy: repeatedly take a vertex, delete its closed 
   neighborhood — each step kills ≤ Δ+1 vertices, ≥ n/(Δ+1) steps, each 
   contributing 1 to α; induction formalizable in core Lean).
   ⚠ check the boundary arithmetic — python-mirror for n ≤ 200 first; if the
   exact ⌊√n⌋ form has boundary holes, deliver the ⌊√n/2⌋-margin form and
   state c(H) = 1/4 (still polynomial!). COMPATIBILITY: n/(⌊√n⌋+1) ≥ ⌊√n⌋+1
   iff n ≥ (⌊√n⌋+1)² — false in general (holes at squares) — the mirror
   decides; the SAFE theorem: max(ω,α) ≥ ⌈√(n/4)⌉ = ⌈√n/2⌉. STATE THE SAFE ONE
   unless the mirror certifies the sharp one.
   - Complement form: K̄3-free → complement is K3-free-ish → same law for ω.

2. **THE CLUSTER LAW (P3-free)**: P3-free graphs are disjoint unions of cliques
   (prove the decomposition: no path of length 2 → every component is a clique).
   Then: some component ≥ ⌈n/#comp⌉... max(ω,α) ≥ ⌈√n/2⌉: if all components
   < ⌈√n/2⌉ → #components > n/⌈√n/2⌉ ≥ √n·(1−o) → α ≥ #components (one vertex
   per component is independent — no edges between components) ≥ ⌈√n/2⌉.
   If some component ≥ ⌈√n/2⌉ → ω ≥ that. 

3. **THE COGRAPH LAW (P4-free) — Seinsche's theorem route**:
   Lemma A (Seinsche 1974, prove elementarily): every P4-free graph G with
   |G| ≥ 2 is disconnected OR its complement is disconnected.
   Proof route (classical): suppose G connected and co-connected. Take a 
   maximal proper disconnecting structure... classical argument: if G is 
   connected P4-free: for any v, G−v... The clean route found in the literature:
   consider G connected, co-connected: take u,v in different complement-
   components... derive a P4 (4 vertices a-b-c-d with edges ab, bc, cd only).
   Derive it YOURSELF rigorously (z3/graph enumeration on ≤ 6 vertices can
   verify the lemma's truth: every connected co-connected graph on ≤ 6 
   vertices contains a P4 — the contrapositive census — while the Lean proof
   is your construction).
   Lemma B: G disconnected → G = G₁ ∪ G₂, both P4-free, smaller.
   Lemma C: complement disconnected → G = G₁ ∨ G₂ (join), both P4-free, smaller.
   Lemma D (the induction): α(∪) = α₁+α₂, ω(∪) = max(ω₁,ω₂);
   α(∨) = max(α₁,α₂), ω(∨) = ω₁+ω₂.
   Then strong induction: max(ω,α) ≥ ⌈√n/2⌉: in the union case
   α ≥ α₁+α₂ ≥ √n₁/2+√n₂/2 ≥ √(n₁+n₂)/2 (since √a+√b ≥ √(a+b)); join case
   symmetric via ω. Python-mirror the arithmetic identity.

4. **THE TRIVIAL FAMILY**: K̄2-free (no non-adjacent pair) → G complete → ω = n.
   K2-free → G empty → α = n. K1-free → n = 0 vacuous.

5. **THE BOARD** `E61.erdos61_board` + arsenal bridge `E61.arsenal_bridge`
   (Arsenal-only imports) + receipts.

## Graph representation in Lean (core-local — Mathlib's SimpleGraph is 
## available transitively but BOSS's law prefers self-built): simplest sound
## route: `def Graph := Finset (Fin n) × (Fin n → Fin n → Bool)`-style or an
## adjacency-function graph `def AdjG (n) := Fin n → Fin n → Bool` with
## symmetry/irreflexivity hypotheses, or use Mathlib's SimpleGraph transitively
## (it IS available via Arsenal imports — the campaign has used both; check
## problem274-coset-tilings or problem677 for graph-adjacent exemplars).
## Choose the representation that makes the inductions cleanest; state
## everything with explicit finite types.

## CAMPAIGN LAWS (absolute — same as all kernels)
- Arsenal imports only (import Arsenal.ErdosTernary2.Basic / CardinalWorlds /
  CardinalWorldsV2), zero sorry/admit/native_decide, axioms within
  [propext, Classical.choice, Quot.sound], NO decide on ∀ k < N, N > 501.
- NO local Lean. CI-only. Author blind.
- Python mirror FIRST: engine61/mirror61.py — brute-force ALL graphs on 
  n ≤ 6 vertices (there are 2^15 of them at n=6 — enumerate via bitmasks over
  pairs): verify every P4-free graph has max(ω,α) ≥ ⌈√n/2⌉ (and test if
  ⌊√n⌋ holds — decide the sharp-vs-safe question); same for P3-free, K3-free,
  K̄3-free, 2K̄1-free...; verify Seinsche's lemma census (every connected
  co-connected graph on ≤ 6 vertices has a P4); verify the complement laws.
  DUAL METHOD: two independent graph engines (bitmask + adjacency-list).
- Receipts: GREEN markers + #print axioms per board theorem.

## CI MECHANICS
- Folder problem61-erdos-hajnal/ + Erdos61.lean + engine61/ + COMPLETE_PROOF.md.
- kills.yml (YOUR worktree): add `- problem61-erdos-hajnal/**` to paths; add
  NEW JOB kernel-61k (elan v4.33.0-rc2 + lake update + lake exe cache get +
  the three Arsenal lake builds + `lake env lean problem61-erdos-hajnal/Erdos61.lean
  2>&1 | tee kernel61k.log` + the guard greps + receipt greps:
  `grep -F "E61_FAMILY_GREEN"` + `grep -E "E61.(family_bound|cograph_law|cluster_law|degree_law|erdos61_board)' (does not depend on any axioms|depends on axioms)"`).
- Push branch w67-p61k (token in skill-bag). Poll CI; ≤ 5 repair rounds.
- Exemplar: problem348-redundant-complete/Erdos348.lean + kills.yml kernel54.

## SUCCESS = CI-green kernel with the family theorem + all 4 law-families
## certified, receipts green, pushed, COMPLETE_PROOF.md with §1 verbatim
## statement + HONEST SCOPE (the family F covered with explicit c(H); the
## general conjecture + the remaining 4-vertex H (2K2, C4, K1,3, K4, K̄4,
## paw...) and beyond remain open — list them).
## English only. Report: theorem list, CI verdict URL, honest scope.
