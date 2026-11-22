# WORKLOG W82-61A — OFFICIAL #61 KILL A: the family floor (official form) + the erha89 hunt

TASK ID: W82-61A | LANE: problem61 | WORKTREE: /home/z/waves/w82-61a | BRANCH: w82-61a
Kernel file: `problem61-erdos-hajnal/DM61_Proof_A.lean` over the OFFICIAL predicate
(vendored verbatim in `DM61_Official.lean`).

## 0. THE TARGETS (from DM61_Official.lean, byte-verified vs DeepMind @ 2207c54d)

FLOOR (guaranteed green): `erdos_61_family` — every H in
{K1, K2, K̄2, P3, P̄3, K3, K̄3, P4} admits ∃ c > 0,
`IsErdosHajnalLowerBound H (fun n => (n:ℝ)^c)`.

STRETCH (primary hunt): `erdos_61.variants.erha89` — ∀ H, ∃ c > 0,
`IsErdosHajnalLowerBound H (fun n => exp (c * sqrt (log n)))`.

## 1. ROUTE DECISION (after reading Erdos61.lean, DM61_Official.lean, Mathlib v4.33.0-rc2)

- The campaign's banked family kernel (Erdos61.lean) is over `adj : α → α → Bool`
  list-greedy (`closedNbhd_greedy`, `k3_bound`, `p3_bound`) — the SGraph carrier.
- DECISION: **DIRECT re-proof over SimpleGraph** for the floor. Reasons:
  (a) the official predicate is comap-based over `SimpleGraph (Fin n)`, so
      comap-copy lemmas are needed regardless (bridge or direct);
  (b) Mathlib v4.33.0-rc2 has the full `cliqueNum`/`indepNum` API
      (`IsClique.card_le_cliqueNum`, `IsIndepSet.card_le_indepNum`,
      `cliqueNum_compl`, `indepNum_compl`, `isIndepSet_neighborSet_of_triangleFree`,
      `CliqueFree`), verified against the pinned commit 51e6992e;
  (c) the floor laws are short dichotomies (below), each < the bridge plumbing.
- Complement transfer at the OFFICIAL level: `(G.comap g)ᶜ = Gᶜ.comap g` for
  embeddings g (needs injectivity), so `IsErdosHajnalLowerBound H f ↔
  IsErdosHajnalLowerBound Hᶜ f` — halves the family: prove K2, K3, P3, P4
  directly; K̄2, K̄3, P̄3 by transfer.

## 2. FLOOR DERIVATION (complete, to be formalized)

All over G : SimpleGraph (Fin n), official H-freeness = ¬∃ g : α ↪ Fin n, H = G.comap g.
Copy lemmas (comap + fin_cases) convert official freeness to local form:
- K1-free (Fin 1, ⊥): any embedding gives a copy (subsingleton) ⟹ n = 0 ⟹ bound 0 ≤ 0.
- K2-free (Fin 2, ⊤): any edge gives a copy ⟹ G edgeless ⟹ univ independent, α ≥ n.
- K3-free (Fin 3, ⊤): 3 distinct pairwise-adjacent give a copy ⟹ `G.CliqueFree 3`.
- P3-free (pathGraph 3): a—b, b—c edges + a—c non-edge give a copy.
- P4-free (pathGraph 4): induced P4 (a,b,c,d) gives a copy.

THE GREEDY CORE (shared engine, over SimpleGraph): if every closed neighborhood
has ≤ D vertices (D ≥ 1) then `indepNum * D ≥ card α`. Proof: strong induction on
card α; pick v₀, rem := univ \ N[v₀]; the induced graph on rem inherits the degree
bound (neighborhoods only shrink); α(G) ≥ 1 + α(G[rem]) via {v₀} ⊔ lifted
independent set (rem is anticomplete to v₀ by construction); conclude
α·D ≥ (1 + α')·D ≥ |N[v₀]| + (n − |N[v₀]|) = n.

K3 LAW: triangle-free G, D := Nat.sqrt n. If some deg(v) ≥ D: N(v) is independent
(`isIndepSet_neighborSet_of_triangleFree`), α ≥ D. Else all closed degrees ≤ D:
greedy core gives α·D ≥ n ≥ D² (since D² ≤ n) ⟹ α ≥ D. Either way
max(α, ω) ≥ D = ⌊√n⌋ ≥ n^(1/4) for n ≥ 4 (⌊√n⌋⁴ ≥ n for ⌊√n⌋ ≥ 2).

P3 LAW: P3-free G, D := Nat.sqrt n. If some |N[v]| ≥ D: N[v] is a clique (any
non-edge u—w inside N(v) completes an induced P3 u—v—w), ω ≥ D. Else greedy core,
α ≥ D. Same finish.

P4 LAW (Seinsche + product): P4-free G, n ≥ 2 ⟹ G or Gᶜ disconnected:
minimal-counterexample induction on n. n = 2: connected ⟹ the two adjacent ⟹
complement edgeless ⟹ disconnected. n ≥ 3: pick u; G−u is P4-free with n−1 ≥ 2
vertices; minimality ⟹ G−u disc ∨ (G−u)ᶜ disc; a MASTER analysis (applied to G
in the first case and to Gᶜ, which is also P4-free since P4ᶜ ≅ P4, in the second)
derives a contradiction from: G conn, Gᶜ conn, u's adjacency vs the components
Dᵢ of the deleted-complement: u uniform on classes ⟹ a Gᶜ-separation {u}∪(u's
non-neighbors) vs (u's neighbors) ⟹ Gᶜ disc; u mixed into a class ⟹ complement-
path switch gives a,b with (a—b non-edge, u—a edge, u—b non-edge), then either an
x outside the class non-adjacent to u ⟹ induced P4 (b,x,a,u) ⟹ contradiction, or
u adjacent to all other classes ⟹ the Gᶜ-separation {u} ∪ class(a) vs rest ⟹
Gᶜ disc ⟹ contradiction.
Then: αω ≥ n by strong induction via the reachability-class separation of G or
Gᶜ (union side: α ≥ Σαᵢ, ω ≥ max ωᵢ; join side: ω ≥ Σωᵢ, α ≥ max αᵢ; either way
αω ≥ Σ αᵢωᵢ ≥ Σ nᵢ = n), and max(α,ω) ≥ √n ≥ n^(1/4) for n ≥ 4.

REAL FINISH: uniform c = 1/4 for the √n-family; c = 1/5-slack or c = 1/6 for the
K5/E5 Ramsey lifts (R(5,t) ≤ C(t+3,4) ≤ (t+4)⁴/24 ladder) if smooth.
Eventually-filter: `eventually_atTop` with N = 4 (or the K5 threshold).

## 3. ARSENAL BRIDGE (read-before-cite)

`import Arsenal.ErdosTernary2.Basic` + `import Arsenal.CardinalWorlds`; cite
≥2 arsenal laws by file:line (the Erdos61.lean kernel pattern:
`CardinalWorlds.two_pow_pos`; exact lines to be recorded at proof time).

## 4. THE STRETCH (erha89) — derivation state (honest, evolving)

Classical reference: Erdős–Hajnal, Ramsey-type theorems, Discrete Appl. Math.
25 (1989) 37–52. The target: ∀H ∃c>0: H-free G on n vertices ⟹
max(α,ω) ≥ exp(c√log n) eventually.

Engines derived so far (validated by hand; census to follow):
- (E1) u universal in H ⟹ ∀v: N_G(v) is (H−u)-free (an (H−u)-copy in N(v)
  completes with v to an induced H).
- (E2) w isolated in H ⟹ ∀v: the non-neighbors of v are (H−w)-free (dual).
- (E3) H = H₁⊔H₂ disconnected ⟹ every (H₁-copy, H₂-copy) pair has a cross edge
  (else the union is an induced H).
- (E4) heredity: induced subgraphs of H-free graphs are H-free.
- EASY CASES: H with a universal or isolated vertex: degree dichotomy at
  n^{1/2}: some deg(v) ≥ √n ⟹ recurse in N(v) (E1/E2, |H| decreases,
  hom ≥ exp(c(H−u)·√(log √n)) = exp((c(H−u)/√2)·√log n)); or all degrees < √n
  ⟹ greedy α ≥ √n/2 (≫ exp(c√log n)). The induction closes at
  c(H) = c(H−u)/√2.
- HARD CASE: H connected and co-connected (no universal, no isolated; then
  |H| ≥ 4 and H ⊇ induced P4). G P4-free ⟹ Seinsche ⟹ hom ≥ √n (banked
  floor!). G ⊇ induced P4: the classical engine (neighborhood pattern
  completion) — DERIVATION IN PROGRESS; the neighborhood engine inventory is
  exactly {F : H−x ⊆_ind F for universal/isolated x} = ∅ in the hard case, so
  the mechanism must be multi-vertex (mixed pairs / maximal copy families).
  Full derivation + census before any Lean.

## 5. LOG

- W82 t0: worktree created; brief + DM61_Official.lean + Erdos61.lean read;
  Mathlib v4.33.0-rc2 API verified against pinned commit 51e6992e (Clique.lean:
  cliqueNum/indepNum/compl lemmas present). Route decision: DIRECT over
  SimpleGraph. This worklog committed (milestone 1).

## 6. COMMANDER-ABSORBED KERNEL (W82-61A, main-thread)

The finisher agent died posthumous after the campaign merge (b963ce9). The
commander wrote DM61_Proof_A.lean directly from §2's complete derivation:
- §0 the official predicate VERBATIM (byte-matches DM61_Official.lean);
- §1 builders: emb2/emb3 (fin_cases + Matrix.cons_val simp), top_comap_of_pairwise
  (ext + comap_adj + top_adj), pathGraph3_comap (the 9-case grid over
  SimpleGraph.pathGraph_adj);
- §2 the no-copy ladder: cliqueFree3_of_no_induced (Finset.orderIsoOfFin),
  no_edge_of_no_induced_K2, closedNbhd_clique_of_no_induced_P3;
- §3 the greedy core: maximal independent set via Finset.exists_max_image,
  Turán-style domination (univ ⊆ s ∪ ΣN(w)), NO induction;
- §4 the arithmetic: le_sqrt_pow_four (n < (s+1)² ≤ (s·s)² via Nat.mul_le_mul,
  s ≥ 2 from Nat.le_sqrt), rpow_quarter_le_sqrt (Real.rpow_le_rpow +
  rpow_mul + rpow_one); ARSENAL BRIDGE: arsenal_threshold from
  CardinalWorlds.two_pow_pos [:420] + two_pow_ge2 [:431] (read at their
  lines this session);
- §5 the family laws: K1 (vacuous), K2 (edgeless → α = n), K3 (the
  neighborFinset-independent dichotomy — IsNClique 3 {v,a,b} contradiction),
  P3 (closed-neighborhood clique dichotomy), Kbar2/Kbar3/Pbar3 via
  isEH_compl ((X.comap g)ᶜ = Xᶜ.comap g by injectivity + indepNum_compl);
- §6 THE BOARD: erdos_61_family — ∃ c = 1/4 > 0, all seven members in the
  OFFICIAL statement form.
HONEST SCOPE: P4 NOT claimed (the Seinsche split derivation stands in §2,
the continuation is named). erha89: the E1-E4 engine + easy-case induction
c(H) = c(H−u)/√2 derived in §4 of this worklog; the hard case
(connected + co-connected H) remains open in-frame — NOT claimed.
CI: kernel-61dm-a wired (the kernel-fc pattern + axiom-clean greps).
