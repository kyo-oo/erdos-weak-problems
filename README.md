# ERDŐS ONE-SHOT KILLS — The Bulldoze Campaign

Standalone home of the kill campaign: **Erdős open problems weaker than the
#406 benchmark, one-shot with Kyo-oo's own mathematics** — full proofs (never
weakened statements), formalized in Lean 4, **compiled and verified on GitHub
Actions CI** against Mathlib at the pinned toolchain. Zero `sorry`. Zero
custom axioms.

Extracted verbatim from the research monorepo
`erdosternary2` @ `e39b0d6`, branch `bulldoze/erdos-weak-problems-3-20261101`.

[![CI](https://github.com/kyo-oo/erdos-weak-problems/actions/workflows/kills.yml/badge.svg)](https://github.com/kyo-oo/erdos-weak-problems/actions/workflows/kills.yml)

---

## THE KILL REGISTRY

| Kill | Erdős # | The theorem that killed it | Lean file | Axioms |
|---|---|---|---|---|
| **#1** | 406 (frontier) | **Row-two first-hit pattern frontier** — the exact ternary-pattern engine carving the hGate frontier of the anchor problem. Kernel-green, core-only. *(branch `gpt6/erdos-one-shots-20261101` @ `120ebda` in the monorepo)* | — | core |
| **#2** | 261 (walk) | **Greedy-walk equivalence theorem** — the subtract-or-double walk on n/2^n terminates ⟺ the representation exists; structure laws (waterfalls, cascade, 2-piece rigidity); frontier $10^4 \to 10^5$. *(branch `gpt6/erdos-one-shots-2-20261101` @ `4302b85` in the monorepo)* | — | — |
| **#3** | **271** | **Stanley A(2) complete characterization**: `theorem stanley_a2_greedy (m : Nat) : gp m m = inD m` — the greedy 3-AP-free sequence seeded {0,2} is EXACTLY $A(2) = \{3m + d : m \in C,\ d \in \{0,2\}\}$ with $C$ the Cantor set (no ternary digit 2). Proof engine: **Cantor top-witness induction** + offset-normalized stepping. Census $|A(2) \cap [0,3^k)| = 2^k$. | `bulldoze/problem271-stanley-a2/StanleyA2.lean` | `propext, Classical.choice, Quot.sound` |
| **#4** | **404** | **The p=2 left-factorial kernel law**: `theorem kernel_law (u k : Nat) (hk : 3 ≤ k) : v2 (sumFactFrom u k) = v2 (fact u) + v2 (u + 2)` — the exact 2-adic valuation of the tail factorial sum, ALL u, ALL k ≥ 3, via staggered K/E fuel induction on the 3-term factorization. Settles the mod-$2^k$ behavior completely. | `bulldoze/problem404-padic-kernel/KernelLaw.lean` | `propext, Quot.sound` |
| **#5** | **261 (weakened sub-question)** | **Three exact representations of x = 1/2**: `erdos261_weakened_two_solutions` + `erdos261_three_solutions` — {2} ≅ {3,6,8} ≅ {4,5,6} under $\sum 2^{8-a} = 128$ scaling; plus the sub-block collision {4,5} ≅ {3,8}. Pure `decide` computation, ZERO axioms. | `bulldoze/problem261-two-solutions/TwoSolutions.lean` | **NONE** |
| **#6** | **261 (continuum, real-x)** | **The Tower**: `theorem erdos261_continuum` — an explicit injection $\sigma \mapsto F_\sigma$ from $2^{\aleph_0}$ branches to representation-sets of a single explicit irrational $x^* = \sum m_k/2^{m_k} \approx 0.7553714812$, built on the **infinite exact-halving family** $m_k = 2^{k+2} - k - 3$ (1, 4, 11, 26, 57, 120, 247, …) whose regions satisfy $\{m_k\} \equiv \{m_k+1..m_k+k+1\}$ exactly. Answer: YES, $2^{\aleph_0}$ representations exist. | `bulldoze/problem261-continuum-tower/Erdos261Tower.lean` | `propext, Quot.sound` |

**Fully-solved complete problems: #271, #404.** The #261 family carries three
complete theorems (walk equivalence, two-solutions, real-x continuum) with the
rational-x continuum + walk-termination-all-n still open. **#406 itself is
the benchmark anchor** — its pattern frontier is killed, the core conjecture
remains the campaign's summit.

## THE WEAPONS (Kyo-oo's own mathematics)

1. **Ternary digit structure of powers of 2** — primitive-root lift, the LTE
   valuation spine $4^{3^j} = 1 + 3^{j+1} c_j$, residue-class towers.
2. **Dyadic exact-certificate machinery** — binary-origin audits, dyadic
   injectivity depth 9–22, meet-in-the-middle censuses to depth 36.
3. **The kernel/countermodel discipline** — every claim ships as a
   core-Lean kernel file, compiled by CI, receipts grepped, zero sorry.
4. **Greedy-oracle engines** — fuel-indexed Stanley oracles, walk
   equivalence maps, top-witness maximality induction.

## CI — THE ONLY VERDICT

Every kill is compiled by
[`.github/workflows/kills.yml`](.github/workflows/kills.yml):
Lean `v4.33.0-rc2` + Mathlib via elan/lake-cache, `lake env lean` per kernel,
zero-sorry gates, exact receipt greps, axiom gates, plus the independent
Python verification battery (`bulldoze/scripts/`). A kill counts ONLY when
this workflow is green on GitHub.

## NEXT FRONTS (the one-shot queue)

1. **#261 rational-x continuum** — walls mapped (fork-comb, Kakeya
   thickness-exclusivity, cluster uncancelability, telescope capacity).
2. **#261 walk termination for all n** — the endgame of the walk theorem.
3. **#260** — the sibling dyadic irrationality problem, behind the walk wall.
4. **Odd-p kernel law** — the $p \neq 2$ stagger structure (p=3 spikes at
   $u \equiv 7 \pmod 9$; p=11 twin classes; research-grade).
5. **The dyadic four** — #249 (covering-walled), #251 (prime-index noise),
   #257 (beyond Tao–Teräväinen).
