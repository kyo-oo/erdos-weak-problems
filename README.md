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
| **#7** | **404 (full problem)** | **The p-adic reduction** (Round 3): `erdos404_split` — every sum factors $a! + \sum_B i! = a!\,(1 + \sum_B P_i)$, so $f(a,p) = v_p(a!) + g(a,p)$; compactness: $g = \infty \iff$ an exact $\mathbb{Z}_p$ zero-sum $\sum_{i \in Z} i! = 0$ $\iff$ the infinite chain of sub-question 3 exists. **The $p \mid a{+}1$ class completely solved** (`erdos404_odd_a`: $f(a,2) = v_2(a!)$ for all odd $a$). **$f(4,2) = 6$ exactly** (`erdos404_f42`: witness $4!+5!+7! = 5184$, the mod-16 obstruction). Block identities $[u,u{+}1] = u!(u{+}2)$, $[u,u{+}2] = u!(u{+}2)^2$. | `problem404-full/PadicReduction.lean` | CI |
| **#8** | **261 (Q3 bridge)** | **The rational-x bridge** (Round 3): `bl_family` — the representation-family identity $\sum_{j=1}^m (n+j) 2^{m-j} = n 2^m$ for $n = 2^{m+1}-m-2$ (Borwein–Loring family, independently re-derived, formalized) + the engines `jpow_sum_eq`, `pow_sum_eq` + toggle receipts; **new theorem (DERIVATION.tex): bounded-room all-n $\Rightarrow$ a rational $x$ with $2^{\aleph_0}$ representations.** | `problem261-q3bridge/BlockIdentity.lean` | CI |
| **#9** | **404 (sub-Q3 program)** | **The gadget-supply engine**: lift law ($v_2 x = v_2 y = V \Rightarrow v_2(x{+}y) \ge V{+}1$), pair law $P_u + P_{u+1} = P_u(u{+}2)$ (ALL $u \ge 3$), triple law (perfect square), dead-end law (greedy traps at $V{=}4$), certified chain $g(2,2) \ge 23$, reachable-set DP $-1 \in R_k\ \forall k \le 24$. | `problem404-gadget-supply/GadgetSupply.lean` | `propext, Quot.sound` |
| **#10** | **261 (funnels)** | **The funnel/coalescence discovery**: the absolute walk state space $\{(N,v)\}$ carries ONE map $\varphi(N,v) = (N{+}1, 2v \bmod N)$; all walks are orbits and they COALESCE (64% die at $N{=}12231$); `death_fuel_mono` = the coalescence certificate; greedy-room census: room UNBOUNDED (max 152125 at $n{=}3817$). | `problem261-funnels/FunnelStructure.lean` | CI |
| **#11** | **404 (p=2 classification I)** | **Obstruction families T2/T3/T4**: $a \equiv 4 \pmod 8 \Rightarrow f = v_2(a!) + 3$; $a \equiv 10 \pmod{16} \Rightarrow f = v_2(a!) + 6$; $a \equiv 32/48 \pmod{64} \Rightarrow f = v_2(a!) + 6$ — for ALL $a$ in the family, uniform modular obstructions (decided leaves), explicit witnesses. | `problem404-p2-classification/ObstructionFamilies.lean` | `propext, (Classical.choice,) Quot.sound` |
| **#12** | **404 (p=2 classification II)** | **Theorem T5**: $a \equiv 8 \pmod{64} \Rightarrow f(a,2) = v_2(a!) + 6$ EXACTLY — `f404_T5_bound` + `f404_T5_exact`: vanish lemma ($128 \mid P_j$, $j \ge 8$), 7-coin mod-128 obstruction (leaf residues $\{8, 72\}$), witness $\{a{+}1, a{+}3, a{+}4, a{+}6\}$; receipts 13/76/140/203; battery 172/172. Found by the uncovered-class mining scan (7/7 members uniform, zero deep). | `problem404-p2-classification/ObstructionFamilies.lean` (§10) | `propext, Classical.choice, Quot.sound` |
| **#13** | **404 (p=2 classification III)** | **Theorems T6/T6b/T6c/T7/T7b**: $a \equiv 40, 56, 88 \pmod{128} \Rightarrow g = 7$ exactly ($f = v_2(a!) + 7$); $a \equiv 70, 118 \pmod{128} \Rightarrow g = 10$ exactly ($f = v_2(a!) + 10$) — five more infinite families, ALL $a$ in each family, KERNEL-GREEN (0 errors, 0 sorry, axioms $[\mathrm{propext}, \mathrm{Classical.choice}, \mathrm{Quot.sound}]$), receipts 45/172/300/427/60/187/92/219/77/204/332/459/123/250, memory-safe boundedForall leaf architecture (one kernel decide per leaf). | `problem404-p2-classification/ObstructionFamilies.lean` (§11–§14) | `propext, Classical.choice, Quot.sound` |
| **#14** | **404 (f(2,2) EXACT)** | **The exact value $f(2,2) = 254$**: `theorem erdos404_f22_lower : v2 (sumFacts witnessB) = 254` — the explicit 118-element witness $B \subseteq [3,254]$, Lean-proven via dvd-decides + the v2 toolkit; **the sound scheduled-precision class-DP**: $g(2,2) = 253$, first unreachable level $= 254$ — Lin's [Li76] upper bound is TIGHT, so $f(2,2) = v_2(2!) + 253 = 254$ exactly. **SESSION 020 — THE CLOSED THEOREM `erdos404_f22_exact` Lean-proven end-to-end** (commit bf0e851, **CI run 41821641176 GREEN**): $v_2(2 + \sum_{i \in B_w} i!) = 254 \wedge \forall B$ (distinct, $\ge 3$): $v_2(2 + \sum_{i\in B} i!) \le 254$ — the full §5d cover machinery (Lemma A live+capped, CoverS, cover_run) + the bridge (filter_proj_perm with NoDupF coin-distinctness, achiev_coins, coin_range_dvd) — **sole hypothesis: `obstructionCheck = true`, kernel-evaluated (receipt printed in-file), cross-validated by the C engine, the Python bitset DP, the 40/40 battery, and Lin's [Li76] published bound.** **SESSION 021 — THE HYPOTHESIS KILL: `obstructionCheck_true` is now a THEOREM (axioms `[propext, Quot.sound]`) and `erdos404_f22_final : f(2,2) = 254` carries ZERO hypotheses (axioms `[propext, Classical.choice, Quot.sound]`) — UNCONDITIONAL, kernel-certified via the 31-module §7 olean chain (`gen_f22_final.py`, all-slices + decide +kernel + show-free architecture), CI-extended to compile the full chain — **CI run 41909053106 GREEN (commit 026c98c).** The congruence chain (L1 mod-shift, L2 v2-agreement, L3 unit-congruence) Lean-proven; battery 40/40; the a-sweep exact values $g(6,2){=}129, g(16,2){=}533, g(18,2){=}45, g(24,2){=}39, g(30,2){=}100, g(38,2){=}793$ — every former "unbounded candidate" bounded; $a{=}14, 34$ alive past 1100. | `problem404-q3-chain/ExactF22.lean` | `propext, Classical.choice, Quot.sound` |
| **#15** | **404 (Theorem B, EVERY prime)** | **The $p \mid a{+}1$ class for EVERY prime**: `erdos404_theoremB (a p) (hp : 2 ≤ p) (hd : p ∣ a+1) (B) (hB) : vpad p (fact a + sumF B) = vpad p (fact a)` — the $p$-adic valuation NEVER GROWS on the whole cross-prime class; **$f(a,p) = v_p(a!)$ exactly** for every prime $p$ dividing $a{+}1$ — e.g. every $(p{-}1, p)$, and (at $p{=}2$) every odd $a$, the Kill-#7 class generalized. Primality is never used — the theorem holds for every integer $p \ge 2$ dividing $a{+}1$. Engine: the **unit-congruence law** `vpad_congr_unit` ($u \equiv 1 \bmod p \Rightarrow v_p(x \cdot u) = v_p(x)$, fuel induction, NO Euclid lemma — pure mod-arithmetic) + the $(a{+}1)$-factor staircase kill + the fuel-structural `vpadf`/`vpad` valuation with the saturation law. Receipts across $p \in \{2,3,5,11\}$; battery +150 cross-prime checks (296/296). **CI run 41950834628 GREEN (commit 5f55fdc) — Kernel 11.** | `problem404-full/TheoremBGeneral.lean` | `propext, Quot.sound` |
| **#16** | **404 (f(6,2) EXACT)** | **The exact value $f(6,2) = 133$**: `erdos404_f62_lower : v₂(6! + Σ_{i∈B₆} i!) = 133` — the explicit 61-element witness $B_6 \subseteq [7,135]$, **UNCONDITIONAL** (axioms `[propext, Quot.sound]`); the closed `erdos404_f62_exact (hob : obstructionCheck = true)`: $g(6,2) = 129$, first unreachable level $= 130$, $f(6,2) = v_2(6!) + 129 = 4 + 129 = 133$ — **sole hypothesis: the kernel-evaluated `obstructionCheck` receipt (printed in-file: `#eval obstructionCheck -- true`), cross-validated by the C class-DP engine (L=130 death run, `capped = 0`, GMP witness), the pure-Python DP twin (218/218 battery, peak 352 states, death ≤ 129, 200 random-subset soundness trials), and the a-sweep L=600 stability runs.** The full §5d cover machinery ported to anchor 6 (CP = 138, 129 coins [7,135], the 720-staircase, coin_range_dvd at the 136-cutoff, the L68-safe inductive TailSorted, the NoDupF bridge) — the second-ever exact $f(a,2)$ value; one §7-freeze olean chain away from unconditional (the Kill-#14 architecture replays at half scale). **CI run 41955350415 GREEN (commit 02e982e) — Kernel 12.** | `problem404-q3-chain/ExactF62.lean` + `verify_f62.py` | lower `propext, Quot.sound`; exact/upper `propext, Classical.choice, Quot.sound` |
| **#17** | **1108 (subset kernel + FULL CASCADE)** | **The subset kernel law + THE FULL PAIR-CASCADE LAW**: `isolated_min_v2` (bottom-pair singleton ⟹ v₂(Σ_{a∈S} a!) = v₂(b!) EXACTLY) + **`full_cascade_v2`** — for EVERY nonempty S: v₂(Σ_{a∈S} a!) = Λ(j₀) + v₂(C(S)) EXACTLY, with j₀ = botPair S the lowest occupied pair, Λ(j) = v₂((2j)!), C(S) = (Σ_{a∈S} a!)/2^{Λ(j₀)} the cascade integer — NO singleton hypothesis: the composite structure above the bottom level lives entirely in C(S) (singleton bottom ⟺ C odd — the isolated-minimum degeneration; full bottom ⟹ C even — the cascade jumps) — + **`square_cascade_even`**: EVERY square in A satisfies (Λ(j₀) + v₂(C(S))) even, i.e. by Legendre (Λ(j) = 2j − s₂(j)) the parity invariant **s₂(j₀) ≡ v₂(C(S)) (mod 2) on all squares**. All-prime stack law + all-prime isolated-minimum verified exact (20475/20475 + 7399/7399: all subsets [1..12] × p ∈ {2,3,5,7,11}). Certified census: exactly **15 squares to max(S) ≤ 24** (zero new for max ∈ [16,24]; largest {1,2,3,7,8,…,15} = 1183893²); 22 powerful sums ≤ 16. Honest scope: the finiteness questions (k-th powers, powerfuls) remain OPEN — the cascade parity is the engine; the wall is the composite cascade beyond the Bertrand window + the sparse-dodge. | `problem1108-subset-kernel/SubsetKernelLaw.lean` | `full_cascade_v2` + `square_cascade_even`: **[propext, Quot.sound]**; `isolated_min_v2` + `square_pair_singleton_even`: [propext, Classical.choice, Quot.sound] — **CI run 42061257046 GREEN (commit e5ab4ca, 4-round compile war 31→4→0 errors) — Kernel 13. Kernel 12 (ExactF62, Kill #16 — never before compiled by this branch's CI) restored and GREEN in the same run.** |
| **#18** | **404 (f(6,2) UNCONDITIONAL — the §7 freeze)** | **THE HYPOTHESIS KILL at anchor 6: `obstructionCheck_true : obstructionCheck = true` — a THEOREM [propext, Quot.sound]** + **`erdos404_f62_final`** : v₂(720 + Σ_{i∈B₆} i!) = 133 ∧ ∀ B (NoDupL, i ≥ 7): v₂(720 + Σ_{i∈B} i!) ≤ 133 — **ZERO HYPOTHESES** [propext, Classical.choice, Quot.sound]. **f(6,2) = 133 UNCONDITIONAL** — the second-ever exact f(a,2) value, now hypothesis-free (Kill #16's sole hypothesis is dead). The Kill-#14 architecture at half scale: 24-module §7 olean ladder (`gen_f62_final.py` — the twin-port generator; DP pre-verified 130/130 sets, obstructionCheck = true, peak 352 states, 129 coins [7,135], 1 multi-chunk round): DataS/C/D + Chain + SweepA/B (coinFrom spec: filter-free via classOf_bound_all, V−4 = classOf via v2_fact_classOf) + Coins (sort ladder) + FM0/1 + DD0–5 + DDm0 + Asm0/1 + AllA–D + All. **CI run 42119256613 GREEN (commit 2498b4f) — Kernel 14, FIRST-ROUND compile war (zero errors), receipts 61/133/129/true/true.** | `problem404-q3-chain/F62All.lean` (chain) + `gen_f62_final.py` | `obstructionCheck_true`: **[propext, Quot.sound]**; `erdos404_f62_final`: [propext, Classical.choice, Quot.sound] — **CI run 42119256613 GREEN — Kernel 14.** |

**Honest accounting (session 022 update):** the complete problems are NOT yet
fully solved.  #404: the reduction (Theorem A) is complete; **the $p \mid a{+}1$
class is closed for EVERY prime $p$ (Kill #15: $f(a,p) = v_p(a!)$ on the
class — including all odd $a$ at $p{=}2$ and, for odd $p$, every $a \equiv p{-}1 \bmod p$)**; for $p = 2$, ELEVEN further infinite families are classified exactly
($a \equiv 4 \bmod 8$; $a \equiv 10 \bmod 16$; $a \equiv 32/48 \bmod 64$;
$a \equiv 8 \bmod 64$; $a \equiv 40, 56, 88, 70, 118 \bmod 128$ —
T2/T3/T4/T5/T6/T6b/T6c/T7/T7b) plus $f(2,2) = 254$ and the full a-sweep
$g$-table ($a \le 60$, all exact, zero unbounded); the open
cores are the class $p \nmid a{+}1$ for odd $p$ (the staircase can grow),
the monsters at $a > 60$, and sub-question 3 for the survivors
(no infinite chain exists at $(2,2)$ — settled negatively by Kill #14; **no infinite chain at $(6,2)$ either — the boundedness side of Kill #16**).
**Cross-prime state after Kills #15/#16:** for EVERY prime $p$: the class $p \mid a{+}1$ is closed ($f(a,p) = v_p(a!)$, Kill #15); at $p = 2$: twelve classified families + TWO exact isolated values $f(2,2) = 254$, $f(6,2) = 133$ + the full a-sweep $g$-table ($a \le 60$).  #261: sub-question 1 is known ([BoLo90], formalized as Kill #8's
`bl_family`); sub-questions 2 (all $n$ — certified to $2\times10^5$) and 3
(rational $x$ — periodic towers DEAD, carry loophole isolated) are the open
cores, connected by the Q3 bridge.  #271: the complete problem
includes $A(4)$ (the open core); Kill #3 verifies one known-family
member.  **#1108 (Session 023):** the subset-kernel + full-cascade laws
are Lean-proven and CI-registered (Kill #17) — the 2-adic valuation of
every element of $A$ is a closed formula $\Lambda(j_0) + v_2(C(S))$ and
every square in $A$ carries the parity invariant $s_2(j_0) \equiv
v_2(C(S)) \pmod 2$; the finiteness questions remain open (Brindza–Erdős
bounds the terms at bounded $|S|$, so the war lives at $|S| \to \infty$;
heuristic: finiteness expected; census: zero new squares for $\max S \in
[16,24]$).  **#406 itself is
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

## NEXT FRONTS (the one-shot queue — Session 023 re-assessment)

1. **#1108 THE WAR (active, Kill #17 opened it)** — finiteness of
   squares/powerfuls in $A$. Engine delivered: the full cascade law +
   parity invariant. Next: Legendre parity in Lean ($\Lambda(j) = 2j -
   s_2(j)$ — the explicit $s_2$ invariant), the all-prime isolated-minimum
   in Lean (the `vpad` toolkit of TheoremBGeneral transfers), census MitM
   beyond 24, the composite-cascade wall (the sparse-dodge beyond the
   Bertrand window).
2. **#404 flat-class value batch** — f(50,2)=62 and siblings as tiny
   freezes (the (6,2) chain architecture re-used at smaller scale; each =
   one more unconditional exact value).
   [DONE THIS SESSION: the (6,2) §7-freeze — Kill #18, CI 42119256613 —
   `obstructionCheck_true` is a THEOREM; Kill #16 is now unconditional.]
3. **#404 classification completion** — the 22 deep survivors at $2^{28}$,
   the bounded staircases, the odd-$p$ staircase class ($p \nmid a{+}1$).
4. **#261 rational-x** — the carry loophole / scattered-representation
   conjecture (tree surgery + the Theorem 2/3/5 machinery) + sub-Q2
   all-$n$ termination (frontier 3,740,200).
5. **#271 / A(4)** — the Type-2 Stanley frontier (census $k{=}21$:
   $c_{21} = 710129$, $\alpha \approx 0.584$).
6. **#406** — the anchor summit (BOSS's own front).

*Corrections (Session 023): #404 Conjecture D is DEAD — refuted by
Kill #14 ($g(2,2) = 253$ finite, so no infinite chain at $(2,2)$).
#260 killed externally (Wang 2026) — removed from the queue.*

---

## FRONT OPENED — Erdős #317 (Session 026, 2026-11-05)

**Signed harmonic sums** (`problem317-signed-harmonic/`): the M/Lₙ integer
reduction + **Theorem A** (the conditional classification kill: if any prime
p ∈ (n/2,n] has lcm(1..n)/p ≢ ±1 mod p, then no δ ∈ {−1,0,1}ⁿ gives
Σδ_k/k = ±1/Lₙ) + the engine certificate (803,790 prime-tests, n ≤ 5000,
zero degenerates). Two kernels named: K1 (the residue lemma), K2 (the
collision-count bound for PART 1). Full audit of all 18 kills: **every kill
unconditional, zero sub-problem remnants** (THE_LIST §A).

*Session 026: full-corpus roulette (588 open problems) — no fast one-shot
remains; new-problem ladder: #317 → #389 → #203. The engine never stops; it
never lies.*
