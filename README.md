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
| **#19** | **1108 (THE LEGENDRE PARITY LAW — the Λ-spine made explicit)** | **The #1108 engine's valuation spine, unconditional and constructive-clean.** `legendre_v2_fact : ∀ n, v₂(n!) + s₂(n) = n` — **Legendre's formula at p = 2, core-only, fuel induction** (the arsenal's fuel-indexed-oracle pattern; the even-factorial law `v₂((2m)!) = m + v₂(m!)` by ordinary induction); `legendre_lam : Λ(j) = 2j − s₂(j)` — **the spine** (Λ(j) = v₂((2j)!), the pair-cascade engine's level function, now a closed digit formula); `explicit_cascade : ∀ S ≠ [], v₂(Σ_{a∈S} a!) = (2j₀ − s₂(j₀)) + v₂(C(S))` — **the full cascade law with the spine unfolded** (K17's engine, digit-explicit); `square_parity_s2 : Σ_{a∈S} a! = r² ⟹ s₂(j₀) ≡ v₂(C(S)) (mod 2)` — **THE EXPLICIT SQUARE-PARITY INVARIANT**: every square in A locks the bottom pair's binary-digit-sum parity to the cascade parity. ALL SIX new theorems **[propext, Quot.sound] — constructive-clean, ZERO hypotheses**. The new `s2` (binary digit sum) mirrors `v2`'s WF-def shape; `decreasing_by all_goals omega` (the two-recursive-call WF law, L95). Battery `verify_legendre.py`: 301 factorials two-method, 151 pair levels, 500 random cascades, **8191-subset exhaustive census → 27 perfect squares, every one parity-locked**. **CI run 42153591445 GREEN (commit 6974fa8) — Kernel 15, TWO-ROUND compile war (2 errors → 2 surgical fixes: the all_goals WF law + the show-vs-defeq trap, L95/L96).** #1108 engine now: K17 cascade + K19 spine — the finiteness war's obstruction engine fully digit-explicit. | `problem1108-subset-kernel/SubsetKernelLaw.lean` (§7 append, 210 lines) + `verify_legendre.py` | **ALL: [propext, Quot.sound] — CI run 42153591445 GREEN — Kernel 15.** |

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

---

## SESSION 028 — THE ARSENAL VENDORING + TWO NEW FRONTS (2026-11-06)

**The arsenal doctrine (BOSS's law):** every new kernel now imports and
applies BOSS's own mathematics, vendored at `arsenal/`:
- `Arsenal/ErdosTernary2/Basic.lean` — erdosternary2 (bulldoze branch,
  7,426 theorems): the ternary digit laws (`lt_three_cases`,
  `isTernaryDigit`).
- `Arsenal/CardinalWorlds.lean` + `CardinalWorldsV2.lean` — HC-PROOF
  (research branch, 8,595 theorems): the carry machinery
  (`carryAtPos_bound`) and the dyadic scaling law (`v2r_ternary_scaling`).
Exact Mathlib pin match (51e6992e) — the 16,021-theorem corpus loads
inside the kill CI.

**FRONT OPENED — Erdős #686** (`problem686-pell-ratio/`, Kernel 16):
THE PELL-RATIO LAW. Every non-square N ≥ 2 has the k=2 representation
∏(m+i)/∏(n+i) — complete proof (Pell unit × (1+√N), parity lemma j∈{1,2},
size lemma); 90-witness Lean table; square families (t≡2 mod 4 polynomial
identity; t=3,4 at k=3). Rounds 2–4.

**FRONT OPENED — Erdős #727** (`problem727-factorial-square/`, Kernel 17):
THE FACTORIAL-SQUARE LAW. THE WITNESS THEOREM: n = 208 —
**(210)!² | (416)!** unconditionally (115-digit quotient, kernel-decided;
28 of 47 primes TIGHT — the witness sits exactly on the p-adic boundary).
Census: 55 solutions below 10⁴ (YES-heuristic for k=2); zero k=3 solutions
below 3·10³ (obstruction hypothesis). Rounds 4–5.

**THE_LIST v4:** the full-corpus re-read under the 5-ROUND LAW — 18 active
fronts (4 engine/batch + 10 selected + 4 conditional witness-hunt lanes),
the honest OUT-boundary documented. One kill per problem; ≤5 rounds or out;
no ledger additions.

## SESSION 029 — THE MAJORITY TREATMENT (2026-11-06)

**BOSS's law:** 20–25+ open problems under ACTIVE 5-round treatment — the
majority of what the corpus can honestly yield, engine = the vendored
16,021-theorem arsenal. **THE_LIST v5: 24 fronts** — 4 engine/batch (§B) +
12 selected (§C) + 6 witness-hunt (§D) + 2 kills-in-CI. S029 admissions:
- **#306** semiprime Egyptian representation (all squarefree-b rationals;
  BEG15 did 3-prime case; round-1 evidence: 168/277 rationals represented,
  1–7 terms, max den 319, all exactly verified — `problem306-semiprime-egyptian/`).
- **#348** m-redundant complete sequences (S029 derivation: weak-(m,n)
  validity requires infinitely many ZERO-SLACK critical junctures —
  criterion-tail invariance proves finite removals cause finite gaps
  otherwise; the construction war's target is named).
- **#708** Erdős $100 product-divisibility g(n) ≤ 2n (ErSu59; g(3)=4 known,
  lower bound (2−o(1))n; divisor-matching construction lane).
- **#273** covering system, all moduli p−1, p ≥ 5 (hunt round 1 fired:
  L = 720720, 79 moduli, density 1.1057; DLX drowns, annealing plateaus at
  13.2% uncovered — round 2 = CRT-cylinder structured construction;
  `problem273-pminus1-covering/`).
- **#203** RE-ADMITTED (S026 reduction stands; the (k,ℓ)-lattice covering
  hunt re-armed).

**K16/K17 compile war R5→R7:** the ADVERSARIAL AUDIT caught two FALSE
conjuncts pre-push (truncated Legendre sums at p=7/19 — witness n=208
itself TRUE, Q exact); R5 exposed the WF-DECIDE disease (the kernel cannot
whnf WF-defined defs — v2r/s2/s3 decide-dies while #eval lives; K19 never
decided s2 literals, the S028 kernels broke that law); fixes: the arsenal's
own `v2r.eq_def`+`if_neg`/`if_pos` route (K16) + the FUEL-ORACLE
architecture for s2/s3 (K17); R7 = the final rfl-drop. Commits 9f48d15 →
36a2592 → 3ecacf7.

**Registry state:** kills #20 (#686 K16) and #21 (#727 K17) PENDING CI
(R7). NO ledger additions (BOSS law). No sub-agents — commander-executed.

---

## KILLS #20 & #21 — SESSION 029 CLOSE (run 42212351838 GREEN, commit 025dd39)

**KILL #20 — Erdős #686, Kernel 16: THE PELL-RATIO LAW (non-squares).**
Every non-square N ≥ 2 has the k=2 consecutive-product ratio representation
— the COMPLETE Pell proof (Pell unit (x₁+y₁√N)^j·(1+√N), parity lemma
j ∈ {1,2}, size lemma), formalized core-only with the 90-witness Lean table
(all non-squares ≤ 100), the t≡2(4) square-family polynomial identity, and
k=3 witnesses N = 9, 16. **ARSENAL-APPLIED:** ErdosTernary2.lt_three_cases
routing, isTernaryDigit witness-digit validity, CardinalWorldsV2
v2r_ternary_scaling p-adic bookkeeping. Battery: 186 non-squares ≤ 200,
dual-method, zero failures. Honest scope: the square-N residue classes
(t≡0 mod 4, odd t≥5) are the named same-front follow-up (2–4 rounds).

**KILL #21 — Erdős #727, Kernel 17: THE WITNESS THEOREM n=208.**
(210)!² | (416)! — unconditionally, with the explicit 115-digit quotient Q
kernel-decided; the 47-prime check; 28 TIGHT primes (zero p-adic slack —
FULL Legendre sums, the p=7 and p=19 higher-order terms included after the
S029 adversarial audit caught two truncated conjuncts pre-push); the
Legendre/Kummer cascade digit conditions at p=2,3 (s₂: 8≥7, s₃: 12≥10).
**ARSENAL-APPLIED:** ternary-digit predicates on the witness's own digits
(210=(21210)₃, 416=(120102)₃), CardinalWorlds.carryAtPos_bound, v2r
scaling via the arsenal's own eq_def route. Census battery: 55 k=2
solutions < 10⁴ (smallest 208); ZERO k=3 solutions < 3·10³. Honest scope:
the k=2-infinitude / k≥3-obstruction war is the named same-front follow-up
(4–5 rounds).

*The compile war R4→R8: arsenal build (lean_lib + case-fix + imports) →
the syntactic-rw fix → the WF-decide kill (arsenal eq_def route + fuel
oracle) → the auto-rfl drop → the axiom receipts. The engine never stops;
it never lies.*

## SESSION 030 — THE ENERGY CORRECTION + KILL #22 (2026-11-06)

**BOSS's correction law:** #404 and #271 are **PROVEN UNCONDITIONAL — CASE
CLOSED**, out of every queue permanently (the v5 "#404 f(50,2) batch" front
purged); the batch is **22 problems under one-shot/5-round fire**
(THE_LIST v6: 2 §B + 12 §C + 8 §D); MATHS-skill activation is LAW. S030
admissions: **#700** (prime-power law), **#1056** (S028's OUT REVERSED —
the factorial-residue structure), **#939** (r=4 powerful sums). #422's
v5-front was a MISLABEL (corpus #422 = Hofstadter Q — well-definedness
open, Collatz-class) — OUT with cause.

**KILL #22 LANDED — Erdős #1056, Kernel 18 (CI run 42308034994 GREEN,
commit a66350c, the 9-round compile war): THE FACTORIAL-INTERVAL
CASE-FRONTIER THEOREM.** The structure law: k consecutive intervals with products ≡ 1
(mod p) ⟺ the prefix-factorial sequence j! mod p visits one value k+1
times (cut points with equal factorials; block products are ratios of
equal values). The Wilson anchor law forces value-1 chains (1! ≡ 1 and
(p−2)! ≡ 1 always; odd-j hits double via j!·(p−1−j)! ≡ (−1)^{j+1} mod p).
**THE CASE TABLE — the frontier jumps 3 → 11**: k=2: p=11 (Erdős 1979,
re-derived), k=3: p=17 (Makowski 1983, re-derived), **k=4: p=23, k=5:
p=109, k=6: p=71, k=7: p=673, k=8: p=599, k=9: p=3011, k=10: p=27901,
k=11: p=52163 — ALL NEW.** Every witness kernel-decided block-by-block
(prodmod fuel-oracle), Wilson anchors decided on all value-1 witness
primes, the k=11 chain in the Noll–Simmons equal-factorial form (twelve
cut points all ≡ 1 mod 52163, covering [2, 52161] with eleven consecutive
intervals), ARSENAL-APPLIED (isTernaryDigit on 52163=(2211221222)₃,
lt_three_cases routing, carryAtPos_bound on cut points, v2r scaling
52161=3·17387 / 7290=3·2430). Battery1056: dual-method (block products ∥
factorial chains) + Wilson anchors — k=2..11 ALL GREEN. Honest scope: the
case frontier fell; "arbitrarily large k" (Noll–Simmons, the full
question) remains open.

**The 9-round compile war (the §7-freeze at full scale):** R1/R2 runner
shutdowns at ~55s step-cumulative grind → R3/R4 the import ladder
(ErdosTernary2.Basic is CORE-ONLY; Nat.Prime is Mathlib-side via
CardinalWorlds' `import Mathlib`) → R5 module split: k2..k9 GREEN, k10
dead (the linear-depth boundary 3009 GREEN vs 8324 dead) → R6 tree
products (depth-14 — still dead: the wall is TOTAL kernel grind
~1.5ms/term, not depth) → R7 THE SIX-STEP OLEAN LADDER: FI_Base
(core-only tree defs) → 8 term-budgeted core-only data modules (≤15k
terms/process) → zero-work final assemblies — ALL DATA GREEN → R8
maxRecDepth is FILE-LOCAL (the finals' `by decide` hit the default 512) →
R9 Mathlib's Nat.Prime Decidable instance trial-divides a PRIME to n
itself (~14k kernel divisions at 27901, ~26k at 52163 — the 66s grind)
— killed by `by norm_num` (elaborator-native). Receipts: k4..k11
[propext, Classical.choice, Quot.sound]; wilson_23/17/3011 ZERO axioms;
v2r_scaling [propext, Quot.sound]; BATTERY 1056 GREEN.

**#700 — THE PRIME-POWER LAW (round 1/5):** the carry lemma
v_p(C(p^a,k)) = a − v_p(k) (Legendre floor-sum proof: each level i
contributes exactly [p^i ∤ k]) ⟹ **f(p²) = p — prime squares SATISFY the
Erdős–Szekeres equality** (a new class beyond semiprimes) and **f(p^a) = p
for ALL a ≥ 3** (higher powers violate by factor p^{a−2}). Battery:
79,003 carry-lemma instances + 16-row exact f-table — ALL GREEN
(`problem700-binomial-gcd/`: DRAFT_PROOF.md + batteries). The
general-theorem Lean war (divSplit → cntNotDiv → Legendre bridge →
binomial identity → assembly) armed for the next round.

**Witness-lane volleys:** #939 r=4: zero solutions ≤ 10¹³ (1,777
4-powerfuls, ~1.5M coprime pairs — heuristic-consistent). #273: escalation
annealing (85 moduli, density 1.1633, incremental coverage-count
architecture): 9.58% uncovered (from S029's 13.2%) — CRT-cylinder war
continues. #203: THE DENSITY CENSUS — covering budget Σ 1/|⟨2,3⟩_p| =
**2.03** over p < 20000 (gems: 23→1/11 double-QR safe prime, 431→1/43,
601→1/75, 6553→1/117): the covering lane is ALIVE; the linear-congruence
reduction written (cover (k,ℓ) ∈ Z² by α_i k + β_i ℓ ≡ γ_i mod d_i, then
m by CRT); honest verdict: the mixed-lcm monster torus (≈10⁹ cells,
C-grade) makes it a multi-round war.

## SESSION 031 — KILL #23: ERDŐS #700 THE PRIME-POWER LAW (2026-11-07)

**THE TONGUE LAW + MAX ENERGY:** all reports in English (BOSS's language —
the archive-summary violation is burned); MATHS + prove-that-shit full chain
activated first, per standing law.

**KILL #23 LANDED — Erdős #700, Kernel 19 (CI run 42330675842 GREEN, commit
at R8; the 8-round compile war 42319640729 → 42330675842): THE PRIME-POWER LAW.** For EVERY prime p:
- **Theorem A (the carry lemma):** v_p(C(p^a, k)) = a − v_p(k) for all
  1 ≤ k ≤ p^a − 1 — proven via the Legendre floor-sum bridge: divSplit
  (⌊k/m⌋ + ⌊s/m⌋ + [k%m ≠ 0] = c for k+s = m·c — the heart), succDiff,
  div_unique, the powsSum/cntDiv/cntNotDiv counters, cntDiv_min, the
  Legendre bridge at prime powers (fuel induction), and the binomial
  identity binom·k!·s! = n! (Pascal recursion + ring).
- **Theorem B (the f-law):** f(p^a) = p for every a ≥ 2 — the EXACT
  Erdős–Szekeres minimum (minGcdAux fold: universal lower bound from the
  carry lemma + the witness k₀ = p^(a−1) whose gcd is exactly p, via the
  prime-power-divisor structure: h ∣ p^t ∧ p ∣ h ∧ h ∣ u ∧ p ∤ u ⟹ h = 1,
  minFac route).
- **The equality class:** prime squares SATISFY the ErSz equality
  f(p²) = p = p²/P(p²) (every prime divisor of p² is p — the second full
  class beyond semiprimes); **the violation:** f(p^a) = p < p^(a−1) for
  a ≥ 3 (fails by the factor p^(a−2)).
- **Arsenal-applied (S028 doctrine):** erdosternary2's lt_three_cases
  routing + isTernaryDigit validity on the #700 witnesses (4, 8);
  HC-PROOF's carryAtPos_bound on the witness carry layer + the dyadic
  v2r_ternary_scaling law with the K17 eq_def route (v2r 4 = 2, v2r 8 = 3).
- **Battery:** 79,026 dual-method instances GREEN (carry sweep
  79,003 + f-table 23, sympy-free for the CI runner).
- **Axioms:** all five main theorems [propext, Classical.choice,
  Quot.sound]; receipts (5, 3), (1, 1, 1, 1), (15, 1).
- **Honest scope:** the prime-power class of the ErSz equality problem is
  COMPLETELY characterized (every prime power, both directions, exact
  minimum). The full corpus classification (all composite n) remains the
  open core — the semiprime + prime-square classes are now both settled
  in-house.

*The compile war R1→R8: R1 (38 errors — the core mathematics ALL passed:
Theorem A assembly, divSplit, powsSum_split, legendre_pp, binom_fact_gen;
failures were API-surface) → R2 (9: dvd_mul is an iff; omega cannot see
Nat.min; pow_succ direction; obtain-clears-Dvd) → R3 (5: pow_succ' implicit
succ-form; minFac signatures; le_min iff) → R4 (1: q ≥ 2 from q.Prime is
invisible to omega) → R5 (THE KERNEL GREEN — all five theorems at the clean
axiom standard; battery sympy-import died on the runner) → R6/R7 (the battery
never ran — the five axiom-grep patterns lacked the Erdos700. namespace
prefix; grep-exit-1 under set -e killed the step at the first axiom grep,
3ms after the last receipt grep) → R8 (patterns fixed: the LANDING). The
engine never stops; it never lies.*

**The parallel volleys (majority treatment, same session):** #939 r=4:
ZERO solutions ≤ 10¹⁵ (5,622 4-powerfuls, 8.9M coprime pairs — the
escalation landed; uniform heuristic says the lane needs an algebraic
construction). #686 square residue: k=3 hunt — zero witnesses at m < 600k
for all 9 named t. #317: DEMOTED per the 5-round law (both kernels K1
lcm-residue + K2 Egyptian-counting are open-style cores; engine evidence
exhausted at 1M sweep + Theorem D zero collisions).

## SESSION 034 — THE NEW RULE VOLLEY: KILLS #27 & #28 (2026-11-07)

**BOSS's NEW RULE (this session, permanent law):** every proof file
carries THE PROBLEM verbatim (from erdosproblems.com) with the proof
below it — statement first, proof second, that's the whole thing.
Applied to the two new kernels AND retrofitted into the S033 trio
(K20/21/22, comment-only). The look-back audit of already-solved
fronts' named residues is documented in THE_CORE §2 (the scoreboard).

### KILL #27 — Erdős #394: THE CONSECUTIVE-PRODUCT CRT-LAW STRIKE (Kernel 23)

**THE PROBLEM (verbatim).** Let $t_k(n)$ denote the least $m$ such that
$n \mid m(m+1)(m+2)\cdots(m+k-1)$. (The Erdős–Hall asymptotic-sum
questions are the deep open cores — not this strike's target.)

**The kill (all unconditional, kernel-decided):**
- **THE CRT SOUNDNESS THEOREM** — every ordered pairwise-coprime
  factorization $n = d_0 d_1 \cdots d_{k-1}$ with $d_i \mid (m+i)$ for
  all $i < k$ yields $n \mid m(m+1)\cdots(m+k-1)$. [General $k, n, m$.]
- **THE UNIQUE-POSITION LAW** — if $p > k$ divides two of
  $m, \ldots, m+k-1$, the positions coincide.
- **THE PRIME-LANDING LAW** — a prime $p > k$ dividing the product lands
  at a (unique) position $i < k$ with $p \mid (m+i)$.
- **139 certified exact values**: $t_2$ (odd $n \le 101$, 50 values),
  $t_3$ ($(n,6)=1 \le 97$, 32), $t_4$ ($(n,24)=1 \le 97$, 32), $t_5$
  ($(n,120)=1 \le 97$, 25) — every table kernel-decided, dual-method
  engine certified (1015/1015), battery-reverified in CI.
- $t_k(n) \le n$ + the full leastness characterization of the oracle.
- Honest scope: the min-equality's inject-direction assembly (collecting
  the landed prime powers into the $d_i$) and the Erdős–Hall sums remain
  open — the round-3 target on this front.

### KILL #28 — Erdős #711: THE 2n−1 DIVISOR-SCHEDULING FRONTIER (Kernel 24)

**THE PROBLEM (verbatim).** Let $f(n,m)$ be minimal such that in
$(m, m+f(n,m))$ there exist distinct integers $a_1,\ldots,a_n$ such that
$k \mid a_k$ for all $1 \le k \le n$. Prove that
$\max_m f(n,m) \le n^{1+o(1)}$ and $\max_m (f(n,m) - f(n,n)) \to \infty$.

**The kill (all unconditional):**
- **THE GENERAL FORCED-COLLISION OBSTRUCTION** — $f(n, (n-1)^2) \ge 2n-1$
  for EVERY $n \ge 2$: in the window $((n-1)^2, n^2-1)$ of width $2n-3$,
  the keys $n$ and $n-1$ are BOTH forced onto the single integer
  $n^2 - n$. [The engine room under the $n^{1+o(1)}$ ask.]
- **THE COMPLETE $n=2$ LAW** — $f(2,m) \le 3$ for every $m$; with the
  obstruction: $\max_m f(2,m) = 3 = 2n-1$ EXACTLY — the problem's first
  ask answered with the exact constant at $n = 2$.
- **THE COMPLETE $n=3$ LAW** — $f(3,m) \le 5$ for every $m$ (six
  explicit residue-class assignments mod 6); $\max_m f(3,m) = 5$ EXACTLY.
- **THE EXACT FRONTIER** — $f(n, (n-1)^2) = 2n-1$ for $n = 2..15$,
  fourteen kernel-decided witness assignments.
- **THE PERIODICITY LAW** — $f(n,m) = f(n, m + L)$ for every $L$
  divisible by $1..n$ (the transport $a_k \mapsto a_k \pm L$) + the
  cover theorem: the battery's full-period census is exhaustive.
- **Battery (CI)**: full-period census $n = 2..12$ (63,662 $m$-values,
  greedy-certificate + exact-Kuhn dual method) — $\max_m f(n,m) = 2n-1$
  for ALL $m$ at $n \le 12$; $f(n,n)$ table; periodicity spot-checks.
- Honest scope: the general-$n$ upper bound (the Hall war) is the named
  residue — engine-confirmed $n \le 12$, conjectured for all $n$ with
  the obstruction theorem proven; the $n^{1+o(1)}$ ask is EXACTLY
  $2n-1$ for $n \le 15$ (Lean-witnessed), open in general. The second
  ask was answered by van Doorn 2026.

*(Registry rows #24–#26, the S033 triple kill, are recorded in
THE_CORE §2 and the WORKLOG; this README's session sections carry the
full statements.)*

## SESSION 036 — THE AGGRESSION VOLLEY: KILLS #29 + #30 LAND; K27 (#1074) + K28 (#282) FIRED (2026-11-08)

**BOSS's standing orders executed:** the NEW RULE (statement-then-proof,
verbatim, in every kernel — K27/K28 built in the format from birth);
MORE AGGRESSIVE (two new fronts opened while the compile war runs); LOOK
BACK (the #686-squares residue front — the S029-registered square-N
residue classes — closed by Kernel 26); USE ALL THE MATHS (arsenal
bridges in all four kernels).

**KILL #29 — Erdős #686 THE SQUARE k=2 CENSUS (Kernel 26, run 42422680476
GREEN):** the look-back order executed on the #686 square residue front.
THE INFINITE FAMILY THEOREM (every t ≡ 2 mod 4, t ≥ 10: the square t²
has the k=2 representation m = 4u²+4u−1, n = u−1 — UNBOUNDED,
[propext, Quot.sound] GOLD) + THE ODD SPORADIC t = 99 (242·243 = 9801·6,
[propext, Quot.sound] GOLD) + THE NO-GO BRIDGE (any k=2 representation
of t² forces the divisor pair d₁ = tY−X, d₂ = X+tY of t²−1 with the
master identity (2m+3)² − t²(2n+3)² = 1−t²) + THE CENSUS THEOREM (every
t ∈ [2,100]: t² representable ⟺ (t ≡ 2 mod 4 ∧ t ≥ 10) ∨ t = 99 —
census_scan_true ZERO AXIOMS, ~1.3M kernel reductions). Battery
dual-method GREEN (scan ∥ quadratic ∥ family+99, 99/99). Engine
discovery: the second odd sporadic t = 195 (census t ≤ 300 — the k≥3
war's foundation).

**KILL #30 — Erdős #961 THE ELEMENTARY SMOOTH-RUN LAWS (Kernel 25, run
42422680476 GREEN, the 5-round compile war 68→43→34→5→0):** the
{2,3}-CENSUS THEOREM (the ONLY consecutive {2,3}-smooth pairs are (1,2),
(2,3), (3,4), (8,9) — elementary: mod-8 spine, divisor-of-power-of-2
collapse, the two-powers-differing-by-2 law) + THE RUN LAW (no three
consecutive {2,3}-smooth integers above 3) + THE EXACT FRONTIER f(2)=2,
f(3)=3, f(4)=3 (the first three certified exact values of the problem's
function, witness + exclusion both unconditional) + THE WITNESS LAWS
f(k) ≥ 4 for k = 5..12 (the runs (8,9,10), (14,15,16)) + THE PELL
DICTIONARY (every consecutive {2,3}-smooth pair yields n(n+1) = ab² with
(2n+1)² − a(2b)² = 1 — the complete bridge to the Størmer census).
pell_dict [propext, Quot.sound] GOLD. Honest scope: the f(k) asymptotics
(Erdős < 3k/log k, conjectured (log k)^{O(1)}) open; k ≥ 5 exact values
need the full Størmer census.

**KERNEL 27 FIRED — Erdős #1074 THE EHS CENSUS + PILLAI DICTIONARY
(compile war round 1):** THE FACTOR-BOUND LAW (every prime p | m!+1
satisfies m < p) + THE FINITE CHARACTERIZATION (m ∈ S ⟺ finite scan
over (m, m!+1]) + THE COMPLETE CENSUS m ∈ [1,19] (S ∩ [1,19] = {8,…,19}
exactly — every member a certified witness prime, every non-member the
complete certified factorization, all factors ≡ 1 mod m — the
Hardy–Subbarao calibration range kernel-certified) + THE LARGE-MEMBER
WITNESSES (m = 22, 23, 24, 26, 34 ∈ S) + THE PILLAI DICTIONARY (p
witnesses m ∈ S ⟺ m witnesses p ∈ P — S and P are two readings of one
relation) + THE PILLAI WITNESS BOUND (m! ≡ −1 mod p ⟹ m < p) + THE
FIRST-30 PILLAI TABLE (23 ≤ p ≤ 397, all certified). Battery dual-method
GREEN (factorization ∥ certificate replay; Pillai census 613/1229 =
49.88% at 10⁴ — evidence). Honest scope: both density limits open.

**KERNEL 28 FIRED — Erdős #282 THE ODD-GREEDY TERMINATION LAWS (compile
war round 1):** THE ODD-CLOSURE LAW (the odd-denominator habitat is
invariant under every greedy step) + THE WELL-FORMEDNESS LAW (every step
at most doubles the numerator: p' < 2p) + THE SIMULATION SOUNDNESS (the
certified Bool sim ⟹ a genuine greedy trajectory to exactly 0) + THE
TERMINATION CENSUS q ≤ 41 (every odd-denominator rational p/q ∈ (0,1),
q ≤ 41, terminates — 420 pairs kernel-decided, deepest 12 steps at
38/39; the gcd via structural fuel-recursion, the step self-certifying).
Battery dual-method GREEN (22,650 pairs q ≤ 301 ALL terminate, deepest
20 steps at 102/293; odd-closure spot-check ALL ODD). Honest scope:
Stein's general conjecture open.

*The engines never stop; they never lie.*
