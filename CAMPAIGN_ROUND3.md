# ROUND 3 — THE FULL-PROBLEM SWEEP (2026-11-02)

**Branch:** `oneshot/full-sweep-20261102`.  **Mandate:** complete the
particular-case kills into FULL-problem one-shots (#271, #404, #261), map
the entire open corpus against the FULL arsenal (both repos' latest
branches), and open the next-round list.

---

## 1. THE STATEMENT RETRIEVAL (ground truth re-established)

All four target statements fetched verbatim from erdosproblems.com (via the
page_reader bypass; saved `/home/z/erdos-recovery/corpus/`):

- **#261** = THREE sub-questions: infinitely many $n$?  all $n$?  a rational
  $x$ with $2^{\aleph_0}$ representations?
- **#271** = characterize $A(n)$ for ALL seeds $n$ + growth (the dichotomy).
- **#404** = classify ALL $(a,p)$: bounded $k$?  behavior of $f(a,p)$?
  does ANY infinite chain with $m_k \to \infty$ exist?
- **#406** = the anchor (finitely many $2^n$ with ternary digits in $\{0,1\}$).

**The audit confirms BOSS's assessment:** Kills #3 and #4 are correct
mathematics for particular cases (A(2) is the $k=0$ member of the
Odlyzko–Stanley known family; the p=2 tail law is the full-tail case of
#404), and #261's family carried three theorems with the all-$n$ and
rational-$x$ cores open.

## 2. WHAT ROUND 3 LANDED

### Erdős #404 — the full problem, substantially cracked
New package `problem404-full/` (kernel-green targets + battery 146/146):

- **THEOREM A (the p-adic reduction)** — every sum factors through the
  quotient staircase $P_i = i!/a!$: $f(a,p) = v_p(a!) + g(a,p)$ where $g$
  is the subset-sum depth of $-1$ in the $P$-staircase mod $p^k$;
  **compactness: $g = \infty \iff$ an exact $\mathbb{Z}_p$ zero-sum
  $\sum_{i\in Z} i! = 0$ exists $\iff$ the infinite chain of sub-question 3
  exists.**  This reduces the whole problem to a p-adic subset-sum closure
  question.  (Kernel: `erdos404_split`.)
- **THEOREM B — the $p \mid a{+}1$ class completely solved:**
  $f(a,p) = v_p(a!)$ (kernel: `erdos404_odd_a` for $p=2$, all odd $a$;
  general $p$ in DERIVATION.tex).
- **THEOREM C — $f(4,2) = 6$ exactly** (witness $4!+5!+7! = 5184 = 2^6\cdot
  81$; the mod-16 obstruction; kernel: `erdos404_f42`).
- **The block-identity structure theory** ($[u,u{+}1] = u!\,(u{+}2)$,
  $[u,u{+}2] = u!\,(u{+}2)^2$, $[u,u{+}3] = u!\,(u{+}2)(u^2{+}5u{+}5)$;
  kernels `block_pair`, `block_triple`).
- **The computational classification** ($a \le 40 \times p \le 61$): all
  bounded entries certified by complete DP; unbounded candidates
  $(2,2), (6,2), \ldots$ obstruction-free to depth $2^{28}$.
- **CONJECTURE D + the König chain:** $g(2,2) = \infty$ (evidence: depth 28;
  the explicit nested chain with valuations $3,7,9,9,13,18,23,\ldots$
  verified exactly).  If proved, **sub-question 3 of #404 = YES.**

### Erdős #261 — the rational-x bridge
New package `problem261-q3bridge/`:

- **THE Q3 BRIDGE (new theorem):** bounded-room all-$n$ $\Rightarrow$ a
  rational $x$ with $2^{\aleph_0}$ representations — connecting
  sub-questions 2 and 3 (full proof in DERIVATION.tex).
- **The representation-family identity formalized** (`bl_family`): the
  Borwein–Loring family $n = 2^{m+1}-m-2$, independently re-derived, with
  the two sum engines (`jpow_sum_eq`, `pow_sum_eq`) and toggle receipts.
- **Frontier:** the walk termination engine re-armed (C, 64-bit);
  Kill-#2 frontier $\le 10^5$ re-verified; the $10^5 \to 3\cdot10^6$ run
  in flight at commit time (log: `frontier_1e5_3e6.log`).

### Erdős #271 — the honest frontier
New package `problem271-status/`: the complete problem (all $n$) includes
$A(4)$ — OEIS A005487, a 45-year open case (the Type-2 growth question).
**No complete one-shot of #271 exists today without cracking the general
Stanley-sequence structure problem.**  Kill #3 stands as the formal
verification of one known-family member ($A(2)$, Odlyzko–Stanley class).
The engine (`discover_sorted.py`) and the attack order are mapped.

## 3. THE FULL-ARSENAL CORPUS RE-MAP (war council, this round)

Arsenal mapped (both repos, latest branches):
- **HC-PROOF (49 rounds):** the transferable lane is the arithmetic-dynamics
  core — ternary digit calculus, LTE cuts/c-towers, tower reads, binomial
  blades, carry automata, mixed-radix equivalences, coupled transport,
  crossing-charge telescoping, six-adic resolution, Cantorian-power
  classification — the same engine family as erdosternary2's GST-406
  modules.  The Hodge-geometric engines (fold equations, Albert
  stratification, K-theory) do not transfer to the Erdős corpus.
- **erdosternary2 (123 branches):** 22 engines (hGate theory, valuation
  spines, worldtrace lifts, carry entropy, Perron barriers, dual-scale
  cuts, syndetic covers, countermodel discipline); #406 core = GAP-A2,
  pinned equivalent to the 1979 conjecture.

Corpus cross-reference (593 open problems; 179 full statements re-fetched
this round, rate-limited; the tag taxonomy from the session-007 full pass):

| Family | Problems | Verdict with the FULL arsenal |
|---|---|---|
| Dyadic/walk (#261 kin) | 260, 249, 251, 257 | #260 behind the walk wall (sustained-orbit = the moving-modulus doubling map — the SAME walk engine); the dyadic four walled as mapped |
| Factorial p-adic (**NEW FRONT**) | 404 (+ 396, 727 kin) | **OPENED THIS ROUND**: Theorems A/B/C + classification; Conjecture D is the one-shot target; #396/#727 remain carry-rare research fronts |
| Stanley/AP-free | 271 (+ 124 kin) | #271 complete = A(4) (45-yr); #124 (BEGL96) research-grade as mapped |
| The anchor | 406 | GAP-A2 (Erdős-strength); every weaker route mapped/green |
| Base-representation | 376 (Graham $1000) | residue towers are native machinery, long-term, NOT one-shot |
| Everything else (500+) | covering systems, analytic density, primes, graphs, Ramsey, geometry | no new one-shot fronts identified by the full-arsenal pass |

**The honest verdict:** the full-arsenal pass did NOT unlock new
one-shot-able classes beyond the digit/valuation/carry family already
engaged — but it OPENED the factorial p-adic family (#404) as a
substantially crackable front (this round's Theorems A/B/C) and connected
#261's two open cores (the bridge).

## 4. THE NEXT-ROUND ONE-SHOT QUEUE (kill-shot order)

1. **#404 Conjecture D** — the gadget-supply lemma (close the gap levels
   $k \in \{5,6,9,12,13,14,\ldots\}$ with closed-form families) $\Rightarrow$
   $g(2,2) = \infty$ $\Rightarrow$ **sub-question 3 = YES** (a complete
   sub-answer of the full problem, CI-green).
2. **#404 classification completion** — the bounded-set structure (exact
   $g$-certificates → closed form for $f$ on the bounded class).
3. **#261-Q2/Q3** — the walk termination (all $n$) + the uniform-room
   conjecture $\Rightarrow$ the rational $x$ (the bridge fires).
4. **#260** — the sibling (sustained-orbit walk analysis).
5. **#271/A(4)** — the 45-year Type-2 frontier (research-grade).
6. **#406 GAP-A2** — the anchor summit.

## 5. CI

`kills.yml` extended: Kernel 5 (`problem404-full/PadicReduction.lean`) +
Kernel 6 (`problem261-q3bridge/BlockIdentity.lean`) + the
`verify_404.py` battery.  All six kernels compile on GitHub Actions
(Lean v4.33.0-rc2 + Mathlib cache); a kill counts ONLY on a green run.
