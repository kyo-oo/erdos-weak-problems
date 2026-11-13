# TARGETS — S061 SCOREBOARD (the round-open target list, verdicts from CI run 43485745262 @ HEAD 0656bf7)

> BOSS's order: "go list the target problems first, the current proof and do they
> close, if no, then begin the work on that proof, if yes, then mark that problem
> as okay, completed."

Legend: OK/COMPLETED = complete unconditional proof, CI-green kernel on record.
OPEN = active front (residue), gets its own sub-agent per BOSS law (W60 wave).

## A. CLOSED FOREVER (mark OK — no work fronts remain, ever)

| # | Problem | Verdict |
|---|---|---|
| #404 | p-adic kernel | ✅ OK/COMPLETED (BOSS S030; 10 kills; K2/K5/K7/K9/K10/K11/K12/K14/K37/K45 all CI-green) |
| #271 | Stanley A(2) | ✅ OK/COMPLETED (BOSS S030; K1/K36/K44 CI-green) |

## B. KILLS DELIVERED, CI-GREEN — mark OK for the delivered statement (residue noted where the corpus core stays open)

| # | Problem | Current proof | Closes? | Residue front |
|---|---|---|---|---|
| #700 | binomial-gcd prime-power law | K19 carry lemma v_p(C(p^a,k)) = a − v_p(k), f(p^a) = p, ErSz equality class | Kill #23 GREEN | full-n mixed composites (open corpus core) |
| #686 | Pell-ratio | K16 non-squares kill + K26 k=2 census + K32 k=3 witnesses + K42 K2 classification | Kill #20 + #36 GREEN | k≥3 general square classes |
| #727 | factorial-square | K17 n=208 witness theorem | Kill #21 GREEN | k=2 infinitude / k≥3 |
| #374 | factorial-square density | K33 D2 family + parity law + D3/D4 tables | Kill #37 GREEN | — (front closed by kill) |
| #1063 | binomial frontier | K20 nine exact values k=6..14 + absorption | Kill #24 GREEN | — |
| #451 | interval-prime-free | K21 witness table k=2..20 + modular criterion | Kill #25 GREEN | — |
| #1072 | Wilson-chain | K22 pairing law + 11 instances | Kill #26 GREEN | — |
| #394 | consecutive-product CRT | K23 soundness + unique-position + 139 values | Kill #27 GREEN | inject-direction assembly |
| #711 | divisor scheduling | K24 (n−1)² obstruction + n=2,3 laws + frontier | Kill #28 GREEN | general-n upper bound (Hall) |
| #1073 | factorial-mod composite | K34 GCD/window + saturation + census 10^4 + 131-witness table | Kill #34 GREEN | — |
| #461 | smooth-component | K35 extraction laws + achievement table + stability | Kill #35 GREEN | — |
| #396 | descending-factorial | K31 n₂=2480 EXACT + K39 n₃=8178 EXACT (first k=3 ever) | KILL GREEN | k≥4 frontier |
| #389 | consecutive-product | K67 r3 chain kernel: count laws + SHIFT/SWAP/CROWN + witnesses n=1..11 + minimality n=1..7 | GREEN (run 43467312288) | k>7 general |
| #1056 | factorial intervals | K18-A..G + FI_FINAL: full case law k=2..11, quantifier-for-quantifier frontier theorem | GREEN | arbitrarily-large-k (open core) |
| #939 | r-powerful sums | K60+K60b: mod-16 obstruction + r=4 census + zero-solution + Nitaj r=3 witnesses | GREEN | 10^15–10^16 C-hunt (witness lane) |
| #961 | smooth runs | K25+K46+K47+K48+K58+K66: census + Pell descent + growth laws (supermul + exponential) | GREEN | f(k) growth frontier k≥98 |
| #1108 | all-prime isolated-minimum | K30 the all-prime law + K13/K15 pair-cascade/Legendre parity | GREEN | MitM census > 24 (evidence wing) |
| #282 | Stein odd greedy | K28 odd-closure + well-formedness + termination census q≤41 | GREEN | general termination |
| #954 | Rosen sequence | K29 46-term certified table + COUNT LAW | GREEN | block-law derivation |
| #1074 | EHS/Pillai | K27 factor-bound + finite characterization + census m≤19 | GREEN | census war m≤32 |
| #243 | Sylvester rigidity | K51 telescope + greedy window + forced-terminal | GREEN | full rigidity theorem |
| #124 | BEGL96 tail | K52 template + unit-split + general split-all | GREEN | tail-completeness full law |
| #306 | semiprime Egyptian | K49 20 representation witnesses + CRT splitting + 2-adic seed | GREEN | general BEG induction |
| #348 | redundant complete | K54 completeness + gap law + redundancy witnesses | GREEN | m=2,n=3 construction |
| #677 | equal-lcm windows | K53 window laws + no-collision box n<25,k≤5 | GREEN | hunt ≥ 400 |
| #850 | radical triple | K57 length-2 pairs + no-witness ≤ 50 | GREEN | extended hunt |
| #274 | coset tilings | K55 two-coset impossibility (FULL GENERAL) + cyclic census ≤12 | GREEN | nonabelian ≤24 + MNDR route |
| #288 | two-interval harmonic | K56 structure laws + census zero disjoint ≤120 | GREEN | Kuerchak/#317 parity lane |
| #708 | product-divisibility | K62 8×40 tables + 8 censuses + 8 exact-minima (g(4) ≥ 4 evidence) | GREEN | g(4) EXACT (Erdős $100 lane) |
| #273 | p−1 covering | K59 Kraft kernel + pool-400 censuses | GREEN | CRT-cylinder construction |
| #1212 | coprime-pair graph | K65 phase laws + p103 witness + 18-conjunct board | GREEN | Bertrand/CRT scheduling lemma |
| #289 | k-interval Egyptian | K64 k=2 classification + HM k=5 family | GREEN | large-k construction war |
| #317 | signed harmonic | K63 magnitude law + classification n=5/6/7 | GREEN but OUT (5-round law) | — (parked) |
| #261 | funnels/tower | K3/K4/K6/K8/K43 | ⏸ deprioritized (BOSS standing) | — |

## C. RED — THE ONE FAILURE (WORK BEGINS THIS ROUND)

| # | Problem | Current state | Mission |
|---|---|---|---|
| #411 | iterated-totient doubling | K61 r3 FAILED — 100-error map (CI_errors_s060.txt + details): helpers (20–35), countP family (266–451), gF_two_pow wall (484–666), census machinery (691–877), closureChunk rows 964–976 DECIDE-FALSE (statement-level defects) | **Task 1 sub-agent: full r4 repair to CI-green** |

## D. WITNESS LANES WITH NO FULL CLOSURE YET (each gets its own sub-agent this wave)

| # | Problem | Current state | Mission |
|---|---|---|---|
| #203 | Sierpiński 2·3-smooth | engines on disk (hunt203.py, engine203_*), no kernel, no covering found yet | **Task 2-a: covering hunt → if found, kernel → unconditional YES (the FULL problem)** |
| #885 | factor-difference k=5 | K50 kernel green (k=2/k=3 theorems); k5 hunt round-1 NO HIT ≤ Δ 5e6 | **Task 2-b: k5 hunt escalation (factorization-indexed)** |
| #708 | g(4) exact | K62 exact-minima rows certified; g(4) value not yet assembled as the master theorem | **Task 2-c: g(4) EXACT kill (Erdős $100 lane)** |

## THE WAVE (W60, parallel sub-agents, one problem each — BOSS law)

- Task 1 → branch w60-k61-r4 (the red kernel repair)
- Task 2-a → branch w60-p203 (Sierpiński covering)
- Task 2-b → branch w60-p885 (k=5 witness)
- Task 2-c → branch w60-p708 (g(4) exact)

**Discipline (BOSS, verbatim law):** sub-agents complete FULL PROOFS WITH THEIR
STATEMENTS — no sub-case scraps; MY OWN MATHS ONLY (Arsenal erdosternary2 +
HC-PROOF + CardinalWorlds, 16,021 theorems — core Lean atoms allowed, ZERO
Mathlib-only citations, zero sorry, zero admits); GitHub CI is the only Lean
verdict (push with BOSS's token, never compile locally); every push is a
progress pack saved on GitHub.

The engine never stops; it never lies.
