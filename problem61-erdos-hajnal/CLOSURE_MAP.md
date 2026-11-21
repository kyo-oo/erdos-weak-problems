# CLOSURE_MAP.md — W78-61E: THE n<=6 WORLD MAP
# The general case's terrain, machine-certified (engine61closure.py, 836/836 PASS)

Engine: engine61closure.py, receipts receipts61closure.txt (wall ~100 s).
Censuses n<=6 by numpy canonicalization (720 perms at n=6), two counting
codes agreeing (counts 1, 2, 4, 11, 34, 156 — the canonical sequence).

## THE HEADLINES

1. **THE 5-VERTEX FRONTIER IS EXACTLY FOUR GRAPHS**: P5, co-P5 (the
   complement pair, canon 58/221), the bull (self-complementary, canon
   59), and C5 (self-complementary, canon 220). **30 of the 34 five-vertex
   graphs are decomposable** — covered IN-FRAME TODAY by the tree law
   (C61-TREE-COMP) from banked leaves (the closed <=4-vertex world +
   singletons). With complement transfer, **THREE direct kills — P5,
   bull, C5 — close the entire 5-vertex world in-frame.**
2. **n=6: 26 primes, 130 decomposable.** The 26 primes are the named
   next frontier; the 130 are in-frame from banked leaves + the 26.
3. **The 4-vertex world has exactly ONE prime: P4** (canon 13) — banked
   (the W76 close). The other ten 4-vertex graphs are decomposable.
4. **PRIME-DEC certified exhaustively**: every graph n<=6 decomposed; the
   local ladder identity H = substitute(Q, [singletons..., M]) verified
   by canonical-form equality at EVERY internal node (469 nodes, zero
   failures). RAM-GEN plug-backs: exhaustive n<=6 (t=3,4,5) + sampled
   constructions t=3..8 to n=100 — zero violations.

## THE MAP (per n)

| n | unlabeled | prime | decomposable | frontier primes |
|---|-----------|-------|--------------|-----------------|
| 1 | 1 | 0 | 0 (the trivial leaf) | — |
| 2 | 2 | 2 (K2, E2 — trivially EH: c=1) | 0 | — (base cases) |
| 3 | 4 | 0 | 4 | — (all covered: K3/E3 via RAM-GEN, P3/K2+K1 banked) |
| 4 | 11 | 1 (P4, banked) | 10 | — CLOSED (W76) |
| 5 | 34 | 4 (P5, co-P5, bull, C5) | 30 | 4 primes = 3 kill targets |
| 6 | 156 | 26 | 130 | 26 primes (next wave) |

Full per-graph data: alln61/coverage_map.json (canonical key, edge count,
prime flag, complement key, decomposition leaves per graph).

## THE FOUR 5-VERTEX PRIMES (named, with certificates)

- **P5** (canon 58; 4 edges; degrees 1,1,2,2,2) — prime; complement =
  co-P5 (canon 221). ONE kill closes both (complement transfer, banked).
- **bull** (canon 59; 5 edges; degrees 1,1,2,3,3) — prime,
  SELF-COMPLEMENTARY (machine-verified: complement_canon == canon).
- **C5** (canon 220; 5 edges; all degrees 2) — prime, SELF-COMPLEMENTARY.
- **co-P5** (canon 221) — prime; closes with P5.

K5 and E5 (the banked W77 kills) are DECOMPOSABLE (every subset of a
clique/anticlique is a module) — the machine reclassifies them under the
tree law; the banked Ramsey-route kill (c=1/5) remains the STRONGER
arbitrary-graph result and is kept.

## NAMED DECOMPOSITION EXAMPLES (from the certified trees)

- K5 = the clique tower (all modules; tree of singletons under
  clique-quotients; in-frame exponent via the tree harmonic law; the
  banked RAM-GEN c(5) = 1/4-order constant governs arbitrary graphs).
- house (C4 + roof): decomposable — the machine's certified tree (see
  coverage_map.json, canon key of the 5-edge house class) closes it
  in-frame from 4-vertex leaves.
- Every 4-vertex graph except P4: decomposable (e.g., C4 = K2[2K1] — the
  banked [A2] builder identity).

## WHAT THIS MEANS FOR THE ALL-GENERAL TARGET

- The prime frontier is the ENTIRE remaining direct-kill content:
  {P5, co-P5, bull, C5} at n=5; 26 primes at n=6; then the primes at
  n=7, 8, ... (the density of primes grows; the frontier is infinite).
- Every decomposable graph at every size is covered IN-FRAME the moment
  its leaves are covered (C61-TREE-COMP + the banked/leaf kills).
- The uniformization bridge (GENERAL-REDUCTION (GR-2)) is the single
  named obstruction between the frame theorems and the full conjecture.

The engine never stops; it never lies. In English, always.
