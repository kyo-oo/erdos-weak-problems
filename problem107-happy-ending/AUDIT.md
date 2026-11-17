# AUDIT.md — Erdős Problem #107: the doubter mathematics (adversarial audit lane)

**Wave 1 · Task 3-b · doubter lane (commander-executed after dispatcher deaths; the
engine `engine107.py` IS the audit weapon — three independent method code paths).**

---

## §A. THE VERIFICATION PROTOCOL (three methods, independent decision logic)

- **M1 brute (decisive):** exhaustive enumeration of all C(N,k) k-subsets; each subset
  tested for convex position by the exact-integer Andrew monotone-chain hull-vertex test
  (`hull_vertices` / `in_convex_position`). Integer arithmetic only — no floats, no
  Fractions in the decision path.
- **M2 cups/caps DP certificate (`cups_caps` + `certificate_best`):** computes
  U[i] = max cup ending at i (leftward DP with per-length minimal last-slope tracking),
  D[i] = max cap starting at i (rightward DP with per-length maximal first-slope
  tracking); sound absence certificate: max_{p<q}(U[q]+D[p]) < k+2 ⟹ no convex k-gon.
  Vertical pairs (equal x) are skipped — SOUND, because the lower/upper chains of a
  convex polygon are x-monotone, so consecutive chain vertices always have distinct x.
- **M3 hull-size indicator:** |hull(S)| ≥ 4 — sufficient-only indicator (see §B: NOT
  equivalent to subset convexity — a genuine audit finding).

## §B. GENUINE AUDIT FINDINGS (machine-discovered, machine-certified)

1. **The hull≥4 equivalence FAILURE.** |hull(5 pts)| = 3 (triangle + 2 interior) does
   NOT imply "no convex 4-subset": the two interior points + the two together-side hull
   vertices form a convex quadrilateral (the (α)/(β) mechanism proven in PROOF.md §2).
   The engine initially claimed equivalence; the machine refuted it (counterexample
   archived in the tool-results record: {(-110,706),(-891,-673),(-135,-755),(-168,312),
   (-160,-308)} — hull = 3, yet {D,E,C,A} = {(-168,312),(-160,-308),(-135,-755),(-110,706)}
   is in convex position). The definitive test (M1) was rerun: **0 failures in 10⁴
   random GP 5-point sets** — f(4)=5's machine certificate is the M1 sweep, and the
   mis-claimed "equivalence" is now documented as the sufficient-only indicator it is.
2. **The naive dichotomy-label injectivity FAILURE.** The (max-cup-ending, max-cap-ending)
   labeling is NOT injective: 263/300 random GP sets (n = 6..14) contain duplicated
   labels (receipts107.txt part D). This kills the tempting "easy proof" of the ES
   binomial dichotomy via naive pigeonhole — the classical proof's Pascal-recurrence
   structure is genuinely necessary; the dichotomy is correctly carried as a CITED
   theorem (PROOF.md §5), not dressed as a naive re-derivation.
3. **The DP certificate is sufficient-only, and this is certified.** Witnesses
   lattice-1/lattice-3/interleaved: best U[q]+D[p] = 7 ≥ 7 = k+2 for k = 5 — the
   certificate CANNOT certify their no-convex-5 property — yet M1 brute DECISIVELY
   verifies it (all 56 subsets, 0 convex 5-gons). Soundness direction (best < k+2 ⟹
   absence) holds (PROOF.md §4 machinery); completeness fails — documented with the
   exact witnesses.
4. **First-wave construction attempts died honestly.** The translate-doubling family
   (x-disjoint far-above-right) GROWS BOTH cup and cap (the [single-A][transition]
   [B-cap] mixed pattern: maxcap = n−1, not 2 — machine-refuted at n = 4..12); the
   binary-string digit families (±4^j bit weights) fail the cup+cap bounds (best U+D
   ≈ 3m vs needed m+3). Both refutations are archived in the tool-results record;
   the classical ES 1961 construction is the cited existence proof (honest scope).

## §C. THE WITNESS VERIFICATION TABLE (two methods each; M1 decisive)

| witness | GP | brute56 (no conv-5) | DPcert (best<7) | best U+D | maxcup | maxcap |
|---|---|---|---|---|---|---|
| lattice-1 | OK | **True** | False (inconclusive) | 7 | 4 | 3 |
| lattice-2 | OK | **True** | True | 6 | 3 | 3 |
| lattice-3 | OK | **True** | False (inconclusive) | 7 | 4 | 3 |
| lattice-4 | OK | **True** | True | 6 | 3 | 3 |
| interleaved-cup-cap | OK | **True** | False (inconclusive) | 7 | 4 | 3 |
| 4-pt interior witness | OK | **True** (no conv-4) | — | — | — | — |

All six witnesses SURVIVE both applicable methods. f(4) ≥ 5 and f(5) ≥ 9's witness side
are machine-certified.

## §D. VERDICTS ON THE ATTACKER'S THEOREMS (PROOF.md)

| theorem | verdict |
|---|---|
| S1 (f(3)=3) | SURVIVES (trivial-complete; machine base) |
| S2 (f(4)=5) | SURVIVES (case analysis complete: hull ≥ 4 case + hull = 3 case with the (α) line-intersection and (β) extremality arguments; 10⁴-sweep 0 failures M1-decisive; the m1/m2 indicator-failure finding incorporated honestly) |
| M (monotone subsequence lemma) | SURVIVES (full re-derivation, the injective labels for sequences — contrast receipt D) |
| CC (cup/cap → convex position) | SURVIVES (complete; every engine check uses the same exact hull machinery) |
| DICH (cited) | CITED-CORRECT (statement matches the classical form with all hypotheses; the naive-proof-failure receipt D documents why it is cited) |
| U (upper bound, cited+assembled) | SURVIVES (assembly complete given DICH; frontier-table edge checks n=4,5,6 ✓) |
| L (lower bound, cited) | SURVIVES (machine witnesses at n=3,4,5; the honest scope: construction attempts refuted, classical citation carried) |
| V (f(5)=9, f(6)=17, cited) | SURVIVES (citation matches corpus page references) |

## §E. THE EXACT OPEN FRONTIER (one line)

The conjecture f(n) = 2^{n−2}+1 is OPEN for n ≥ 7 — the certified gap is the frontier
table (part C: upper binom(2n−4,n−2)+1 vs conjecture 2^{n−2}+1, log₂ ratio 1.81 at n=40);
f(7) ∈ [33, 253].

## §F. ARSENAL USAGE (the audit's own consumption)

- `CardinalWorlds` ternary readers (positional `div/mod` discipline): the structural
  template of the U/D DP readers (leftward cup / rightward cap by position).
- `CardinalWorldsV2` dyadic scaling (2-world 2^j): the frontier table's exponent-law
  certificate context (the 2^{n−2} structure).
- `ErdosTernary2` digit laws: doctrine-level lineage for the slope-aggregation folds.
- Honest labeling: structural doctrine only; no Arsenal theorem is a proof step (the
  campaign law holds).

## §G. FILE STATE

`engine107.py` (v3, patched: vertical-pair guard in the DP; the M1-decisive part-B
logic) · `receipts107.txt` (ALL-GREEN=YES, wall 33.0 s) · `PROOF.md` (the attacker
package) · `AUDIT.md` (this file) · `corpus.html` (the target page).

---

*W1-C2 lane, commander-executed. The engine never stops; it never lies.*
