# AUDIT_W81.md — W81-107B / W81-107B-F: the complete audit seal of the #107 Happy-Ending package

Task ID: W81-107B (auditor/doubler lane), sealed by finisher **W81-107B-F**
after the W81-107B dispatch died mid-mission with its audit fixes in flight.

Instruments (all fresh code, written for this lane — **no campaign engine
code is imported**; exact `int`/`Fraction` arithmetic, zero floats, seed
20261181, deterministic):

| code | what it is |
|---|---|
| **OT** | own order-type enumerator: per-subset sign vectors over triples, canonical key = min over all `n!` relabelings × {id, mirror} |
| **CVA / CVB** | own convexity codes: Andrew monotone chain (strict pops) / gift wrap (Jarvis, far-point tie-break) — every convexity verdict two-code |
| **DP** | own longest cup/cap DP (exact `Fraction` slopes, minimal-last-slope tracking), validated against brute-force chain scans |
| **E/X** | own rebuild of the ES_SANDWICH_ALLN.md §1 construction (`E(a,b;δ)` recursion + cluster-arc assembly), scaled once to integers |
| **GREEDY** | own GP-ELIM greedy extraction + exact max-collinearity census (primitive-direction line keys) |
| **C-PORT** | the sibling W81-107A `engine107f9` C binary (read-only), driven from the dumped v2-parent realizations |

Engine: `engine107audit_w81.py` — **8/8 stage checks PASS, wall 133.4 s
(budget 480 s), `AUDIT_ENGINE_GREEN=1`** (`receipts107audit_w81.txt`).
Sibling-lane comparison: `audit_w81_c_compare.py` — **C-COMPARE PASS**
(`receipts107audit_w81_ccompare.txt`).

---

## §A VERDICT TABLE — every audited document

| document | audit verdict | defects found | fixed by | where |
|---|---|---|---|---|
| `ALLN_PROOF.md` | **CLEAN after fix** | 1 (header overstatement: "all GREEN" vs the raw W77 receipts) | W81-107B (dirty diff, verified by −F) | `ALLN_PROOF.md:3–13` |
| `ES_PACKAGE_PROOF.md` §5 ($f(4)=5$) | **CLEAN after fix** | 1 **mathematical** (the upper-side finish "segments $ab$ and $pq$ properly cross" was FALSE — $a,b$ on the same side of line $pq$ makes $ab$/$pq$ opposite *edges*, not crossing diagonals) | W81-107B (dirty diff, verified + machine re-proved by −F) | `ES_PACKAGE_PROOF.md:219–262` (claim at :231) |
| `ES_PACKAGE_PROOF.md` §2 (Theorem CC, three-case extension lemma) | **CLEAN — no defect** (boundary re-verified by hand and machine) | 0 new (the W74 label-injectivity replacement re-audited at the $k{=}3,l{=}3$ boundary) | — | `ES_PACKAGE_PROOF.md:111–159` (cases :136–152) |
| `ES_PACKAGE_PROOF.md` §7.3 (Theorem GP-ELIM) | **CLEAN — no defect** ($N\geq2$ boundary re-verified by hand and machine) | 0 new (the W73 $N \geq 2$ correction re-audited) | — | `ES_PACKAGE_PROOF.md:449–538` |
| `ES_SANDWICH_ALLN.md` §1 (slope separation) | **CLEAN after completed fix** | 2 (i: display normalized by $\lvert i{-}j\rvert$ instead of $\lvert i{-}j\rvert/4$ — found by W81-107B; ii: the repair's own line printed the false equality $2\cdot(19/48) = (19/12)$ where the honest pair constant is $19/24$ — found by −F) + 1 boundary note ($s \leq 1/64$ holds iff $n\geq5$) | W81-107B (i, note) + W81-107B-F (ii, honest constants propagated) | `ES_SANDWICH_ALLN.md:55–85` (note :59, repair :70–75) |
| `SHARP_PROOF.md` §4 (Lemma VANDERMONDE-DOUBLE) | **CLEAN after completed fix** | 2 (i: pre-audit prose subtracted a spurious $t{=}b{-}1$ term — found by W81-107B; ii: the repair still ran the outer stick to $a{+}b{-}4$ and closed at $\binom{a+b-3}{b-2}-1$, a false intermediate (at $a{=}b{=}4$: reads 9, true sum 5), with an incoherent Pascal close — found by −F) | W81-107B (i) + W81-107B-F (ii: stick to $a{+}b{-}5$, closes $\binom{a+b-4}{b-2}-1 = \binom{a+b-4}{a-2}-1$) | `SHARP_PROOF.md:240–267` (repair :252–261) |
| `receipts107alln.txt` / `receipts107sharp.txt` (claims referenced by the docs) | **CONSISTENT** — the ALLN header's new numbers (8/13 raw; three defects; S8 batteries 3000/2000/500, 0 violations; 14/14 re-cert) all match the receipt files byte-for-byte in content | — | — | `receipts107alln.txt` (addendum), `receipts107sharp.txt` (TOTAL: 14/14) |

**No "open" labels were placed on any shipped claim.** Every load-bearing
statement of the package is either proved in-document (with the repaired
proofs above) or banked with a machine certificate listed in §B.

---

## §B INDEPENDENT VERIFICATION RESULTS (fresh code, this lane)

| # | verification | result | receipt line |
|---|---|---|---|
| A1 | **$f(4)=5$ exhaustive, both directions**: all GP 5-subsets of the grids 2×2, 3×3, 4×4, 5×5, 6×6, 5×8 (≤ 40 pts) — 615,714 GP 5-sets swept, **0 lack a convex 4** (both codes); 31,888 GP 4-sets with no convex 4 exist (lower side); order-type anchors $n{=}4 \to 2$, $n{=}5 \to 3$; the banked 4-point witness (triangle + interior) no-convex-4 both codes | **PASS** | A1-OTF4 |
| A1′ | **the repaired §5 mechanism in code**: 87/87 in-grid hull-3 (triangle + 2 interior) witnesses have the 2-1-split quadruple $\{a,b,p,q\}$ convex by BOTH codes | **PASS** | A1-OTF4 |
| A2 | **the banked 8-point no-convex-5 witnesses** (kernel + interleaved): GP exact; all $\binom{8}{5}=56$ subsets non-convex, BOTH codes; hull 4/4 | **PASS** | A2-W5WITNESS |
| A3 | **the ES-SANDWICH lower-side construction rebuilt at $n = 6, 7, 8$ with max-convex $= n-1$**: own rebuild of $X_n$ — sizes $2^{n-2}$ ✓, cluster sizes $\binom{m}{i}$ ✓, GP exact (integer scale) ✓, y-bands ordered ✓, slope separation measured exactly (intra $\leq s$, inter $\geq 1/(1+38\rho) > 1/2$, vertical = ∞) ✓, Lemma M spot-checks ✓; **no-convex-$n$ exhaustive: $n=6$ all 8008 subsets both codes; $n=7$ all 3,365,856 subsets both codes; $n=8$ 60,000 random + 400 hillclimbs, best hull 7, 0 convex-8**; convex-$(n{-}1)$ transversal witness both codes at every $n$ | **PASS** | A3-SANDWICH-N6/N7/N8 |
| A3′ | sandwich at $n=3,4,5$ (quick lane) + **audit finding #3**: the doc's constant "$s \leq 1/64$" holds **iff $n \geq 5$** ($s = 1/32, 1/48$ at $n = 3, 4$); the load-bearing chain $s < 1/2 < \sigma \leq \lvert\text{inter}\rvert$ holds for EVERY $n \geq 3$ — now stated in the doc | **PASS** | A3-SANDWICH-N3/N4/N5 |
| A4 | **U-BIS closed form $G(n)+1 = \binom{2n-2}{n-1}-2n+4$, $n = 3..11$**: $[4, 16, 64, 244, 914, 3420, 12856, 48604, 184738]$ — double-sum == closed form by two binomial codes $n = 3..30$; anchors 4, 16, 64, 244, 914 match ALLN_PROOF.md; $U\text{-BIS} \geq$ ES-ALLN-SHARP every $n$; instances: 25/25 16-point GP sets force convex 4; 12/12 64-point GP sets force a 5-cup-or-cap by the own DP (each chain convex by both codes); label census $\lvert P_{ij}\rvert \leq \binom{i+j-2}{i-1}$ | **PASS** | A4-UBIS |
| A5 | **the binomial table** $\binom{2n-4}{n-2}+1$, $n=3..30$, two codes; $n=3..8 = [3,7,21,71,253,925]$ (fresh, matches receipts107alln S7); gap ratios $n=3..10 = [1.0, 1.4, 2.33, 4.18, 7.67, 14.23, 26.61, 50.08]$ (match §6); sharpening recursion telescopes; **+ the repaired VANDERMONDE-DOUBLE identities (inner hockey, corrected outer intermediate, final) both binomial codes, all $3 \leq a,b \leq 30$** | **PASS** | A5-BINOMTABLE |
| A6 | **the v2-parent re-run** (comparison base for the sibling C port): 3 seeded-random $n=8$ parents from the banked 3315-type census re-run through the campaign python v2 machinery (read-only): cells = 287 each, children 422/401/391, fingerprints `6b276e021de358ec` / `739be4fc8a4829b7` / `6cf8c58eb310e29c`; realizations dumped | **PASS** | A6-V2RERUN |
| A7 | **negative controls (all six)**: NC1 planted convex-5 detected by both codes; NC2 convex-6 hexagon detected; NC3 collinear triple rejected by GP; NC4 corrupted U-BIS ($-2n+2$) rejected; NC5 translated-cluster corruption violates inter-separation while intra survives (the slope checker has teeth); NC6 own DP == brute force on 40 random 8-sets | **PASS** | A7-NEGCONTROLS |
| A8 | **the two boundary lanes named by the audit brief** (added by the finisher): (i) **Theorem CC's three-case extension lemma at the $k{=}3,l{=}3$ boundary** — the statement at $(k,l) = (3,3), (3,4), (4,3)$ on 5444/17720/17720 threshold-size GP x-distinct grid subsets, **0 violations** (own DP + brute chains agree everywhere); the $(3,3)$ X/Y-split + $\sigma/\tau$ trichotomy mechanism mechanized on all 5444 GP x-distinct 3-sets (Y = leftmost, cup = [1,2,·], $\sigma \neq \tau$ by GP, $\sigma>\tau \Rightarrow$ 3-cup, $\sigma<\tau \Rightarrow$ 3-cap, no-3-cup census $\Rightarrow \lvert X\rvert = 2 = \binom{1}{1}+1$); $E(k,l)$ tightness (size $\binom{k+l-4}{k-2}$, GP, distinct x, no $k$-cup, no $l$-cap — the bound is exact); (ii) **GP-ELIM at the $N \geq 2$ boundary** — 114 greedy extractions at/above the exact measured-$t$ threshold on planted-collinearity boards, all reached $m$; per-stage forbidden census $\leq \binom{j}{2}(t-2)$ (Claim 2 shadow); degenerate lanes $t{=}2$ / $m{=}1$ / $m{=}2$; the all-collinear board ($t=8$, $m{=}3$ threshold 9) stalls at 2 below threshold — the $+1$ has teeth | **PASS** | A8-BOUNDARIES |

**Engine totals: 8/8 stage checks PASS, wall 133.4 s, `AUDIT_ENGINE_GREEN=1`.**

---

## §C THE v2-PARENTS-vs-C COMPARISON (sibling lane W81-107A, `engine107f9`)

Driver: `audit_w81_c_compare.py` (this lane; the C binary is read-only in
the sibling worktree). **Finisher repair**: the first draft packed the
chirotope hex little-endian; the C port reads the `engine107f5v4.py
pack_signs` convention (big-endian zero-padded hex of the bits integer) and
FATAL'd `shear chi mismatch` on every parent. Fixed (`pack_hex`/`unpack_hex`
now match `pack_signs`/`unpack_signs` exactly); the comparison then ran
clean (`receipts107audit_w81_ccompare.txt`):

| layer | content | result |
|---|---|---|
| L1 | parent admission: the C accepts the dumped arrangement-generic realizations, selfcheck = 1, children emitted | **3/3 OK** (0 GENERIC-FAIL) |
| L2 | CELLS: the C's cell count on the same parents vs the python slab-sampler count | **287 == 287 on all 3, C-internal formula check = 1** |
| L3 | S1 CHILDREN: the python deterministic cell-insertion child set (231 canonical keys per parent) ⊆ the C's emitted canonical set | **3/3 OK** (C-only keys 129/113/114 — walk/sweep rng differences, expected and documented) |
| L4 | CANONICAL FORM: every python child chirotope (S1 + full A6 sets, 1214 chirotopes) fed through the C's `--canon-only` mode; C canonical key == python `canonical_key` packing | **1214 agree, 0 disagree** |
| L5 | FULL SET relations (informational): C children 360/344/345 vs python 422/401/391, both ⊇ S1, both certify | consistent (rng differences only) |

**C-COMPARE PASS (exit 0).**

---

## §D DEFECT LEDGER (found + fixed, with file:line)

1. `ALLN_PROOF.md:3–13` — header claimed the W77 engine run was "all
   GREEN"; the raw receipts say **8/13** (three engine-side defects, later
   fixed and re-certified 14/14). **Fixed (W81-107B)**: header now states
   the raw result, the three defects, the re-runs, and points at the
   append-only addendum. Verified against `receipts107alln.txt` /
   `receipts107sharp.txt` by the finisher.
2. `ES_PACKAGE_PROOF.md:219–262` — **$f(4)=5$ upper side, mathematical
   defect**: the finish of the $|H|=3$ case asserted that segments $ab$
   and $pq$ "properly cross" hence form a convex quadrilateral with
   crossing diagonals — FALSE ($a, b$ lie strictly on the SAME side of
   line $pq$ by the 2-1 split, so $ab$ and $pq$ are opposite EDGES).
   **Fixed (W81-107B, verified + machine-shadowed by −F)**: replaced by
   the extremality finish — (α) $\operatorname{conv}\{a,b,q\} \cap
   \operatorname{line}(pq) = \{q\}$ (signed distances $\lambda d(a) +
   \mu d(b) + \nu \cdot 0$ with $d(a), d(b) > 0$), so $p \notin
   \operatorname{conv}\{a,b,q\}$, symmetrically for $q$; (β) $a, b$ are
   hull vertices of $S$, hence extreme, hence not convex combinations of
   the others; all four extreme ⟹ convex position. Machine: 615,714 GP
   5-sets, zero counterexamples; 87/87 2-1-split quadruples convex by both
   codes (A1).
3. `ES_SANDWICH_ALLN.md:55–85` — **slope-separation arithmetic, two
   slips**. (i) The pre-audit display normalized the perturbations by
   $\lvert i-j\rvert$ instead of $\lvert i-j\rvert/4$ (found by W81-107B;
   conservative). (ii) The in-flight repair then printed the false
   equality $2 \cdot (19/48) s\rho = (19/12) s\rho$ — the honest pair
   constant is $19/24$ (found by W81-107B-F). **Fixed (completed by −F)**:
   honest constants throughout — $|\Delta y| \geq d/4 - (19/24)s\rho$,
   $|\Delta x| \leq d/4 + (19/16)\rho$, display
   $\frac{1-(19/6)s\rho/d}{1+(19/4)\rho/d} \geq \frac{1}{1+38\rho} > 1/2 >
   s$, with the exact-algebra bracket
   $38 - \frac{19}{4d} - \frac{19s}{6d} - \frac{361 s\rho}{3d} \geq 38 -
   \frac{19}{4} - \frac{19}{192} - \frac{361}{3 \cdot 32 \cdot 2^{15}} >
   33$ (finisher re-verified exactly; both slips were conservative — the
   final bound was never in doubt, and A3 machine-certifies the real
   construction's measured slopes at every $n = 3..8$). Boundary note
   added: $s \leq 1/64$ iff $n \geq 5$ (audit finding #3).
4. `SHARP_PROOF.md:240–267` — **Lemma VANDERMONDE-DOUBLE prose, two
   slips**. (i) The pre-audit prose subtracted a spurious $t = b-1$ /
   $\binom{b-2}{b-3}$ term mid-derivation (found by W81-107B). (ii) The
   in-flight repair still ran the outer hockey stick to $a+b-4$ and
   closed at $\binom{a+b-3}{b-2} - 1$ — a FALSE intermediate (at
   $a=b=4$: 9 where the sum is 5), papered over by an incoherent Pascal
   close ($\binom{a+b-4}{b-3} = \binom{a+b-4}{a-2}$ is also false; the
   complement is $\binom{a+b-4}{b-2} = \binom{a+b-4}{a-2}$) — found by
   W81-107B-F. **Fixed (completed by −F)**: the stick runs $t = u+b-2 \in
   [b-2, a+b-5]$, loses exactly the single $t = b-3$ term, closes at
   $\binom{a+b-4}{b-2} - 1 = \binom{a+b-4}{a-2} - 1$. The final identity
   and its two-code machine certificate were correct throughout; the
   corrected intermediates are now machine-certified too (A5, both
   binomial codes, all $3 \leq a,b \leq 30$; finisher exhaustive
   re-check to $a,b \leq 60$).
5. `audit_w81_c_compare.py:49–67` — **the comparison script's hex
   convention** (found by −F when running the unrun check): little-endian
   packing vs the C port's big-endian `pack_signs` convention — the C
   FATAL'd `shear chi mismatch` on parent 0 and the comparison could not
   run. **Fixed (−F)**: `pack_hex`/`unpack_hex` now match
   `pack_signs`/`unpack_signs` exactly; #E GENERIC-FAIL lines parsed
   explicitly; dead code removed. C-COMPARE then PASS (§C).

**Verified-clean lanes (no defect):** `ES_PACKAGE_PROOF.md` §2 at the
$k{=}3,l{=}3$ boundary (the three-case extension lemma: base $k{=}2$/$l{=}2$
correctly feeds Bound 1 at $(2,l)$ and Bound 2 at $(k,2)$; at $(3,3)$ the
2-cup $C_1 = (u_1 < v_1)$, the 2-cap $V = (v_1 < v_2)$, and the
$\sigma/\tau$ trichotomy with the GP collinearity trap all specialize
correctly — hand-verified and mechanized in A8) and §7.3 GP-ELIM at the
$N \geq 2$ boundary ($t(S) \geq 2$ well-definedness, Claims 1–4, the
$t{=}2$/$m{=}1$/$m{=}2$ degenerate rows — hand-verified and mechanized in
A8).

---

## §E SEVERITY ASSESSMENT

- Both mathematical defects (D2, D3-ii/D4-ii) were **prose-level**: the
  final stated theorems and their machine certificates were correct
  throughout; in each case the defective text was a derivation step whose
  stated conclusion remained true (and separately machine-certified).
  Both are now repaired with honest derivations, and every repaired step
  carries a fresh two-code machine certificate (A1, A3, A5, A8).
- No defect touched: the ES-SANDWICH theorem statement, the U-BIS closed
  form, the binomial table, the witness family, the comparator solution,
  or any engine receipt of record.
- The audit engine's own first draft (the dead agent's) was correct in
  all 7 of its checks; the finisher's additions (A5's VANDERMONDE-DOUBLE
  lane, A8, the C-compare repair) extend coverage to every lane named by
  the audit brief.

**AUDIT VERDICT: the #107 package is CLEAN — every defect found is fixed,
every fix is machine-certified, every boundary named by the brief is
hand- and machine-verified. The engine never stops; it never lies.**
