# WORKLOG_W81_107B.md — the W81-107B audit lane, dispatched and died, sealed by the finisher

Task ID: W81-107B (auditor/doubler lane, problem #107 Happy Ending), branch
`w81-107b`. The W81-107B dispatch died mid-mission after banking
substantial work: four proof docs modified with audit fixes in flight, the
auditor engine `engine107audit_w81.py` (7/7 PASS on its own run), the dump
`audit_w81_v2parents.json`, and an unrun comparison script
`audit_w81_c_compare.py`. Finisher **W81-107B-F** recovered the lane,
verified every in-flight fix with adversarial duty, completed the two that
were still defective, added the missing machine lanes, ran the unrun
comparison, sealed the audit document, extended the official comparator
gate, and pushed. Zero work lost.

---

## §1 THE RECOVERED STATE (what the dead agent left)

- Dirty diffs on 4 docs: `ALLN_PROOF.md` (+8/1: header honesty),
  `ES_PACKAGE_PROOF.md` (+36/31: the §5 $f(4)=5$ upper-side repair),
  `ES_SANDWICH_ALLN.md` (+22/5: slope-separation re-derivation + the
  $s \leq 1/64$ iff $n \geq 5$ boundary note), `SHARP_PROOF.md` (+19/17:
  the §4 VANDERMONDE-DOUBLE prose repair).
- `engine107audit_w81.py` (fresh-code auditor: own order types, own two
  convexity codes, own cup/cap DP, own construction rebuild) with
  `receipts107audit_w81.txt`: 7/7 PASS, `AUDIT_ENGINE_GREEN=1`, wall 154 s.
- `audit_w81_v2parents.json` (3 seeded-random $n=8$ parents re-run through
  the campaign v2 machinery, cells 287, fingerprints
  `6b276e021de358ec` / `739be4fc8a4829b7` / `6cf8c58eb310e29c`).
- `audit_w81_c_compare.py` — **never successfully run** (its first
  execution FATAL'd in the C port; see §2 defect D5).

## §2 THE FINISHER'S ADVERSARIAL PASS (defects found + fixed)

The mission brief named five areas to verify. Verdicts:

1. **ES_PACKAGE_PROOF.md §2, the three-case extension lemma at the
   $k{=}3,l{=}3$ boundary — CLEAN, no defect.** Hand-verified: the base
   $k{=}2$/$l{=}2$ rows correctly feed Bound 1 at $(2,l)$ and Bound 2 at
   $(k,2)$; at $(3,3)$ the 2-cup $C_1 = (u_1 < v_1)$, the 2-cap
   $V = (v_1 < v_2)$, the $\sigma/\tau$ trichotomy and the GP
   collinearity trap all specialize correctly; the Pascal closure
   $\binom{1}{1} + \binom{1}{0} = \binom{2}{1}$ closes the induction.
   Then **mechanized** (new engine lane A8): the statement at
   $(3,3)/(3,4)/(4,3)$ on 5444/17720/17720 threshold-size GP x-distinct
   grid subsets (0 violations, own DP + brute chains agreeing), the
   $(3,3)$ X/Y-split + trichotomy mechanism on all 5444 GP x-distinct
   3-sets, and the $E(k,l)$ tightness (the bound exact in both
   directions).
2. **The slope-separation arithmetic — the dead agent's repair was
   INCOMPLETE; finished.** The in-flight fix corrected the
   normalization slip (perturbations divided by $|i-j|$ instead of
   $|i-j|/4$) but printed the false equality $2 \cdot (19/48) s\rho =
   (19/12) s\rho$ (honest pair constant: $19/24$; the repair's value was
   $2\times$ too big — conservative, so the final bound survived, but
   the displayed arithmetic was false). Completed at
   `ES_SANDWICH_ALLN.md:55–85`: honest constants ($19/24$ pair, $19/6$
   normalized), the E-set box justification ($E \subseteq [0,24/23]
   \times [0,18s/23]$, offset past both midpoints), and the exact-algebra
   bracket $38 - \tfrac{19}{4d} - \tfrac{19s}{6d} - \tfrac{361 s\rho}{3d}
   \geq 38 - \tfrac{19}{4} - \tfrac{19}{192} - \tfrac{361}{3 \cdot 32
   \cdot 2^{15}} > 33\rho$ — re-derived by the finisher in exact
   arithmetic and machine-shadowed by A3 (measured slopes on the real
   construction at every $n = 3..8$).
3. **The GP-ELIM $N \geq 2$ boundary — CLEAN, no defect** (the W73
   correction stands as written). Hand-verified ($t(S) \geq 2$
   well-definedness, Claims 1–4, the $t{=}2$/$m{=}1$/$m{=}2$ degenerate
   rows) and mechanized in A8: 114 greedy extractions at/above the exact
   measured-$t$ threshold on planted-collinearity boards (all reached
   $m$), the per-stage forbidden census $\leq \binom{j}{2}(t-2)$, and the
   all-collinear board ($t = 8$, $m{=}3$ threshold 9) stalling at 2 —
   the $+1$ has teeth.
4. **The binomial table (SHARP_PROOF.md §4 VANDERMONDE-DOUBLE) — the
   dead agent's repair was STILL WRONG; fixed.** The pre-audit prose had
   a spurious $t{=}b{-}1$ subtraction; the in-flight repair removed it
   but introduced/kept an **off-by-one**: the outer hockey stick ran to
   $a+b-4$ and closed at $\binom{a+b-3}{b-2} - 1$ — a FALSE intermediate
   (at $a{=}b{=}4$: reads 9, true sum 5), with an incoherent Pascal
   close ($\binom{a+b-4}{b-3} = \binom{a+b-4}{a-2}$ is false; the true
   complement is $\binom{a+b-4}{b-2} = \binom{a+b-4}{a-2}$). The final
   identity and its two-code machine certificate were correct
   throughout. Fixed at `SHARP_PROOF.md:240–267`: the stick runs
   $t = u+b-2 \in [b-2, a+b-5]$, loses exactly the $t = b-3$ term,
   closes $\binom{a+b-4}{b-2} - 1 = \binom{a+b-4}{a-2} - 1$. The
   corrected inner/outer/final identities are now machine-certified
   (A5, both binomial codes, all $3 \leq a,b \leq 30$; finisher
   exhaustive re-check to $a,b \leq 60$).
5. **$f(4) = 5$ both directions — the dead agent's repair is CORRECT;
   verified and machine-shadowed.** The old finish ("segments $ab$ and
   $pq$ properly cross") was genuinely FALSE ($a,b$ on the same side of
   line $pq$ makes them opposite edges); the repair's extremality
   finish — (α) $\operatorname{conv}\{a,b,q\} \cap \operatorname{line}(pq)
   = \{q\}$, (β) hull-vertex extremality of $a,b$ — is correct
   (finisher hand-proof), and A1 re-proves the mechanism in code:
   615,714 GP 5-sets swept with 0 lacking a convex 4 (both codes),
   31,888 GP 4-sets with no convex 4 (the lower side), 87/87 2-1-split
   quadruples convex by both codes, the banked 4-point witness verified.

Plus one defect **in the audit tooling itself** (D5): the unrun
`audit_w81_c_compare.py` packed the chirotope hex little-endian while the
C port reads the `engine107f5v4.py pack_signs` big-endian convention —
the C FATAL'd `shear chi mismatch` on the first parent. Fixed
(`pack_hex`/`unpack_hex` now match `pack_signs`/`unpack_signs` exactly;
#E GENERIC-FAIL lines parsed explicitly; dead code removed); the
comparison then ran clean.

## §3 ENGINE RESULTS (final state)

`engine107audit_w81.py --stage verify`: **8/8 stage checks PASS, wall
132–133 s (budget 480 s), `AUDIT_ENGINE_GREEN=1`**
(`receipts107audit_w81.txt`):

| check | result |
|---|---|
| A1-OTF4 | $f(4)=5$ both directions: 615,714 GP 5-sets, 0 without convex 4; 31,888 GP 4-sets without convex 4; OT anchors 2/3; 87/87 2-1-split quadruples convex both codes; W4 witness ✓ |
| A2-W5WITNESS | both banked 8-point witnesses: GP, 56/56 subsets non-convex both codes, hull 4/4 |
| A3-SANDWICH-N3..N8 | construction rebuilt $n = 3..8$: sizes $2^{n-2}$, cluster sizes, GP, y-bands, exact slope separation, Lemma M; **no-convex-$n$ exhaustive both codes at $n = 6$ (8008) and $n = 7$ (3,365,856)**; $n=8$: 60k random + 400 hillclimbs, best hull 7, 0 convex-8; convex-$(n{-}1)$ transversal witnesses; audit finding #3 ($s \leq 1/64$ iff $n \geq 5$) quantified |
| A4-UBIS | closed form $n=3..11$ = [4, 16, 64, 244, 914, 3420, 12856, 48604, 184738], two binomial codes $n=3..30$, U-BIS ≥ ES-ALLN-SHARP, 16-pt/64-pt instances, label census |
| A5-BINOMTABLE | table $n=3..30$ two codes, anchors [3,7,21,71,253,925], gap ratios §6, sharpening recursion, **+ VANDERMONDE-DOUBLE inner/outer/final identities (the repaired prose)** |
| A6-V2RERUN | 3 parents re-run (cells 287, children 422/401/391, deterministic fingerprints), dump refreshed |
| A7-NEGCONTROLS | all six controls behave (planted convex-5, hexagon, collinear, corrupted U-BIS, translated cluster, DP-vs-brute) |
| **A8-BOUNDARIES** (new, finisher) | the two brief-named boundary lanes: CC three-case at $(3,3)/(3,4)/(4,3)$ — 5444/17720/17720 sets, 0 violations, mechanism on 5444 3-sets, $E(k,l)$ tightness; GP-ELIM — 114 greedy extractions, census, degenerate lanes, all-collinear stall |

`--stage gate` (comparator battery, cache-independent): 7/7 stage checks,
12 PASS lines, wall ~37 s.

## §4 THE v2-PARENTS-vs-C COMPARISON (`receipts107audit_w81_ccompare.txt`)

Against the sibling W81-107A C port `engine107f9` (read-only), after the
hex repair: **L1** 3/3 parents accepted (selfcheck 1, 0 GENERIC-FAIL);
**L2** cells 287 == 287, C formula check 1; **L3** the python S1 child
set (231 canonical keys) ⊆ the C's emitted set on all 3 parents (C-only
keys 129/113/114 — walk/sweep rng differences, expected); **L4** canonical
forms: **1214 chirotopes agree, 0 disagree**; **L5** full-set relations
consistent. **C-COMPARE PASS (exit 0).**

## §5 THE OFFICIAL GATE

`comparator-official/challenges/107/driver.py` extended with
**S-AUDIT-W81** (subprocess `engine107audit_w81.py --stage gate`; PASS =
exit 0 + ≥ 8 PASS lines + 0 FAIL + receipts sealed `AUDIT_ENGINE_GREEN=1`).

Run: `python3 official_gate.py 107` →

```
CHECKS: 15/15 passed (official=2, solution=9, controls=4)
WALL: 42.38s
VERDICT: YOUR SOLUTION IS OKAY
```

(was 14/14 before this lane; every prior check unchanged and green.)

## §6 COMMIT LEDGER (this lane, branch `w81-107b`)

| commit | content |
|---|---|
| `accc6a6` | (1/4) the audit-seal core: 4 doc fixes verified/completed (2 residual defects fixed by the finisher), engine extended to 8/8 (new A8 + A5 VANDERMONDE-DOUBLE lane), receipts, v2parents dump, the repaired c_compare + its receipt |
| `799a71b` | (2/4) `AUDIT_W81.md` — the verdict table, defect ledger D1–D5 with file:line, verification table A1–A8, the C-comparison results, severity assessment |
| `e9af674` | (3/4) comparator: S-AUDIT-W81 in the 107 driver + the 15/15 gate receipt + the post-gate full-verify receipts refresh |
| (this commit) | (4/4) the worklog |

## §7 HONEST RESIDUALS

- None open. Every defect found in this audit is fixed and carries a
  fresh two-code machine certificate; every boundary named by the brief
  is hand- and machine-verified; no "open" label was placed on any
  shipped claim.
- The receipts file `receipts107audit_w81.txt` is rewritten by each run
  (documented engine behavior): the banked state is the full
  `--stage verify` record; a comparator gate run temporarily rewrites it
  to the gate record (identical verdicts, sampled $n=7$ code B).
- The C-comparison's L5 layer documents (not fails) the walk/sweep rng
  differences between the python and C full child sets — S1, the
  deterministic layer, agrees exactly on all parents.

The dispatch died; the finisher landed everything. The engine never
stops; it never lies.
