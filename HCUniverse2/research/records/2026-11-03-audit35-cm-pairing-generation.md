# AUDIT-35 — certificate scope (independent adversarial audit)
**Task ID**: 35-audit-cert | **Auditor**: fresh agent | **Scope**: certificate + receipts

## Verdict: PASS

Certificate `cm_pairing_generation_round35_checks.py` (765 lines) re-run twice by this auditor:
exit 0, `186 checks passed, 0 failed`, wall 13.2 s / 13.4 s (limit 120 s), peak RSS 45.6 MB (limit
500 MB; also inside the file's own <30 s / <50 MB contract), outputs byte-identical to each other and
to `run1.txt`/`run2.txt`, md5 `b564869f0a1af8b8d9c31fa40b73ead2` = the md5 claimed in the round
record. Every substantive mathematical claim was independently recomputed by different algorithms
and agreed; every hostile control was traced and forced to fire, and sabotage runs prove the checks
have teeth. The findings below are wording/annotation-level only; none conceals a false mathematical
statement.

## Findings

- **F1 — minor (bound annotation false).** Location: py L23–24 (docstring CONTRACT), L267
  (`gaussian_rref_rank` docstring), L312 (inline comment), round record L26 ("matrices ≤ 70×70").
  Issue: the V2 supply matrix for shape `("K",)*8` is **70 rows × 1365 columns** (105 same-field
  matchings × 13 graph-basis choice vectors), not ≤ 70×70; likewise `("K",)*4+("L",)*4` is 36×117 and
  `("K",)*6` is 20×120 (measured by independent reconstruction). The inline claim "npairs ≤ 4 ⇒ ≤ 11
  choices per matching" is also wrong — the choice family has **13** elements at npairs = 4
  (1 all-Γ₁ + 4 single-α + 6 double-α + 1 triple-α + 1 all-α). Rows ≤ 70 and every other stated bound
  (letters ≤ 8, assignments ≤ 256, matchings ≤ 105, instances ≤ 40, zero floats) holds. No
  computational consequence (13 s, 45.6 MB), but the stated bound is false as written.
  Suggested repair: reword to "matrix rows ≤ 70, columns ≤ 1400 (70×1365 worst case)" and
  "≤ 13 choices per matching" in both the py CONTRACT/docstrings and the record's certificate line.
- **F2 — minor (label overstates a weak check).** Location: py L377–380. Issue: the check labeled
  "V2 the two graph classes Gamma_1, Gamma_alpha are independent" only asserts the two hardcoded
  constants are **distinct** (`not (g1[0]==ga[0] and g1[1]==ga[1])`). Garbage test: the predicate
  PASSES on the Q-**dependent** pair (1,0),(2,0) — so it is not an independence test. The underlying
  claim is nonetheless true ({(1,0),(0,1)} is the standard Q(i)-basis; exact realified rank = 2,
  confirmed in the recompute), so no false statement is concealed.
  Suggested repair: replace with `gaussian_rref_rank([[(1,0),(0,1)]]) == 2` (a genuine rank-2 test).
- **F3 — minor (by-construction checks).** Location: py L522–543 (V4 trials). Issue: the 90 per-trial
  `ok()` calls are true **by construction**: base words are built as same-field pairs, the graft
  appends a same-field pair (even + 2 stays even), and a same-field perfect matching always exists
  once all per-field counts are even — so the third check adds nothing beyond the second. They test
  implementation plumbing, not mathematics. The round record is honest about the level ("Letter-level
  shadow: V4 (30/30 grafts)"), so no false claim; content is simply shallow.
  Suggested repair (optional): assert something with content, e.g. that the transported word's supply
  rank (V2 machinery) equals the base word's rank + graft dimension.
- **F4 — minor (one hostile, ten times).** Location: py L544–553. Issue: the cross-field hostile loop
  runs the **same** case — base `("K","K")`, graft `("K","L")` — ten identical iterations (no rng
  consumed). It does fire and does discriminate (see hostile-fire results), but coverage is one
  instance, not ten. Suggested repair: vary base/fields across iterations.
- **F5 — minor (range of the generic-span check).** Location: py L492–498. Issue: the generic
  (non-CM) pairing-span rank = Catalan identity is checked only at p = 2, 3, while the V3 docstring
  text states it generically; p = 4 (8 letters, 256×105 exact matrix) is feasible but skipped. The
  record's own V3 claim (the surplus values 4/15/56) is checked for all p = 1..4.
  Suggested repair: add p = 4 or scope the wording to "at the committed generic shapes p = 2, 3".
- **F6 — observation (brief/artifact label mismatch, no defect in the artifacts).** The audit brief's
  section map says "V6 = the surplus C(2p,p)−Catalan_p = 4/15/56"; in the file, the tex §6, and the
  docstring, the surplus receipts are **V3** (py L441–443) and **V6** is the hostile battery. The
  record makes no per-section content claim ("Sections V1–V6 as in the derivation §6"), so nothing in
  the audited artifacts is mislabeled. Also verified: seed 0xFEEDFACECAFEBEEF is unique in the
  campaign tree (0x9E3779B97F4A7C15 occurs in this file only as the zero-seed fallback guard).

## Garbage tests / hostile-fire results / recompute results

**Garbage tests (certificate's own predicates, nonsense input):** all reject garbage —
`word_balance_ok(("K","L","Q"))=False`, `(("K",))=False`, `(("K","K"))=True`;
`|balanced_assignments(("K","K","K"))|=0`, `(("A","B"))=0`, `(("Q","Q"))=2`, `(("K",)*4)=6`,
`(("K","K","L","L"))=4`; `constant_term_laurent(("K","K","K"))=0`. The one check that survives
garbage is F2's "independence" predicate (passes on the dependent pair (1,0),(2,0)) — see F2.

**Hostile-fire results (traced AND executed on the certificate's own code):**
- V4 cross-field hostile (record: "Hom⁰ = 0 transports nothing"): hostile input
  `graft(("K","K"),("K","L"))` → word `("K","K","K","L")` → same-field matchings = **0** → hostile
  FIRES (transports nothing); `cross_ok` stays True so the check passes *because* the hostile behaved
  as predicted. Benign input `("K","K")+("K","K")` → 3 matchings → `cross_ok` = False → the check
  itself FAILS: the control discriminates. Sabotage run S2 (hostile defused to same-field in a doctored
  copy): exit 1, `FAIL: V4 hostile: cross-field graphs transport NOTHING (Hom^0 = 0 fires)`.
- V6-H1 unbalanced word ("K","K","K"): `cm_supply_rank` = (rank 0, dim 0) → FIRES; fed a balanced
  word ("K","K") it returns rank 2 ≠ 0 → discriminates.
- V6-H2: of the 3 perfect matchings of 4 letters with fields ("K","K","L","L"), exactly **2** are
  cross-field and **1** same-field — both hardcoded expectations verified; a same-field-only field
  tuple would break them.
- V6-H3 fake CM: exhaustive check over all 14 nonempty proper subsets of {0,1,2,3}: **every** partial
  sign-flip breaks some balanced assignment (the control is mathematically forced to fire, rng or
  no rng); the global flip preserves all 6 balanced assignments.
- V6-H4/H5: 3-letter balanced count = 0 (≠ 5, fires); Laurent CT = 0; graft length 4 (≠ 5, fires).
- Sabotage runs of doctored copies (failure path exercised): S1 published arity total m=1 changed
  4→5: exit 1, 3 FAILs (V5.a/b/c). S3 expected surplus 15→16: exit 1, FAIL. S4 supply restricted to
  Γ₁-only (α-graphs deleted): exit 1, **12 V2 FAILs** — rank collapses to 1/3/10/35 at 2/4/6/8
  letters vs dims 2/6/20/70, i.e. the CM α-structure is load-bearing and the V2 rank identity has
  real teeth.

**Recompute (independent, `/tmp/audit35_recompute.py`, 2.0 s, algorithms different from the file's):**
- (a) Surplus C(2p,p) − Catalan_p: **Pascal-triangle binomial + brute-force Dyck-path enumeration**
  (file used comb + product/hook/recurrence formulas): 2p=4 → 6−2 = **4**; 2p=6 → 20−5 = **15**;
  2p=8 → 70−14 = **56**. MATCH with the claimed 4/15/56.
- (b) V5 arity totals: object read from V5's code = dim of the invariants of the signed exterior
  algebra Λ*(Z^{2m}) under the cyclic deck σ:(b,t)↦(b+1 mod m, t). Independent method:
  (1/m)Σ_j det(I + P_{σ^j}) with **exact integer Bareiss determinants** (file used the cyclotomic
  character formula and the 2^{2m}-subset signed character sum): m=1..5 → **4, 8, 24, 64, 208**
  (MATCH, all five), m=6 → **688** (matches the file's two-internal-algorithm agreement control).
- (c) V2 rank identity (rank of the Γ₁/Γ_α matching-product supply = balanced-assignment dimension):
  my own construction of the supply (independent code, certificate's restricted 13-choice family),
  ranked by **modular elimination** over GF(998244353) with i↦√−1, over GF(1000003²), and over
  GF(1000000097), plus **exact-Fraction doubled-column realification** (rank_Q = 2·rank_Q(i)) on four
  shapes (file used exact Q(i) RREF):
  `("K",)*2`: dim 2, ranks 2/2/2/2 · `("K",)*4`: dim 6, ranks 6/6/6/6 · `("K",)*6`: dim 20, ranks
  20/20/20/20 · `("K",)*8`: dim 70, ranks 70/70 (matrix 70×1365) · `("K","K","L","L")`: dim 4, ranks
  4/4/4/4 · `("K",)*4+("L",)*4`: dim 36, ranks 36/36 (matrix 36×117). Dims also confirmed by the
  closed form Π_f C(m_f, m_f/2). All AGREE — rank = dim at every committed shape; the full
  2^{npairs}-choice family gives the same ranks. V3's generic-side span independently re-ranked mod
  two primes: p=2 → rank 2 = Catalan 2, p=3 → rank 5 = Catalan 5 (MATCH).
- Check-count breakdown reconciled to the claimed 186: V1 22 + V2 15 + V3 23 + V4 91 + V5 24 +
  V6 10 + vacuity-scan 1 = 186; runtime confirms `186 checks passed, 0 failed`.
- Determinism is robust: two runs in separate processes (per-process string-hash randomization) are
  byte-identical, so no output depends on set-iteration order.

## Mechanical scan raw output

Patterns scanned (code only, docstring/comments stripped): `or True`, `and False`, `ok(True`,
`is not None`, self-comparison `X == X` (any line, and the file's own 3-line-after-assignment scan),
`is True` sites, float literals/`float(`/transcendental math. Raw hits:
```
or True / and False / ok(True / is not None (code lines only):
  L28: (docstring) "fail (no `or True`, no self-comparison ...)"        [docstring — excluded]
  L724/725: scan's own pattern definitions                              [scan machinery — excluded]
self-comparison X == X (code lines): none
float literals / float( / math.sqrt|sin|cos|exp|log / 1e±: none
  (divisions present: L132,L480 Fraction/Fraction exact; L399,L414,L576,L618 integer //)
`is True` sites: L552 ok(cross_ok is True ...) | L701 ok(fake_cm_breaks is True ...)
  | L705 ok(global_flip_preserves is True ...) — genuine loop-computed booleans, all CAN fail
  (L552 proven to fail under sabotage S2; L701 mathematically forced — see hostile-fire results)
```
Ledger-092/107 classes: **none present**; the file's self-scan ("CLEAN") agrees with this
auditor's independent scan. No tautological predicate sums beyond the by-construction V4 trials (F3).

## Required repairs before claiming success: [ ] ...

- [ ] **None blocking** — the mathematical content of the certificate and the record's substantive
  claims (186/0/exit 0, deterministic md5, V2 rank identity, surplus 4/15/56, arity totals
  4/8/24/64/208, hostile fires) are all true and independently verified. Verdict: PASS.
- [ ] *(recommended, wording)* F1: correct "matrices ≤ 70×70" → "rows ≤ 70, columns ≤ 1400
      (70×1365 worst case)" in the py CONTRACT (L23–24, L267) and record L26; "≤ 11 choices" → "≤ 13".
- [ ] *(recommended, check strength)* F2: replace the distinctness-only "independence" check with a
      genuine rank-2 test of {Γ₁, Γ_α} via `gaussian_rref_rank`.
- [ ] *(optional)* F3/F4/F5: deepen V4 (content-bearing assertion; vary the single hostile case),
      add p=4 to the generic span or scope its wording to p = 2, 3.
