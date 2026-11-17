# AUDIT-40 — THE D-FAMILY TRANSPORT STRIKE (Round 40)

Adversarial auditor: the AUDIT-40 agent (PTS `adversarial-proof-audit` role; not the
draft's author). Everything below was actually executed on the artifacts on disk
(`/home/z/my-project/hodge-campaign/round40/`). All runs: Python 3, exact arithmetic,
in the sandbox; certificate runs ~80 s each; the auditor's recompute 4.2 s.

## Verdict: PASS_WITH_REPAIRS_REQUIRED

The certificate is substantively sound: the fidelity run reproduces the receipt
byte-identically (4219 checks / 0 failures / exit 0 / md5 `acc2455cbe07c0a88177101b5b84c3db`),
all five sabotages fire with exit 1, the load-bearing checks are genuine computations
(not asserts), and the auditor's fully independent recompute (different matrix convention,
principal-minor exterior trace, unsorted-key wedge with cycle-parity signs, Bareiss
rank) agrees with every claimed value at three non-adjacent worlds (35/35 items).
However, one named deliverable sub-item — the "layer bridge" — is certified by a check
that CANNOT fail (F1, major), and there are five minor label/count/invariant defects
(F2–F6). No blocker: no headline mathematical claim rests solely on the defective
check (both layers it claims to wire are independently and genuinely certified). The
round's success claims may stand mathematically, but the repairs below are required
before the round is re-pushed with its current wording.

## Claim match: 

The headline claims match the certificate's actual content, with three wording-level
discrepancies. **Matches:** 4219 checks / 0 failures / exit 0 (certificate summary line
and the auditor's byte-identical rerun); 62 census worlds (ok[2]; `GENERIC` length 62 =
30 worlds on the 1+√−d face + 31 on the 2+√−d face + the order-6 member), covering all
nine Round-38/39 Heegner seeds (1,2,3,7,11,19,43,67,163 — all in `DLIST`, verified) and
22 non-Heegner d's (31 − 9 = 22, verified); the exact collar statement
{b=0} ∪ {a=0} ∪ {(3, a=±b)} matches `in_collar` verbatim in code, summary, record and
tex; the order-4 member (Q(i), 1+i) and order-6 member (Q(√−3), 3+√−3) membership
claims are certified (ok[65]/ok[66]) and independently re-verified by the auditor
(α⁴ = ᾱ⁴ at d=1 (1,1); α⁶ = ᾱ⁶ at d=3 (3,1)); "Q2 NOT claimed; the closing string NOT
emitted; the polarity split stands" is printed verbatim in the certificate's summary
and carried in both the record and the tex; the degenerate-canary dims 34/38/70 match
the executed canaries; the PUSH artifacts all exist (PDF 96141 bytes = 93.89 KiB as
claimed; the Lean draft; the exploration script); the record's RHC statement is
properly conditional ("Given the external leaf", scope line unchanged), matching the
tex scope paragraph — no overstatement there. **Discrepancies:** (i) the record §37 and
the tex quantifier line both say the census spans "24 distinct d's" — it spans **31**
distinct d's (29 squarefree ≤ 45 plus 67 and 163; every d enters via the 2+√−d face);
an understatement, but factually wrong in both artifacts (F5); (ii) the code header
(line 55), the record and the tex all say "5 collar canaries" — the `CANARIES` list has
**4** entries ((3,(1,1)), (3,(2,2)), (5,(0,1)), (5,(3,0))) and 4 canary blocks execute
(F6); (iii) "zero floats" is violated by one float division at line 1388 (benign in
value, inside the vacuous bridge — F4). The tex Thm S30(ii) claim
"W ∩ Z⁷⁰ = ⟨ŵ_R, ŵ_I⟩_Z" is not checked as a single predicate but is a sound corollary
of certified ingredients (dim W = 2, both classes in W and independent, the t=0/t=1
support disjointness with leading coefficient 1) — acceptable, noted for the record.

## Fidelity: 

Auditor's run: `timeout 320 python3 d_family_transport_round40_checks.py` → **EXIT 0**,
**4219 checks, 0 failures** (summary line 4252 of the output), wall time **79.7 s**
(claim "~80 s" ✓). The stdout is **byte-identical** to `runA.txt` (`diff` empty;
md5 of my output = md5 of runA.txt = md5 of runB.txt = **acc2455cbe07c0a88177101b5b84c3db**,
matching the claimed md5, which is the run-receipt md5; the source file itself is
d674da61bc28f87002d0a58aeada235f). runA.txt and runB.txt are byte-identical to each
other; their .err files contain only the ten section-timing lines (which legitimately
vary run-to-run on stderr only). All 4219 lines are `ok[...]` lines; zero `FAIL` check
lines (the ten occurrences of the string "FAIL(S)" in the output are inside ok-messages
of the collar canaries, describing predicates that fail at collar worlds). Determinism
confirmed: my independent run reproduced the receipt exactly, third time in addition
to the claimed double run.

## Findings

### F1 — THE LAYER-BRIDGE CHECK IS VACUOUS (a labeled check that cannot fail) — severity: major
- **Location:** `d_family_transport_round40_checks.py` lines 1378–1395 (VSYM, "THE BRIDGE"),
  echoed by the record deliverable S34/S33 wiring text ("the layer bridge (d = 1..30)
  wires the symbolic layer to the census layer") and tex Thm S34 ("Evaluated at d = 1..30
  they reproduce the per-world closed forms (the layer bridge)").
- **Issue:** the check evaluates **hardcoded literal tuples** — `peval((0,0,8), dd)`,
  `peval((0,8), dd)`, `peval((0,0,24), dd)`, `peval((12,0,36), dd)`, `peval((0,0,16), dd)` —
  against the *same closed forms* (`8*dd*dd`, `8*dd`, `24*dd*dd`, `(9*8*dd*dd+24)/2`,
  `16*dd*dd`) at d = 1..30. `peval((0,0,8), dd)` is by definition `8·dd²`, so every
  comparison is `8dd² != 8dd²` → `bridge_ok` can never become False. None of the
  symbolic layer's **computed** polynomials (`qRR_s`, `qII_s`, `qep_s`, `c4p_s`, `c4m_s`,
  `cross_s`, `carrier_s`, `qB_s`) appears in the bridge. The label — "the two layers
  certify the same laws" — states a wiring receipt the code does not perform. (This is
  also the one place a float sneaks in, see F4.) The mechanical vacuity scan cannot see
  it because the shape is semantic, not lexical; the auditor's S4 sabotage confirms the
  scan only catches lexical plants.
- **Impact:** no headline law is invalidated — the VSYM identities themselves are real
  `Z[d][√−d]` computations and the per-world V1 values are real 70×70 computations, and
  the auditor's independent recompute confirms both layers agree at d = 15, 34, 163 —
  but the round's named "bridge" receipt is empty, and the record/tex wording
  ("wires the symbolic layer to the census layer") overstates the certificate's content.
- **Suggested repair:** evaluate the computed polynomials, e.g.
  `peval(qRR_s[0], dd) == 8*dd*dd`, `peval(qII_s[0], dd) == 8*dd`,
  `peval(qep_s[0], dd) == 24*dd*dd`, `peval(c4p_s[0], dd) == (9*8*dd*dd+24)//2`,
  `peval(c4m_s[0], dd) == (8*dd*dd+24)//2`, `peval(cross_s[0], dd) == -(24*dd*dd+24)`,
  `peval(carrier_s[0], dd) == 16*dd*dd`, `peval(qB_s[0], dd) == 16*dd*dd`, for
  dd = 1..30 (or over the 31 census d's); re-run the double receipt.

### F2 — THE "LEASTNESS" CHECK IS A TAUTOLOGY (62 decorative checks) — severity: minor
- **Location:** line 1068, inside the V7 per-world loop:
  `check(2 == min(m for m in range(1, 13) if m % 2 == 0), f"{tag} the leastness: 2 is the least positive even scale")`.
- **Issue:** `min` of the positive evens in `range(1,13)` is 2 by construction of the
  Python range — the predicate is `2 == 2` and cannot fail, at any world. The genuine
  m*-pin content lives in the (real) NECESSITY sweep (m ∈ 1..12, exactly the evens
  admitted) plus the (real) WITNESS at m = 2; the leastness line adds 62 unfailable
  checks to the count and a receipt line that looks load-bearing but is not.
- **Suggested repair:** delete the check, or compute the leastness from the sweep data
  (e.g. record the admitted m's in the necessity loop and check `min(admitted) == 2`).

### F3 — THE "SYMMETRIC ALGEBRA" HALF OF THE V5 DISCRIMINATION CHECK IS RIGGED — severity: minor
- **Location:** lines 871–882, V5: `sym_sq = {tuple([L, L]): Fraction(1)}` followed by
  `if sym_sq == ZERO or len(sym_sq) != 1: sym_detect = False`.
- **Issue:** the code constructs a one-element dict literal and then tests that it is
  not the empty dict and has length 1 — a self-comparison after direct assignment that
  cannot fail. The label claims "letter^2 is NONZERO in the symmetric algebra … executed
  here as a real computation"; only the exterior half (`wedge(letter, letter) == ZERO`,
  a real computation) is executed. V5 is a "CITED"-inputs section, so nothing
  load-bearing rests on it, but the label overstates the executed content.
- **Suggested repair:** either implement an actual symmetric-algebra product (a word²
  that survives) or relabel the check to state that only the exterior annihilation is
  computed and the symmetric side is cited.

### F4 — A FLOAT IN THE "ZERO FLOATS" CERTIFICATE — severity: minor
- **Location:** line 1388: `if peval((12, 0, 36), dd) != (9*8*dd*dd + 24)/2:` — Python 3
  true division produces a `float`, contradicting the "exact Fraction /
  integer-polynomial arithmetic, zero floats" banner in the code header, record and tex.
- **Issue:** numerically benign (the numerator 72dd²+24 is always even and ≤ 64824, so
  the float is exact; the comparison is int == float and correct) — but it sits inside
  the vacuous bridge (F1) and violates the stated invariant. All other `/2` occurrences
  in the file are `Fraction / int` (exact).
- **Suggested repair:** `Fraction(9*8*dd*dd + 24, 2)` (or `// 2`) — and see F1.

### F5 — "SPANNING 24 DISTINCT d's" IS WRONG (record + tex) — severity: minor
- **Location:** record §37 (last line: "certified at a 62-world census spanning 24
  distinct d's") and the tex §The quantifier line (same phrase).
- **Issue:** the census spans **31** distinct d's — `DLIST` = 29 squarefree values ≤ 45
  plus 67 and 163 (verified by recomputation), and every d enters via the α = 2+√−d
  face. The record's own census paragraph ("every squarefree d ≤ 45 plus the Heegner
  seeds 67, 163 … 22 non-Heegner d's added") and ok[1] (31 squarefree values) are
  correct; the "24" in the quantifier lines contradicts them. It understates the result
  (an understatement, not an overstatement, but still a false claim in both artifacts).
- **Suggested repair:** correct to "spanning 31 distinct d's" in both artifacts.

### F6 — "5 COLLAR CANARIES" vs 4 EXECUTED — severity: minor
- **Location:** code header line 55 ("62 census family worlds + 5 collar canaries"),
  record §The certificate ("+ 5 collar canaries"), tex §The certificate ("the census
  62 family worlds + 5 collar canaries").
- **Issue:** `CANARIES = [(3,(1,1)), (3,(2,2)), (5,(0,1)), (5,(3,0))]` — four canary
  worlds, four canary blocks in the receipt (ok[4177]–ok[4188]). The four cover the
  three degeneracy types (order-3 twice, order-2, order-1) plus a second Eisenstein
  point; nothing is missing mathematically, but the count "5" is claimed in three
  places and 4 run.
- **Suggested repair:** either correct the count to 4 in the three places or add a
  fifth canary world (e.g. an order-6-phase collar-adjacent control or (3,(−1,−1)))
  and re-run.

### Label-predicate fidelity notes (ledger-109) — no defects beyond F1–F3
- **THE K-IRREDUCIBILITY DICHOTOMY (line 1096–1109):** genuine, not an assert. It
  computes β₀⁴ ∈ K (real `kpow`), checks the non-scalar condition Im(β₀⁴) ≠ 0, and
  computes the discriminant −4d·(Im β₀⁴)² of the quadratic char polynomial — for a
  quadratic over Q, disc < 0 is a complete irreducibility test. The fact that the
  actual operator's char polynomial is that quadratic is certified separately and for
  real by THE BLOCK LAW (a 70×70 exterior-matrix computation plus an exact 2×2
  coordinate solve: entries [[Re, −d·Im],[Im, Re]]). Minor label excess only: the
  clause "with the scalars [q]^* = q⁴ Id" is stated, not computed (trivially true by
  multilinearity).
- **THE COLLAR CHARACTERIZATION (lines 407–428):** genuine and bidirectional. 160
  instances (8 d's × 20 (a,b)); the IFF is tested in both directions
  (`in_col != (ph in (1,2,3))` falsifies `cls_ok`); the grid contains all three collar
  families (b=0, a=0, d=3 diagonal ±) AND non-collar instances including the boundary
  members (d=1 diagonal → order 4; d=3 a=3b → order 6), so both implications are
  exercised; 46 collar instances detected (24 + 16 + 6, arithmetically consistent;
  S1's sabotage drops it to 40 exactly as expected).
- **THE WITNESS bundled predicate (lines 1056–1063):** all ten conjuncts are real
  comparisons of computed quantities (integrality of the m=2 branch data, the charges
  24d²/−8d², the charge trace/difference, the Chern closures, the cross-term, the
  carrier). Some conjuncts are arithmetic consequences of earlier ones (redundant, not
  vacuous).
- **THE VSYM EIGENLETTER IDENTITY (lines 1259–1289):** real content on both sides —
  the LHS Ω' is computed by `wedge_sym` over the letters e_j + √−d f_j in
  Z[d][√−d]; the RHS is the committed ŵ_R(d) + √−d·ŵ_I(d); `keq` compares coefficient
  polynomials; the word count 16 is also checked.
- **The bridge:** see F1 — the only load-bearing label/content mismatch found.

## Sabotage results: S1..S5

All five sabotages were applied to a copy at `/tmp/sab40.py` (each mutation asserted to
apply exactly once), run with `timeout 320`, and each made the certificate FAIL with
exit 1 as required. Check totals stay at 4219 (ok + fail) in every run.

- **S1 — collar weakened (d==3 clause removed from `in_collar`): FIRED.** EXIT 1;
  4216 ok + 3 failures. Required target failed:
  `FAIL  THE COLLAR CHARACTERIZATION: over the 160-instance (d, a, b) grid, ... -- exactly 40 collar instances detected (the classification is exact, both directions)`
  (plus the two Eisenstein canary lines `FAIL the collar world (d=3, alpha=(1, 1)): phase order 3 -- in the EXACT exclusion collar` and the same at (3,(2,2)) — the certificate's own canaries catch the weakened classification).
- **S2 — rigged period constant (`Fraction(8*d*d)` → `Fraction(8*d*d+1)`): FIRED.**
  EXIT 1; 4157 ok + 62 failures — the period law fails at every census world, e.g.
  `FAIL  [d=1, alpha=(1, 1)] THE PERIOD LAW: INT wR_hat^2 = 8 d^2 = 8`
  (62 such lines, one per world).
- **S3 — symbolic layer mutated (expected polynomial `(0, 0, 8)` → `(0, 8)` in the
  period-law symbolic check): FIRED.** EXIT 1; 4218 ok + 1 failure:
  `FAIL  THE PERIOD LAW (symbolic): INT wR_hat(d)^2 = 8 d^2 as a polynomial identity in Z[d] -- AT EVERY d`
- **S4 — planted vacuity (`check(cls_ok,` → `check(True,`): FIRED, and the mechanical
  vacuity scan CAUGHT it.** EXIT 1; 4218 ok + 1 failure:
  `FAIL  the mechanical vacuity scan: 1 pattern hits across the dead-code shapes and the numeric-truthy rigging`
  followed by the detail line `[vacuity] hits: [('check(True,', 423)]` — the scan
  correctly names the planted pattern and its line number. (Caveat for the record: the
  scan is lexical; the semantic vacuities F1–F3 in the clean file are NOT caught by it.)
- **S5 — beta directions deleted (list cut to 4 directions, forcing <5 distinct): FIRED.**
  EXIT 1; 4157 ok + 62 failures — the beta-sample check fails at every world, e.g.
  `FAIL  [d=1, alpha=(1, 1)] the beta-sample: 5 distinct K-directions, none equal to alpha (...)`.
  Robustness note: deleting a *single* direction from the original 8-tuple list does NOT
  fire anywhere (the `[:5]` slice still finds 5 distinct directions at every world); the
  check is passed only when 5 genuinely distinct β-directions are available, which is
  what its label claims.

## Counterexample / computation attempts:

The auditor wrote an independent verifier (`/home/z/audit40/audit40_recompute.py`, int /
Fraction only, no sympy) with deliberately different algorithms: the 8×8 matrix in the
row convention with block letters swapped (f_j at even indices); the exterior trace as
the sum of the 70 principal 4×4 minors (full Laplace expansion over S₄) instead of the
letter-by-letter `ext_action`; the ∧⁴ matrix via the minor formula
(∧⁴A)_{I,J} = det(A[I,J]); nullities via the auditor's own fraction-free Bareiss
elimination; the transversal-word wedge with UNSORTED merged keys and the sign computed
at the end by cycle-decomposition parity of the sorting permutation (the certificate
folds inversion counts into coefficients and sorts keys); K-arithmetic re-implemented
from scratch. Run time 4.2 s; **35 items, 0 disagreements** with the certificate's
claimed values at three mutually non-adjacent census worlds:

- **(d=15, α=(2,1)):** spectral trace: binomial K-sum = 6070 = sum of principal 4×4
  minors (imaginary part 0); dim ker minpoly(α⁴)(∧⁴A) = **2**; ambient dim = **36**;
  mixed dim = **32**; sector total 70; INT ŵ_R² = **1800 = 8d²**; INT ŵ_I² = **120 = 8d**;
  INT ŵ_R·ŵ_I = 0. (Certificate: ok[874–887], Re(α⁴) = −119 — also confirmed by hand:
  (2+√−15)⁴ = −119 − 88√−15.)
- **(d=34, α=(1,1)):** spectral trace 9046 = 9046; dims **2/36/32**; periods
  **9248 = 8·34²** and **272 = 8·34**; orthogonality 0. (Certificate ok[474–487];
  Re(α⁴) = 953, confirmed: (1+√−34)⁴ = 953 − 132√−34.)
- **(d=163, α=(2,1)):** spectral trace 199654 = 199654; dims **2/36/32**; periods
  **212552 = 8·163²** and **1304 = 8·163**; orthogonality 0. (Certificate ok[1274–1287];
  Re(α⁴) = 22673, confirmed.)
- **Phase order:** α = 2+√−15 has NO α^k = ᾱ^k for k ∈ {1,2,3,4,6} (generic member,
  phase order None — matching ok[43]); at d=3, α=(1,1): **α³ = ᾱ³** (order 3 — the
  collar, matching the canary ok[4177]); also re-confirmed α⁴ = ᾱ⁴ at d=1 (1,1)
  (order-4 member) and α⁶ = ᾱ⁶ at d=3 (3,1) (order-6 member).

No counterexample was found; no disagreement of any kind. The degenerate canaries were
also re-derived by hand: at (3,(1,1)) the phase is a cube root of unity so
minpoly(α⁴) = minpoly(α³ᾱ) and the merged primary part is 2+32 = 34; at (5,(0,1)),
α⁴ = d² is rational, merging Weil+ambient to 2+36 = 38; at (5,(3,0)) all factors merge
to dim 70 — exactly the certificate's ok[4178], ok[4181], ok[4184], ok[4187].

## Required repairs before claiming success:

- [ ] **F1 (major):** rewrite the bridge check to evaluate the symbolic layer's
      *computed* polynomials (`qRR_s[0]`, `qII_s[0]`, `qep_s[0]`, `c4p_s[0]`, `c4m_s[0]`,
      `cross_s[0]`, `carrier_s[0]`, `qB_s[0]`) at d = 1..30 against the closed forms
      (exact integer arithmetic — no `/2` float), so the "layer bridge" receipt has
      content; re-run the deterministic double receipt.
- [ ] **F2:** remove or re-implement the tautological leastness check (62 copies).
- [ ] **F3:** compute the symmetric-algebra half of the V5 discrimination or relabel it
      as cited.
- [ ] **F4:** replace the float `(9*8*dd*dd + 24)/2` with exact `Fraction(...,2)`/`//2`.
- [ ] **F5:** correct "spanning 24 distinct d's" → "spanning 31 distinct d's" in the
      record §37 and the tex quantifier line.
- [ ] **F6:** correct "5 collar canaries" → 4 (or add a fifth canary world) in the code
      header, the record, and the tex.
- [ ] Re-generate runA/runB receipts after the repairs and re-verify byte-identity; the
      AUDIT-40 paragraph in the round record should reference this file.

*Auditor's summary judgment: the mathematics of the round survives adversarial
recomputation and a five-shot sabotage battery without a scratch; the defects are all
in the certificate's periphery — one empty labeled receipt (the bridge), two decorative
checks, one benign float, and two count/wording errors in the artifacts. Repair F1–F6
and the round's claims are fully aligned with its certificate.*
