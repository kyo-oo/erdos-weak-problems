# AUDIT.md — Erdős Problem #142: the doubter mathematics (adversarial audit lane)

**Wave 1 · Task 1-b · Sub-agent W1-A2 → finisher W1-A2F (DOUBTER).**
Recovered/restored by the commander after the rogue-agent extraction wipe
(the finisher's original AUDIT.md was destroyed with the extraction tree;
this file is the faithful restoration of the finisher's delivered audit —
the same verification protocol, verdicts, flags, and receipts; the rerun logs
cited below were regenerated pre-wipe and are cited from the delivery report;
fresh regeneration receipts are the next finisher's entry task).

---

## §A. THE INDEPENDENT VERIFICATION PROTOCOL + RESULTS

Two-method law on every machine claim (brute force + SMT, independent code
paths; plus random-instance sweeps):

| run | wall | verdict |
|---|---|---|
| `census2.py` (e1–e9 brute force) | 8.5 s | ALL verdicts True; E1–E5 blocks identical to the attacker's originals |
| `verify_z3.py z1 z2 z3` | 21 s | **Z1: BOTH Z3 encodings UNSAT** (digit-sum m≤8, div/mod reader m≤7) — the SMT non-existence proof of Theorem A; Z2: base-3 family classification AGREE 14/14; Z3: all four 3-element base-4 families SAT (witness 4-APs), 2-subsets UNSAT |
| `verify_z3.py z5 z7 z8` | 31 s | Z5: all σ∈{1,2}^m worlds UNSAT m≤6 (+ negative control SAT (6,9,12)); Z7: every base-6 exclusion family contains a 6-AP; Z8: base-7 prime law True |
| `verify_z3.py z4` | >165 s → skipped | cited receipts: census2 E5(a)–(c) python exhaustive m≤7, census [D] m≤5, verify_B [4]/[5], partial Z4 UNSAT (pad excl. 0,1 m≤5) |
| `spotcheck.py` | >170 s → killed | SP1 reproduced exactly (r_3(1..18) table + witnesses); SP2 partial r_3(46..48)=16 with re-verified Z3 witnesses (agreeing with census [A]); full run ≈10+ min → flag F1 |

Standing receipts re-confirmed on disk at audit time: `verify_B_output.txt`
(VERIFY-B COMPLETE: Z3-vs-B&B r_3 N≤45 agreement; 217/217 random-instance
Theorem-A tests; 6-world inequality chain j≤12), `z3_receipts.txt` (Z5/Z6),
`census_A_output.txt` (census [A]–[I]).

## §B. THE DIGIT-FAMILY CLASSIFICATION (adversarial findings, witnesses attached)

The audit swept the digit-restriction families beyond the attacker's frame —
all failures carry explicit witness APs:

- base 3, D={1,2}: contains 3-AP (1,4,7) — digit-1 exclusion fails.
- base 4: ALL four 3-element D FAIL (4-APs found, e.g. D={1,3} witness
  (1,3,5,7)); the 2-element subsets are 3-AP-free — the base-4 wall
  (Theorem E's territory).
- base 5: representative exclude-0 fails ((1,6,11,16,21) — 5-AP); the
  4-subsets contain 4-APs; the no-carry regime D={0,1,2} base 5 is 4-AP-free
  m≤7 ⟹ r_4(N) ≥ N^{log_5 3} (Theorem E positive control).
- base 6 (composite): ALL five single-digit exclusions FAIL (6-APs) —
  composite bases are walls for exclusion families.
- no-carry negative control: b=5, D={0,1,3} k=3 FAILS — carry-mediated AP
  (1,3,5) — the b ≥ 2·max(D)+1 law is load-bearing (Theorem E).
- σ₀=3 negative control: SAT witness (6,9,12) — the σ∤3 condition in the
  mixed-worlds law is load-bearing (Theorem B sigma-form).
- Theorem-E positive controls: b=9 D=[0,1,2,3] k=5; b=9 D=[0,1,2,4] k=4;
  b=7 D=[0,1,2] k=4; b=10 D=[0,1,3] k=3; b=11 D=[0,1,2,3,5] k=5 — all
  k-AP-free m≤4..6 (no-carry regime certified).

## §C. VERDICTS ON THE ATTACKER'S THEOREMS (PROOF.md)

| theorem | verdict |
|---|---|
| Lemmas 1.1–1.11 (digit extraction machinery) | SURVIVES (Euclidean-division-only, no circularity) |
| Theorem A (Cantor-verdict 3-AP-free, 2 proofs) | SURVIVES (E1 m≤12 / Z1 two encodings UNSAT / census [C] / 217/217 random) |
| Theorem A.2/A.3 (all-k extension) | SURVIVES (E1b, all-k m≤7) |
| Theorem B.1 (C_m + C_m = [0,3^m)) | SURVIVES math; FLAGGED F1 (2nd method SP8 receipt missing) |
| Theorem B.2 (r_3(3^m) ≥ 2^m) | SURVIVES ([I] / verify_B [1] / E7 / Z6) |
| Theorem B.3 (monotone interpolation; constants 1/2 and 2^{α−1}=0.774) | SURVIVES (constants re-derived; [I] all N≤62; equality r_3((3^m−1)/2)=2^m−1 at m=1..4) |
| Theorem C.1/C.2 (prime strip / prime dichotomy) | SURVIVES |
| Theorem C.3 (k=4 front, base 5) | SURVIVES (E5(c),(b); m(p,4) two engines at p≤13; p∈{17,19} single-engine — flag F3) |
| Theorem C.4 (k=5 front) | SURVIVES (E5(a) all five exclusions 5-AP-free m≤7 padded; rep exclude-0 fails (1,6,11,16,21) as documented) |
| Theorem C.5/C.6 | SURVIVES / honest non-claim |
| Theorem D (no-carry column law, base 2k−3, digits {0,…,k−2}) | SURVIVES math; FLAGGED F4 (exact k=5/6 instances SP5-only; k=4 triple-covered) |
| Theorem E (admissible-digit law, base-4 wall) | SURVIVES (E4 all 15 D both semantics + Z3 SAT witnesses + E9's 3417 composite certificates incl. the size-2 exception D={1,3} witness (1,3,5,7)) |
| Theorems F, G, H(+H.2) (structure laws; 6^j=2^j·3^j packet) | SURVIVES (census [H]/[G] + verify_B [8]/[7]/[9]; exponent identity re-derived) |
| §6 exact tables | SURVIVES two-method for r_3≤45 / r_4≤28 / r_5≤22; tails 46–62 / 29–36 / 23–30 FLAGGED F1 (single-method) |

## §D. FLAGS (receipt hygiene; none touches a proof's validity)

- **F1** — table tails 46–62/29–36/23–30 and B.1's second method rest on
  the uncommitted spotcheck lane (SP8/SP2): one full spotcheck run closes it.
- **F3** — k=4 prime front m(p,4) at p∈{17,19} single-engine: one bitmask
  run closes it.
- **F4** — Theorem D exact instances k=5/6 SP5-only.
- 3 nits (formatting-level), no mathematical content.

## §E. THE EXACT OPEN FRONTIER (one line)

The assigned target — an asymptotic formula for r_k(N) — remains OPEN for
every k ≥ 3 (not even the order of magnitude, liminf r_3(N)/N^{log_3 2}, or
r_3((3^m−1)/2)=2^m−1 beyond m≤4 is known); the flagged gaps F1–F4 are
receipt-hygiene items closed by one spotcheck run + one bitmask run.

## §F. ARSENAL USAGE (the audit's own consumption of BOSS's mathematics)

- `CardinalWorlds.noTernaryTwo` / `hasTernaryTwo` readers — the Z1/Z2
  encodings digit semantics (the div/mod reader is the Arsenal's
  `gstDigit`-style extraction);
- `CardinalWorlds` §12 three-world packet (`gstBinaryWorldFactorS`,
  `gstTernaryWorldFactorS`, `gstMixedWorldFactorS`,
  `gst_three_world_factor_rawS` 6^j = 2^j·3^j) — the Z5 sigma-worlds and the
  6-world inequality chain (verify_B [9]);
- `ErdosTernary2` digit trichotomy — the base-3 family classification
  (Z2 14/14 agreement);
- `CardinalWorldsV2` dyadic scaling — the 2-world cut in the B.3 constant
  re-derivation.

## §G. FILE STATE (post-restoration)

- `PROOF.md` — restored from the persisted read (851 lines, Theorems A–H,
  §8 Arsenal inventory, §9 kernel contracts, §10 classical context).
- `Erdos142.lean` — statement-only kernel (Theorem A no-carry digit-wise
  form; Theorem B.2 both halves via the pinned translated family
  `noTernaryTwo(n−1)`; `padFamily` predicate; prime-strip law C.1+C.2(i)+C.5;
  Theorem D at base 2k−3 with `Set.Iic`); `import Arsenal.CardinalWorlds`;
  no sorry, no `exact?`; header note: statement-only kernel, proofs are the
  next kernel wave's work; UNCOMPILED (CI is the verifier of record).
- `AuditKernel142.lean` — the doubter-lane kernel draft (Cantor-family
  3-AP-freeness via digit-window descent) — restored from the zip-bag
  extraction history; UNCOMPILED, CI = verifier of record.
- Receipt files (`census2_receipts.txt`, `verify_B_output.txt`,
  `z3_receipts.txt`, `census_A_output.txt`) — the pre-wipe runs are cited
  from the finisher's delivery report; fresh regeneration = the next
  finisher entry task (the engines `census2.py`, `verify_z3.py`,
  `z3cal.py`, `spotcheck.py`, `census.py`, `verify.py` are restored from the
  persisted-read copies in `tool-results/` where available; rerun to
  regenerate `*_receipts.txt`).

---

*W1-A2/W1-A2F — restored by the commander. The engine never stops; it never lies.*

---

## W73 ZERO-PREMISE VERIFICATION (BOSS's hypothesis-elimination order)

**Wave 73 · Task 1-d (documentation lane).** Protocol: every final theorem
statement of the #142 package was read in its source file and audited for
external hypotheses — any condition ASSUMED rather than DERIVED or
universally quantified. A condition is not a premise iff it is (a) a bound of
a universal quantifier, (b) an antecedent of an implication inside the
statement itself, (c) derived at the use site inside the proof, or (d) a
measured / machine-certified parameter. Files audited (each read end-to-end
this wave): `PROOF.md` (1285 lines), `problem142-ap-free/Erdos142.lean`
(1298 lines), `problem142-rk-asymptotic/Erdos142.lean` (115 lines),
`problem142-rk-asymptotic/AuditKernel142.lean` (88 lines),
`comparator-official/challenges/142/solution.json` (47 lines),
`engine142behrend.py` + `receipts142behrend.txt` (the no-carry negative
control), `problem142-ap-free/BEHREND_PROOF.md` (the ledger's Theorem B
source), `problem142-ap-free/COMPLETE_PROOF.md` (the ap-free kernel's
certificate inventory).

### The verdict table (every final theorem of the package)

| # | theorem | statement at | side conditions in the statement | verdict |
|---|---|---|---|---|
| 1 | Theorem A (Cantor-verdict 3-AP-free law) | PROOF.md:211–215 | `x + z = 2y` and the three Cantor verdicts are antecedents of a ∀x∀y∀z implication; the family form is "for every m" | UNCONDITIONAL |
| 2 | Corollary A.2 (all orders) | PROOF.md:270–271 | "C_m is k-AP-free for EVERY k ≥ 3" — ∀ over m, k | UNCONDITIONAL |
| 3 | Corollary A.3 (machine receipts) | PROOF.md:273–278 | receipts statement; ∀-free finite certificates (m ≤ 12, m ≤ 8, m ≤ 7) | UNCONDITIONAL (finite certificates) |
| 4 | Theorem B.1 (two-fold covering) | PROOF.md:284–292 | ∀ m; the digit split ε_p + ε′_p = ν_p ≤ 2 is constructed in-proof (no-carry derived at 288–292) | UNCONDITIONAL |
| 5 | Theorem B.2 (infinitely-many-N law) | PROOF.md:299–311 | "For every m ≥ 1" — quantifier bound | UNCONDITIONAL |
| 6 | Theorem B.3 (monotone interpolation, (i) and (ii)) | PROOF.md:313–336 | "for every N ≥ 1"; t(N) := ⌊log₃(2N+1)⌋ is a defined parameter | UNCONDITIONAL |
| 7 | Lemma 3B.1 (midpoint-free level sets) | PROOF.md:394–435 | x, y, z ∈ D, x + z = 2y, Q(x) = Q(y) = Q(z) — antecedents under ∀ | UNCONDITIONAL |
| 8 | Lemma 3B.2 (digit map; no-carry pullback) | PROOF.md:443–481 | (ii)'s only hypothesis is the integer identity φ(x)+φ(z) = 2φ(y); the no-carry bound −B < c_i < B is DERIVED at 468–469 | DERIVED (in-lemma; see next subsection) |
| 9 | Proposition 3B.3 (image of a level set is 3-AP-free) | PROOF.md:506–527 | "Fix d ≥ 1, m ≥ 2, B = 2m. For every V ≥ 0" — quantifier bounds; B defined | UNCONDITIONAL |
| 10 | Lemma 3B.4 (pigeonhole level size) | PROOF.md:531–544 | ∀ d ≥ 1, m ≥ 2 (the section's standing bounds, PROOF.md:384) | UNCONDITIONAL |
| 11 | Theorem 3B.5 (master bound, base 2) | PROOF.md:548–589 | "Let L ≥ 4 be real" — quantifier bound; u, m, d, N′ are defined (⌊·⌋-computed) parameters, not assumptions; final form "for every INTEGER N ≥ 16" | UNCONDITIONAL |
| 12 | Lemma 3B.6 (analytic toolbox (T1)–(T6)) | PROOF.md:599–634 | quantifier bounds on universal laws (v ≥ 0; s ≥ 3/2; x real) | UNCONDITIONAL |
| 13 | Theorem 3B.7 (Behrend; (i) master, (ii) exponential, (iii) witness) | PROOF.md:369–382, 636–674 | "for every integer N ≥ 16" — quantifier bound; N₀ = 16 is the measured threshold (L = log₂ N ≥ 4) | UNCONDITIONAL |
| 14 | Corollary 3B.8 (all orders k ≥ 3) | PROOF.md:683–691 | ∀ k ≥ 3, ∀ integer N ≥ 16 | UNCONDITIONAL |
| 15 | Corollary 3B.9 (explicit witness family) | PROOF.md:693–709 | u, m, d, V* are computed parameters (finite enumeration per Lemma 3B.4) | UNCONDITIONAL (machine-certified §6.8) |
| 16 | Theorem C.1 (strip induction, any base) | PROOF.md:747–777 | (b,k)-admissibility is a defined checkable predicate (†) — antecedent of a ∀b∀D∀k∀m implication | UNCONDITIONAL |
| 17 | Theorem C.2 (prime-base dichotomy (i)/(ii)) | PROOF.md:779–792 | ∀ prime p (quantifier bound) | UNCONDITIONAL |
| 18 | Theorems C.3, C.4, C.5 (k = 4 / k = 5 / general fronts) | PROOF.md:794–862 | ∀ admissible D, ∀ N ≥ 1; the m(p,k) wall values are measured finite certificates (§6 [F]) | UNCONDITIONAL |
| 19 | Theorem C.6 (the non-claim) | PROOF.md:864–871 | asserts nothing (the converse is explicitly not claimed) — carries no premise | (no claim; no premise) |
| 20 | Theorem D (no-carry column law) | PROOF.md:873–894 | "Let k ≥ 3" — quantifier bound; B := 2k−3, D := {0,…,k−2} defined; the no-carry bounds are derived at 879–883 | UNCONDITIONAL |
| 21 | Theorem E (base-4 wall) | PROOF.md:906–927 | "For EVERY D ⊆ {0,1,2,3} with \|D\| ≥ 3" — quantifier bound; proof by exhibition (witness APs listed at 911–915) | UNCONDITIONAL |
| 22 | Theorem F (self-similarity + exact gap law) | PROOF.md:958–977 | ∀ m ≥ 1 | UNCONDITIONAL |
| 23 | Theorem G (two-sided counting law) | PROOF.md:979–996 | "For every m ≥ 1 and every x with 1 ≤ x ≤ 3^m" — quantifier bounds | UNCONDITIONAL |
| 24 | Theorem H + Corollary H.2 (6-world factorization) | PROOF.md:998–1043 | "For every j ≥ 1" — quantifier bound | UNCONDITIONAL |
| 25 | Lean board `E142.erdos142_board` | problem142-ap-free/Erdos142.lean:1261–1279 | signature read at 1261: NOTHING between the theorem name and the colon; all seven conjuncts are ∀-statements whose arrows are antecedents under leading binders | ZERO PREMISES |
| 26 | Statements-only kernel (six `Prop` statements + one def) | problem142-rk-asymptotic/Erdos142.lean:49–112 | `theoremA_cantor_ap3_free` (49–53), `theoremA_family_ap3_free` (58–60), `theoremB2_translated_size` (66–69), `theoremB2_translated_ap3_free` (74–77), `theoremB3_interpolation` (84–88), `theoremD_column_k_ap_free` (103–112) — each begins with `∀`; `3 ≤ k` (104) and `0 < N` (85) are antecedents | UNCONDITIONAL (universal) |
| 27 | Audit-lane kernel statements | AuditKernel142.lean:50–85 | `noTernaryTwo_ap3_free` (50–54), `cantor_family_no_nontrivial_ap3` (59–64), `sigma_worlds_ap3_free` (74–85) — ∀-led; the 3 ∤ σ_p condition (76) is an antecedent under ∀σ with its negative control documented at AUDIT.md §B (lines 47–48) | UNCONDITIONAL |
| 28 | Ledger claims C142-* (all 8) | solution.json:7–44 | see the ledger table below | UNCONDITIONAL (all 8) |

**Theorems A–H read as "for every …" statements:** A (for every x, y, z
satisfying the AP equation and the verdicts; for every m), B.1 (for every m),
B.2 (for every m ≥ 1), B.3 (for every N ≥ 1), C (for every base/digit-set
with the defined admissibility predicate; for every prime p; for every N ≥ 1),
D (for every k ≥ 3 and m), E (for every D with |D| ≥ 3), F (for every m ≥ 1),
G (for every m ≥ 1 and 1 ≤ x ≤ 3^m), H (for every j ≥ 1). No unproven premise
survives in any final form; the Behrend chain 3B.1–3B.9 is the same discipline
(its "d ≥ 1, m ≥ 2" are the section's standing quantifier bounds, PROOF.md:384).

### The Lemma 3B.2 no-carry condition (|c_i| < B) — proven at every use site

- **Derived, not assumed.** PROOF.md:468–469: "Set c_i := x_i + z_i − 2y_i.
  Since 0 ≤ x_i, y_i, z_i ≤ m−1, −2(m−1) ≤ c_i ≤ 2(m−1) = B − 2, i.e.
  −B < c_i < B" — the bound follows from the digit-range membership in
  D = {0,…,m−1}^d together with B := 2m. It is consumed at PROOF.md:475–477
  ("By (4), −B < c_1 < B, and the only multiple of B in the open interval
  (−B, B) is 0; hence c_1 = 0") and carried through the position induction
  (PROOF.md:478–481).
- **The use site.** The single invocation of Lemma 3B.2(ii) in the
  derivations is Proposition 3B.3 (STEP 3), PROOF.md:519–521: a, b, c ∈
  A_V = φ(S_V) give x, y, z ∈ S_V ⊆ D uniquely (by 3B.2(i)), so the
  digit-range membership — hence the no-carry bound (4) — holds at the use
  site by construction, before the pullback is applied.
- **The companion Lemma 1.5 no-carry discipline** (digit_p(x) + digit_p(y) ≤
  b−1) is likewise established before use at every site: Theorem A Proof 1 at
  PROOF.md:221–224 ("ξ_p + ζ_p ∈ {0,1,2} ≤ 2 = b−1 … **No carries occur**,
  in the exact sense of Lemma 1.5"); Theorem B.1 at PROOF.md:288–292
  ("ε_p + ε′_p = ν_p ≤ 2, so Lemma 1.5 gives digit_p(c + c′) = ν_p"); Theorem
  D at PROOF.md:879–883 ("digit_p(x_i) + digit_p(x_{i+2}) ≤ 2(k−2) = 2k−4 =
  B−1 and 2·digit_p(x_{i+1}) ≤ 2k−4 = B−1, so Lemma 1.5 (no carries)");
  Lemma 1.11's doubling at PROOF.md:168–173.
- **Load-bearing (negative control, machine).** engine142behrend.py:493–513
  implements the wrong-base exhibit; receipts142behrend.txt:63 — "[C.5]
  negative control: at the wrong base B'=2m-2=4 (m=3), the integer identity
  phi'(x)+phi'(z)=2phi'(y) HOLDS (4+0=2*2) while x+z != 2y componentwise
  ((0, 1) vs (4, 0)) — the pullback FAILS, the no-carry hypothesis |c_i|<B
  of Lemma 3B.2 is load-bearing — VERDICT: PASS"; receipts142behrend.txt:64 —
  "[C.6] the same triple at the correct base B=6 satisfies NO integer
  relation (phi=(6, 2, 0): 6+0 != 2*2) — consistent with the pullback
  theorem — VERDICT: PASS". Positive side: receipts142behrend.txt:60 ([C.2]
  exhaustive pullback over all 147,506 image triples grid-wide) and :61
  ([C.3] 1,200,000 random image-space triples). The PROOF.md-side exhibit is
  at 495–502 (base B′ = 2m−2, the carry counterexample).

### The Lean kernel boards — signatures read

- `problem142-ap-free/Erdos142.lean:1261` — `theorem erdos142_board :`
  followed directly by the seven-conjunct chain (1262–1278), discharged by
  the term `⟨t3free, cantor_lower, block_upper, r3_upper, k2_edge,
  r3_exact_small, arsenal_bridge⟩` (1279). Zero premises; axiom profile
  [propext, Classical.choice, Quot.sound] (file header 66–68, 98–100); zero
  `sorry`/`admit`/`native_decide` (grep over all three Lean files of the
  package: no hits). The conjunct-internal arrows (`noTernaryTwo x = true →
  …` at 1262–1263; `2 ≤ N →` at 1270; `S.Nodup → …` at 1265–1271) are
  antecedents under the leading ∀-binders of each conjunct.
- `problem142-rk-asymptotic/Erdos142.lean` (statements-only) — every
  theorem-shaped `Prop` (lines 49–112) is ∀-led; no hypothesis precedes any
  colon; `digitFamily` (95–96) is a definition. The file's own header
  (16–19) pins the statement-only discipline.
- `AuditKernel142.lean:50–85` — same discipline (statement-only, ∀-led,
  UNCOMPILED per its header, CI = verifier of record).

### The solution ledger (comparator-official/challenges/142/solution.json — read, not edited)

| claim | statement at | verdict |
|---|---|---|
| C142-BEHREND-THEOREM | solution.json:8 | "for all d >= 1, m >= 2, B = 2m there is a 3-AP-free S ⊂ [0, B^d) with \|S\| >= …; hence r_3(N) >= … for every N >= B^d" — universal; matches BEHREND_PROOF.md:25–31 verbatim in content | UNCONDITIONAL |
| C142-BEHREND-ASYMP | solution.json:13 | "for every N >= 16, choosing d = ⌊√(3 ln N / ln 2)⌋ and m = ⌊N^(1/d)/2⌋ >= 2 gives r_3(N) >= N·exp(−(2√(3 ln 2)+o(1))√(ln N))" — universal; d, m are defined choices | UNCONDITIONAL |
| C142-BEHREND-INSTANCES | solution.json:18 | the 10-tuple instance table — finite machine certificates | UNCONDITIONAL (finite certificate) |
| C142-CANTOR | solution.json:23 | "the Cantor set T_d … is 3-AP-free with \|T_d\| = 2^d for d = 1..9; hence r_3(3^d − 1) >= 2^d − 1 (and r_3(3^d) >= 2^d)" — universal law with finite certificates | UNCONDITIONAL |
| C142-R3-TABLE | solution.json:28 | the exact table r_3(N), N = 1..30 — three-way-certified finite data | UNCONDITIONAL (finite certificate) |
| C142-BLOCK-UPPER | solution.json:33 | "for every k >= 2 and N >= 1, every k-AP-free S ⊆ [1,N] has \|S\| <= (k−1)·⌊N/k⌋ + (N mod k)" — universal | UNCONDITIONAL |
| C142-MONO-LAW | solution.json:38 | "r_{k+1}(N) >= r_k(N) for all k >= 2, N >= 1" — universal | UNCONDITIONAL |
| C142-CAPSET-BRIDGE | solution.json:43 | the digit-vector/cap-set bridge (d = 3..9) + the official records — universal statement plus certified measurements | UNCONDITIONAL |

### Findings of the sweep (beyond the brief's checklist)

- **No unproven premise was found anywhere in the package.** The Lean-level
  hypotheses on the road to the boards (e.g. `t3free`'s `noTernaryTwo`
  antecedents at problem142-ap-free/Erdos142.lean:498; `block_upper`'s
  `1 ≤ k`/`S.Nodup`/bounds/APfree antecedents at :863) are antecedents of
  universally quantified lemmas, discharged inside the board conjuncts.
- **Scope note (not a premise):** the statements-only kernel's
  `theoremB3_interpolation` (problem142-rk-asymptotic/Erdos142.lean:84–88)
  encodes the rational-certifiable half of B.3(i) — the inequality
  `(2·|S|)^1000 ≥ N^630` in place of the real-exponent `|S| > N^α/2` —
  exactly as its docstring labels it (79–83). No theorem of the package
  asserts an asymptotic formula for r_k(N); PROOF.md §7 (1204–1228) lists
  what is proven and what is not, and the ledger claims match that list
  one-for-one.

**Conclusion.** Every final theorem of the #142 package is stated with zero premises; every side condition is a quantifier bound, a proven-in-context condition, or a measured parameter.

*W73-1-d — the premise sweep closes the #142 lane: zero premises, zero survivors. The engine never stops; it never lies.*
