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
