# WORKLOG_W81_142A — THE ORDER-k DEVIATION IDENTITY (the #142 sublinear blocker, delivered)

Lane: W81-142A (Erdős #142, the deviation-identity lane of the W81 six-lane
wave). Mission: kill the named blocker of UPPER_STACK.md "WHAT REMAINS" —
the ORDER-k DEVIATION IDENTITY (the L-EP analog at order k): an exact
Fourier-side count of T_k(A) = #{(x,d) ∈ Z_p² : x, x+d, ..., x+(k−1)d ∈ A}
with a usable extraction, for general k ≥ 3, complete with the extraction
layer and exact constants. Finisher: W81-142A-F.

## EVENTS

### The opener agent (W81-142A, died mid-mission after the engine banked)

1. Read the stack per the brief: ASYMPTOTIC_STACK (the named fronts),
   SUBLINEAR_PROOF.md (the k=3 method being generalized: Lemma F1 the
   identity, Lemma F2 the extraction, Lemma I the arc increment),
   UPPER_STACK.md WHAT REMAINS (the exact blocker statement + the arsenal
   inventory: the GST "higher-order" towers are DG-algebra jet laws, no
   k-AP content), LOGDECAY.md (the banked k=3 sublinear law), the brief
   W81_BRIEFS/W81-142A.md.
2. Derived THEOREM D1-k: expand 1_A = δ+f (the order-k deviation split),
   Fourier-invert each factor, the two geometric sums (the x-sweep forces
   Σr_i ≡ 0, the d-sweep forces Σi·r_i ≡ 0 (p)); the s=1 layers die by the
   group permutation, the s=2 layers die because (i−j) is invertible mod p
   (p > k) forcing the trivial solution with f̂(0) = 0 (THEOREM V2-k).
   Built the full companion structure: LEMMA PAR (the constraint-space
   parametrization, #V_S = p^{s−2}), THEOREM CLS-3 (the affine λ-classes
   with dihedral symmetry, the k=4 closed forms D_3(4) = 2E_2+2E_3 and the
   D_4(4) two-variable kernel), the F1 byte-reproduction at k=3.
3. Derived the extraction layer with exact constants: LEMMA FREE (T_k = |A|
   on cyclically k-AP-free sets), L-EP-k (deviation floor δ^k p²/2),
   PB-GEN (Parseval B = δ(1−δ)p²; |E_S| ≤ MB/p; |D_3(k)| ≤ C(k,3)MB/p; cap
   M ≤ min(δ,1−δ)p), D4-GEN (|D_4| ≤ B²/p² and ≤ M²B/p), X-4(i) (M ≥
   c_4(δ)p, c_4 = (δ²/2−(1−δ)²)/(4(1−δ))), X-4(ii) (the threshold-free
   sqrt-route M ≥ √(4δ²+δ³p/(2(1−δ)))−2δ), F2-SHARP (M ≥ δ²p/(2(1−δ)),
   implying banked F2), TC-4 (the carriage law (1−δ)²/δ² ≤ 1/4 ⟺ δ ≥ 2/3),
   L-TERM-3-SHARP (δ ≤ 2−√2 = 0.585786, sharpening the banked L-TERM
   (9−√17)/8 = 0.6096), L-TERM-4 (δ ≤ (10−√10)/9 = 0.759747), OB-4 (the
   quantified k=4 obstruction: 11/21 + 22/p < 2−√2 for every prime p ≥ 359
   — the integer form 2p²21² < (31p−462)²; the p-scale single-coefficient
   extraction cannot fire at certified stone densities; the correlation
   route is the named next front).
4. Built engine142deviation.py (898 lines, complete): S1 the identity by
   FOUR independent methods (M1 brute; M2 float DFT; M3 EXACT modular at
   two independent primes q ≡ 1 (mod p) via the ring homomorphism
   Z[ω] → F_q at primitive p-th roots; M4 the exact integer layer expansion
   p^k T_k = Σ a^{k−s}Es_int in int64) at k ∈ {3,4,5,6} × p ∈
   {11,13,17,101,1009}; S2 the vanishing battery (exhaustive 2-subset
   systems k=3..8, the dimension law with s≤4 exhaustive cross-enumeration,
   the affine classification tables, the dihedral symmetry, the p ≤ k
   negative control); S3 the extraction plug-backs on 14 greedy cyclic
   k-AP-free cells + the constant arithmetic; S4 five negative controls
   (sign corruption, multiplicity corruption, phantom s=2 layer, planted
   AP, premise refusal).
5. Ran the engine: 50/51 PASS, wall 164s. THE SINGLE FAILURE:
   S3-TC4-CARRIAGE — a floating-point boundary artifact: the law
   (1−δ)²/δ² ≤ 1/4 ⟺ δ ≥ 2/3 is TRUE at δ = 2/3 ((1/9)/(4/9) = 1/4
   exactly), but the float evaluation (1−2/3)²/(2/3)² rounds to
   0.2500000000000001 > 1/4 and the biconditional collapses. THE DISPATCH
   DIED before the fix, the docs, and the comparator extension — the
   engine + receipts were banked untracked in the worktree (the protection
   engine's AUTO-SEAL had already caught the earlier state; the final bank
   was picked up by this finisher).

### The finisher round (W81-142A-F, this document's author)

6. SALVAGE AUDIT: read the 898-line engine line by line, the 50/51
   receipts, the brief, UPPER_STACK/SUBLINEAR_PROOF/NEW_LAWS_142, and the
   comparator lane (driver.py, solution.json, official_gate.py). Confirmed
   the single failure is EXACTLY the documented float-boundary artifact and
   NOTHING else: every other check green, the law true, the engine
   complete.
7. THE FIX (minimal, math-preserving): S3-TC4-CARRIAGE rewritten with
   EXACT rational arithmetic (fractions.Fraction): δ ∈ {1/2, 3/5, 2/3,
   7/10, 9/10} as Fractions, the biconditional (1−δ)²/δ² ≤ Fraction(1,4)
   ⟺ δ ≥ Fraction(2,3) — the δ = 2/3 boundary now evaluates exactly
   (1/9)/(4/9) = 1/4 ≤ 1/4. NO other check touched; the law unchanged;
   verified in isolation before the run (the old float path reproduces
   0.25000000000000006 > 0.25 — the artifact, not the mathematics).
8. RE-RAN THE ENGINE: `timeout 400 python3 engine142deviation.py --verify`
   → **CHECKS: 51/51 passed, WALL: 111.0s, ENGINE VERDICT: ALL GREEN**.
   Zero other failures — no further fixes needed. Committed (9100b3b).
9. WROTE DEVIATION_IDENTITY.md — the complete proof document: §0 setting +
   NEW LAW FULL-GROUP-SUM; §1 THEOREM D1-k with the full derivation (the
   order-k deviation split, the Fourier inversion, the two geometric sums,
   the constraint system), LEMMA PAR, THEOREM CLS-3 (affine classes +
   dihedral + the k=4 closed forms), COROLLARY F1-REPRO, the M3/M4
   exactness methods; §2 THEOREM V2-k complete (both vanishings, the
   dimension law, the direction non-zeroness, the p ≤ k negative control);
   §3 the extraction layer — every inequality with its exact constant and
   its plug-back conditions (L-EP-k, PB-GEN, D4-GEN, X-4(i)/(ii), F2-SHARP,
   TC-4, L-TERM-3-SHARP, L-TERM-4, OB-4 with the full parabola closure
   79p²−28644p+213444 > 0 for all p ≥ 355, largest failing prime 353);
   §4 the 51/51 certification table with every check name. 16 arsenal laws
   cited at their exact lines (all read this wave); 14 NEW laws flagged
   NEW. Committed (0d24ad4).
10. LEDGER: appended C142-DEVIATION-K, C142-VANISH-K, C142-EXTRACT-K
    (exact statements + verification routes) to problem142-ap-free/
    NEW_CLAIMS.md, and the three new laws with their citations to
    NEW_LAWS_142.md (the W81-142A section). Committed (b84ceb1).
11. COMPARATOR EXTENSION: appended the three claims to
    comparator-official/challenges/142/solution.json (14 → 17 claims) and
    added the S-DEVIATION-W81 family to driver.py:
    S-DEVIATION-ENGINE (subprocess the engine; PASS = exit 0 + "51/51
    passed" + "ALL GREEN" in the receipts), S-DEVIATION-IDENTITY (fresh
    in-driver code: D1-k + V2-k by BRUTE constraint enumeration over
    Z_p^s — independent of the engine's parametrized route — at (3,13) and
    (4,11), with the k=3 F1-kernel reduction), S-DEVIATION-CONSTANTS
    (exact Fraction TC-4, OB-4 integer arithmetic at the boundary primes
    349/353 fail + 359..104729 pass, the c_4 sign law, the L-TERM-4
    crossing c_4((10−√10)/9) = 1−(10−√10)/9, L-TERM-3-SHARP < the banked
    constant). Standalone-tested the in-driver logic (0.01s, all green)
    before the gate. Committed (9e9a4e8).
12. RAN THE GATE: `python3 official_gate.py 142` →
    **CHECKS: 23/23 passed (official=5, solution=11, controls=7), WALL:
    121.06s, VERDICT: YOUR SOLUTION IS OKAY.** The three new S-DEVIATION
    checks all PASS; the 20 pre-existing checks unchanged and green; the
    engine re-ran under the gate subprocess (fresh receipts: 51/51, wall
    118.2s, ALL GREEN — the receipts stay live-verified).
13. Pushed the lane to origin w81-142a after every deliverable (commit
    discipline: engine fix 9100b3b → DEVIATION_IDENTITY.md 0d24ad4 →
    ledgers b84ceb1 → comparator + gate 9e9a4e8 → this worklog).

## THE DELIVERED THEOREMS (exact scope, no "open" labels)

- **THEOREM D1-k** (the order-k deviation identity) — complete, all
  p > k ≥ 3, four-method machine-certified, k=3 byte-identical to banked F1.
- **THEOREM V2-k** (the s ≤ 2 vanishing) — complete, identical vanishing,
  negative-controlled both directions (p ≤ k breaks it; a phantom layer
  breaks the identity).
- **LEMMA PAR / THEOREM CLS-3** — the constraint-space parametrization and
  the affine classification with the dihedral symmetry — complete.
- **The extraction layer** — LEMMA FREE, L-EP-k, PB-GEN, D4-GEN, X-4(i),
  X-4(ii), F2-SHARP, TC-4, L-TERM-3-SHARP, L-TERM-4 — complete, every
  constant exact, plug-backed on 14 greedy cells.
- **THEOREM OB-4** — the quantified k=4 obstruction: the p-scale
  single-coefficient route cannot fire at certified densities for p ≥ 359;
  the k ≥ 4 sublinear arc's named next front is the correlation route along
  (r, r', −r−r') built on top of D1-k. (The brief's GUARANTEED floor —
  identity + vanishing + extraction layer — is fully delivered; the
  LOGDECAY-GEN stretch goal was never claimed.)

## STATE OF THE LANE

Banked and green: engine (51/51), receipts, DEVIATION_IDENTITY.md, the
three claims in both ledgers, the comparator gate (23/23, YOUR SOLUTION IS
OKAY). The opener's work survived the dispatch death in full — the finisher
fixed one float-comparison artifact (the law was true), wrote the docs,
extended the comparator, and sealed the lane. Zero work lost; the engine
never stopped; it never lied.

*In English, always.*
