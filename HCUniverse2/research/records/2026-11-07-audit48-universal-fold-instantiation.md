# AUDIT-48 — ADVERSARIAL PROOF AUDIT (Round 48: the Universal Fold Instantiation)

**Target**: `GST_universal_fold_instantiation_round48_2026_11_07.tex` + certificate
`universal_fold_instantiation_round48_checks.py` (v2, 1871 checks) + `runA.txt`/`runB.txt`
+ `GSTLawStackRound48.lean` (DRAFT-NOT-COMPILED).
**Claim under audit**: "THE CLOSING STRING AT FULL GENERALLY: every rational (p,p) class on
every smooth projective complex variety is algebraic (the Clay statement / Q2)".
**Auditor**: independent adversarial agent (AUDIT-48). Not an author of the round. Full
authority to read, re-run, re-derive, and sabotage (copies only, in /tmp/audit48_sab and
/home/z/audit48_work). Originals untouched.

---

## 0. Executive summary

The **arithmetic is sound and the certificate is honest at the arithmetic level**. I re-ran
it (1871 checks, 0 failures, exit 0, byte-identical double-run, both md5 seals reproduce),
independently re-derived every computable claim with a different stack (fractions +
sympy + cyclotomic resultants), swept a 60,500-world hostile grid, and ran seven sabotage
attacks. Every arithmetic claim of the round checks out, including the round's genuinely
new observation (the phase-pair cancellation `z·σ(z)=1` is a sign-blind polynomial
identity, verified symbolically in Q(s,q)) and the exhaustive four-stratum partition
(counts CM 64 / RM 68 / UC 516 / FOLD 24 / DEGEN 8 over 680 worlds — reproduced exactly).

The **headline claim is not established**. The weld (Theorem 3) presents the Clay statement
as an unconditional theorem with a proof, while its proof runs through (a) a committed
landing chain that is a *supplied Lean field* (`FoldProcessOn.landing_cycle`) — a
hypothesis-packet of strength comparable to the Hodge conjecture itself, which R32's own
"honest reading" remark declares *cannot* close the residual core — and (b) an **undeclared
identification of the campaign's two-letter-world frame with the actual input space of all
smooth projective varieties**. R47 §7(c) explicitly declared the frame quantifier ("the
closing string is the Clay statement *on this frame*"); Round 48 drops precisely that
declaration while jumping the quantifier to "every variety". No step in this round (or in
the cited receipts) extracts a quadratic phase from the cohomology of a general variety:
the R32 middle extraction produces `M_mid`/`J_mid`, not a two-letter phase; a general X
(e.g. a cubic fourfold's 10-dimensional H³ with no rational letter action) has no
associated (s,q), so "every extracted phase lands in a receipted stratum" has no referent
there. The certificate's geometric shadows are input-insensitive (the "witness" is one
fixed pair of line bundles on P² realizing 2h — the trivial divisor case — repeated at
every input).

**VERDICT: FAIL** (two blockers, both at the claim/weld level; the arithmetic core would
survive a re-scoped re-submission — repair list in §13).

---

## 1. The ten checklist rulings

### Point 1 — CLAIM MATCH: **PARTIAL FAIL**
The delivered *statement* (Theorem 3, boxed) literally equals Q2 (the Clay statement,
rational form: ∀X smooth projective complex, ∀p, ∀α ∈ H^{2p}(X,Q) ∩ H^{p,p}, ∃Z ∈
CH^p(X)_Q with cl(Z)=α). Statement-match: yes.
The *claim-as-scoped* is **not accurately described**: the derivation does carry an
unusually explicit scope-discipline section (§"The scope discipline", dependency classes
(a)–(d)), and it *does* declare the landing chain and the R32 T2/T4 equivalences as
commitments — that part is honest. But:
- the abstract, the Theorem-3 theorem/proof environment, the boxed closing string, and §8
  ("Q2 — the Clay statement — is closed") present a conditional-on-commitments result as
  an unconditional closure;
- the scope inventory **omits the largest hidden dependency** (the frame→variety
  instantiation — see Point 10);
- §scope(d) says "The closing string's strength is the conjunction of (a)–(c)" — but the
  proof needs (d) itself, i.e. the commitments are load-bearing, not ancillary;
- R47 §7(c) is cited as having "named the single remaining frontier"; in fact §7(c)
  *declares the frame quantifier* (a limitation), it does not name a full-generality
  frontier (narrative embellishment, F5c).

### Point 2 — HIDDEN STRENGTHENINGS: **PASS with minors**
Theorem 3's mathematical statement carries no silent extra assumptions (X, p, α only —
clean). The Lean draft is declared DRAFT-NOT-COMPILED and is all-`sorry` by design; no
Lean toolchain exists in this environment (verified: no `lean`/`lake`/`elan` binary) — the
discipline claim is accurate. Two Lean *shape* defects (not silent strengthenings, but
semantic errors in the recorded shapes): see F6.

### Point 3 — CIRCULAR REDUCTIONS: **FAIL (two findings, one silent, one mislabeled)**
(i) **Silent**: the weld's step "every extracted phase lands in a receipted stratum"
assumes every input of every variety is a two-letter world (i.e., that the frame models
the actual input space). This is an unproved statement of comparable strength, and it is
*nowhere declared* in R48's dependency inventory (F2). (ii) **Declared but mislabeled**:
the landing chain (`FoldProcessOn.landing_cycle`, the capstone's supplied field) is a
hypothesis-packet; R32's own remark (derivation, §Theorem 4 remark) states the
conclusion-form of (b2) "is not known, and no reformulation of it as a hypothesis-packet
can close it (the campaign's anti-circularity audits prove the packets equivalent to the
conclusion)". R48 declares it as a commitment but glosses it as "standard mathematics at
its proven scope" (Theorem C + Serre + Thom–Porteous + GAGA) — the *converse* direction
(bundle pair given ⟹ α algebraic, via GRR) is standard; the *needed* direction
(existence of the integrable pure pair at an arbitrary transcendental α) is HC-hard (F3).
The (b1) route similarly leans on R32 T2 (a)⇒(b) fed by R41's "general-input vanishing" —
declared derivation-level, but see F10 (h≤2 extrapolation).

### Point 4 — UNIFORMITY: **SPLIT — arithmetic PASS, geometry FAIL**
- T2's partition is genuinely uniform over ALL integer (s,q), q>0: the doors (D2 sign /
  perfect-square / Niven set) are total and mutually exclusive by construction; I verified
  zero leaks over a 60,500-world grid and proved the door totality case-by-case. The
  quadraticity and cancellation laws are polynomial identities (sympy-verified), uniform.
- T1's *algebraic* clauses are uniform (identities), but its *geometric* clauses and all
  of T3 are uniform **only by assertion**: no check ever touches a variety. Layer census
  (instrumented copy): X1 = 190 checks of `i²=−1` in Q(i) with the input only in the check
  *name*; X3's `C(N)=+N` and multiplicativity = 57 Q(i)-tautologies that never reference
  z, D2, s, or q (they compute `(i·x)(−i·x)=x²`); X6 = 29 weld-shadow checks, of which the
  19 "bit fires at every stratum's witness" checks re-run the *same fixed P² pair*
  ([1,1],[1,−1]) at every input. Genuinely input-sensitive: ~1430 checks (X5 sweep 1288,
  X0 87, X4 80, X3's z·σ(z) 19) — all purely arithmetic. The born instance realizes 2h on
  P²: a divisor class, i.e. Lefschetz-(1,1) territory, *not* the open sector
  2≤p≤⌊d/2⌋ where the conjecture is open (F3/F4).

### Point 5 — DEFINITION DRIFT: **PASS with three minors**
- The five fold equations (rank balance / grade-2 vanishing via the alternating
  polarization / trace law / scale m=2≠0 / norm rationality) match R47's
  `GSTLawStackRound47.lean` `norm_pair_born_witness` shape clause-for-clause. ✓
- `HodgeWorld`/`FoldProcessOn` (PairWit/scale/landing/landing_cycle) in R48's Lean match
  the capstone `GSTGraphV2OntologicalFoldForAllN.lean` exactly; R48's
  `universal_instantiation` is precisely the capstone's `forAllN_landing` shape. ✓
- Strata definitions (CM/Weil via the Niven set and orders 2,3,4,6; RM D2>0 non-square;
  fold-world D2 square; degenerate D2=0) match R41's phase-order dichotomy and R47's
  usage. ✓
- Drift nits (F5): (a) R47's Lean comment states the trace-law difference "PURE at grade
  2, zero at grades 0,1,3,4" while the shared P² witness, the capstone, and R48 have it
  pure at **grade 1** (2h) — an internal grade-convention inconsistency inherited in the
  R47 face; (b) R48's tex parenthetical "nonzero on conjugate pairs" (the polarization)
  is **false as stated for the witness x=1** (ψ(1,σ(1)) = 0; true only when both
  coordinates are nonzero — verified: ψ(x,σ(x)) = 4ab·D2) and is not checked by the
  certificate; (c) the "R47 §7(c) named the frontier" embellishment (see Point 1).

### Point 6 — COMPUTATIONAL LEAPS: **PASS (all recomputations succeed)**
Re-ran the certificate myself: `1871 checks, 0 failures, exit 0`; runA ≡ runB byte-identical;
my re-run byte-identical to runA; output md5 `6d665fd660c1bf97b9a267b400251a30` ✓; source
md5 `3b61f6304a5901ed9df026cdbf7b3850` ✓; source scan clean of floats/randomness/time ✓;
PINNED_PRE = 1871 ✓. Independent re-computation (different stack, /home/z/audit48_work +
sympy):
- **(a) Niven boundary**: quadratic z is a root of unity ⟺ t ∈ {−2,−1,0,1,2} — verified at
  **1209 worlds** (s ∈ [−15,15], q ∈ [1,39]) with exact pair-arithmetic order search
  (complete: a root of unity of degree ≤2 has order n with φ(n)≤2, and φ(n)≤2 ⟺
  n ∈ {1,2,3,4,6}, verified for n ≤ 2000); cross-checked via cyclotomic resultants: the
  rational traces of all roots of unity of orders 1..20 are exactly {−2,−1,0,1,2}. **0
  mismatches.** (Bonus door law: D2 = q(t−2), so t=2 never co-occurs with D2<0 — the
  Niven value 2 is a vacuous disjunct in the CM door, harmless.)
- **(b) Strata counts**: my own doors over the same grid: **CM 64, RM 68, UC 516, FOLD 24,
  DEGEN 8, total 680** ✓; 516/680 = 75.9% ≈ 76% ✓; hostile wider grid s ∈ [−60,60],
  q ∈ [1,500] (60,500 worlds): **0 leaks, 0 exceptions**; no D2<0 squares; no FOLD torsion
  phases (rational phase ±1 impossible at q>0).
- **(c) Norm rationality at (5,10)**: K = Q(√−15), x = 3+2√−15: **N(x) = 69 ∈ Q, ≥ 0**
  (also 1, 760, 1219, 15 for the other letters); float cross-check |3+2i√15|² = 69 ✓.
- **(d) Cancellation**: z·σ(z) = 1 verified at RM (5,2),(4,1),(6,2),(7,2) and UC
  (5,10),(7,14),(3,6),(3,4),(9,36),(1,2) plus CM/FOLD controls, and **symbolically as an
  identity in Q(s,q)** (numerator = denominator = 4q = s²−D2; `simplify(z·σ(z)−1)=0`),
  with `z+z^{-1}=(s²−2q)/q` and `z²−tz+1=0` also identity-verified.
- Also verified: the six UC instances' claimed t ∈ {1/2, 3/2, −1/2, 1/4, 1/4, −3/2} and
  D2 ∈ {−15,−7,−15,−7,−63,−7} ✓; CM control orders 2,3,4,6,3,4 ✓; projector laws
  (P_A²=P_A, P_A+σ(P_A)=I) re-derived at (5,10),(5,2),(9,36),(1,2) ✓; trace law
  ch(O1+O1)−ch(O1+O−1) = [0,2,0] = 2h ✓; ψ alternating and isotropic ✓.
The *computational leaps* are therefore not in the arithmetic — they are in the
**interpretation** (Points 3, 4, 10).

### Point 7 — CASE LEAKS: **PASS**
Degenerate D2=0: handled by a dedicated branch (z=1; note the K-pair representation is
degenerate at D2=0 — z = (1, 2/s) denotes 1 — and the certificate correctly avoids
pair-equality there; sabotage S4b shows misrouting degenerate worlds into the CM door
*fails* the cm-finite-order check, an unintended but effective canary). D2>0-square
(FOLD): z rational, never ±1 at q>0 (verified), hence never torsion (the n≤40 search is
therefore complete — rational roots of unity are ±1). D2<0 automatically non-square. s<0
covered (doors depend on s²). q>0 enforced at every layer. No input class missed —
confirmed by construction and by the 60,500-world sweep.

### Point 8 — CITATION ACCURACY: **PASS with one imprecision**
Spot-checked by reading (heads or full files) — all real and matching:
- `GSTLawStackRound47.lean` (fold-birth shape, five equations, DRAFT discipline) ✓
- `GSTGraphV2OntologicalFoldForAllN.lean` (HodgeWorld/FoldProcessOn/`forAllN_landing`/
  `landing_cycle`; **sorry-free and axiom-free by inspection**, `#print axioms` capstones;
  the landing chain honestly labeled a supplied field) ✓
- `GSTClassicalHodgeLimitlessExactClayFinale.lean`:
  `everyHodgeClassIsRationalAlgebraic_of_fullLimitless` exists verbatim — **conditional on
  the three supplied structures G/M/R** exactly as R48 describes ✓; the zero-cycle
  countermodel `spine_laws_do_not_force_hodge` exists
  (`GSTClassicalHodgeGeometricCycleClassSpine.lean:186`) ✓
- `GST_input_axis_decomposition_round32_2026_10_28.tex` (T2 correspondence equivalence —
  (a)⟺(b) with the (a)⇒(b) direction *assuming* mixed closure; T4 irreducible core; the
  honest-reading remark) ✓
- `GST_transcendental_fold_birth_round47_2026_11_07.tex` (§7(c) frame declaration;
  conclusion scoped to "the campaign's certified frame") ✓; `AUDIT-47` record ✓
- `GST_octic_census_r3_r4_round41_2026_11_07.tex` (the general-input vanishing, with its
  own h=1,2 disclosure) ✓
- R25 stack, R31, R35, R44, R45, R46 derivations exist; R46's "all 114 committed worlds"
  verified in-file ✓
- **Imprecision (F7a)**: "R35–R43 censuses" cites a range that includes **round 42, for
  which no derivation or record exists anywhere in the repo** (the round sequence skips
  42). **Provenance oddity (F7b)**: the certificate is labeled "v2, the post-AUDIT-48
  repair batch" while AUDIT-48 (this audit) had not yet run — a self-referential label.
- CI-green run numbers cannot be re-verified here (no Lean toolchain in this environment
  — confirmed); the Lean files themselves are sorry-free by inspection.

### Point 9 — HOSTILE COUNTEREXAMPLES + SABOTAGE: **arithmetic PASS, sabotage 5/7 caught**
Counterexample hunt:
- (s,q) with q>0 landing in **no** stratum: none exists — doors are total (case analysis
  + 60,500-world sweep).
- A phase where the cancellation fails: impossible — z·σ(z)=1 is a polynomial identity
  (symbolic verification); the certificate's X3 first check computes it exactly at every
  input.
- A UC instance where the norm is irrational or negative: impossible — N = a²−D2·b² ∈ Q
  and D2<0 forces N ≥ a² + |D2|b² ≥ 0 (verified at 5 letters + floats).
- **The counterexample to the *claim* is structural, not arithmetic**: take X a general
  smooth projective variety whose H^{2p−1} carries no 2-dimensional rational letter
  structure (e.g. a general cubic fourfold: H³ is 10-dimensional, general Mumford–Tate
  group; no rational 2×2 "letter action" with integral (s,q)). There is no extracted
  phase, no stratum, no (s,q) — the weld's "every extracted phase lands in a receipted
  stratum" has no referent; and nothing in the round produces, on such X, the integrable
  pure pair (P,M) with ch(P)−ch(M)=mα for a transcendental α (the born instance lives on
  P²). The closing string does not cover this X except by invoking the supplied
  landing-chain field — i.e., by hypothesis.
Sabotage battery (copies in /tmp/audit48_sab; originals untouched):
- **S1** delete the UC stratum increment → `X5:strata-exhaustive` + `uc-stratum-nonempty`
  FAIL, exit 1. **CAUGHT** ✓
- **S2** fake Niven value (add 1/2 to the door) → check count shifts to 1869 → SEAL
  BROKEN, exit 1 (the door would also fail: t=1/2 worlds mislabeled CM with no finite
  order). **CAUGHT** ✓
- **S3** delete one check (H10) → SEAL BROKEN (1870 ≠ 1871), exit 1. **CAUGHT** ✓
- **S4b** disable the DEGEN door (degenerate worlds routed down the chain) → 8 ×
  `cm-finite-order` FAIL (the degenerate K-pair (1, 2/s) never literally equals (1,0)),
  exit 1 — the count seal alone would NOT have caught this (8 checks swap for 8), the
  door logic does. **CAUGHT** ✓
- **S5** break `knorm` (drop −D2·b²) → 615 failures, exit 1. **CAUGHT** ✓
- **S7** gut the failure recorder (`if False:`) → 1871 checks, "0 failures", RESULT:
  PASS, exit 0 — **NOT caught internally**; caught only by the external source-md5 anchor
  (sabotaged md5 3c828307… ≠ anchored 3b61f630…). **ESCAPE (documented class)** ✗
- **S8b** compensated substitution (delete H10, insert a decorative check before the seal)
  → count seal preserved (1871), RESULT: PASS, exit 0 — **NOT caught internally**; caught
  only by the external md5 anchor (9088ea05… ≠ 3b61f630…). **ESCAPE (documented class)** ✗
Consistent with AUDIT-47's residual register: the count seal defeats pure
deletions/insertions, the doors defeat semantic sabotage, and the gutting/substitution
classes are defended only by the external receipt (the md5 printed in the tex — present
and correct, but only if the reader checks it).

### Point 10 — BLOCKED-ROUTE SMELL: **FAIL (the load-bearing smell)**
- The weld's proof of Theorem 3 says "(b1) … the R41 general-input vanishing and the R32
  T2 (a)⇒(b) direction close the mixed sector at general inputs" and "with (b1) and (b2)
  discharged at every stratum, the R32 Theorem 4 equivalence yields the rational Hodge
  conjecture on the open sector at *every* input of *every* smooth projective complex
  variety". Discharging (b2) runs through the committed landing chain (declared, but
  mislabeled "standard mathematics at its proven scope" — F3). Discharging (b1) at
  *actual* general varieties runs through R41's vanishing — which R41 itself discloses as
  computed at h = 1, 2 only (F10) — and at special strata through committed censuses that
  live on the model worlds, not on varieties.
- **The undeclared step**: "every phase lands in a receipted stratum" presupposes the
  frame's two-letter-world parameterization covers the actual input space. R47 §7(c)
  declared exactly this limitation ("The universal quantifier of the R32 Theorem 4
  equivalence is the frame's universal quantifier"); R48's scope inventory contains no
  corresponding item — the declaration was dropped at the same round that the quantifier
  jumped from "the frame" to "every smooth projective complex variety". This is a
  quiet assumption of what must be proved (F2), and it is almost certainly false as a
  blanket modeling claim (general Mumford–Tate structures do not reduce to quadratic
  phases).
- The Lean terminal composition is conditional on three supplied structures (G, M, R);
  R48's remark says "This round's weld supplies them" — but the supply is narrative
  assignment (G "from the fold-channel's geometric semantics", M "from the
  conserved-charge/tower nonvanishing", R "from the spread's projector/one-source
  machinery"), not construction. The countermodel discipline is respected *in words*
  (the witness is "the non-intrinsic geometric input"), but nothing is constructed.
- What is NOT smuggled: the landing chain, the R32 T2/T4 status, and the Lean draft
  status are all declared in §scope(d). The declaration is incomplete (F2) and one
  commitment is mischaracterized (F3), but the campaign's commitment-labeling convention
  is otherwise followed.

---

## 2. Findings (numbered, with severity)

- **F1 (BLOCKER — claim match / packaging).** The Clay statement is presented as an
  unconditional theorem (Theorem 3 + proof + boxed closing string; abstract: "This round
  closes that frontier"; §8: "Q2 — the Clay statement — is closed") while the proof is
  conditional on commitments of comparable strength. R32's own honest-reading remark:
  the residual content "is not known, and no reformulation of it as a hypothesis-packet
  can close it"; `FoldProcessOn.landing_cycle` is exactly such a packet (a supplied field
  of the CI-green capstone, hypothesis form: ∀v, landing v → scale v ≠ 0 → ∃Z, cl Z =
  α). §scope(d) even says the strength "is the conjunction of (a)–(c)" — but (d) is
  load-bearing.
- **F2 (BLOCKER — silent circular reduction / uniformity).** The frame→variety
  instantiation is assumed, not proved and not declared: no receipt extracts a quadratic
  phase (an (s,q)) from the cohomology of an arbitrary smooth projective variety. R32's
  middle extraction yields M_mid/J_mid (abelian-variety realization — classical), not a
  two-letter phase. R47 §7(c) declared the frame quantifier; R48 drops it exactly where
  the quantifier becomes "every variety". For general X the strata partition has no
  referent (cf. the hostile structural counterexample, Point 9).
- **F3 (MAJOR — mischaracterized commitment).** The landing chain is glossed "standard
  mathematics at its proven scope" (Theorem C + Serre generation + Thom–Porteous + GAGA).
  The usable direction (integrable pure pair of algebraic bundles given ⟹ α algebraic via
  GRR/Chern roots) is standard; the needed direction (existence of the pair at an
  arbitrary transcendental α) is HC-hard. The certificate's actual witness is a fixed
  pair of line bundles on P² realizing 2h — the divisor (p=1) case, outside the open
  sector where the conjecture lives — repeated identically at every input (X6).
- **F4 (MAJOR — uniformity of the certificate).** ~440 of the 1871 checks are
  per-instance repetitions of input-independent computations or fixed toy identities:
  X1 (190 × i²=−1 in Q(i), input in the name only), X3's cancellation avatar (57 ×
  `(i·x)(−i·x)=x²`, never referencing z/D2/s/q), X6 (19 × the same P² pair; plus
  `h*h==F(1)` labeled "hard-Lefschetz instance"). No check connects any (s,q) to any
  variety's cohomology. (The genuinely input-sensitive mass — X5's 1288, X0's 87, X4's
  80, X3's 19 — is purely arithmetic and is sound.)
- **F5 (MINOR — definition drift / overstatement).** (a) R47 Lean's trace-law comment
  ("pure at grade 2, zero at grades 0,1,3,4") vs the shared P² witness / capstone / R48
  (pure at grade 1, 2h) — inherited grade-convention inconsistency. (b) Tex's "nonzero on
  conjugate pairs" for ψ is false for the witness x=1 (ψ(1,σ(1))=0; ψ(x,σ(x))=4ab·D2) and
  is unchecked. (c) "R47 §7(c) named the frontier" — §7(c) declares the frame scope; it
  does not name a full-generality frontier.
- **F6 (MINOR — Lean draft shape defects).** `phase_quadraticity_sign_blind`'s `hz` gives
  z as a *rational* expression with no √D2 component; since σ fixes Q, the stated
  conclusion z·σ(z)=1 becomes z²=1 — literally false for the given z (e.g. (5,10):
  z=1/16). The statement is semantically incoherent with Lemma 1 (missing the quadratic
  structure). `unit_circle_fold_birth`'s `ht` reads "t ∉ Z" (not an integer) instead of
  "t ∉ {−2,−1,0,1,2}" — a different condition (it implies the intended one, so the shape
  proves less than the tex theorem). Both are DRAFT-status defects, not compiled claims.
- **F7 (MINOR — citation hygiene).** (a) "R35–R43 censuses" includes round 42, which does
  not exist in the repo (derivations or records). (b) The certificate's "v2, the
  post-AUDIT-48 repair batch" label is self-referential — no AUDIT-48 preceded this audit.
- **F8 (MINOR — decorative checks).** Tautologies inside the count: `X0:fold:
  rational-phase` (a Fraction's denominator ≥ 1 — always true), `X6:p>d/2:
  hard-lefschetz-instance` (h·h==F(1)), X2's parity constants. Acceptable as "finite
  shadows" but the 1871 figure overstates the distinct verified content.
- **F9 (MINOR — residual sabotage escapes, documented).** Gutted-verifier (S7) and
  compensated-substitution (S8b) attacks pass all internal seals; only the external
  source-md5 anchor (correctly printed in the tex and matching) defends them. The defense
  requires the receipt reader to actually verify the md5.
- **F10 (MINOR — inherited uniformity exposure).** The weld's (b1) at general X leans on
  R41's general-input vanishing, which R41 itself discloses as computed at h=1,2 only —
  an extrapolation to all ranks that R48 cites without re-flagging.

**Positive findings (for the record).** (P1) The certificate re-runs clean, is
deterministic, float-free, and both md5 seals and the pinned count reproduce. (P2) Every
independently recomputable claim of the round is *correct* — including the round's real
new arithmetic: the sign-blind cancellation identity (sympy-verified as a polynomial
identity in Q(s,q)) and the exhaustive, leak-free four-stratum partition with the
reproduced counts. (P3) The scope-discipline section is the campaign's best-practice
genre and is more explicit than most mathematical writing about dependencies; the
sabotage sensitivity (5/7 caught internally) is strong; the DEGEN misroute canary (S4b)
works even though the count seal would not catch it. (P4) The capstone Lean and the Clay
finale Lean are sorry-free, and the finale honestly carries its three supplied structures
as hypotheses with the zero-cycle countermodel discipline.

---

## 3. Independent re-computation results (summary table)

| Item | Method (independent of certificate) | Result |
|---|---|---|
| Certificate re-run | direct | 1871 / 0 / exit 0; ≡ runA ≡ runB; md5s match |
| Niven iff (root of unity ⟺ t ∈ 5-set) | own K-pair order search, 1209 worlds; φ(n)≤2 ⟺ n∈{1..6} (n≤2000); cyclotomic resultants (orders 1..20) | 0 mismatches; rational traces exactly {−2,−1,0,1,2} |
| Strata counts | own doors, own grid | CM 64 / RM 68 / UC 516 / FOLD 24 / DEGEN 8 / 680; 76% |
| Partition totality | s∈[−60,60], q∈[1,500] | 60,500 worlds, 0 leaks / exceptions |
| Norm rationality at (5,10) | own pair arithmetic + floats | N(3+2√−15)=69 ∈ Q≥0; |x|²=69 |
| Cancellation z·σ(z)=1 | own pairs at 13 instances + sympy identity in Q(s,q) | holds; sign-blind identity confirmed |
| Quadraticity z²−tz+1=0, z+z⁻¹=t | sympy identities | hold identically |
| Projectors (X4) | own 2×2 pair-linear algebra at 4 instances | P_A²=P_A, P_A+σ(P_A)=I |
| Trace law, ψ alternating, grades | own arithmetic | 2h pure grade 1; ψ alternating & isotropic; ψ(x,σ(x))=4ab·D2 (⇒ F5b) |
| UC instance data (t, D2) | direct | match tex exactly |

## 4. Sabotage results (summary)

| Attack | Internal catch | Exit |
|---|---|---|
| S1 delete UC stratum | YES (coverage count ×2) | 1 |
| S2 fake Niven value | YES (count seal + door) | 1 |
| S3 delete a check | YES (pinned count 1870≠1871) | 1 |
| S4b disable DEGEN door | YES (8 × cm-finite-order) | 1 |
| S5 break knorm | YES (615 failures) | 1 |
| S7 gut failure recorder | NO — external md5 only | 0 |
| S8b compensated substitution | NO — external md5 only | 0 |

---

## 5. Required repairs (for a re-submission)

- **R1 (blocker-level).** Re-state Theorem 3 conditionally: either scoped "on the frame"
  (R47 §7(c) discipline) with the frame→variety instantiation named as the open frontier,
  or with the landing-chain and K-correspondence conjuncts as explicit hypotheses in the
  theorem statement. Strike "Q2 — the Clay statement — is closed" (abstract, §8) and
  re-align with R32's honest-reading remark.
- **R2 (blocker-level).** Add the missing dependency-inventory item: the
  frame-models-every-variety step (existence of an extracted quadratic phase at every
  input of every X) must be declared as an unproved commitment — or the jump to "every
  variety" withdrawn.
- **R3 (major).** Re-characterize the landing chain: remove the "standard mathematics at
  its proven scope" gloss; state that the existence direction (integrable pure pair at
  arbitrary transcendental α) is the HC-strength content, per R32's packet-equivalence
  discipline.
- **R4 (minor).** Repair the Lean shapes: give `phase_quadraticity_sign_blind` a genuine
  quadratic z (K with √D2, σ the Galois involution); fix `unit_circle_fold_birth`'s `ht`
  to t ∉ {−2,−1,0,1,2}.
- **R5 (minor).** Hygiene: correct "R35–R43" (R42 does not exist); de-self-reference the
  "post-AUDIT-48" label; qualify "nonzero on conjugate pairs" (true iff b≠0); mark the
  decorative checks (X6 hard-Lefschetz instance, X0 fold rational-phase, X2 parity
  constants) as definitional; reconcile the R47 grade-2 vs grade-1 trace-law wording.

---

## FINAL VERDICT (original audit, artifact batch v2)

**FAIL.** The round's arithmetic is correct, its certificate is genuine, deterministic,
and tamper-sensitive (with two externally-anchored escape classes), and the UC-stratum
arithmetic (Theorem 1's algebraic content) and the exhaustive stratification (Theorem 2)
are real, verifiable mathematics. But the ordered statement — Q2, the Clay statement, at
full generality — is claimed as closed while its proof runs through an undeclared
frame→variety instantiation (F2) and a committed landing chain of strength comparable to
the conjecture itself, mislabeled as standard mathematics and packaged as closure (F1,
F3). Under the campaign's own anti-circularity discipline this is the blocked route.
Repairs R1–R3 are required before any re-submission; with them (and the minors R4–R5) the
round would stand honestly as: *the frame's input axis closed at every arithmetic
stratum, the UC majority included — the closing string remaining conditional on the named
commitments.*

---

# RE-AUDIT ROUND (v3) — THE CLOSING RE-AUDIT

**Auditor**: the same independent adversarial agent (AUDIT-48), resuming. The repair
batch (v3) was applied to the derivation and the Lean face; the certificate was left
unchanged per this auditor's own ruling (the arithmetic was sound; the blockers were at
the claim level). Originals re-read in full; seals re-verified.

## v3 repair verification

**Certificate + seals (unchanged by design).** Source md5
`3b61f6304a5901ed9df026cdbf7b3850` — identical to the audited v2. Re-run: **1871 checks,
0 failures, exit 0**, byte-identical to runA/runB, output md5
`6d665fd660c1bf97b9a267b400251a30` reproduced. PDF recompiled: 121,314 bytes = 118.47
KiB, matching the claimed size.

**R1 (for F1) — VERIFIED REPAIRED.**
- §5 now opens with `Definition [The two named commitments]` naming **(C1)** (the landing
  chain: "HC-strength committed content --- not proved, not standard", with the
  functorial/existence direction split) and **(C2)** (the instantiation hypothesis,
  "declared unproved; for general X with higher-degree Mumford--Tate fields the (s,q)
  referent does not exist" — my hostile counter-referent, now named in the artifact).
- Theorem 3 is retitled **"The conditional weld"** and states "Assume (C1) and (C2)"
  before the Clay-form conclusion; the proof is titled "under (C1), (C2)" and each
  load-bearing step is tagged ("under (C2), the middle extraction's input ... is a
  two-letter world"; "under (C1), the landing chain converts ...").
- The boxed string now reads **"Under (C1) and (C2): every rational (p,p) class on every
  smooth projective complex variety is algebraic."**
- The abstract states Theorem 3 as conditional and reduces "the remaining falsifiable
  line for Q2 ... to exactly the pair of named objects (C1, C2)".
- **Corollary "The unconditional content of this round"** cleanly separates: frame input
  axis closed at every arithmetic stratum (unconditional, and independently verified by
  this auditor) vs. the conditional closing string.
- The round record (final section) states both contents separately; §scope now says the
  strength "is the conjunction of (a)--(d)" — repairing the earlier (a)–(c) inconsistency
  I flagged, since (d) is load-bearing.
- **Unconditional-closure sweep**: grep over the full tex for every "is closed / Q2 /
  closing string / unconditional / conditional" occurrence — every claim-bearing
  environment is either frame-scoped arithmetic (verified true by me) or explicitly
  conditional. The v2 phrase "Q2 --- the Clay statement --- is closed" is gone. Residual:
  the *title* still reads "the closing string for Q2 at full generality" — a topic
  descriptor, not a claim; ruled cosmetic (see residual register).

**R2 (for F2) — VERIFIED REPAIRED.** (C2) is declared in all four required places: the
Definition (§5), the abstract, §7 item (d) ("the frame's own boundary, declared unproved
(for general X with higher-degree Mumford--Tate fields the (s,q) referent does not
exist)"), and the Lean face (`hC2 : ∀ i, IsTwoLetterWorld (W i)` as an explicit
hypothesis of the renamed weld theorem). The proof of Theorem 3 now routes the
frame→variety step explicitly through (C2). The silent assumption is silenced: it is now
a named, declared, unproved hypothesis.

**R3 (for F3) — VERIFIED REPAIRED.** §7 item (a) now reads "Standard mathematics (each
used at its proven scope, supplying functorial directions only)" and lists the functorial
toolkit (GAGA, Serre generation, Thom–Porteous) separately from the existence-direction
commitment; item (d) states the landing chain "is *not* standard-classical (the functorial
direction is standard; the existence direction is HC-strength content)". Definition (C1)
carries the same split. This matches R32's packet-equivalence discipline as demanded.

**R4/R5 (minors) — VERIFIED REPAIRED (with cosmetic residuals).**
- Lean Lemma 1 (`phase_quadraticity_sign_blind`) now carries `rho` with `rho * rho =
  (D2 : ℚ)`, `sigma rho = -rho`, and `z = a + b * rho` with a = (s²+D2)/(s²−D2), b =
  2s/(s²−D2). **I verified the repaired shape is semantically coherent and true**: z·σ(z)
  = a² − b²·D2 = (s²−D2)²/(s²−D2)² = 1 identically; 2a = t; z² − tz + 1 = 0 (sympy,
  symbolic in s,q). The v2 defect (σ fixing the rational z, making the conclusion z²=1 —
  false) is gone.
- `unit_circle_fold_birth`'s `ht` now tests membership in the 5-element set
  `{(-2:ℚ),(-1:ℚ),(0:ℚ),(1:ℚ),(2:ℚ)}` — the Niven set, not the integers.
- The weld theorem is renamed `conditional_weld_universal_instantiation` with `hC2` as an
  explicit hypothesis; its comment block states the conditional form and the unconditional
  Corollary content.
- Tex: "the census rounds R35--R41 and R43" in all three occurrences (§2 state-at-receipt,
  Theorem 2, §7(b)) — R42 eliminated. The **grade-conventions remark** (§7, "Grade
  conventions and witness scope") reconciles the letter-grade (P² model, grade 1) vs
  carrier-grade (R47 phrasing, c₂-grade) conventions as "the same law at the respective
  grade", and — exactly matching my computation ψ(x,σ(x)) = 4ab·D2 — qualifies the
  polarization: "it vanishes on the rational letter x=1 --- the conjugate-pair
  nonvanishing holds for letters with nonzero √D₂-component, not for the scalar letters".
  Theorem 1(ii) is qualified in-line ("nondegenerate on conjugate pairs with nonzero
  √D₂-component"). The certificate section is labeled v3 with the accurate note that the
  arithmetic was verified sound by AUDIT-48's independent re-derivation and the repairs
  land at the claim level.

## Per-finding rulings (v3)

| Finding | v2 severity | v3 ruling |
|---|---|---|
| F1 unconditional packaging of the Clay statement | BLOCKER | **REPAIRED** — conditional weld with (C1)/(C2) as explicit hypotheses; conditional boxed string; conditional abstract; unconditional content separated into a Corollary; §scope conjunction now (a)–(d) |
| F2 undeclared frame→variety instantiation | BLOCKER | **REPAIRED** — (C2) named and declared unproved in Definition, abstract, §7(d), Lean `hC2`; higher-degree Mumford–Tate counter-referent stated in the artifact |
| F3 landing chain mislabeled standard | MAJOR | **REPAIRED** — "supplying functorial directions only" in (a); existence direction explicitly "not standard-classical", HC-strength, in (d) and Definition (C1) |
| F4 input-insensitive check repetitions (~440/1871) | MAJOR | **ACCEPTABLY DISCLOSED-BY-DESIGN** — the new remark discloses the per-instance repetition as the campaign's receipt convention and locates the input-sensitive content in X0/X2/X4/X5, which matches this auditor's instrumentation exactly (X0 87 + X2 108 + X4 80 + X5 1288 sensitive; X1 190, X3-avatar 57, X6 19 fixed/repetitive). Re-issuing a deduplicated certificate would break the sealed md5 chain for cosmetic gain while the arithmetic is sound and independently verified. Disclosure accurate and honest → accepted |
| F5 definition drift (grade convention; ψ overstatement; §7(c) phrasing) | MINOR | **REPAIRED** — grade-conventions remark; ψ qualified (matches ψ(x,σ(x))=4ab·D2); R35–R41+R43; §7(c) now honestly characterized via (C2) as "the R47 §7(c) boundary stated as a named hypothesis" |
| F6 Lean shape defects (no √D2 component; ht testing ℤ) | MINOR | **REPAIRED** — ρ²=D2, σρ=−ρ, z=a+bρ (shape re-verified semantically true by symbolic computation); ht is the 5-set; weld renamed with hC2 |
| F7 citation hygiene (nonexistent R42; self-referential label) | MINOR | **REPAIRED in the tex** (3 occurrences); residual: the Lean comment still reads "R35-R43" (line 95); the "post-AUDIT-48" label now has true content (this audit did verify the arithmetic sound) |
| F8 decorative checks inside the count | MINOR | **PARTIALLY ADDRESSED, ACCEPTABLE** — the repetition class is disclosed by the remark; the individual tautologies (h·h==F(1) as "hard-Lefschetz instance"; denominator ≥ 1) remain unlabeled. Cosmetic |
| F9 sabotage escape classes (gutted-verifier; compensated substitution) | MINOR | **UNCHANGED BY DESIGN** — certificate untouched per this auditor's ruling; the escapes remain defended by the external source-md5 anchor, which this auditor re-verified this round (3b61f630… reproduced). Documented, non-blocking |
| F10 R41 h≤2 extrapolation cited without re-flag | MINOR | **NOT RE-FLAGGED, INHERITED** — the (b1) route still cites R41's vanishing without re-flagging its h=1,2-only computation; disclosed at source (R41); neither (C1) nor (C2) formally subsumes it. Non-blocking |

## Residual register (v3, all cosmetic / non-blocking)

1. Tex *title* still reads "the closing string for Q2 at full generality" — a topic
   descriptor; every claim-bearing environment (theorem, proof, boxed string, abstract,
   round record, scope inventory) is conditional or frame-scoped.
2. Lean *file header* (lines 7–9) still carries the unconditional descriptor, while the
   theorem blocks below are conditional; Lean line 15 says "v2" (the tex says v3); Lean
   line 95 still says "R35-R43" (includes the nonexistent R42).
3. Tex labels the unchanged .py as "v3" while the file's internal docstring says "v2" —
   the parenthetical ("the certificate's arithmetic was verified sound by AUDIT-48's
   independent re-derivation; the repairs land at the claim level, in this derivation")
   explains the intent; strictly, the .py is the unchanged v2.
4. Typo at §7(b): "the the census rounds".
5. F10's inherited exposure (R41's h=1,2 bound inside the conditional weld's (b1) route),
   disclosed at source only.
6. F8's individual tautologies unlabeled; F9's escape classes defended only by the
   external md5 anchor (re-verified by this auditor).

None of these reverses or weakens any repaired claim; none is load-bearing.

## RE-AUDIT FINAL VERDICT

**PASS.** Both blockers are repaired (F1: the Clay statement is now stated only
conditionally, under the two explicitly named and declared commitments, with the
unconditional content separated into a verified Corollary; F2: the frame→variety
instantiation is now the named, declared-unproved hypothesis (C2), present in the
Definition, abstract, scope inventory, and Lean hypothesis `hC2`, with the Mumford–Tate
counter-referent stated). Both majors are resolved (F3 repaired with the
functorial/existence split; F4 accurately disclosed by design, matching this auditor's
own instrumentation). The minors are repaired or acceptably disclosed. The certificate is
unchanged with both seals reproducing; the arithmetic — already independently re-derived
and verified sound in the original audit round (Niven boundary, exhaustive leak-free
stratification with reproduced counts, norm rationality, the sign-blind cancellation
identity as a polynomial identity) — stands as the round's unconditional content. The
round now claims exactly what it proves: *the frame's input axis closed at every
arithmetic stratum, the UC majority included; the closing string for Q2 conditional on
the named pair (C1, C2) — the remaining falsifiable line reduced to those two objects.*
The audit loop is CLOSED at PASS.
