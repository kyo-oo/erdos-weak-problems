# Audit — Round 29 product transport — 2026-10-31

Auditor: independent adversarial auditor (Task 2-a). Artifacts audited:
`research/derivations/GST_complete_mathematics_round29_2026_10_31.tex` (§6, §7),
`research/experiments/product_transport_checks.py` (27 checks), against the committed
law stack `GST_law_stack_full_derivations_round25_2026_10_31.tex` §2/§3. All computations
in `/tmp/audit_29/` (exact int/Fraction arithmetic; repo untouched; sabotage runs on copies).

## Verdict: PASS_WITH_REPAIRS_REQUIRED
The lattice-level mathematics of the round (Theorems 6.2(1),(3), 6.3, 6.4, 6.5) is **correct**
— every module-level claim was independently re-derived and survived all attacks. But the
Hodge bridge (§6.3 + §7 item 3 + the disposition) is **false as stated and vacuous in
content**, one theorem (6.2(2)) is **false at its printed generality** (dropped torsion-freeness),
and **7 of the 27 certificate checks are vacuous, dead-coded, or test the wrong predicate**
while the .tex and the certificate docstring claim otherwise. The round may not claim
"Q1 extended to the product family" until F1–F3 are repaired.

## Claim match
- Thm 6.2(1),(3) ↔ certificate T1 (0001–0004, 0014, 0015): **match** (partial coverage, see F4).
- Thm 6.3 + both corollaries ↔ T2 (0005–0008): **match**, and the checked law is genuinely
  verified (solver validated against an independently re-derived criterion: 15,625 exhaustive +
  20,000 random vectors, zero disagreements).
- Thm 6.4 ↔ T3 (0009–0013): **match** of content, but 0011 is a hardcoded determinant and 0012
  is a tautology (F3); the genuine backing is 0005/0009/0010/0013.
- Thm 6.5 ↔ T4 (0017–0020): **mismatch** — the certificate docstring and .tex §6.6 claim the
  return-leg factor is receipted; check 0018 is `len(range(m)) == m` (vacuous, F3).
- §6.3 Hodge-typing claims: **no certificate backing at all**, and they are false (F1).
- Disposition bullet 1 ("Q1 … extended this round to the product family … deck–door laws
  transported universally in Y") vs. what is proven (lattice-level laws over an **empty** set of
  Hodge-typed rays): **scope inflation** (F1, F6). The closing statement and §7 item 3 do carry
  the "at the lattice level" qualifier; the disposition bullet and abstract do not.

## Findings

### F1 — The Hodge-typing subsection misidentifies the (p,p) input set; the "Hodge-typed product ray" set is empty; §7 item 3 is vacuous — severity: blocker
- **Location:** §6.3 ("The Hodge typing and the input-sensitivity line"); §7 Theorem 6.6 item 3;
  Disposition bullet 1; Abstract (iii)/(iv).
- **Issue (three independent defects, all verified by exact computation):**
  1. **The stated input set is empty.** For every smooth projective Y and every p, the image of
     H^{2p−1}(Y,Z) in H^{2p−1}(Y,C) is conjugation-fixed; a conjugation-fixed class of pure type
     (p−1,p) lies in H^{p−1,p} ∩ H^{p,p−1} = 0 (Hodge decomposition is a direct sum; (p−1,p) ≠ (p,p−1)).
     Hence H^{p−1,p}(Y) ∩ H^{2p−1}(Y,Z) = Tor H^{2p−1}(Y,Z) — for p = 1 exactly {0} (H¹ is
     torsion-free). Verified computationally (probe P5a: a·e′ + b·f′ purely (0,1) ⟺ a = b = 0).
     The set of "primitive Hodge-typed product rays" over which §7 item 3 and §6.3's "the machine
     pins the door at m*=2 on every primitive Hodge-typed product ray" quantify is therefore
     **empty** (torsion debris aside).
  2. **e is not purely (1,0).** e = ½[(e+if) + (e−if)] with e+if ∈ H^{1,0}, e−if ∈ H^{0,1}
     (the eigenray e+if is the (1,0) class — probe W1: γ(e+if) = i(e+if)). So even a hypothetical
     pure ℓ would not make e⊗ℓ purely (p,p): e⊗e′ has a (2,0)-component equal to ¼ (probe P5c).
     Also "their conjugate f⊗ℓ-type rays" is wrong twice: the Hodge conjugate of e⊗ℓ is
     e⊗conj(ℓ) (e is real), and f is not the conjugate of e.
  3. **The actual (p,p) inputs of the one-letter sector are combinations, not rays — and the
     theorem misses them.** x = e⊗p + f⊗q (p,q ∈ H^{2p−1}(Y,Z), middle-piece condition
     p^{p−1,p} = −i q^{p−1,p}) is purely (p,p) for suitable Y. **Counterexample (p = 1):**
     on B = E×E′ (both CM by i), x = e⊗e′ + f⊗f′ = ½(E⁺⊗E′⁻ + E⁻⊗E′⁺) is integral and purely
     (1,1) — exact Gaussian-rational verification P5b: (2,0)- and (0,2)-coefficients are exactly 0,
     (1,1)-coefficients exactly ½. This is the Poincaré-bundle divisor class; it lives in exactly
     the module M of Theorem 6.3; it is not of the ray form; and its door behavior (refused at
     m = 1 since e′+f′ ∉ 2L, admitted at m = 2 — P5d) is not covered by the ray analysis.
- **Consequence:** §7 item 3 ("The product rows, proven this round") is vacuous as an FS row; the
  extension of Q1 to the product family adds **no** Hodge-input coverage beyond Lefschetz (1,1)
  (item 1): the non-divisor (p,p) inputs of E×Y lie either in the deck-trivial e∧f⊗ℓ′ sector
  (γ = id there — the door never opens; that is Y's own input-axis content) or in the unanalyzed
  combination sector. The abstract's "the FS_∀ theorem on the extended world model, every row
  receipted" and Disposition bullet 1's "extended this round to the product family" are scope
  inflation relative to the module-level proofs.
- **Repair:** rewrite §6.3 with the correct input identification (combinations e⊗p + f⊗q with the
  middle-piece + phase condition; rays impossible by conjugation); state the emptiness of the ray
  set on the face (it is itself a sharp form of the input-sensitivity discipline); re-scope §7
  item 3, Disposition bullet 1, and the abstract to "lattice-level transport; no new (p,p) inputs
  covered".

### F2 — Theorem 6.2(2) silently drops R1's freeness hypothesis; false for Y with 2-torsion — severity: major
- **Location:** §6 Theorem 6.2(2) ("M_a^{C_4}=0, N=0, H²(C_4;M_a)=0 …") and the §6 intro
  ("any integral cohomology lattice L_Y ⊆ H*(Y,Z)").
- **Issue:** the committed R1 (§2, and law stack §2.2) hypothesizes a *finitely generated free*
  Z-module; Theorem 6.2 states the vanishing for "an inert lattice L = L_Y" with no freeness.
  **Counterexample (exact, probe P6):** L = Z ⊕ Z/2 (realizable: Y = Enriques surface,
  L = H²(Y,Z) ⊇ Z/2, γ inert), t the 2-torsion element: v = (e+f)⊗t satisfies γ(v) = v ≠ 0, so
  M^{C_4} ≠ 0 and H²(C_4;M) = M^{C_4}/NM ≠ 0 (N = 0 still holds; H¹ 2-elementarity also still
  holds). The refined door law 6.3 and both corollaries are **unaffected** — they are valid for
  arbitrary abelian L (structural reason: L/2L is an F₂-vector space, so mℓ ∈ 2L ⟺ m even or
  ℓ ∈ 2L — probe P4g).
- **Repair:** add "torsion-free" to the hypothesis of 6.2(2) (one word), or restate
  M_a^{C_4} ⊆ M_a[2].

### F3 — Certificate receipt inflation: 7 of 27 checks vacuous / dead / wrong-predicate — severity: major
- **Location:** `product_transport_checks.py` checks 0012, 0018, 0019, 0302, 0303, 0305, 0307;
  docstring "every check CAN fail"; .tex §6.6 sentence.
- **Issue (each verified by direct evaluation and by sabotage runs on copies):**
  - **0018** ("return-leg factor = m"): computes `sum(1 for _ in range(m)) == m` — the length of
    a Python range. No deck, cover, trace, or class appears. Cannot fail. The claim (certificate
    docstring T4 and .tex §6.6) that the return leg is receipted is **false**; the identity
    (q∘δ)*α̂_m = mα rests on the law stack §3.5 proof alone.
  - **0012** ("plane door iff m even"): `plane_in_im(m)` is *defined* as (m%2==0) AND a clause
    satisfiable exactly when m is even — a self-comparison; verified tautological for m = 1..199.
  - **0302/0303** ("computed H² = Z/2", "H² = M/4M"): compute |{a mod 2}| and |{a mod 4}| over
    fixed integer ranges — input-free constants; cannot fail. The .tex §6.6's "the swap deck
    σ²=+1 detected with computed H²=Z/2" overstates: the group theory (M^{C_4} = diagonal,
    N′M = 2·diagonal) is asserted in comments, never computed.
  - **0305** ("degenerate map detected"): determinant of a hardcoded singular matrix; no
    detection machinery runs; cannot fail.
  - **0020** ("Gaussian exchange commutes"): `block_gamma` = [pgamma(b) for b in blocks] — *any*
    per-block map commutes with the block permutation by construction (demonstrated with a
    deliberately crazy map); cannot fail.
  - **0019** ("antipodal pairs … the ±i orbit law"): first conjunct ends in `or True` — dead
    code; the live residue is the single spot-check γ(e₀) ≠ e₀; nothing about antipodal pairs,
    arities, or orbits is tested.
  - **0307** ("naive 'iff m even' law MISclassifies — detected"): the written predicate
    (m%2==1) != in_im(…) fires exactly at the **even** arities — where the naive law *agrees*
    with the refined law; the true misclassification set is the odd arities (m=1: naive refuses,
    refined admits). The control also **still passes under a totally broken always-False
    membership solver** (sabotage run). The .tex's "the naive law proven to misclassify
    2-divisible rays" is genuinely covered by 0007, but 0307 itself tests the wrong condition.
  - Consequently the docstring's "Hostile controls (every check CAN fail — ledger 102 garbage
    discipline)" is false for 0012, 0018, 0302, 0303, 0305, 0020.
- **Mitigation (verified):** the genuine core is live. Sabotage runs on copies: swap deck
  (γ: (x,y)↦(y,x)) fails 0001–0007, 0009, 0013 (9 checks); trivial deck fails 11 checks
  (incl. 0019); sign-broken rotation (γ: (x,y)↦(−y,x)) fails 0009/0010 (it has the *same*
  im(γ−1) — caught only by the plane-exchange checks); always-False solver fails
  0004–0007, 0013. The module-level content of T1/T2/T3 is really verified.
- **Repair:** replace 0018 with a genuine module-level return-leg computation (Θ_m(α) =
  Σ pr_i*α pulled back along the diagonal equals mα — easy on a small test module); fix 0307's
  predicate to (m%2==0) != in_im(…); delete the `or True` and test actual antipodal structure;
  derive the 0302/0303 quotients from the deck matrices; note 0012's tautology; correct the
  docstring and .tex §6.6; re-run the double-run receipt.

### F4 — Coverage gaps between the .tex claims and the certificate — severity: minor
- Thm 6.2(3) asserts deck-fixity of "every e∧f⊗ℓ"; 0015 tests the bare word e∧f only.
- 0003 (invariants vanish) is a 3-vector spot-check; an exact integer solve of γv = v is easy
  and stronger.
- The word model tests k_E = 3 words — fictitious (Λ³⟨e,f⟩ = 0; the letter space has rank 2);
  harmless as a superset, but the declared bound "words total degree ≤ 4" tests non-existent words.
- §6.3's Hodge-typing claims carry no receipt at all (compounds F1); §6.5's family-transport
  components (D_m mixed structure, transfer, sector laws) are unreceipted — the .tex honestly
  does not claim they are, but the only offered receipt block (0017–0020) is the weakest.
- §7 item 2's "1,708 checks across 15 scripts, all re-run green this session" was not re-verified
  here (out of audit scope); one spot-run of `rotation_deck_checks.py`: 59 checks, exit 0, green.

### F5 — Plane-matrix convention mismatch between .tex and certificate — severity: minor
- Thm 6.4 states the (γ−1)-matrix as [[−1,1],[−1,−1]] (column convention); the certificate
  hardcodes ((−1,−1),(1,−1)) with "rows = images' plane coordinates" — the transpose (verified).
  Both determinants are 2, so no mathematical error, but the two artifacts print different
  matrices for the same object with no convention declared; and 0011's determinant is computed on
  the hardcoded matrix rather than derived from pgamma (justified only together with 0009/0010).
- Repair: declare the convention in both artifacts.

### F6 — Scope-language inconsistency for m* and the extension — severity: minor
- §7 item 3 and the closing statement carry "at the lattice level"; Disposition bullet 1 and the
  abstract do not. "The door-pin m*=2 at the lattice level" conflates the lattice-level door-pin
  with the full principal fold-scale m* (whose bundle side is, by the .tex's own §7 boundary
  remark, open for transcendental ℓ). Repair: uniform phrasing "lattice-level door-pin = 2; the
  full m* is not established for product rays".

## Counterexample / computation attempts
Independently verified (survived the attack — the round's lattice core is sound):
- **[i]-convention** re-derived from the lattice Λ = Z+iZ by dual bases: [i]*e = −f, [i]*f = e;
  order 4; [i]² = −1 on H¹ (probes P2a–P2d). Matches the committed G_LETTER convention
  (repo `rotation_deck_checks.py`, `letter_map_for_factor`: e_j ↦ −f_j, f_j ↦ e_j).
- **Letter-degree parity:** γ² = (−1)^a for a = 0,1,2 by matrix powers and by the eigenvalue
  argument (char. poly λ²+1); γ(e∧f) = +e∧f (deck-fixed divisor word) — no break at a = 2.
- **Refined door law re-derived from scratch:** (γ−1)(e⊗p+f⊗q) = e⊗(q−p)+f⊗(−p−q);
  im(γ−1) = {(r,s): r+s ∈ 2L ∧ r−s ∈ 2L} — necessary direction (all 15,625 parametrized points
  satisfy the criterion), constructive converse (p = −u, q = v), set equality in the box, and
  20,000 random vectors at coordinates ±60 — **the theorem is correct**, and valid for any
  abelian L.
- **Ray law** m(e⊗ℓ) ∈ im ⟺ mℓ ∈ 2L: unique-candidate solve over 25 adversarial ℓ's × m = 1..12 —
  correct, including all mixed 2-divisibility patterns ((2,1), (2,3), (1,2), (0,3), (6,4), (5,0,3)).
- **Primitive corollary** exhaustively: 638 primitive ℓ's × m = 1..12 — mℓ ∈ 2L ⟺ m even holds
  for **every** ℓ ∉ 2L (structural proof via L/2L as F₂-vector space, valid for any abelian L).
- **Certificate's 14-vector classification:** exactly 10 primitive / 4 in 2L — as claimed.
- **Certificate solver** (`in_im_gm1`, floor-division elimination) validated against the exact
  criterion: 15,625 exhaustive + 20,000 random vectors, zero disagreements.
- **Receipt fidelity:** two runs, exit 0, byte-identical, 27/27 checks, 0.02 s, zero float and
  zero complex literals (AST scan) — the .tex's "27 checks, exit 0, deterministic double-run
  byte-identical" claim is TRUE.
- **Family transport (Thm 6.5):** law stack §3 read in full — freeness, D_m, transfer, sector
  laws, return leg are all stated and proven for arbitrary connected smooth projective X; the
  "runs verbatim with B_Y" claim is legitimate; the Gaussian-exchange commutation is blockwise.
  (Only its *receipt* is broken — see F3/0018.)
- **Künneth:** H*(E,Z) is free in each degree, so no Tor terms — the decomposition claim is exact.

Counterexamples that LANDED:
- **F1:** H^{p−1,p}(Y) ∩ H^{2p−1}(Y,Z) = Tor (empty for p = 1) — the .tex's ray input set;
  Poincaré class x = e⊗e′ + f⊗f′ on E×E′: integral, purely (1,1), in Theorem 6.3's module,
  not a ray; ray e⊗e′ not purely (1,1) (¼ (2,0)-component).
- **F2:** L = Z ⊕ Z/2, v = (e+f)⊗t: γ(v) = v ≠ 0 — kills Thm 6.2(2)'s M_a^{C_4} = 0 and
  H² = 0 as stated.
- **F3:** demonstrations for 0012/0018/0019/0302/0303/0305/0307 (incl. 0307 passing under a
  broken solver and firing on agreement cases).

## Required repairs before claiming success
- [ ] F1: rewrite §6.3 (correct (p,p) input identification + emptiness of the ray set);
      re-scope §7 item 3, Disposition bullet 1, and the abstract ("lattice level; no new (p,p)
      inputs covered"); state that non-divisor (p,p) inputs of E×Y reduce to Y's input-axis
      content in the deck-trivial sector.
- [ ] F2: add torsion-freeness of L_Y to Theorem 6.2(2) (or restate M_a^{C_4} ⊆ M_a[2]).
- [ ] F3: repair/replace certificate checks 0012, 0018, 0019, 0302, 0303, 0305, 0307; correct
      the "every check CAN fail" docstring and .tex §6.6; re-run the double-run byte-identical
      receipt.
- [ ] F4 (cheap): add an e∧f⊗ℓ deck-fixity check and an exact γv = v invariant solve.
- [ ] F5/F6: declare the matrix convention; make the "lattice level" qualifier uniform.

---

# Closing re-check (v3) — 2026-10-31 (the same auditor, resumed)

Artifacts re-read in full (not from memory): the v3 .tex (899 lines) and the v3 certificate
(610 lines) in /home/z/my-project/hodge-campaign/. The clone still holds the v2 artifacts
(confirmed by diff); it was not modified. Probes: /tmp/audit_29/probe_v3_math.py (12 checks,
12 pass), probe_v3_cert.py, sabotage_v3.py, tectonic compile.

## Verdict: PASS_WITH_REPAIRS_REQUIRED (conditional)
The mathematics of the round is now correct and honestly scoped — every component of the F1
repair was independently re-derived and verified (12/12), F2's hypothesis is in place with a
real counterexample, and 8 of the 10 flagged certificate checks are genuinely repaired and
falsifiable. But two of the repairs the .tex claims on its face are **fake receipts** (checks
0008 and 0408 are vacuous code — proven by static read, dynamic branch analysis, and survival
under every sabotage), plus three minor stale-language items. The round may not print "every
row receipted / nothing asserted beyond its certificate" until R1 is fixed (a 10-line repair).

## Receipt and compile verification
- Certificate v3: **31/31 checks, exit 0, deterministic double-run byte-identical** (0.05 s,
  zero float and zero complex literals by AST scan). The .tex's "31 checks, exit 0,
  deterministic" claim is TRUE.
- Compile: tectonic exit 0, **zero errors**, 36 cosmetic warnings (overfull hboxes; one
  ℤ-in-monospace-font warning), 156.41 KiB PDF; my rebuild's extracted text is **identical**
  to the author's PDF (binary diff = ID/timestamp bytes only).

## Per-finding disposition
- **F1 (blocker) — REPAIRED and VERIFIED at its site.** §6.3 rewritten: Theorem (conjugation):
  integral ℓ_C is conjugation-fixed, hence never purely (p−1,p) — re-derived independently
  (probe Vg/Vh: a−ib = 0 iff a=b=0 over 121 Gaussian pairs; the H^{p−1,p}∩H^{p,p−1}=0
  argument). The ε/η decomposition e = ½(ε+η), f = −i/2(ε−η) with ε = e+if the +i-eigenline
  (H^{1,0}), η = e−if the −i-eigenline (H^{0,1}) — verified exactly (Va/Vb/Vc). The balanced
  theorem x = ½ε⊗(p−iq) + ½η⊗(p+iq), "(p,p) iff p−iq purely (p−1,p)" — verified exactly (Vd),
  including the no-cancellation step (the ε- and η-terms sit in distinct Künneth summands;
  p+iq = conj(p−iq) makes the second condition automatic). The Poincaré exemplar
  x = e⊗e′+f⊗f′ = ½(ε⊗η′+η⊗ε′), integral and purely (1,1) — verified by Gaussian-exact tensor
  computation (Vf/Vf2: (2,0)/(0,2) coefficients exactly 0, (1,1) coefficients exactly ½),
  matching my round-1 counterexample computation. The full-form door law
  m(e⊗p+f⊗q) ∈ im(γ−1) ⟺ m(p+q) ∈ 2L ∧ m(p−q) ∈ 2L — verified exhaustively (Vi: 187,500
  instances; Vj: the certificate's 12 pairs + 5 mixed-parity stress pairs). Theorem 6.3 now
  states the full form; the corollaries and the Poincaré corollary are correct. Assembly item 3,
  the disposition bullet, the abstract, and the closing statement all carry the "at the lattice
  level / no new (p,p) input coverage" qualifiers. The two-letter sector deck-triviality is
  stated, not hidden. Scope inflation REMOVED.
- **F2 (major) — REPAIRED and VERIFIED, with two garbled/false softening sentences (→ R4).**
  Theorem 5.2 now hypothesizes L torsion-free; the boundary remark exhibits the 2-torsion
  counterexample, which I re-verified as a genuine computation (Vl: γ((e+f)⊗t) − (e+f)⊗t = 0
  in Z²⊗(Z⊕Z/2), element nonzero). Residual: the remark's sentence "The product worlds' own
  cohomology is torsion-free in the relevant degrees…" is FALSE (Enriques: H³ ≅ H₁ = Z/2 by
  Poincaré duality, H² = Z^{10}⊕Z/2 — the exhibited invariant is realizable inside the product
  world's own cohomology), and the theorem's parenthetical "as every subgroup of the
  torsion-free H*(Y,Z)'s free part is" is garbled.
- **F3 (major) — 8 of 10 REPAIRED and VERIFIED; 2 claimed repairs are VACUOUS (→ R1).**
  Genuine and falsifiable now: 0005 (full-form law, 144 solves — validated against my
  independent criterion), 0007 (Poincaré exemplar), 0003 (full bounded invariant solve over
  15,625 vectors; nit: equations hardcoded, not derived from pgamma), 0014 (real two-equation
  Diophantine solve — verified to discriminate the swap-deck system), 0019/0020/0021/0022 (real
  Θ_m computations; 0022 catches a sabotaged symmetrizer), 0023 (real 2m×2m matrix products
  with a genuine in-block-twist control; the theorem-side commutation remains structural for
  any block-diagonal G — the control is what gives it value), 0402/0403 (H² quotients computed
  through actual N₄ matrix powers and generator indices — the machinery discriminates decks:
  swap→2, rotation/trivial/degenerate→None), 0405 (BAD² ≠ −I through the product), 0407 (the
  corrected predicate fires at m=1 — verified). NOT repaired: 0008 and 0408 (see R1).
  Sabotage confirmation: swap deck → 10 failures; trivial deck → 11; sign-broken rotation →
  0011/0012; always-False solver → 7 failures; broken symmetrizer → 0022. The genuine core is
  live and broader than v2.
- **F4 (minor) — REPAIRED.** e∧f⊗y1 deck-fixity added (0017); words restricted to E-degree ≤ 2
  with distinct letters (Λ³⟨e,f⟩ = 0 respected, 0016); the invariant solve is now a full
  bounded solve (0003).
- **F5 (minor) — REPAIRED.** Conventions declared in both artifacts (.tex §6 intro: column
  convention, certificate computes row transposes; certificate header declares row convention;
  the plane theorem notes the transpose).
- **F6 (minor) — REPAIRED in the disposition/assembly/closing statement** (uniform "at the
  lattice level"); residual stale language in two places (→ R2, R3).

## Residual findings
### R1 — checks 0008 and 0408 are vacuous; the .tex claims them as receipts — severity: major (F3-class)
- **0008** ("the pure-ray input set is EMPTY: a − i*b = 0 iff a = b = 0 (conjugation)"): the
  only statement that could set the flag False is `a==0 and b==0`, which the loop `continue`s
  past — the failure branch is UNREACHABLE (dynamic proof); the second conjunct is a hardcoded
  list of nonzero pairs; **no Gaussian arithmetic appears anywhere** (there is no `i` in the
  expression). It cannot fail under any mathematical content — proven by survival under all
  five sabotages (swap / sign-broken / trivial deck / broken solver / broken symmetrizer).
  A genuine implementation is four lines (probe Vg). The .tex §6.6 lists "the empty-ray
  conjugation receipt" as on the face — **FALSE**.
- **0408** ("the 2-torsion boundary … computed in Z/2"): every operand is an integer constant
  (`(1+1)%2==0`, `(1−1+0)%2==0`, `(2*1)%2==0`) — no module, no γ, no tensor, no Z/2 element.
  Cannot fail (survives all sabotages). The .tex freeness remark says "the certificate carries
  the hostile control" — **FALSE**.
- Impact: no theorem is false (both items are proven in the .tex and independently verified
  here), but the artifact's own standard — "Nothing in this document is asserted beyond its
  certificate" (abstract) and the certificate's "vacuous classes repaired per AUDIT-29" — is
  violated by these two claimed receipts.
- Repair: implement 0008 as `(a,−b) == (0,0) iff (a,b) == (0,0)` over a box in Z[i]; implement
  0408 as an actual Z⊕Z/2-module computation of γ((e+f)⊗t) − (e+f)⊗t (probe Vl is a template);
  re-run and recompile.
### R2 — stale "27 checks" in §9.3 (line 811) — severity: minor
- The corpus-map verification-state bullet still reads "(27 checks, §6)" while the disposition
  and §6.6 say 31. One-token repair.
### R3 — stale pre-repair ray language in the bundle-side remark (§7, line 647) — severity: minor
- "For a primitive ray e⊗ℓ with ℓ transcendental on Y…" — post-repair, pure rays are empty (the
  conjugation theorem) and the (p,p) one-letter inputs are balanced classes; the boundary
  content is correct but the phrasing should reference x = e⊗p+f⊗q with p−iq
  transcendental-typed.
### R4 — two false/garbled sentences inside the F2 repair — severity: minor
- (a) Theorem 5.2's parenthetical "as every subgroup of the torsion-free H*(Y,Z)'s free part
  is" — garbled (H*(Y,Z) is not torsion-free in general; the intended true fact is "subgroups
  of free abelian groups are free"). (b) The freeness remark's "The product worlds' own
  cohomology is torsion-free in the relevant degrees for smooth projective Y with char 0
  standard lattice structure" — FALSE: Y = Enriques has H³(Y,Z) ≅ H₁(Y,Z) = Z/2 (Poincaré
  duality) and H² = Z^{10}⊕Z/2, so the exhibited invariant is realizable inside the product
  world's own cohomology. Honest replacement: torsion classes have zero complexification and
  carry no Hodge type — the Hodge-input lattice is unaffected; the hypothesis is needed for the
  module-level theorem's stated generality. (Related nit: the conjugation theorem's "nonzero
  integral class" should read "nonzero of infinite order" — a torsion class has ℓ_C = 0,
  trivially 'pure'.)

## Counterexample / computation attempts (closing round)
- Attempted to break the conjugation theorem (torsion edge: a nonzero torsion ℓ has ℓ_C = 0,
  which is vacuously 'pure') — lands only as the R4 nit; the theorem's use (L_Y torsion-free)
  is sound.
- Attempted to break the balanced characterization (cancellation between the ε- and η-terms) —
  fails: the terms live in distinct Künneth summands (direct sum), so no cancellation; the
  "exactly" is correct.
- Attempted to break the full-form door law with mixed-parity (p,q) (including pairs where
  p+q and p−q have differing zero patterns) — impossible: (p+q)−(p−q) = 2p, so the two
  conditions are always congruent mod 2; the law holds (187,500 exhaustive instances). (Note:
  the two conjuncts of the full form are equivalent — a harmless redundancy, not a defect.)
- Attempted to break the Poincaré exemplar — verified exactly (Gaussian tensor arithmetic).
- Sabotage of the v3 certificate: five attacks, all detected by the genuine core; 0008/0408
  survive everything (vacuity proven).
- Two bugs in my own probe (HALF misdefined as 1+2i; Lzero applied to a pair) were found and
  fixed before concluding — the final probe is 12/12.

## Required repairs before printing the receipt claims
- [ ] R1: replace 0008 and 0408 with genuine computations (≤ 10 lines total); re-run
      (double-run byte-identical) and recompile.
- [ ] R2: "27 checks" → "31 checks" (line 811).
- [ ] R3: re-phrase the bundle-side remark in the balanced-class language.
- [ ] R4: fix the two false/garbled sentences in the F2 repair (and the "infinite order" nit).
