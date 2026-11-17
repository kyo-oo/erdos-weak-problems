# GST Weil-Forcing Frame, End-Mass Law, and Input Stratification (Cycle 2, Part I)

**Date:** 2026-10-25
**Kind:** cycle-2 foundation: completed geometric zero-or-full dichotomy frame for the Weil-fourfold
discriminator (explicit rational algebraic correspondence), stratification of the forcing input into three
inequivalent forms (pair / carrier / specified-carrier) with the monoid and torsion gaps identified,
End-mass law for every holomorphic realization of the exact carrier on abelian worlds (corrected sign; End-mass no-go),
exact discriminator periods re-derived independently, and the minimal scale m0 = 1 on the discriminator.
**Repair note (2026-10-25, post-audit):** the committed first version carried two mathematical errors caught by the
independent adversarial audit (grade-duality parity in ch(E^vee) at even p, and a false P1 monoid witness); both are
corrected in this revision and in the derivation .tex (audit findings F1, F2).
**Base checkpoint:** `2ac3b2f` (branch research/gpt6-native-point-primitive-span-20261017).
**Continuation of:** `2026-10-24-gst-forcing-site-pure-realization-congruence-closure-and-gr25-calibration`
(Theorem A, Lemma B1, Theorem B2), `2026-10-24-gst-gr25-lattice-completion-pure-pair-and-universal-two-center-descent-law`
(Theorem C, all p), the Weil records 2026-10-17/18/19/21 (projector, Gram, dichotomy, no-gos), and the
2026-10-25 adversarial-audit cycle-1 record.
**Immutable target (unchanged):** for every smooth projective complex X, every codimension p, every rational
(p,p) Hodge class alpha: construct Z in CH^p(X)_Q with canonical class alpha. Open sector 2 <= p <= floor(d/2), d >= 4.

## 1. What is new and proved

1. **The Weil Chow correspondence (explicit).** P_W(t) = -(t-25)(39t-79)(t^2-30t+625)/44000000 expanded to
   coefficients (a_0..a_4) = (-79/2816, 359/22000, -527/400000, 139/2750000, -39/44000000), so
   Pi_W^CH = sum_j a_j * transpose-graph(f^j) is a rational algebraic codimension-4 correspondence on AxA
   whose cohomology action is the projector with kernel-verified polynomial identities (identity on the Weil
   plane W_Q, zero on the mixed and ambient primary components; CRT idempotence on the full f*-spectrum --
   (a)-(c) kernel-verified in the companion Lean file, (d) in the pre-existing
   GSTUniversalCMArithmeticObstruction.lean given the record-level spectrum census).
2. **Theorem W1 (completed geometric zero-or-full frame).** S := Pi_W^CH cl_A CH^2(A)_Q satisfies:
   (i) S subset W_Q, stable under f*, f*; (ii) S = 0 or S = W_Q (via the module identification with
   Q[t]/(t^2+14t+625) and the kernel-verified cmWeilStableSourceDichotomy); (iii) S = 0 forces W_R, W_I
   nonalgebraic (rational Hodge fails for these classes on A); (iv) S = W_Q iff one algebraic surface has
   nonzero Weil projection, and then every rational Weil class has an EXPLICIT rational algebraic
   representative from the one-source reconstruction (kernel-verified Cramer coefficients); (v) carrier
   connection: S = 0 forbids EVERY holomorphic realization of the exact Weil carrier character r + mW_R at
   EVERY scale m >= 1, every rank r >= 5, and likewise every pure pair; a single holomorphic carrier at any
   scale forces S = W_Q and full Weil algebraicity.
3. **Theorem W2 (input stratification).** The forcing input has three forms: pair form at SOME positive
   integer scale (x in K0_alg with ch(x) = m' alpha pure) iff alpha algebraic; carrier form (a holomorphic
   bundle with the pure character at a pinned scale) implies pair form; specified-carrier form implies
   carrier form. The layers between the forms: the **bundle-monoid layer** M(X) := {pure characters realized
   by single holomorphic bundles} inside {realized by algebraic K-classes} -- an OPEN layer; the projective
   line is proved MONOID-FULL in the derivation (every rank-r class r+q(L-1) is O(q)+O^{r-1}, in particular
   every pure character is carrier-realizable there), and NO world with a nonempty layer is exhibited; and
   the **K-torsion gap** of Theorem A's construction ambiguity (ker(ch) = K0_tors; measured qualitatively).
   A conditional fusion lemma is proved (one-step presentable pairs give carriers via kernel + twist-back).
   On the discriminator the residual layer M(A, W) is named and left open (emptiness not claimed). This
   corrects the cycle-1 audit finding F4 into its true shape: the descent law reads the character only
   (Theorem A torsion ambiguity harmless for cycle-1 constructions); the monoid layer is the substantive
   open boundary. The first version's P1 "non-representability witness" was FALSE ((r+1)[O]-[O(1)] IS
   [O(-1)]+O^{r-1} since [O(-1)] = 2[O]-[O(1)]) and is repaired here (audit finding F1).
4. **Theorem W3 (End-mass law; corrected sign) + End-mass no-go.** ch(E^vee) = r + (-1)^p m alpha (the
   per-grade duality sign; at even p the dual COINCIDES, it does not negate), hence
   ch(End E) = r^2 + (1+(-1)^p) rm alpha + (-1)^p m^2 alpha^2; at p = 2: r^2 + 2rm alpha + m^2 alpha^2
   (three grades). On abelian fourfolds chi(A, End F) = + m^2 * INT(alpha^2) > 0 for EVERY holomorphic
   realization; Serre duality gives the End-mass identity h^0 + h^2/2 = h^1 + (m^2/2) INT(alpha^2)
   >= (m^2/2) INT(alpha^2). On the discriminator (INT W_R^2 = 8): h^0 + h^2/2 >= 4m^2, and for simple
   realizations h^2 >= 8m^2 - 2 (>= 6 at the minimal scale m = 1). Corollary (End-mass no-go): any birth
   law producing carriers whose even-End-cohomology mass h^0 + h^2/2 is bounded independently of m cannot
   realize the forcing input at all scales on abelian fourfolds. NO claim about rigidity/isolatedness (the
   corrected identity permits h^1 = 0 with the mass in h^2). Complementary to the 2026-10-18 polystable
   Chern-Weil zero-degree no-go (pairing alpha.theta^{d-2}; it kills the polystable channel): whatever
   survives must be unstable and carry even-End-cohomology mass >= 4m^2 on the discriminator. The first
   version stated the negative-sign End-signature and a rigidity no-go; both were wrong (grade-duality
   parity error at even p -- audit finding F2) and are corrected here and in the derivation.
5. **Exact periods and minimal scale.** Independent exterior-algebra recomputation: W_R^2 = 8 vol (as a
   class, no other components), W_I^2 = 8 vol, W_R W_I = 0, Omega Omega_bar = 16 vol — reproducing the
   2026-10-19 Wolfram computation by an independent method. Kunneth lemma: ch carries the topological
   K-lattice of every complex torus ONTO the integral even cohomology lattice (ch(eta_S) = +- monomial), so
   on abelian worlds m0 equals the integrality denominator of alpha itself. On the discriminator: W_R
   integral, td(A) = 1, B2 additive scale 1, c_4 = (m^2/2) W_R^2 = 4m^2 [A] integral — the exact Weil
   carrier exists topologically at scale m = 1 with fully integral data: c_1 = 0, c_2 = -mW_R, c_3 = 0,
   c_4 = 4m^2[A], rank r >= 5.

## 2. Method and verification

- Correspondence algebra verified exactly (integer arithmetic; key identity
  (t-25)(39t-79)(t^2-30t+625) + 44000000 = (t^2+14t+625)(39t^2-2770t+72375); P_W congruences and
  P_W(-7+-24i) = 1, P_W(15+-20i) = 0, P_W(25) = 0).
- Periods verified by an exact exterior computation (8-monomial expansion of Re Omega, complementary-pair
  sign count, 64 ordered products) — matches the record's Wolfram Gram exactly.
- All proofs written in the companion derivation with declared external leaves (E1-E10: correspondence
  compatibility, Gysin maps, GAGA, Thom-Porteous through the proved descent law, ch identities,
  (L-1)^2 ring arithmetic, K-theory finiteness/AH, HRR, Serre duality, Kunneth).
- Lean shadow (separate commit): GSTWeilForcingFrameCertificate.lean certifies the pure-algebra cores
  (projector polynomial identities + coefficients; the exterior sign-count certificate INT W_R^2 = 8 and
  the corrected End-mass arithmetic) with sorryAx audit and #print axioms on GitHub Actions.

## 3. Scope and discipline

- The stratification theorem is input normalization (M3-equivalence map), labeled as such: it is NOT
  progress toward the target by itself; its value is identifying which layer each future mechanism addresses.
- W1 does not decide S = 0 vs S = W_Q on any actual nonsplit instance; producing S = 0 on an instance
  remains the campaign's negative certificate (PROMPT sec 2). The unauthenticated external manuscript
  claim p3sw:weil-plane would force the full-plane outcome if ever verified; it remains an external leaf.
- The End-mass law and its no-go corollary are blind to the Hodge/non-Hodge distinction (they apply to any
  holomorphic bundle with the carrier's Chern data); they prune mechanism families, they do not decide the
  dichotomy.
- No family switching, no input outside (X, p, alpha), five-question preflight respected (the new laws take
  the same typed input and produce scheme-level or bundle-level objects with exact Betti equalities).

## 4. Consequences for the registry

- R4: the discriminator's certificate frame is now COMPLETE as a conditional frame (with declared standard
   leaves E1/E2 for the correspondence-action and Gysin steps; the purely algebraic core is kernel-anchored): either outcome is a
  closed statement about its consequences; the zero-test is one well-posed binary geometric question.
- R1: the forcing input's layer structure is fixed: the pair layer = the conjecture itself; the carrier
  layer = the monoid question M(X); the specified layer = + torsion. Any cycle-2 construction mechanism must
  declare which layer it addresses. The End-mass law gives every candidate construction a sharp
   necessary condition to satisfy on abelian test worlds (h^0 + h^2/2 >= 4m^2 on A; h^2 >= 8m^2 - 2 for
   simple realizations).
   Next strike (R1): the (p,p)-harmonic/Deligne-cocycle input must now target the CARRIER layer through a
  mechanism compatible with the End-mass no-go (even-End-cohomology mass >= 4m^2 at scale m; unstable carriers); or R4: an all-surface
  vanishing theorem on one nonsplit instance.

## 5. Provenance

- Derivation: research/derivations/GST_weil_forcing_frame_end_signature_and_input_stratification_2026_10_25.tex.
- Lean shadow: GSTWeilForcingFrameCertificate.lean + .github/workflows/gst-weil-forcing-frame-certificate.yml
  (path-filtered; elan-init.sh hyphen URL; sorryAx audit; #print axioms capstones).
- Pre-commit banned-word gate executed (rule 50 / ledger 076): zero hits.
- Author self-audit plus independent adversarial audit to follow per Mode B Phase 4 (sec 27) before any
  cycle-2 success claim; computational cross-checks are exact-integer and included above.

## 6. Status line

Cycle 2 opened at full power: R4 frame completed (Theorem W1), R1 input stratified (Theorem W2),
End-mass law proved (Theorem W3, corrected sign, End-mass no-go), discriminator constants exact (INT W_R^2 = 8, m0 = 1,
carrier data integral at m = 1). Forcing input remains the open target; no conditional-equivalence claim is
promoted as progress; the next registry movement must be a carrier-layer construction mechanism or an
R4 decision on an actual instance.
