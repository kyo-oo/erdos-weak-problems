# GST Carrier-Mechanism Verdict: RR-Invisibility, Cohomological-Spread No-Go, and the Exact Remainder (Cycle 2, Part II)

**Date:** 2026-10-25
**Kind:** cycle-2 strike 2 (final): the carrier-layer mechanism verdict on the discriminator --- the
Euler-zero law, Riemann--Roch invisibility of the Weil grade (the scale m is arithmetically free), the
cohomological-spread no-go (no exact carrier on any abelian world is WIT_j/IT_j; conditional on Mukai's
semi-homogeneous band theorem, no semi-homogeneous bundle is a carrier), the scale-monoid structure of
the carrier layer (one bit and a least scale), the End-twist table (the Weil--End mass 8m^2 is
twist-constant), and the exact-remainder synthesis (the distance from the audit-hardened strata to the
forcing input is the dichotomy bit plus the monoid bit, with the entry tests any candidate must clear).
**Base checkpoint:** `93f9aaa` (branch research/gpt6-native-point-primitive-span-20261017).
**Continuation of:** `2026-10-25-gst-weil-forcing-frame-end-signature-and-input-stratification` (cycle-2
strike 1: W1 frame, W2 stratification, W3 End-mass law, all audited to PASS through the 9-a/9-b/9-c loop;
CI-green at 40105212209, 40108110670, 40109050940), the cycle-1 forcing-site and lattice-completion
records, and the 2026-10-25 adversarial-audit cycle-1 record.
**Immutable target (unchanged):** for every smooth projective complex X, every codimension p, every
rational (p,p) Hodge class alpha: construct Z in CH^p(X)_Q with canonical class alpha. Open sector
2 <= p <= floor(d/2), d >= 4.

## 1. What is new and proved

1. **The Pic^0-class lemma (E12) and the Euler-zero law.** c_1(P) = 0 in H^2(A,Z) for every
   P in Pic^0(A) (exponential sequence; ker(c_1) = Pic^0; every line bundle is O(k Theta) tensor P on
   the discriminator since NS = Z theta). Consequently every exact carrier F (ch(F) = r + m alpha,
   grades 0 and 2p only, p < d) on every abelian d-fold satisfies chi(A, F) = 0: the forcing input's
   Euler characteristic is PINNED TO ZERO on all abelian worlds. Entry test: any construction outputting
   a carrier candidate with chi != 0 is refuted on the spot.
2. **RR-invisibility of the Weil grade (Theorem V1(ii)).** On the discriminator, for EVERY line bundle L
   with c_1(L) = k theta: chi(A, F tensor L) = r * k^4 = rk(F) * chi(O(k Theta)). The m-grade
   contributes NOTHING to any line-bundle-twist Euler characteristic. Certified constants: INT W_R
   theta^2 = 0 (the 48-pairing index-collision certificate: every ordered W_R-monomial--theta^2-word
   pairing dies by a repeated generator; the 8 monomials carry exactly one of e_j, f_j per index, every
   theta^2 word carries both letters of its two indices; kernel certificate
   weil_WR_theta2_collision) and INT theta^4 = 24 (surjection count: 24 distinct-index words out of
   4^4 = 256, all +1 by 2-form commutativity, 232 colliding words die; kernel certificate
   theta4_surjection_count). Corollary: every additive lattice invariant of the carrier in the Theorem
   B2 clearing family is rank-only; NO additive RR/Schwarzenberger-type congruence constrains the scale
   m; the arithmetic layer of the carrier form on the discriminator is rank-only and the B2 clearing
   requires no scale beyond the K-lattice integrality m0 = 1 (strike 1). Scope: no claim about
   non-additive invariants or Euler pairings with higher-rank sheaves.
3. **The cohomological-spread no-go (Theorem V2).** For every exact carrier with p < d on every abelian
   world: (i) chi(A, F tensor P) = 0 for every P in Pic^0(A); (ii) F is not WIT_j per point for any j
   (single band + Euler-zero forces the band empty, hence acyclic for all P, hence the perfect transform
   R-Phi-hat(F) has all derived fibers zero, hence is zero, hence F = 0 by the Fourier--Mukai
   equivalence -- contradicting rank >= 1); a fortiori not IT_j; (iii) every twist F tensor P is either
   acyclic or has nonzero cohomology in at least two degrees. **Corollary (conditional on E14, Mukai's
   semi-homogeneous band theorem): no semi-homogeneous vector bundle is an exact carrier with p < d.**
   The Fourier-band birth family (IT-type spectral constructions and transform-pure sources, both with
   locally free transforms, semi-homogeneous
   component births) dies on abelian worlds in one stroke.
4. **The scale-monoid structure (Proposition V3).** The set Sigma of realized carrier scales is an
   additive submonoid of Z_{>=1} (direct sums add scales and ranks; F^(⊕k) multiplies scales): the
   carrier layer is ONE emptiness bit plus a least scale m*. Nonempty at one scale iff nonempty at
   every multiple thereof.
5. **The End-twist table (Remark R1).** chi(A, End F tensor L) = r^2 k^4 + 8 m^2 for every L with
   c_1(L) = k theta: the Weil--End mass 8 m^2 is TWIST-CONSTANT (k = 0 reproduces the certified
   End-mass chi = +8 m^2; even in k, consistent with Serre duality; no three-term identity claimed at
   k != 0 since Serre pairs +k with -k).
6. **The exact-remainder synthesis (Theorem V4, M3-labeled).** On the discriminator: input realizable
   IFF [dichotomy bit S = W_Q] AND [monoid bit M(A,W) nonempty]. Every carrier automatically satisfies
   the three walls (Euler-zero; no cohomological band; End-mass >= 4 m^2, simple h^2 >= 8 m^2 - 2); the
   corpus no-gos enter as channel constraints on any construction (the Q[theta]-trapping of line-bundle
   K0 words constrains line-bundle word channels; the twelve killed routes of the 2026-10-25 armament
   dossiers stay dead). The equivalence is input normalization (taxonomy M3), recorded as
   such; the new content is the entry-test package. No exhaustiveness claim beyond the typed corpus.
7. **Transform-side remark (R2).** chi(R-Phi-hat(E)) = rk(E) for every perfect E on the discriminator
   pair (the Poincare class is purely mixed by the Pic^0 lemma on both factors; only the rank grade
   pairs with eta^8/8!; normalization pinned by R-Phi-hat(O_A) = O_{hat0}[-4] at g = 4): the
   Fourier--Mukai Euler sees only the rank --- the same invisibility theme, explaining the spread no-go.

## 2. Statement-integrity note

Strike 1 proved: pair form iff alpha algebraic (at some scale); carrier => pair; the End-mass law. Strike
2 adds ONLY new necessary conditions and structure (V1--V3, R1); it does not promote any conditional
equivalence, does not claim the input, the dichotomy, or the monoid bit, and labels the remainder
synthesis as normalization. The auditor-directed strike-2 constraint is honored: the mechanism analysis
is built against the CORRECTED End-mass law (even-mass >= 4 m^2; h^2 >= 6 for simple carriers at m = 1;
NO deformability assumption anywhere).

## 3. Relation to prior records

- Strike-1 package (same date): V1--V4 sharpen the W2 stratification's carrier layer on the fixed test
  world and add the entry tests; the W3 End-mass law gains the twist-constant form (R1); the W1 frame
  is unchanged.
- Cycle-1 B2 clearing theorem: V1(iii) is its discriminator-local completion (the additive family is
  rank-only; m is free) --- consistent with, and sharper than, the general clearing-by-scale.
- 2026-10-19/20/21 Weil records: the Q[theta]-trapping no-go for line-bundle words and the Hilbert/
  incidence dead channels are the fourth wall in the entry-test list; the spread no-go is NEW and
  independent of those.
- The 2026-10-20 prescribed-residual-spectral record (with the 2026-10-24 spectral/eigenbundle records):
  the spectral-bundle trivial-image failure already killed the specific spectral construction; V2 kills
  the entire IT band (locally free transforms) and the per-point single-band class on abelian worlds,
  unconditionally.
- The 2026-10-25 armament dossiers (7-a/7-b): the twelve dead routes stay dead; the two live typed
  handles (component-birth, 2-cell coherence) are NOT killed by V2 (they are not band constructions) --
  they now face the entry tests explicitly.

## 4. Artifacts and verification

- Derivation: `research/derivations/GST_carrier_mechanism_verdict_spread_no_go_and_rr_invisibility_2026_10_25.tex`
  (full proofs; leaves E1--E11 carried over from strike 1 verbatim, E12--E14 declared; scope box;
  M3 label on the synthesis; explicitly-not-claimed list).
- Lean certificate: `GSTCarrierMechanismVerdictCertificate.lean` (self-contained, import Mathlib):
  Part A the index-collision certificate (48/48 duplicated pairings; sign-irrelevant by vanishing) and
  the theta^4 surjection count (24 + 232 = 256); Part B the single-band kill arithmetic and the
  carrier/End twist-chi arithmetic with the certified constants as hypotheses; three capstones and
  #print axioms. The period INT W_R^2 = 8 is companion-certified (strike-1 file) and used as a hypothesis.
- Workflow: `.github/workflows/gst-carrier-mechanism-verdict-certificate.yml` (path-filtered on the .lean
  + itself; same audited-green pattern: elan-init hyphen URL, toolchain cache, sorryAx audit, artifact
  upload).
- CI receipt: recorded in STATUS.md after the run (target: green, sorryAx-audited, capstones
  [propext, Classical.choice, Quot.sound] or axiom-free).

## 5. Explicitly not claimed

The Hodge conjecture or its negation; any holomorphic structure on any Weil carrier; any decision of
S = 0 vs S = W_Q; emptiness or nonemptiness of M(A,W); any rigidity claim; any exhaustiveness of the
entry tests beyond the typed corpus; anything about non-additive invariants beyond the scoped family.
The forcing input remains equivalent to the target in pair form (M3 in force); no conditional-equivalence
promotion.
