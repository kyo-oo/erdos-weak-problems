# GST Gr(2,5) lattice completion: explicit pure pair at scale 360, and the universal two-center descent law

- **Date:** 2026-10-24 IST; active branch `research/gpt6-native-point-primitive-span-20261017`.
- **Kind:** Direct completion of the forcing-site dossier's declared open sub-task (grade-4/6 lattice correction -> completed pure pair -> Law-4 two-center calibration run -> descent law extracted for arbitrary (X,p,alpha)); includes one statement-integrity correction (scale 10 -> 360 on the calibration world).
- **Base checkpoint:** pre-commit HEAD `666e163e32b413794d41dc572db1734cbcb84f37` ("Forcing site dossier: pure realization ladder ... (LaTeX + record)", 2026-10-24).
- **Correct continuation of:** [2026-10-24 forcing-site dossier record](2026-10-24-gst-forcing-site-pure-realization-congruence-closure-and-gr25-calibration.md); closes that record's "concrete open sub-task" (the grade-4 lattice correction) and executes its "Typed calibration protocol (Law-4 two-center machine)".
- **Actual mathematics written:** [Gr(2,5) lattice completion derivation](../derivations/GST_gr25_pure_pair_lattice_completion_and_universal_two_center_descent_law_2026_10_24.tex) (new LaTeX file, this commit).
- **Target remains:** given any original smooth projective X, codimension p, prescribed rational (p,p) Hodge alpha, independently construct Z_alpha in CH^p(X)_Q with canonical Betti class exactly alpha, without requiring its Chow representation as input.

## 1. The completed pure class and its minimal scale (Theorem 1 of the derivation)

On the calibration world X = Gr(2,5) (d=6, p=2, alpha = (2/5)h^2 - s_2), the K-lattice is the free abelian group on the ten Schur bundles B_(j,i) = Sym^j S^v (x) O(i), j+i <= 3 (2x3 box). The unique pure class xi_1 with ch(xi_1) = alpha (all other grades zero, rank zero) has denominator scale m_0 = 360, and

xi_360 = 351[S^v] + 5[Sym^3 S^v] + 736[S^v(1)] + 36[O(2)] + [O(3)] - 17[O] - 51[Sym^2 S^v] - 1620[O(1)] - 141[Sym^2 S^v(1)] - 9[S^v(2)]

is INTEGRAL with ch(xi_360) = 360*alpha = 144 h^2 - 360 s_2 and ALL grades >= 3 zero (verified grade-by-grade; grades > 6 vanish for dimension reasons). Minimality: any K-class V with ch(V) = m*alpha pure satisfies V = m*xi_1 by uniqueness of ch^{-1} (Atiyah-Hirzebruch), hence V integral iff 360 | m. STATEMENT-INTEGRITY CORRECTION: the dossier's scale-10 expectation is corrected --- 10*xi_1 = xi_360/36 is NOT integral; the exact pure pair on Gr(2,5) first exists at scale 360 (= 36 x the naive Plucker scale). The full Schur-basis ch component table (10 generators x 10 graded components) is displayed in the derivation and is the re-verification/future-Lean certificate.

## 2. The completed pure pair (Corollary 2 of the derivation)

E_+ := 351 S^v + 5 Sym^3 S^v + 736 S^v(1) + 36 O(2) + O(3); E_- := 17 O + 51 Sym^2 S^v + 1620 O(1) + 141 Sym^2 S^v(1) + 9 S^v(2). Exact algebraic bundles, EQUAL ranks 2231 = 2231, equal ch_1 = 2664 h, and ch(E_+) - ch(E_-) = 360*alpha EXACTLY, with identical higher components on both sides: ch_3 = (1245, -2709/2), ch_4 = (3043/4, -459), ch_5 = 1947/8, ch_6 = 1999/48. A c_1-zero normalization (add O(-2664) to both sides) is available (Remark 3). This is the "input pure pair E_+/-" the dossier's Law-4 protocol demanded --- the protocol's input now EXISTS explicitly on the calibration world.

## 3. The universal two-center descent law (the `Universal two-center descent law' theorem of the derivation; all p, arbitrary X)

Two lemmas with full proofs: Lemma N (Newton conductor: ch_j(V) = 0 for j < p, ch_p(V) = m*alpha => c_j(V) = 0 for j < p and c_p(V) = (-1)^(p-1) (p-1)! m alpha, by Newton's identities and induction), Lemma T (twist cancellation: c_j(E_+) = c_j(E_-) for j < p => c_p(E_+ (x) L) - c_p(E_- (x) L) = c_p(E_+) - c_p(E_-) for every line bundle L, by the binomial twist expansion c_p(E (x) L) = sum_t binom(r-t, p-t) c_t(E) ell^(p-t)).

THE LAW: for a pure pair (E_+/- of equal rank r, ch(E_+) - ch(E_-) = m alpha with all off-grade-p components zero), s = r - p + 1 general sections of E_+/- (x) L, determinantal centers D_+/- = D_{s-1} of expected codimension p:
- PAIR FORM (correction-free, for every twist): [D_+] - [D_-] = (-1)^(p-1) (p-1)! m alpha in CH^p(X)_Q (Thom-Porteous at maximal degeneracy gives [D] = c_p(E (x) L); Lemmas N + T give the difference).
- OUTPUT: W = ((-1)^(p-1) / ((p-1)! m)) ([D_+] - [D_-]) in CH^p(X)_Q with cl^can(W) = alpha. In particular alpha is algebraic.
- SINGLE-CENTER FORM (when an exact single pure carrier E exists, c_1(E) = 0, L = O(k)): [D_E] = (-1)^(p-1) m (p-1)! alpha + binom(r,p) k^p [H_1 cap ... cap H_p] --- exactly the dossier's p=2, m=10 bookkeeping (-10 alpha + binom(r,2) k^2 h^2), now proved for all p.

Corollary (typed forcing implication): the single input of B2(iii) --- an integrable structure (dbar_{E_alpha})^2 = 0 on the exact carrier, equivalently a pure pair at some scale m != 0 --- IMPLIES alpha algebraic through the explicit conduit above. Input is bundle-side, output cycle-side; no cycle-class surjectivity, no Hodge-surjectivity field, no preimage selector enters. The forcing problem reduces, with zero residual ambiguity, to constructing the input pair from GST laws on the SAME carrier.

## 4. The calibration run (Section 3 of the derivation)

Run at p=2, m=360, r=2231, any Plucker twist O(k): [D_+] - [D_-] = -360 alpha for every k; W = (-1/360)([D_+] - [D_-]). Schubert-component identity: W = (2/5) sigma_2 - (3/5) sigma_{1,1}. The proven Rees witness Z_alpha = (2/5)[H_1 cap H_2] + b_*E^2 with b_*E^2 = -s_2 = -sigma_{1,1} and [H_1 cap H_2] = h^2 = sigma_2 + sigma_{1,1} expands to (2/5) sigma_2 - (3/5) sigma_{1,1} = W. COMPONENT-BY-COMPONENT AGREEMENT in CH^2_Q: the disagreement branch of the dossier's protocol is CLOSED on the calibration world; the law's bookkeeping (sign, factorial, scale, single-center correction, pair-form cancellation) is CALIBRATED. The extracted law (the `Universal two-center descent law' theorem verbatim with pinned constants) is the universal candidate for arbitrary (X, p, alpha), to be forced by the single input (dbar_{E_alpha})^2 = 0.

## 5. Evidence and provenance

- All finite computations: exact rational arithmetic (Python fractions, bounded 10x10 exact Gauss solve; script preserved at hodge-campaign/experiments/gr25_lattice.py in the campaign workspace, not part of this repository commit). Periods INT h^6 = 5, INT s_2 h^4 = 2, INT s_2^2 h^2 = 1, INT s_2^3 = 1, INT alpha h^4 = 0, INT alpha^2 h^2 = 1/5 re-derived inside the presentation ring Z[h,s_2]/(h^4 - 3h^2 s_2 + s_2^2, h^3 s_2 - 2 h s_2^2, s_2^3 = h^2 s_2^2) with INT h^2 s_2^2 := 1, and independently cross-checked by Pieri (sigma_1^6 = 5 sigma_{3,3}).
- The naive Plucker assembly x of the dossier re-verified: ch_2(x) = 4h^2 - 10 s_2 = 10 alpha, ch_4(x) = (-2/3) h^2 s_2 + (1/2) s_2^2, ch_6(x) = -(1/72) h^2 s_2^2 (all three match the dossier's hand values).
- Standard external inputs at standard strength, named where used: splitting principle, Newton identities, Thom-Porteous at maximal degeneracy, ch of Schur bundles, Schur Z-basis of K^0(Grassmannian) + K_alg = K_top (cellular), Atiyah-Hirzebruch rational K-theory.

## 6. Exact scope statement

No universal constructor claimed; no Hodge-surjectivity / cycle-class / preimage hypothesis enters the law; the Hodge content remains entirely on the analytic input side (B2(iii)), which this record does NOT claim to construct on arbitrary X. The scale correction 10 -> 360 is a calibration-world integrality fact, not a law change (the law itself is scale-correct: given any pure pair at any scale m, the output normalization is 1/m). No Lean file changed by this commit; no GitHub Actions run claimed by this record. The Lean shadow of the certificate (ring, degree functional, periods, carrier identity, purity) is the NEXT commit and is the CI-green target.
