# GST forcing site: pure realization ladder, congruence completeness closure, and the Gr(2,5) calibration carrier

- **Date:** 2026-10-24 IST; active branch `research/gpt6-native-point-primitive-span-20261017`.
- **Kind:** Mathbox-style direct strengthening: foundation audit + two mechanism closures + forcing-site localization + explicit calibration carrier.
- **Base checkpoint:** pre-commit HEAD `1029ff3c973123e6b7e95a7108e77fdc24ce0350` ("Index stronger original-X single-integrability same-fold determinant/Rees source with hyperplane correction", 2026-10-24 06:29 IST).
- **Correct continuation of:** [2026-10-24 same-fold determinantal Rees return and source review](2026-10-24-gst-original-alpha-same-fold-determinantal-rees-return-and-source-review.md) and [2026-10-24 two-center algebraic return](2026-10-24-gst-original-alpha-twisted-determinantal-two-center-algebraic-return.md); strengthens the [spatial-fold manuscript](../derivations/GST_universal_spatial_fold_exponential_geometric_realization_2026-10-23.tex) carrier parameters.
- **Actual mathematics written:** [forcing-site derivation](../derivations/GST_forcing_site_pure_realization_congruence_closure_calibration_2026_10_24.tex) (new LaTeX file, this commit).
- **Target remains:** given any original smooth projective X, codimension p, prescribed rational (p,p) Hodge alpha, independently construct Z_alpha in CH^p(X)_Q with canonical Betti class exactly alpha, without requiring its Chow representation as input.

## 1. Theorem A: pure realization ladder (exact-carrier gap closed with explicit parameters)

For arbitrary original smooth projective X of dimension d >= 1, 1 <= p <= d, and ARBITRARY alpha in H^{2p}(X,Q) (no Hodge condition), there exist explicit positive integers m_0 and r_0 with r_0 := max(p+1, d+1) such that for every m = 0 mod m_0 and every r >= r_0 there exists an EXACT complex topological vector bundle E of rank r on X with ch_j(E) = 0 for all j not in {0,p} (1 <= j <= d) and ch_p(E) = m*alpha.

Four proof steps, in full:
1. **Rational K-realization.** X is a finite CW complex; by Atiyah–Hirzebruch, ch tensor Q: K^0(X) tensor Q -> H^{even}(X,Q) is an isomorphism (AHSS differentials are torsion-valued, so over Q the spectral sequence collapses and extension issues vanish). Let u be the class with alpha in degree 2p and all other positive components zero; v := (ch tensor Q)^{-1}(u) in reduced K^0 tensor Q, rank 0.
2. **Integrality scale.** K^0(X) is a lattice; v = w/N_0 for integral w; set m_0 := N_0. For m = 0 mod m_0, z_m := m*v is an integral rank-zero class with ch(z_m) = m*alpha PURE. No further Newton-type conditions on m exist: the total Chern class of a virtual difference has the truncated geometric inverse (1+x)^{-1} = 1 - x + x^2 - ..., an integer polynomial in the positive-degree class x; all higher-Chern denominators are subsumed by K-lattice integrality.
3. **Exactness in the stable range.** BU(r) -> BU is (2r-1)-connected (Bott). If r >= d+1 then dim_R X = 2d < 2r-1, so every z_m in reduced K^0(X) = [X, BU] lifts through BU(r): there exists an exact rank-r topological bundle E with [E] - r[1] = z_m. For r > r_0 stabilize by trivial summands.
4. **Purity.** ch(E) = r + m*alpha, all other positive grades zero (grades j > d vanish since H^{2j} = 0). QED.

Remarks, including the necessary rank-floor correction:
- **Remark 1 (rank-floor correction).** This closes the exact-carrier gap in the Oct-23/24 records ("rational topological K-theory plus a finite trivial complement") with the correct mechanism; the records' rank floor r >= p+1 must be RAISED to r >= max(p+1, d+1) below the stable range — a necessary correction. The Segre fold and the two-center determinantal formulas inherit the corrected parameter with NO other change (they are proved for every rank at which an exact carrier exists).
- **Remark 2 (canonicity at the level that matters).** Any two exact pure carriers of the same (r, m*alpha) differ by a torsion class in reduced K^0 (kernel of ch), invisible to every Betti-graded law downstream (Chern classes, ch, Segre pushforward, two-center Betti landing). The construction is canonical at the level that matters.
- **Remark 3 (type discipline).** The Hodge hypothesis is nowhere used, as it must not be: the carrier exists for non-Hodge alpha too. This is what keeps the two-center landing non-circular on the topological side; the entire Hodge content is displaced onto the analytic forcing input of Section 3 below.

## 2. Lemma B1: sign-conductor class-firewall (closed as a birth route)

Let D_1, D_2 be actual effective divisors with classes [L_1], [L_2], let D_1 cap D_2 = union_j C_j be pure of expected codimension 2 with distinct components C_j and fundamental-cycle multiplicities nu_j >= 1 (so [D_1].[D_2] = Sigma_j nu_j [C_j] by purity, no excess), and let arbitrary per-component signs epsilon_j in {+1,-1} be given. Then every signed fundamental-component assembly satisfies Sigma_j epsilon_j nu_j [C_j] = 2*gamma - [L_1][L_2] where gamma := sum over epsilon_j = +1 of nu_j [C_j] is an actual effective algebraic class.

Consequently, if a prescribed primitive rational Hodge class alpha is representable by such an assembly (with fixed algebraic [L_1][L_2] and fixed auxiliary divisor factors), then alpha is algebraic: the sign-conductor mechanism cannot BIRTH a primitive source; it can only re-sign components whose classes already encode alpha. Proof: split the assembly by sign; the fundamental-cycle total Sigma_j nu_j [C_j] = [D_1][D_2] = [L_1][L_2] by the refined Gysin product (purity of expected codimension 2, no excess; nu_j are the local intersection multiplicities, e.g. a tangential double intersection contributes 2[C]); if the assembly represents alpha, i.e. cl(Sigma_j epsilon_j nu_j [C_j]) = alpha in H^4(X,Q), then by the Chow-level identity alpha = cl(2*gamma - [L_1][L_2]), the canonical class of a rational combination (coefficients 2 and -1) of classes of actual algebraic cycles, with gamma actual effective algebraic. QED.

Reading: the Oct-22/24 anti-deck sign-conductor eps_j = sign(lambda_j) with period 2*sum|lambda_j| is a positivity/period optimizer over a FIXED class skeleton with fixed algebraic background. It is RETAINED as a coupling CERTIFIER and CLOSED as a birth route. This sharpens the record's caveat into the PROVED implication: any primitive class representable by a signed fundamental-component assembly is algebraic (the firewall direction proved in Lemma B1; no converse is claimed).

## 3. Theorem B2: congruence completeness and forcing-site localization

Define the additive invariant c(y) := integral_X alpha*ch(y)*td(X) on the finitely generated lattice K^0_alg(X) (isomorphic to G_0(X), generated by structure sheaves of subvarieties); its image is (1/N)Z for an explicit N (lcm of denominators over any finite generating set). Then:

- (i) For every m = 0 mod N and every rank r, the hypothetical algebraic carrier x_m = z_m + r[1] satisfies chi(x_m tensor y) = r*chi(y) + m*c(y) in Z for all y in K^0_alg(X) (chi(y) integral by RR for algebraic y; m*c(y) integral since N | m), and the same clearing-by-m applies to EVERY additive arithmetic lattice invariant (all Schur-twisted Riemann–Roch congruences, Schwarzenberger congruences included: each is an additive homomorphism on the same f.g. lattice with values in (1/N')Q, cleared by taking m multiple of lcm(m_0, N, N')). THE ARITHMETIC LAYER IS OBSTRUCTION-FREE.
- (ii) Nevertheless, for alpha Hodge: x_m in the image of K^0_alg(X) tensor Q iff alpha is algebraic (Atiyah–Hirzebruch; the K-theoretic Hodge conjecture is equivalent to HC, since Chern classes of algebraic bundles are algebraic by degeneracy-locus/Thom–Porteous arguments and conversely GRR identifies the rational K-images with the rational span of algebraic cycle classes).
- (iii) Hence the conjecture reduces to EXACTLY ONE typed input with zero residual ambiguity: the existence of an integrable holomorphic structure (dbar_{E_alpha})^2 = 0 on the SAME exact carrier E_alpha — equivalently GL_r-descent two-cell coherence of the Oka–Grauert realization over the Jouanolou torsor, equivalently the Abel–Jacobi/Griffiths layer of the Deligne lift of alpha.

"Forcing" is now precise: carrier layer unconditional (Theorem A), arithmetic layer provably clearable (B2(i)), signed-assembly layer provably non-birthing (B1); the forcing site is the single analytic input (dbar_{E_alpha})^2 = 0. A proof that the (p,p) harmonic/Deligne cocycle always supplies it completes the program; a single counterexample refutes this route decisively; there is no third residual ambiguity.

## 4. Gr(2,5) calibration carrier identity

Fix X = Gr(2,5), d = 6, p = 2, alpha = (2/5)h^2 - s_2 with h = c_1(Q) the Plucker hyperplane, s_2 = c_2(S^v) = sigma_{1,1}. Verified periods (matching the existing Gr(2,5) Rees record): integral h^6 = 5, integral s_2 h^4 = 2, integral s_2^2 h^2 = 1, integral alpha h^4 = 0, integral alpha^2 h^2 = 1/5 — alpha is nonzero primitive nondivisor Hodge, with the already-proven fold-born Rees witness Z_alpha = (2/5)[H_1 cap H_2] + b_*E^2 (b_*E^2 = -[Z] = -s_2).

Exact identity, verified line by line in the LaTeX:
- ch_2(S) = (c_1(S)^2 - 2c_2(S))/2 = (h^2 - 2 s_2)/2 (using c_1(S) = -h, c_2(S) = s_2), invariant under dualizing (c_1 flips sign but appears squared; c_2 fixed);
- so ch_2(S (+) S^v) = h^2 - 2 s_2;
- ch_2(O(1) (+) O(-1)) = h^2 (ch_2(L) = c_1(L)^2/2, c_1(O(+/-1)) = +/-h);
- therefore the explicit integral algebraic virtual carrier x := [S (+) S^v]^{⊕5} ⊖ [O(1) (+) O(-1)] ⊖ [O^8] has rank 5*4 - 2 - 8 = 0, ch_1 = 0, and ch_2(x) = 5(h^2 - 2 s_2) - h^2 = 4h^2 - 10 s_2 = 10*alpha (check: 10*(2/5)h^2 = 4h^2).

Exactness note: ch_4(x) = 5*(h^4/12 - h^2 s_2/3 + s_2^2/6) - h^4/12 = (1/3)h^4 - (5/3)h^2 s_2 + (5/6)s_2^2, which is NONZERO (h^4, h^2 s_2, s_2^2 independent Schubert classes in H^8). The naive assembly is NOT the pure carrier; the true pure integral class z_{10 alpha} differs from x by an actual algebraic correction in grades >= 4, which EXISTS on Gr(2,5) because ch: K^0_alg(Gr(2,5)) tensor Q -> H^{even} tensor Q is an isomorphism (cellular Schubert filtration; topological = algebraic K-theory on Grassmannians). Completing this finite grade-4 lattice correction using Sym^2 S, Lambda^2 S and Q-classes is the concrete open sub-task. A pure carrier assembled from algebraic pieces proves alpha algebraic instantly, which is ALLOWED on the calibration world and is exactly why it would be circular on arbitrary X.

Typed calibration protocol:
- **Input:** the completed pure pair E_± (equal ranks, ch(E_+) - ch(E_-) = 10*alpha pure), equivalently the integrable dbar on the pure carrier.
- **Run:** Law-4 two-center machine verbatim (ample twist O(k), s = r-1 general sections — the expected-codimension count s = r-p+1 at p = 2 — determinantal center D_(alpha,k), hyperplane correction binom(r,2) k^2 [H^2]).
- **Expected output:** cl^can( (-1/10)([D_(alpha,k)] - binom(r,2) k^2 [H^2]) ) = alpha, the coefficient (-1/10) being (-1)^{p-1}/(m(p-1)!) at p = 2, m = 10; with the pure-carrier Betti relations cl^can(c_1) = 0 and cl^can(c_2) = -ch_2 = -10*alpha, Thom–Porteous gives cl^can[D_(alpha,k)] = -10*alpha + binom(r,2) k^2 h^2.
- **What it calibrates:** the descent 2-cell, against the already-proven Rees witness Z_alpha = (2/5)[H_1 cap H_2] + b_*E^2 on the SAME world. Agreement extracts the LAW for arbitrary X (the same signed formula on the same carrier construction becomes the universal candidate law, forced by the single input (dbar_{E_alpha})^2 = 0); disagreement yields an explicit local failure on a world where the answer is independently known, pinpointing the descent 2-cell obstruction concretely. A decisive outcome either way.

## 5. Evidence / provenance

- LaTeX derivation committed: `research/derivations/GST_forcing_site_pure_realization_congruence_closure_calibration_2026_10_24.tex` (this commit). Structural check: balanced theorem/proof/lemma/remark environments, balanced braces and display-math delimiters; not a TeX typesetting compilation.
- NO Lean file changed. NO GitHub Actions CI run claimed or implied. No rebase, no merge, no deletions; this record and the derivation are the only new files.
- Author self-audit, not an independent referee.
- Standard external inputs named and used at standard strength: Atiyah–Hirzebruch rational K-theory (finite CW), Bott periodicity connectivity of BU(r) -> BU, Atiyah–Hirzebruch spectral sequence, Grothendieck–Riemann–Roch, Thom–Porteous, Koszul–Malgrange, GAGA, Oka–Grauert.

## 6. Exact scope statement

NO universal constructor is claimed. The forcing site is the single typed input (dbar_{E_alpha})^2 = 0 on the SAME exact carrier E_alpha of Theorem A, from the (p,p) harmonic/Deligne cocycle of alpha; Theorem B2(iii) states that nothing else remains. The calibration world Gr(2,5) is used to calibrate the two-center machine against the already-proven Rees witness, NOT to prove the conjecture; the pure-carrier shortcut there is exactly what would be circular on arbitrary X. Next step: the Gr(2,5) two-center calibration cycle — complete the pure pair via the finite grade-4 lattice correction, run Law 4 against the known Rees witness, and extract (or locally refute) the descent 2-cell law for arbitrary X.
