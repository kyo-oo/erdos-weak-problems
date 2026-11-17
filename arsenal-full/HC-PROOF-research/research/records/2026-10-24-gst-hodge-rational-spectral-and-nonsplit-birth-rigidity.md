# GST Hodge: exact rational spectral source and non-split birth rigidity

- **Date:** 2026-10-24 IST
- **Kind:** Sustained Mathbox research attempt; mathematical theorem construction and self-audit
- **Program/claim IDs:** Existing prose research program; no initialized .mathbox ledger inspected
- **Base checkpoint:** `41ea5d5eea6ad42f879a5388ca752f9ccc66f6d5`; latest branch with October 22–23 full spatial Hodge bifurcation, true nonlinear anti-deck/reentrant Rees folds and all-target holomorphic spectral curvature results
- **Immutable target:** For every original smooth projective complex X, p and prescribed rational (p,p) alpha, independently construct actual Z_alpha in CH^p(X)_Q with canonical Betti class alpha
- **Instructions respected:** AGENTS.md root-cause directions, locked execution plan, Mathbox research-program/research-attempt/proof-audit/computation-audit skills; no external public web, no local Lean installation

## Exact new mathematical results

1. **The complex spectral projector is not Q-linear on all rational cohomology, even for genuine projective X.** On actual elliptic X=E_tau x E_tau, with tau=i 2^(1/4), write integral cohomology 1-forms a_i=dx_i, b_i=dy_i. A rational degree-two class A a1b1+B a2b2+C a1a2+D a1b2+E b1a2+F b1b2 is Hodge (1,1) precisely when F=sqrt(2) C and E=-D. Rationality forces C=F=0, and the full rational Hodge fibre is spanned over Q by F1=a1b1, F2=a2b2, M=a1b2-b1a2. The algebraic diagonal has canonical class F1+F2-M. For every prescribed alpha=A F1+B F2+D M, the ACTUAL original-X Chow class Z_alpha=(A+D)[{0}xE]+(B+D)[Ex{0}]-D[Delta] has EXACT canonical Betti alpha. Yet the COMPLEX spectral projection of the integral a1a2 equals (a1a2+sqrt(2) b1b2)/2, not rational. This is a concrete projective, actual-cycle distinction between Hodge kernel and rational Chow source, not an HC counterexample or all-X proof.

2. **ALL-X, ALL-p polynomial GST spectral-fold homotopy rigidity.** For any smooth affine Jouanolou fold J over any smooth projective original X, every regular algebraic polynomial involution A(t) in Mat_N(Gamma(J,O)[t]), A(t)^2=I, yields a finite projective bundle E(t)=im((I+A(t))/2). Quillen K0 homotopy invariance on smooth affine J implies [E(t0)]=[E(t1)] in genuine algebraic K0(J), hence ALL rational CH Chern character components and original-X Chow returns are equal. The direct differential P'=[[P',P],P] verifies infinitesimal conjugacy. A regular polynomial spectral deformation, even with alpha-dependent coefficients, cannot birth a new canonical rational Hodge direction between two distinct target classes.

3. **Broader connected-parameter BETTI rigidity.** For any connected algebraic parameter variety T and any ACTUAL vector bundle E on JxT (global regular matrix family a special case), restriction to fibers has constant canonical rational Betti Chern character because fiber inclusions are homotopic on the connected analytic T. CH/K0 may vary over a non-affine parameter: Poincare line bundles on E x E^dual give nonconstant Pic0 classes with identically zero Betti c1. A changing actual Chow class is not necessarily a changed rational Hodge direction.

4. **Genuine singular born support with exact derived cancellation.** For any algebraic Z subset J, take F=O_(Zx{0}) on JxA1. The special naive fiber has O_Z while generic fibers vanish; the derived special fiber has Tor0=O_Z and Tor1=O_Z, and its alternating K/G class is ZERO. A singular GST birth can create honest support geometry while its derived K class carries zero newly transported canonical source. Any claimed source must compute localized excess/Tor and a genuine nonzero canonical target coupling, rather than treating singularity itself as the target.

## Mathematical proof artifacts

- [October 22 exact spectrum and rational native elliptic test](../derivations/GST_hodge_spectral_rational_cycle_reduction_2026-10-22.tex), source commit `ea88f88b658942b9bd5119b07f46921dca351bd1`.
- [October 23 full dimensional-fold spectral/Deligne paper strengthened with polynomial homotopy, Tor and connected-parameter theorems](../derivations/GST_alpha_deligne_integral_fold_kgersten_source_birth_2026_10_23.tex), commits `c313c7651cbc00f4a5a90c833791f6a69a516b3d`, `bb7b3ead9b491748dc1a3e9773963f5a2446a809`, and proof-audit correction `f312ac64c6e0acd81c787fc7f2754b3e81a2837e`.

## Exact symbolic checks and provenance

Independent stateless Wolfram computation evaluated the elliptic Hodge wedge coefficient `sqrt(2)*C - F + i 2^(1/4)*(D+E)`, confirmed the irrational spectral coefficient `sqrt(2)/2` (not in rationals). A separate exact finite-matrix computation on P(t)={{1,t},{0,0}} returned `{P²=P:True, A²=I:True, P'=[[P',P],P]:True, Tr(P)=1, Det(P)=0, ranks at 0 and 17 both 1}`. The unrestricted proofs are the algebraic-geometry derivations, not finite numerical extrapolation.

Both LaTeX files were fetched again from live branch; all theorem/proposition/proof/document environment counts pair correctly. No pdflatex build is claimed. No Lean source changed or new GitHub Actions compiler run claimed; prior October 22–23 green workflows remain SHA-specific and do not certify these papers.

## Attempt verdict and route disposition

- **Proved as written subject to standard exact named theorems:** actual elliptic rational Hodge/Chow cycle formula, K0 A1 homotopy rigidity, connected algebraic family Betti rigidity, special-fiber Tor cancellation.
- **Refuted inference (not HC):** complex Hodge-charge projection of arbitrary rational cohomology can automatically be interpreted as a rational Chow source; continuous algebraic idempotent families can generate distinct rational Betti classes without changing components.
- **Mechanism status:** polynomial/smooth-connected-family-only source birth is obstructed in its stated scope; true nonlinear singular/non-split, different-moduli-component algebraic source mechanisms are NOT ruled out.
- **Full original-X all-Hodge target:** this attempt does not construct a regular algebraic spectral/Gersten source with canonical class equal to a completely arbitrary higher-primitive alpha; no full classical proof or Lean target closure is claimed.
- **Provenance:** Mathbox-guided author self-review with exact Wolfram finite checks; no independent mathematical referee.
- **Direct successful outcome:** new all-X GST spectral source BIRTH CONSTRAINT specifying a rigorous mathematical mechanism by which true new algebraic K0 and Betti directions must differ from pure folds/deformations. It protects the simultaneous geometric-algebraic proof program from a false rational-projection/holomorphic-curvature inference.
