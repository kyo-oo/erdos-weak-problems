# Mathbox — target-sensitive genuine K₀ perfect-complex source with exact original-X Chow pairing

- **Date:** 2026-10-19, local research checkpoint.
- **Program:** construct an actual codimension-\(p\) rational Chow representative for every prescribed primitive rational Hodge class on every original smooth projective complex \(X\). This route constructs a target-dependent algebraic **source**, not a selected unknown Hodge preimage.
- **Base:** \`70a8c0169a0dc694caed8d99499fdfc3ca998147\`, active branch \`research/gpt6-native-point-primitive-span-20261017\`.
- **Code edited:** \`GSTUniversalResolvedSupportHodge.lean\` (new actual \(K_0\)-source compiler and integer-denominator certificate), \`GSTActualXHodgeResidualProjection.lean\` (actual native rational Chow output and pairing), \`GSTK3PrimitiveGram.lean\` (geometric tangent/diagonal comparison and target-period reconstruction). No traditional reduction substituted for GST world/cycle architecture; its finite-flat algebraic K₀ projector, Chow/Betti source geometry and polarized GST residual readouts are the actual inputs.
- **Evidence:** K₀ target coupling [Lean #39155696135](https://github.com/kyo-oo/HC-PROOF/actions/runs/39155696135) PASS; original-X target coupling [pinned Lean #39156658770](https://github.com/kyo-oo/HC-PROOF/actions/runs/39156658770) PASS; independently geometric K3 cross-check [Lean #39156728692](https://github.com/kyo-oo/HC-PROOF/actions/runs/39156728692) PASS. Integer-denominator and latest full run verdict to be read separately from the newer commit. These Lean theorems do not assert the missing canonical singular-Betti comparison for the abstract supplied \`H.cycleClass\` structures.

## 1. All-X target-sensitive source compiler with no target-Chow preimage

For a finite flat projection \(f:X\to\mathbf P^n\), let
\[
 u=[f_*\mathcal O_X]\in K_0(\mathbf P^n)_{\mathbf Q},\qquad
 P_K(E)=E-f^*(u^{-1}f_*E).
\]
Since \(u\) is positive rank plus a nilpotent rank-zero term, the inverse is a FINITE polynomial in actual algebraic \(K\)-classes. The existing GST theory verifies the exact \(K\)-pushforward-zero and idempotence laws.

Let \(E_1,\ldots,E_N\) be **independently constructed algebraic perfect-complex \(K\)-classes on original \(X\)**. The target Hodge class \(\alpha\) is NOT among these objects. Define genuine rational Chow source classes
\[
 V_i=\left[\operatorname{ch}(P_K E_i)\operatorname{Td}(T_X-f^*T_{\mathbf P^n})\right]_p
\in CH^p(X)_{\mathbf Q},\quad z_i=\operatorname{cl}_X(V_i).
\]
Genuine scheme Grothendieck–Riemann–Roch gives \(f_*V_i=0\); the classes are algebraic, and the \(z_i\) are rational (p,p) Hodge classes for the official Betti cycle class. Let \(Q\) be an authentic rational intersection pairing on the selected primitive Hodge sector.

For **every prescribed rational** \(\alpha\), no representability assumption, compute its RATIONAL source periods
\[
w_i(\alpha)=Q(\alpha,z_i)\in\mathbb Q
\]
and build the actual algebraic rational virtual source
\[
\boxed{\mathcal E_\alpha=\sum_{i=1}^N w_i(\alpha)\,P_K(E_i)\in K_0(X)_{\mathbf Q}.}
\]
Its original-X rational algebraic Chow output is
\[
\boxed{Z_\alpha=
\left[\operatorname{ch}(\mathcal E_\alpha)
 \operatorname{Td}(T_X-f^*T_{\mathbf P^n})\right]_p
=\sum_iw_i(\alpha)\,V_i.}
\]
The source is **computed from actual algebraic perfect complexes** with scalar coefficients evaluated on the target, not from a map \(\alpha\mapsto\) a preexisting Chow representative.

The exact universal pairing identity follows from rational \(\mathbf Q\)-bilinearity:
\[
\boxed{Q(\alpha,\operatorname{cl}_X Z_\alpha)
  =\sum_{i=1}^NQ(\alpha,z_i)^2\ \ge0.}
\]
If any independently constructed perfect complex has nonzero target pairing, the constructed \(Z_\alpha\) automatically has a STRICTLY POSITIVE target pairing. This works even before assuming positive definiteness of the intersection form, since each period is rational and squared. In every original codimension, \(f_*Z_\alpha=0\) automatically.

**Evidence typing:** \`GSTUniversalResolvedSupportHodge.GSTNativeFiniteFlatK0Extraction.targetCoupledVirtualSource_pairing_eq_sum_squares\` and \`..._positive_of_detected\` prove the full finite-arity \(\mathbb Q\)-linear construction. \`GSTActualXHodgeResidualProjection.ActualXCycleProjectionData.targetCoupledK0ChowCycle\` and \`..._positive\` give the actual original-\(X\) Mathlib \`codimensionCycles X.X p\` output using a supplied genuine GRR linear map and \`H.cycleClass\`. Their official geometric realization requires supplying the true \(K_0(X)\), Chow GRR, and canonical Betti comparison, which are not all instantiated inside these abstracts.

## 2. Rational \(K_0\) is not literally a perfect complex; construct a real one

The formula \(\mathcal E_\alpha\in K_0(X)_{\mathbb Q}\) is a **virtual rational class**, not automatically one object of \(\mathrm{Perf}(X)\). Because the source family is FINITE and every \(w_i\) and every coefficient of the finite-polynomial \(u^{-1}\) lies in \(\mathbf Q\), choose a positive common denominator \(D\). Then
\[
D\mathcal E_\alpha=\sum_j m_j[F_j]\in K_0(X),
\qquad m_j\in\mathbf Z,
\]
where each \(F_j\) is an actual independently existing algebraic perfect complex (terms from \(E_i\), their finite-flat pullback/pushforward and the polynomial inverse). The integer virtual class is represented by an **ACTUAL perfect complex**
\[
\boxed{
\mathscr C_\alpha=
 \bigoplus_{m_j>0} F_j^{\oplus m_j}
 \ \oplus\
 \bigoplus_{m_j<0} F_j[1]^{\oplus(-m_j)}.
}
\]
Odd shifts negate the \(K_0\) class. Thus \([\mathscr C_\alpha]=D\mathcal E_\alpha\) and the rational Chow output is genuinely
\[
Z_\alpha=\frac1D[
 \operatorname{ch}(\mathscr C_\alpha)
 \operatorname{Td}(T_X-f^*T_{\mathbf P^n})]_p.
\]
The Lean theorem \`targetCoupledVirtualSource_integer_denominator_certificate\` checks the scalar equality once the finite common-denominator integers are supplied; choosing their common denominator and the literal derived perfect-complex object are authenticated by finite rational arithmetic and the standard perfect-complex direct-sum/shift construction. **Do not claim Lean has formalized this entire geometric derived-category step**.

## 3. Independent GST geometric validation on the original K3 self-product

Let \(S\) be any complex projective K3 with polarization \(h^2=d\in\mathbb Z_{>0}\) and \(X=S\times S\). Actual original-X algebraic sources:

- \(F_{\mathrm{tan}}=4[\mathcal O_X]-[T_X]\), a rank-zero perfect virtual class. Its first nonzero normalized Chow component is
  \[
  Z_{\mathrm{tan}}=16(A+B)-\frac{16}{d}U,
  \quad A=[pt]\times S,\quad B=S\times[pt],\quad U=h\times h.
  \]
- \(F_\Delta=[\mathcal O_{\Delta_S}]\), an actual coherent/perfect class. Its first nonzero normalized Chow component is
  \[
  Z_\Delta=\Delta_S-\frac2{3d}(H^2)
  =\Delta_S-\frac23(A+B)-\frac4{3d}U.
  \]

The **GST rational Gram-orthogonalized diagonal perfect source** is
\[
\boxed{Z_\perp=Z_\Delta-\frac1{48}Z_{\mathrm{tan}}
=\Delta_S-A-B-\frac1d U.}
\]
This exactly equals the preexisting, independently constructed \`GSTK3PrimitiveGram.primitiveDiagonal\`, not a mysterious new Hodge basis vector. Likewise \(Z_{\mathrm{tan}}\) is \(-16/d\) times GST's preexisting primitive divisor \(U-d(A+B)\). Existing geometric intersection entries are \(\Delta^2=24,\Delta A=\Delta B=1,\Delta U=d,\ AB=1,\ U^2=d^2\).

The resulting ACTUAL rational geometric primitive Gram is
\[
\boxed{
Q(Z_{\mathrm{tan}},Z_{\mathrm{tan}})=768,\quad
Q(Z_\perp,Z_\perp)=21,\quad
Q(Z_{\mathrm{tan}},Z_\perp)=0,\quad
\det G=16128>0.
}
\]
New Lean in \`GSTK3PrimitiveGram.lean\` verifies the **exact K₀→existing GST native basis identity**, the squared energies and determinant, [CI #39156410396](https://github.com/kyo-oo/HC-PROOF/actions/runs/39156410396) PASS.

For arbitrary specified rational primitive target alpha on X, compute genuine periods
\(a=Q(\alpha,Z_{\mathrm{tan}})\), \(b=Q(\alpha,Z_\perp)\). The target-selected actual algebraic virtual source
\[
\boxed{
\mathcal E_{\alpha}^{(2)}
=\frac{a}{768}F_{\mathrm{tan}}
 +\frac{b}{21}
  \left(F_\Delta-\frac1{48}F_{\mathrm{tan}}\right)
}
\]
should be interpreted at first-nonzero Todd-corrected primitive degree as written (the subtraction of the *K-theory sources* and their normalized leading Chow classes is exact in degree 2). Its resulting rational CHOW class is
\[
Z_\alpha^{(2)}
=\frac{a}{768}Z_{\mathrm{tan}}
 +\frac{b}{21}Z_\perp.
\]
The exact source periods are
\[
Q(Z_\alpha^{(2)},Z_{\mathrm{tan}})=a,\qquad
Q(Z_\alpha^{(2)},Z_\perp)=b,\qquad
Q(\alpha,Z_\alpha^{(2)})=\frac{a^2}{768}+\frac{b^2}{21}.
\]
Thus one actual perfect-complex program realizes every target's **exact algebraic projection** onto the two-dimensional geometric primitive sector, and if alpha is in that sector, realizes alpha itself.

Wolfram exact rational symbolic check, with the genuine 4×4 K3 intersection matrix, returned \`{768,21,0,a,b,0}\` for the two squared source norms, cross-pairing, target-selected two period readouts, and difference between the pairing and its rational quadratic expression. No numerical tolerance.

The further Lean \`k0TargetSelectedPrimitive_tangent_readout\`, \`..._diagonal_readout\`, \`..._pairing_eq_weighted_squares\`, and \`..._idempotent_on_generated_sector\` were edited in the SAME K3 Gram module, with their final CI verdict to be recorded separately from the earlier successful source identity checkpoint.

## 3b. GST finite source-frame completeness test and integral perfect-complex numerator

**Exact frame-kernel law.** For genuine perfect-complex sources E_i on the ORIGINAL X, write z_i for the true rational Hodge class of the Todd-corrected primitive Chern source, and form the GST target-sensitive class
\[
\mathcal E_\alpha=\sum_i Q(\alpha,z_i)\mathcal P_f^K(E_i),
\quad
F(\alpha)=\operatorname{cl}_X([\operatorname{ch}(\mathcal E_\alpha)\operatorname{Td}(T_f)]_p).
\]
The independently proved rational sum-of-squares pairing now gives the equivalence
\[
\boxed{F(\alpha)=0\iff\forall i,\ Q(\alpha,z_i)=0.}
\]
Proof: pairing F with alpha yields a sum of rational squares; each square is nonnegative, so if it vanishes all coefficients vanish; conversely zero coefficients give the zero source. This tests exactly which primitive directions a finite GST geometric source family detects, without presuming that the family detects ALL rational Hodge classes. The all-rank Lean versions and their genuine original-X native-cycle specialization were added directly to GSTUniversalResolvedSupportHodge.lean and GSTActualXHodgeResidualProjection.lean; pinned integration [#39161495843](https://github.com/kyo-oo/HC-PROOF/actions/runs/39161495843) passed for this checkpoint.

**Dimension-uniform integral normalization of K₀ projection.** For any smooth projective X of dimension n, a finite flat degree-d projective map f:X→P^n yields the genuine algebraic rank bundle \(u=[f_*\mathcal O_X]=d+\eta\) in \(K_0(P^n)\), where \(\eta^{n+1}=0\). Put \(N=n+1\) and define the integral adjugate recurrence
\[
A_0=0,\quad A_{k+1}=d^k-\eta A_k,\quad
A_N=\sum_{j=0}^{N-1}(-1)^jd^{N-1-j}\eta^j.
\]
Direct induction gives \((d+\eta)A_N=d^N-(-\eta)^N=d^N\), hence
\[
\boxed{d^Nu^{-1}=A_N\in K_0(P^n)}
\]
and, for each actual algebraic perfect complex E on X,
\[
\boxed{d^N\mathcal P_f^K(E)=d^NE-f^*(A_N f_*E)\in K_0(X).}
\]
The right side is visibly INTEGRAL: it uses only finitely many algebraic direct sums, tensor products, push/pull operations and differences.

For a prescribed rational Hodge alpha, each of the finitely many period coefficients \(q_i=Q(\alpha,z_i)\) is rational. Choose a positive finite common denominator \(D\) and integers \(m_i=Dq_i\). The explicit integral original-X class
\[
\boxed{[\mathscr C_\alpha]=
\sum_i m_i(d^N[E_i]-f^*(A_Nf_*[E_i]))
=Dd^N\,\mathcal E_\alpha\in K_0(X)}
\]
is realized by ONE actual bounded algebraic perfect complex: expand finite products into differences of genuine perfect complexes, use direct sums for positive coefficients, and one-step shifts for negative coefficients. Divide the Todd-corrected Chern class by \(Dd^N\) to recover the GST original-X rational Chow source \(Z_\alpha\). It obeys the exact equation
\[
\boxed{Q(\alpha,\operatorname{cl}_X Z_\alpha)=
\sum_iQ(\alpha,z_i)^2.}
\]

The Lean project now contains the dimension-uniform integral adjugate and virtual-source numerator statements in the EXISTING GST resolved-support module. Their latest GitHub focused verification must be checked at the post-repair revision before kernel-verification is claimed. The statements work algebraically with the actual finite-flat perfect-complex source operations; the Lean module-level abstraction does not itself install the complete scheme GRR/analytic Betti comparison.

**Mathematical outcome:** finite original-X algebraic perfect-complex construction from any fixed genuinely algebraic source catalogue, exact rational period response, finite integral denominator, and an exact source-detection test. The required all-X discovery is a geometric catalogue that detects every primitive rational Hodge direction; choosing coefficients does not invent new algebraic source directions.

## 4. Decisive geometric target and next experiment

The new \(K_0\) compiler is universal **as a construction for every alpha**, but its Hodge class remains in the span of the independently existing algebraic perfect-complex catalogue. It gives an automatically positive pairing for any alpha detected by that catalogue; it does NOT create a fresh class from a target residual which is orthogonal to every available algebraic K-theory source. Such a new source requires actual sheaf/derived geometric construction outside the previous algebraic span.

The next decisive GST geometric target is to develop an independently realized **family of perfect complexes whose algebraic primitive Chern characters detect a prescribed class beyond the existing catalogue**, using the real Hilbert/CM–NM/noncommuting original-X geometry rather than a freely chosen Hodge-space endomorphism. Algebraic sheaves varying inside one connected flat family have locally constant topological Chern classes, so a genuinely new rational cohomology direction must change the K₀ class/flat-family component, not merely continuously adjust the sections of a fixed bundle.

**Evidence classification:** genuine target-sensitive finite-\(K_0\) algebraic source and exact source pairing proved in Lean at the abstract linear interface, original-\(X\) Chow specialization checked, independent K3 real geometric test checked; universal all-X source-separation beyond the known catalogue and full canonical Betti realization remain independent geometric proof obligations. No arbitrary Hodge-to-Chow selector was inserted.

