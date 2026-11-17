# GST Part 1 addendum — exact ORIGINAL U+J+M wave-to-Chow quotient

Date 2026-11-10. Supplements [the user's original Part-1 construction](2026-11-10-gst-hypothesis-part1-user-derivation-geometric-chow-square.md). Source proof: existing \`GSTHodgeWaveAllNHoleReadout.nativeWaveReadout_T\`, \`holeReadout_intertwines\`, \`waveReadout_seed\`, \`holeReadout_orbit\`; true Chow geometry in the previous record.

## Original GST — not a substitute matrix

The original GST 12-state Wave-I operator \`T0=U+J+M\` acts on the original 4 carry x 3 trit information graph. The original fixed-cell detector \(\ell_0(u)=u(0,0)-u(3,2)\) satisfies the existing Lean theorem
\[
\boxed{\ell_0(T_0u)=2\ell_0(u).}
\]
For every NShape \`s\` and every actual Wave-II hole \`i\`, the existing \`holeReadout_intertwines\` theorem gives the full original channel-shifted fold \`F_s\` and
\[
\boxed{\ell_0((F_su)_i)=(2+10s.\mathrm{channel}(i))\ell_0(u_i).}
\]
The original uniform GST seed has detector value exactly one in every hole, so its arbitrary-natural-iteration eigenvalues are genuine GST original laws.

## Exact universal geometric interpretation of each GST wave detector

For any original smooth projective complex \(X\) of dimension \(d\), any \(0\le p\le d\), any ample \(h\) with \(q=\int_Xh^d>0\), and any \`s,i\`, define
\[
\lambda_i=2+10s.\mathrm{channel}(i),\qquad
\Gamma^{GST}_{X,p,s,i}=\frac{\lambda_i}{q}\operatorname{pr}_1^*(h^{d-p})\operatorname{pr}_2^*(h^p)
\in CH^d(X\times X)_{\mathbb Q}.
\]
This is a **genuine algebraic Chow correspondence**, not an arbitrary linear map.
Let \(\Psi_i(u)=\ell_0(u_i)\,h^p\) be the map from the original GST N-wave carrier to genuine original-X codimension-p cycles. Its genuine Chow action \(\mathcal N_i\) satisfies
\[
\boxed{\Psi_i(F_su)=\mathcal N_i\Psi_i(u)}
\quad\text{because}\quad
\mathcal N_i(a h^p)=\lambda_i a h^p.
\]
The canonical Betti action \(\mathcal T_i\) satisfies \(\operatorname{cl}(\mathcal N_i Z)=\mathcal T_i\operatorname{cl}(Z)\) on *all native cycles Z*, not only those in \(\Psi_i\)'s range, by the Chow push-pull/projection formula. Hence
\[
\boxed{\operatorname{cl}(\Psi_i(F_s^n u_*))=
 \lambda_i^n \operatorname{cl}(h^p)\ \text{for all }n\ge0.}
\]
This is a direct, exact, **unconditional, every-original-X** realization of one original GST wave-eigenchannel on a genuine algebraic Chow-line quotient. It uses the user's original seven-axis information fold, Wave-I SURVIVE source, CM mirror and Wave-II/N-cohomology channel shift.

**Critical rank boundary:** \(\operatorname{im}\Psi_i=\mathbb Q h^p\) is one dimensional. This is a quotient of the complete \(12N\)-coordinate GST wave signal, not a faithful full-wave representation on \(W_p(X)\), and does not imply unknown higher-primitive Hodge directions algebraic. Global Hodge cyclicity remains the independently required universal theorem.

## Independent exact computation

The [committed Wolfram source](../computations/GST_original_Nwave_geometric_ample_quotient_20261110.wl) was fetched back and executed verbatim, returning \`allPassed -> True\`. It built original 12x12 U,J,M from the canonical carry/trit laws, proved U^5=I, J^2=-I, the fixed-cell left-eigenvalue \`2\`, the original uniform seed readout \`1\`, and a 36x36 three-hole shifted original wave with addresses 0,3,9. All three literal eigenvalues \`2,32,92\` passed full-matrix intertwining and orbit checks for n=0,...,8. The universal all-N algebraic identity is already formalized in the existing Lean file, not inferred from the finite Wolfram sample.

**Verdict:** exact positive original-GST-to-geometry *rank-one quotient* established; exact full original-GST-to-canonical-Hodge source-full-rank realization not established. Do not merge these claims.
