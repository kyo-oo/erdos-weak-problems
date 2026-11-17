# GST construction — canonical analytic fundamental classes

## Target
Build the canonical rational Betti cycle-class map for each genuine algebraic codimension-\(p\) cycle on a smooth projective complex variety \(X\).

## Geometric definition
For an irreducible closed subvariety \(V\subseteq X\) of complex dimension \(n-p\), its complex analytic regular locus gives a canonical orientation. The resulting analytic Borel–Moore fundamental class extends across the singular locus:

\[
[V_{\mathrm{an}}]\in H_{2(n-p)}^{BM}(V_{\mathrm{an}},\mathbb Z).
\]

Projectivity makes \(V_{\mathrm{an}}\) compact. The proper inclusion \(i:V_{\mathrm{an}}\hookrightarrow X_{\mathrm{an}}\) and Poincaré duality produce

\[
\operatorname{cl}_X([V])=\operatorname{PD}_X(i_*[V_{\mathrm{an}}])
\in H^{2p}(X_{\mathrm{an}},\mathbb Q).
\]

Extend linearly over finite rational cycle sums. Closed integration currents identify these classes as Hodge type \((p,p)\). Projective intersection theory and normal-bundle self-intersection give the exact cup-product measurements for the Fermat sources.

## Fermat realization
For \(X_{m,d}:\sum_i(y_i^d-x_i^d)=0\), choose the \(d\) disjoint planes \(P_\zeta\), \(\zeta^d=1\), and \(Z_\zeta=d[P_\zeta]-h^m\). Their geometric primitive Gram is \(d^2 q_{m,d}I_d-dJ_d\), \(q_{m,d}=[t^m](1+t)^{m+1}/(1+dt)\).

## Lean integration
`GSTClassicalHodgeGeometricCycleClassPointRigidity.lean` builds the finite rational extension from point classes. `GSTCanonicalPointGeometryStage2G.lean` assembles all codimensions. `GSTFermatCanonicalPointRankBridge.lean` connects native subvariety cycles to the measured Gram.

**Next construction:** implement the analytic Borel–Moore, proper pushforward, and Poincaré duality terms in the Lean geometric library, and establish the pointwise comparison theorem.
