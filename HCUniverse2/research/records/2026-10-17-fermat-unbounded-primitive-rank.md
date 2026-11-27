# GST construction — unbounded independent primitive cycles

## Theorem target
Construct arbitrarily large families of **geometrically independent primitive algebraic middle cycles** on original smooth projective varieties, uniformly across even dimensions.

## Explicit geometry
For \(m\ge1,d\ge3\), define

\[
X_{m,d}:\sum_{i=0}^{m}(y_i^d-x_i^d)=0\subset\mathbb P^{2m+1}_{\mathbb C}.
\]

Its projective Jacobian is nonsingular. Each distinct \(d\)-th root of unity \(\zeta\) gives a maximal linear plane \(P_\zeta\) through the equations \(y_i=\zeta x_i\). The planes are pairwise disjoint.

Let \(H=h^m\), \(q=q_{m,d}=c_m(N_{P_\zeta/X})\), and \(Z_\zeta=d[P_\zeta]-H\). Their intersection measurements are

\[
H^2=d,\quad H[P_\zeta]=1,\quad
[P_\zeta][P_\eta]=q\delta_{\zeta\eta},\quad
Z_\zeta Z_\eta=d^2q\delta_{\zeta\eta}-d.
\]

The exact normal-Chern recurrence is \(q_0=1\), \(q_{m+1}=1+(1-d)q_m\). For \(m\ge1,d\ge3\), \(q\le-1\) or \(q\ge2\). Therefore the Gram eigenvalues \(d^2q\) and \(d^2(q-1)\) are nonzero, producing \(d\) independent primitive rational Hodge directions.

## Machine proof
- [Run #39022136074](https://github.com/kyo-oo/HC-PROOF/actions/runs/39022136074): fourfold full-rank theorem.
- [Run #39022662792](https://github.com/kyo-oo/HC-PROOF/actions/runs/39022662792): all-dimensional normal-Chern sign and rank.
- [Run #39022821753](https://github.com/kyo-oo/HC-PROOF/actions/runs/39022821753): smooth Fermat equations and pairwise plane separation.
- [Run #39022986348](https://github.com/kyo-oo/HC-PROOF/actions/runs/39022986348): cohomological measurement bridge.

## Next construction
Generalize the independent geometric cycle mechanism from these explicit hypersurfaces to all original smooth projective carriers and all primitive rational Hodge directions, using canonical cycle-class comparisons.
