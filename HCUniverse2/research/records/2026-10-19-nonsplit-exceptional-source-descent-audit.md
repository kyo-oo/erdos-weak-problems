# Mathbox GST — nonsplit exceptional-source descent audit

- **Date:** 2026-10-19
- **Kind:** adversarial direct mathematical check and route-scope limitation
- **Base:** research/gpt6-native-point-primitive-span-20261017 at positive construction record commit f2ce9a11f58e89b59652f7487f20505617b4d356
- **Corrects:** no prior theorem. Supplements [nonsplit blowup original-X source](2026-10-19-gst-nonsplit-blowup-incidence-perfect-complex.md) to prevent a false extension to arbitrary original X.
- **Original all-X target:** all X,p,alpha, canonical original-X Chow representative without any target-surjectivity assumptions
- **Test:** Can the positive exceptional primitive perfect-complex source from Bl_Q²(P4) be pushed down to the base as a new source, then reused as a generic-original-X construction?

Let pi:X=Bl_Y(P4)→P4, exceptional j:E→X, q:E→Y=P1×P1, h=a+b, δ=a-b, Z=j_*q*δ, E the exceptional Cartier divisor and ξ=c1(O_E(1)). Then E·Z=-j_*(ξ q*δ) and
\[
  \pi_* (E^k Z)
    =(-1)^k i_*\bigl( q_*(\xi^k)\,\delta\bigr).
\]
For N_{Y/P4}=O_Y(1)⊕O_Y(2) the projective-bundle pushforwards satisfy
\[
 q_*1=0,\quad q_*\xi=1,\quad q_*\xi^2=3h,\quad
 q_*\xi^3=(3h)^2-2h^2=7h^2.
\]
All higher terms vanish by dimension. In CH*(P4), i_*δ=0 because ∫Y hδ=0, and hδ=0. Therefore
\[
 \boxed{\pi_*(E^k Z)=0\quad\text{for every }k\ge0.}
\]
In particular pi_*Z=0 and no polynomial in E multiplied by this exceptional primitive source descends to a new Chow class on the base. This is a **geometric pushforward obstruction to this specific route**, not an obstruction to the Hodge conjecture or to different intrinsic Hilbert/incidence constructions on arbitrary X.

**Exact Wolfram test:** set a²=b²=0, δ=a-b, c1N=3(a+b), c2N=2(a+b)² and use the projective-bundle recurrence q_*ξ^k=c1N q_*ξ^(k-1)-c2N q_*ξ^(k-2). Returned k=0..6 pairs (q_*ξ^k, (q_*ξ^k)δ), reduced mod a²,b²:
k=0 (0,0); k=1 (1,a-b); k=2 (3a+3b,0); k=3 (14ab,0); k≥4 (0,0). The sole k=1 component dies after i_* to P4 as above. All arithmetic exact rational polynomial arithmetic.

**Decision:** the true perfect-complex source is valid and reconstructs every primitive target ON the nonsplit original blowup; do NOT propose "blow up an arbitrary X and push the exceptional source back down" as a universal original-X solution. The genuinely different next construction must reside intrinsically on the arbitrary original X, e.g. Hilbert universal incidence / scheme-theoretic determinantal sheaves, and show a target-sensitive primitive period against the actual prescribed residual. **No claim that such a universally detecting source exists has been established.**

**Evidence:** checked scheme-level pushforward identities and finite exact Wolfram recurrence; not a Lean-formalized blowup Chow instance. **Disposition:** this descent subroute closed by a valid restricted no-go; the original-Hodge Hilbert/incidence source route remains open.
