# GST universal Hodge priority: CM+NM geometric descent and obstruction

**2026-10-15. Contributor name omitted.**
**Full target:** for every smooth projective complex X and every rational Hodge (p,p) class α, construct a genuine algebraic cycle Z with cl(Z)=α.
**Status:** OPEN. No unconditional proof of this full target is established by this checkpoint.

## Independently kernel-verified today

Source: GSTUniversalCMArithmeticObstruction.lean, GitHub Actions run 38683156369 (SUCCESS, no sorryAx). Two new conclusions are proved:

1. The imaginary-quadratic CM polynomial T²−2aT+(a²+b²)I=0, b≠0, cannot hold on the rational one-dimensional module Q. Thus the previous 'J²=-I everywhere' proof route cannot apply uniformly to all genuine Hodge weights, including rank-one Hodge fibers.
2. Every genuine algebraic cross-carrier correspondence takes the class of an actual algebraic source cycle into the algebraic cycle-class range of the target. The obstruction survives composition. Thus formal CM or GST transport of **already algebraic** classes alone cannot create the existence of an unrepresented rational Hodge class.

This does not refute the Hodge conjecture; it rules out using these insufficient operations as its universal existence proof.

## New constructive finite-degree route

Source: GSTCMFiniteGeometricDegreeDescent.lean, independently **kernel verified**, GitHub Actions **38683813227 SUCCESS** after correcting the Lean Stage-2G membership application. The earlier run 38683541455 failed on that API-application error, not a mathematical counterexample.

Let f:A→X be a generically finite surjective morphism of **smooth projective** complex varieties of equal dimension, with degree d>0. Proper algebraic pushforward and rational cohomology pullback obey the genuine geometric degree identity f_*f^*=d·id.

Assume the rational Hodge conjecture has already been **independently established** for the source A. Given a rational Hodge (p,p) class α of X, pull it back to f*α, obtain an actual algebraic source cycle C with cl(C)=f*α, then explicitly form

\[
Z = \frac1d f_* C.
\]

Because pushforward of a rational algebraic cycle remains algebraic and the cycle-class square is natural, cl(Z)=d^(-1)f_*f*α=α. There is no target Hodge class preimage inserted as an input. This proves Hodge for targets actually dominated by independently solved sources with a proven degree-split action.

The CM-NM Gaussian source family E_i^g, where E_i=C/(Z+iZ), gives a genuine test of this mechanism. A finite free group quotient E_i^g/G is one example of a target with a genuinely constructed finite dominant map from that source. Singular quotients and their resolutions require additional verified geometric steps.

**This mechanism does not cover arbitrary X without actual dominating source geometry.**

## A real counterexample to universal Gaussian-CM elliptic dominance

For a smooth projective curve C with genus >=2 there is no nonconstant morphism f:E→C from an elliptic curve E. Indeed the Riemann-Hurwitz formula gives

\[
0=2g(E)-2=\deg(f)(2g(C)-2)+R>0
\]

for a nonconstant morphism, contradiction (R>=0). Thus not even every *curve* is dominated by E_i^1. In particular the claim 'every smooth projective n-fold is the generically finite image of the specific NM-generated E_i^n' is **false**. This obstructs that particular universal proof method, NOT the Hodge conjecture.

The target could admit other geometric sources or correspondences; their existence and surjectivity must be proved, not renamed as a GST law.

## Known unconditional Hodge range on arbitrary X

For every smooth projective complex n-fold X, the rational Hodge conjecture is already established for p=0,1,n−1,n:

- p=0: classes of connected components.
- p=1: the classical Lefschetz theorem on (1,1) classes yields rational divisor classes.
- p=n−1 for n>=2: Hard Lefschetz gives L^(n−2):H²(X,Q)≅H^(2n−2)(X,Q); a rational (n−1,n−1) class has rational (1,1) inverse image, represented by a rational divisor D; the algebraic intersection D·H^(n−2) represents the target.
- p=n: classes of closed points on connected components.

Consequently the rational Hodge conjecture holds for every smooth projective X of dimension <=3. The first generally open geometry occurs at n=4, p=2, including the primitive rational (2,2) classes.

Source verification: Theorem 3.39 of https://etheses.durham.ac.uk/id/eprint/3716/1/3716_1277.pdf discusses exactly this dimension/codimension reduction and the Lefschetz (1,1) theorem. These are known classical results, not a new GST solution.

## Exact next original priority

For arbitrary smooth projective fourfold X, build actual rational codimension-two cycles for EVERY rational primitive (2,2) class, and give an inductive/functorial argument extending the mechanism to all X and p. This is the genuine non-circular existence problem that the CM–NM formulas have not yet resolved.

Do not assert a universally available CM isogeny action, universally sufficient abelian-source correspondences, arbitrary fixed zeta/period readouts, or geometric matrix-unit naturality as a free hypothesis. An arithmetic identity and an exact Lean kernel pass do not replace the genuine cycle-class geometry.

The present proof attempts give a new geometrically legitimate finite-degree transfer mechanism with explicit output cycle, plus verified obstructions to extending the specific Gaussian-CM source blindly to every X. Overall original Hodge program: unresolved.