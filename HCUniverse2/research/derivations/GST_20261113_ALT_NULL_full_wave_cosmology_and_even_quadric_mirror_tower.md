# GST ALT/NULL all-N wave compatibility and arbitrarily-high mirror-primitive quadric tower

**Status:** mathematically proved algebraic and tensor identities, with classical quadric Chow geometry as an external input. This is a second, uniform development of the first GST triad ALT/NULL source-birth record, not a universal Hodge proof or a Lean verification claim.

**Input branch:** research/gpt6-native-point-primitive-span-20261017; original GST reference 01c908d116f1d1397a5e59bea11a8c561ab7b991; preceding research commits 353dfa114fdefdc9f9dc1d73b5029b2c6c821cae and 4ff683e9ebf9176ae636e68d0ffa068a93ddc195.

## Full original 12-cell wave on a TRUE NULL differential

From the preceding theorem, over R=Q[x,y], the four-state GST+ (tensor) ALT- differential D obeys D²=0 and its cohomology is H_odd(D)=R/(x,y), H_even(D)=0.

Let V be the owner's ORIGINAL 12-state WaveSignal module (with Q scalars extended to R), and retain WITHOUT substitution the actual finite GST operators U,J,M, C=[J,M] and physical T_b=U+J+M+bC, b=0 or 1 (GSTGraphV2CMWaveFusion and GSTImageThreeCurvatureResonance).

On W=R^4 tensor_R (R tensor_Q V) define

  D_V = D tensor I_V,
  T_V,b = I_4 tensor T_b.

Then D_V²=0 and [D_V,T_V,b]=0 for ALL b, because (A tensor I)(I tensor B)=A tensor B=(I tensor B)(A tensor I). Hence the COMPLETE ORIGINAL physical 12-state wave descends to the NULL homology, H_odd(D_V)=R/(x,y) tensor_Q V, for every parameter. Its actual five-cycle shuffle U^5=I and complex J^2=-I remain valid on that module.

This was checked independently as an exact 48×48 integer matrix identity for two nonzero integer coordinates x=2,y=3 and both physical navigation states b=0,1 in Wolfram and SymPy; the general theorem is the displayed tensor identity, NOT extrapolation from the sample.

For N-hole Wave-II channels V_N= direct_sum_(i in N) V (for any finite N) the same proof gives H_odd(D tensor I_VN)=R/(x,y) tensor V_N. For an arbitrary cardinal index type I, the finite-support direct sum V_(I) has the same algebraic exactness by exactness of direct sums. This is a genuine unbounded/cosmological SOURCE-COMPLEX construction. It is NOT a claim that an infinite direct sum is a finite-type perfect complex or that formal 12I wave coordinates yield 12I linearly independent cycle classes on one projective X. Geometry controls that final rank.

## Any finite codimension via repeated triadic NULL births

Given a smooth projective X, rank-p algebraic bundle E with a regular global section s and p ≤ dim X, its coordinate-free Koszul complex uses all exterior powers of E^dual. On local trivializations, the p components of s form a regular sequence and the Koszul complex has only the coherent sheaf O_Z(s) as surviving homology. Its cycle has codimension p and class c_p(E).

For even p=2m, organize local coordinates in m adjacent (+,ALT) mirror pairs, apply the preceding 4-state curvature-cancelling construction to each pair, and take the graded tensor totalization. The anti-commuting Koszul signs imply a total square-zero differential; regularity gives exactly R/(f1,...,f_(2m)) cohomology in one total parity (the two-periodization of the usual Koszul complex). For odd p add the ordinary one-coordinate 2-term Koszul differential for the final variable. The coordinate-free exterior-power construction glues globally by algebraic GL_p transition maps. This yields actual algebraic cycles in EVERY prescribed finite codimension WHEN the needed rank-p algebraic bundle and regular section are supplied. Their availability from arbitrary prescribed Hodge alpha is NOT established; do not silently assert such a selection law.

The only new GST-specific aspect is realizing each two-coordinate Koszul pair through the owner's actual J/M/commutator and the three universal sectors. Koszul exactness itself is standard (Stacks project tag 062D).

## Uniform mirror-primitive family in every even complex dimension

For each m≥1 let X_m=Q^(2m) be any smooth complex projective quadric of even dimension 2m, h the hyperplane class. There are TWO distinct families of maximal linear projective m-planes. Their true codimension-m Chow classes A_m,B_m form the rank-two middle Chow/Hodge basis. Classic quadric intersection theory gives

  h^m=A_m+B_m;
  h A_m = h B_m;
  pairing_m = identity matrix if m even,
  pairing_m = [[0,1],[1,0]] if m odd.

Thus the opposite-world difference P_m=B_m-A_m is a genuine Chow-primitive class:

  h P_m=0;  ∫_(X_m) P_m^2=2*(-1)^m !=0.

This is a real two-ruling/mirror geometry for ALL m, not an invented non-algebraic source direction. The middle rational Hodge space is spanned by A_m,B_m, known by the cell decomposition of split quadrics. Source reference: classic even quadric Schubert calculus (including the two middle classes and h^m relation; e.g. quantum cohomology of minuscule homogeneous spaces, §even dimensions, and standard split-quadric Chow motives).

Because the exact intersection matrix is invertible for both parities, use its inverse to build genuine codimension-2m Chow matrix units on X_m×X_m. Realize the original GST null/maximum physical factor T_b=[[1,1+2b],[2b-1,3]] on (A_m,B_m) as a genuine correspondence. The owner's Part I second-order F_b=T_b+T_b² produces

  det([A_m,F_0 A_m]) = -5;
  det([A_m,F_1 A_m]) = +5

independently of m. Exact recovery of the born primitive:

  P_m = -(4/5)A_m -(1/5)F_0 A_m
      = -2 A_m +(1/5)F_1 A_m.

This is an unbounded-dimensional theorem for actual Chow cycles and the two-cell original GST wave quotient; it does not claim the full 12-state operator is algebraically independent on these two-dimensional fibers. The quadric geometry is classical; its wave realization is explicit.

## What the tower cannot yet do

All X_m above are geometries where the Hodge conjecture already holds by known cellular/quadric arguments. The coherent NULL source can increase the span relative to **hyperplane-only** sources but does not create an unknown Hodge class outside the FULL algebraic cycle-class image on arbitrary X.

The universal original-X proof remains to construct, for arbitrary (X,p,alpha), alpha-sensitive algebraic section/bundle/complex data without assuming the desired target class is already algebraic. Original U,J,M,N-hole/cohomology, cardinal-world indexing and +/ALT NULL cancellation are now faithfully combined at the level of certified algebraic complexes. A universal alpha-to-algebraic input theorem has NOT been proved.

## Executed checks

- Symbolic Wolfram and independent SymPy 4×4 and 48×48 exact integer checks.
- Wolfram exact both parity pairings and the wave determinants ±5.
- Source literature context: stacks.math.columbia.edu/tag/062D (Koszul regularity); split even quadric Schubert calculus, rank-two middle cohomology, max-plane classes.
- All mathematical statements separately scoped; no Lean sources modified; no fresh Lean CI claim.
