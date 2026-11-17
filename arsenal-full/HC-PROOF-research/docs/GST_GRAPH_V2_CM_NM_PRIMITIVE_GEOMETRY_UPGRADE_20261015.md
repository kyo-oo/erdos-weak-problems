# GST Graph V2, CM–NM and primitive geometry — upgraded bridge

Date: 2026-10-15. Authorship deliberately anonymous.
Branch: mathbox/bd23-single-operator-charge-wedge.
Original target: algebraic representatives of all primitive rational Hodge classes on arbitrary smooth projective complex varieties. NOT YET PROVED.

## Existing graph identified

1. GSTGraphV2Production.lean: historical unbounded x4/base3 arithmetic production sheet.
2. GSTGraphV2ArithmeticOmniversalRealization.lean: actual arithmetic node carrier, horizontal and vertical causal events, legacy seven-axis observable.
3. GSTGraphV2OmniversalCore.lean: sector-aware graph, finite certified paths, all-index causal closure, event morphisms.
4. GSTClassicalHodgeOmniversalConstructorGraph.lean: actual codimension-point cycles, rational Betti/Hodge nodes and geometric cycle-class edges, with NO arbitrary Hodge-to-cycle reverse arrow.

These are preserved, not replaced. The new CM-NM geometric extension is GSTGraphV2CMNMPrimitiveUpgrade.lean (focused Lean CI 38713065733 SUCCESS). The coupled arithmetic plus true geometry extension is GSTGraphV2CMNMCoupledUniverse.lean (**CI 38713197684: SUCCESS**).

## The user's Equations (4) and (5) as precise typed mathematics

Equation (4) proposes A_g(s) ± GST infinite cosmology ⊕ G_a × primitive Hodge classes. The symbols mix different types; A_g, G_a, direct sum, signed operation and Hodge primitive tensor require real definitions. The upgrade interprets their useful arithmetic-to-geometry action *without pretending this is an already proved equality*.

For Gaussian rational x,y let u_m=x^(m+1)-y^(m+2). Define the fixed rational CM readouts r_m=Tr_Q(i)/Q (1/u_m) and s_m=2 Im(1/u_m). Given two actual projective scheme morphisms f,g : X→X and one native codimension-p algebraic cycle Z, build the actual rational algebraic cycle

Z_NM = r_m f_*Z + s_m g_*Z.

There is a **proved forward cycle-class identity**:

cl_p(Z_NM) = r_m cl_p(f_*Z) + s_m cl_p(g_*Z).

**Exact non-cancellation audit:** a nonzero CM denominator need not make every geometric sum nonzero. For u=1+i, the inverse is (1-i)/2 and the two rational readouts are (r,s)=(1,-1), verified exactly by Wolfram. If f=g, then Z_NM=(r+s) f_*Z=0 even when the source Z is nonzero. Therefore geometric independence of actual correspondence images must be separately derived; arithmetic nonvanishing alone does not force all primitive directions. This prevents a false "universal rank" claim.

The new graph has a genuine native-cycle event creating Z_NM; the old graph events embed identically; cycle-to-Hodge is allowed only for an actual algebraic cycle. Nothing here selects a preimage of an arbitrary Hodge target.

Equation (5) proposes lim_{x→infinity} ℒ(n^x) tensor primitive cycles. The function ℒ, topology, normalization and target are not specified. Wolfram evaluated the unnormalized 3^x limit as +Infinity. Therefore the safe precise interpretation is the EXISTING indexed closure-union identity:

Closure(union_n Seed_n) = union_n Closure(Seed_n).

This follows for arbitrary index sets and retains all finite event stages without assuming a convergence or finite terminal dimension. It does NOT turn all Hodge classes algebraic automatically.

## Wolfram check of prior all-codimension projective primitive formula

For X dimension d=6 and p=3, existing all-dimensional product polynomial (with u and t hyperplane classes on X and P³) has coefficients {1,-4,10,-20}:

P=u³-4u²t+10ut²-20t³.

Exact Wolfram polynomial ideal reduction gives the remainder of (u+t)^4 P modulo <u^7,t^4> equal to ZERO. This independently tests the existing generic formula derived from the negative-binomial identity. It does not formalize native projective Betti cycle-class comparison for an arbitrary X.

Gaussian CM test: (1+i)^2-i^3=3i has ZERO real trace, and a nonzero imaginary channel; therefore retaining both rational CM channels is essential.

## Geometric primitivity versus Hodge algebraicity

An arbitrary projective pushforward need NOT preserve primitiveness with respect to an arbitrary polarization. Additional certified Lefschetz compatibility is required. Therefore the graph creates actual native cycles, not arbitrarily declared primitive cycles.

The upgraded graph proves all its events preserve actual algebraicity. The equality between its Hodge reachability closure and genuine existence of a native cycle is also verified. It is a structural FIREWALL, not a universal Hodge proof.

To finish the original target one must construct enough independently algebraic primitive Hodge directions for arbitrary smooth projective X, using true primitive-preserving mixed correspondences and a separately proved non-circular rank/surjectivity statement.

## C. Primitive-preserving geometric realization added and verified

The separate GSTGraphV2CMNMPrimitiveLefschetzBridge.lean (**CI run 38714580375: SUCCESS**) extends the graph with a precisely typed rational Betti Lefschetz-kernel test L. If the actual cycle classes of f_*Z and g_*Z are annihilated by L, the exact CM-NM-weighted cycle is also annihilated by L. It also proves the genuine one-step GST coupled-graph reachability of this primitive-tested native cycle at EVERY arithmetic address. This is not an unjustified claim that arbitrary pushforwards preserve primitiveness: the two geometric inputs are checked explicitly.

The module imports the earlier verified universal codimension-two primitive polynomial profile for X×P² and reuses its exact coefficient cancellation, without misrepresenting that coordinate model as a fully formalized scheme-theoretic Betti comparison. Both the older product primitive module and the new graph primitive bridge have now been registered in lakefile.toml. The three certified new graph modules are imported into the public HodgeConjecture.lean root.

## Verification checkpoint

- 38713065733: CM-NM native geometric graph upgrade, SUCCESS.
- 38713197684: Coupled infinite arithmetic-geometric GST universe, SUCCESS.
- 38714580375: Primitive-kernel native CM-NM bridge, SUCCESS.
- Full HodgeConjecture.lean root: separate long compilation, not automatically equivalent to Hodge conjecture.

Original universal rational Hodge conjecture: NOT PROVED. Remaining: produce enough actual primitive class directions on arbitrary varieties and prove true primitive-surjective geometric correspondences.

No local Lean installation and no public internet search.
## 2026-10-16 Mathbox / Wolfram: conserved-charge graph saturation

Original all-X Hodge goal: not proved. An exact rational four-dimensional
operator model distinguishes noncommutativity from universal geometric rank.
Seed S=(1,1,0,0), swap A exchanges coordinates 2,3 and fixes coordinates
1,4; diagonal B=diag(1,2,3,5). Both preserve first-coordinate charge.
The commutator [A,B]S=(0,0,-1,0) is NONZERO, verified with Wolfram.
Nevertheless all finite words and rational linear combinations applied to
S stay in the hyperplane x4=0. The exact orbit rank is 3, not 4.
The basis graph's seeded vertices {1,2,3} cannot reach coordinate 4.
This is a toy graph representation, NOT a counterexample on a variety.

Lean source upgraded at 5c413b8ca82a2ddbe4961709732b0213ec965e82:
GSTClassicalHodgeActualCommutatorRankGain.lean formalizes the finite graph
invariant and an unreachable fourth basis direction. The existing file
GSTMathboxIndependentGeometricCoordinate.lean proves a STRICT algebraic
Hodge-span increase when an independently constructed ACTUAL native cycle
has a rational detector reading zero on every old cycle and nonzero on
the fresh one, without any fixed rank bound.

The unresolved geometric theorem is the genuine construction of such fresh
native cycles for EVERY remaining primitive rational Hodge direction of
EVERY smooth projective complex variety. It cannot be inferred solely from
graph connectivity, conserved charge, or nonzero commutators.

### Genuine two-direction geometric success test on P1 x P1

Take X=P1_C x P1_C. Its two native ruling divisors h1,h2 are
algebraic and have intersection matrix J=[[0,1],[1,0]], J^2=I.
The dual classes are d1=h2, d2=h1. On X x X, genuine algebraic
codimension-two product correspondences
C_ij=pr1^*(d_j) * pr2^*(h_i) implement rational matrix units
on H^2(X,Q): C_ij(h_k)=delta_jk h_i, by the projection formula.

Choose A=I+E_21=[[1,0],[1,1]], B=diag(1,2), S=h1.
The first-coordinate charge is preserved by A and B.
Wolfram exact result: [A,B]S=(0,-1), and the determinant of the
columns S and [A,B]S is -1, hence both independent divisors span
the entire two-dimensional rational Hodge fiber. All these
correspondences come from explicitly algebraic divisor products.

This demonstrates a truly geometric positive instance of the GST
commutator-rank strategy. It does NOT extend to arbitrary X unless
enough algebraic product-correspondence classes dual to the UNKNOWN
primitive Hodge directions are independently constructed. Assuming
such algebraic dual basis classes on arbitrary X would be circular.
