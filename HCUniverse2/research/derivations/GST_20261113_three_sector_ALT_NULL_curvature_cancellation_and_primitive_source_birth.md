# GST three-root ALT/NULL curvature-cancellation and primitive-source birth

**Status:** new mathematical integration of GST's existing wave operators with classical matrix-factorization/Koszul geometry; exact symbolic checks performed. **NOT** a universal Hodge conjecture proof, novelty claim, or Lean-kernel result.

**Base:** original branch at 01c908d116f1d1397a5e59bea11a8c561ab7b991. New math first; all existing Lean files unchanged.

## Original GST map (owner's 3 universes, NOT a new artificial graph)

- GSTGraphV2OmniversalCore: three ontological sectors gstPlus, altMinus, null; event and path semantics.
- GSTGraphV2SelfExpandingCosmology: arbitrary-arity certified world births and mixed-root descendants.
- GSTGraphV2OmniversalHyperEvents: higher-arity generation that can encode tensor/intersection operations.
- GSTGraphV2CMWaveFusion: owner's 12-cell U, CM J, true SURVIVE M.
- GSTImageThreeCurvatureResonance: actual commutator C=[J,M], source-sensitive full F=U+J+aM+bC.
- GSTWorldCosmology and GSTGradedWorldAlgebra: unbounded finite-window states and graded sectors.
- waves/GSTNCohomologyV3: independent N-hole channel coordinates and curvature-boundary tests.

We propose to interpret a **new certified three-world hyper-event** as a crossed differential, while retaining those original definitions and separating wave analogies from proved geometry.

## Exact law 1: GST+ and ALT- have opposite curved squares

Let R be a commutative Q-algebra, x,y in R. Retain the original fixed-pair matrices:

    J = [[0,1],[-1,0]], M = [[0,0],[0,2]],
    C = JM-MJ = [[0,2],[2,0]].

The original algebra generates the elementary channels

    E12 = J/2 + C/4 = [[0,1],[0,0]],
    E21 = -J/2 + C/4 = [[0,0],[1,0]].

Define

    Qplus = x E12 + y E21
    Qminus = x E12 - y E21.

Direct multiplication (no extra independent operator assumed) proves

    Qplus^2 = xy I2,  Qminus^2 = -xy I2.

Set Sigma=diag(1,-1), and on the four-state crossed world put

    D = Qplus (tensor) I2 + Sigma (tensor) Qminus.

Since Sigma Qplus = -Qplus Sigma and Sigma^2=I2, the mixed products cancel. Thus

    D^2 = (xy-xy) I4 = 0.

This is an algebraic graded-differential cancellation. It does NOT say the original (0,2) holomorphic connection-curvature obstruction is resolved: these are different typed curvatures.

## Exact law 2: NULL cohomology is a genuinely constructed algebraic source

Over R=Q[x,y], put even states in basis indices {1,4} and odd states {2,3}. The crossed operator has blocks

    d0: Even -> Odd = [[-y,x],[y,-x]],
    d1: Odd -> Even = [[x,x],[y,y]].

Both d0 d1 and d1 d0 equal zero.

The pair x,y is a regular sequence. One computes explicitly

    ker d0 = R*(x,y) = image d1,
    ker d1 = R*(1,-1),
    image d0 = (x,y)*R*(1,-1).

Hence H_even=0 and H_odd = R/(x,y). This is the actual structure module of the origin in affine algebraic 2-space, not a freely inserted target-cohomology symbol.

For non-regular input x=y=t over Q[t], both parity cohomology groups instead become Q[t]/(t), detecting an excess/nontransverse NULL channel. Transversality is a genuine theorem hypothesis.

The two-periodic crossed complex is isomorphic by constant basis changes to the two-periodization of the Koszul complex for the ordered section (x,y). When E is an algebraic rank-two bundle on smooth projective X and s is a *regular algebraic section*, the invariant Koszul complex

    exterior^2(E^dual) -> E^dual -> O_X

glues globally, with surviving coherent cohomology O_(zero(s)) and actual codimension-two cycle [zero(s)]=c2(E) cap [X]. The combined NULL object glues even if the particular separately expressed GST+ and ALT- curved factors need not glue by themselves. This is **known Koszul geometry**, now represented by exact original GST J/M/C formulas.

## Exact law 3: non-hyperplane primitive born on an original projective fourfold

Let X=Gr(2,4) over C (complex dimension 4), S universal rank-two subbundle, Q rank-two quotient, h=c1(S^*)=c1(Q).

- A generic section of S^* vanishes on Gr(2,3)=P^2, a regular codimension-two subscheme. Denote its algebraic class A=c2(S^*)=sigma_(1,1).
- A generic section of Q vanishes on Gr(1,3)=P^2, another regular codimension-two subscheme. Denote its algebraic class B=c2(Q)=sigma_2.

Both A and B therefore are actual original-X algebraic cycles produced by the NULL/Koszul birth semantics, not prescribed Hodge preimages.

Standard Grassmannian Chow/Schubert identities:

    h^2=A+B,   hA=hB=sigma_(2,1),
    int_X A^2=int_X B^2=1,   AB=0.

Consequently P=B-A is Chow-primitive (hP=0), nonzero (int_X P^2=2), and not in the one-dimensional hyperplane-only span Q*h^2. The middle rational Hodge space is precisely Q*A+Q*B by the known Schubert cell decomposition. This is a genuine source-direction gain **relative to the hyperplane-only sector**, NOT a claim to cross the full algebraic-image/Hodge-defect boundary.

## Exact law 4: the owner's N+N² original physical two-cell wave reconstructs the born primitive from one Chow seed

The ORIGINAL GST fixed null/maximum pair, with direct source coefficient a=1 and physical navigation b=0 or b=1, is

    T_b = [[1,1+2b],[2b-1,3]].

Use rational intersection duals to realize this matrix as an actual algebraic correspondence on CH^2(Gr(2,4)) in the basis (A,B). Implement precisely the owner's original proposed second-order fold F_b=T_b+T_b^2:

    F_0=[[1,5],[-5,11]],   F_1=[[5,15],[5,15]].

With single actual Chow seed A,

    det[A,F_0 A]=-5; det[A,F_1 A]=+5.

In fact the exact primitive class has two alternate source-wave expressions:

    P=B-A= -(4/5) A-(1/5)F_0 A
             = -2 A+(1/5)F_1 A.

This realizes the true original **two-cell factor** and both physical navigation states, not the entire 12-cell wave on a rank-two Hodge space.

## Boundary theorem and remaining universal obligation

Every finite within-X word of genuine Chow correspondences preserves the image of the canonical algebraic cycle-class map. Cardinal many labels, graph closure, extra native coordinates and nonzero commutators alone cannot change that invariant. The new triadic hyper-event takes *different inputs* (actual algebraic bundles plus regular sections) and produces new directions compared to a smaller pre-existing operator/ample-only source sector.

The actual universal owner target is: arbitrary original smooth projective X, p and prescribed rational Hodge alpha -> produce a new actual codimension-p algebraic cycle of canonical class alpha, without assuming a prior Chow representative. The current three-sector law constructs nontrivial codimension-two sources for available regular sections, including a higher-primitive Gr(2,4) class. It does not construct alpha-sensitive algebraic bundle/section data on every X, so it does not settle universal source birth. **Do not promote the missing alpha-to-bundle existence to a free "GST birth" field.**

## Verification, provenance and historical status

- Exact Wolfram: Qplus^2=xy I, Qminus^2=-xy I, D^2=0, d0,d1, original navigation determinants -5/+5.
- Independent SymPy script /mnt/data/gst_triad_alt_null_exact_check.py, SHA256 a61103814108532651e238faf7a92578bd07dcd83588b8fceed68919010621d2; its symbolic assertions passed. (This container path is not part of the GitHub repository.)
- Standard Schubert calculus and algebraic zero-locus theorem; see symmetricfunctions.com/schubert-calculus.htm and sites.lsa.umich.edu/idolga/wp-content/uploads/sites/1334/2024/08/CAG.21.pdf. Opposite-potential tensoring and Koszul sign rules are established matrix-factorization mathematics; do not assert literature novelty without a separate literature audit.
- The reviewed original Lean modules remain unchanged; no new Lean CI green is claimed.
- Mathbox-style evidence: original symbolic algebra proved; geometry on Gr(2,4) supported by standard exact Schubert identities; extension to all X incomplete. This record is additive and does not alter prior theorems.
