# GST Mathbox — first-order Weil Hodge leak of the raw derived graph-ideal source

- **Date:** 2026-10-20 (IST)
- **Kind:** direct source/deformation falsification and exact Chern-character audit
- **Active route:** original-X primitive algebraic source birth for the rational Hodge conjecture; bounded test on the central CM Weil sixfold
- **Base:** `77e77e676841698d88b8ec6700c39540d0fbf0f8`
- **Lean change:** `GSTUniversalCMArithmeticObstruction.lean`, commit `505d13671430bb8a65caa414d9b441794dc9d3f6` (exact coefficient/Chern arithmetic; CI revision-matched status to check)
- **Review:** Mathbox-guided self-audit, independent direct exterior expansion and exact symbolic Chern computation; not an independent proof audit of scheme-level family geometry
- **Evidence boundary:** Lean proves commutative ring / integer certificates; the holomorphic family, geometric Chern comparison and Atiyah implication are worked mathematical derivations, not Lean-inhabited scheme structures

## Source and exact fixed Chern data

On the central Weil-type abelian sixfold `A=E^3_x × E^3_y` with `K=Q(i)` acting as `+i` on x and `-i` on y, choose two embedded codimension-three graph abelian subvarieties:

- `Z0`: for each k=1,2,3, `x_k - y_k = 0`;
- `Z1`: for each k, `(2-i)x_k - (2+i)y_k = 0`.

Their intersection has 64 reduced points, and each graph has trivial normal bundle. Write `zj=[Zj]`. The actual perfect object is `F=RHom_A(I_Z0,O_A) ⊗^L I_Z1`; the recorded Koszul/GRR calculation gives

```
ch(F) = 1 + z0 - z1 - z0 z1,
ch3(F) = z0-z1,  ch6(F)=-z0 z1,
z0²=z1²=0,  degree(z0 z1)=64.
```

Consequently the exact Newton relations (c1=c2=c4=c5=0) imply
```
c3(F)=2(z0-z1),    c3(F)²=-8 z0 z1,   degree c3(F)²=-512;
c6(F)=116 z0 z1,   degree c6(F)=7424;
2c6(F)+29c3(F)²=0,       chi(F,F)=0.
```

In particular this rank-one PERFECT object cannot be replaced by a rank-one **locally free** sheaf having the same Chern classes: a line bundle has c3=0. Nor does chi(F,F)=0 establish unobstructedness.

## Exact nonsplit Weil-period tangent

Let `u_k=dz_{x_k}`, `v_k=dz_{y_k}`, `U_k=dbar(z_{x_k})`, `V_k=dbar(z_{y_k})`. The K-action has eigenvalues `+i` on `u_k,V_k` and `-i` on `v_k,U_k`. Consider the genuinely **mixed** first-order holomorphic subspace

```
u_1(t) = u_1 + t V_2,
v_2(t) = v_2 + t U_1,
all other u_k(t),v_k(t) unchanged.
```

The cross terms of the product Riemann form cancel: the two changes are symmetric in the matched polarization-weight-one coordinates x1 and y2. Thus the deformed H^(1,0) remains isotropic for the fixed rational polarization, and positivity is open for |t| sufficiently small. The K eigenvalues also agree termwise. This supplies a polarized Weil-type infinitesimal deformation through the split CM point, valid as well with the third negative Hermitian diagonal entry weighted by 3; it does not assume that the CM graph subvarieties deform.

For Gaussian integers a,b, the normalized (1,1) cohomology form of `{a x_k-b y_k=0}` is the exterior form

```
D_{a,b;k} = (a u_k-b v_k) ∧ (conj(a) U_k-conj(b) V_k).
```

Its actual Chern class differs by one fixed nonzero normalization factor, common to Z0 and Z1. Both z0 and z1 have normalized product `D_{a,b;1} D_{a,b;2} D_{a,b;3}`, with `(a,b)=(1,1)` and `(2-i,2+i)` respectively.

## Hand-checkable nonzero (2,4) coefficient

Use the ordered six-form monomial

```
M = u2 ∧ u3 ∧ U1 ∧ U2 ∧ U3 ∧ V2.
```

In the new Hodge basis, `u1=u1(t)-t V2+O(t²)` and `v2=v2(t)-t U1+O(t²)`. Therefore the first graph divisor changes by
```
delta D_{a,b;1} = (-a V2) ∧ (conj(a) U1-conj(b) V1),
```
and the second by
```
delta D_{a,b;2} = (+b U1) ∧ (conj(a) U2-conj(b) V2).
```

To produce M, the first variation must use `V2 ∧ U1`, while the remaining two factors choose `u2 ∧ U2` and `u3 ∧ U3`. The second variation cannot contribute M: its `U1` duplicates the first divisor's required `U1`, or else the first divisor contributes the prohibited `V1`. Sorting the six wedge factors into the displayed order contributes a minus sign. Thus the exact normalized coefficient is

```
[M] delta(z_{a,b})^(2,4) = - (a conj(a))^3 = -Norm(a)^3.
```

With `Norm(1)=1` and `Norm(2-i)=5` the coefficient for the **raw derived source** is

```
[M] delta(ch3(F))^(2,4) = -1-(-125) = 124 ≠ 0.
```

The same 124 was recovered independently by full signed exterior-basis enumeration (32 nonzero resulting (2,4) coefficients) and is the exact integer Lean certificate `cmTwoPlusIGraphDerivedIdealPair_mixedHodgeLeak_exact`. A fixed nonzero Chern-form normalization cannot remove this failure of Hodge type.

## Consequence and changed route

A relative holomorphic perfect complex extending F across this named K-compatible nonsplit tangent would have locally constant rational Betti Chern character of type (3,3). The explicit 124 first-order component contradicts that necessary condition. Hence **the raw F cannot extend as a perfect complex with its fixed Chern character in this direction**, independently of the earlier 576-versus-495 raw Ext2 dimension test. Under the standard Atiyah/Kodaira-Spencer-to-Hodge-variation compatibility, the obstruction `At(F) ⌟ κ` is nonzero for this tangent. This is a no-go for THIS unprojected derived source and THIS tangent, not a counterexample to the Hodge conjecture and not a proof that all conceivable nonsplit sources are obstructed.

The live repo already has the genuine CM isogeny projector `cmWeilSixfoldTwoOperatorProjector`, which kills non-Weil K-weight sectors while retaining the exceptional pure Weil component. Its projected K0 *virtual* class has zero first-order Hodge leakage on Weil-type deformations. The new exact research objective is to construct a genuinely coupled holomorphic coherent/perfect object with **that projected class**, and check its actual Atiyah obstruction; do not attempt to deform the raw F unchanged or infer unobstructedness from chi(F,F)=0.

**Classification:** formal integer and Chern-ring identities proved in Lean (subject to revision-matched CI); nonzero exterior coefficient directly derived and independently enumerated; polarized deformation and derived-category Atiyah compatibility remain mathematical, not Lean-instantiated. Universal arbitrary-X algebraicity is not inferred.
