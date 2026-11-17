<!-- ======================================================================
<!-- CHRONOLOGICAL LABEL -- #0835 / 1132
<!--    Path         : branches/sol_physical-phase-crossing-implementation/docs/GST_V2_HANDWRITTEN_X6_CYCLOTOMIC_CHORD.md
<!--    Ref          : origin/sol/physical-phase-crossing-implementation
<!--    First-commit : 2026-08-17 05:53:45 +0530  (c28c9a1)
<!--    Last-commit  : 2026-08-17 05:53:45 +0530  (c28c9a1)
<!--    Total commits: 1
<!-- ======================================================================
<!-- GIT HISTORY (chronological, oldest first)
<!-- ======================================================================
<!-- [01/1] 2026-08-17 05:53:45 +0530  c28c9a1  (ker07-dev)
<!--        Record x-6 cyclotomic V2 chord and six-space Navigation factorization
<!-- ====================================================================== -->

# GST V2 handwritten `x-6` cyclotomic chord

Status: exact algebraic discoveries + explicitly marked interpretation.  Not yet transplanted into the monolithic Lean proof.

## 1. Exact six-sector pair cycle

For `s>=1`, let

```text
N = 3^s
B = 2^N
D = 3^(s+1)
```

At ternary row `s+1`, the six half-phase sectors `B^j`, `j=0,...,5`, have exact two-x2 mass pairs

```text
j=0  (0,0)
j=1  (1,3)
j=2  (2,4)
j=3  (5,5)
j=4  (4,2)
j=5  (3,1)
```

independent of `s`.

The two physically important x4 phase sectors are

```text
j=2 : (2,4) = CREATE -> DESTROY = hidden phase-one BIG2
j=4 : (4,2) = DESTROY -> CREATE = NULL SURVIVE
```

and the binary midpoint is

```text
j=3 : (5,5) = SURVIVE -> SURVIVE = GST+ SURVIVE.
```

## 2. The handwritten coordinates

Define

```text
x_j = m1_j + m2_j
z_j = m2_j - m1_j.
```

Then

```text
j : 0      1      2       3       4       5
x : 0      4      6      10       6       4
z : 0      2      2       0      -2      -2
```

Thus `x=6` occurs at exactly `j=2,4`, and `|z|=2` on both.

The symmetric product coordinate is also identical there:

```text
m1*m2 = 8
```

for both `(2,4)` and `(4,2)`.

Hence the handwritten kernel `z/(x-6)` has a precise experimental interpretation:

- denominator: select the two nontrivial physical phase orientations;
- sign of `z`: distinguish hidden vs exposed orientation;
- absolute `|z|`: forget orientation and retain the same BIG2 magnitude;
- symmetric product `8`: another orientation-free packet coordinate.

## 3. Sixth-root Fourier/cyclotomic encoding

Put

```text
zeta_j = exp(i*pi*j/3).
```

The six exact coordinates admit the closed forms

```text
z_j = (4/sqrt(3))*sin(pi*j/3)

x_j = 5 - 4*cos(pi*j/3) - (-1)^j.
```

Equivalently, using `zeta^6=1`,

```text
zeta*(x-6)
 = -(zeta^2 + zeta + 1)*(zeta^2 - zeta + 2).
```

The first factor is the third cyclotomic polynomial

```text
Phi_3(zeta) = zeta^2 + zeta + 1.
```

Therefore the `x-6` singular fibre is exactly the pair of nontrivial cube-root sectors `j=2,4` inside the six half-phase universe.

This is an exact finite-cycle statement.  The use of complex roots is only a Fourier/character encoding of the finite cyclic phase group; no complex-analytic assumption enters the number-theory proof.

## 4. Physical meaning of the six sectors

The binary half-phase is

```text
B_s = 2^(3^s).
```

The physical x4 phase multiplier is

```text
A_s = B_s^2 = 4^(3^s).
```

Thus:

- one `B_s` step moves one half-phase;
- two `B_s` steps move one physical x4 phase;
- six `B_s` steps close the finite prefix cycle and advance one next-level Navigation block.

At the forced row, multiplication by `B_s` produces the exact sector cycle above.

## 5. Six-space affine factorization of Navigation

Work at the cut after the forced low prefix, of length `s+2` ternary digits.  Let the six universal low residues be

```text
r0 = 1
r1 = D-1
r2 = D+1
r3 = 3D-1
r4 = 2D+1
r5 = 2D-1
r6 = 1
```

where residues are interpreted modulo `3D=3^(s+2)`.

If sector `j` has high tail `Y_j`, then exact multiplication by the half-phase gives

```text
Y_(j+1) = B_s*Y_j + mu_(s,j)
```

with

```text
mu_(s,j) = (B_s*r_j-r_(j+1))/(3D).
```

Writing

```text
h_s=(B_s+1)/D,
```

the offsets are

```text
mu0 = (h_s-1)/3
mu1 = ((D-1)h_s-2)/3
mu2 = ((D+1)h_s-4)/3
mu3 = (3D h_s-h_s-5)/3
mu4 = (2D h_s+h_s-4)/3
mu5 = (2D h_s-h_s-2)/3.
```

These are integers because of the exact half-phase congruences.

The composition of all six maps is

```text
Y_6 = c_(s+1) + A_(s+1)*Y_0.
```

Indeed

```text
B_s^6 = 4^(3^(s+1)) = A_(s+1)
```

and the composed affine constant is exactly `c_(s+1)`.

Therefore if

```text
Y_0 = Q_(s+1)(n),
```

then

```text
Y_6 = Q_(s+1)(n+1).
```

**Interpretation:** the six half-phase subspaces give an exact sixth-root factorization of the Navigation successor map.

This is a direct arithmetic model for the handwritten `U * N * Omega` intuition:

- `U` = half-phase affine transport;
- six `U` sectors = complete binary/ternary bridge cycle;
- `N` = canonical Navigation successor after the six-sector product;
- the emitted local CREATE/DESTROY/SURVIVE states form the information wave.

## 6. Exact 3-adic inverse-system extension

At deeper ternary depth the finite six-cycle does not remain a six-cycle.  This is important.

For modulus `3^(s+2+q)`, the half-phase generator `B_s` has exact order

```text
6*3^q.
```

The physical phase generator `A_s=B_s^2` has exact order

```text
3^(q+1).
```

Thus the three physical spaces at the first lifted row refine as

```text
3 -> 9 -> 27 -> 81 -> ...
```

and the binary-oriented half-phase universe refines as

```text
6 -> 18 -> 54 -> 162 -> ...
```

This is the exact inverse-limit/nested-subspace geometry.  It also explains why promoting the first six-cycle to a global fixed six-state transport is false.

The finite first quotient is the six-sector cyclotomic picture above; deeper rows are Hensel/3-adic lifts of that phase group.

## 7. New relation to the final seam

The hard prefix-one parent is the `j=2` sector.  At the forced row it lies on

```text
x=6, z=+2  -> hidden CREATE->DESTROY.
```

The phase-two sector is `j=4`:

```text
x=6, z=-2  -> NULL SURVIVE.
```

The midpoint `j=3` is

```text
x=10, z=0 -> GST+ SURVIVE.
```

So the final crossing can now be viewed as a **lift problem**:

> the first cyclotomic quotient already contains the hidden/exposed conjugate BIG2 orientations; prove that the canonical natural-origin Hensel lift cannot remain forever on the hidden orientation while avoiding every physical SURVIVE lift.

This is equivalent in spirit to the existing final contract `bad -> infinite origin support`, but the new cyclotomic coordinate supplies an explicit first quotient and an exact half-phase lift operator.

## 8. Hard warning

Do not claim from this document that `B_s` transports an arbitrary deep-row GST cell by the same six-state permutation.  At depth `q>0` the order is `6*3^q`, not six.  The six-state table is the exact first quotient/boundary condition; deeper levels must be treated through the inverse-system lift.
