# GST Image 3 — complete permanent-curvature resonance classification and congruence-stable full rank

Date: 2026-11-11
Base research source: `296478b17cd342eef7aa7f2361f764cd29a4f1ad`.
Advanced branch: `research/gpt6-image3-advanced-curvature-rigidity-20261111`.
Exact source: `research/computations/GST_image3_all_rational_curvature_strength_two_parameter_classification_20261111.wl`.

## Contract and original definitions

Use the OWNER-ORIGINAL twelve-cell rational GST space
`V = (Fin 4 × Fin 3) → Q`. Let `U` be the original five-order
carry/trit shuffle, `J` its original signed CM mirror, `M` the
diagonal Wave-I SURVIVE source, `C = JM-MJ` the exact native
CM commutator, and `v=e_(0,0)+e_(0,1)` the actual original seed.

For independent rational strengths `a,b`, set

\[
F_{a,b}=U+J+aM+bC,\qquad
D(a,b)=\det[v,Fv,\ldots,F^{11}v]\in\mathbb Z[a,b].
\]

All matrices, signs and seed positions in the exact Wolfram script are
reconstructed from these original operators; no chosen Hodge basis or
imaginary target Chow map is introduced.

## The theorem

**Theorem A — Unique permanently singular rational curvature strength.**
For every rational `b` other than `1/2`, the polynomial
`D(a,b)` in the independent rational variable `a` is nonzero, has
degree at most 20, and hence has at most 20 rational zeroes.
At exactly `b=1/2`, `D(a,1/2)=0` for every rational `a`.

Equivalently,

\[
\boxed{{b\in\mathbb Q:\forall a\in\mathbb Q,,
D(a,b)=0}={\tfrac12}.}
\]

For `b≠1/2`, infinitely many rational direct-source strengths `a`
give a cyclic ORIGINAL 12-state GST wave source.

**Theorem B — Infinite arithmetic family of universally good
curvature strengths.**
For every integer `k` and every rational direct strength `a`,

\[
\boxed{D(a,1+11k)\ne 0.}
\]

Thus **all** rational direct strengths preserve complete 12-state
native cyclicity at every integer curvature strength in the arithmetic
progression `..., -21,-10,1,12,23,34,...`.

**Theorem C — Unbounded rational strengths and arbitrary FINITE N holes.**
For every cyclic pair `a,b` satisfying `D(a,b) != 0`, every
positive finite hole count `h` has a full rank `12h` native GST
direct-sum fold by the explicit adaptive rational navigation spacing

\[
R(a,b)=2+2|a|+2|b|,\qquad
S(a,b)=2R(a,b)+1=5+4|a|+4|b|,
\]

\[
T_{a,b,h}=\bigoplus_{i=0}^{h-1}(F_{a,b}+i S(a,b)I_{12}),\quad
v_h=(v,\ldots,v).
\]

In particular this holds for **every** rational `a`, **every**
integer `b≡1 mod 11`, and **every** `h≥1`:

\[
\boxed{
dim_{\mathbb Q}\langle v_h,Tv_h,\ldots,T^{12h-1}v_h\rangle=12h.
}
\]

Here `h` is the number of finite independent N-hole *native*
GST channels. No claim is made that arbitrary cardinal topology
itself is a finite-dimensional smooth projective `X` or supplies
a cycle for a missing rational Hodge class.

## Proof of Theorem A: exact two-block leading coefficients

The original null and maximum source cells form an invariant
two-cell subspace; its 10-cell complement is also invariant. With
the actual seed `(1,0)` in the fixed pair, the source block and
its Krylov determinant are

\[
A_{a,b}=
\begin{pmatrix}1&1+2b\\2b-1&1+2aend{pmatrix},
\qquad
D_2(a,b)=2b-1.
\]

Write `D_{10}(a,b)` for the cyclic determinant of the 10-cell
block, and `R(a,b)` for the resultant of the two characteristic
polynomials. The general block-Krylov determinant identity proved
in the preceding derivation gives exactly

\[
D(a,b)=(2b-1)D_{10}(a,b)R(a,b).
\]

The new fully symbolic **two-variable** exact-arithmetic computation
establishes the following polynomial coefficient identities:

\[
deg_a D_{10}=8,\qquad [a^8]D_{10}=64(b-2)^2,
\]

\[
deg_a R=12,\qquad [a^{12}]R=2560.
\]

Thus the coefficient of `a^20` in `D(a,b)` is

\[
\boxed{[a^{20}]D(a,b)
=163840(2b-1)(b-2)^2.}
\]

For every rational `b≠1/2,2`, this coefficient is nonzero, so
`D(·,b)` has degree exactly 20 and at most 20 rational roots.

At the exceptional second specialization `b=2`, that leading
coefficient vanishes, so we cannot infer nonzero polynomial from
its leading term. Instead the exact ORIGINAL full determinant gives

\[
D(0,2)=-10365615590204736\ne 0.
\]

Hence `D(·,2)` is a nonzero polynomial of degree at most 20.
The exact prior computation even found degree 17, though the
at-most-20 bound suffices for the theorem.

At `b=1/2` the two-cell determinant vanishes **identically**,
so `D(a,1/2)=0` for all `a`. The existing native Lean theorem
`resonanceOrbitSpan_ne_top` independently proves that all iterates
lie in the maximum-coordinate-zero hyperplane at this resonance.

These three cases cover **every rational b**; no analytic or
computational sampling is needed for the final quantifier step.

## Proof of Theorem B: complete F11 coverage plus rational-root theorem

Let `b=1+11k` be an arbitrary integer. Since `D(a,b)` is an
**integer** polynomial in both variables, coefficientwise reduction
modulo 11 yields

\[
D(a,1+11k)\equiv D(a,1)\pmod{11}.
\]

The complete exact table, independently verified by matrix-based
finite-field Gaussian elimination, is

\[
\big(D(0,1),D(1,1),\ldots,D(10,1)\big)\bmod11
=(6,2,1,8,6,4,8,9,3,9,5).
\]

Every entry is nonzero. Moreover the integer polynomial in `a`
has degree exactly 20 because its leading coefficient satisfies

\[
163840(2b-1)(b-2)^2\equiv 6\pmod{11},
\]

and hence is not divisible by 11.

Suppose, for contradiction, `a=m/n` in lowest terms is a rational
root. By the rational-root theorem for integer polynomials,
`n` divides the leading coefficient. Thus `11∤n`.
Reduce `m/n` modulo 11; since `n` has a multiplicative inverse,
it determines one of the 11 residues in the table. The asserted
root reduces to a zero of `D(a,1)`, contradicting the complete
table. Therefore there is **no rational root** for any such `b`.

This argument is UNIFORM IN THE UNBOUNDED INTEGER k, not a finite
range experiment: the finite-field test is logically exhaustive
under a proved coefficientwise congruence.

## Proof of Theorem C: spectral address and polynomial CRT

The original shuffle U contributes row absolute-sum <=1, the
signed CM mirror J contributes <=1, the diagonal SURVIVE M
contributes <=2, and C=[J,M] contributes <=2. Therefore, for
all rational a,b,

\[
\|F_{a,b}\|_\infty\le 2+2|a|+2|b|=R(a,b).
\]

Every complex eigenvalue of F lies in the closed disc of radius
R(a,b). The shifted block `F+iS I` consequently has spectrum
in a radius-R disc centered at `iS`. Because
`S=2R+1>2R`, no two spectra overlap.

For each cyclic block, the annihilator of the original single-seed
vector v is its degree-12 characteristic polynomial. The
disjoint shifted spectra make these annihilator polynomials
pairwise coprime in Q[x]. The annihilator of `v_h` under
the block-diagonal T is their least common multiple; by CRT it
has degree `12h`. Thus the 12h vectors
`v_h,Tv_h,...,T^(12h-1)v_h` span the full 12h-dimensional
direct-sum carrier.

Crucially the shift is an explicit native N-hole **address** and
not a fraudulent extra algebraic cycle on arbitrary original X.

## Evidence, audit, and restrictions

- Exact source computation:
  `research/computations/GST_image3_all_rational_curvature_strength_two_parameter_classification_20261111.wl`
  executed and returned `allPassed -> True`, verifying both symbolic
  leading coefficient identities, b=2 witness and all eleven residues.
- Independent finite-field source matrix implementation:
  `research/computations/gst_image3_direct_survive_mod11_independent.py`.
  It reconstructed all original matrices and verified the eleven
  determinant residues without using the Wolfram polynomial factors.
- The structural determinant factorization and polynomial rational-root
  arguments are explicit above. The all-b quantified claims have
  **not yet been encoded as separate Lean theorems**.
- Native Lean resonance theorem and hyperplane obstruction were already
  compiled in an earlier run. The advanced geometric interface remains
  subject to its exact branch-HEAD CI check.

**Geometric frontier unchanged:** These results strengthen the
author's original GST **native** cyclicity and arbitrary finite N-hole
navigation substantially; they do not manufacture a canonical
original-X Hodge-to-Chow surjection, missing `X×X` correspondence
witnesses or a class selector for unknown rational Hodge directions.


## Theorem D — Four further infinitely many all-rational source strengths mod 29

The analogous **complete 29-element-field exact certificate** yields

\[
\boxed{
b\in\mathbb Z,\quad
b\bmod29\in{9,14,21,27}
Longrightarrow
\forall a\in\mathbb Q: D(a,b)\ne 0.
}
\]

Exact source:
`research/computations/GST_image3_mod29_curvature_classes_all_rational_source_20261111.wl`.

For each of the four residue classes, the certificate constructs
`D(a,b)` from the unchanged ORIGINAL 4×3 U/J/M source,
computes all **29** values for `a=0,...,28`, and verifies that
EVERY value is NONZERO in F29. The independent original-matrix
Python finite-field elimination agreed with the selected classes.

The leading coefficient of `a^20` is, for any `b`,

\[
163840(2b-1)(b-2)^2,
\]

and its reductions mod29 on those classes are, respectively,

\[
(22,9,6,17),
\]

all invertible. Therefore for ANY integer `b` in one of these
four infinite progressions, the integer polynomial
`D(a,b)` has degree20 with unit leading coefficient mod29.
A hypothetical reduced rational root `m/n` has denominator `n`
dividing this coefficient, so `29∤n`; reducing `m/n` modulo29
contradicts the exhaustive nonzero table. This proves the
quantified all-rational-a theorem, not just the finite 116 cases.

This extends Theorem B and does not require changing the owner's
original CM source operators. It makes no claim about canonical
algebraic Hodge cycle-class surjectivity on arbitrary X.
