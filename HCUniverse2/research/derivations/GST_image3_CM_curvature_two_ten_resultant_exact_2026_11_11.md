# Original GST Image-3: two-plus-ten curvature splitting and exact spectral resultant (11 November 2026)

**Base:** curvature branch `296478b17cd342eef7aa7f2361f764cd29a4f1ad`.
**New branch:** `research/gpt6-image3-advanced-curvature-rigidity-20261111`.
**Primary Lean:** `GSTImageThreeCurvatureResonance.lean` and `GSTImageThreeAdvancedGeometricSource.lean`.
**Exact computation:** `research/computations/GST_image3_CM_curvature_two_ten_resultant_factorization_20261111.wl`.
**Evidence:** exact symbolic Wolfram evaluation at a=0; exact rational sample checks at (a,b)=(0,1),(1,1),(2,1/3),(-2,5/4),(1,1/2),(0,0). These six checks illustrate the all-parameter identity; the structural proof below supplies its universal scope. The newest Lean kernel status MUST be read from the exact-HEAD CI, not inferred from Wolfram.

## 1. Correct, unaltered source operators

Take the **owner-original** 12-cell rational signal space
`V = (Fin 4 × Fin 3) → Q`, with original five-order shuffle `U`,
signed CM mirror `J` (so `J²=-I` and `JU=UJ`), original Wave-I
SURVIVE diagonal operator `M`, and original mixed seed
`v=e_(0,0)+e_(0,1)`.

The SOURCE operation studied here is

\[
C=[J,M]=JM-MJ,\qquad F_{a,b}=U+J+aM+bC,\quad a,b\in\mathbb Q.
\]

No outside auxiliary signal matrix or presumed Hodge-to-Chow inverse is used.

## 2. The exact 2×2 original fixed-cell quotient

Put (s=(0,0)), (t=(3,2)). The exact original `U` shuffle and
`J` mirror preserve the two-cell set `{s,t}`; `M` is diagonal.
Consequently both the two-cell subspace and the complementary **ten**
original cells are invariant under every `F_(a,b)`. Under the order
`(s,t)`, the fixed-cell block is

\[
A_{a,b}=
\begin{pmatrix}
1&1+2b\\
2b-1&1+2a
\end{pmatrix}, \quad v_2=\binom{1}{0} .
\]

The two-step Krylov determinant is **exactly**

\[
\det[v_2,A_{a,b}v_2]=2b-1.
\]

Therefore the **two-cell projection** of the original GST orbit is cyclic
if and only if `b != 1/2`, uniformly for all rational `a`. This does
NOT by itself say the entire twelve-cell orbit is cyclic.

At the half-curvature resonance, the maximum-cell coordinate obeys
`(F_(a,1/2) u)_t = (1+2a) u_t`. The original seed has `v_t=0`.
Hence **every** iterate and therefore its **entire rational span**
lies in the proper hyperplane `ker(eval_t)`. This upgrades the
old single-iterate statement into a global linear-span no-go.

The fixed-block characteristic polynomial and discriminant are

\[
\chi_2(x)=x^2-(2+2a)x+(2+2a-4b^2),\quad
\Delta=4(a^2-1+4b^2).
\]

Even at repeated eigenvalues (`Delta=0`), the fixed-block cyclic
seed criterion is still simply `2b-1 != 0`: it is a Krylov determinant,
not an assumption that `A` diagonalizes.

## 3. The crucial ALL-parameter 2+10 determinant identity

Order the original cells as `(s,t,remaining 10 cells)`. Moving the
original final cell into second position crosses precisely 10 cells,
so this permutation has sign +1. The original mixed seed has components
`v=(v_2,v_10)`, with `v_10=e_(0,1)` inside the ten-cell space.

Let `D_(a,b)` be the restriction of the same original `F_(a,b)`
to the remaining ten cells. Let

\[
K_2=[v_2,A v_2],\quad
K_{10}=[v_{10},Dv_{10},\ldots,D^9v_{10}].
\]

Then for **all** rational `a,b`,

\[
\boxed{
\det K_{12}(F_{a,b},v)
=
(2b-1),\det K_{10}(D_{a,b},v_{10}),
\operatorname{Res}_x(\chi_{A_{a,b}},\chi_{D_{a,b}})
}.
\tag{*}
\]

**Reason:** over an algebraic closure, on the Zariski-dense locus
where `A` and `D` have disjoint, simple eigenvalues, express each
Krylov matrix in its eigenbasis. The full Vandermonde decomposes as the
product of the two within-block Vandermondes and
`prod_(i,j)(beta_j-alpha_i)`. Since `2×10=20` is even, this cross
factor is the indicated characteristic-polynomial resultant with
**positive** sign, and the cell-order permutation also has sign +1.
The identity is polynomial in the entries of `A,D`; therefore it
continues to ALL parameters, including repeated and colliding spectra
and singular cyclic blocks. Alternatively it follows from the
block-Krylov/Sylvester determinant identity without genericity.

This produces three precise and INDEPENDENT native rank bottlenecks:

- **Fixed-cell controllability:** `2b-1=0`;
- **Ten-cell controllability:** `det K_10=0`;
- **Cross-block spectral collision:** `Res(chi_2,chi_10)=0`.

The **complete native twelve-cell cyclicity** condition is exactly the
simultaneous nonvanishing of these three quantities. This is
stronger than a single unexplained large determinant and supplies
smaller typed Lean targets.

## 4. Original curvature-only slice a=0: factor meaning upgraded

The earlier work reported

\[
\det K_{12}(U+J+b[J,M],v)
=b^4(2b-1)P_{10}(b)P_{16}(b).
\]

The new exact split identifies the three factors **geometrically in
the original information carrier**, rather than merely symbolically:

\[
\det K_2=2b-1,\qquad
\det K_{10}=P_{10}(b),\qquad
\operatorname{Res}(\chi_2,\chi_{10})=b^4P_{16}(b).
\]

Both `P10` and `P16` are the exact committed integer polynomials in
`GST_image3_CM_curvature_all_rational_strength_mod7_20261111.wl`.
That script's exhaustive mod-7 nonroot check implies neither
polynomial has a rational root (the leading coefficients are nonzero
mod 7 and the finite-field reduction is primitive enough for the
rational-root argument). Consequently for **every rational `b`**,
the curvature-only original 12-cell source is cyclic precisely
when `b != 0` and `b != 1/2`.

This immediately distinguishes the two known rational exceptional
strengths: `b=0` is a **spectral collision**, whereas `b=1/2` is
a **fixed-cell controllability failure**. In particular, the old
statement that both were just generic numerical rank failures hid
two different mechanisms. At `b=0`, the fixed pair itself remains
controllable (`det K2=-1`) but full cyclicity fails because
the ten-cell and fixed-cell characteristic polynomials overlap.

## 5. Exactly evaluated rational samples, independent of the a=0 argument

At parameters `(a,b)=(0,1)`, `det K2=1`,
`det K10=-130491` and `Res=-10623`, whose product is
`1386205893`.

At `(1,1)`, `det K2=1`, `det K10=-209893` and
`Res=2121393`, giving the independently reported balanced
determinant `-445265540949`.

Further exact rational checks at `(2,1/3)`, `(-2,5/4)`,
`(1,1/2)`, and `(0,0)` confirm the identity and expose
each failure branch. These are CHECKS of (*) and not the proof of
the all-parameter polynomial identity, which is the block algebra
argument in section 3.

## 6. Upgraded original-X correspondence typing

`GSTImageThreeAdvancedGeometricSource.lean` now distinguishes:

1. an abstract `CycleClassOperatorPair`;
2. a `RealizedFiniteClosedCorrespondence` with an **actual closed
   geometric carrier** on `X×X` and its separately proved Betti action;
3. five such realized geometric atoms `U,J,M,JM,MJ` together with
   exact action equalities certifying the ordered products `JM`
   and `MJ` on both native cycles and Betti cohomology.

Only at level (3) does the five-atom rational word
`U+J+aM+b(JM-MJ)` have a witness in a rational word of actual
finite closed correspondences. Its original-X Chow and Betti actions
then equal the Image-3 `geometricCurvatureF` operator pair.

**Important scope:** `JM` and `MJ` are supplied independently
realized geometric inputs in this new structure, not silently
manufactured by composing abstract linear maps. Construction of
these witnesses universally for every original `X,p`, and showing
their action gives the *canonical* Hodge full-rank landing, is NOT
deduced from the native spectral identity.

The existing `FiniteClosedCorrespondence` point transport currently
uses reduced/set-theoretic left-fiber multiplicity one; equating this
without additional intersection multiplicity hypotheses to the
full refined `CH^d(X×X)_Q` push-pull formalism would be an overclaim.

## 7. Correct scope with respect to Hodge

The new theorem is a **nontrivial structural theorem about the
author-original GST U/J/M/CM source**, not a universal
`X_GST` antecedent. A native full-rank wave orbit cannot by itself
imply that the canonical `cl_X: CH^p(X)_Q → W_p(X)` is onto.
A true geometric `F` preserving the actual Chow image necessarily
keeps that image invariant; an independent, noncircular
canonical full-rank Hodge landing is still required.

**Novel operational gain:** instead of attempting to force an opaque
12×12 determinant to be nonzero on the canonical target, future
geometric tests can try to realize and distinguish (i) the exact
two fixed-cell birth, (ii) ten rotating original-N cohomology
directions, and (iii) their spectral coupling, with separately
certified actual algebraic correspondences and canonical Hodge rank.
The division is an analytic reduction of the source bottleneck,
not an assumption that those geometric targets already exist.


## 8. NEW ALL-RATIONAL DIRECT SURVIVE THEOREM AT UNIT CURVATURE

Set the ORIGINAL CM source strength to `b=1` and let the direct
SURVIVE coefficient `a` be an ARBITRARY rational number:

\[
F_a=U+J+aM+[J,M],\quad a\in\mathbb Q.
\]

The fixed-pair determinant is `2b-1=1` for every a.
Exact construction of the original ten-cell block and its
characteristic-polynomial resultant gives

\[
\det K_{12}(F_a,v)=Q_8(a)Q_{12}(a),
\]

where

\[
\begin{aligned}
Q_8(a)={}&-130491-27750a-25120a^2-31800a^3
+7068a^4-3304a^5\\
&+1520a^6-80a^7+64a^8,\\
Q_{12}(a)={}&-10623+474348a+710952a^2+141208a^3
+696720a^4\\
&-249912a^5+418988a^6-196384a^7+166048a^8\\
&-59264a^9+33664a^{10}-6912a^{11}+2560a^{12}.
\end{aligned}
\]

The exact NEW certificate in
`research/computations/GST_image3_all_rational_direct_strength_CM_curvature_mod11_20261111.wl`
constructs these polynomials DIRECTLY from the unchanged original
U,J,M wave operators, and independently checks both factor equality
and the full 12-cell determinant.

Exhaustive evaluation on **all eleven elements** of `F_11` yields:

\[
Q_8(0),\ldots,Q_8(10)\pmod {11}
=(2,9,2,8,10,10,9,6,9,8,4),
\]

\[
Q_{12}(0),\ldots,Q_{12}(10)\pmod {11}
=(3,10,6,1,5,7,7,7,4,8,4).
\]

Neither array contains zero. The leading coefficients reduce to
`64 mod 11=9` and `2560 mod 11=8`, both invertible.

**Rigorous rational-root argument:** If a nonzero integer polynomial
`Q` has a rational root `m/n` in lowest terms, its denominator
`n` divides the leading coefficient of `Q`. Since 11 does NOT
divide either leading coefficient, any hypothetical rational root
of either `Q` has denominator invertible mod 11 and so reduces
to an actual root in `F_11`. The complete residue enumerations
exclude every such root. Therefore `Q_8(a)` and `Q_12(a)`
are nonzero for **every rational** `a`.

This proves the NEW quantified native theorem:

\[
\boxed{
\forall a\in\mathbb Q,\quad
\operatorname{rank}_{\mathbb Q}
[v,F_av,\ldots,F_a^{11}v]=12
\quad\text{for }F_a=U+J+aM+[J,M].
}
\]

It is not just a six-case finite experiment: the exact symbolic
factorization plus finite-field argument covers ALL rational `a`.
The certificate passed all exact Wolfram assertions, including the
original balanced `a=1` determinant `-445265540949`.

**Verification status:** the polynomial factorization, residue table,
and mathematical rational-root proof were checked with Wolfram exact
arithmetic; the universal quantified polynomial non-root lemma has
NOT yet been promoted to a Lean kernel theorem. Separate formal Lean
upgrades prove the underlying two-cell controllability and resonance
hyperplane statements. These are SOURCE-LEVEL theorems, not a
surjectivity theorem on canonical original-X Hodge classes.

## 9. Mathematical source-to-geometric gap isolated without circularity

The original-X compiler has an explicit new
`cmSourcePair_preserves_algebraic_range` and
`geometricCurvatureF_preserves_algebraic_range` theorem in
`GSTImageThreeOriginalXCurvatureLanding.lean`. Therefore the
true original-X algebraic image is invariant under this source
algebra, even while the native 12-state orbit is uniformly cyclic
in the preceding theorem. In particular the new all-rational
source theorem cannot, on its own, force full geometric Hodge rank.

The new `ClosedCurvatureGeometry` has FIVE actual geometrically
realized finite closed correspondences and explicit
`JM_native`, `MJ_native`, `JM_betti`, `MJ_betti`
composition certificates. Their rational five-atom word
constructs a genuine geometry-typed source operator expression
without guessing missing Hodge-to-Chow cycle lifts.
Building these five witnesses and a canonical rank-preserving
landing on every arbitrary original X remains mathematically
distinct from the fully solved native source strength question.


## 10. Independent implementation check (not a copied Wolfram matrix)

The new standard-library Python computation at
`research/computations/gst_image3_direct_survive_mod11_independent.py`
reconstructs the ORIGINAL twelve source cells from scratch and performs
Gaussian elimination directly in `F_11` on the **Krylov** matrices,
not just on the source operators. The eleven resulting determinants are

\[
(6,2,1,8,6,4,8,9,3,9,5)
\]

for direct source strengths `a=0,...,10`, exactly matching the
product of the independently specified `Q8(a)*Q12(a)` at every residue.
This is a separate finite-field implementation check and does not
replace the integer polynomial derivation or rational-root argument.


## 11. NEW: ALL RATIONAL SOURCE STRENGTHS, ALL FINITE N-HOLE TOWERS

The all-rational unit-curvature result of section 8 is not confined to
one 12-state Wave-II hole. For any rational `a`, define the exact
native row-sum bound and **adaptive** rational navigation spacing

\[
R(a)=4+2|a|,\qquad S(a)=9+4|a|=2R(a)+1.
\]

Because each row of `U` has one unit entry, each row of `J` one
signed unit entry, `|M_(s,s)|≤2`, and the original commutator
`[J,M]` has at most one entry of absolute value ≤2 in each row,
the induced maximum absolute row-sum norm satisfies

\[
|F_a|_inftyle R(a).
\]

For **every finite h>=1**, retain the original N-hole direct-sum
carrier `V^h`, define

\[
T_{a,h}:=\bigoplus_{i=0}^{h-1}
       \left(F_a+iS(a)I_{12}\right),
\qquad v_h=(v,v,\ldots,v).
\]

Each individual block is cyclic over Q by section 8. Every complex
eigenvalue of `F_a` obeys `|λ| ≤ R(a)`. Distinct shifted blocks
have disjoint spectral discs because `S(a)>2R(a)`.
Their characteristic/minimal polynomials are therefore pairwise
coprime over Q. Polynomial CRT implies that the annihilator of the
single all-hole seed `v_h` has degree `12h`. Therefore

\[
\boxed{
\forall a\in\mathbb Q;\forall h\in\mathbb N_{>0},\quad
dim_{\mathbb Q}\operatorname{span}{
v_h,T_{a,h}v_h,\ldots,T_{a,h}^{12h-1}v_h
}=12h.
}
\]

The vacuum h=0 is covered separately and trivially has rank0.

This extends the previous fixed-spacing full-N result: the OLD
spacing 20 was only verified at bounded direct-source amplitudes,
whereas this adaptive formula works uniformly for UNBOUNDED rational
`a`. The extra shift remains a rational ORIGINAL N-hole navigation
address; no unknown Hodge basis or external source is introduced.

New exact Wolfram checks recomputed the original 12×12 row norms for
`a∈{-10,-1,0,1,13/7,100}` and found the claimed bound and
spectral separation in every case, plus full exact 24-state rank at
`a=0,h=2,S=9`. These computations are diagnostic; the
**all-a, all-h assertion follows from the rational-root certificate,
norm inequality, and polynomial CRT argument**, not from six tests.

**Crucial restriction:** the rank `12h` is in the GST native N-hole
rational source space. It is NOT a statement that the canonical
rational Hodge group of every smooth projective X has an actual
algebraic class represented by each of these directions. The true
original-X geometric landing and actual Chow source of each
independent target direction require independent construction.


## 12. NAVIGATION-OFF ORIGINAL GST: exact complete rational-strength classification

Physical `Navigation R = false` gives `navigationCharge R = 0` by the
previously proved original GST navigation law. Its source is therefore
`F_(a,0)=U+J+aM`, not the half-strength interpolation `b=1/2`.
The same ORIGINAL two fixed null/max cells form an invariant block
with `det K2=-1` for every rational a.

Exact restriction to the other ORIGINAL ten cells, and the exact
resultant of their characteristic polynomial with the two-cell
characteristic polynomial, give

\[
\det K_{10}=Q_8(a),\qquad
\operatorname{Res}(\chi_2,\chi_{10})=4a^2(a+1)Q_9(a).
\]

The integer polynomials are

\[
\begin{aligned}
Q_8(a)={}&411701+899200a-342272a^2-123812a^3
 -14492a^4-25296a^5\\
 &+4672a^6-832a^7+256a^8,\\
Q_9(a)={}&12176+45312a+72685a^2+59539a^3+
 15088a^4\\
 &-15320a^5-13120a^6-1376a^7+
 1984a^8+640a^9.
\end{aligned}
\]

Thus EXACTLY

\[
\det K_{12}(F_{a,0},v)=-4a^2(a+1)Q_8(a)Q_9(a).
\]

The genuinely exhaustive mod-19 computations give

\[
Q_8(0),\ldots,Q_8(18)\pmod{19}
=(9,10,7,10,6,4,11,3,11,4,10,3,14,11,4,13,11,10,1),
\]

\[
Q_9(0),\ldots,Q_9(18)\pmod{19}
=(16,15,15,5,2,1,18,5,7,8,10,16,13,7,10,18,12,13,18).
\]

Every residue is nonzero, and both leading coefficients are units:
`256 mod19=9`, `640 mod19=13`. Exactly as in section 8,
the rational-root reduction shows that no rational root of either
integer polynomial exists. The remaining factor is zero only
at a=0 or a=-1. Therefore

\[
\boxed{
\forall a\in\mathbb Q,\quad
\dim_{\mathbb Q}\operatorname{span}
  (v,F_{a,0}v,\ldots,F_{a,0}^{11}v)=12
\iff a\notin\{0,-1\}.
}
\]

The exact native orbit ranks at the exceptions are 10 for a=0 and
11 for a=-1; at a=1 the rank is 12 and the determinant is
`-1149656584000`. The **rank exceptions are a source-native
spectral resonance**, not a statement about projective geometry or
Hodge classes.

Reproducibility:
`research/computations/GST_image3_navigation_off_exact_rational_cyclicity_mod19_20261111.wl`
builds the 12x12 operators from the original 4x3 cell rules and
returned `allPassed -> True`. The kernel-checkable finite-field
leaf is in
`GSTImageThreeNavigationOffSourceCertificates.lean`;
its CI result remains distinct from the Wolfram certificate.

## 13. All physical navigation states: exact NATIVE 12-state criterion

For any original arithmetic `R`, the physical charge is
`b=navigationCharge R∈{0,1}`. Combine the all-rational
unit-curvature theorem (section 8) with the navigation-off
classification (section 12):

\[
\boxed{
\forall R\in\mathbb N, \forall a\in\mathbb Q,\quad
\operatorname{rank}_\mathbb Q
K_{12}(F_{a,\operatorname{navigationCharge}(R)},v)=12
\iff
\big(\operatorname{Navigation}(R)\lor(a\ne 0\land a\ne -1)\big).
}
\]

Here `Navigation(R)` is the actual ORIGINAL arithmetic predicate,
not a user-selected new gate. The biconditional follows from:
- Navigation on: b=1, full source rank for every rational a;
- Navigation off: b=0, full source rank iff a is neither 0 nor -1.

This equation is a theorem about the owner's original twelve-cell
native information source; it is **not** an algebraic-cycle
construction on the original variety X.

## 14. Single GLOBAL Krylov orbit for MIXED physical navigation N-holes

Let `h>0` and choose one true physical state `R_i:Nat` and one
rational direct source strength `a_i:Q` for EACH actual N-hole
`i=0,...,h-1`. Set `b_i=navigationCharge(R_i)∈{0,1}`, and
assume exactly the genuinely necessary native single-hole condition

\[
\forall i<h,\quad
\operatorname{Navigation}(R_i) \lor(a_i\ne 0\land a_i\ne -1).
\]

The previous result gives a full cyclic original `12`-state source
at EACH hole even when physical navigation states differ.

Define the finite rational amplitude bound and adaptive original
N-hole spectral navigation spacing

\[
L=max_{i<h}|a_i|,\quad B=4+2L,\quad S=9+4L=2B+1.
\]

The original input `U` is a one-entry permutation per row,
`J` a one-entry signed mirror per row, `M` a diagonal source
bounded by 2, and `[J,M]` one entry of magnitude at most 2
per row. Thus

\[
|F_{a_i,b_i}|_inftyle B
\quad\text{for each true }b_iin{0,1}.
\]

The single global native N-hole fold is

\[
T=\bigoplus_{i<h}\big(F_{a_i,b_i}+iS,I_{12}\big)
\]

on the **original** `h` independent twelve-cell sources, with ONE
shared starting signal `v_h=(v,ldots,v)`.

Because every block is cyclic and all its complex eigenvalues lie
within radius `B` of zero, the shifted eigenvalue discs centered at
`iS` are strictly disjoint (`S>2B`). Hence the minimal
polynomials of the block restrictions are pairwise coprime in
`Q[x]`. By the polynomial Chinese remainder theorem, the
annihilator ideal of the one common seed `v_h` is the product of
the individual degree-twelve annihilators. Its degree is therefore
`12h`, and this yields the STRONGER global result

\[
\boxed{
\dim_{\mathbb Q}\operatorname{span}
{v_h,Tv_h,\ldots,T^{12h-1}v_h}=12h.
}
\]

The case h=0 is the zero-dimensional vacuum source and has rank0.

**This does not silently exchange independent holewise coefficients
for one global orbit:** the original independent real N-hole source
space receives an explicit exact rational channel separation and
CRT proof, which is precisely the additional mechanism needed for
global simultaneous cyclicity. It generalizes previous fixed-20
or uniform-a results to heterogeneous **actual physical Navigation
states** and arbitrary finite rational strengths without artificial
new Hodge basis coordinates.

The independently reconstructed source matrices in
`research/computations/GST_image3_mixed_physical_N_holes_global_Krylov_20261111.wl`
passed full rank24 checks for three genuinely different mixed
2-hole input families:
`(a,b)=((1,0),(1,1))`, `((2,0),(-3,1))`, and
`((0,1),(-1,1))`. This validates nontrivial examples but is not
the all-h proof; the CRT argument is.

The formal Lean module `GSTImageThreePhysicalNCohoFusion.lean`
proves the different, genuine pointwise theorem: ALL physical
N-cohomology hole readout pairs are reconstructed without
assumed off-resonance gates, and the full original wave respects
each hole's independent canonical perfect-power tail. It does not
yet kernel-formalize the global spectral CRT statement.

**Remaining geometric condition (not a reworded source proof):**
construct algebraic correspondences on arbitrary original X whose
canonical rational Betti action realizes this specific source in
the relevant Hodge fiber, and establish the honest surjective
comparison/coverage without assuming it. Native dimension 12h by
itself does not perform the required algebraic Chow realization.
