# Transport to every Weil period and extraction on the original fourfold

Base checkpoint: `dd274dd5b0c245435bbd637ee6f04c95ccfed5f6` on
`research/gpt6-native-point-primitive-span-20261017`.
This continues the constructed smooth secant seed. It does not start a
different source family or change the locked all-varieties target.

## Result, mathematical inputs, and formalization level

The argument below establishes the following geometric conclusions using
the explicitly identified complex-geometric theorems and comparisons.

1. For any imaginary quadratic field K, every compatible period of a
   hyperbolic K-Weil sixfold has algebraic rational Weil plane, including
   product periods and periods with extra endomorphisms.
2. For every original K-Weil abelian fourfold A of signature (2,2), its
   rational Weil plane is represented by genuine codimension-two cycles
   on A. No discriminant-one hypothesis on A is needed.
3. When the rational middle Hodge space is Q theta_A^2 plus that plane,
   these cycles give a representative of every prescribed middle Hodge
   class on A. This includes the very general simple fourfold in the
   question. We do not impose this three-dimensional description at
   arbitrary special fourfold periods.

This is a geometric manuscript proof, with a source-dependent application
of the precise semiregularity/deformation theorem below. It is not a
complete Lean realization of complex abelian varieties, Chow groups,
Atiyah classes or the canonical Betti map. The new Lean declarations
verify the obstruction comparison, the Baire argument, the isogeny
pullback logic and the explicit CM reconstruction. Their geometric
instantiations are the statements proved/applied here, not new axioms.

We do not assume the sixfold algebraicity conclusion T6 as a premise.
Instead, we expand its seed-to-period argument. The essential geometric
inputs are the exact Hochschild--Atiyah identity and its enhanced
Fourier--Mukai transport, the smooth projective germ deformation theorem,
Hilbert representability, proper analytic images, and canonical
Chow--Betti compatibility. Calling these inputs by name is part of the
proof's provenance, not a claim that they have been formalized in Lean.

## 1. Fixed source and character

Use [the direct smooth seed](2026-10-18-direct-smooth-secant-seed-and-character.md).
For K=Q(u0), u0^2=-d0 with d0 a positive integer, put

    u=420 u0,  d=176400 d0,  n=d+1,  r=8d.

There are disjoint Abel-curve orbit unions A_seed and Sigma on a smooth
nonhyperelliptic genus-three Jacobian X, with independent cyclic groups
G2 and G1 of order n. The ordinary coherent perfect sheaf E0 on
M=X x Xhat is the shifted dual of the specified fixed transform G of
I=I_Sigma external-product I_A_seed. Its normalized character is

\[
 \kappa_M=e^{-c_1(E_0)/r}\operatorname{ch}_{B}(E_0)
    =\sum_{j=0}^6 P_j(d)\theta_M^j
       -\alpha(\Omega_++\Omega_-),\qquad
 \alpha=\frac{d+1}{4d}>0,                         \tag{1}
\]

where the last summand has codimension three and

\[
 P_3=\frac{(d-1)(d+1)^2}{24d^2}.
\]

Every component of (1) remains Hodge on the full compatible marked
Weil domain: the polarization does, and each sixth determinant line has
type (3,3). This formula replaces a separate spin-stabilizer argument
for this particular character. It is not by itself a deformation of a
cycle or sheaf.

The actual homological form is
h(x,y)=e(x,uy)+u e(x,y), conjugate-linear in the first variable.
The seed form is hyperbolic of signature (3,3). Replacing u0 by 420 u0
scales that form by 420, preserving its isotropic subspaces. Thus the
large parameter in the smooth-seed construction loses no field or
hyperbolic period.

## 2. The entire invariant obstruction group

For a disjoint orbit Z of n Abel curves on X, the normal sequence and
the multiplication of canonical sections give

\[
 H^0(T_X)\simeq H^0(N_{C/X}),\qquad \dim=3.
\]

Here the canonical model of a nonhyperelliptic genus-three curve is a
plane quartic. Restriction of quadrics is an injection between the
six-dimensional spaces Sym^2 H^0(K_C) and H^0(K_C^2), hence an
isomorphism. Serre duality in the normal sequence proves the displayed
normal-section assertion.

The local resolution of the regular ideal (f,g) gives sheaf Hom(I_Z,I_Z)
=O_X, sheaf Ext^1(I_Z,I_Z)=N_Z/X and no higher sheaf Ext. Independently
translating the n disjoint components splits the local-to-global edge
sequence. This supplies an equivariant decomposition

\[
 \operatorname{Ext}^1(I_Z,I_Z)
   \simeq H^1(O_X)\oplus
       \bigoplus_{j=1}^n H^0(T_X).                 \tag{2}
\]

The finite group acts regularly on the n summands and trivially on
each three-dimensional factor. Its invariant Ext^1 therefore has
dimension six. Equivariant perfect Serre duality on X makes invariant
Ext^2 its dual, also dimension six; invariant Hom has dimension one.
Perfect Kunneth and averaging in the two independent groups now give

\[
 \dim W_{\rm inv}=\dim\operatorname{Ext}^2_{X^2}(I,I)^{G_1\times G_2}
     =6\cdot1+6\cdot6+1\cdot6=48.                \tag{3}
\]

These are derived Ext groups. Replacing them by H^2 of a sheaf of
endomorphisms would remove needed local contributions and would not
justify the deformation argument.

For raw Hodge character and the first-jet sign a=-At_BF, put

\[
 f_n=\operatorname{ch}_H(I_Z)
       =1-\frac n2\theta_H^2+\frac n3\theta_H^3.
\]

Write U=H^1(O_X), W=H^0(Omega_X^1), T=W^dual, each dimension three.
The polarization gives the isomorphism j:T -> U. Contraction c^1 has
the two projections eta and -n j(xi) wedge theta_H into H^1(O_X)
and H^2(Omega_X^1), so is injective of rank six. Contraction c^2 is
onto the six-dimensional space H^2(O_X) plus H^3(Omega_X^1): the U-wedge-U
block supplies the first part; eta tensor xi maps to
-n eta wedge j(xi) wedge theta_H and supplies the second part.

For I the three images have ranks 6,36,6 and ordered factorwise
Hodge imbalances (2,0), (1,1), (0,2). These summands are disjoint.
Hence c_I^2 has rank exactly 48, not merely a rank on a selected
piece of the obstruction group.

There is also a directly checkable universal minor. In a symplectic
Hodge basis theta=sum u_i w_i, select the three rank-term coordinates
and three separate -n*j(xi)*theta coordinates of c^1. Select the three
U-wedge-U inputs and three off-diagonal eta_i tensor xi_j inputs of
c^2, where i,j complement the requested remaining index. Both resulting
six-by-six diagonal detectors have determinant -n^3. On the product,
their three blocks have sizes 6,36,6; the middle is the tensor square
of the c^1 detector. The full selected determinant is

    (-n^3) * ((-n^3)^6 * (-n^3)^6) * (-n^3) = n^42.

Thus the cochains divided by their nonzero diagonal monomials give
the required explicit right inverse for all n != 0. The exact program
`research/computations/secant_obstruction_rank.py` computes the actual
contractions in twelve exterior generators, checks all 2304 entries of
this minor against the independent factorwise tensor construction and
verifies the determinant over Q[n]. It does not sample orbit lengths.
The factorwise dimension proof above gives the matching upper bound.

The exact Hochschild--Atiyah trace identity is

\[
 HT^2(X^2)\xrightarrow{o_I}\operatorname{Ext}^2(I,I)
       \xrightarrow{\sigma_I}\bigoplus_j H^{j+2}(\Omega^j),
 \qquad \sigma_I o_I=c_I^2.                       \tag{4}
\]

Translations act trivially on HT^2 and evaluation is natural. Thus
im(o_I) lies in W_inv. Equations (3)-(4) force its image to be all of
W_inv, with sigma_I injective there. Equivalently, a 48-coordinate
detector for the three displayed contraction images has a right
inverse given by those explicit cochains; the Lean theorem
`periodTransport_full_obstruction_injection` proves the resulting
full-space inference. This is obstruction rank, not an assumed rank
of the algebraic cycle-class map.

The fixed enhanced Fourier--Mukai equivalence carries evaluation and
character contraction in commuting squares with isomorphisms on all
three spaces. Its conjugated action is exactly the coherent
line-translation action on G. Consequently sigma_G is injective on
the entire invariant Ext^2(G,G). Perfect duality and the shift defining
E0 give sigma_E0,j(d_2 v)=(-1)^(j+1) sigma_G,j(v), preserving injection.
No assertion that raw trace is naturally invariant on arbitrary Ext
under an arbitrary Fourier transform is used.

## 3. Descent makes invariant obstruction control sufficient

The actual line-translation action has underlying translations

\[
 b_{g_1,g_2}=(g_1-g_2,\ a(-g_1-g_2)).
\]

The map is injective because G1 and G2 intersect trivially. The quotient
q:M -> Y0=M/Gbar is a finite etale isogeny. Associative line compositors
come from conjugating the genuine source action by the fixed integral
kernel; no simplicity assumption on E0 is needed.

Choose local sheets of q, trivialize the transition lines, and normalize
the resulting sheaf transitions by r-th roots of their determinants.
Their triple multipliers lie in mu_r and satisfy the Cech cocycle law.
This constructs a determinant-trivial rank-r alpha-twisted coherent
perfect sheaf B on a finite-band gerbe over Y0. Locally it is E0
tensored with a twisted line of raw first Chern class -c1_H(E0)/r.

Line factors cancel in derived endomorphisms. Exact finite-cover
pushforward and the averaging projector give, in every degree,

\[
 \operatorname{Ext}^i(B,B)\simeq
       \operatorname{Ext}^i(E_0,E_0)^{\bar G}.       \tag{5}
\]

The Atiyah tensor rule and perfect trace give

\[
 q^*\sigma_B=e^{-c_{1,H}(E_0)/r}\sigma_{E_0},
 \qquad q^*\operatorname{ch}_{B}(B)=\kappa_M.       \tag{6}
\]

The exponential is a finite invertible operator on the obstruction
target. Equations (5)-(6) prove injectivity of sigma_B on its full
Ext^2. The character kappa_Y=ch_B(B) is rational, since its pullback
is rational and (deg q)^(-1) q_* is a rational left inverse to q^*.
It transports as a Hodge character through the compatible domain.

To use ordinary coherent-sheaf deformation, realize alpha by a finite
projective representation. For Lambda=H_1(Y0,Z) of rank twelve, alpha
is an alternating mu_r-valued pairing b on Lambda. On G_r=Lambda/rLambda
choose the cocycle c(x,y)=product over i<j of b(e_i,e_j)^(x_i y_j).
On the regular vector space of dimension m=r^12 set

    T_x v_y = c(x,y) v_(x+y).

Then T_x T_y=c(x,y) T_(x+y). Its projective representation and the
relative [r]-torsor construct a P^(m-1) bundle p:Z -> Y over a small
polarized germ of the quotient family. Determinant-normalized lifts
give on the central fiber an alpha-twisted vector bundle Q0 of rank m
with trivial determinant. The inverse-twisted O(1) on P(Q0) cancels
the twist of p0^*B, giving the ordinary coherent sheaf

\[
 F_0=p_0^*B\otimes O(1).
\]

The anticanonical line H=omega_(Z/Y)^(-1) is globally ordinary and
zeta=c1_B(H)/m restricts to the hyperplane class. It is flat rational
and Hodge. Since Rp_*O_Z=O_Y, perfect base change and the projection
formula identify the full Ext^2(F0,F0) with Ext^2(B,B). The trace square is

\[
 \sigma_{F_0}(p_0^*v)=e^{\zeta_H}p_0^*\sigma_B(v).  \tag{7}
\]

Pullback in (7) is injective, with left inverse eta -> p_*(zeta^(m-1) eta)
on Betti classes; Hodge comparison gives the same injection on the raw
targets. The exponential is invertible. Thus F0 is fully semiregular.
Every fiber Z_s is projective: it is a free finite quotient of the
projective variety Y_s x P^(m-1); tensoring translates of an ample line
and descending proves ampleness. Locally a relative ample line exists.

## 4. Actual local deformation, followed by algebraic extraction

We use this exact deformation theorem, with its hypotheses retained:

**Projective germ semiregularity theorem.** For a smooth analytic germ
S, a proper holomorphic submersion with a relative ample line, and an
ordinary coherent central sheaf F0, suppose its full Ext^2 trace-Atiyah
map is injective in selected degrees. If the corresponding rational
central Chern characters extend as flat de Rham classes lying in F^k,
then F0 extends, after shrinking S, to a flat coherent sheaf with these
fiber characters.

This is `p3sw:projective-germ` in the pinned source; its proof is the
smooth projective case of the Buchweitz--Flenner argument. We checked
the coefficient obstruction, iteration and analytic effectivity, not
just its statement. In brief, over R/m^(nu+1), a flat sheaf is absolutely
perfect and its coefficient Ext^2 is central Ext^2 tensor J_nu. The
Atiyah obstruction square sends its obstruction through semiregularity
and coefficient differentiation to the Hodge edge of the Gauss--Manin
derivative. The latter vanishes for a flat filtered class. Differentiation
J_nu -> Omega_R^1/m^(nu+1) is injective by the homogeneous Euler identity;
proper-smooth Hodge freeness preserves this injection. Semiregularity
therefore kills the actual sheaf obstruction at every order.

The character of each lift is its constant central de Rham character:
use a finite locally free resolution on the projective thickening,
smoothly trivialize over the nilpotent coefficient ring and use
Chern--Weil/Chern--Simons comparison. This justifies iteration for the
lift actually chosen, not only for a hypothetical preferred lift.
Relative Serre generation and H^1 vanishing lift a fixed quotient
compatibly through the orders. The relative analytic Quot germ then
has a formal section; Artin approximation yields an exact analytic
section with the fixed central quotient. Its universal quotient is the
required flat sheaf. It need not reproduce the entire chosen formal
tower. Its central character and flatness determine the desired fiber
characters. This step supplies existence of actual sheaves, not only
vanishing of a first-order obstruction.

Apply it on Z with the full flat character

\[
 A_B=p^*\kappa_Y e^\zeta.
\]

All its components have the required type by (1), and its central value
is ch_B(F0). Take all indices 1,...,dim Z, which include every nonzero
component of the semiregularity target. The raw Hodge input in degree k
is the edge of (2 pi i)^k A_B,k. On semiregularity targets the Tate
weight is the form degree j; we do not normalize them by half their
total degree. This keeps (6)-(7) and the obstruction square consistent.

Let F_s be the resulting coherent sheaf on Z_s. Projective GAGA makes
it algebraic. In the rational Chow ring put zeta_CH=c1_CH(H_s)/m and

\[
 C_s=p_{s*}\left(\zeta_{CH}^{m-1} e^{-\zeta_{CH}}
                          \operatorname{ch}_{CH}(F_s)\right).
                                                               \tag{8}
\]

All exponentials are finite at the dimension of Z_s. Canonical Chern
comparison, product compatibility and proper pushforward give
cl_B(C_s)=kappa_Y(s), since p_*(zeta^(m-1) p^*eta)=eta. In particular

\[
 \Gamma_{Y,s}=(C_s)_3-P_3\Theta_{Y,s}^3,\qquad
 \operatorname{cl}_B(\Gamma_{Y,s})=w_s\ne0          \tag{9}
\]

on a nonempty neighborhood. A rational polarization is represented by
an ample line divided by an integer. Equations (8)-(9) construct the
local source from the deformed ordinary sheaf; they assume no Hodge
preimage and no cycle-class surjectivity.

## 5. A fixed nonzero source at every compatible period

Let (V,h,e) be the rational homological space of Y0. Compatible periods
are positive three-planes for the Hermitian form of signature (3,3).
After a positive/negative splitting these are graphs of matrices Z with
operator norm less than one. The domain D is connected and contractible
of complex dimension nine. Cohomologically the periods are
P plus Ann(P) in the two K-eigenspaces, a holomorphic map to the Siegel
domain. Thus no product or extra-endomorphism period is excluded.

Choose a rational symplectic basis of e. Its integral span Lambda_pp
gives a principally polarized marked family over D, pulled back from
the algebraic universal family over the fine level-four moduli variety
A_6(4). The universal morphism is smooth projective. A constant lattice
denominator supplies fiberwise algebraic K-linear isogenies
j_s:A_s^pp -> Y_s. Their pullbacks carry (9) to a fixed nonzero flat
rational vector w_pp(s) on a nonempty open O in D.

We prove spread for this fixed vector, rather than assuming that a
particular sheaf exists globally. Enumerate all finite rational lists
(q_1,...,q_l) and Hilbert polynomials (P_1,...,P_l) of degree three.
This is a countable set. For one datum i let H_i be the product over
A_6(4) of these relative Hilbert schemes. It is projective. Pull it
analytically to D and let H_i^good be the locus where

\[
 \sum_{a=1}^{l}q_a\operatorname{cl}_B
       ([\mathscr Z_a]_{\mathrm{top}})=w_{pp}(s).   \tag{10}
\]

The universal fiber classes are locally constant, including at singular
and nonreduced Hilbert points. Here is the needed justification. The
universal structure sheaf is flat over the Hilbert base, the ambient
family is smooth of relative dimension six, and the regular fiber rings
bound its absolute projective dimension by six. The ample resolution
property gives a finite global vector-bundle resolution. It restricts
exactly on every fiber by flatness. A differentiable local trivialization
of the original smooth projective family pulls back to the possibly
singular Hilbert base. Restricted vector bundles have locally constant
topological Chern character there. The degree-three leading character
of a dimension-three subscheme is the class of its top-dimensional
fundamental cycle, with generic lengths. Lower-dimensional and embedded
terms do not change it. Hence (10) is locally constant.

Thus H_i^good is open and closed in the pulled-back Hilbert space. It
is a closed analytic subspace, proper over D. By the proper-image
theorem its image C_i is a closed analytic subset of D. Reduction of
the parameter space does not change its image; smoothness of that
space is not required.

Every s in O belongs to some C_i by (9): an actual rational Chow
representative is a finite signed rational sum of integral subvarieties,
which are Hilbert points with degree-three polynomials. Therefore

    O is contained in the union of the countably many C_i.

If every C_i were proper, the analytic identity principle on the
connected manifold D would make all C_i nowhere dense. Baire contradicts
this covering of the nonempty open O. Some C_i0 is consequently all of
D. This is exactly the argument verified by
`periodTransport_countable_closed_spread` and
`periodTransport_all_period_witnesses` once proper analytic images and
the identity principle are instantiated.

For ANY requested period s, the proper fiber (H_i0^good)_s is nonempty.
Choose a point in it and take the signed rational fundamental-cycle sum
in (10). This is a genuine codimension-three cycle Gamma_pp,s with
cl_B(Gamma_pp,s)=w_pp(s) != 0. Its existence follows from the proved
nonemptiness of a geometric parameter fiber. No arbitrary-target
preimage selector is postulated. A single sheaf has not been claimed
to travel through every period.

## 6. The second Weil direction and every hyperbolic lattice

There is an explicit uniform CM element, eliminating a generic-choice
step. Set m=d+1 and k=m+u. On the two rational Weil coordinates of a
sixfold its action has matrix r6 I+s6 J with J^2=-d and

\[
 r_6=m^6-15dm^4+15d^2m^2-d^3,\qquad
 s_6=2m(3m^2-d)(m^2-3d)>0.                       \tag{11}
\]

Indeed m^2-3d=d^2-d+1>0 and 3m^2-d=3d^2+5d+3>0.
For any nonzero rational v=(x,y),

\[
 \det(v,k^*v)=s_6(x^2+dy^2)>0.                    \tag{12}
\]

The two cycles Gamma_pp,s and k^*Gamma_pp,s therefore span the Weil
plane. Clearing a denominator c makes f=c k an actual algebraic
endomorphism; on H^6 its action is c^6 k^*, so use c^(-6) f^* on
rational Chow groups. This is an algebraic operation, including at
special periods. The Lean sixth-power and reconstruction theorems prove
(11)-(12) and the exact coefficients of any prescribed vector.

Now let X_target be ANY hyperbolic K-Weil sixfold with its actual
compatible homological form. Split isotropic pairs to identify that
Hermitian space K-isometrically with (V,h). The coefficient of u in h
recovers e, so the transported complex structure is a point s of the
full domain D. The target lattice and Lambda_pp are commensurable.
Choose a positive integer c_lat clearing their inclusion. The map
c_lat times the K-isometry induces a holomorphic finite-kernel
surjection X_target -> A_s^pp. It is algebraic since both tori are
projective. Its pullback is an isomorphism on rational H^1 and on both
sixth determinant lines. Pull back the two actual cycles above.
This proves conclusion 1 for the original X_target and every rational
Weil target on it. No integral-polarization match or rational spin lift
is required. The seed isogeny need not extend through the family.

## 7. Apply transport to the ORIGINAL fourfold

Let A now be the given fourfold, with compatible K action of signature
(2,2). Choose a K-basis with positive rational determinant delta of its
actual Hermitian form. On B=E_+ x E_- choose opposite CM actions and
positive rational elliptic polarization multiples giving Hermitian
coefficients t and -1/(delta t), t>0. Then X_target=A x B has signature
(3,3) and determinant -1 modulo norms, hence is hyperbolic.

For completeness, the rational hyperbolicity criterion used here does
not assume algebraicity of Weil classes. An indefinite Hermitian form
of rank at least four has an isotropic vector by applying Meyer's
theorem to its underlying indefinite rational quadratic form. Split
off a hyperbolic plane and repeat until rank two. In rank two,
determinant class -1 means the ratio of the two diagonal coefficients
is a negative norm, giving an isotropic vector directly. Each split
pair normalizes to [[0,1],[1,0]]. For signature (3,3), determinant class
-1 therefore implies three hyperbolic planes. Clear polarization
denominators afterwards; the determinant changes by a norm.

Conclusion 1, applied to this precise PRODUCT period, constructs a
nonzero rational Weil cycle Gamma in CH^3(A x B)_Q. Its construction is
the Hilbert-fiber source and isogeny pullback of Sections 5-6. It is not
a new invocation of the unexpanded source assertion T6.

The algebraic detector on B is D0=Delta-F1-F2. Together with
Du=Graph(u)-F1-dF2 its Gram matrix is diag(-2,-2d), and D0 kills both
fiber divisors. Define the genuine original-A cycle

\[
 Z=(p_A)_*\bigl(\Gamma\cdot p_B^*D_0\bigr)
      \in CH^2(A)_Q.                              \tag{13}
\]

The balanced determinant tensor has rational coordinates
[[x,y],[y,-x/d]]. Contraction with D0 sends it to (-2x,-2y), so is
injective, with determinant four. The determinant sector has only
Kunneth degree (4,2). Canonical cup/Gysin compatibility proves

\[
 \operatorname{cl}_{B,A}(Z)=
 c_{D_0}(\operatorname{cl}_{B,A\times B}(\Gamma))
       \in W_K(A)\setminus\{0\}.                  \tag{14}
\]

Dimensions agree: codimension three plus one minus the relative
dimension two is codimension two. Proper Chow pushforward, intersection
and pullback in (13) are algebraic; no auxiliary cycle-class map is
being designated canonical by its name.

Again use k=d+1+u, now acting on fourth determinant powers. With m=d+1,

\[
 r_4=m^4-6dm^2+d^2,\qquad
 s_4=4m(m^2-d)=4(d+1)(d^2+d+1)>0.
\]

For v=cl_B(Z)=(x,y), det(v,k^*v)=s4(x^2+d y^2)>0.
Choose c>0 with f=c k an actual isogeny of A and put
Z1=c^(-4) f^* Z. Then Z and Z1 are actual independent rational
codimension-two cycles on this SAME A. The existing fourth-power
and contraction Lean theorems establish these arithmetic facts.

For a prescribed Weil vector (a,b), set Delta=s4(x^2+d y^2) and

\[
 \lambda=\frac{a(s_4x+r_4y)-b(r_4x-ds_4y)}{\Delta},
 \qquad \mu=\frac{xb-ya}{\Delta}.
\]

Then lambda Z+mu Z1 has exactly that canonical class. If the given
middle Hodge space is Q theta_A^2 direct-sum W_K(A), write its target
as q theta_A^2+(a,b) and add q Theta_A^2. The result represents the
prescribed full middle Hodge class. `auxiliaryWeilEveryMiddleHodgeClass`
already checks this native linear assembly; the present argument
supplies its geometric auxiliary source at the required period at
manuscript level.

The new Lean entry point
`auxiliaryWeilEveryMiddleHodgeClass_from_periodSpread` uses the proved
Baire witness theorem and then this existing assembly. A fixed auxiliary
cycle is no longer a parameter of that entry point. Its inputs expose
the Hilbert parameter family, closed analytic images, local witnesses,
the cycle built from a parameter on the requested fiber and its fixed
canonical comparisons. These geometric instances are supplied in the
manuscript argument and are not yet constructed as Lean inhabitants.

For the stated very general fourfold this also gives the full rational
Hodge conjecture in every codimension at manuscript level. Codimension
one is Lefschetz (1,1), codimension three follows by the Hodge-compatible
isomorphism theta_A^2:H^2 -> H^6 and intersection with the algebraic
polarization square, and codimensions zero and four are represented by
the variety and a point. The only exceptional middle directions were
the two just constructed. This does not extend the conclusion to
uncontrolled extra middle Hodge directions at special periods.

Finally take a finite cycle representative of Z. If every integral
surface in its support had zero exceptional projection, linearity
would contradict (14). Thus at least one actual irreducible surface
on the original fourfold detects an exceptional direction. Signed
cycles are permitted; an effective primitive middle cycle was never
claimed. This supplies the source requested in the question.

## Source audit and dependency dictionary

Exact local primary source: OpenAI/math revision
`301488868beec11bfd897168433b0a64f5258559`, TeX Git blob
`d154748feaa7775d2488902ca32f5615e5f4dad6`, SHA-256
`1ff56b1b900b70df2a8817ae90725f45ae74b267bb1568025bc4bcaa598c1c23`.
[Pinned source](https://github.com/openai/math/blob/301488868beec11bfd897168433b0a64f5258559/preprints/Weil-classes-and-Hodge-classes-on-abelian-powers-October-6-2026/build/paper.tex).
The already authorized local copy was used; no internet search was run.

| Needed implication | Exact source locus checked | Application |
|---|---|---|
| Exact trace/evaluation identity, signs and enhanced transport | `p3sw:hh-triangle`, `p3sw:hh-transport`, their proofs | Abelian source and target, perfect orbit ideals, fixed kernel and shifts. |
| Full invariant Ext, contraction rank and trace injection | `p3sw:invariant-orbit-ext` through `p3sw:invariant-injectivity` | Our direct seed has exactly the disjoint nonhyperelliptic Abel orbits required. |
| Coherent line compositors and finite quotient | `p3sw:coherent-action` and proof | The same fixed kernel, independent G1,G2 and inverse-Poincare signs. |
| Twisted descent on full derived Ext | `p3sw:descent-duality`, `p3sw:twisted-descent` and proofs | Positive rank 8d, perfect determinant, finite characteristic-zero averaging. |
| Ordinary projective conversion | `p3sw:ordinary-conversion` and proof | Finite-band class on a torus lattice of rank twelve, polarized smooth local family. |
| Actual analytic coherent-sheaf deformation | `p3sw:projective-germ`, coefficient/one-step/Artin-character lemmas and effectivity proof | Relative ample line; full Ext^2 injection; all normalized character components flat Hodge. |
| Countable proper Hilbert spread | `p3sw:spread` and proof | Smooth projective level-four ambient family; connected marked analytic domain; our fixed-vector version needs one generator per list. |
| Arbitrary rational lattice and product periods | `p3sw:endpoint-all-lattices` and proof | Actual Hermitian K-isometry, commensurable lattices, fiberwise GAGA isogeny. |
| Fourfold padding | `p3ab:hyperbolic`, `p3ab:determinant-supply` | Opposite CM elliptic actions, arbitrary original determinant delta. |

The source authentication, theorem applications and reconstructed argument
are distinct checks. The original articles cited inside the pinned source
were not independently reacquired in this round. The pinned source itself
gives proofs of the specialized transport statements used here; their
applications above were checked against those exact statements and proofs.
This is a reconstruction and specialization of an existing method, not a
claim to have discovered the all-period theorem independently.

## Adversarial self-review

- Flat Hodge character is used only after full obstruction control and
  actual analytic effectivity; it is not itself an algebraicity argument.
- Invariant Ext^2 injection is transferred to the FULL obstruction group
  of an ordinary sheaf before deformation. No injection on the full
  Ext^2 of the original covering sheaf is inferred.
- The projective bundle is built over the quotient family; a relative
  deformation of the seed isogeny or twisted sheaf is unnecessary.
- Hilbert good loci include singular and nonreduced parameter points;
  their images are proper analytic images. Closed sets alone would not
  give the identity-principle conclusion used by Baire.
- Product periods remain in the connected domain, so the particular
  padded A x B is covered. The final cycle is on the original A.
- The second CM operation uses its sixth or fourth exterior character,
  respectively. Multiplication by u alone can be scalar and is not used
  to manufacture a second independent direction.
- The very-general three-direction description is not asserted at all
  special fourfold periods. The Weil-plane construction itself is
  independent of that generality condition.

Primary mathematical verdict: **proved as written using the named,
checked source theorems**. The displayed transport/extraction chain
gives the three stated geometric conclusions. The complete geometric
Lean proof is **incomplete**: the new core Lean results and the
previous native assembly do not yet instantiate all the analytic,
derived and canonical geometric objects. The arbitrary smooth-projective
all-varieties Hodge theorem is not a consequence of this Weil-family
construction alone and is not claimed here.

## Uniform CM projector that purifies an original-fourfold algebraic source

The same original-A Weil fourfold proof has a new rational algebraic correspondence that extracts the exceptional Weil component of ANY raw codimension-two algebraic cycle. This is an advance within the *same* source construction: the extracted cycle need not arrive without ambient contamination.

Let K=Q(u), u²=-d, d>0 rational, and set m=d+1, q=m²+d. The actual K-endomorphism m+u is algebraic after one denominator is cleared. On H⁴(A,Q), let T be its pullback and set
\[
 r=m^4-6dm^2+d^2,\qquad s=q(m^2-d),\qquad n=q^4.
\]
The exceptional Weil, mixed and central eigenfactors are
\[
 G_W(t)=t^2-2rt+n,\quad G_M(t)=t^2-2st+n,\quad t-q^2.
\]
With N(t)=(t-q²)G_M(t), exact polynomial division yields
\[
 N(t)=G_W(t)(t+2r-2s-q^2)+a+bt,\quad
 a=2(s-r)q^4,\quad b=2(r-s)(2r-q^2).
\]
The determinant of the residue's rational inverse factors uniformly:
\[
 D=a(a+2rb)+q^4b^2
  =256d^3(d+1)^2(d^2+3d+1)^6(3d^2+5d+3)^2>0.
\]
Define the **explicit rational CM projector**
\[
 \boxed{P_d(t)=\frac{(t-q^2)(t^2-2st+q^4)(a+2rb-bt)}D.}
\]
Then P_d≡1 modulo G_W, P_d≡0 modulo G_M, and P_d(q²)=0. Thus P_d(T) fixes exactly the rational two-dimensional Weil plane and kills the entire remaining degree-four CM spectral decomposition. The expression is a genuine rational **algebraic correspondence**, since every power T^j is a pullback by an actual isogeny.

For the algebraic cycle obtained from the already constructed auxiliary sixfold source,
\[
 Z_{\rm raw}=(p_A)_*(\Gamma\cdot p_B^*(D_0))\in CH^2(A)_Q,
\]
the new cycle Z_W=P_d(T)Z_raw is an ACTUAL rational algebraic codimension-two cycle on ORIGINAL A. Its canonical Betti class is exactly the Weil projection of cl_A(Z_raw). The geometric detector from (14) proves this source nonzero, and the existing CM fourth-power orbit and Cramer coefficients then realize any prescribed rational Weil target from Z_W. The ambient-purity comparison is achieved by the explicit algebraic projector rather than being assumed about a raw source.

**Evidence.** The exact polynomial reduction, inverse on the exceptional quadratic, other-sector annihilation and gap positivity are Lean theorems in GSTWeilFourfoldAuxiliaryExtraction.lean. Dedicated [Weil CI #39077204383](https://github.com/kyo-oo/HC-PROOF/actions/runs/39077204383) and [full Hodge integration #39077204423](https://github.com/kyo-oo/HC-PROOF/actions/runs/39077204423) are GREEN at e7bb94aeb1b726a7ea6d6a211f1373a20cadcb42, with no sorryAx reported. The standard-library rational certificate research/computations/weil_general_d_projector.py passed 69 rational values and checked polynomial idempotence in the complete degree-four spectral quotient. The uniform CRT derivation and positivity factor are symbolic identities, checked in Wolfram, independent of the finite sweep.

**Scope.** This improves source purification for all imaginary-quadratic fourfold parameters. Instantiating the complex analytic Hilbert-spread, sheaf deformation and canonical Betti comparisons remains a separate part of the original manuscript proof, and the all-varieties Hodge conjecture remains its unchanged global target.

## Verification receipts

Final mathematical source: `46b126eb1a40cf5406efd28a68b027b662ef4945`.
No local Lean installation or local Lean run was used.

- **[Full integration 39075550466](https://github.com/kyo-oo/HC-PROOF/actions/runs/39075550466): PASSED**, job `117521836538`. Build completed successfully with 8961 jobs. All nine exact computation steps passed, including the new symbolic obstruction detector. The downloaded Lean log has 1757 printed axiom receipts, union exactly `propext`, `Classical.choice`, `Quot.sound`, and no `sorryAx` or Lean errors. This includes the receipt for `auxiliaryWeilEveryMiddleHodgeClass_from_periodSpread`.
- Full artifact `12116687291`: ten logs, ZIP SHA-256 `469a9f2cf6049694ddc1a9fd8d9c21db870bab7431ed9693a56ace8f243b55d2`, checked against the GitHub digest.
- **[Dedicated transport check 39075550336](https://github.com/kyo-oo/HC-PROOF/actions/runs/39075550336): PASSED**, job `117521835762`. Its 37 printed axiom receipts have the same standard-only union. Artifact `12117290301`, ZIP SHA-256 `34b515eb61beb7d486211eca1fd60360bfab501bd0d34dc1607264945eae1cfa`, independently checked after download.
- This round added **eleven transport/core theorems** to the existing extraction module and **one transport-to-native-assembly theorem** to the existing CM obstruction module. The Baire proof and assembled entry point are actual kernel-checked declarations, not placeholder statements.
- Extraction/transport Lean source SHA-256 `a3d942c7921ee6f49b949cbd4ffce6a9c970e04221ceb1cb8a669bffde3c8855`; native CM assembly source SHA-256 `59cd74582aa6c5729ca82da6c8c150b785cbcfb4f86e7a99d6cc455c6e74b7a4`.
- Exact detector script SHA-256 `8810947aa34cb61e55d51edeb78de378a03cff6c0e60b1b3bd20e27c4dc31bb8`; local output SHA-256 `92d351eac1861039afeb1a8bdd0f13be1fc9dc7d6f1b9935626faa1745fa7f09`. Its version-1 manifest validated with its stated legacy provenance limits. GitHub Python 3.12.3 and local Python 3.12.14 give identical scientific output after the version line, for both this detector and the seed-character computation.

The first source run failed on a renamed set lemma and denominator
normalization. The set proof was replaced by direct extensionality.
The Cramer proof now combines terms over one explicitly nonzero common
denominator before cancellation. The final two green runs above certify
the repaired complete source and its native integration; failed earlier
revisions are not verification receipts for the final theorem.


## Native CM functoriality and canonical Hilbert source bridge (2026-10-18)

This checkpoint integrates the exact polynomial Weil projector with **native rational Chow cycles on the original fourfold**. It strengthens the same source route rather than adding another special family.

Let T_Chow be pullback of rational codimension-two Chow cycles by the genuine CM isogeny k=d+1+u, and T_B the induced action on Betti H^4. The canonical naturality law cl∘T_Chow=T_B∘cl implies by Horner induction, for every polynomial P,

\[
 \boxed{\operatorname{cl}\big(P(T_{\mathrm{Chow}})Z\big)
     =P(T_{\mathrm{B}})\operatorname{cl}(Z).}
\]

The exact Weil projector P_d from the previous section is a degree-four rational polynomial. Its five expanded coefficients agree symbolically with the factored expression; Wolfram gave difference zero identically in the symbols q,r,s,a,b,t.

**Native operator proved in Lean.** In GSTWeilFourfoldAuxiliaryExtraction.lean the new theorems nativeCMHorner_natural, nativeWeilProjector_cycleClass and nativeWeilProjectorCoeffs_exact prove uniform cycle-class functoriality and the full coefficient identity. Dedicated Weil [CI #39096019777](https://github.com/kyo-oo/HC-PROOF/actions/runs/39096019777) and full Hodge [CI #39096019760](https://github.com/kyo-oo/HC-PROOF/actions/runs/39096019760) passed at commit 22bee45912c815397378127d09cb89307abdcbe6 with sorryAx audits.

**Original-fourfold isogeny action.** In GSTUniversalCMArithmeticObstruction.lean, auxiliaryWeilEveryMiddleHodgeClass_from_periodSpread_CMFunctorial replaces the old per-Hilbert-cycle CM comparison by a single global geometric action. On the Hodge coordinates Q theta^2 ⊕ W_K, the true CM isogeny acts as (c,v) ↦ (Norm(k)^2 c, fourthPowerAction(d,d+1)(v)). A fixed source class equality then implies every required pointwise CM equality. Full [CI #39096320930](https://github.com/kyo-oo/HC-PROOF/actions/runs/39096320930) passed at 17a61f4c21c1a48dbfee168ed2dcef6ddc402c9a.

**Fixed Hilbert-source class.** The further theorem auxiliaryWeilEveryMiddleHodgeClass_from_canonicalHilbertSource replaces individual extraction hypotheses by (i) one flat rational auxiliary Betti class w defining the good relative Hilbert locus, (ii) one global proper-pushforward/cup Gysin comparison, and (iii) one global isogeny compatibility law. From these laws the previously kernel-proved period spread and original-fourfold source assembly construct a native codimension-two cycle with the prescribed rational Betti class. Full [CI #39096564529](https://github.com/kyo-oo/HC-PROOF/actions/runs/39096564529) passed at e7691d08e5d927176435f8b1ed613e63ba08bc01; no sorryAx, artifact 12125455110, sha256:4f12c0949c2f22da99e22e03467b05a4919c01da6f2c1a9f06eb0a3130af1207.

**Precisely remaining geometric input.** The pinned primary source openai/math revision 301488868beec11bfd897168433b0a64f5258559, label p3sw:projective-germ, was read at its exact statement. It requires a proper smooth complex analytic germ with relative ample line, an ordinary coherent central sheaf, injectivity of its FULL Ext² semiregularity trace and flat rational Chern characters of the requisite Hodge filtration; it concludes a locally flat coherent sheaf with those characters. Sections 1–5 of this record construct the seed and apply this theorem before the proper Hilbert/Baire spread. Those analytic/coherent-sheaf and canonical scheme-to-Betti maps still require concrete Lean instantiation.

The source pipeline is now: geometric secant sheaf → local semiregular deformation → algebraic Chern/Chow cycle on sixfold → Hilbert spread → true Gysin extraction to original fourfold → genuine native CM projector → prescribed Weil Hodge class. The full all-varieties Hodge theorem remains the unchanged goal.


## Pure-Chow correction and nonzero-Weil-source reconstruction (2026-10-18)

**Final Lean commit:** [`e85d6eba76bc6791e669245f999a816464af8feb`](https://github.com/kyo-oo/HC-PROOF/commit/e85d6eba76bc6791e669245f999a816464af8feb).
**Pinned full integration:** [GitHub Actions #39099028550](https://github.com/kyo-oo/HC-PROOF/actions/runs/39099028550), **success**, the complete `GSTPinnedHodgeGeometricGate` dependency build and its no-`sorryAx` check. This supersedes the preliminary failed edit `5db73ca` (Lean elaboration/type mismatch) and the intermediate green repair `990e6e3`.

The exact Lean theorem **`GSTUniversalCMArithmeticObstruction.auxiliaryWeilEveryMiddleHodgeClass_from_canonicalHilbertSource`** now needs only a **single fixed nonzero rational Weil component**:
\[
z:=(\operatorname{bettiExtract}(w)).2\ne(0,0),
\]
where $w$ is the fixed auxiliary-sixfold Betti class. The former hypotheses requiring a balanced `TensorCoefficients`, a nonzero tensor, and the equality $z=\operatorname{contractGraph}(\mathrm{tensor})$ have all been **removed from this theorem's inputs**. In particular, it does **not** require the raw extracted source to be pure Weil: its ambient coefficient $c=(\operatorname{bettiExtract}(w)).1$ may be arbitrary.

At any target period, the existing Baire/Hilbert source assumptions select a genuine codimension-three auxiliary native cycle $\Gamma$ with class $w$. Let $R=\operatorname{extract}(\Gamma)$ on the **original fourfold $A$**, and let $\Theta^2$ be the actual native polarization-square cycle with canonical Hodge coordinate $(1,(0,0))$. Form the *native algebraic cycle*
\[
R_0=R-c\Theta^2.
\]
By the existing single global proper-Gysin cycle-class naturality law, its fixed Hodge coordinate is **exactly** $(0,z)$, with $z\ne0$. The already proved global CM cycle-class functoriality for the genuine isogeny $d+1+u$ yields a second actual cycle $T R_0$ of class $(0,T_W z)$. The exact existing GST fourth-power orbit theorem gives
\[
\det(z,T_Wz)=4(d+1)\big((d+1)^2-d\big)(z_1^2+d z_2^2)>0
\quad(d>0,z\ne0).
\]
Consequently the explicitly constructed Cramer coefficients, together with $\Theta^2$, give a **single signed rational Chow cycle on the original A** with any prescribed rational middle Hodge class, *under the theorem's stated geometric input hypotheses*.

**Independent exact computation.** Wolfram `FullSimplify` returned `{True,True,True}` for the determinant formula, $s>0$, and $(z\ne0)\Rightarrow\det>0$ assuming $d>0$ and real coordinates. The arbitrary rational case is already established by the kernel-verified Lean positivity theorem.

**Evidence boundary.** This is a strictly stronger *conditional original-fourfold construction* than the previous pure-source/tensor-coordinate entry point. The external geometric leaves are still the true analytic/coherent semiregular deformation source, its proper Hilbert spread across all periods, canonical Chow-to-Betti Gysin/isogeny comparisons, and the actual three-direction rational Hodge-fiber identification for the fourfolds to which it applies. Passing Lean CI proves the theorem with **those explicit hypotheses**, not their existence. It does **not** prove the original all-varieties/all-codimensions Hodge conjecture. Gate 3 of `research/ACTIVE_HODGE_PROOF_PLAN.md` remains unresolved.
