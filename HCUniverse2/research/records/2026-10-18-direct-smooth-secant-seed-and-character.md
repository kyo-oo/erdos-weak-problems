# Direct smooth secant seed and its explicit exceptional character

Start: `bd0a22c8f649558734b845c6879475907abde18c`, GPT-6 branch.
This executes the source-construction obligation of the locked plan.
It constructs the geometric seed on a genus-three Jacobian product and
calculates its exceptional class. It does not assert transport to an
arbitrary Weil period or the all-varieties Hodge theorem.

## Exact result and verification levels

For every imaginary quadratic field K, choose an integral imaginary
generator u0 with u0²=-d0, d0 positive. Set

    u=420u0,   d=176400d0,   n=d+1.

The construction below supplies a smooth nonhyperelliptic genus-three
curve C, its Jacobian X, two independent cyclic subgroups of X[n],
the required disjoint Abel-curve orbit unions A and Σ, and an ordinary
coherent perfect sheaf E0 on M=X×Xhat of rank r=8d. On this actual
polarized hyperbolic K-Weil sixfold, its normalized third Chern class is

\[
 \kappa_3(E_0)=
 \frac{(d-1)(d+1)^2}{24d^2}\theta_M^3
 -\frac{d+1}{4d}(\Omega_++\Omega_-).                 \tag{1}
\]

Consequently subtracting the displayed polarization cube gives an
actual rational codimension-three Chern cycle with a nonzero Weil class
at the seed period. No sixfold source cycle is assumed in this argument.

The proof below uses standard complex-curve, abelian-variety and
coherent-sheaf geometry. Those theories have not all been formalized here.
Lean verifies the four-mark vanishing, finite-orbit restriction,
torsion/support, translate-selection and dual-resolution algebra;
the exact exterior program verifies the character calculation. Keep
these verification levels distinct from a complete geometric Lean proof.

## 1. Choose a smooth curve directly

There exists a genus-three curve C with simple Jacobian and with

\[
 p-q\text{ torsion in }J(C)\quad\Longrightarrow\quad p=q. \tag{2}
\]

Here is a dimension proof that includes both requirements. The moduli
space of smooth genus-three curves has dimension six. If p≠q and
m(p-q) is principal, a rational function with divisor m(p-q) is a
degree-m map to P1, totally ramified at p and q. Riemann–Hurwitz gives
total ramification 2m+4. Those two points contribute 2m-2, leaving six.
There are at most eight branch values. For each degree and ramification
type the Hurwitz space is finite over the corresponding branch
configuration space; its dimension is at most 8-3=5. The closures of
their images in curve moduli are therefore proper. There are countably
many degrees and types.

If J(C) is not simple, Poincaré reducibility in dimension three gives
an elliptic quotient. The Abel curve generates J(C), so its composition
with that quotient is a nonconstant map C→E. Riemann–Hurwitz gives total
ramification four for this cover. The elliptic curve and at most four
branch values have parameter dimension at most 1+4=5, even before
quotienting translations. For a fixed degree and branching data there
are finitely many covering monodromies. The resulting countable union
of image closures is again proper in dimension six.

Choose C outside both unions and the five-dimensional hyperelliptic
locus. Existence follows over C by the countable-proper-locus/Baire
argument. This supplies the curve; its existence does not depend on T6.
The standard Hurwitz parameter-space and Poincaré-reducibility results
are classical geometric inputs, not new Lean declarations in this branch.

Fix p∈C and identify X=Pic²(C), with origin O(2p), with J(C). Let H
be the principal theta line and θ its integral class. The positive
and negative Abel curves C_p and Σ_p have class θ²/2 and theta degree 3.
In particular θ³=6. Condition (2) also holds on the negative Abel curve.

## 2. Independent actual torsion orbits

The group X[n](C) is isomorphic to (Z/nZ)^6. Choose two vectors of a
torsion basis, and let G1 and G2 be the cyclic groups they generate.
Both have order n and G1∩G2={0}. For arbitrary cosets put

\[
 A=\coprod_{g\in G_2}t_{s_0+g}C_p,\qquad
 \Sigma=\coprod_{g\in G_1}t_{t_0+g}\Sigma_p.
\]

These are disjoint unions within each part: an intersection of two
distinct translates would give a nonzero torsion difference of two
points of C, contradicting (2). The construction works for both signs.
No disjointness between the positive and negative unions is required.

## 3. Uniform vanishing without a compact-type degeneration

We prove, simultaneously for every N∈Pic0(X),

\[
 H^0(X,I_A\otimes H^2\otimes N)=
 H^0(X,I_\Sigma\otimes H^2\otimes N)=0.             \tag{3}
\]

Consider a nonzero section whose divisor D contains an orbit union.
Its class is 2θ. Write its distinct prime components as D1,...,Dm.
Each positive integer θ²·Di is at least one; their multiplicity-weighted
sum is θ²·D=12. Hence m≤12.

Every nonzero effective divisor on a simple abelian variety is ample.
Put Li=O(Di). Multiplication by a section of O(D-Di) embeds
H0(Li) in H0(O(D)). Kodaira vanishing and abelian Riemann–Roch give

\[
 1\leq\chi(L_i)=h^0(L_i)\leq h^0(H^2\otimes N)=8.
\]

The polarization kernel K(Li) has order χ(Li)². Our choice of parameter
has n≡1 modulo every integer 1,...,8, since 176400 is divisible by
each of them. Thus the order-n orbit group G has trivial intersection
with K(Li). A translation stabilizing Di stabilizes Li, so G acts freely
on the translation orbit of each Di.

For an ordered pair (Di,Dj), at most one g∈G satisfies t_g Di=Dj.
At most m²≤144 translations can therefore make D and t_g D share a
prime divisor. Since n≥176401, choose a translation outside this set.
The two divisors intersect properly. Both contain every curve in the
same G-orbit: translation by g permutes that orbit. Their effective
intersection cycle therefore has theta degree at least 3n. But

\[
 \theta\cdot D\cdot t_gD=4\theta^3=24<3n,
\]

a contradiction. This proves (3) for both orbit unions and for all
Picard twists. The argument is unaffected by coset translation.

This proof uses neither generic N nor semicontinuity to make N uniform.
The large parameter costs nothing in the existence argument. Scaling
u0 by 420 leaves K fixed and scales its actual homological Hermitian
form by the positive factor 420, preserving hyperbolicity and signature.
The construction only claims the enlarged parameter range needed after
this rescaling; it does not reprove seed existence for every small d≥3.

## 4. Construct the actual ordinary coherent sheaf

Use the same fixed kernel and signs as the pinned source:
OpenAI/math, revision `301488868beec11bfd897168433b0a64f5258559`,
TeX blob `d154748feaa7775d2488902ca32f5615e5f4dad6`, equations
`p3sw:support-fixed-transform` and `p3sw:support-source-object`.
That source is used for the transform dictionary, not as an assumed T6.

On X_y×M_(x,N), let π(y,x,N)=(x,N), α(y,x,N)=y+x, and set

\[
 \mathscr F=(H_y\otimes\alpha^*H\otimes\mathcal P_{y,N}^{-1})
       \otimes(\operatorname{pr}_y^*I_A\otimes^L\alpha^*I_\Sigma),
 \quad G=R\pi_*\mathscr F,\quad E_0=R\mathcal Hom(G,O_M)[-1].
\]

No positive Abel curve is a translate of a negative one: otherwise a
fixed degree-two line would have a moving effective divisor on C,
giving a g1_2 and contradicting nonhyperellipticity. Thus every pair
of positive/translated-negative curves meets in dimension zero or is
disjoint. The local length-two Koszul resolution shows that their
ideal tensor is the ordinary product ideal with the required Tor
vanishing. Applying this on the disjoint components gives the flat
product-ideal family and its derived base changes.

Each fiber line is H² times a Picard twist. Equation (3) kills its
ideal H0; the ideal sequence, one-dimensional support and Kodaira
vanishing kill H3. Outside the finite union of difference surfaces
Σ_j-C_i, the support is 2n disjoint genus-three curves. The fiber line
has degree six on each, so its H1 is zero by curve duality (6>4).
Thus the derived fibers of G occupy only degrees one and two, with
degree two zero on a nonempty open set.

Proper perfect base change gives a local two-term vector-bundle model
K1→K2. Its differential is generically surjective. On the integral
base M its dual is injective: clear a rational right inverse to get
fg=a·id with a≠0, and cancel a in the torsion-free dual. Therefore
E0 is an ordinary coherent sheaf with local resolution

    0 → (K2)* → (K1)* → E0 → 0.

It is perfect. The fiber Euler characteristic is 8-2n·4=-8d, so
rank(E0)=8d. This constructs a sheaf from the orbit ideals; it does not
select a sheaf from a prescribed cohomological preimage. The local Tor,
perfect-base-change and coherent-sheaf theories used here remain
classical geometric inputs to the manuscript's construction.

## 5. Direct computation of its Weil character

Identify M with X×X using a=-λ_H on the second factor. Write the two
symplectic cohomology bases as x1,...,x6 and w1,...,w6. Put

\[
 \theta_1=\sum x_{2i-1}x_{2i},\quad
 \theta_2=\sum w_{2i-1}w_{2i},\quad
 R=\sum(x_{2i-1}w_{2i}-x_{2i}w_{2i-1}),\quad
 t=\theta_M=d\theta_1+\theta_2.
\]

The actual K-endomorphism has pullback matrix ((0,-d),(1,0)) on
the two factor indices. Its eigenspaces are spanned by uxj+wj and
-uxj+wj. Define Ω± as the ordered wedges of those six forms. This
action has Weil multiplicities (3,3) and is compatible with the ample
line H^d⊠H. On homology, the K-span of a rational symplectic
Lagrangian in the first factor is a three-dimensional totally isotropic
subspace, so the actual Hermitian form is hyperbolic.

Riemann–Roch for the Abel curves gives

\[
 v=\operatorname{ch}(I_A(H))=\operatorname{ch}(I_\Sigma(H))
   =1+\theta-\frac d2\theta^2-\frac d6\theta^3
   =c_+e^{u\theta}+c_-e^{-u\theta},
 \qquad c_\pm=\tfrac12(1\pm u^{-1}).
\]

For one symplectic pair, oriented Fourier integration is the polynomial

\[
 H(a,b)=(a+b)+ab\theta_x-aR_x-\theta_w-a\theta_x\theta_w.
\]

If a+b≠0, it equals
(a+b)exp((ab θ_x-aR_x-θ_w)/(a+b)). The full fixed transform
has sign (-1)^3. Apply it to the four choices a,b∈{u,-u}.
Set q=(d-1)/(4d), A±=4d±2u(d-1), and α=(d+1)/(4d). The
same-sign terms of β=ch Φ(I_Σ(H)⊠I_A(H)) are

\[
 e^{-R/2}\bigl(A_+e^{ut/(2d)}+A_-e^{-ut/(2d)}\bigr).
\]

The opposite-sign terms are α(e^{uθ1}Ω+ +e^{-uθ1}Ω-). In particular
β0=8d and β1=-4dR-2(d-1)t. Moreover

\[
 \Omega_\pm t=0,\qquad
 \Omega_\pm(\pm u\theta_1+R/2)=0.
\]

These follow by setting wj=∓uxj modulo the ideal generated by the
six factors of Ω±. They also show that normalization removes the
exponentials multiplying the opposite-sign terms. Duality gives
ch(E0)=ιβ, where ι acts by (-1)^j in codimension j. Consequently

\[
 \kappa(E_0)=\sum_{j=0}^6 P_j(d)t^j-\alpha(\Omega_++\Omega_-),
 \quad
 P_j(d)=\frac{A_+(-q-u/(2d))^j+A_-(-q+u/(2d))^j}{j!}.
\]

Conjugation makes every Pj rational. P0=8d, P1=0 and
P3=(d-1)(d+1)²/(24d²), proving (1). The exceptional coefficient is
nonzero for d>0. More explicitly its all-w coefficient is
-(d+1)/(2d), which never vanishes in that range.

## 6. The actual cycle and the period-compatible class

All Chern operations in the following expression are algebraic:

\[
 \Gamma_0=\frac{c_3(E_0)}2
 -\frac{r-2}{2r}c_1(E_0)c_2(E_0)
 +\frac{(r-1)(r-2)}{6r^2}c_1(E_0)^3
 -\frac{(d-1)(d+1)^2}{24d^2}\Theta_M^3
 \in CH^3(M)_\mathbb Q.
\]

The canonical Chern/Betti comparison gives
cl(Γ0)=-α(Ω++Ω-)≠0, a primitive rational Weil class on this seed M.
The entire normalized character has Hodge type (j,j) along the full
compatible marked Weil domain: t stays a polarization, and the two
determinant lines have type (3,3). This compatibility follows from the
displayed formula; no spin-stabilizer classification is needed for it.

Transporting this algebraic source to other periods still requires the
semiregularity/descent/deformation and all-period spread arguments. A
flat Hodge character alone is not asserted to transport algebraicity.
The original arbitrary-X target is unchanged. This checkpoint supplies
the seed and its measured character, not that final transport theorem.

## Verification and self-review

The exact program `research/computations/secant_seed_character.py`
implements exterior multiplication from its sign rule and uses rational
sparse Laurent coefficients reduced by u²=-d. It verifies the oriented
one-pair integral, rank, first character, both annihilator identities,
the full degree-six formula and its rational nonzero component. It also
computes P0,...,P6. No sample value of d is used as the universal proof.

The Lean source is the existing `GSTWeilFourfoldAuxiliaryExtraction.lean`.
Its new results include four-mark vanishing over every field, all finite
orbit lengths ≥4, finite axis-evaluation vanishing, explicit torsion
orbits, disjoint star supports, good-translation existence, the degree
budget, dual precomposition injectivity, and the source coefficient.
They are source-construction lemmas; no arbitrary-target preimage or
Hodge-surjectivity hypothesis is introduced.

Self-review checked: counted indices rather than distinct marks;
the two curve unions only need within-part disjointness; component
count is multiplicity-compatible; χ(Li) uses simplicity for ampleness;
kernel orders use actual polarizations; the choice n avoids every
possible χ(Li)≤8; the Fourier shift is [-3] before duality and [2]
after it; the all-w coefficient is checked independently of nonzero
formal symbols; and the final Γ0 remains on the constructed seed M.

This is an alternative proof of the needed large-parameter seed and an
explicit source-character derivation. The pinned paper already proves
the more general seed statement for all d≥3. No global novelty claim
is made. Complete analytic/algebraic Lean instantiation is not claimed.
The four-mark proof has a direct combinatorial form. If two marks differ
in every coordinate, normalize them to 000 and 111; their axis equations
kill all eight coefficients. Otherwise color each pair of indices by an
agreeing coordinate. Each color is a matching, since a fiber has at most
two indices. Six edges covered by three matchings force the three perfect
matchings of K4. Normalize the coordinate values to get the four marks
000, 011, 101, 110. Their axis equations again kill every coefficient.
This also explains why the Lean proof needs no characteristic-zero
matrix-pencil argument. Restricting any longer orbit to four indices
proves the unbounded-orbit version.

### Completed verification receipts

- Final mathematical source: `2a5c980af9066150017d7cdf273115aea0a49c88`.
- **[Full integration 39071168177](https://github.com/kyo-oo/HC-PROOF/actions/runs/39071168177): PASSED**, job `117508923584`; 8961 build jobs, 1736 printed axiom receipts, union exactly `propext`, `Classical.choice`, `Quot.sound`; no sorryAx or Lean errors. All eight exact Python certificate steps passed.
- Full artifact `12115576025`, nine logs, downloaded ZIP SHA-256 `6822e88f3436fb4d532a981c472220b0a5ba7cded5eef6cf3aebde2fbbef1672` (matches GitHub digest).
- **[Dedicated seed check 39071168188](https://github.com/kyo-oo/HC-PROOF/actions/runs/39071168188): PASSED**, job `117508923627`; artifact `12115357205`, ZIP SHA-256 `cc345c612b52f2c77614c0ef4acefe900d291c79bc8125600a109d8c7265ce9a`.
- The existing Lean module acquired **25 theorem declarations**. Its SHA-256 is `48ac49920b6da091d6c5d54f3812d90715c928f2efc8ddf9ca069506cb2c35d0`. The original native middle-Hodge assembly still compiles unchanged against it.
- Exact character script SHA-256 `d2fa582b96732132e6f7ca4378fe5f4b4992c9930ab4ca5b88230d743389a0c6`; local output SHA-256 `ee0c5ad1f19b3d77fcf65e85109c383b23ca9dff0219cdad89e6c4a5a964491c`. Version-1 manifest validation passed, with its stated legacy provenance limits. Local Python 3.12.14 and GitHub Python 3.12.3 produced identical scientific output after the version line.

Initial source commit `5c4c6ba` failed finite-basis simplification and an
automated matching proof exceeded its heartbeat limit. `32963ee` repaired
both by explicit finite reduction and the 27 coordinate-color cases;
its dedicated and integration runs passed. `4e712a4` added the finite
axis restrictions and good-translation theorem, again with both checks
green. The receipt above additionally covers the dual-resolution and
character-coefficient lemmas and the new exact character computation.
Only the final green revision certifies this complete checkpoint.

