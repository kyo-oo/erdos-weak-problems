# A genuine fourfold source by auxiliary elliptic extraction

Start checkpoint: `aa2abbe546a6de367c2d970217627bcf0131a7bb` on
`mathbox/residual-zero-direct-audit-20261015`.

## Exact result and its dependency

There is an explicit Chow-theoretic extraction

\[
 Z=(p_A)_*\bigl(\Gamma\cdot p_B^*(\Delta-F_1-F_2)\bigr)
      \in\mathrm{CH}^2(A)_{\mathbb Q}
 \tag{1}
\]

which sends EVERY nonzero rational Weil class of a suitable auxiliary
sixfold to a nonzero exceptional Weil class of the ORIGINAL fourfold A.
It requires no discriminant-one hypothesis on A. This is a geometric
reduction using an external source theorem, not a GST-only construction
of the sixfold cycle and not a complete Lean formalization.

The named external input is:

**T6.** For every imaginary quadratic field K, the rational Weil plane
of every complex abelian sixfold with compatible hyperbolic Hermitian
polarization of signature (3,3) consists of algebraic codimension-three
classes, at every period, including product periods.

The exact statement occurs as `p3sw:weil-plane` in OpenAI,
*Weil classes and Hodge classes on abelian powers*, October 6, 2026.
The source used is pinned to repository revision
`301488868beec11bfd897168433b0a64f5258559`, TeX blob
`d154748feaa7775d2488902ca32f5615e5f4dad6`:
[source](https://github.com/openai/math/blob/301488868beec11bfd897168433b0a64f5258559/preprints/Weil-classes-and-Hodge-classes-on-abelian-powers-October-6-2026/build/paper.tex).
The statement, conventions, applicability to products, padding argument,
and relevant source-construction passages were read directly. The entire
external proof was not independently audited or formalized here. Attempts
to open the cited arXiv v2 and published DOI directly were unavailable;
those citations are not separately authenticated by this record.

The source's `p3ab:determinant-supply` already uses elliptic padding and
determinant extraction. Thus this is an explicit specialization and
detector calculation for that mechanism; no novelty claim is made.

## 1. Pad the given fourfold, not a substitute fourfold

Let A be the given polarized complex abelian fourfold of Weil type
for K=Q(u), u^2=-d, d a positive integer. Let the K-action on H^1
have signature (2,2). Use the homological Hermitian convention

\[
 h_A(v,w)=e_A(v,uw)+u e_A(v,w),
\]

conjugate-linear in the first argument. In a K-basis let
delta=det(h_A)>0. Its representative depends on that basis, which is
harmless because the auxiliary polarization is chosen after the basis.

Choose a CM elliptic curve E with K contained in End^0(E), and use the
chosen and conjugate K-actions on its two copies. Put B=E_+ x E_- and
X=A x B. Positive rational rescaling of elliptic polarizations permits
the rank-one Hermitian coefficients

\[
 t,\qquad -\frac{1}{\delta t},\qquad t>0.
\]

The product form on X has signature (3,3) and determinant -1. The
rational Hermitian hyperbolicity test in `p3ab:hyperbolic` therefore
makes it hyperbolic. That test uses Meyer's theorem; it is an external
number-theoretic leaf, not a determinant calculation alone. Clearing
denominators makes the product polarization integral. Its determinant
changes by a sixth power, which is a K/Q norm, so hyperbolicity persists.
All this changes auxiliary polarizations; A itself and its period remain
fixed. The product polarization on B is a positive combination of F1,F2.

Apply T6 to THIS X. Its geometric construction supplies a rational
codimension-three cycle Gamma with

\[
 0\ne \operatorname{cl}_B(\Gamma)\in W_K(X).
 \tag{2}
\]

This is the load-bearing source-existence step. It is supplied by T6,
not inferred from GST coordinates, a class-range retraction, or a
full-rank hypothesis. Without T6 or a replacement geometric proof,
equation (2) remains an unproved obligation in this project.

## 2. An actual algebraic elliptic detector

Write F1=E x {0}, F2={0} x E, Delta for the diagonal, and Gamma_u
for the graph of the integral CM endomorphism u of E. One may choose
E with maximal-order multiplication so u is integral. Define genuine
divisor classes

\[
 D_0=\Delta-F_1-F_2,\qquad
 D_u=\Gamma_u-F_1-dF_2.
\]

Their intersection calculations use the actual elliptic graph numbers:

\[
 F_1F_2=\Delta F_1=\Delta F_2=\Gamma_u F_2=1,\quad
 \Gamma_u F_1=d,\quad \Delta\Gamma_u=\deg(u-1)=d+1,
\]

and all four self-intersections vanish. Consequently

\[
 D_0^2=-2,\qquad D_0D_u=0,\qquad D_u^2=-2d,
 \qquad D_0F_1=D_0F_2=0.                 \tag{3}
\]

On B the total K-action is (u,-u). Its two determinant eigenspaces
in H^2 are of type (1,1). D0 and Du span their rational plane W_K(B).
To see the character convention concretely, on this cross-factor plane
the partial pullback g=(u,id)^* satisfies g(D0)=Du and g(Du)=-d D0
in Betti cohomology. Thus J_B=g has matrix [[0,-d],[1,0]]. These are
cohomological assertions; an arbitrary equality of divisors in the Chow
group is not required.

## 3. The detector cannot lose a nonzero Weil direction

Set V_sigma=H^1(A,K)_sigma and L_sigma=H^1(B,K)_sigma. Their dimensions
are four and two. The natural exterior-product map identifies

\[
 W_K(X)_K=
 (\wedge^4 V_\sigma\otimes\wedge^2 L_\sigma)
 \oplus
 (\wedge^4 V_{\bar\sigma}\otimes\wedge^2 L_{\bar\sigma}). \tag{4}
\]

In particular this lies in H^4(A) tensor H^2(B); no other Kunneth
degrees occur. D0 has nonzero components in both conjugate lines of
W_K(B): it is rational and nonzero by (3), and conjugation exchanges
the two lines. The pairing in (3) is nondegenerate. Hence contraction
with D0 is nonzero on each line in (4), and gives an isomorphism

\[
 c_{D_0}: W_K(X)\longrightarrow W_K(A).       \tag{5}
\]

Here is also a rational coordinate verification, including its signs.
Choose a rational basis A0,A1 of W_K(A) with J_A A0=A1,
J_A A1=-d A0, where J_A has eigenvalues sigma(u),bar-sigma(u) on
the respective determinant lines. In the B basis D0,Du, the equalizer
J_A tensor 1 = 1 tensor J_B consists of the matrices

\[
 M(x,y)=\begin{pmatrix}x&y\\y&-x/d\end{pmatrix}.
\]

This is exactly the rational space in (4). By (3), contraction with
D0 sends M(x,y) to -2x A0 -2y A1. Its determinant in these rational
bases is 4, so a nonzero Weil vector cannot contract to zero. These
coordinates certify the detector; they are not the source cycle.

The polarization on A has one factor of each K embedding. Wedging it
with either fourth exterior eigenspace requires five vectors in a
four-dimensional eigenspace, so W_K(A) is primitive. The same degree
argument identifies the usual Weil classes on X. Also, if a source
character is presented as a theta_X^3+w, equation (3) kills its
polarization-cube term under (1), since theta_X is a product polarization.
For the global application it is safer simply to use the pure cycle
provided by T6; no global deformation of a particular sheaf is presumed.

## 4. Canonical class and actual surface support

Proper pushforward, divisor intersection and external pullback in (1)
are genuine algebraic Chow operations. X has dimension six; intersecting
a codimension-three cycle with one divisor gives codimension four,
and pushing along a relative-dimension-two projection gives codimension
two on A. Functoriality of the ordinary canonical rational Betti cycle
class map and the projection formula give

\[
 \operatorname{cl}_B(Z)=
 (p_A)_*\bigl(\operatorname{cl}_B(\Gamma)\smile p_B^*\operatorname{cl}_B(D_0)\bigr)
 =c_{D_0}(\operatorname{cl}_B(\Gamma))\ne0.      \tag{6}
\]

Thus Z is a rational algebraic source with a nonzero exceptional Weil
class, conditional only on the stated geometric/standard external
inputs. This uses the ordinary canonical map, not an arbitrary Stage-2G
linear map carrying the same name. The repository has not formalized
the identification with that canonical map.

Choose a finite cycle representative of Z, using proper intersections
or the Chow moving lemma as needed. It is a rational combination of
actual integral surfaces on A. If every surface in its support had
zero exceptional projection, (6) would have zero exceptional projection
by linearity. Therefore at least one genuine integral surface in that
support detects an exceptional direction. This existence argument does
not provide equations for a distinguished surface or an algorithm for
finding the Hilbert-scheme parameters in T6. Z is signed; a nonzero
effective primitive middle cycle would have positive ample degree.

## 5. One source supplies the second exceptional direction

For a=m+u, the actual pullback on W_K(A) has eigenvalues a^4,bar(a)^4.
Writing

\[
 r=m^4-6m^2d+d^2,\qquad s=4m(m^2-d),
\]

its rational matrix is r I+s J_A. Choose m=d+1, so
s=4(d+1)(d^2+d+1)>0. For any nonzero v=(x,y),

\[
 \det(v,a^*v)=s(x^2+dy^2)>0.                \tag{7}
\]

Consequently Z and a^*Z have independent exceptional classes. If a
exists only in End^0(A), choose n>0 with f=n a an actual endomorphism
and replace a^*Z by n^(-4) f^*Z. The isogeny f is finite flat, so
this is a genuine rational codimension-two cycle and has the asserted
degree-four Betti action. Pullback preserves the canonical class.

Together with an ample polarization square, these classes span the
three-dimensional rational middle Hodge space in the very general
case described by the user. This conclusion is relative to T6 and
the geometric operations above. Multiplication by u alone would act
on W_K(A) by u^4=d^2 and would NOT supply a second direction; the
non-real fourth power in (7) is essential, including when d=1.

## Verification and remaining work

`GSTWeilFourfoldAuxiliaryExtraction.lean` proves the graph-lattice
identities, the exact balance/contraction calculation, determinant
padding, and (7), universally over rational d>0 where applicable.
It does not formalize abelian varieties, the exterior-cohomology
dictionary, hyperbolicity via Meyer, Chow operations, T6, or the
canonical Betti comparison. There is no axiom asserting a source
cycle in that Lean file.

The Wolfram script `research/computations/weil_fourfold_auxiliary_extraction.wl`
was evaluated with exact symbolic arithmetic. It independently checks
the graph Gram matrix, the two tensor equalizer equations, the derived
extraction matrix, the padded determinant, and the actual fourth-power
character modulo u^2+d. Computation does not prove algebraicity.

The raw output and version-1 manifest are adjacent to the script. The
Mathbox manifest validator accepted the record with its documented legacy
provenance limits. Input SHA-256:
`322e4592ff058fa8aa06bd18d372debba7f5249dc83ef634722bd4ce70438f36`;
output SHA-256:
`8ccf96065c8f6da4ecadb0385e9daac62f210e63a41c8ca762761f3fa2467cda`.

### Adversarial self-review

Primary verdict: **conditional on the named external source theorem T6**,
with a written geometric extraction and separate arithmetic proofs.

| Obligation | Status and evidence |
|---|---|
| Original A retained | Passed: every auxiliary construction is on A x B; the final projection lands on A. |
| Auxiliary signature and discriminant | Determinant identity proved arithmetically; rational Hermitian hyperbolicity uses the stated external Meyer-based test. |
| Nonzero actual sixfold cycle | Conditional external leaf T6, including its product/all-period clause; never a coordinate consequence. |
| Tensor sector and detector | The character and exterior-product derivation is written; rational contraction and graph arithmetic are in the Lean file. |
| Degree and sign of pushforward | Passed on paper: codimension 3+1-2=2; all crossed cohomological degrees are even. |
| Canonical class comparison | Standard Chow/Betti functoriality used explicitly; not implemented by a freely chosen linear map and not Lean formalized. |
| Independence of two Weil outputs | Actual degree-four K character derived; positive determinant calculation in Lean. |
| Three directions exhaust the generic Hodge space | The generic rank-three premise in the user's target is retained; no analogous assertion for arbitrary special periods. |
| Novel GST-only construction or full geometric Lean proof | Not established. |

As a small independent sign and character check, exact integer arithmetic
at d=1 gives (2+u)^4=-7+24u and r^2+d*s^2=625=5^4. At d=2,3,7 the
same norm invariant was checked, as were orbit determinants for vectors
(1,0),(0,1),(1,-2). These checks support the implementation and do not
extend the theorem's geometric scope. The universal arithmetic claims
are the Lean declarations, not this finite sample.

CI for the new arithmetic: [run 39066130937](https://github.com/kyo-oo/HC-PROOF/actions/runs/39066130937)
**PASSED**, at revision `44fd48497a9be20f3e467fafb12cc167da0bb194`.
All eleven theorem declarations kernel checked. The diagnostic prints
report standard axioms only, with no sorryAx; no geometric source axiom
is declared. Artifact ID `12113695466`, ZIP SHA-256:
`6b21837b493d3320e45e985a0f6f852e0b4e1370785b83e1da09fd257c0162e0`.
The earlier run `39065886210` failed to reduce finite-vector coordinates
in two graph calculations. Direct value definitions repaired those
elaboration failures; the contraction and orbit proofs already passed
in that failed aggregate run. Only the final successful run is the
verification receipt for the complete arithmetic file.

The prior directed native-source construction now has a complete
successful Lean receipt: run `39015742539`, revision
`aa2abbe546a6de367c2d970217627bcf0131a7bb`. Both source geometry and
full residual landing passed with no sorryAx. Its artifact SHA-256 is
`13bb5a37b1ff8c5a3e7e9517888124d32bcaf9179f00350bf03df61adfc29a05`.
It does not establish (2).

The GST-only goal and full geometric Lean verification remain OPEN.
The precise next geometric obligation is to construct the nonzero
sixfold source (2) within GST, or formalize and import T6 with its
canonical cycle-class theorem. The padding/extraction step is no
longer a speculative route; its exact reduction and arithmetic are
written above. No universal all-varieties Hodge theorem follows.


## GPT-6 branch transfer and native proof assembly

Transferred from `mathbox/residual-zero-direct-audit-20261015` at
`94f9f20c4cb73ad37821d324125b4b81e3176318` onto
`research/gpt6-native-point-primitive-span-20261017`, based on
`48955f6be6b61a3dd61c6dded65957855a42e768`.
The extraction arithmetic module and Wolfram evidence are unchanged.
The native assembly extends the existing
`GSTUniversalCMArithmeticObstruction.lean`, preserving its obstruction
theorems and the GPT-6 branch's earlier CM/QM work.

For target coordinates \((a,(u,v))\), write
\(z=\operatorname{contractGraph}(M)=(x,y)\),
\(w=(d+1+u_K)^*z=(r x-d s y,s x+r y)\), where \(u_K^2=-d\).
Set \(D=xw_2-yw_1=s(x^2+dy^2)>0\). The constructed coefficients are
\[
 c=\frac{u w_2-v w_1}{D},\qquad e=\frac{xv-yu}{D}.
\]
The native output on the original fourfold is exactly
\[
 Z_\alpha=a\,\Theta^2+c\,\operatorname{extract}(\Gamma)
                  +e\,\operatorname{cmPullback}(\operatorname{extract}(\Gamma)).
\]
`weilPlaneCramerReconstruction` proves both coordinate equalities.
`auxiliaryWeilNativeCycle` defines this actual rational native cycle;
`auxiliaryWeilNativeCycle_class` proves equality in the supplied rational
Hodge fiber; `auxiliaryWeilEveryMiddleHodgeClass` proves
`H.cycleClass 2 Z = alpha` in the original supplied Betti cohomology.
The determinant is derived from tensor balance and nonvanishing, not
assumed. No source is selected as a function of alpha. This also avoids
misapplying the earlier Q(i) companion formula to a general quadratic K.

### Exact formal inputs and interpretation

| Input | Mathematical instantiation | Lean status in this assembly |
|---|---|---|
| One fixed native codimension-three source Γ | T6 on the padded split sixfold, pure nonzero Weil class | Explicit theorem parameter; T6 is external |
| Native extraction linear map | Intersect with the genuine diagonal difference, then proper pushforward | Explicit map; geometric construction is in this manuscript |
| Balanced nonzero tensor M | K-determinant sector of the source's canonical class | Explicit two balance equations and nonzero condition |
| Native CM pullback | Rationally normalized integral isogeny pullback for d+1+u_K | Explicit native endomorphism |
| Hodge coordinates | Generic decomposition Q·theta² ⊕ W_K(A), not algebraic-cycle spanning | Explicit linear equivalence |
| Three fixed class identities | Polarization, extraction naturality, degree-four CM character | Explicit equalities; independent of the prescribed target |
| H and G | Actual Betti/Hodge data and geometric cycle-class spine | Existing interfaces; canonical geometric instantiation remains required |

The theorem computes a preimage for every target only **after** these
fixed geometric inputs. It does not quantify over geometrically
constructed Weil fourfolds or formalize their dimension, K-action,
canonical analytification, T6 or Chow intersection. The stronger paper
claim follows using the stated external geometry; the Lean result is
its explicit conditional native-cycle assembly. No all-varieties Hodge
claim is made. The completed GitHub integration receipt follows.


### Completed GPT-6 integration receipt

- Transfer commit: `566a66e06bad3a5aa8aad1482b7fcd683090b758`.
- Final mathematical source: `b38695e412291e9b8e271ac0ecc6a2b445257074`.
- Full integration: **[39068146715](https://github.com/kyo-oo/HC-PROOF/actions/runs/39068146715) PASSED**, job `117499985045`.
- Native module blob: `666c04c555be2cffee0857144188143316ae2f87`.
- Build completed successfully: **8961 jobs**, with **264 local modules** registered by the pinned integration root generator.
- All seven pre-existing exact certificate steps passed, preserving the GPT-6 CM/QM results.
- Full log audit: **1719 printed axiom receipts**, union exactly `propext`, `Classical.choice`, `Quot.sound`; no `sorryAx` and no Lean errors.
- All three new theorem receipts (`weilPlaneCramerReconstruction`, `auxiliaryWeilNativeCycle_class`, `auxiliaryWeilEveryMiddleHodgeClass`) individually show only those standard axioms.
- Artifact: `12114465235`, eight logs; downloaded ZIP SHA-256 `a39430bd04f1283eea0a1781838a2dbc2ff96d7c261e150665d4a9498707cec0`, matching GitHub's digest.
- Separate arithmetic verification on this branch: **[39067876686](https://github.com/kyo-oo/HC-PROOF/actions/runs/39067876686) PASSED**, source `566a66e06bad3a5aa8aad1482b7fcd683090b758`, artifact `12114042487`, ZIP SHA-256 `551d38e8b31233f26996db46f154d5f1677206c460e275019df14585c77707d8`.
- The transferred extraction module is byte-identical to the source-branch green module: SHA-256 `fef4a92deb7c345a70a299071e5cdf0b5ea095ee7e1ab1764d5fef04b6d6addb`. The Wolfram script, output and manifest are also unchanged.

The first integration attempt, `39067876668`, failed at two final
coordinate equalities because a restricted simplifier left nested product
scalar actions unreduced. Commit `b38695e` repairs precisely those two
proof lines with scalar-action simplification; no theorem statements,
source hypotheses or cycle formula changed. The universal Cramer identity
already compiled in the first attempt. Only the successful final run is
the verification receipt for the assembled native theorem.

**Completion scope:** the transfer and conditional native-cycle proof
assembly are finished on the GPT-6 branch. T6, the geometric source-to-tensor
dictionary, extraction/CM comparison, the generic Hodge decomposition and
the canonical Betti realization remain the explicit external geometric
inputs listed above. CI does not certify that these inputs have been
constructed in Lean, and does not establish the all-varieties Hodge theorem.


## Unconditionalization attempt at checkpoint f5b69f5

**Requested target:** discharge the displayed geometric inputs of the
GPT-6 assembly and finish the original all-varieties canonical Hodge
statement. **Outcome:** not proved. The green Lean theorem and its
hypotheses are unchanged. No new geometric source or canonical Betti
realization was constructed in this attempt.

The start revision is `f5b69f58a680fe4cde22b06631af850f3b1cbd8d`.
The following are dependencies or attempts on the same Weil-fourfold
construction, not a switch to new families.

### 1. Trace the actual source theorem

The pinned external TeX was acquired again by its Git blob and its
identity checked: blob `d154748feaa7775d2488902ca32f5615e5f4dad6`,
SHA-256 `1ff56b1b900b70df2a8817ae90725f45ae74b267bb1568025bc4bcaa598c1c23`.
The statement and selected construction/deformation passages were read;
this is not a complete independent audit of the external proof.

The relevant chain is `p3sw:seed` (equivariant Abel-curve orbits),
`p3sw:invariant-injectivity` (the full invariant derived obstruction
space), `p3sw:exceptional-character`, `p3sw:projective-germ`,
`p3sw:spread`, and `p3sw:endpoint-all-lattices`.
It constructs sheaves and controls their deformation; an arithmetic
nonzero tensor alone does not implement this chain. The relevant GST
files inspected supply extraction, incidence, coefficient descent and
K0 purification, but do not supply those geometric constructions as
Lean terms. This is an external proof dependency, not an established
internal source constructor.

### 2. Explicit Chern-cycle extraction from the required sheaf

Let X=A×B be the padded sixfold and let E be an actual coherent perfect
sheaf of nonzero rank r. Its normalized third Chern character is
\[
 \kappa_3(E)=\frac{c_3(E)}2
 -\frac{r-2}{2r}c_1(E)c_2(E)
 +\frac{(r-1)(r-2)}{6r^2}c_1(E)^3.                  \tag{8}
\]
To derive this, multiply the Chern character through degree three by
\(\exp(-c_1(E)/r)\). The degree-three coefficient is
\(\operatorname{ch}_3-(c_1/r)\operatorname{ch}_2+c_1^3/(3r^2)\);
substitution of the usual Chern-character polynomials gives (8).
For a line class b, normalization is unchanged by tensoring E with its
line bundle, since \(\operatorname{ch}(E\otimes L)=e^b\operatorname{ch}(E)\).

Thus the genuinely algebraic candidate on the original fourfold is
\[
 Z_E=(p_A)_*\left[
 \left(\frac{c_3(E)}2-\frac{r-2}{2r}c_1(E)c_2(E)
 +\frac{(r-1)(r-2)}{6r^2}c_1(E)^3\right)p_B^*D_0\right].       \tag{9}
\]
The degree is exactly 3+1-2=2. If E has the required normalized
character \(a\theta_X^3+w\), the polarization term is killed by
\(\theta_BD_0=0\), and the existing injective contraction detects w.
Formula (9) makes the needed source concrete, but it does not construct
E with a nonzero Weil component on the required period. Arbitrary
Chern classes or an arbitrary sheaf cannot be substituted for that
source. The external theorem's all-period cycle conclusion also does
not, by itself, assert that its particular seed sheaf extends to every
period as the same ordinary sheaf.

### 3. Test whether the existing elementary operations birth that source

On the generic seven-dimensional even Hodge representation, the
polarization powers occupy five directions and the exceptional Weil
plane occupies two. The stated Lefschetz, Fourier and Adams matrices
preserve the five-dimensional ambient block. Their lower-left blocks
are zero. Products and sums of such matrices have the same property,
by block multiplication, so every word preserves this block, with no
word-length restriction. Starting from 1, the five vectors L^k1,
0≤k≤4, span exactly that block. A CM action confined to the Weil plane
does not move an ambient seed into it.

This rules out source creation by this particular generator family;
it is not an exhaustion of the GST library or all algebraic operations.
The seven-dimensional calculation is a formal representation check,
not a newly constructed Betti realization.

There is also no direct quaternionic anti-K endomorphism available in
the generic endomorphism algebra K itself. In its rational regular
representation, write
\[
 J=\begin{pmatrix}0&-d\\1&0\end{pmatrix},\qquad
 R=\begin{pmatrix}a&-db\\b&a\end{pmatrix}.
\]
Then RJ=JR, while RJ+JR=0 forces a=b=0 when d≠0. This excludes copying
the QM graph isogeny as an endomorphism of a fourfold with End^0(A)=K;
it makes no assertion against other algebraic surfaces or correspondences.

### 4. Canonical realization remains a separate obligation

`AnalytificationData` stores a topological space and a bijection with
complex scheme points. `HodgeBigradedBettiData` still stores a Hodge
bigrading and a cycle-class map. The point-generated construction
linearly extends the supplied point-class values; it does not construct
their analytic fundamental classes. In particular,
`suppliedPointBettiClass` is defined from H.cycleClass itself.
The existing `arbitrary_cycleClass_semantics_cannot_be_final_target`
theorem supplies the zero-map obstruction to deleting this distinction.
That semantic obstruction concerns unconstrained data, not the actual
canonical Hodge conjecture. An unconditional result must instantiate
these objects by the genuine geometry.

### Computation and continuation

Wolfram verified (8), its line-tensor invariance, the quadratic
centralizer calculation, and the stated block/rank checks with exact
arithmetic. Reusable script, output and manifest:
`research/computations/weil_source_construction_frontier.{wl,output.txt,manifest.json}`.
Input SHA-256 `78943940eae18a2cfe7ce7523364791db690fe1d7d2c4b3e93daf6affc3b7bcb`;
output SHA-256 `1df46c0ed236706d1d5d6413557d8233ef346339f68cad6c2f72a2ac61338e1d`.
The version-1 evidence validator passed with its documented provenance
limits. An initial matrix-power implementation aborted at exponent
zero for a singular matrix; the final successful run uses direct
successive matrix-vector multiplication.

The source-construction route stays **open**. The deferred work is to
implement the actual geometric seed and its all-period deformation/spread,
or supply an independently proved replacement source, together with
canonical class comparison. The first geometric construction to implement
is the seed, not a new existential certificate containing an assumed Γ.
No ordinary-sheaf construction, semiregularity theorem or all-period
source was proved by this attempt. No Lean source was edited and no new
Lean CI was triggered: the previously green assembly remains exactly as
verified. Even a completed Weil-fourfold formalization would not by
itself supply cycles on arbitrary smooth projective varieties.


## Source construction executed after the audit checkpoint

The next checkpoint now contains actual construction work:
[Direct smooth secant seed and its explicit exceptional character](2026-10-18-direct-smooth-secant-seed-and-character.md).
It constructs the required orbit ideals and ordinary rank-8d sheaf at
a smooth Jacobian seed, derives a genuine nonzero Weil Chern cycle, and
supplies 25 new Lean source-construction lemmas plus an exact exterior
calculation. The complete integration is green at `2a5c980`, run
[39071168177](https://github.com/kyo-oo/HC-PROOF/actions/runs/39071168177).
The new manuscript distinguishes the seed construction from all-period
transport and from full geometric Lean realization. The earlier audit's
statement that no Lean source was edited describes only its earlier
`f5b69f5` attempt, not this later construction checkpoint.

## Seed-to-every-period continuation, 2026-10-18

[The new transport and original-fourfold proof](2026-10-18-weil-all-period-transport-and-original-fourfold.md) expands the previously unexpanded T6 dependency. It reconstructs the full invariant obstruction argument, finite descent, ordinary sheaf conversion, actual local deformation, proper Hilbert/Baire spread and all-lattice isogeny step from the exact pinned source and the directly constructed smooth seed. It includes product periods, so applies to the particular padded original A in this record. Its explicit Hilbert-fiber cycle and the extraction above supply the requested source at manuscript level. The exact cochain minor is n^42 and the same explicit d+1+u generates the second Weil direction in both relevant dimensions. The new Lean period-spread entry point is connected to the native three-direction assembly. Complete actual analytic/derived geometry and canonical realization in Lean remain explicit obligations; this historical record's earlier CI receipts are not reinterpreted as that formalization.
