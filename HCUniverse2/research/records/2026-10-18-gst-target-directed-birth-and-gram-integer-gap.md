# Mathbox: target-directed GST native birth and an intrinsic integral Gram energy gap

- **Date:** 2026-10-18
- **Kind:** research attempt and exact mathematics
- **Program/route/claim IDs:** Original all-varieties rational Hodge target, Gate 3; GST target-coupling and integer-Gram energy law
- **Base checkpoint:** ca7f988b2edeee2614ea2e89e8d6bf80faaeee42, branch research/gpt6-native-point-primitive-span-20261017
- **Target:** For every original smooth projective complex X, each p, every rational (p,p) alpha, independently construct Z_alpha in CH^p(X)_Q with the canonical Betti equality cl_X(Z_alpha)=alpha. **NOT PROVED.**
- **Hypotheses and types:** Rational native codimension-p cycle spaces; genuine canonical rational Betti cycle classes; a rational signed Hodge–Riemann polarization positive on the chosen primitive (p,p) fiber; old genuine native basis, its true rational intersection Gram, and actual rational target alpha.
- **Conventions:** For primitive (p,p) of degree 2p in a smooth projective n-fold with 2p<=n, use the positive signed primitive form Q(x,y)=(-1)^p integral_X x∪y∪h^(n-2p). For general Hodge fibers first perform the rational Lefschetz decomposition and sign choice piecewise. Integral statements apply only after clearing alpha's denominator and the projection coefficients.
- **Current evidence:** The exact new target-coupling and optimal energy identities compiled in [GitHub CI #39118709619](https://github.com/kyo-oo/HC-PROOF/actions/runs/39118709619). The first exact fixed-denominator gap compiled in [#39118931417](https://github.com/kyo-oo/HC-PROOF/actions/runs/39118931417). The determinant-normalized strengthening was written into the same Lean file, with CI receipt to be checked at commit c9c12237f1101e481b0f663a3317a7b61e9c1c10. No claim of canonical global Betti infrastructure beyond the actual supplied GST geometric comparisons is promoted.
- **Nearest prior attempt:** Arbitrary world birth, native trace-zero surgery and Gram surplus could only certify an independently constructed class Z, not optimize towards a PRESCRIBED alpha.
- **Route:** Construct a target-specific readout directly from GST's canonical residual and positive polarization; take a native algebraic cycle Z of nonzero coupling and apply the exact optimal rational coefficient. Separately exploit the integer geometry of genuine intersection Gram matrices to turn a sufficiently small error into a rigorous exact statement in ONE finite step.
- **Success criterion:** A concrete original-X native source Z for every nonzero target residual, with its verified nonzero coupling and denominator-controlled improvement; show exact residual zero and canonical Chow class without assuming target algebraicity.
- **Failure/no-go criterion:** A positive residual with zero intersection against every genuine native class, or coefficient denominators growing so fast that the normalized arithmetic gap never closes.
- **Cheapest decisive check:** Cubic fourfold containing an actual plane, Q-Gram [[3,1],[1,3]], old h², target [P]. Then r=(-1/3,1), Q(r,r)=8/3, coupling with [P] is 8/3, self-norm of [P] is 3, optimal coefficient 8/9, corrected residual (-1/3,1/9), energy 8/27. Wolfram exact checks returned these rational values.

## 1. A target-directed geometric BIRTH law, not an arbitrary sheet operator

Fix genuine already-constructed algebraic native classes z_1,...,z_s on the ORIGINAL X; let G_{ij}=Q(cl z_i, cl z_j) be nondegenerate. The rational Gram-dual projective source is

\[
 Z_{\rm old}(\alpha)=\sum_{i,j}(G^{-1})_{ij}\,Q(\alpha,cl(z_j))\,z_i.
\]

The remaining GST Hodge class r=alpha-cl(Z_old(alpha)) satisfies Q(r,cl z_i)=0 for every i. (This identity and its positive-energy Pythagoras are kernel-verified in the existing GST modules.)

Now find an ACTUAL new algebraic codimension-p cycle Z on X with z=cl(Z) and

\[
 \boxed{Q(r,z)\ne0.}
\]

This geometric coupling constructs the *independent readout* x↦Q(r,x) without a chosen third coordinate. Since it kills all existing classes but not z, z strictly increases the OLD algebraic Hodge span. The new Lean theorem is target_residual_coupling_constructs_native_rank_birth; ActualXCycleProjectionData.target_directed_gram_coupling_birth specializes it to true original-X Mathlib rational cycles.

If Q(z,z)>0, rational geometric intersection data produce the explicit optimal coefficient

\[
 t=\frac{Q(r,z)}{Q(z,z)},\qquad
 \boxed{Q(r-tz,r-tz)=Q(r,r)-\frac{Q(r,z)^2}{Q(z,z)}<Q(r,r).}
\]

This is NOT a theorem constructing the missing Z from alpha. It is a precise law for an independently constructed Z and the actual target, with a strict measurable outcome rather than a postulated abstract GST nonzero determinant.

## 2. Stronger arithmetic exactness: integral Schur Gram gap

Let alpha be an INTEGRAL primitive Hodge class. Let the old native classes z_i be integral primitive algebraic cohomology classes (or multiply every rational input by a common denominator first), and assume G positive definite with g=det(G)>0. Define integer intersection row b_i=Q(alpha,z_i) and integer c=Q(alpha,alpha). The augmented Gram matrix

\[
\widehat G=\begin{pmatrix} G & b\\ b^{\mathsf T} & c\end{pmatrix}
\]

has an INTEGER determinant m>=0. The residual of the true Gram-orthogonal projection is

\[
r=\alpha-\sum_{i,j}(G^{-1})_{ij}b_j\,z_i.
\]

Block row/column elimination gives an exact mathematical proof:

\[
\widehat G
 \begin{pmatrix}I &-G^{-1}b\\0&1\end{pmatrix}
=\begin{pmatrix}G&0\\b^{\mathsf T}&c-b^{\mathsf T}G^{-1}b\end{pmatrix}
\]

and the right multiplier has determinant one. Hence

\[
\boxed{g\,Q(r,r)=\det\widehat G=m\in\mathbb Z_{\ge0}.}
\]

It follows with no guessed denominator that

\[
\boxed{Q(r,r)=0\quad\text{OR}\quad Q(r,r)\ge1/g.}
\]

For rational target alpha of minimal cohomological denominator N, multiply by N and obtain the corresponding gap 1/(g N²) for the original alpha. There is no extra Hodge-surjectivity hypothesis in this arithmetic derivation. The old native projective basis G and the integer target cohomology are geometrically given, and the exact determinant relation holds universally for such input data.

The new Lean theorem gram_determinant_gap_exactness verifies the integer-to-zero inference from g*energy=m and energy<1/g; geometric_gram_determinant_gap_constructs_exact_native wires that to the actual native residual decomposition. The full all-rank BLOCK determinant theorem and canonical Chow/Betti integration still need full native formalization; the mathematical block argument here is a complete elementary proof.

**Exact Wolfram audit:** symbolic 2-source G=[[a,b],[b,c]], coupling v=(u,v), target norm d gives

\[
\det\widehat G=acd-b^2d-cu^2+2buv-av^2
=\det(G)(d-v^{\mathsf T}G^{-1}v).
\]

Wolfram simplified the symbolic difference to zero under detG!=0. Exact 3-direction integer Gram matrix [[3,1,0],[1,3,1],[0,1,3]] has augmented determinant 21, old determinant 8, residual energy exactly 21/8. All these are finite consistency checks of the independent general proof.

## 3. Crucial adversarial test: rational descent alone does not cross the gap

In the cubic fourfold lattice Q=[[3,1],[1,3]], old H=h², target [P], old Gram determinant g=3. The genuine rational residual is r=(-1/3,1), with energy 8/3 and canonical scaled determinant g*energy=8 (integer, not <1).

The first greedy correction by the actual native [P] uses t=8/9, gives r'=(-1/3,1/9), and reduces energy from 8/3 to 8/27. But the minimal coefficient denominator rises from 3 to 9: the fixed-D normalized squared energy stays 24. Precisely, 3²*(8/3)=24 and 9²*(8/27)=24. **Thus strict energy descent, even with real algebraic geometry, does not by itself force the integer quantum gap to close.**

A second universal adversarial model is the rational vector r_n=(1/n,0) in a positive integral Gram lattice. Energy tends to zero as 1/n² but denominators are n, so D_n² E_n=1 forever; not one finite step is exact. A successful GST quantization strategy must control the actual Gram determinant of the GROWING algebraic source basis or deliver a fixed denominator via independent geometry.

## 4. Mathematical boundary: new-world geometry must produce coupling

Suppose a finite-dimensional true primitive Hodge fiber V has native cycle-class image A⊊V. Its positive rational polarization gives nonzero r∈A^perp. For EVERY actual native cycle Z, Q(r,cl Z)=0, because cl Z∈A. Therefore the universal source-coupling assertion

\[
\forall 0\ne r \ \text{of this type},\quad
 \exists\, Z\in CH^p(X)_{\mathbb Q}:\ Q(r,clZ)\ne0
\]

is **not derivable merely from positivity, Gram invertibility, world-birth syntax, or algebraic-cycle closure**. Adding it without independent geometric construction would assume precisely the missing Hodge spanning statement. The abstract finite model V=Q², native N=Q, cl(n)=(n,0), standard positive Q, alpha=(0,1) satisfies all the elementary rational energy laws and has r=(0,1), but no native coupling. It is NOT a counterexample to Hodge on a genuine smooth projective X; it is a valid test that energy-and-birth formalism alone cannot force source existence.

**Candidate GST geometric upgrade (UNPROVED, NOT an axiom):** use target-born exceptional algebraic incidence from genuine projective geometry of X, and prove that its positive integral intersection Gram with r has nonzero coupling. The existing Hilbert/CM/NM, semiregularity and projective-source modules supply tools to investigate it; neither positive energy nor quantization alone provides the required incidence.

## 5. Attempt result, scope, continuation

- **Attempt outcome:** two exact new rational laws established: target-directed native energy descent and integer Schur determinant quantization; universal source existence NOT established.
- **Evidence label:** proved for the exact rational linear geometry (Lean kernel receipts), mathematically proved block determinant identity, computationally verified for stated Wolfram inputs. Any claim of universal prescribed-alpha algebraic birth remains **open**.
- **Route disposition:** open; continue source-specific geometric incidence, not repeated linear remappings.
- **Review:** self-review with countermodels and denominator-growth tests; no independent geometric full-Hodge proof audit passed.
- **First unresolved implication:** construct, FOR EVERY arbitrary original X,p,primitive alpha with positive residual, a genuine source cycle Z with Q(r_alpha,clZ)≠0 and enough geometric control to eliminate residual in at most finite rank.
- **Strongest surviving statement:** If such cycles can be constructed, the target-directed Gram law gives finite strictly growing native rank; if the residual energy is below its integral Gram gap, one native original-X cycle already realizes alpha exactly. These remain conditional on INDEPENDENT source construction.
- **Next experiment:** fixed difficult nonsplit Weil fourfold: compute the actual projected exceptional primitive coupling for one newly constructed Hilbert/sheaf geometric source, rather than supplying its nonzero Weil projection as a hypothesis. Use the true Hilbert incidence, CM graph, and native integral pairing from repo; do not substitute a freely selected Hodge endomorphism.
- **Artifacts:** GSTPolarizedHodgeResidualEnergy.lean and GSTActualXHodgeResidualProjection.lean (existing modules edited in place), Mathematica exact symbolic calculations, GitHub Actions receipts above. No local Lean installation, no public web search.
