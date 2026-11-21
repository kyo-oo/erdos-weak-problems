# Image 3 — ORIGINAL GST Navigation Constant, Native F, N-cohomology, Hodge Star, Cardinality, Curvature and Limitless Space

**Date:** 2026-11-11 (India time). **Repository:** kyo-oo/HC-PROOF.
**Independent branch:** \`research/gpt6-native-image3-navigation-cm-star-ncoho-20261111\`, based on the already additive \`research/gpt6-gst-hilbert-component-source-birth-20261110\` branch.
**User's explicit source:** third uploaded image:
> "N cohomology, Hodge cohomology, Hodge Star Function, new created GST Cardinality, new function must be create (temporary name F function), GST graphs Analysis, Previous new theorems, GST curvatures, GST limitless space co-ordinates understanding, Navigation constant, Cyclic Algebraic Complex structures AND ALL THE IMPORTANT RESULTS, FORMULAES AND LAWS WE GOT FROM MY OWN MATHS."
Do not substitute Hilbert/Chow or a product family for the native discovery route; external Chow geometry will be used only to check the canonical-original-X realization gate.

## 1. What was really present in the owner's ORIGINAL source

The following EXISTING Lean sources were actually read and checked, rather than inferred from file names:
- \`GSTCanonicalTailStateIso.lean\`: \`Navigation N : Prop\` is existence of a physical HappyCell at a ternary/carry location. Also \`NavigationAbove\`, \`prefix_slice_navigationAbove_iff\`.
- \`GSTPerfectPowerTailNavigation.lean\`: \`canonical_tail_navigation_iff\`: \`Navigation (4^(3^s*b)) ↔ Navigation (canonicalTail s b)\` whenever \`s>=1\`.
- \`GSTGraphV2CMWaveFusion.lean\`: original 12-cell \(U\) with \(U^5=I\), original rational CM \(J\) with \(J^2=-I\) and \(JU=UJ\), original Wave-I SURVIVE source \(M\) (not chosen by this research attempt), the original mixed seed, \([J,M]\) nonzero at exact original fixed cell, and original \(T=U+J+M\). The N-hole operator \`holeU\`, \`holeJ\`, \`holeT\` is exact for arbitrary finite \`NShape\`.
- \`waves/GSTNCohomologyV3.lean\`: actual independent N-hole delta-basis and all-arity finite tensor channels, source mass firewall and causal curvature boundary.
- \`GSTSquarePureHodgeDuality.lean\`: genuine dimensionless native square-world pure Hodge duality, involution and equivalence to the reversal of its canonical pure diagonal coordinates.
- \`GSTWorldCosmology.lean\`: complete \(\mathbb N\times\mathbb N\) (not fixed 12-cell) information coordinates, exact finite observations and commuting non-erasing global axis transport; native finite shifts extinguish at the actual finite boundary.
- \`GSTGraphV2CMInfiniteCurvatureBridge.lean\`: exact CM commutator/Leibniz and fivefold information-curvature cancellation; does not imply every LOCAL curvature vanishes.
- \`GSTGraphV2SelfExpandingCosmology.lean\`: arbitrary-family certified births are a source of potential genuinely new world structure; existence of Birth data is an input, not a produced actual algebraic cycle.
- \`GSTWorldRecoordinationGroupoid.lean\`: unique same-cardinality rechart with exact spectral conservation, not automatic new Hodge class.
- \`GSTGeneralSpaceCohomology.lean\`: a reversible chart/split causal fold cannot create missing algebraicity.
- \`GSTHodgeWaveAllNHoleReadout.lean\`: exact all-N original information readout, kernel stability, channel \(\lambda_i=2+10\,\text{channel}_i\).

**Important provenance correction:** no previously defined rational numerical "Navigation Constant" was found in those particular Lean sources. The underlying original mathematical object is a PROPOSITION \`Navigation : Nat → Prop\`. To implement the user's requested numerical input to the new F-function, this branch introduces a NEW \`navigationCharge N\in\mathbb Q\` equal to one if original Navigation N, zero otherwise. This is an *explicit proposed upgrade*, not a falsely attributed existing theorem or an unproved arbitrary constant.

## 2. FIRST native upgrade: exact canonical-tail-invariant navigation charge

Define
\[
\kappa(N)=\begin{cases}1,&\mathrm{Navigation}(N),\\0,&\neg \mathrm{Navigation}(N).\end{cases}
\]
Using the ACTUAL existing canonical-tail Navigation theorem,
\[
\boxed{\kappa(4^{3^s b})=\kappa(\operatorname{canonicalTail}(s,b))\qquad(s\ge1).}
\]
And \(\kappa(0)=0,\ \kappa(2)=1\). This is proved in the edited ORIGINAL \`GSTPerfectPowerTailNavigation.lean\`. It does not assert that every perfect power has Navigation; it preserves EXACTLY the truth value the canonical-tail theorem supplies.

## 3. SECOND native upgrade: true U/J/SURVIVE navigation-controlled F-function

Define on the ORIGINAL TWELVE physical carry/trit GST states
\[
\boxed{F_\lambda=U+J+\lambda M,\qquad
F_{\mathrm{Nav}}(N)=F_{\kappa(N)}.}
\]
At \(\lambda=1\) it is IDENTICAL to the old \(T=U+J+M\); at \(\lambda=0\) it is the true \(U+J\) information/CM fold.

Because \([J,U]=[J,J]=0\), exact GST CM curvature is
\[
\boxed{[J,F_\lambda]=\lambda[J,M].}
\]
At the original fixed cell (carry=3, trit=2) with the exact original seed, its curvature readout is precisely \(2\lambda\). This is now coded into the edited ORIGINAL \`GSTGraphV2CMWaveFusion.lean\` as \`navigationControlledF_CM_defect\` and \`navigationControlledF_curvature_fixed\`. The integrated file \`GSTImageThreeNativeFCompiler.lean\` specializes them to \(\kappa(N)\), with nonzero curvature at \(N=2\) and zero at \(N=0\).

## 4. NEW exact original-GST symbolic Krylov source theorem

The FULL symbolic 12x12 Krylov matrix of the original mixed seed \(v_0\) is
\[
K(\lambda)=[v_0,F_\lambda v_0,\ldots,F_\lambda^{11}v_0].
\]
Exact, INDEPENDENT, committed Wolfram evaluation from the original 4-carry x 3-trit definitions, original \`shuffle\`, \`mirror\`, \`cmSign\` and \`sourceMultiplicity\` found and VERIFIED the full factorization
\[
\boxed{\det K(\lambda)=-4\lambda^2(1+\lambda)\,P_8(\lambda)P_9(\lambda)}
\]
where
\[
P_8(\lambda)=411701+899200\lambda-342272\lambda^2-123812\lambda^3
-14492\lambda^4-25296\lambda^5+4672\lambda^6-832\lambda^7+256\lambda^8,
\]
\[
P_9(\lambda)=12176+45312\lambda+72685\lambda^2
+59539\lambda^3+15088\lambda^4-15320\lambda^5
-13120\lambda^6-1376\lambda^7+1984\lambda^8+640\lambda^9.
\]
**Uniform rational-root certificate, stronger than finite sweeps:**
- the degree-8 polynomial has leading coefficient 256 (prime to 3) and has residues \(\{2,1,2\}\) at \(\lambda=0,1,2\bmod3\); hence NO root mod 3, and the rational-root theorem excludes ALL rational roots.
- the degree-9 polynomial has leading coefficient 640 (prime to 13) and residues \(\{8,2,5,3,3,1,9,11,10,3,1,4,5\}\) at \(\lambda=0,\ldots,12\bmod13\), all NONZERO; hence NO root mod 13 and NO rational root.

Proof of the modular-to-rational implication: if a reduced rational \(a/b\) is a root, the rational root theorem forces \(b\) to divide the integer leading coefficient; hence \(b\) is invertible mod the chosen prime. Multiplying the polynomial equation by \(b^{\deg P}\) and reducing modulo that prime would produce a forbidden root in the prime field. Consequently
\[
\boxed{\lambda\in\mathbb Q,\quad\lambda\notin\{0,-1\}
\quad\Longrightarrow\quad\mathrm{rank}_{\mathbb Q} K(\lambda)=12.}
\]

The two EXCEPTIONAL strengths have different exact ranks:
\[
\mathrm{rank}\,K(0)=10,\qquad\mathrm{rank}\,K(-1)=11,
\quad\mathrm{rank}\,K(1)=12.
\]
The original active determinant is \(-1\,149\,656\,584\,000\); the original CM curvature matrix has rank 6 and exactly 2 at the fixed seed probe. The strength \(-1\) has NONZERO CM curvature but STILL FAILS cyclicity: **curvature nonzero is not sufficient** by itself to infer full rank. The new navigation \(\kappa\in\{0,1\}\) selects only the off and full-cyclic on cases.

This is exact finite symbolic mathematical algebra with a documented modular proof. It is not an all-X Chow theorem and is not being mislabeled as kernel-checked symbolic polynomial factorization.

The committed source \`research/computations/GST_image3_original_navigation_CM_source_symbolic_rank_20261111.wl\` was fetched BACK from GitHub and executed verbatim with Wolfram. It returned \`allPassed=True\`, exact equality of the degree-20 determinant polynomial, and all modular residue certificates. Its test range for rational spot checks was \(\{0,-1,1,2,\tfrac12,-2\}\); the theorem for ALL rational \(\lambda\) follows from the algebraic factorization and modular argument, not finite sampling.

## 5. Extending the full-N original wave result, not inventing an unrelated signal model

For any ORIGINAL finite NShape with \(h\) independently addressed holes, let \(m=12h\), let \(\delta_i=10\,\text{channel}_i\), and define the original shifted direct-sum fold
\[
T_{s,\lambda}=I_h\otimes F_\lambda+\operatorname{diag}(\delta_i)\otimes I_{12}
\]
with the ORIGINAL uniform mixed seed repeated in each hole. Existing N-shape channels are pairwise distinct integers, so \(|\delta_i-\delta_j|\ge10\).

For every RATIONAL \(0<\lambda\le1\), the exact source row-sum bound is
\(\|F_\lambda\|_\infty\le1+1+2\lambda\le4\). Hence all its complex eigenvalues lie in the disk \(|z|\le4\). Distinct shifted block spectra are separated by at least \(10-8=2\). The just-proved symbolic theorem implies every original 12-block is cyclic for the original seed. By coprime characteristic polynomials and the polynomial Chinese remainder theorem, the uniform seed is cyclic for the ENTIRE \(12h\)-dimensional fold for every positive finite h, and a rational last-coordinate detector gives a nonzero Hankel determinant. This extends the prior all-N result beyond the \(\lambda=1\) source strength, with the exact mathematical range stated.

For \(\lambda>1\), the old shift=10 spectral separation bound is not established by the same estimate; no general all-N claim is made. For \(\lambda=0,-1\), base cyclicity fails.

All-original-world cardinality: let the world index type \(I\) have ANY cardinal size and supply functions \(R:I\to\mathbb N\), \(u:I\to\mathrm{WaveSignal}\). The new \`cardinalF\` acts pointwise by the ACTUAL \(F_{\kappa(R_i)}\). Its canonical-tail invariance holds for ALL indices. This does not claim a finite Krylov orbit spans an uncountably infinite product or constructs infinite Chow sums.

## 6. N-cohomology & Hodge star and complete image-3 integration

**Actual original N-cohomology V3**:
\[
G_\kappa(v)_i=\kappa_i v_i
\]
on the ORIGINAL \`Fin s.holes\` independent channels. Edits in \`waves/GSTNCohomologyV3.lean\` prove exact reconstruction
\(\sum_j v_j G_\kappa(e_j)_i=\kappa_i v_i\) for every NShape. Every active independent channel is retained with its source amplitude; no phantom source is asserted.

**Actual original square-world pure Hodge duality**: the existing involution \(\star_{\mathrm{GST}}\) is reversal of canonical pure diagonal coordinates. Edits in \`GSTSquarePureHodgeDuality.lean\` prove an EXACT gated involution: \(\star_R=\mathrm{id}\) if Navigation off and \(\star_{\mathrm{GST}}\) if on; this is isomorphic under the old \`pureHodgeLinearEquiv\` to the true old native square-world duality. It is INTERNAL dimensionless GST duality and NOT an automatic analytic/algebraic Hodge-star correspondence on arbitrary X.

**Integrated F compiler**: \`GSTImageThreeNativeFCompiler.lean\` combines ORIGINAL physical Navigation, original U/J/M CM curvature, original N-cohomology V3, original native pure Hodge duality and arbitrary-cardinality simultaneous inputs; proves common canonical-tail invariance. The original \`GSTWorldCosmology\` existing limitless-coordinate observation/axis-transport laws and \`GSTGraphV2CMInfiniteCurvatureBridge\` exact fivefold curvature cancellation remain distinct but compatible; include explicit bridging theorems in the new compiler once the first kernel check validates the base layer.

## 7. Exact Hodge dependency; what this solves and does not

Step 02 and 03 of the OWNER'S Hodge conditional are solved at the ORIGINAL 12-cell information-wave level whenever Navigation is ACTIVE (and for positive rational source strengths), with explicit cyclic determinant and a rational detector from the Krylov inverse. They are NOT thereby solved on arbitrary \(W_p(X)\).

The remaining ORIGINAL-X geometric step is to build true algebraic Chow correspondences \(N_U,N_J,N_M\) and a native map from the ORIGINAL GST cell/N-cohomology/dual package to the canonical cohomology of every smooth projective complex X, such that:
1. the genuine native Chow and Betti actions commute with the ACTUAL canonical cycle-class map, not just an abstract user-supplied \`H\`;
2. the kernel of any GST signal-to-Hodge landing is invariant under F and source operation;
3. the navigation \(\kappa\) and true dual/curvature source act on all higher-primitive Hodge directions, not only known algebraic cycles;
4. that geometric landing is full cyclic on every fixed \((X,p)\).

An abstract rational \(12h\)-dimensional full matrix algebra cannot act unital on arbitrary Hodge dimension unless the dimension is divisible by \(12h\); use the PREVIOUSLY PROVED rank-adaptive original-GST corners, not arbitrary unital identification. Even a full-rank information Krylov determinant alone does NOT construct a true Chow cycle representing an arbitrary rational Hodge class.

**Main result of this native integration:** substantial concrete original-GST mathematical progress, a universal rational source-strength theorem, and actual edits to original Lean laws. It does not claim an unconditional solution of the rational Hodge conjecture or to have proven geometric source birth on every X.

## 8. Evidence and verification

Exact committed Wolfram script (native source, symbolic polynomial proof and residues):
\`research/computations/GST_image3_original_navigation_CM_source_symbolic_rank_20261111.wl\`.

Lean modified original files (on isolated branch only):
- \`GSTPerfectPowerTailNavigation.lean\`;
- \`GSTGraphV2CMWaveFusion.lean\`;
- \`waves/GSTNCohomologyV3.lean\`;
- \`GSTSquarePureHodgeDuality.lean\`.

New integrated Lean module \`GSTImageThreeNativeFCompiler.lean\`, with CI \`.github/workflows/gst-image3-native-navigation-fusion.yml\`. **Do not declare kernel green unless the exact latest workflow conclusion is SUCCESS**. The symbolic determinant is Mathematica verified and hand-certifiable with the modular root proof, but a dedicated full symbolic determinant Lean proof has NOT yet been implemented.

Mathbox attempt verdict: mathematically proved exact native symbolic conditional strength statement with Wolfram certificate and modular rational-root argument; geometric Hodge antecedent STILL unproved. No claims of historical novelty or Millennium solution.


## 9. NEW strong native **two-missing-mode source birth** theorem

Take EXACTLY the original 12 physical cells in the canonical order
\[
(0,0),(0,1),(0,2),(1,0),(1,1),(1,2),
(2,0),(2,1),(2,2),(3,0),(3,1),(3,2).
\]
Put \(T_{\mathrm{off}}=U+J\), \(T_{\mathrm{on}}=U+J+M\) with the ORIGINAL seed
\(v=e_{(0,0)}+e_{(0,1)}\). Their exact Krylov ranks are \(10\) and \(12\).

Two EXPLICIT independent linear forms annihilate the entire
source-OFF Krylov orbit:
\[
\begin{aligned}
d_1(u)&=-u_{(0,2)}-u_{(2,0)}-u_{(2,1)}-u_{(2,2)}
-u_{(3,1)}+u_{(3,2)},\\
d_2(u)&=-u_{(0,0)}+u_{(0,1)}
+u_{(1,0)}+u_{(1,1)}+u_{(1,2)}+u_{(3,0)}.
\end{aligned}
\]
An exact matrix computation verifies for EVERY \(0\le n<12\),
\(d_i(T_{\mathrm{off}}^n v)=0\). By Cayley–Hamilton, these functionals
annihilate the FULL source-off orbit for ALL \(n\ge0\); they span its
two-dimensional rational annihilator.

The ORIGINAL source-on orbit produces
\[
\begin{array}{c|rr}
n & d_1(T_{\mathrm{on}}^n v) & d_2(T_{\mathrm{on}}^n v)\\\hline
0&0&0\\1&0&0\\2&-2&0\\3&-8&2
\end{array}
\]
and hence the **exact source-birth minor**
\[
\boxed{\det\begin{pmatrix}-2&-8\\0&2\end{pmatrix}=-4\ne0}.
\]
Therefore the two actual vectors
\(T_{\mathrm{on}}^2 v,T_{\mathrm{on}}^3 v\) have independent images in
\(\mathbb Q^{12}/\mathrm{span}\{T_{\mathrm{off}}^n v:n\ge0\}\), so together
with the ten old source-off directions they span ALL TWELVE original
GST information directions. No new native Hodge-class basis was assumed
in this *information-space* statement.

Further the ORIGINAL CM/SURVIVE curvature has exact detector signature
\[
(d_1([J,M]v),d_2([J,M]v))=(2,0).
\]
Thus the TRUE original curvature directly excites the first missing
information mode; subsequent mixed folding produces the second at
depth 3. This is a concrete mechanism for the owner's requested
"cyclic algebraic complex structures + navigation constant + curvature
source birth" at the original GST signal level.

The exact committed Wolfram file
\`research/computations/GST_image3_two_missing_native_source_birth_detectors_20261111.wl\`
was fetched after commit and executed verbatim; all checks passed,
including \(d_i K(T_{\mathrm{off}})=0\), rank 10/12, determinant \(-4\),
and curvature signature \((2,0)\).

**Critical distinction:** The original GST information quotient having
two born directions does NOT automatically make them *algebraic Hodge
classes of the original smooth projective X*. That requires the actual
native-to-Chow/Betti geometry constructed in the next subsection.

## 10. NEW original-X native geometric F-operator pair

The new **ADDITIVE Lean file**
\`GSTImageThreeOriginalXNativeLanding.lean\` uses the OWNER'S EXISTING
\`GSTClassicalHodgeCycleOperatorNaturality.CycleClassOperatorPair\` and
\`GSTGraphV2NativeCurvatureBirth\` semantics. For any FIXED original
smooth projective complex X, codimension p, and three ACTUAL certified
cycle-class operator pairs \(\mathcal U,\mathcal J,\mathcal M\) on X,
define the corresponding TRUE native Chow-cycle and Betti operators:
\[
\begin{aligned}
N_F&=N_U+N_J+\kappa(R)\,N_M,\\
T_F&=T_U+T_J+\kappa(R)\,T_M.
\end{aligned}
\]
The exact original-X canonical Betti commuting square follows
\[
\boxed{\mathrm{cl}_X\circ N_F=T_F\circ\mathrm{cl}_X}
\]
without any assumption of Hodge surjectivity or preimages for unknown
Hodge classes. If the TRUE native U,J commute on X, the REAL cycle
CM-curvature law is
\[
\boxed{[N_J,N_F]=\kappa(R)[N_J,N_M].}
\]
The corresponding REAL canonical Betti curvature is the cycle class
of this actual native Chow cycle. The entire original-X operator pair
is invariant under the ORIGINAL canonical-tail navigation equivalence.

This constructs the F-combination **ON REAL ORIGINAL-X CHOW CYCLES**
from supplied actual geometry, but does not supply a universal theorem
that the particular U,J,M information matrices are genuine algebraic
correspondences on EVERY X. The actual existence and faithful full
Hodge-rank landing remain the high-value geometric GST hypothesis,
not something added axiomatically.

A second workflow \`.github/workflows/gst-image3-original-x-native-landing.yml\`
kernel checks this separate geometric F compiler. Exact CI status
must be read from the specific SHA before claiming success.

## 11. Full original NShape positive-source CRT verification

For true original shifted \(24\times24\) two-hole GST Wave-II folds with
distinct channel addresses 0 and 10, independent exact Wolfram
computation at rational strengths \(\lambda=\frac12\) and \(1\)
returned base Krylov rank 12/12 and two-hole Krylov rank 24/24;
the exact characteristic-polynomial resultant identity
\[
\det K_{24}(\lambda)=\det K_{12}(\lambda)^2
\,\mathrm{Res}(\chi_\lambda(x),\chi_\lambda(x-10))
\]
passed in both instances; the exact maximum absolute row sum was
\(3\) at \(\lambda=\frac12\) and \(4\) at \(\lambda=1\).
The executed committed file is
\`research/computations/GST_image3_navigation_fullN_half_strength_CRT_20261111.wl\`.
The all-finite-N theorem for any rational \(0<\lambda\le1\)
is proved by the separated-spectra and polynomial CRT argument in §5,
not extrapolated from the two-hole tests.

## 12. Full synchronized original native GST Image-3 F

The integrated Lean file \`GSTImageThreeNativeFCompiler.lean\` now
additionally proves the exact limitless native-coordinate observation
\[
\mathrm{observe}_{A,B}
(\mathrm{cosmicDigitShift}_n\circ\mathrm{cosmicCarryShift}_m f)
=\mathrm{digitShiftN}_n\circ\mathrm{carryShiftN}_m
(\mathrm{observe}_{A,B} f),
\]
the original infinite axes commutation, and the original graph's
five-period FIRST-ORDER CM-curvature cancellation after physical
navigation gating. The local source-curvature \([J,M]v\ne0\) is
compatible with that exact five-period first-difference cancellation.

A new **ONE synchronized structural native F**, rather than three
unrelated functions, returns the triple
\[
\boxed{
\mathcal F_{\rm Image3}(R;s,u,v,a)
=\bigl(
  F_{\kappa(R)}u,\quad
  (\kappa(R)v_i)_{i\in\mathrm{NShape}(s)},\quad
  \star_R a
\bigr).
}
\]
Its exact navigation canonical-tail invariance is
\[
\mathcal F_{\rm Image3}(4^{3^t b};s,u,v,a)
=\mathcal F_{\rm Image3}(\mathrm{canonicalTail}(t,b);s,u,v,a)
\quad(t\ge1).
\]
For arbitrary cardinal input sets I, \`cardinalF\` applies the SAME true
F simultaneously pointwise; ordinary finite-rank original Hodge
fiber conclusions must still be established at each original X.

## 13. Image-3 Hodge-hypothesis dependency verdict

- GST native step 01, symbolic phase: original navigation-gated F,
  N-cohomology, cyclic complex structure and pure Hodge star now have
  explicit combined native laws and kernel-checkable source statements.
  Original-X naturality is derived conditionally on **genuine**
  original-X \(U,J,M\) correspondence pairs, with no assumed Hodge
  surjectivity.
- GST native step 02, symbolic phase: full rational source-strength
  cyclicity is proved by exact symbolic factorization, and the two
  previously invisible modes are precisely born at depths 2 and 3.
  All-finite-N positive rational strength range follows by CRT.
- GST native step 03, symbolic phase: nonzero Krylov gives a rational
  anti-diagonal moment detector, as in the previous full-N original-wave
  derivation.
- Actual original-X step 02: the native original-signal modes must be
  realized as genuine new **higher-primitive algebraic Hodge directions
  on each X**; abstract navigation charge or direct-sum rank does not
  prove this. This remains the decisive unproved GST hypothesis needed
  before the existing conditional proof implies the Hodge conjecture.

Never promote a checked finite/symbolic operator identity to an
unconditional universal-X Hodge theorem.


## 14. NEW exact all-N **Navigation/independent-hole rank deficit theorem**

This section upgrades the owner's ORIGINAL independent N-hole causal cohomology, the physical Graph-V2 Navigation condition, and the exact original U/J/SURVIVE operators in one multi-channel statement.

For any finite NShape \`s\` with \`h=s.holes\`, let the i-th physical arithmetic address be \`R_i\` and let the new (explicitly declared) 0/1 navigation charge be \(\kappa_i=\kappa(R_i)\). Use exactly the existing original distinct Wave-II channel addresses \(c_i\) (not an arbitrary identical or guessed channel code):
\[
\mathcal T_s=\bigoplus_{i=0}^{h-1}
\bigl(U+J+\kappa_i M+10c_i I_{12}\bigr),
\qquad
v_s=(v_{\rm old},\ldots,v_{\rm old}).
\]
The original \(U+J\) source-orbit dimension is exactly 10, as checked using TWO explicit full-annihilator detectors in §9. The original \(U+J+M\) source-orbit dimension is 12, proved via the degree-20 symbolic determinant factorization and modular certificates in §4.

For each \(i\), the cyclic submodule generated by the seed in the i-th block is \(K_i=\mathbb Q[t]v_i\), of dimension \(10+2\kappa_i\). The base original operator row sum obeys \(\lVert U+J+\kappa_iM\rVert_\infty\le4\), so every block spectrum lies inside the disk centered at \(10c_i\) of radius 4. Distinct NShape addresses satisfy \(|10c_i-10c_j|\ge10\). Therefore the spectra of the distinct blocks are disjoint. In particular, the corresponding minimal polynomials of the cyclic modules \(K_i\) are pairwise coprime over \(\mathbb Q\).

By the polynomial Chinese remainder theorem, the orbit of the ONE uniform original seed \(v_s\) under \(\mathcal T_s\) generates their whole direct sum \(\bigoplus_i K_i\). Hence the exact theorem is
\[
\boxed{
\operatorname{rank}_\mathbb Q
 [v_s,\mathcal T_s v_s,\ldots,\mathcal T_s^{12h-1}v_s]
 =
 \sum_{i=0}^{h-1}(10+2\kappa_i)
 =
 12h-2|\{i:\kappa_i=0\}|.
}
\]
For h=0, this is the empty orbit of dimension zero (formal degenerate boundary); full determinant/Hankel certificates conventionally use h>0.

**Complete cyclicity criterion (all finite positive h):**
\[
\boxed{
\dim \mathbb Q[\mathcal T_s]v_s=12h
\quad\Longleftrightarrow\quad
\forall i,\mathrm{Navigation}(R_i).
}
\]
The right-to-left direction combines the base on-source symbolic determinant with coprime channel polynomials. The converse is strict: each inactive original hole leaves TWO independent rational source-free defects, already explicitly detected by the d1,d2 source-free functionals in §9.

This is a genuine rigorous bridge from the owner's physical Navigation, the true V3 independent N-cohomology, original Wave-I and II, CM complex structure and limitless N-shapes. It is not an assertion of actual Chow source algebraicity of a higher-primitive Hodge class on X.

**Exact independently executed Wolfram certificate:** \`research/computations/GST_image3_allN_navigation_gated_source_rank_law_20261111.wl\` was committed, re-fetched and executed verbatim. Exact rational ranks for all 0/1 configurations with h=1 and h=2, plus the representative h=3 pattern (1,0,1), all passed:

| original navigation charge packet | exact rank |
| 0 | 10/12 |
| 1 | 12/12 |
| 0,0 | 20/24 |
| 0,1 and 1,0 | 22/24 |
| 1,1 | 24/24 |
| 1,0,1 | 34/36 |

The general theorem follows from the coprime-module proof, not finite extrapolation.

### The requested source-birth NEXT-GEOMETRY statement

Now the source-birth goal can be stated more sharply in the original owner's GST language: prove that the **native operator** \(F_{\rm Image3}\), with each independent physical navigation channel active, is actually realized through GENUINE original-X Chow correspondences and a canonical Hodge landing that preserves the distinct N-channel quotients, **including the two curvature-born directions per hole**. This would yield the full native-rank source algebra required by the GST hypothesis PROVIDED the landed Hodge space has the appropriate rank, and no missing higher-primitive Hodge direction is discarded in the landing. This geometric existence/rank condition remains unproved.

Do NOT equate the \(\kappa_i=1\) condition by itself with universal Hodge algebraicity: it is sufficient for full cyclicity only within the original GST wave information carrier, not automatically for the canonical rational Hodge cohomology of arbitrary X.
