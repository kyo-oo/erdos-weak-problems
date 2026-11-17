# GST pure algebraic K₀ sources encoded by one smooth center

Base checkpoint: `b7a3706fcf0775faf26964c6afab95a8ea126449`.
Target: construct a center whose genuine native output detects the prescribed
primitive residual on the original X. This record completes the conversion of
**any native GST cycle** to **one** such center, through its actual algebraic
K₀ lift and an exact Chow-class formula. It does not assume or claim a K₀ source representing
an arbitrary rational Hodge class exists.

Behavioral correction: the constant spectral-bundle experiment at the base
checkpoint did not disprove any Lean-verified GST law. Its matrix readout was
not the native Chern readout. The failure label belongs only to that added
constructor. The GST laws below are composed with their actual native maps.

## The construction and theorem

Let X be a smooth projective complex n-fold, L an ample line bundle, h=c₁(L),
and 1≤p≤n. Start with a genuine algebraic K₀ class ξ. Use the existing GST
algebraic Adams weight filter if necessary to arrange

\[
\operatorname{ch}_i(\xi)=0\quad(0\leq i<p),\qquad
z=\operatorname{ch}_p(\xi)\in CH^p(X)_{\mathbb Q}.
\]

In particular, for **any native cycle already produced by GST**, write its
finite cycle presentation z=Σaⱼ[Zⱼ] and take ξ=Σaⱼ[O_Zⱼ]. Smoothness of X
gives finite locally free resolutions, and the supported-sheaf leading law
gives precisely the displayed vanishings and chₚξ=z. Thus this theorem
converts the entire actual native cycle image, not only a chosen bundle
subfamily. Adams purification is optional for these supported-sheaf lifts.
If a previous K₀ source was read through a relative Todd factor, lift its
**actual Chow output** this way; do not purify an uncorrected character and
silently drop the relative Todd terms.

There exist explicitly specified construction choices M>0, R≥n, k>0 and a
smooth incidence center S in X×ℙⁿ⁻ᵖ such that, for projection a to X,

\[
\boxed{a_*[S]=\binom Rp k^p h^p+
       (-1)^{p-1}(p-1)!\,M z.} \tag{1}
\]

If n≤2p+1, S is isomorphic to a smooth determinantal center D **inside the
same original X**, and (1) holds with [D] instead of a_*[S]. In particular
this applies to every middle problem n=2p. Empty centers are permitted when
the class permits; the nonzero residual period below guarantees nonemptiness.

For every rational linear primitive readout ℓ with ℓ(h·u)=0,

\[
\boxed{\ell(a_*[S])=(-1)^{p-1}(p-1)!M\,\ell(z).} \tag{2}
\]

Thus a detected native K₀ source produces **one detecting center**, with no
positive-copy packet, center-search premise, or possible cancellation of its
source coefficient. Its corrected native output recovers the entire source
class, not just a nonzero period:

\[
z=\frac{(-1)^{p-1}}{M(p-1)!}
   \left(a_*[S]-\binom Rp k^p h^p\right). \tag{3}
\]

## Proof: absorb the negative bundle rather than interpolate copies

Clear rational denominators and write Mξ=[E]−[F] with algebraic vector
bundles E,F. This is possible by the definition of algebraic K₀ on smooth
projective X and the finite locally free resolution property. Rank ξ=0
implies rank E=rank F.

Choose an integer m large enough that F(m)=F⊗Lᵐ is globally generated.
Take an actual evaluation surjection and its locally free kernel:

\[
0\longrightarrow K\longrightarrow\mathcal O_X^{N}
  \longrightarrow F(m)\longrightarrow0.
\]

The ordinary algebraic bundle B=E(m)⊕K satisfies the exact K₀ identity

\[
[B]=M\xi\otimes L^m+N[\mathcal O_X]. \tag{4}
\]

Consequently rank B=N, chᵢ(B)=0 for 0<i<p, and chₚ(B)=Mz. The twist by m
cannot introduce a smaller nonzero character degree because **all** degrees
of ξ below p, including rank, vanish. No complement to F itself inside a
trivial bundle is being assumed; the genuine globally generated F(m) and its
kernel give (4).

Adjoin enough trivial summands to B to obtain B′ of rank R≥n. This does not
alter any positive character degree. Newton's identities give

\[
c_i(B')=0\ (0<i<p),\qquad
c_p(B')=(-1)^{p-1}(p-1)!M z. \tag{5}
\]

Now choose k large enough that B′(k) is globally generated. The full twist
formula, with all lower positive Chern terms zero, is exactly

\[
c_p(B'(k))=c_p(B')+\binom Rp k^p h^p. \tag{6}
\]

There is no approximation or discarded lower Chern term in (6).

Take R−n general global sections of B′(k). Their failure to be independent
has expected codimension n+1 and is absent on X. Their quotient V is a
globally generated rank-n bundle, with c(V)=c(B′(k)). Choose general n−p+1
sections s₀,…,sₙ₋ₚ of V and form

\[
S=\{(x,[\lambda]):\sum_{j=0}^{n-p}\lambda_j s_j(x)=0\}
  \subset X\times\mathbb P^{n-p}.
\]

It is a general zero scheme of the globally generated rank-n bundle
prₓ*V⊗O(1), hence smooth of dimension n−p, or empty. The projective push is

\[
a_*[S]=[\eta^{n-p}]\sum_{i=0}^{n}c_i(V)\eta^{n-i}=c_p(V).
\]

Equations (5)–(6) prove (1). The next determinantal rank-drop stratum has
codimension 2(p+1). If n≤2p+1 it is absent; the kernel along the first
stratum is one-dimensional, so S→D is an isomorphism and D is smooth in X.
Applying ℓ proves (2); dividing the actual nonzero rational coefficient gives
(3). This is the promised geometric construction, not an assumed center.

## Exceptional birth and original-X feedback

For n≤2p+1, blow up original X along D, with exceptional divisor F and map ρ.
The genuine exceptional push is

\[
\rho_*(F^p)=(-1)^{p-1}[D].
\]

It follows that the primitive readout of this actual exceptional output is

\[
\boxed{\ell(\rho_*F^p)=M(p-1)!\,\ell(z).} \tag{7}
\]

**The signs cancel.** If the GST source was target-directed, with
ℓ(z)=ΣᵢQ(r,zᵢ)², the new exceptional feedback is exactly
M(p−1)!ΣᵢQ(r,zᵢ)². Hence the native sum-of-squares coupling survives as a
positive multiple, with no assumed new geometric detector.

For arbitrary n,p, blow up X×ℙⁿ⁻ᵖ along S instead. Its center codimension is
n; a_*ρ_*(Fⁿ)=(-1)ⁿ⁻¹a_*[S]. All resulting cycles and the normalized output
(3) are native cycles on the original X after proper push. This does not
claim D is smooth inside X outside the stated dimension range.

## How the verified GST laws enter

| Existing GST component | Exact role here |
|---|---|
| Arbitrary-arity native world birth | Supplies an actual native source; its cycle-class compatibility is retained |
| CM–NM native graph arithmetic | Supplies actual rational combinations of proper graph sources when that geometry is present |
| Perfect-complex/K₀ realization | Represents those genuine native sources in algebraic K₀; no holomorphic or topological substitution |
| Algebraic Adams weight filter | Makes all degrees below p vanish while retaining chₚ |
| Global-generation kernel completion | Newly replaces the virtual source by one actual bundle modulo trivial rank |
| All-degree Newton and twist laws | Gives the nonzero coefficient in (1) in every codimension |
| Smooth incidence and exceptional birth | Constructs the center and the native output (7) |
| Target-directed Gram/residual law | Measures the prescribed residual and keeps its exact source coupling |
| Canonical cycle-class/proper-push naturality | Takes (1)–(7) to Betti cohomology on the same X |

This composition is valid for any native GST source produced by these laws,
including sources descended from higher worlds. No assertion that every
original X is dominated by a solved GST world is inserted.

## Prescribed targets on the complete connected blowup family

This also supplies a center for **every prescribed nonzero primitive target**
on the connected arbitrary-rank worlds constructed in
[the interacting-blowup record](2026-10-20-gst-interacting-blowups-connected-arbitrary-rank.md).
This corollary uses that earlier construction; it does not introduce another
example family as a replacement for arbitrary original X.

Fix any r≥1 and its original connected fourfold Xᵣ, with the already proved
very ample polarization Lᵣ. For any prescribed rational primitive class α,
`parallel_birth_recovers_every_primitive_target` gives its native cycle
zα=bw₀+Σsᵢwᵢ directly from its complete cup-kernel coordinates. There is no
target source-existence premise in that reconstruction. Lift this **constructed**
cycle to the supported-sheaf K₀ class above and execute (4)–(6), with p=2.
The result is one smooth center Dα inside that same Xᵣ, with

\[
[D_\alpha]=\binom R2 k^2 h^2-Mz_\alpha.
\]

Since hα=0, its prescribed-target readout and exceptional feedback are

\[
Q(\alpha,[D_\alpha])=-M Q(\alpha,\alpha),\qquad
Q(\alpha,\rho_*F^2)=M Q(\alpha,\alpha)>0\quad(\alpha\ne0). \tag{8}
\]

The strict inequality follows from the actual complete primitive Gram, not an
assumed detector: its lower block is dI+J/4, d=(t²−1)/3>0, t=2r+1, and
the exact Schur factor `(d+r/4)A-r*c^2` is strictly positive by
`parallel_birth_gram_has_positive_schur`. Explicitly, with S=Σsᵢ and
u=cb/(d+r/4), its quadratic form is

\[
d\sum_i(s_i+u)^2+
  \frac14(S+ru)^2+
  \left(A-\frac{rc^2}{d+r/4}\right)b^2.
\]

This is positive for every nonzero (b,s), at every r. Thus (8) is a
construction for all prescribed primitive targets on the previously complete
GST family. The all-varieties objective still asks for the corresponding
native source birth on every original X.

## Formal and computational evidence

**GREEN:** full pinned integration
[#39397085626](https://github.com/kyo-oo/HC-PROOF/actions/runs/39397085626)
at code revision `77077d430c2572bb21bafabfd9fff69a7fa42b88`, **8967 jobs**.
All four new selected printed axiom receipts contain only `propext`,
`Classical.choice`, and `Quot.sound`; the entire Lean build log contains no
`sorryAx`. The new computation ran successfully in that workflow and its output
is byte-identical to the locally retained exact output. The revision-matched
receipt is `research/computations/gst_pure_k0_single_center_lean.receipt.txt`.
The v2 computation manifest validates with current input hashes and completed
run status. An earlier parser error in the new inequalities was repaired;
it was not a mathematical failure of any existing GST law.

`GSTUniversalResolvedSupportHodge.lean`, in the existing
`GSTNativeSmoothIncidenceCenter` namespace, now defines the all-degree Newton
recursion `chernFromCharacter` and proves:

- `chernFromCharacter_pure_leading`;
- `chernFromCharacter_below_pure`;
- `one_center_class_from_pure_character`;
- `one_center_period_from_pure_character`;
- `one_center_detects_pure_native_source`;
- `one_center_exceptional_feedback`.

These are universal coefficient theorems. The scheme-level evaluation-kernel,
Bertini, rank-compression and canonical comparison steps above are a separate
mathematical proof; they are not claimed to be constructed Lean schemes by
the coefficient declarations.

The reproducible exact computation is
`python3 research/computations/gst_pure_k0_single_center.py`.
It checks 96 formal cases p=1,…,12, preserving independent lower character
symbols through (4), using two kernel twists, two generation twists and two
denominator factors. Newton reconstruction then proves the implemented class
formula and exact normalization in each case. It also checks the dimension
and exceptional-sign arithmetic for 300 pairs 1≤p≤n≤24.

The separate Wolfram script reconstructs the total Chern class by exponentiating
the Chern-character series, independently of the Python/Lean Newton recursion.
It checks p=1,…,10. These finite calculations support the implementation;
the preceding proof and the universal Lean coefficient theorems carry the
all-p statement. See the manifest, raw outputs and Lean receipt beside the
scripts for pinned evidence.

## Remaining original target and continuation

The original arbitrary-X, arbitrary-prescribed-Hodge-class goal has not been
replaced by a theorem about already native classes. What changed is that
**center construction is now completed for every genuine native K₀ source**,
using one center rather than a Chern interpolation packet.

For a prescribed residual r, the remaining source operation is to construct
a genuine algebraic K₀ class ξᵣ on that X with ℓ(chₚξᵣ)≠0. Once it is
constructed, (4)–(7) give the center and its nonzero exceptional feedback
without any further detection hypothesis. The existing GST program compiler
and native birth laws retain their exact proved conclusions; this record
does not manufacture their missing input from a matrix-level spectral symbol.

Disposition: the K₀-to-one-center conversion is proved at the mathematical
level, with universal coefficient formalization; universal prescribed-residual
source creation remains the active research obligation. A continuation must
construct ξᵣ or an actual source program on X, not repeat the completed
center-selection calculation.

## Self-review of the precise claim

Primary verdict: **conditional on the named scheme-level geometric inputs**
for the full smooth-center statement; the universal coefficient statements
are separately kernel checked. This is a self-review, not an independent
agent review.

| Obligation | Review result |
|---|---|
| Negative virtual bundle absorbed by a real locally free kernel | Passed: global generation is used on F(m), not a fictitious trivial complement of F |
| Rank and twisting order | Passed: rank ξ=0; kernel twist m preserves leading degree; trivial summands are added before the generation twist k |
| Chern factorial and sign | Passed: Newton recursion in all degrees, with independent exponential checks |
| Ambient error | Passed: full class formula (6); only c₀ and cₚ contribute |
| Smooth center inside X | Correct only in stated range n≤2p+1; outside it the center is smooth over X in the projective product |
| Empty center | Allowed in the construction; excluded by nonzero period when detection is claimed |
| Exceptional feedback | Passed: center codimension p inside X versus n in the product; both signs explicitly tracked |
| Bertini, generic section independence and canonical Chow–Betti maps | Named geometric inputs from the existing incidence constructor; not instantiated as Lean schemes by this update |
| Prescribed residual acquires a native source on every X | Not addressed by the conversion theorem; no target-preimage field added |

The decisive comparison is between actual algebraic K₀/Chow classes throughout
(4)–(7). A spectral matrix trace is never substituted for their Chern period.
