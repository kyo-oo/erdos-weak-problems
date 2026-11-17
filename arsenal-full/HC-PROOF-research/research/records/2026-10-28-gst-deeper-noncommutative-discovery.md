# GST deeper continuation: ordered words, arbitrary nilpotent depth, finite holonomy

Base checkpoint: `417b4aa5a50280b655c31bd066f588e0c6330365`.
Branch: `research/gpt6-native-point-primitive-span-20261017`.
Date: 2026-10-28. The original `(X,p,alpha)` canonical-cycle target is retained.

This continuation adds **five Lean modules and 38 theorem declarations**,
strengthens the prior correction module, and extends the existing import entry
point. All changed Lean remains uncompiled proof drafts, at the owner's request.
The work used Mathbox research/proof/computation-audit workflows and actual
Wolfram Language evaluations, with an independent exact Python implementation.

## Results and the restrictions removed

| Result | Earlier restriction | New statement | Evidence |
| --- | --- | --- | --- |
| Ordered dressing | Commutativity and vanishing triple products for `1+2x+2x²` | The ordered law `x⋆y=x+y+xy` is associative in every ring; finite geometric inverses work at every nilpotent depth | Complete ring proof; generic symbolic strictly upper triangular 4×4 model; exact matrix orders 1…9 |
| Word source recovery | Recovering all targets with one fixed scalar-combined frame | A concrete three-operator family has every scalar combination singular, yet three length-four words sum to identity | Symbolic determinant; exact matrix identity; original-X source adapter |
| Integer-coefficient reconstruction | The shorter quadratic formula divides by two | The length-four identity uses only integer coefficients | No new division in the reconstruction formula; this is not a claim that rational source cycles become integral |
| Generalized blind modes | Prior obstruction tested only vectors fixed by N | Every finite generalized 1-eigenvector of N is excluded from a polynomial certificate with q(1) nonzero | Universal induction; explicit Jordan examples, including a nonfixed generalized mode already in the source image |
| Finite holonomy | Missing additive primitive in a finite action layer | `S(g)=sum_k c(g,k)` gives `delta S=|G|c`; over Q, `S/|G|` is an actual primitive | Universal sum proof; every basis vector of 13 finite cocycle spaces independently checked |
| Nonabelian lifting | Additive cancellation falsely promoted to a multiplicative gauge | Exact ordered defect, plus the actual corrected-section product in a finite abelian extension layer | Ring/group proofs and a nonabelian affine-extension check |
| Source birth | Arbitrarily deep trivial-graded extensions treated as fresh Chern sources | Their positive additive characteristic is zero; finite trace reflects this back to the original X | K0 filtration induction and degree-trace argument |

The crucial word example is:

\[
 A=\begin{pmatrix}0&0&0\\0&0&-1\\0&1&0\end{pmatrix},\quad
 B=\begin{pmatrix}0&0&1\\0&0&0\\-1&0&0\end{pmatrix},\quad
 C=\begin{pmatrix}0&-1&0\\1&0&0\\0&0&0\end{pmatrix}.
\]

For all rational x,y,z, `det(xA+yB+zC)=0`, but
`A²B²+A²C²+B²C²=I`. Thus no fixed scalar frame works globally, while ordered
compositions provide an exact global identity. This changes the recovery
mechanism rather than claiming a singular frame became invertible.

Given genuine source returns `L_A,L_B` with classes `A(v),B(v)`, the actual
original-X cycle is

`L_A(A(B(B(alpha)))) + L_A(A(C(C(alpha)))) + L_B(B(C(C(alpha))))`.

The third channel needs a Hodge-fiber action but no source-algebraicity theorem
for its source in this formula. Existence of such source geometry for arbitrary
X is not asserted. Earlier branch word frames already acted on an algebraic
spine; this update's distinction is target-first source readout, no native tail
endomorphism, and an explicit identity rather than an assumed frame determinant.

## Files

- `GSTOrderedNilpotentDressing.lean`: associative coordinate law, arbitrary-order
  finite inverse, unit coordinates, exact nonlinear gauge defect, and the
  traceless involution showing tracelessness does not imply nilpotence.
- `GSTFiniteGroupCocycleAveraging.lean`: integral averaging identity, rational
  primitive, normalization, and corrected nonabelian section product.
- `GSTTargetWordRecovery.lean`: nonempty word constructor, finite target-word
  recovery, explicit three-word cycle formula and exact matrix identities.
- `GSTClassicalHodgeWordSourceRecovery.lean`: original-X native-cycle adapter
  using the previous independently solved source systems.
- `GSTFilteredK0SourceConservation.lean`: arbitrary-length filtration sum,
  characteristic conservation and finite-cover zero-source obstruction.
- `GSTFiniteSourceCorrection.lean`: generalized fixed-mode obstruction added.
- `GSTOpenAISourceCorrectionUpgrade.lean` and `lakefile.toml`: new imports and
  module registrations. Later owner verification: `lake build GSTOpenAISourceUpgrade`.

[Full hand derivation](../derivations/GST_noncommutative_word_and_finite_holonomy_2026_10_28.tex).
The hand derivation also proves the finite-dimensional maximal-domain/Fitting
characterization and the induction through an actual rational central
filtration of a group extension. The Lean files encode the generalized-mode
obstruction and the individual averaging/corrected-product layer; they do not
claim to formalize all group-quotient and central-filtration infrastructure.

## Executed source attempt on arbitrary original X

The attempted constructor was: take the alpha-selected carrier, correct its
finite holonomy through rational nilpotent layers, and use the resulting
filtered algebraic object as a fresh positive Chern source. The correction
equations are solved in the stated domain. The exact class computation then
shows that trivial graded pieces give `[E]=rank(E)[O]` after the finite pullback.
Every positive Chern-character piece vanishes there; genuine finite push-pull
forces it to vanish on original X. A proposed class `mu*alpha` with mu nonzero
would therefore force alpha=0.

This closes **only** the finite-cover/trivial-graded constructor. It does not
rule out nontrivial graded sources, new supports, or every future nilpotent
descent construction. General SL-valued transport need not have a rational
nilpotent filtration: the traceless block `[[0,1],[1,0]]` squares to identity.
Neither finiteness of the translation groupoid nor universal deck existence
was proved or assumed. The universal prescribed-Hodge source remains open.

## Computations, bounds, and provenance

Wolfram source: [exact Wolfram program](../experiments/gst_deep_noncommutative_wolfram_20261028.wl).
Raw result: [pinned Wolfram output](../computations/gst_deep_noncommutative_wolfram_20261028.output.json).

Observed kernel: **15.0.1 for Linux x86 (64-bit), July 2, 2026**.
The final run passed **56 assertions** with exact symbolic/rational mathematical
arithmetic. Kernel-reported runtime: **0.550701 seconds**. The remote kernel's
process exit status is not exposed and is recorded as unknown, not invented.

The finite cocycle-space checks cover every rational kernel basis vector for:

| Action | Cochain dimension | Cocycle dimension |
| --- | ---: | ---: |
| Trivial C1…C6 | 1, 4, 9, 16, 25, 36 | 1, 2, 3, 4, 5, 6 |
| Sign C2 | 4 | 1 |
| Swap C2 | 8 | 3 |
| Rotation C3 | 18 | 4 |
| Rotation C4 | 32 | 6 |
| Rotation C6 | 72 | 10 |
| Trivial S3 | 36 | 6 |
| Permutation S3 | 108 | 16 |

Total: **67 cocycle basis vectors in 13 actions**. Linearity makes each complete
basis test cover the entire specified finite cochain kernel. This is not an
enumeration of every finite group or arbitrary geometric descent datum; the
all-finite-group statement is supplied by the separate hand sum proof.

Independent implementation: [Python exact sparse elimination](../experiments/gst_deep_noncommutative_checks.py).
It passed **2,526 checks**, including every corresponding cocycle basis vector,
group/action laws, matrix identities, actual affine-section correction,
source integrity and the local import graph. The count includes structural
checks; it is not a count of independently proved mathematical theorems.

Reproduce the local verifier and a fresh manifest:

```sh
python research/experiments/gst_deep_noncommutative_run.py
```

[Validated v2 computation manifest](../computations/gst_deep_noncommutative_20261028.manifest.json)
and [independent result](../computations/gst_deep_noncommutative_20261028.independent.output.json).
The Mathbox manifest validator passed with root/hash verification. The local
verifier process exited 0. Its manifest records all 13 input hashes before and
after, the observed runtime, software versions and declared result hash.

The first remote inverse probe exposed a kernel behavior: `MatrixPower` at
zero on a singular matrix returned an unevaluated expression with a singularity
message. The final program defines powers by repeated multiplication from an
explicit identity, then reruns the entire suite. This was an implementation
issue, not a counterexample to the inverse theorem. A separate minimal 2×2
probe reproduced it. No failed run is counted as evidence of the final claims.

No Lean installation, compilation or CI dispatch was performed. The new
`#print axioms` lines are future verification commands, not session receipts.

## Proof audit and continuation

Review provenance: **self-review** by the implementing assistant. Wolfram and
Python are independent computational checks, not independent proof reviewers.

| Obligation | Verdict |
| --- | --- |
| Ordered ring identities and nilpotent inverse | Passed as written; associative ring, finite nilpotence where used |
| Exact finite-group averaging | Passed as written; finite G, actual cocycle, additive actions; Q division only in the rational form |
| Corrected section product | Passed under the displayed embedding, slide and multiplication equations |
| Target-first word class and explicit identity | Passed under the source class equations; geometric instantiation is conditional |
| Generalized-mode obstruction | Passed as written; no finite-dimensional hypothesis |
| Finite-dimensional maximal-domain theorem | Hand proof supplied; not fully encoded in Lean |
| Full central-filtration splitting | Hand induction supplied; Lean encodes its individual lifting step |
| Universal original-X source existence | Not established |

No global priority or novelty assertion is made for algebra groups, finite-group
averaging or Fitting decomposition. These are stronger integrations relative
to checkpoint 417b4aa. The successful word identity is a concrete mechanism
change; the remaining source-geometry implication is not renamed as an easy
lemma. Continuation must construct a nontrivial prescribed-class source or a
new support, rather than repeat trivial-graded coherence correction.
