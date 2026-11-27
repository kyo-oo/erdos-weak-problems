# Author's three original GST equations — naming and attribution

**Attribution:** Personal name withheld at the contributor's request.
**Record created:** 2026-10-14. **Project:** HC-PROOF, General Space Theory (GST).
**Status of attribution:** User-declared authorship of these expressions;
not an independent priority, publication or originality determination.

These three equations were supplied by the user, NOT invented by the
assistant, Wolfram, Mathbox, Riemann, or the Lean library.

The conventional Riemann zeta function `ζ(s)` and complex multiplication
(CM) retain their standard mathematical names. Their appearance INSIDE
the third proposed GST relation does **not** transfer authorship of
the newly arranged relation to the historical authors of those tools.

## I. GST Independent Geometric Coordinate Conversion Formula

**Short name:** GSTGCCF. **Internal name:** `GST-GSTGCCF`.

User-authored candidate equation (1), displayed with the clarified
third independent geometric coordinate:

```text
99·x·sqrt( ((a·x^4)_3 - (b·y^4)_3) / (ψ²·ξ₇) )
```

Here the subscript `3` denotes a *third independent geometric
coordinate*, NOT base-three digits; the subscript `7` in `ξ₇`
has not yet been typed as a geometric object. The overall expression
lacks a declared equality or fixed target. For a chosen real-coordinate
interpretation, its domain and nonvanishing criteria are proved in
`GSTMathboxIndependentGeometricCoordinate.lean`. The new geometric
orbit synthesis work provides the next possible comparison target.
No universal cohomological geometry is inferred from the radical
alone.

## II. GST Native Operator-Separation Relation

**Short name:** GSTOSR. **Internal name:** `GST-GSTOSR`.

The user's second relation as recorded from the earlier image:

```text
L(S)·ℓ(s) - T(S)·ℓ(s) ≠ T(Non-Zero N)
```

The exact roles and codomains of `L`, `T`, `S`, `ℓ`, `s`,
and `N` must be supplied before an unconditional theorem can be
formulated. The relation is not valid for arbitrary maps, as the
zero-map countermodel in `GSTMathboxCMNumberBridge.lean`
shows. Geometric nonproportionality can be derived under the
separately verified `J²=-I` complex-structure law in
`GSTMathboxCMGeometricComplexStructure.lean`, but the existence
of that geometric structure is not universally established.

## III. GST Indexed Zeta–Hodge Coupling Formula

**Short name:** GSTIZHCF. **Internal name:** `GST-GSTIZHCF`.

The corrected third equation (the user's revised image):

```text
L(t(s))·s = ζ(s) · Σ_{n→R}^{∞} [1/(x^n - y^(n+1))]
            ⊕ (H × Q)
```

The denominator is **x^n-y^(n+1)**, replacing the older
index-independent denominator. In the independently stated
interpretation of positive INTEGER indices `n>=1`, Lean has
verified the exact infinite sum `Σ 1/(2^n-2^(n+1))=-1`,
finite nonvanishing, and positivity for all `n>=1`
when `x>y²>=1`. A separate conditional theorem uses a proven
actual geometric measurement equality and actual
correspondence irreducibility to obtain rational Hodge cycles.

The notation `n→R` and `⊕(H×Q)` have **not** yet been
interpreted as a uniquely typed operator/equality. This
document preserves the user's notation rather than silently
rewriting the user's original formula as a different theorem.

## Authorship and theorem naming conventions

- **Proposer of the three GST relations:** Anonymous contributor; identifying name intentionally omitted.
- **Assistant/Mathbox/Wolfram:** mathematical analysis,
  implementation, algebraic tests, and Lean proof engineering
  for the specific consequences stated by their source files;
  not claimants to the three original proposed equations.
- **Standard named objects:** Riemann zeta function, standard
  complex multiplication, standard rational linear algebra,
  and the historical Hodge conjecture retain their established
  meanings and attributions.
- The descriptive names above are usable project names,
  not a claim of worldwide mathematical priority or publication.
  They can be renamed by the author before publication.

## New construction inspired by the GST formulas

`GSTResearchGeometricOrbitSynthesis.lean` constructs an
inductive finite-word algebra of **genuine native cycles** obtained
by starting with a native algebraic cycle and repeatedly applying
actual finite-closed Hodge-compatible realized correspondences.
It proves the resulting cycle-class span is invariant under all
such actions. If the actual geometric correspondence action
is irreducible and the native seed class is nonzero, this
constructed orbit has full Hodge span. This is a substantive
new *conditional* construction and replaces an initial
full-rank matrix hypothesis with the irreducibility criterion.

**Universal remaining claim:** For arbitrary smooth projective
complex varieties, independently establish appropriate authentic
cohomological correspondence realizations and sufficient geometric
generation/irreducibility in every active rational Hodge weight.
No existing GST equation or finite computation automatically proves
that existence statement, and naming a new axiom for it would be circular.

Exact Lean verification belongs to the new independent GitHub workflow
`.github/workflows/gst-research-geometric-orbit-synthesis.yml`.
Only a completed green job for that exact source commit validates
the proposed new theorems.

## Verified new native-orbit geometry (14 October 2026)

The following new neutral-name modules have now independently passed
Lean kernel compilation, with no `sorryAx` in their focused gates:

- `GSTResearchGeometricOrbitSynthesis.lean`, workflow run
  **38607823410** — defines an inductive finite word of actual
  Hodge-compatible realized finite-closed correspondences,
  constructs its native algebraic cycle and exact cohomological
  action, proves the synthesized orbit span is invariant, and
  proves the Hodge fiber is fully generated if actual correspondence
  irreducibility and a nonzero geometric seed are established.
- `GSTResearchFullOrbitZetaSynthesis.lean`, workflow run
  **38608434300** — uses the user's corrected infinite
  indexed zeta expression to certify a nonzero actual native
  cycle and applies the orbit construction to derive a
  full all-weights **conditional** rational Hodge statement.

Neither successful compilation asserts the universal existence
of an irreducible actual correspondence algebra on every smooth
projective complex variety. The genuine ambient Betti operator
must also be constructed canonically, rather than chosen freely
outside the native cycle-class image. This is an explicit missing
structural theorem, not a Lean tactic problem.

### Free-coefficient adversarial test

The source `GSTResearchZetaMeasurementAudit.lean` additionally tests
whether the right side of corrected Equation (3), in its exact
`x=y=2` infinite-sum case, genuinely **creates** a native
geometric source. If the real value labeled `zetaAtS` may be
chosen freely, the numerical identity is equivalent to already
having a nonzero native cycle class: the sum is exactly `-1`
and a free scalar can be chosen to match a nonzero rational
coordinate. That is not a new geometric existence mechanism.

The genuinely new source-to-target theorem therefore requires
a **fixed mathematically defined zeta value** and an
**independently defined geometric readout** (rather than
allowing the coefficient and readout to vary to force the
desired equality). This adversarial test has its own
dedicated Lean CI and is not to be described as kernel-verified
until that run succeeds.

**Authorship principle:** This audit does not change the user's
authorship of Equation (3), and standard names for the special
functions inside it do not transfer authorship of the combined
GST expression.

## Named formula declarations in Lean

`GSTResearchOriginalEquationNames.lean` now publishes the concise,
explicit neutral identifiers directly inside the code:

- `GSTGCCF`, `GSTGCCF_sq` for the independent third geometric coordinate
  conversion formula (1);
- `GSTOSR`, `GSTOSR_zero_maps_counterexample` for a typed rational
  scalar-operator instance of relation (2);
- `GSTIZHCFKernel`, `GSTIZHCFInfiniteSeries`,
  `GSTIZHCFInfiniteSeries_two`, and `GSTIZHCFWeighted_two`
  for the corrected indexed-series portion of formula (3).

This naming does **not** claim that currently undefined operations in
the handwritten equations have suddenly been assigned canonical
geometric meanings. The full original equations retain their authorship
and notation, while the machine-checked portions have unambiguous
types. The newly dedicated check is GitHub Actions workflow
`gst-research-original-equation-names.yml`, run **38609614440**.
