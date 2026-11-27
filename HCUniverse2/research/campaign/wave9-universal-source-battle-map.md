# WAVE 9 — THE UNIVERSAL PRIMITIVE-X SOURCE: THE STATEMENT DESIGN (FROZEN)

Written by the commander (the wave-9 design round), branch
`research/gpt6-gst-hypothesis-part1-chow-square-20261110`, base HEAD `8acf848`
(wave 8-C). Static verification only from the sandbox (the ARSENAL law: no
local Lean); the kernel verdict belongs to CI at the pushed SHA.

This is the statement-design freeze the wave-8 residual ledger prescribed
("the universal primitive-X source theorem — statement design still open").
The execution wave follows this map exactly.

## THE NAME'S MEANING (the honest scope)

The lane's job title promises "THE UNCONDITIONAL LAW + universal
primitive-X source". Item one is WRITTEN (the gate-free law,
`native_GST_single_fold_orbit_law_finiteLine_unconditional_gatefree`,
GSTFiniteLinePointsGateDischarge.lean §3 — kernel verdict pending the
discharge lane). Item two — THIS design — is the SOURCE-BASIS package:

* **X** = the finite-line world `finiteLineWorld M` itself (the lane's own
  world; no arbitrary-X claim is smuggled in — the campaign's acceptance
  discipline).
* **primitive** = the genuine point/component cycles of the world's own
  arithmetic (the honest atoms of GSTFiniteLinePointAlgebra — the closed
  points and the generic points of the M lines).
* **source** = an EXPLICIT, INDEPENDENT carrier family whose classes carry
  the rational Hodge fiber — not the law's existential certificate
  (`∃ C, C.IsKrylovCyclic`) but the CONSTRUCTED family with the basis
  certificate.
* **universal** = uniform in M: ONE recipe (the honest seed + the two
  M-cycle letters) for EVERY `M ≥ 1`, the general-M family claim.

The mathematical step beyond the law: the law SPANS (existence of a
certificate); the source theorem names the carriers, proves the
INDEPENDENCE (a genuine basis), and compiles the witness (the explicit
finite combination — the coordinates).

## THE CLASSICAL CONTENT (what a human proof says)

The finite-line world is M disjoint ℙ¹'s. Its rational Hodge classes:

* codimension 0 (weight 0): the component classes `[X_i]`, `i : Fin M` —
  a basis of H⁰ = ℚ^M (every class is (0,0));
* codimension 1 (weight 1): the point classes `[pt_i]`, `i : Fin M` — a
  basis of H² = ℚ^M (every class is (1,1));
* codimension ≥ 2: the fiber is trivial (each line is a curve — no H^{2p}
  for p ≥ 2 on a disjoint union of ℙ¹'s).

The universal source: the two orbit families
`{R₀^i Z₀}` (the generic-point family — the components) and
`{R₁^i Z₁}` (the closed-point family) are each a ℚ-BASIS of their sector:
independent (distinct atoms evaluate independently) and spanning (the law's
certificate at the honest letters/seeds). The compiler: given a rational
Hodge class α, its coordinates against the honest atom evaluation are the
witness's coefficients — the cycle `Z(α) = Σ_i q_i · (the i-th source
carrier)`.

## THE FROZEN STATEMENTS (the module's shape)

New module `GSTFiniteLinePrimitiveXSource.lean`; imports
GSTFiniteLinePointsGateDischarge (the gate-free law + the gate), the
point-algebra (the atoms), the honest data (the class maps), the exact
Clay statement (the consequence types). Same preamble discipline as the
sister modules (`maxHeartbeats 200000000`, `maxRecDepth 1000000`,
`noncomputable section`, the standard opens).

### §0 THE SOURCE FAMILIES (the explicit carriers)

```
noncomputable def finiteLineSourceOne (M) [NeZero M] (i : Fin M) :
    codimensionCycles (finiteLineScheme M) 1 :=
  -- the closed-point cycle at line i (the R₁-orbit of the honest seed:
  -- lineHonestSeedOne M at i = 0, rotated i times by the M-cycle letter)
noncomputable def finiteLineSourceZero (M) [NeZero M] (i : Fin M) :
    codimensionCycles (finiteLineScheme M) 0 :=
  -- the generic-point cycle of line i (the R₀-orbit of lineHonestSeedZero)
```
Route: the atoms are ALREADY in the corpus — `lineClosedPointAt M i` /
`lineGenericPoint M i` with their coheight receipts
(`lineClosedPointAt_coheight` / `lineGenericPoint_coheight`,
GSTFiniteLinePointAlgebra — the wave-4-A closed-point family, CI-green).
The orbit identification `R₁^i Z₁ = the i-th atom's cycle` is the §2
letter-action receipt (the same L3/L6 index-rotation machinery the
letters' realization used — GSTFiniteLineCycleCorrespondence §3's
`finiteLineCycleLetterOne`-action on the atoms).

### §1 THE INDEPENDENCE (the basis certificate, weight one)

```
theorem finiteLineSourceOne_independent (M) [NeZero M] :
    LinearIndependent ℚ (fun i => cycleClassMap (finiteLineSourceOne M i))
```
Route: the honest atom evaluation — the classes of the closed points at
DISTINCT lines are distinct and independent: evaluate against the
component-class functionals (the honest data's `honestComponentLinear`
family — the i-th functional reads the i-th component and annihilates the
others; the closed point at line i evaluates to 1 on functional i, 0 on
the others — the Gram matrix is the identity, hence independent). The
evaluation content is the corpus's own `presentationOfNativeCycle_point`
receipt (green) + the on-line characterization
(`finiteLineComplexPoint_on_line_iff`, GSTFiniteLineAnalytification:416).
Weight zero: same shape with the generic points (the component classes'
independence: the `honestComponentLinear` functionals again — dual pair).

### §2 THE SPAN (the source theorem proper — every class an explicit
combination of the family)

```
theorem finiteLine_universal_primitive_X_source (M) [NeZero M] (ω) :
    ∀ p : Nat,
    ∀ α : RationalSingularCohomology (the honest analytification) (2 * p),
      α ∈ rationalHodgeSubspace (the honest bigrading p) →
        ∃ q : Fin M → ℚ,
          α = ∑ i, q i • (cycleClassMap (the source family at i))
```
Route: the law (`native_GST_single_fold_orbit_law_finiteLine_
unconditional_gatefree` — the gate-free form at the honest data) supplies
the certificate's SPAN at every p; the certificate's orbit family at the
HONEST letters IS the source family (the orbit-identification of §0);
the p=0/p=1 sectors fall out with the families; p ≥ 2 is the vacuous
sector (the fiber is trivial — the sphere-union's degree-2p cohomology
vanishes for p ≥ 2; the receipt: the green `sphereUnionZerothHomotopy`
component machinery at the slice level — H⁰ = components, H² = the
sphere class per component, H^{≥4} = 0).

### §3 THE COMPILER (the uniform witness map — the universal content)

```
noncomputable def finiteLineSourceCompiler (M) [NeZero M] (p) (α ...) :
    codimensionCycles (finiteLineScheme M) p :=
  -- the assembled cycle from the coordinates of §2 (the family at p=1;
  -- the point-finite sum; p=0 the components; p≥2 the zero cycle)
theorem finiteLineSourceCompiler_correct (M) [NeZero M] (ω) : ...
  -- the class of the compiled cycle IS α (the §2 combination + the
  -- class-map's linearity)
```
Route: the coordinates are read off the honest atom evaluation (the
§1 functionals — a dual-basis readout); the assembly is the finite sum
in `codimensionCycles` (a ℚ-vector space — the sum is genuine); the
correctness is the §2 identity. THE UNIVERSALITY: the compiler takes NO
data beyond M and α — one recipe for the whole general-M family.

### §4 THE MASTER PACKAGE (the ∀M claim)

```
theorem the_universal_primitive_X_source_package :
    ∀ (M : ℕ) (hM : NeZero M) (ω : ...),
      (the independence family) ∧ (the source theorem) ∧
      (the compiler's correctness)
```

## THE DISEASE CATALOG (campaign law — every item bites here)

ofHom-fusion direction; subtype-motive (show-bridges/Subtype.ext);
Fin-mk-vs-OfNat (`⟨0, Nat.pos_of_neZero ‹_›⟩`); semireducible
rw-visibility (show-unfold first); stale-Decidable (split); universe
pinning; rw-pattern direction; NO autoImplicit (explicit binders);
`lineCoverHomogeneousOneQ`-style named membership proofs exactly as the
green homes spell them. NEW for this module: the `Finset.sum` over
`Fin M` with the `q i •` smul at the class map (the `Finsupp`/
`Finset.sum_apply` discipline of the green consequence proofs — mirror
`rationalAlgebraic_iff_finiteRationalCombination`'s sum handling,
GSTClassicalHodgeExactClayStatement:84-100).

## THE HONESTY LAW

Zero sorry/admit/native_decide/new axioms. The independence and the vacuity
of p ≥ 2 are the two mathematical risks; if either resists, it is
documented in the module's ledger (NOT stated). The kernel verdict
belongs to the new CI lane at the pushed SHA. The ω-liveness stays fenced
(the law is ∀ω; the source theorem inherits the ∀ω shape — no
nonvanishing is fabricated).

## THE REGISTRATION (the commander's job at the execution wave)

* `lakefile.toml`: `GSTFiniteLinePrimitiveXSourceLib` (roots: the new
  module; the import chain through the discharge module).
* CI lane: `.github/workflows/gst-finite-line-primitive-x-source.yml`
  (mirror the discharge lane's cache-bank discipline: restore-keys prefix
  chain `hc-lean-incremental-Linux-finite-line-`, the 1500s timeout, the
  sorryAx hard-fail, the artifact upload, the path filter carrying the
  new file + its direct import chain).

## THE PRE-CONDITION (the wave's gate)

The execution wave lands AFTER the discharge lane's verdict: the source
theorem consumes the gate-free law, whose module (the discharge) is at
CI now (run 45237909347 / the cache-bank cycle). If the discharge lane
reports diagnostics at the defeq seams, THOSE repairs come first (the
designated repair points: the authored bridges of the core module).
