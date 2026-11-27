# Wave 68-A — THE GENERAL-M LAW ARCHITECTURE: `GSTFiniteLineGeneralMLaw.lean`

Date: 2026-11-22. Author: Wave 68 Agent A (law architecture, task W68-A).
Design mission: the COMPLETE architecture — interface freeze, gap map, import
closure, risk ledger, skeleton — of the module that discharges
`NativeGSTSingleFoldOrbitLaw` on the finite-line world at **every M ≥ 1**,
composing the carrier (F1, green run 44899187702), the closed immersion (F2,
`GSTFiniteLineClosedImmersion.lean`, in CI), the smoothness package (F3, wave
67, `GSTFiniteLineSmoothness.lean` in flight), and the wave-64 cyclic word.
The law's discharge engines are ALREADY kernel-green; this document maps
EXACTLY how the general-M world plugs into them.

---

## 0. THE COMPOSITION TOWER (one page)

```
F1  GSTFiniteLineWorldCarrier.lean   (GREEN)   finiteLineScheme M, finiteLineStructureMap M,
                                              finiteLineCycle M (+ isIso, lineRotateGraded_pow),
                                              finiteLineEmbedding M
F2  GSTFiniteLineClosedImmersion.lean (CI)     finiteLine_closedImmersion M
F3  GSTFiniteLineSmoothness.lean     (W67)     finiteLine_smoothness M
─────────────────────────────────────────────────────────────────────────────
W68 §0  THE WORLD: finiteLineWorld M : SmoothProjectiveComplexScheme
        = ⟨finiteLineScheme M, finiteLineStructureMap M, finiteLine_smoothness M,
           ⟨2*M-1, finiteLineEmbedding M, finiteLine_closedImmersion M,
            finiteLineEmbedding_over_base M⟩⟩           [one NEW lemma: the over_base square]
─────────────────────────────────────────────────────────────────────────────
GATE-A  the analytification receipt (INPUT):  A : AnalytificationData (finiteLineWorld M),
        hspace : A.space = TopCat.of (sphereUnionSpace M)   — the honest ⊔ M S²
        (the ℂ-points classification wave's target; NOT constructed here)
GATE-L  the letter gates (INPUT): R₁/hR₁ at weight 1, R₀/hR₀ at weight 0 —
        genuine RealizedFiniteClosedCorrespondences rotating the two honest
        families by cyclicPred (finiteLineCycle's graphs; the wave-64
        "realization gate"; NOT constructed here)
GATE-S  the honest cycle nontriviality (INPUT): Z₀ ≠ 0, Z₁ ≠ 0
        (the world's own 0- and codimension-1 cycles; the wave-63 honesty ledger)
─────────────────────────────────────────────────────────────────────────────
W68 §1–§4  THE HODGE DATA ASSEMBLY at general M (the wave-63 §1–§4 pattern
        lifted): the A-typed honest families (point classes, component
        classes), the functional cycle-class maps, the assembled
        finiteLineHodgeData (stash@0 / span@1 / stash@p≥2), the fiber and
        seed-class equations (all by construction + green engines).
W68 §5–§7  THE CERTIFICATES: the single-letter M-cycle words [(1,R₁)], [(1,R₀)]
        with the honest seeds — the IDENTITY KRYLOV MATRIX of wave-64, realized
        formally as the green cyclic-orbit span law (span_range_cyclicIterate).
W68 §8     THE LAW: native_GST_single_fold_orbit_law_finiteLine — by the GREEN
        wave-60 engine native_GST_single_fold_orbit_law_of_sphereUnion_gate,
        re-instantiated on the assembled concrete world.
W68 §9–§13 the dead-weight stash receipt, the M=1 monogenic de-risking receipt
        (NO letters needed at M=1), the liveness receipts (2 ≤ M, ω-gated),
        the master package, the every-frame consequences (exact-Hodge, the
        per-weight typed FS law, the finite-rational-combination form).
```

**The two-line summary of what changes from wave 63.** At M = 1 the law was
discharged by the *dead-or-monogenic* engine with the **empty word** at every
weight (`Subsingleton (Fin 1)` collapsed both live fibers to rational lines).
At M ≥ 2 the fibers have rank M: the discharge needs (i) a genuine
correspondence — the M-cycle letter, the graph of `finiteLineCycle M` — at
both live weights, and (ii) the cyclic-orbit span law in place of the
monogenic collapse. Both engines are green (wave 60 + `GSTCyclicOrbitSpan`);
the law module's only new mathematics is the world bundling (§0) and the
assembly glue.

---

## 1. THE INTERFACE FREEZE

Every theorem the module will contain, in dependency order, with the green
engine each plugs into. Names are frozen; statement spellings follow the
green corpus verbatim (the wave-60 gate spellings, the wave-63 assembly
spellings). `M : ℕ`, `[NeZero M]` throughout; `hM : 0 < M := NeZero.pos M`.

### §0 The world — the F1+F2+F3 composition (NEW; the finite-point
`finitePointWorld` pattern, `GSTFinitePointWorldCarrier.lean:735-739`)

```lean
/-- **THE OVER-BASE SQUARE OF THE EMBEDDING.**  The F2-tail item: the
embedding commutes with the structure maps over Spec(ℂ). -/
theorem finiteLineEmbedding_over_base (M : ℕ) [NeZero M] :
    finiteLineEmbedding M ≫ projectiveSpaceToBase (2 * M - 1) =
      finiteLineStructureMap M
-- PLUG (route): the finite-point over_base Γ-route (GSTFinitePointWorldCarrier
-- :660-730, green) transposed: unfold both sides, the toSpecΓ/ΓSpecIso
-- triangle, the constants-through-degree-zero lemma (T6/hzero of the wave-67
-- recon).  NO pin lemma exists for Proj.map/toSpecZero naturality — see the
-- risk ledger (R3).

/-- **THE FINITE-LINE WORLD** — the smooth projective complex scheme bundle. -/
noncomputable def finiteLineWorld (M : ℕ) [NeZero M] :
    SmoothProjectiveComplexScheme where
  X := finiteLineScheme M
  structureMap := finiteLineStructureMap M
  smooth := finiteLine_smoothness M            -- F3 (wave 67)
  projective := ⟨2 * M - 1, finiteLineEmbedding M,
    finiteLine_closedImmersion M,              -- F2 (wave 66)
    finiteLineEmbedding_over_base M⟩
-- PLUG: the anonymous-constructor bundle — the finitePointWorld pattern
-- verbatim under the renames.  Receipts (rfl):
theorem finiteLineWorld_X (M : ℕ) [NeZero M] :
    (finiteLineWorld M).X = finiteLineScheme M := rfl
theorem finiteLineWorld_structureMap (M : ℕ) [NeZero M] :
    (finiteLineWorld M).structureMap = finiteLineStructureMap M := rfl
```

**Switch note:** if the F3.4 stage ships the same bundle under the wave-67
name `finiteLineSmoothProjective`, replace the body by that name (one line);
the frozen name `finiteLineWorld` stays (the lane-facing name).

### §0.5 The local instance bridges (the wave-63 §0 discipline, verbatim)

```lean
local instance (priority := high) instFLModule
    {V : SmoothProjectiveComplexScheme} (A : AnalytificationData V) (n : Nat) :
    Module ℚ (RationalSingularCohomology A n) :=
  inferInstanceAs (Module ℚ (singularCohomologyOf A.space n))
local instance (priority := high) instFLAddCommGroup
    {V : SmoothProjectiveComplexScheme} (A : AnalytificationData V) (n : Nat) :
    AddCommGroup (RationalSingularCohomology A n) :=
  inferInstanceAs (AddCommGroup (singularCohomologyOf A.space n))
-- PLUG: the rfl bridge GSTSingularCohomologyMaps.singularCohomologyOf_eq
-- (green, wave 57) — the wave-63 :121-132 pattern verbatim.
```

### §1 The analytification gate — the honest sphere-union ⊔ M S² (INPUT)

The module does NOT construct the analytification. Every theorem below takes
as explicit inputs:

```lean
variable (M : ℕ) [NeZero M]
variable (A : AnalytificationData (finiteLineWorld M))
variable (hspace : A.space = TopCat.of (sphereUnionSpace M))
```

This is the points-classification wave's target interface:
`finiteLineAnalytification M : AnalytificationData (finiteLineWorld M)` with
the space receipt (the ℂ-points classification
`ComplexPoint (finiteLineWorld M) ≃ sphereUnionSpace M`, the Riemann-sphere
identification per line). The gate-form keeps THIS module compilable and
green before that wave lands.

### §2 The honest families — the A-typed transports (the wave-59 gate at the
world; the wave-63 §1 / wave-60 §0 pattern)

```lean
/-- **THE HONEST POINT-CLASS FAMILY, A-TYPED.**  The wave-59 gate family
`spherePointClass M ω`, transported to the world's own analytification along
the space identification (rfl-equal, once H is assembled, to the wave-60
world family `spherePointClassWorld M hspace ω`). -/
def finiteLinePointClass (M : ℕ) [NeZero M]
    (A : AnalytificationData (finiteLineWorld M))
    (hspace : A.space = TopCat.of (sphereUnionSpace M))
    (ω : singularCohomologyOf (TopCat.of unitSphereType) 2) (j : Fin M) :
    singularCohomologyOf A.space 2 :=
  (Equiv.cast (by rw [hspace])).symm (spherePointClass M ω j)
-- PLUG: the wave-63 §1 transport (positive_dimensional_live_weight_family's
-- witness, made explicit); green calculus = GSTSphereUnionPointClassGate.

/-- **THE COMPONENT-CLASS FAMILY, A-TYPED.**  The 0-th cohomology component
machine through the sphere-union component identification (rfl-equal to the
wave-60 `sphereComponentClass M hM hspace`). -/
def finiteLineComponentClass (M : ℕ) [NeZero M]
    (A : AnalytificationData (finiteLineWorld M))
    (hspace : A.space = TopCat.of (sphereUnionSpace M)) (j : Fin M) :
    RationalSingularCohomology A 0 :=
  (componentCohomologyZeroEquivFinM A M
    (sphereUnion_cohomology_zero hspace)).symm (Pi.single j (1 : ℚ))
-- PLUG: GSTComponentCohomologyZero.componentCohomologyZeroEquivFinM (green,
-- run 44545624743) + GSTSphereUnionComponents.sphereUnion_cohomology_zero
-- (green).

-- the receipts (the family is honest given the honest sphere class):
theorem finiteLinePointClass_ne_zero (hω : ω ≠ 0) (j : Fin M) :
    finiteLinePointClass M A hspace ω j ≠ 0
-- PLUG: spherePointClass_ne_zero (green) through the cast.
theorem finiteLinePointClass_indep (hω : ω ≠ 0) :
    LinearIndependent ℚ (finiteLinePointClass M A hspace ω)
-- PLUG: spherePointClass_indep (green) through the cast.
theorem span_range_finiteLineComponentClass :
    Submodule.span ℚ (Set.range (finiteLineComponentClass M A hspace)) = ⊤
-- PLUG: the wave-60 span_range_sphereComponentClass route (green): the
-- singles-span law + the surjective linear transport (span-image chain).

-- the H-typed identification bridges (rfl; syntactic alignment for the
-- wave-60 gate spellings consumed in §5–§8):
theorem finiteLinePointClass_eq_world (j : Fin M) :
    finiteLinePointClass M A hspace ω j =
      spherePointClassWorld (V := finiteLineWorld M)
        (H := finiteLineHodgeData M A hspace ω Z₀ hZ₀ Z₁ hZ₁) M hspace ω j := rfl
theorem finiteLineComponentClass_eq_world (j : Fin M) :
    finiteLineComponentClass M A hspace j =
      sphereComponentClass (V := finiteLineWorld M)
        (H := finiteLineHodgeData M A hspace ω Z₀ hZ₀ Z₁ hZ₁) M hM hspace j := rfl
```

### §3 The seeds and the cycle-class maps (the wave-63 §2/§4 functional
construction, choose-formed for top-level defs)

```lean
/-- The degree-style honest cycle-class functional (the green wave-63 §2
engine, restated in choose form for use inside definitions). -/
theorem exists_cycle_functional' {X : Type} [AddCommGroup X] [Module ℚ X]
    (Z₀ : X) (hZ₀ : Z₀ ≠ 0) :
    ∃ f : X →ₗ[ℚ] ℚ, f Z₀ = 1 :=
  GSTPositiveDimensionalLiveWeightLaw.exists_cycle_functional Z₀ hZ₀
-- PLUG: GREEN VERBATIM (wave-63, run 44844378079).  No re-derivation.

-- the seed classes (the honest 0-th component class / the honest 0-th point
-- class — the wave-64 seed design):
def finiteLineSeedClassZero (M) [NeZero M] (A) (hspace) :
    RationalSingularCohomology A 0 :=
  finiteLineComponentClass M A hspace ⟨0, NeZero.pos M⟩
def finiteLineSeedClassOne (M) [NeZero M] (A) (hspace)
    (ω : singularCohomologyOf (TopCat.of unitSphereType) 2) :
    singularCohomologyOf A.space 2 :=
  finiteLinePointClass M A hspace ω ⟨0, NeZero.pos M⟩

-- the cycle-class maps (f • seed-class; linear by the smul-calculus — the
-- wave-63 cl₀/cl₁ spellings :332-357):
def finiteLineCycleClassZero (M) [NeZero M] (A) (hspace)
    (Z₀ : codimensionCycles (finiteLineWorld M).X 0) (hZ₀ : Z₀ ≠ 0) :
    codimensionCycles (finiteLineWorld M).X 0 →ₗ[ℚ] RationalSingularCohomology A 0 := ...
def finiteLineCycleClassOne (M) [NeZero M] (A) (hspace) (ω)
    (Z₁ : codimensionCycles (finiteLineWorld M).X 1) (hZ₁ : Z₁ ≠ 0) :
    codimensionCycles (finiteLineWorld M).X 1 →ₗ[ℚ] singularCohomologyOf A.space 2 := ...
-- PLUG: (exists_cycle_functional' _ hZ).choose, then the wave-63
-- map_add'/map_smul' smul-calculus verbatim.  Receipts (by choose_spec):
theorem finiteLineCycleClassZero_seed : finiteLineCycleClassZero M A hspace Z₀ hZ₀ Z₀
    = finiteLineSeedClassZero M A hspace
theorem finiteLineCycleClassOne_seed : finiteLineCycleClassOne M A hspace ω Z₁ hZ₁ Z₁
    = finiteLineSeedClassOne M A hspace ω
```

### §4 THE HODGE DATA ASSEMBLY at general M (the wave-63 §3/§4 assembly lifted;
the honest bigrading design of the curve world)

```lean
/-- **THE ASSEMBLED HODGE DATA OF THE FINITE-LINE WORLD.**  Weight zero: the
stash bigrading (the fiber is the forced top).  Weight one: the SPAN bigrading
on the honest point-class family (the fiber IS the rational span of the
family).  Weights p ≥ 2: the stash bigrading (honestly dead — no vanishing
proof).  The cycle-class maps: the honest component/point class functionals
at the live weights, zero above. -/
noncomputable def finiteLineHodgeData (M : ℕ) [NeZero M]
    (A : AnalytificationData (finiteLineWorld M))
    (hspace : A.space = TopCat.of (sphereUnionSpace M))
    (ω : singularCohomologyOf (TopCat.of unitSphereType) 2)
    (Z₀ : codimensionCycles (finiteLineWorld M).X 0) (hZ₀ : Z₀ ≠ 0)
    (Z₁ : codimensionCycles (finiteLineWorld M).X 1) (hZ₁ : Z₁ ≠ 0) :
    HodgeBigradedBettiData (finiteLineWorld M) where
  analytification := A
  hodgeBigrading := fun p =>
    match p with
    | 0 => stashBigrading _ 0
    | 1 => spanBigrading (finiteLinePointClass M A hspace ω) 1 (by omega)
    | (p + 2) => stashBigrading _ (2 * (p + 2))
  cycleClass := fun p =>
    match p with
    | 0 => finiteLineCycleClassZero M A hspace Z₀ hZ₀
    | 1 => finiteLineCycleClassOne M A hspace ω Z₁ hZ₁
    | (p + 2) => 0
-- PLUG: the wave-63 §4 assembly (:258-268) verbatim under the renames; the
-- A-typed families elaborate against the analytification literal by the
-- singularCohomologyOf_eq rfl-defeq (the wave-63 green precedent).

-- the fiber and seed equations (the law's gate discharges, ALL internal):
theorem finiteLineHodgeData_hone :
    (finiteLineHodgeData M A hspace ω Z₀ hZ₀ Z₁ hZ₁).hodgeBigrading 1 =
      spanBigrading (spherePointClassWorld M hspace ω) 1 (by omega)
-- PLUG: rfl through finiteLinePointClass_eq_world (the match-arm reduction).
theorem finiteLineHodgeData_hstash (p : ℕ) (hp : 1 < p) :
    (finiteLineHodgeData M A hspace ω Z₀ hZ₀ Z₁ hZ₁).hodgeBigrading p =
      stashBigrading (RationalSingularCohomology A (2 * p)) (2 * p)
-- PLUG: the rcases p with _ | _ | p + rfl pattern (wave-63 :279-285).
theorem finiteLineHodgeData_fiber_one :
    rationalHodgeSubspace ((finiteLineHodgeData M A hspace ω Z₀ hZ₀ Z₁ hZ₁).hodgeBigrading 1) =
      Submodule.span ℚ (Set.range (spherePointClassWorld M hspace ω))
-- PLUG: rationalHodgeSubspace_span_eq (green kit).
theorem finiteLineHodgeData_fiber_zero :
    rationalHodgeSubspace ((finiteLineHodgeData M A hspace ω Z₀ hZ₀ Z₁ hZ₁).hodgeBigrading 0) = ⊤
-- PLUG: rationalHodgeSubspace_eq_top_of_degree_zero (green, wave 42).
theorem finiteLineHodgeData_fiber_stash (p : ℕ) (hp : 1 < p) :
    rationalHodgeSubspace ((finiteLineHodgeData M A hspace ω Z₀ hZ₀ Z₁ hZ₁).hodgeBigrading p) = ⊥
-- PLUG: rationalHodgeSubspace_stash_eq_bot (green kit) through hstash.
theorem finiteLineHodgeData_seed_zero :
    (finiteLineHodgeData M A hspace ω Z₀ hZ₀ Z₁ hZ₁).cycleClass 0 Z₀ =
      sphereComponentClass M hM hspace ⟨0, hM⟩
-- PLUG: finiteLineCycleClassZero_seed + the rfl-bridge (by construction).
theorem finiteLineHodgeData_seed_one :
    (finiteLineHodgeData M A hspace ω Z₀ hZ₀ Z₁ hZ₁).cycleClass 1 Z₁ =
      spherePointClassWorld M hspace ω ⟨0, hM⟩
-- PLUG: finiteLineCycleClassOne_seed + the rfl-bridge (by construction).
```

**The seed gates of the wave-60 law are discharged INTERNALLY, by
construction** — the functional construction arranges the class of each
honest seed cycle to BE the 0-th family class. The remaining external inputs
are the cycle nontrivialities `Z₀ ≠ 0`, `Z₁ ≠ 0` (honesty inputs, the
wave-63 ledger; dischargable later by the points wave).

### §5 THE FOLD REALIZATION — the letter gates (INPUT; the wave-64
realization gate)

**What the wave-63 law consumed as its fold: NOTHING.** At M = 1 every
certificate was the **empty word** `[]` (the dead-or-monogenic engine). What
changes at M: the live-weight certificates are the **single-letter words**
`[( (1 : ℚ), R)]` where `R` is the graph-correspondence of the M-cycle
automorphism `finiteLineCycle M` — the fold. The law module takes the letters
as its gates (the frozen wave-60 plug-in design), in the exact green spelling:

```lean
variable (R₁ : RealizedFiniteClosedCorrespondence (finiteLineWorld M)
    (finiteLineHodgeData M A hspace ω Z₀ hZ₀ Z₁ hZ₁) 1)
variable (hR₁ : ∀ j : Fin M, R₁.cohomologyOperator
    (spherePointClassWorld M hspace ω j) =
      spherePointClassWorld M hspace ω (cyclicPred M j))
variable (R₀ : RealizedFiniteClosedCorrespondence (finiteLineWorld M)
    (finiteLineHodgeData M A hspace ω Z₀ hZ₀ Z₁ hZ₁) 0)
variable (hR₀ : ∀ j : Fin M, R₀.cohomologyOperator
    (sphereComponentClass M hM hspace j) =
      sphereComponentClass M hM hspace (cyclicPred M j))
```

The intended realization (the letter wave's construction targets, documented
here; the law module does not build them):

* **Geometry:** `FiniteClosedCorrespondence.graphCorrespondence` of the cycle
  endomorphism — `finiteLineCycle M` is an isomorphism (green
  `finiteLineCycle_isIso`) whose graded M-th power is the identity (green
  `lineRotateGraded_pow`); as a `ComplexSchemeEndomorphism (finiteLineWorld M)`
  it needs the still-unproved `finiteLineCycle_over_base` (the cycle
  commutes with the structure map — a carrier-side lemma, see R1).
* **Operator:** the transported M-cycle pullback
  `sphereUnionCoe ∘ (cohomologyPullbackOf (sphereCycle M) 2) ∘ sphereUnionCoe.symm`
  — exactly the operator gate of the green derived form.
* **Realization (`realizes_on_points`):** the pointwise class square
  `cl_p (σ x) = T (cl_p x)` for every codim-p point — the honest
  point-classification content (the class of a closed point on line i is the
  i-th point class). The hand-built-letter precedent is the green
  `GSTFinitePointShiftWord` lane (point-pair letters with explicit
  `RealizesAmbientOnPoints` proofs).

The derived-form documentation lemma (the honest content of hR₁, one green
re-instantiation — the law module's only letter-adjacent theorem):

```lean
/-- **THE DERIVED LETTER EQUATION.**  A weight-1 letter whose cohomological
operator is the transported M-cycle pullback rotates the world point-class
family exactly as the green gate calculus dictates. -/
theorem finiteLineLetterOne_rotate_of_pullback
    (R₁ : RealizedFiniteClosedCorrespondence (finiteLineWorld M)
      (finiteLineHodgeData M A hspace ω Z₀ hZ₀ Z₁ hZ₁) 1)
    (hRop : ∀ u : singularCohomologyOf (TopCat.of (sphereUnionSpace M)) 2,
      R₁.cohomologyOperator (sphereUnionCoe M hspace u) =
        sphereUnionCoe M hspace ((cohomologyPullbackOf (sphereCycle M) 2) u)) :
    ∀ j : Fin M, R₁.cohomologyOperator
      (spherePointClassWorld M hspace ω j) =
        spherePointClassWorld M hspace ω (cyclicPred M j) :=
  spherePointClassWorld_rotate_of_pullback M hspace R₁ hRop ω  -- GREEN (wave 60)
```

(A weight-0 derived form — the component-class rotation under the transported
pullback — does NOT exist in the green corpus; it is the letter wave's small
new item, via the component machine's naturality. The law itself only needs
the raw gate `hR₀`. See R6.)

### §6 THE WEIGHT-1 CERTIFICATE — the M-cycle word, the identity Krylov matrix

```lean
/-- **THE WEIGHT-1 KRYLOV CERTIFICATE.**  The single M-cycle letter with the
honest 0-th point-class seed. -/
noncomputable def finiteLineCertificateOne (M : ℕ) [NeZero M] (A) (hspace) (ω)
    (Z₀) (hZ₀) (Z₁) (hZ₁) (R₁) (hR₁) :
    RealizedCorrespondenceKrylovCertificate (finiteLineWorld M)
      (finiteLineHodgeData M A hspace ω Z₀ hZ₀ Z₁ hZ₁) 1 :=
  sphereUnionCertificateOne M hM hspace ω
    (finiteLineHodgeData_hone M A hspace ω Z₀ hZ₀ Z₁ hZ₁) R₁ hR₁ Z₁
    (finiteLineHodgeData_seed_one M A hspace ω Z₀ hZ₀ Z₁ hZ₁)
-- PLUG: GREEN (wave 60) — the certificate builder applies verbatim at the
-- concrete world; the word is [( (1 : ℚ), R₁)], the seed Z₁.

theorem finiteLineCertificateOne_isKrylovCyclic ... :
    (finiteLineCertificateOne M A hspace ω Z₀ hZ₀ Z₁ hZ₁ R₁ hR₁).IsKrylovCyclic
-- PLUG: GREEN sphereUnionCertificateOne_isKrylovCyclic (wave 60) — the orbit
-- IS the rotated family (sphereUnionCertificateOne_hodgeOrbit), and the
-- cyclic-orbit span law span_range_cyclicIterate (GSTCyclicOrbitSpan, green)
-- closes the span against the designed fiber.  THIS IS THE FORMAL SHADOW OF
-- THE WAVE-64 CERTIFICATE: the Krylov matrix of the M-cycle letter on the
-- honest family basis is the permutation (inverse-cycle orientation: the
-- identity matrix) — det = 1, rank M — no determinant ever appears; the
-- span law IS the closed-form certificate.
```

### §7 THE WEIGHT-0 CERTIFICATE — the mirror

```lean
noncomputable def finiteLineCertificateZero (M : ℕ) [NeZero M] (A) (hspace)
    (Z₀) (hZ₀) (Z₁) (hZ₁) (R₀) (hR₀) :
    RealizedCorrespondenceKrylovCertificate (finiteLineWorld M)
      (finiteLineHodgeData M A hspace ω Z₀ hZ₀ Z₁ hZ₁) 0 :=
  sphereUnionCertificateZero M hM hspace R₀ hR₀ Z₀
    (finiteLineHodgeData_seed_zero M A hspace ω Z₀ hZ₀ Z₁ hZ₁)
-- PLUG: GREEN (wave 60).  word := [( (1 : ℚ), R₀)]; seed Z₀; the word-Hodge
-- field is the forced-⊤ fiber (rationalHodgeSubspace_eq_top_of_degree_zero).

theorem finiteLineCertificateZero_isKrylovCyclic ... :
    (finiteLineCertificateZero M A hspace Z₀ hZ₀ Z₁ hZ₁ R₀ hR₀).IsKrylovCyclic
-- PLUG: GREEN sphereUnionCertificateZero_isKrylovCyclic (wave 60) — the
-- component family spans H⁰ (span_range_finiteLineComponentClass), the
-- cyclic-orbit span law transports it.
```

### §8 THE LAW (the headline theorem)

```lean
/-- **THE GENERAL-M LAW.**  The finite-line world — the honest carrier of the
M disjoint projective lines (F1+F2+F3), with the honest sphere-union
analytification ⊔ M S², the assembled Hodge data of §4 (span bigrading at
weight 1, stash at 0 and p ≥ 2), and the two M-cycle letters as genuine
realized closed correspondences rotating the two honest families — satisfies
the FULL NativeGSTSingleFoldOrbitLaw, at EVERY M ≥ 1.

ω-DISCLOSURE (wave 60): the honest sphere class ω appears only as the INDEX
of the family design; its nonvanishing is needed ONLY for the liveness
receipts (§11), never for the law. -/
theorem native_GST_single_fold_orbit_law_finiteLine (M : ℕ) [NeZero M]
    (A : AnalytificationData (finiteLineWorld M))
    (hspace : A.space = TopCat.of (sphereUnionSpace M))
    (ω : singularCohomologyOf (TopCat.of unitSphereType) 2)
    (R₁ : RealizedFiniteClosedCorrespondence (finiteLineWorld M)
      (finiteLineHodgeData M A hspace ω Z₀ hZ₀ Z₁ hZ₁) 1)
    (hR₁ : ∀ j : Fin M, R₁.cohomologyOperator
        (spherePointClassWorld M hspace ω j) =
          spherePointClassWorld M hspace ω (cyclicPred M j))
    (Z₁ : codimensionCycles (finiteLineWorld M).X 1) (hZ₁ : Z₁ ≠ 0)
    (R₀ : RealizedFiniteClosedCorrespondence (finiteLineWorld M)
      (finiteLineHodgeData M A hspace ω Z₀ hZ₀ Z₁ hZ₁) 0)
    (hR₀ : ∀ j : Fin M, R₀.cohomologyOperator
        (sphereComponentClass M hM hspace j) =
          sphereComponentClass M hM hspace (cyclicPred M j))
    (Z₀ : codimensionCycles (finiteLineWorld M).X 0) (hZ₀ : Z₀ ≠ 0) :
    NativeGSTSingleFoldOrbitLaw (finiteLineWorld M)
      (finiteLineHodgeData M A hspace ω Z₀ hZ₀ Z₁ hZ₁) :=
  native_GST_single_fold_orbit_law_of_sphereUnion_gate (M := M) hM hspace ω
    (finiteLineHodgeData_hone M A hspace ω Z₀ hZ₀ Z₁ hZ₁)
    (finiteLineHodgeData_hstash M A hspace ω Z₀ hZ₀ Z₁ hZ₁)
    R₁ hR₁ Z₁ (finiteLineHodgeData_seed_one M A hspace ω Z₀ hZ₀ Z₁ hZ₁)
    R₀ hR₀ Z₀ (finiteLineHodgeData_seed_zero M A hspace ω Z₀ hZ₀ Z₁ hZ₁)
-- PLUG: GREEN ENGINE (wave 60, run 44642555839) — the entire weight dispatch:
-- weights 0/1 by the two cyclic single-letter certificates (§6/§7), weights
-- p ≥ 2 by the stash engine (§9).  NOTE the argument order: the seed-class
-- gates hZ₁/hZ₀ of the green theorem are supplied by the §4 internal lemmas.
```

(The `Z₀`/`Z₁` binders must be moved before `R₁`/`R₀` in the final spelling
since the letters' types mention the assembled `finiteLineHodgeData`, which
is itself a function of `Z₀ hZ₀ Z₁ hZ₁` — the skeleton §5 fixes the order:
seeds first, letters second.)

### §9 The dead-weight discharge at p ≥ 2 (the stash)

```lean
/-- **THE DEAD WEIGHTS.**  Every weight p ≥ 2 of the assembled data is
honestly dead: the (p,p)-slot is ⊥ and complexification is injective — no
vanishing proof for H^{2p} anywhere.  The empty word with the zero seed
discharges the law at these weights. -/
theorem finiteLineHodgeData_deadWeights (M : ℕ) [NeZero M] (A) (hspace) (ω)
    (Z₀) (hZ₀) (Z₁) (hZ₁) :
    ∀ p : ℕ, 1 < p →
      Subsingleton (ClassicalHodgeFiber (finiteLineWorld M)
        (finiteLineHodgeData M A hspace ω Z₀ hZ₀ Z₁ hZ₁) p)
-- PLUG: subsingleton_hodgeFiber_of_eq_bot (green) + §4's fiber_stash.  (The
-- law's own dispatch consumes this internally; the standalone receipt
-- documents the dead half and feeds no-free-lunch framing.)
```

### §10 The M = 1 monogenic de-risking receipt (NO letters; the wave-63
engine on the assembled world)

```lean
/-- **THE ONE-LINE SPECIALIZATION, LETTER-FREE.**  At M = 1 the assembled
data satisfies the full law WITHOUT any correspondence input: Fin 1 is a
subsingleton, both live fibers are rational lines (weight 0 by the component
machine, weight 1 by the single point class), and the dead-or-monogenic
engine discharges everything with the empty word.  This is the wave-63 law
re-instantiated on the concrete one-line world — the module's built-in
de-risking receipt: the M = 1 half of the law lands even if the letter wave
stalls. -/
theorem native_GST_single_fold_orbit_law_finiteLine_one_line
    (A : AnalytificationData (finiteLineWorld 1))
    (hspace : A.space = TopCat.of (sphereUnionSpace 1))
    (ω : singularCohomologyOf (TopCat.of unitSphereType) 2)
    (Z₀ : codimensionCycles (finiteLineWorld 1).X 0) (hZ₀ : Z₀ ≠ 0)
    (Z₁ : codimensionCycles (finiteLineWorld 1).X 1) (hZ₁ : Z₁ ≠ 0) :
    NativeGSTSingleFoldOrbitLaw (finiteLineWorld 1)
      (finiteLineHodgeData 1 A hspace ω Z₀ hZ₀ Z₁ hZ₁)
-- PLUG: the wave-63 §4 engine verbatim at M = 1: haveI fin1_subsingleton;
-- hmono₀ (every H⁰ class is a multiple of the transported 0-th indicator —
-- at M = 1 the constant-one and the 0-th indicator coincide);
-- hmono₁ (every fiber class is a multiple of the single point class — the
-- span induction of wave-63 :396-412); then
-- native_GST_single_fold_orbit_law_of_dead_or_monogenic_weights (GREEN).
-- NOTE: no hω needed — if ω = 0 the weight-1 fiber is ⊥ and the subsingleton
-- branch fires; the law is uniform.
```

### §11 The liveness receipts (2 ≤ M; the ω-gated honesty — the only place
the fenced sphere-machine core is consumed)

```lean
theorem finiteLine_weightZero_fiber_not_subsingleton (hM : 2 ≤ M) ... :
    ¬ Subsingleton (ClassicalHodgeFiber (finiteLineWorld M)
      (finiteLineHodgeData M A hspace ω Z₀ hZ₀ Z₁ hZ₁) 0)
-- PLUG: GREEN weightZero_fiber_not_subsingleton (wave 60) — the two
-- component classes are distinct (the component iso sends them to distinct
-- indicators).
theorem finiteLine_weightOne_fiber_not_subsingleton (hM : 2 ≤ M) ...
    (hω : ω ≠ 0) :
    ¬ Subsingleton (ClassicalHodgeFiber (finiteLineWorld M)
      (finiteLineHodgeData M A hspace ω Z₀ hZ₀ Z₁ hZ₁) 1)
-- PLUG: GREEN weightOne_fiber_not_subsingleton (wave 60) — the two world
-- point classes are distinct (the ω-gated independence).
theorem finiteLine_exists_nonzero_algebraic_hodge_class (hM : 2 ≤ M) ...
    (hω : ω ≠ 0) (R₁ ...) (hR₁ ...) :
    ∃ Z : codimensionCycles (finiteLineWorld M).X 1,
      (finiteLineHodgeData ...).cycleClass 1 Z ∈
        rationalHodgeSubspace ((finiteLineHodgeData ...).hodgeBigrading 1) ∧
      (finiteLineHodgeData ...).cycleClass 1 Z ≠ 0
-- PLUG: exists_nonzero_algebraic_hodge_class_of_law (GREEN) applied to §8's
-- law + the §11 liveness — the no-free-lunch receipt (the seed itself).
```

### §12 THE MASTER PACKAGE

```lean
/-- **THE COMPLETE GENERAL-M RECEIPT.**  For the gated world (M ≥ 2, the
honest sphere class nonzero): the law; the exact-Hodge consequence through
the repository's conditional chain; the liveness of both live weights
(weight 0 of rank M by the component machine, weight 1 of rank M by the
honest sphere class); the no-free-lunch nonzero algebraic class; and the
rank-M family record (nonzero on every line, linearly independent, spanning
the designed weight-1 fiber). -/
theorem the_finiteLine_general_M_package (hM : 2 ≤ M)
    (A) (hspace) (ω) (hω : ω ≠ 0) (R₁) (hR₁) (Z₁) (hZ₁) (R₀) (hR₀) (Z₀) (hZ₀) :
    NativeGSTSingleFoldOrbitLaw (finiteLineWorld M) (finiteLineHodgeData ...) ∧
    EveryHodgeClassIsRationalAlgebraic (finiteLineHodgeData ...) ∧
    ¬ Subsingleton (ClassicalHodgeFiber ... 0) ∧
    ¬ Subsingleton (ClassicalHodgeFiber ... 1) ∧
    (∃ Z : codimensionCycles (finiteLineWorld M).X 1,
      (finiteLineHodgeData ...).cycleClass 1 Z ∈
        rationalHodgeSubspace ((finiteLineHodgeData ...).hodgeBigrading 1) ∧
      (finiteLineHodgeData ...).cycleClass 1 Z ≠ 0) ∧
    (∃ c : Fin M → singularCohomologyOf A.space 2,
      (∀ i, c i ≠ 0) ∧ LinearIndependent ℚ c ∧
      Submodule.span ℚ (Set.range c) =
        rationalHodgeSubspace ((finiteLineHodgeData ...).hodgeBigrading 1))
-- PLUG: §8 + exactHodge_of_one_GST_fold_orbit (GREEN) + §11 + §2 receipts +
-- §4's fiber_one.  The wave-60 §8 assembly pattern at the concrete world.
```

### §13 The every-frame consequences

```lean
/-- **EXACT HODGE.**  Every rational Hodge class of the assembled data is the
cycle class of a genuine algebraic cycle — through the repository's
conditional chain, applied at a positive-dimensional world that discharges
its own hypothesis at LIVE weights of rank M. -/
theorem finiteLine_everyHodge ... :
    EveryHodgeClassIsRationalAlgebraic (finiteLineHodgeData M A hspace ω Z₀ hZ₀ Z₁ hZ₁)
-- PLUG: exactHodge_of_one_GST_fold_orbit (native_GST_single_fold_orbit_law_finiteLine ...)

/-- **THE TYPED FS LAW, INSTANTIATED AT EVERY WEIGHT.**  Through the
native⇒typed bridge, the law yields — for every weight — a genuine typed
GSTHypothesisData over the native cycle module and the rational singular
cohomology whose complete GST hypothesis holds with the GENUINE rational
Hodge fiber of that weight. -/
theorem finiteLine_FS ... : ∀ p : Nat,
    ∃ D : GSTHypothesisComplete.GSTHypothesisData
        (codimensionCycles (finiteLineWorld M).X p)
        (RationalSingularCohomology (finiteLineHodgeData ...).analytification (2 * p)),
      GSTHypothesisComplete.GSTHypothesisComplete D ∧
      D.hodgeFiber = rationalHodgeSubspace
        ((finiteLineHodgeData ...).hodgeBigrading p)
-- PLUG: gst_FS_of_native_law (GREEN) — the finitePoint_FS spelling discipline
-- (the def-spelled statement to avoid the projection-vs-def isDefEq).

/-- **THE FINITE-RATIONAL-COMBINATION FORM.** -/
theorem finiteLine_finiteRationalCombination ... :
    EveryHodgeClassIsFiniteRationalCombination (finiteLineHodgeData ...)
-- PLUG: finiteRationalCombination_of_one_GST_fold_orbit (GREEN).
```

(The twelve-cell / `IntersectionChowFrame` re-citations of the landing
module's FrameWire section are already green and carry no new content at the
finite-line world; they are NOT re-instantiated here.)

---

## 2. THE GAP MAP — where the wave-63 M = 1 proof does NOT generalize

| # | The M = 1 piece (wave-63 file) | Why it fails at M ≥ 2 | The repair (all green) |
|---|---|---|---|
| **G1** | `haveI : Subsingleton (Fin 1) := fin1_subsingleton` (:309) — the index collapse under BOTH monogenic discharges | `Fin M` is not a subsingleton at M ≥ 2 | the M-cycle single-letter certificates (§6/§7): the orbit `(cyclicPred M)^[n] ⟨0⟩` visits EVERY index (`exists_iterate_cyclicPred`, green) — the identity Krylov matrix of wave-64, formalized as `span_range_cyclicIterate` |
| **G2** | `hmono₀` (:377-393): every H⁰ class is a multiple of `c₀w := E.symm (fun _ => 1)` — the transported CONSTANT-ONE function | at M ≥ 2 the constant-one spans only the diagonal; H⁰ has rank M | the weight-0 certificate: the seed class is the 0-th COMPONENT class (the indicator `Pi.single ⟨0⟩ 1`), the letter rotates the component family (hR₀), cyclicity = `span_range_cyclicIterate` + the component-family H⁰ span (`span_range_sphereComponentClass`, green) |
| **G3** | `hmono₁` (:396-412): every weight-1 fiber class is a multiple of the single point class `c₀` (the span induction over a one-element range) | the weight-1 fiber is the rank-M span of the family — not a rational line | the weight-1 certificate: the single M-cycle letter + the 0-th point-class seed; the orbit IS the rotated family (`sphereUnionCertificateOne_hodgeOrbit`, green); cyclicity = the cyclic-orbit span law against the designed fiber (`rationalHodgeSubspace_span_eq`, green) |
| **G4** | the discharge engine `native_GST_single_fold_orbit_law_of_dead_or_monogenic_weights` (:414-440) — the empty word at every weight | at M ≥ 2 weights 0 and 1 are neither dead nor monogenic — the engine cannot fire | the engine swap: `native_GST_single_fold_orbit_law_of_sphereUnion_gate` (green wave-60) fed with the two cyclic certificates; equivalently `positive_dimensional_live_core_law` (green wave-46) |
| **G5** | **the fold was the EMPTY WORD** — no correspondence anywhere in the wave-63 law | the M ≥ 2 discharge needs a GENUINE `RealizedFiniteClosedCorrespondence` rotating each family — the Krylov operator is no longer free | the letter gates R₀/R₁ (§5) — the realization gate (finiteLineCycle's graphs); the single-letter word `[( (1 : ℚ), R)]` with the word-Hodge field = the rotation-preservation proof (`sphereUnionWordOne_hodge`, green) |
| **G6** | `V` a free variable, the analytification a free input; the law never touched a concrete scheme | the general-M law must land on the CONCRETE world | §0: the world bundling (F1+F2+F3 + the NEW `finiteLineEmbedding_over_base` square — the only new lemma in the module) |
| **G7** | the weight-0 seed class = the transported constant-one function (:321) | must be the 0-th indicator at general M | §2/§3: the A-typed component family; the seed equation holds by the functional construction (unchanged trick) |
| **G8** | liveness = "the witness `c ⟨0⟩ ≠ 0`" (a single-class receipt, :446) | the honest liveness at M ≥ 2 is the pair-distinctness of the families | §11: the wave-60 §7 receipts re-instantiated (all green, generic in V/H) |
| **G9** | the package = the law + the live witness + the family record (§5) | the general-M package is richer | §12/§13: exact-Hodge + both liveness receipts + no-free-lunch + the rank-M family record + the per-weight typed FS consequences |

**TOP 3:** G1–G3 (the monogenic collapse — the mathematical heart: the
identity-matrix Krylov certificate replaces the one-generator spanning),
G5 (the fold: empty word → the M-cycle letter — the one new external gate),
G6 (the world bundling — the one new internal lemma).

---

## 3. THE IMPORT CLOSURE (exact module names)

```lean
import GSTFiniteLineWorldCarrier          -- F1: finiteLineScheme, finiteLineStructureMap,
                                          --    finiteLineCycle (+ _isIso, lineRotateGraded_pow),
                                          --    finiteLineEmbedding, lineGradedQuotientHom
import GSTFiniteLineClosedImmersion       -- F2: finiteLine_closedImmersion
import GSTFiniteLineSmoothness            -- F3: finiteLine_smoothness   (wave-67, IN FLIGHT)
import GSTPositiveDimensionalLawLanding   -- wave 60: sphereUnionCoe, spherePointClassWorld,
                                          --    spherePointClassWorld_rotate_of_pullback,
                                          --    sphereComponentClass, span_range_sphereComponentClass,
                                          --    the certificates + cyclicities, THE LAW ENGINE,
                                          --    the liveness receipts
import GSTPositiveDimensionalLiveWeightLaw -- wave 63: exists_cycle_functional (+ the M=1 anchor)
import GSTNativeSingleFoldOrbitLawLanding  -- the engines, gst_FS_of_native_law, no-free-lunch
```

Transitive (no direct import needed, but all green): `GSTFiniteLineRing`,
`GSTProjectiveOverC`, `GSTGeometricRealizationStage2D/2F/2G`,
`GSTClassicalHodgeFiberedCosmology`,
`GSTClassicalHodgeRealizedClosedCorrespondenceAlgebra`,
`GSTClassicalHodgeRealizedCorrespondenceKrylovFinale`,
`GSTClassicalHodgeFiniteClosedCorrespondence(+Operator)`,
`GSTHodgeSingleHypothesisConditional`, `GSTClassicalHodgeExactClayStatement`,
`GSTPositiveDimensionalLiveCoreKit`, `GSTPositiveDimensionalLiveCoreLaw`,
`GSTSphereUnionComponents`, `GSTComponentCohomologyZero`,
`GSTSingularCohomologyMaps`, `GSTSphereCycleLegs`,
`GSTSphereUnionPointClassGate`, `GSTCyclicOrbitSpan`,
`GSTFinitePointHodgeData`, `Mathlib`.

**Existence audit:** every name above exists in the repo today EXCEPT
`GSTFiniteLineSmoothness` (the wave-67 module — the single hard dependency
edge; the law module cannot land before F3). Direct-import discipline
(the W42E-IMPORTCHAIN lesson): the six imports above are all DIRECT — the
module consumes something from each.

---

## 4. THE RISK LEDGER (ranked, with fallbacks)

**R1 — the letter-gate discharge (EXTERNAL, highest impact on the program,
zero impact on this module's compilability).** Constructing R₀/R₁ as genuine
`RealizedFiniteClosedCorrespondence`s with the rotation equations. Sub-battles:
(i) `finiteLineCycle_over_base` — the cycle as a `ComplexSchemeEndomorphism`
(not yet proved anywhere; the graded rotation fixes the degree-zero piece,
so it should follow from the Proj.map calculus + the degree-zero triangle);
(ii) `realizes_on_points` for the assembled cycle-class maps — needs the
class of EVERY closed point (`cl(codim-1 point on line i) = c_i`), i.e. the
point-classification content; (iii) the operator identification with the
transported `sphereCycle` pullback (the analytification functoriality of the
cycle). *Fallback:* the law module is gate-form — it lands green without R1;
§10 gives the letter-free M = 1 law; the derived form
(`finiteLineLetterOne_rotate_of_pullback`, green) localizes (iii) to one
equation. The hand-built-letter precedent is the green finite-point
shift-word lane.

**R2 — the analytification receipt (EXTERNAL, same structure as R1).** The
ℂ-points classification `ComplexPoint (finiteLineWorld M) ≃ sphereUnionSpace M`
(the M Riemann spheres) — the `pointsEquiv` field of the AnalytificationData.
*Fallback:* gate-form inputs `(A, hspace)`; the module compiles and lands
green before that wave.

**R3 — `finiteLineEmbedding_over_base` (INTERNAL §0, medium).** No pin lemma
for `Proj.map`/`toSpecZero` naturality (verified against the wave-65.2-R pin
set). Route: the finite-point over_base Γ-route (`GSTFinitePointWorldCarrier.lean
:660-730`, green) transposed — the `toSpecΓ_SpecMap_ΓSpecIso` triangle + the
constants-through-degree-zero lemma (T6/hzero of the wave-67 recon, the
battle the finite-point lane already fought). Estimate 60–120 lines.
*Fallbacks:* (a) chartwise via the `awayι` squares + sheaf-morphism ext;
(b) the F3.4 stage ships it (the wave-67 Stage-4 design already lists it as
consumed — coordinate with F3 before authoring); (c) the world bundling moves
whole into F3.4 and the law module imports it (one-line switch).

**R4 — F3's smoothness itself (UPSTREAM).** The wave-67 Stage-1 chart
equivalence (`chart_monomial`/`chart_surjective`, its own RISK-1, ~150–250
lines). The law module simply waits; no mitigation inside this architecture.
*Fallback:* none needed here — the import edge is the contract.

**R5 — the assembled-H elaboration (INTERNAL, low).** The `def ... where`
form must elaborate the A-typed families against the `analytification := A`
literal (the `singularCohomologyOf_eq` rfl-defeq) and the match-arm
rfl-reductions (`hone`, `hstash`). *Fallback:* the wave-63 `set`-form —
assemble H inside each theorem (green precedent, at the cost of the §4
lemma layer); or split the def through `let`-free explicit chain (the §2/§3
top-level defs already isolate the risk).

**R6 — the weight-0 derived letter form (EXTERNAL, low).** A
`cycle_componentClass` rotation lemma (the M-cycle's H⁰ action) does not
exist in the green corpus — the raw gate `hR₀` suffices for the law, but the
letter wave will want the derived form for honesty documentation. *Fallback:*
the raw gate; the derivation (component-machine naturality) is the letter
wave's small item.

**R7 — spelling/CI friction (INTERNAL, low).** The choose-form of
`exists_cycle_functional`; the `⟨0, hM⟩` Fin-literal proof-irrelevance
matches; the tuple-with-ascription word spelling `((1 : ℚ), R)` (the 60.3
lesson); the same-line projection discipline (60.4); the `NeZero.pos`
spelling (W42E-NEZEROPOS); the local-instance priority bridges (wave-63
§0.5). All have green precedents cited inline in the skeleton.

---

## 5. THE SKELETON (`GSTFiniteLineGeneralMLaw.lean`)

Sorry-free placeholder structure: section headers + frozen statements +
`-- PLUG:` comments marking which green engine feeds which hole. (The
`...`-elisions are the repeated explicit argument blocks frozen in §1.)

```lean
import GSTFiniteLineWorldCarrier
import GSTFiniteLineClosedImmersion
import GSTFiniteLineSmoothness
import GSTPositiveDimensionalLawLanding
import GSTPositiveDimensionalLiveWeightLaw
import GSTNativeSingleFoldOrbitLawLanding

/-!
# THE GENERAL-M LAW — NativeGSTSingleFoldOrbitLaw on the finite-line world

[module docstring: the composition tower of §0 of the architecture record
repairs/wave68_A_law_architecture.md; the honesty ledger — the single
fenced core ω ≠ 0 enters only the liveness receipts; the gates (analytification
receipt, letter realization, cycle nontriviality) are explicit inputs; the
green-engine citation ledger.]
-/

set_option maxHeartbeats 200000000
set_option maxRecDepth 1000000

noncomputable section

open CategoryTheory
open AlgebraicTopology
open GSTProjectiveOverC
open GSTGeometricRealizationStage2D
open GSTGeometricRealizationStage2F
open GSTGeometricRealizationStage2G
open GSTClassicalHodgeExactClayStatement
open GSTSphereUnionComponents
open GSTComponentCohomologyZero
open GSTSingularCohomologyMaps
open GSTSphereUnionPointClassGate
open GSTPositiveDimensionalLiveCoreKit
open GSTPositiveDimensionalLiveCoreLaw
open GSTNativeSingleFoldOrbitLawLanding
open GSTHodgeSingleHypothesisConditional
open GSTFinitePointHodgeData
open GSTPositiveDimensionalLawLanding
open GSTPositiveDimensionalLiveWeightLaw
open GSTCyclicOrbitSpan
open GSTFiniteLineRing
open GSTFiniteLineWorldCarrier
open GSTFiniteLineClosedImmersion
open GSTFiniteLineSmoothness

namespace GSTFiniteLineGeneralMLaw

/-! ## §0 The world (F1+F2+F3) -/

theorem finiteLineEmbedding_over_base (M : ℕ) [NeZero M] :
    finiteLineEmbedding M ≫ projectiveSpaceToBase (2 * M - 1) =
      finiteLineStructureMap M := by
  -- PLUG: the finite-point Γ-route (:660-730) transposed; the T6/hzero
  -- constants-through-degree-zero lemma; R3 of the architecture record.

noncomputable def finiteLineWorld (M : ℕ) [NeZero M] :
    SmoothProjectiveComplexScheme where
  X := finiteLineScheme M
  structureMap := finiteLineStructureMap M
  smooth := finiteLine_smoothness M
  projective := ⟨2 * M - 1, finiteLineEmbedding M,
    finiteLine_closedImmersion M, finiteLineEmbedding_over_base M⟩

/-! ## §0.5 The instance bridges (wave-63 §0 discipline) -/

local instance ... -- instFLModule / instFLAddCommGroup (frozen in §0.5 above)

/-! ## §1 The analytification gate (INPUT: A, hspace) -/

variable (M : ℕ) [NeZero M]
variable (A : AnalytificationData (finiteLineWorld M))
variable (hspace : A.space = TopCat.of (sphereUnionSpace M))

/-! ## §2 The honest families (A-typed transports + receipts) -/

def finiteLinePointClass ... := ...            -- PLUG: the cast transport
def finiteLineComponentClass ... := ...        -- PLUG: componentCohomologyZeroEquivFinM
theorem finiteLinePointClass_ne_zero ...       -- PLUG: spherePointClass_ne_zero
theorem finiteLinePointClass_indep ...         -- PLUG: spherePointClass_indep
theorem span_range_finiteLineComponentClass ... -- PLUG: the wave-60 span route
theorem finiteLinePointClass_eq_world ...      -- PLUG: rfl
theorem finiteLineComponentClass_eq_world ...  -- PLUG: rfl

/-! ## §3 The seeds and the cycle-class maps -/

theorem exists_cycle_functional' ...           -- PLUG: GREEN wave-63, verbatim
def finiteLineSeedClassZero ... / def finiteLineSeedClassOne ...
def finiteLineCycleClassZero ... / def finiteLineCycleClassOne ...
  -- PLUG: choose-form + the wave-63 smul-calculus
theorem finiteLineCycleClassZero_seed ... / theorem finiteLineCycleClassOne_seed ...
  -- PLUG: choose_spec + one_smul

/-! ## §4 THE HODGE DATA ASSEMBLY at general M -/

noncomputable def finiteLineHodgeData ... := ...  -- the frozen where-literal
theorem finiteLineHodgeData_hone ...           -- PLUG: rfl + the bridge
theorem finiteLineHodgeData_hstash ...         -- PLUG: rcases + rfl (wave-63 :279)
theorem finiteLineHodgeData_fiber_one ...      -- PLUG: rationalHodgeSubspace_span_eq
theorem finiteLineHodgeData_fiber_zero ...     -- PLUG: rationalHodgeSubspace_eq_top_of_degree_zero
theorem finiteLineHodgeData_fiber_stash ...    -- PLUG: rationalHodgeSubspace_stash_eq_bot
theorem finiteLineHodgeData_seed_zero ...      -- PLUG: by construction
theorem finiteLineHodgeData_seed_one ...       -- PLUG: by construction

/-! ## §5 THE FOLD — the letter gates (INPUT) + the derived form -/

variable (ω : singularCohomologyOf (TopCat.of unitSphereType) 2)
variable (Z₁ : codimensionCycles (finiteLineWorld M).X 1) (hZ₁ : Z₁ ≠ 0)
variable (Z₀ : codimensionCycles (finiteLineWorld M).X 0) (hZ₀ : Z₀ ≠ 0)
variable (R₁ : RealizedFiniteClosedCorrespondence (finiteLineWorld M)
    (finiteLineHodgeData M A hspace ω Z₀ hZ₀ Z₁ hZ₁) 1)
variable (hR₁ : ∀ j : Fin M, R₁.cohomologyOperator
    (spherePointClassWorld M hspace ω j) =
      spherePointClassWorld M hspace ω (cyclicPred M j))
variable (R₀ : RealizedFiniteClosedCorrespondence (finiteLineWorld M)
    (finiteLineHodgeData M A hspace ω Z₀ hZ₀ Z₁ hZ₁) 0)
variable (hR₀ : ∀ j : Fin M, R₀.cohomologyOperator
    (sphereComponentClass M hM hspace j) =
      sphereComponentClass M hM hspace (cyclicPred M j))

theorem finiteLineLetterOne_rotate_of_pullback ...
  -- PLUG: GREEN spherePointClassWorld_rotate_of_pullback

/-! ## §6 THE WEIGHT-1 CERTIFICATE (the identity Krylov matrix) -/

noncomputable def finiteLineCertificateOne ...
  -- PLUG: GREEN sphereUnionCertificateOne
theorem finiteLineCertificateOne_isKrylovCyclic ...
  -- PLUG: GREEN sphereUnionCertificateOne_isKrylovCyclic
  -- (the formal shadow of the wave-64 det = 1 certificate)

/-! ## §7 THE WEIGHT-0 CERTIFICATE (the mirror) -/

noncomputable def finiteLineCertificateZero ...
  -- PLUG: GREEN sphereUnionCertificateZero
theorem finiteLineCertificateZero_isKrylovCyclic ...
  -- PLUG: GREEN sphereUnionCertificateZero_isKrylovCyclic

/-! ## §8 THE LAW -/

theorem native_GST_single_fold_orbit_law_finiteLine ... :
    NativeGSTSingleFoldOrbitLaw (finiteLineWorld M)
      (finiteLineHodgeData M A hspace ω Z₀ hZ₀ Z₁ hZ₁) := by
  -- PLUG: GREEN native_GST_single_fold_orbit_law_of_sphereUnion_gate with
  -- §4's hone/hstash/seed lemmas as the gate discharges.

/-! ## §9 The dead weights (the stash receipt) -/

theorem finiteLineHodgeData_deadWeights ...
  -- PLUG: subsingleton_hodgeFiber_of_eq_bot + fiber_stash

/-! ## §10 The M = 1 monogenic de-risking receipt (letter-free) -/

theorem native_GST_single_fold_orbit_law_finiteLine_one_line ...
  -- PLUG: the wave-63 §4 engine (fin1_subsingleton, hmono₀, hmono₁,
  -- native_GST_single_fold_orbit_law_of_dead_or_monogenic_weights).

/-! ## §11 The liveness receipts (2 ≤ M, ω-gated) -/

theorem finiteLine_weightZero_fiber_not_subsingleton ...
  -- PLUG: GREEN wave-60 weightZero_fiber_not_subsingleton
theorem finiteLine_weightOne_fiber_not_subsingleton ...
  -- PLUG: GREEN wave-60 weightOne_fiber_not_subsingleton (THE ω-core's
  -- single consumption site)
theorem finiteLine_exists_nonzero_algebraic_hodge_class ...
  -- PLUG: GREEN exists_nonzero_algebraic_hodge_class_of_law

/-! ## §12 THE MASTER PACKAGE -/

theorem the_finiteLine_general_M_package ...
  -- PLUG: §8 + exactHodge_of_one_GST_fold_orbit + §11 + §2 + §4

/-! ## §13 The every-frame consequences -/

theorem finiteLine_everyHodge ...
  -- PLUG: exactHodge_of_one_GST_fold_orbit ∘ §8
theorem finiteLine_FS ...
  -- PLUG: GREEN gst_FS_of_native_law ∘ §8 (the def-spelled statement)
theorem finiteLine_finiteRationalCombination ...
  -- PLUG: GREEN finiteRationalCombination_of_one_GST_fold_orbit ∘ §8

/-! ## Receipts -/

#check ... -- every declaration above
#print axioms native_GST_single_fold_orbit_law_finiteLine
#print axioms the_finiteLine_general_M_package
-- (target: [propext, Classical.choice, Quot.sound] only)

end GSTFiniteLineGeneralMLaw
end -- noncomputable section
```

---

## 6. The CI plan + honesty ledger

* Lane: `gst-finite-line-general-M-law.yml` (the campaign's standard
  per-module pattern: Lean v4.33.0-rc2 + Mathlib v4.33.0-rc2, `lake build`,
  the error/`sorryAx` grep gates, 95-min timeout). The module builds ONLY
  after `GSTFiniteLineSmoothness.lean` (F3) is green — sequence the lanes.
* Staged authoring order inside the module (each stage independently
  landable): (1) §0–§4 (the world + the assembly — needs only F1/F2/F3);
  (2) §10 (the M = 1 law — the first LAW on the board, letter-free);
  (3) §5–§9 + §8 (the letter-gated general-M law — pure green-engine
  plumbing); (4) §11–§13 (the receipts and consequences).
* Honesty ledger: no `sorry`, no new axioms, no `native_decide`. The fenced
  sphere-machine core (`ω ≠ 0`) is consumed ONLY at §11 (liveness) — never by
  the law. The three gate families (the analytification receipt, the letter
  realization, the cycle nontriviality) are explicit inputs, each owned by a
  named sibling wave; every other input is structural (the certified carrier
  shapes F1–F3). The general-M law at M ≥ 2 discharges the positive-
  dimensional live weight at rank M — the frontier's rank-≥2 core — through
  the single M-cycle fold with the identity Krylov matrix.
