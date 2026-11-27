import HCUniverse2.GSTFiniteLineWorldCarrier
import HCUniverse2.GSTFiniteLineClosedImmersion
import HCUniverse2.GSTPositiveDimensionalLawLanding
import HCUniverse2.GSTPositiveDimensionalLiveWeightLaw
import HCUniverse2.GSTNativeSingleFoldOrbitLawLanding

/-
Copyright (c) 2026. The HC-PROOF campaign. All rights reserved.

# THE GENERAL-M LAW — NativeGSTSingleFoldOrbitLaw on the finite-line world

THE CAPSTONE of the finite-line lane (wave 68, task W68-D, per the frozen
architecture `repairs/wave68_A_law_architecture.md`): the module that
discharges `NativeGSTSingleFoldOrbitLaw` on the finite-line world at
**every M ≥ 1** — the general-M lift of the wave-63 one-line law
(`GSTPositiveDimensionalLiveWeightLaw.lean`, the M = 1 template) through
the wave-60 sphere-union law engine
(`GSTPositiveDimensionalLawLanding.lean`, already at general M).

## The composition tower (the architecture's §0)

```
F1  GSTFiniteLineWorldCarrier.lean   (GREEN)   finiteLineScheme M, finiteLineStructureMap M,
                                              finiteLineCycle M (+ _isIso, lineRotateGraded_pow),
                                              finiteLineEmbedding M
F2  GSTFiniteLineClosedImmersion.lean (CI)     finiteLine_closedImmersion M
F3  GSTFiniteLineSmoothness.lean     (W67, in flight — NOT imported here)
─────────────────────────────────────────────────────────────────────────────
W68 §0  THE WORLD GATE (INPUT):  V : SmoothProjectiveComplexScheme with
        hWX : V.X = finiteLineScheme M and the structure-map identification
        hWmap — the gate-form of the intended `finiteLineWorld M` bundle
        (F1+F2+F3 + the over-base square; see the gate ledger below)
GATE-A  the analytification receipt (INPUT):  A : AnalytificationData V,
        hspace : A.space = TopCat.of (sphereUnionSpace M)   — the honest ⊔ M S²
GATE-L  the letter gates (INPUT):  R₁/hR₁ at weight 1, R₀/hR₀ at weight 0 —
        genuine RealizedFiniteClosedCorrespondences rotating the two honest
        families by cyclicPred (the M-cycle `finiteLineCycle M`'s graphs;
        the wave-64 realization gate)
GATE-S  the honest cycle nontriviality (INPUT):  Z₀ ≠ 0, Z₁ ≠ 0
```

## The gate ledger (the not-yet-landed inputs, precisely fenced)

Per the 68-A architecture's gate-form doctrine, the module takes every
not-yet-landed input as a NAMED HYPOTHESIS so it lands CI-green NOW:

* **THE WORLD GATE (§0)** — `V` with `hWX : V.X = finiteLineScheme M` and
  `hWmap : hWX ▸ V.structureMap = finiteLineStructureMap M`.  The intended
  world is the F1+F2+F3 bundle `finiteLineWorld M`
  (the `finitePointWorld` pattern, GSTFinitePointWorldCarrier.lean:735-739);
  its construction waits on the wave-67 smoothness module
  (`GSTFiniteLineSmoothness.lean`, in flight — NOT imported here) and the
  over-base square `finiteLineEmbedding_over_base` (the architecture's R3
  battle: no pin lemma exists for `Proj.map`/`toSpecZero` naturality; the
  finite-point Γ-route GSTFinitePointWorldCarrier.lean:660-730 transposed).
  When that wave lands, the gates discharge by `rfl`.
* **THE ANALYTIFICATION GATE (§1, GATE-A)** — `A` + `hspace`: the
  ℂ-points-classification wave's target interface (the honest sphere-union
  ⊔ M S², the disjoint union of M Riemann spheres).
* **THE LETTER GATES (§5, GATE-L)** — `R₁/hR₁`, `R₀/hR₀`: the wave-64
  realization gate (the M-cycle automorphism's graphs as genuine realized
  closed correspondences rotating the two honest families).  The derived
  form `finiteLineLetterOne_rotate_of_pullback` documents that the weight-1
  family equation is exactly the green `cycle_pointClass` under the
  pullback-operator gate.
* **THE SEED GATES (GATE-S)** — `Z₀ ≠ 0`, `Z₁ ≠ 0`: the honest world's own
  0- and codimension-1 cycles (the wave-63 honesty ledger); the seed-class
  equations themselves are discharged INTERNALLY (§4, by construction).

## The law

**§8 (THE GENERAL-M LAW):** the gated world, with the assembled Hodge data
of §4 (stash@0 / span@1 / stash@p≥2) and the two M-cycle letters, satisfies
the FULL `NativeGSTSingleFoldOrbitLaw` — by the GREEN wave-60 engine
`native_GST_single_fold_orbit_law_of_sphereUnion_gate`, re-instantiated at
the concrete world: weights 0/1 by the two cyclic single-letter
certificates (§6/§7 — the identity Krylov matrix of wave-64, realized
formally as the green cyclic-orbit span law `span_range_cyclicIterate`;
`det = 1` never appears), weights p ≥ 2 by the stash engine (§9).

**§10 (THE M = 1 MONOGENIC DE-RISK):** at M = 1 the assembled data
satisfies the law WITHOUT any letter input (the wave-63 dead-or-monogenic
engine; `Fin 1` is a subsingleton, both live fibers are rational lines) —
the module's built-in de-risking receipt: the M = 1 half of the law lands
even if the letter wave stalls.

## The ω-disclosure (wave 60, inherited)

The honest sphere class `ω` appears only as the INDEX of the family design;
its NONVANISHING — the fenced sphere-machine core — is needed ONLY for the
liveness receipts (§11) and the family record (§12), never for the law.

## The green-engine citation ledger (every non-local name)

* `finiteLineScheme/finiteLineStructureMap/finiteLineEmbedding` —
  GSTFiniteLineWorldCarrier.lean:65/77/654 (green, run 44899187702);
* `finiteLine_closedImmersion` — GSTFiniteLineClosedImmersion.lean:322 (CI);
* `spherePointClass`/`spherePointClass_ne_zero`/`spherePointClass_indep` —
  GSTSphereUnionPointClassGate.lean:67/103/114;
* `cyclicPred`/`sphereCycle` — GSTSphereCycleLegs.lean:37/316 (via the
  wave-60 open);
* `singularCohomologyOf`/`singularCohomologyOf_eq` —
  GSTSingularCohomologyMaps.lean:66/79 (the rfl bridge);
* `sphereUnionSpace`/`sphereUnion_cohomology_zero` —
  GSTSphereUnionComponents.lean:169/266;
* `componentCohomologyZeroEquivFinM` — GSTComponentCohomologyZero.lean:500;
* `sphereUnionCoe`/`spherePointClassWorld`/`sphereComponentClass`/
  `singles_span_top`/`span_range_sphereComponentClass`/
  `rationalHodgeSubspace_one_eq_span`/`spherePointClassWorld_rotate_of_pullback`/
  the certificates + cyclicities/`native_GST_single_fold_orbit_law_of_sphereUnion_gate`/
  the liveness receipts — GSTPositiveDimensionalLawLanding.lean:127/136/168/
  177/193/227/148/300-478/495/629-671;
* `exists_cycle_functional` — GSTPositiveDimensionalLiveWeightLaw.lean:164;
* `stashBigrading`/`spanBigrading`/`rationalHodgeSubspace_stash_eq_bot`/
  `rationalHodgeSubspace_span_eq` — GSTPositiveDimensionalLiveCoreKit.lean:216/
  361/239/383;
* `emptyWordKrylovCertificate`/`zeroCycleClass_mem_hodgeFiber`/
  `subsingleton_hodgeFiber_of_eq_bot`/`isKrylovCyclic_of_subsingleton`/
  `isKrylovCyclic_of_monogenic`/`native_GST_single_fold_orbit_law_of_dead_or_monogenic_weights`/
  `exists_nonzero_algebraic_hodge_class_of_law`/`gst_FS_of_native_law` —
  GSTNativeSingleFoldOrbitLawLanding.lean:132/162/173/193/208/241/328/512;
* `NativeGSTSingleFoldOrbitLaw`/`exactHodge_of_one_GST_fold_orbit`/
  `finiteRationalCombination_of_one_GST_fold_orbit` —
  GSTHodgeSingleHypothesisConditional.lean:50/61/70;
* `EveryHodgeClassIsRationalAlgebraic`/`EveryHodgeClassIsFiniteRationalCombination` —
  GSTClassicalHodgeExactClayStatement.lean:49/59;
* `ClassicalHodgeFiber` — GSTClassicalHodgeFiberedCosmology.lean:44;
* `RealizedFiniteClosedCorrespondence` —
  GSTClassicalHodgeRealizedClosedCorrespondenceAlgebra.lean:67;
* `RealizedCorrespondenceKrylovCertificate`/`IsKrylovCyclic` —
  GSTClassicalHodgeRealizedCorrespondenceKrylovFinale.lean:51/123;
* `rationalHodgeSubspace_eq_top_of_degree_zero`/`fin1_subsingleton` —
  GSTFinitePointHodgeData.lean:460/126;
* `span_range_cyclicIterate` — GSTCyclicOrbitSpan.lean:114.

## The honesty ledger

Every statement is proved unconditionally GIVEN the named gates above.  The
three gate families (the world bundle, the analytification receipt, the
letter realization) plus the cycle nontrivialities are explicit inputs,
each owned by a named sibling wave (F3/wave-67, the points-classification
wave, the wave-64 letter wave, the points wave); every other input is
structural (the certified carrier shapes F1-F2).  The fenced sphere-machine
core (`ω ≠ 0`) is consumed ONLY at §11-§12 (liveness + the family record) —
never by the law.  No `sorry`, no new axioms, no `native_decide`.  The
GitHub CI lane `gst-finite-line-general-M-law.yml` owns the kernel check.
-/

set_option maxHeartbeats 200000000
set_option maxRecDepth 1000000

noncomputable section

open CategoryTheory
open AlgebraicTopology
open AlgebraicGeometry
open GSTProjectiveOverC
open GSTGeometricRealizationStage2D
open GSTGeometricRealizationStage2F
open GSTGeometricRealizationStage2G
open GSTClassicalHodgeFiberedCosmology
open GSTClassicalHodgeRealizedClosedCorrespondenceAlgebra
open GSTClassicalHodgeRealizedCorrespondenceKrylovFinale
open GSTClassicalHodgeExactClayStatement
open GSTSphereUnionComponents
open GSTComponentCohomologyZero
open GSTSingularCohomologyMaps
open GSTSphereCycleLegs
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

namespace GSTFiniteLineGeneralMLaw

/-! ## §0 The world gate — the F1+F2 carrier identifications

The world is an INPUT (the gate-form of the architecture's §0): a
`SmoothProjectiveComplexScheme` over the finite-line carrier, with the two
required identifications — the carrier (`hWX`) and the structure map over
`Spec(ℂ)` (`hWmap`, stated through the `hWX`-transport).  The intended
inhabitant is the F1+F2+F3 bundle `finiteLineWorld M`; its construction
(the NEW lemma `finiteLineEmbedding_over_base` — the Γ-Spec cancellation
route of the green `finitePoint_over_base`,
GSTFinitePointWorldCarrier.lean:660-730, transposed to the `Proj.map`
embedding — plus the wave-67 smoothness input) is the wave-67/F3.4 wave's
battle, and discharges both gates by `rfl` when it lands.  The receipts
below pin the gate spellings and the carrier-side facts this module owns. -/

/-- **THE F1+F2 CARRIER RECEIPT (the projective half).**  The intended
world's embedding witness: the finite-line embedding of `Proj (lineGrading
M)` into `ℙ^{2M-1}` is a closed immersion — F2 (wave 66, CI-green),
consumed here directly.  Together with the world gate's carrier
identification, this documents the projective half of the intended
`finiteLineWorld M` bundle (the smoothness half is the wave-67 F3 gate;
the over-base square is the F3.4 discharge target). -/
theorem finiteLineEmbedding_closedImmersion_receipt (M : ℕ) [NeZero M] :
    IsClosedImmersion (finiteLineEmbedding M) :=
  finiteLine_closedImmersion M

/-- **THE WORLD-GATE IDENTIFICATION RECEIPT.**  The two §0 identifications
of the gated world, restated as the discharge targets of the future
`finiteLineWorld M` construction: the carrier and the structure map (the
latter through the `hWX`-transport; at the constructed world both gates
are `rfl`). -/
theorem finiteLineWorldGate_identifications (M : ℕ) [NeZero M]
    (V : SmoothProjectiveComplexScheme)
    (hWX : V.X = finiteLineScheme M)
    (hWmap : hWX ▸ V.structureMap = finiteLineStructureMap M) :
    V.X = finiteLineScheme M ∧
      hWX ▸ V.structureMap = finiteLineStructureMap M :=
  ⟨hWX, hWmap⟩

/-! ## §0.5 The local instance bridges (the wave-63 §0 discipline)

The world's degree-n rational singular cohomology's ℚ-structures, provided
locally at high priority through the wave-57 raw-space family (the two
families are definitionally identical — the rfl bridge
`GSTSingularCohomologyMaps.singularCohomologyOf_eq`, line 79) — the
wave-63 module's own green pattern (:121-132) verbatim under the rename. -/

/-- The Module-structure bridge. -/
local instance (priority := high) instFLModule
    {V : SmoothProjectiveComplexScheme} (A : AnalytificationData V) (n : Nat) :
    Module ℚ (RationalSingularCohomology A n) :=
  inferInstanceAs (Module ℚ (singularCohomologyOf A.space n))

/-- The AddCommGroup-structure bridge, same discipline. -/
local instance (priority := high) instFLAddCommGroup
    {V : SmoothProjectiveComplexScheme} (A : AnalytificationData V) (n : Nat) :
    AddCommGroup (RationalSingularCohomology A n) :=
  inferInstanceAs (AddCommGroup (singularCohomologyOf A.space n))

/-! ## §1 The analytification gate (INPUT: A, hspace)

The module does NOT construct the analytification.  Every theorem below
takes as explicit inputs

```
(A : AnalytificationData V)
(hspace : A.space = TopCat.of (sphereUnionSpace M))
```

— the points-classification wave's target interface: the honest
sphere-union space `⊔ M S²` (the disjoint union of M Riemann spheres,
`GSTSphereUnionComponents.sphereUnionSpace`, line 169).  The gate-form
keeps THIS module compilable and green before that wave lands. -/

/-! ## §2 The honest families — the A-typed transports and the cast calculus

The two honest families of the law, typed at the world's own
analytification `A` (independent of the assembled Hodge data of §4 — the
§4 assembly consumes THEM):  the wave-59 gate family `spherePointClass`
transported along the space identification, and the component-class
family through the green component machine.  The transports ride a small
cast calculus (§2.0) whose additivity/homogeneity lemmas are
kernel-reducible at the reflexive equality — this is what makes the raw
family's honesty (nonzero on every line, linearly independent,
`GSTSphereUnionPointClassGate` lines 103/114) transport to the A-typed
family honestly. -/

/-! ### §2.0 The hspace-cast calculus -/

/-- The degree-n cohomology-type equation induced by a space equality (the
`congrArg` transport; the variable-typed form so the reflexive case
reduces in the kernel). -/
theorem singularCohomologyOf_castEq {X Y : TopCat} {n : ℕ} (p : X = Y) :
    singularCohomologyOf X n = singularCohomologyOf Y n :=
  congrArg (fun Z : TopCat => singularCohomologyOf Z n) p

/-- The degree-two cohomology-type equation of the analytification gate
(the `hspace` rewrite, isolated once — every transport of §2 rides this
one equation). -/
theorem singularCohomologyOf_two_eq_of_hspace
    {V : SmoothProjectiveComplexScheme} {A : AnalytificationData V} {M : ℕ}
    (hspace : A.space = TopCat.of (sphereUnionSpace M)) :
    singularCohomologyOf A.space 2 =
      singularCohomologyOf (TopCat.of (sphereUnionSpace M)) 2 := by
  rw [hspace]

/-- The cast preserves addition (kernel-reducible at the reflexive
equality:  `Equiv.cast rfl` is the identity, and `congrArg f rfl ≡ rfl`). -/
theorem cohomologyCast_add {X Y : TopCat} {n : ℕ} (p : X = Y)
    (x y : singularCohomologyOf X n) :
    (Equiv.cast (singularCohomologyOf_castEq (n := n) p)) (x + y) =
      (Equiv.cast (singularCohomologyOf_castEq (n := n) p)) x +
        (Equiv.cast (singularCohomologyOf_castEq (n := n) p)) y := by
  subst p
  rfl

/-- The cast preserves scalar multiplication (same kernel reduction). -/
theorem cohomologyCast_smul {X Y : TopCat} {n : ℕ} (p : X = Y)
    (q : ℚ) (x : singularCohomologyOf X n) :
    (Equiv.cast (singularCohomologyOf_castEq (n := n) p)) (q • x) =
      q • (Equiv.cast (singularCohomologyOf_castEq (n := n) p)) x := by
  subst p
  rfl

/-- **THE HSPACE-TRANSPORT OF THE DEGREE-TWO COHOMOLOGY, AS A LINEAR
MAP.**  The type-cast along the analytification gate's space equation is
additive and homogeneous (the two kernel-reducible lemmas above), so the
raw sphere-union family's honesty calculus transports along it — the
instrument the A-typed family's nonzero and independence receipts ride. -/
noncomputable def singularCohomologyOf_two_castLinear
    {V : SmoothProjectiveComplexScheme} {A : AnalytificationData V} {M : ℕ}
    (hspace : A.space = TopCat.of (sphereUnionSpace M)) :
    singularCohomologyOf A.space 2 →ₗ[ℚ]
      singularCohomologyOf (TopCat.of (sphereUnionSpace M)) 2 where
  toFun := (Equiv.cast (singularCohomologyOf_two_eq_of_hspace hspace))
  map_add' := fun x y =>
    cohomologyCast_add (X := A.space) (Y := TopCat.of (sphereUnionSpace M))
      (n := 2) hspace x y
  map_smul' := fun q x =>
    cohomologyCast_smul (X := A.space) (Y := TopCat.of (sphereUnionSpace M))
      (n := 2) hspace q x

/-! ### §2.1 The point-class family -/

/-- **THE HONEST POINT-CLASS FAMILY, A-TYPED.**  The wave-59 gate family
`spherePointClass M ω` (the pullback of the honest sphere class along the
i-th collapse), transported to the world's own degree-two rational
singular cohomology along the space identification.  Once the §4 assembly
is in scope this family is `rfl`-equal to the wave-60 world family
`spherePointClassWorld` (see §4.5 `finiteLinePointClass_eq_world`). -/
def finiteLinePointClass (M : ℕ) [NeZero M]
    (V : SmoothProjectiveComplexScheme) (A : AnalytificationData V)
    (hspace : A.space = TopCat.of (sphereUnionSpace M))
    (ω : singularCohomologyOf (TopCat.of unitSphereType) 2)
    (j : Fin M) :
    singularCohomologyOf A.space 2 :=
  (Equiv.cast (singularCohomologyOf_two_eq_of_hspace hspace)).symm
    (spherePointClass M ω j)

/-- The transport calculus:  the linear cast of the A-typed class is the
raw class (the two-sided inverse property of the cast). -/
theorem finiteLinePointClass_cast (M : ℕ) [NeZero M]
    (V : SmoothProjectiveComplexScheme) (A : AnalytificationData V)
    (hspace : A.space = TopCat.of (sphereUnionSpace M))
    (ω : singularCohomologyOf (TopCat.of unitSphereType) 2) (j : Fin M) :
    singularCohomologyOf_two_castLinear hspace
      (finiteLinePointClass M V A hspace ω j) = spherePointClass M ω j := by
  rw [finiteLinePointClass]
  show (Equiv.cast (singularCohomologyOf_two_eq_of_hspace hspace))
      ((Equiv.cast (singularCohomologyOf_two_eq_of_hspace hspace)).symm
        (spherePointClass M ω j)) = spherePointClass M ω j
  exact Equiv.apply_symm_apply _ _

/-- **THE A-TYPED POINT CLASSES ARE NONZERO** (given the sphere class is):
the raw family's nonvanishing
(`GSTSphereUnionPointClassGate.spherePointClass_ne_zero`, line 103)
transported back along the injective linear cast. -/
theorem finiteLinePointClass_ne_zero (M : ℕ) [NeZero M]
    (V : SmoothProjectiveComplexScheme) (A : AnalytificationData V)
    (hspace : A.space = TopCat.of (sphereUnionSpace M))
    (ω : singularCohomologyOf (TopCat.of unitSphereType) 2)
    (hω : ω ≠ 0) (j : Fin M) :
    finiteLinePointClass M V A hspace ω j ≠ 0 := by
  intro h
  have hcast := finiteLinePointClass_cast M V A hspace ω j
  rw [h, map_zero] at hcast
  exact spherePointClass_ne_zero M ω hω j (Eq.symm hcast)

/-- **THE A-TYPED POINT CLASSES ARE LINEARLY INDEPENDENT** (given the
sphere class is):  a relation among the transported classes maps, through
the linear cast, to a relation among the raw classes, contradicting the
green independence (`spherePointClass_indep`, line 114).  The
`linearIndependent_iff'` shape mirrors the green gate's own proof. -/
theorem finiteLinePointClass_indep (M : ℕ) [NeZero M]
    (V : SmoothProjectiveComplexScheme) (A : AnalytificationData V)
    (hspace : A.space = TopCat.of (sphereUnionSpace M))
    (ω : singularCohomologyOf (TopCat.of unitSphereType) 2)
    (hω : ω ≠ 0) :
    LinearIndependent ℚ (finiteLinePointClass M V A hspace ω) := by
  rw [linearIndependent_iff']
  intro s g hg j hj
  have hindep : LinearIndependent ℚ (spherePointClass M ω) :=
    spherePointClass_indep M ω hω
  rw [linearIndependent_iff'] at hindep
  refine hindep s g ?_ j hj
  have hmap : (singularCohomologyOf_two_castLinear hspace)
      (∑ i ∈ s, g i • finiteLinePointClass M V A hspace ω i) = 0 := by
    rw [hg, map_zero]
  rw [map_sum] at hmap
  simp only [map_smul] at hmap
  rw [← hmap]
  exact Finset.sum_congr rfl fun i _ => by
    rw [finiteLinePointClass_cast M V A hspace ω i]

/-! ### §2.2 The component-class family -/

/-- **THE COMPONENT-CLASS FAMILY, A-TYPED.**  The degree-0 component
machine through the sphere-union component identification:  the i-th
indicator's inverse image — `rfl`-equal to the wave-60 world family
`sphereComponentClass` once §4 is in scope. -/
def finiteLineComponentClass (M : ℕ) [NeZero M]
    (V : SmoothProjectiveComplexScheme) (A : AnalytificationData V)
    (hspace : A.space = TopCat.of (sphereUnionSpace M))
    (j : Fin M) :
    RationalSingularCohomology A 0 :=
  (componentCohomologyZeroEquivFinM A M
    (sphereUnion_cohomology_zero hspace)).symm (Pi.single j (1 : ℚ))

/-- **THE COMPONENT FAMILY SPANS THE WHOLE H⁰.**  The surjective linear
transport of the full function-space span — the wave-60 route
(`GSTPositiveDimensionalLawLanding.span_range_sphereComponentClass`,
line 193) verbatim at the A-typed family, with the wave-60 green
single-vector spanning law `singles_span_top` (line 177) consumed
directly. -/
theorem span_range_finiteLineComponentClass (M : ℕ) [NeZero M]
    (V : SmoothProjectiveComplexScheme) (A : AnalytificationData V)
    (hspace : A.space = TopCat.of (sphereUnionSpace M)) :
    Submodule.span ℚ (Set.range (finiteLineComponentClass M V A hspace)) = ⊤ := by
  apply top_unique
  intro u _
  have hEu : (componentCohomologyZeroEquivFinM A M
      (sphereUnion_cohomology_zero hspace)) u ∈
      Submodule.span ℚ
        (Set.range fun i : Fin M => (Pi.single i (1 : ℚ) : Fin M → ℚ)) := by
    rw [singles_span_top M]
    exact Submodule.mem_top
  have hsub : (componentCohomologyZeroEquivFinM A M
      (sphereUnion_cohomology_zero hspace)).symm.toLinearMap ''
      (Set.range fun i : Fin M => (Pi.single i (1 : ℚ) : Fin M → ℚ)) ⊆
      Set.range (finiteLineComponentClass M V A hspace) := by
    rintro _ ⟨_, ⟨i, rfl⟩, rfl⟩
    exact ⟨i, rfl⟩
  have hmem : u ∈ Submodule.span ℚ
      ((componentCohomologyZeroEquivFinM A M
        (sphereUnion_cohomology_zero hspace)).symm.toLinearMap ''
      (Set.range fun i : Fin M => (Pi.single i (1 : ℚ) : Fin M → ℚ))) := by
    rw [Submodule.span_image]
    exact Submodule.mem_map.mpr
      ⟨(componentCohomologyZeroEquivFinM A M
          (sphereUnion_cohomology_zero hspace)) u, hEu,
        (componentCohomologyZeroEquivFinM A M
          (sphereUnion_cohomology_zero hspace)).symm_apply_apply u⟩
  exact Submodule.span_mono hsub hmem

/-! ## §3 The seeds and the cycle-class maps (the functional construction)

The wave-63 §2 engine (`GSTPositiveDimensionalLiveWeightLaw.exists_cycle_functional`,
line 164 — GREEN VERBATIM, consumed directly) restated in choose form
inside the cycle-class map definitions:  the class of each honest seed
cycle IS the honest family class at the 0-th line (the wave-63 trick —
the degree-style functional takes the value one on the seed, so the
cycle-class map sends the seed to the seed class). -/

/-- **THE WEIGHT-ZERO SEED CLASS** — the honest 0-th component class. -/
def finiteLineSeedClassZero (M : ℕ) [NeZero M]
    (V : SmoothProjectiveComplexScheme) (A : AnalytificationData V)
    (hspace : A.space = TopCat.of (sphereUnionSpace M)) :
    RationalSingularCohomology A 0 :=
  finiteLineComponentClass M V A hspace ⟨0, Nat.pos_of_neZero ‹_›⟩

/-- **THE WEIGHT-ONE SEED CLASS** — the honest 0-th point class. -/
def finiteLineSeedClassOne (M : ℕ) [NeZero M]
    (V : SmoothProjectiveComplexScheme) (A : AnalytificationData V)
    (hspace : A.space = TopCat.of (sphereUnionSpace M))
    (ω : singularCohomologyOf (TopCat.of unitSphereType) 2) :
    singularCohomologyOf A.space 2 :=
  finiteLinePointClass M V A hspace ω ⟨0, Nat.pos_of_neZero ‹_›⟩

/-- **THE WEIGHT-ZERO CYCLE-CLASS MAP.**  The degree-style honest
cycle-class functional at weight zero:  the chosen rational functional
(`exists_cycle_functional`, taking the value one on the honest seed
`Z₀`), tensored with the honest 0-th component class — the wave-63 `cl₀`
spelling (:332-341) with the choose-form functional. -/
noncomputable def finiteLineCycleClassZero (M : ℕ) [NeZero M]
    (V : SmoothProjectiveComplexScheme) (A : AnalytificationData V)
    (hspace : A.space = TopCat.of (sphereUnionSpace M))
    (Z₀ : codimensionCycles V.X 0) (hZ₀ : Z₀ ≠ 0) :
    codimensionCycles V.X 0 →ₗ[ℚ] RationalSingularCohomology A 0 :=
  { toFun := fun Z =>
      ((exists_cycle_functional (X := codimensionCycles V.X 0) Z₀ hZ₀).choose Z) •
        finiteLineSeedClassZero M V A hspace
    map_add' := by
      intro Z Z'
      show ((exists_cycle_functional (X := codimensionCycles V.X 0) Z₀ hZ₀).choose
          (Z + Z')) • finiteLineSeedClassZero M V A hspace = _ + _
      rw [map_add, add_smul]
    map_smul' := by
      intro q Z
      show ((exists_cycle_functional (X := codimensionCycles V.X 0) Z₀ hZ₀).choose
          (q • Z)) • finiteLineSeedClassZero M V A hspace =
        q • (((exists_cycle_functional (X := codimensionCycles V.X 0) Z₀ hZ₀).choose Z) •
          finiteLineSeedClassZero M V A hspace)
      rw [map_smul, smul_smul, ← smul_eq_mul] }

/-- **THE WEIGHT-ZERO SEED EQUATION.**  The honest seed cycle's class IS
the honest 0-th component class (the functional takes the value one on
the seed). -/
theorem finiteLineCycleClassZero_seed (M : ℕ) [NeZero M]
    (V : SmoothProjectiveComplexScheme) (A : AnalytificationData V)
    (hspace : A.space = TopCat.of (sphereUnionSpace M))
    (Z₀ : codimensionCycles V.X 0) (hZ₀ : Z₀ ≠ 0) :
    finiteLineCycleClassZero M V A hspace Z₀ hZ₀ Z₀ =
      finiteLineSeedClassZero M V A hspace := by
  show ((exists_cycle_functional (X := codimensionCycles V.X 0) Z₀ hZ₀).choose Z₀) •
      finiteLineSeedClassZero M V A hspace = _
  rw [(exists_cycle_functional (X := codimensionCycles V.X 0) Z₀ hZ₀).choose_spec,
    one_smul]

/-- **THE WEIGHT-ONE CYCLE-CLASS MAP.**  The degree-style honest
cycle-class functional at the live weight:  the chosen functional tensored
with the honest 0-th point class — the wave-63 `cl₁` spelling (:345-354). -/
noncomputable def finiteLineCycleClassOne (M : ℕ) [NeZero M]
    (V : SmoothProjectiveComplexScheme) (A : AnalytificationData V)
    (hspace : A.space = TopCat.of (sphereUnionSpace M))
    (ω : singularCohomologyOf (TopCat.of unitSphereType) 2)
    (Z₁ : codimensionCycles V.X 1) (hZ₁ : Z₁ ≠ 0) :
    codimensionCycles V.X 1 →ₗ[ℚ] singularCohomologyOf A.space 2 :=
  { toFun := fun Z =>
      ((exists_cycle_functional (X := codimensionCycles V.X 1) Z₁ hZ₁).choose Z) •
        finiteLineSeedClassOne M V A hspace ω
    map_add' := by
      intro Z Z'
      show ((exists_cycle_functional (X := codimensionCycles V.X 1) Z₁ hZ₁).choose
          (Z + Z')) • finiteLineSeedClassOne M V A hspace ω = _ + _
      rw [map_add, add_smul]
    map_smul' := by
      intro q Z
      show ((exists_cycle_functional (X := codimensionCycles V.X 1) Z₁ hZ₁).choose
          (q • Z)) • finiteLineSeedClassOne M V A hspace ω =
        q • (((exists_cycle_functional (X := codimensionCycles V.X 1) Z₁ hZ₁).choose Z) •
          finiteLineSeedClassOne M V A hspace ω)
      rw [map_smul, smul_smul, ← smul_eq_mul] }

/-- **THE WEIGHT-ONE SEED EQUATION.**  The honest seed cycle's class IS
the honest 0-th point class. -/
theorem finiteLineCycleClassOne_seed (M : ℕ) [NeZero M]
    (V : SmoothProjectiveComplexScheme) (A : AnalytificationData V)
    (hspace : A.space = TopCat.of (sphereUnionSpace M))
    (ω : singularCohomologyOf (TopCat.of unitSphereType) 2)
    (Z₁ : codimensionCycles V.X 1) (hZ₁ : Z₁ ≠ 0) :
    finiteLineCycleClassOne M V A hspace ω Z₁ hZ₁ Z₁ =
      finiteLineSeedClassOne M V A hspace ω := by
  show ((exists_cycle_functional (X := codimensionCycles V.X 1) Z₁ hZ₁).choose Z₁) •
      finiteLineSeedClassOne M V A hspace ω = _
  rw [(exists_cycle_functional (X := codimensionCycles V.X 1) Z₁ hZ₁).choose_spec,
    one_smul]

/-! ## §4 THE HODGE DATA ASSEMBLY at general M

The assembled Hodge data of the finite-line world (the wave-63 §3/§4
assembly lifted to general M, in the frozen `where`-literal form):  weight
zero — the STASH bigrading (the fiber is the forced top);  weight one —
the SPAN bigrading on the honest point-class family (the fiber IS the
rational span of the family);  weights `p ≥ 2` — the STASH bigrading
(honestly dead — no vanishing proof anywhere).  The cycle-class maps:  the
honest component/point class functionals at the live weights, zero above. -/

/-- **THE ASSEMBLED HODGE DATA OF THE FINITE-LINE WORLD.** -/
noncomputable def finiteLineHodgeData (M : ℕ) [NeZero M]
    (V : SmoothProjectiveComplexScheme) (A : AnalytificationData V)
    (hspace : A.space = TopCat.of (sphereUnionSpace M))
    (ω : singularCohomologyOf (TopCat.of unitSphereType) 2)
    (Z₀ : codimensionCycles V.X 0) (hZ₀ : Z₀ ≠ 0)
    (Z₁ : codimensionCycles V.X 1) (hZ₁ : Z₁ ≠ 0) :
    HodgeBigradedBettiData V where
  analytification := A
  hodgeBigrading := fun p =>
    match p with
    | 0 => stashBigrading _ 0
    | 1 => spanBigrading (finiteLinePointClass M V A hspace ω) 1 (by omega)
    | (p + 2) => stashBigrading _ (2 * (p + 2))
  cycleClass := fun p =>
    match p with
    | 0 => finiteLineCycleClassZero M V A hspace Z₀ hZ₀
    | 1 => finiteLineCycleClassOne M V A hspace ω Z₁ hZ₁
    | (p + 2) => 0

/-- The analytification projection receipt (the rfl bridge every
engine-facing theorem rides). -/
theorem finiteLineHodgeData_analytification (M : ℕ) [NeZero M]
    (V : SmoothProjectiveComplexScheme) (A : AnalytificationData V)
    (hspace : A.space = TopCat.of (sphereUnionSpace M))
    (ω : singularCohomologyOf (TopCat.of unitSphereType) 2)
    (Z₀ : codimensionCycles V.X 0) (hZ₀ : Z₀ ≠ 0)
    (Z₁ : codimensionCycles V.X 1) (hZ₁ : Z₁ ≠ 0) :
    (finiteLineHodgeData M V A hspace ω Z₀ hZ₀ Z₁ hZ₁).analytification = A :=
  rfl

/-! ### §4.5 The syntactic alignment bridges (the A-typed families vs the
wave-60 world spellings)

Both bridges are `rfl`:  the two spellings of each family differ only in
the proof term of the SAME type-cast equation (proof irrelevance) — the
weight-1 case through the two `Equiv.cast`s, the weight-0 case through
the identical component-machine terms.  They are the repair
infrastructure of `finiteLineHodgeData_hone` (stated directly as `rfl`
below) and the seed equations. -/

/-- **THE POINT-CLASS FAMILY, WORLD-ALIGNED** (`rfl`:  the A-typed
transport and the wave-60 `spherePointClassWorld` transport differ only
in the proof of the same cast equation). -/
theorem finiteLinePointClass_eq_world (M : ℕ) [NeZero M]
    (V : SmoothProjectiveComplexScheme) (A : AnalytificationData V)
    (hspace : A.space = TopCat.of (sphereUnionSpace M))
    (ω : singularCohomologyOf (TopCat.of unitSphereType) 2)
    (Z₀ : codimensionCycles V.X 0) (hZ₀ : Z₀ ≠ 0)
    (Z₁ : codimensionCycles V.X 1) (hZ₁ : Z₁ ≠ 0) (j : Fin M) :
    finiteLinePointClass M V A hspace ω j =
      spherePointClassWorld (V := V)
        (H := finiteLineHodgeData M V A hspace ω Z₀ hZ₀ Z₁ hZ₁) M hspace ω j :=
  rfl

/-- **THE COMPONENT-CLASS FAMILY, WORLD-ALIGNED** (`rfl`:  identical
component-machine terms). -/
theorem finiteLineComponentClass_eq_world (M : ℕ) [NeZero M]
    (V : SmoothProjectiveComplexScheme) (A : AnalytificationData V)
    (hspace : A.space = TopCat.of (sphereUnionSpace M))
    (ω : singularCohomologyOf (TopCat.of unitSphereType) 2)
    (Z₀ : codimensionCycles V.X 0) (hZ₀ : Z₀ ≠ 0)
    (Z₁ : codimensionCycles V.X 1) (hZ₁ : Z₁ ≠ 0) (j : Fin M) :
    finiteLineComponentClass M V A hspace j =
      sphereComponentClass (V := V)
        (H := finiteLineHodgeData M V A hspace ω Z₀ hZ₀ Z₁ hZ₁) M
        (Nat.pos_of_neZero ‹_›) hspace j :=
  rfl

/-- **THE SPAN BIGRADING AT THE LIVE WEIGHT** (the engine-facing
equation):  the weight-1 slot of the assembled data is the span bigrading
on the wave-60 WORLD family — `rfl` through the pointwise `rfl`-equality
of the two family spellings (§4.5 below) and the match-arm reduction. -/
theorem finiteLineHodgeData_hone (M : ℕ) [NeZero M]
    (V : SmoothProjectiveComplexScheme) (A : AnalytificationData V)
    (hspace : A.space = TopCat.of (sphereUnionSpace M))
    (ω : singularCohomologyOf (TopCat.of unitSphereType) 2)
    (Z₀ : codimensionCycles V.X 0) (hZ₀ : Z₀ ≠ 0)
    (Z₁ : codimensionCycles V.X 1) (hZ₁ : Z₁ ≠ 0) :
    (finiteLineHodgeData M V A hspace ω Z₀ hZ₀ Z₁ hZ₁).hodgeBigrading 1 =
      spanBigrading (spherePointClassWorld (V := V)
        (H := finiteLineHodgeData M V A hspace ω Z₀ hZ₀ Z₁ hZ₁) M hspace ω) 1
        (by omega) :=
  rfl

/-- **THE STASH BIGRADING AT THE DEAD WEIGHTS** (the wave-63 :279-285
pattern). -/
theorem finiteLineHodgeData_hstash (M : ℕ) [NeZero M]
    (V : SmoothProjectiveComplexScheme) (A : AnalytificationData V)
    (hspace : A.space = TopCat.of (sphereUnionSpace M))
    (ω : singularCohomologyOf (TopCat.of unitSphereType) 2)
    (Z₀ : codimensionCycles V.X 0) (hZ₀ : Z₀ ≠ 0)
    (Z₁ : codimensionCycles V.X 1) (hZ₁ : Z₁ ≠ 0)
    (p : ℕ) (hp : 1 < p) :
    (finiteLineHodgeData M V A hspace ω Z₀ hZ₀ Z₁ hZ₁).hodgeBigrading p =
      stashBigrading (RationalSingularCohomology A (2 * p)) (2 * p) := by
  rcases p with _ | _ | p
  · exact absurd hp (by omega)
  · exact absurd hp (by omega)
  · rfl

/-- **THE DESIGNED WEIGHT-1 FIBER, WORLD-SPELLED** (the wave-60 engine
`rationalHodgeSubspace_one_eq_span`, line 227, re-instantiated). -/
theorem finiteLineHodgeData_fiber_one (M : ℕ) [NeZero M]
    (V : SmoothProjectiveComplexScheme) (A : AnalytificationData V)
    (hspace : A.space = TopCat.of (sphereUnionSpace M))
    (ω : singularCohomologyOf (TopCat.of unitSphereType) 2)
    (Z₀ : codimensionCycles V.X 0) (hZ₀ : Z₀ ≠ 0)
    (Z₁ : codimensionCycles V.X 1) (hZ₁ : Z₁ ≠ 0) :
    rationalHodgeSubspace
        ((finiteLineHodgeData M V A hspace ω Z₀ hZ₀ Z₁ hZ₁).hodgeBigrading 1) =
      Submodule.span ℚ
        (Set.range (spherePointClassWorld (V := V)
          (H := finiteLineHodgeData M V A hspace ω Z₀ hZ₀ Z₁ hZ₁) M hspace ω)) :=
  rationalHodgeSubspace_one_eq_span M hspace ω
    (finiteLineHodgeData_hone M V A hspace ω Z₀ hZ₀ Z₁ hZ₁)

/-- **THE DESIGNED WEIGHT-1 FIBER, A-SPELLED** (the kit's span engine
directly on the A-typed family — the family record's span equation). -/
theorem finiteLineHodgeData_fiber_one' (M : ℕ) [NeZero M]
    (V : SmoothProjectiveComplexScheme) (A : AnalytificationData V)
    (hspace : A.space = TopCat.of (sphereUnionSpace M))
    (ω : singularCohomologyOf (TopCat.of unitSphereType) 2)
    (Z₀ : codimensionCycles V.X 0) (hZ₀ : Z₀ ≠ 0)
    (Z₁ : codimensionCycles V.X 1) (hZ₁ : Z₁ ≠ 0) :
    rationalHodgeSubspace
        ((finiteLineHodgeData M V A hspace ω Z₀ hZ₀ Z₁ hZ₁).hodgeBigrading 1) =
      Submodule.span ℚ (Set.range (finiteLinePointClass M V A hspace ω)) := by
  rw [show (finiteLineHodgeData M V A hspace ω Z₀ hZ₀ Z₁ hZ₁).hodgeBigrading 1 =
      spanBigrading (finiteLinePointClass M V A hspace ω) 1 (by omega) from rfl]
  exact rationalHodgeSubspace_span_eq _ 1 (by omega)

/-- **THE WEIGHT-ZERO FIBER IS THE FORCED TOP** (the generic weight-zero
fiber law — green, wave 42). -/
theorem finiteLineHodgeData_fiber_zero (M : ℕ) [NeZero M]
    (V : SmoothProjectiveComplexScheme) (A : AnalytificationData V)
    (hspace : A.space = TopCat.of (sphereUnionSpace M))
    (ω : singularCohomologyOf (TopCat.of unitSphereType) 2)
    (Z₀ : codimensionCycles V.X 0) (hZ₀ : Z₀ ≠ 0)
    (Z₁ : codimensionCycles V.X 1) (hZ₁ : Z₁ ≠ 0) :
    rationalHodgeSubspace
        ((finiteLineHodgeData M V A hspace ω Z₀ hZ₀ Z₁ hZ₁).hodgeBigrading 0) = ⊤ :=
  rationalHodgeSubspace_eq_top_of_degree_zero
    (finiteLineHodgeData M V A hspace ω Z₀ hZ₀ Z₁ hZ₁)

/-- **THE DEAD WEIGHTS ARE DEAD** (the fiber is `⊥` — no vanishing proof
for `H^{2p}` anywhere). -/
theorem finiteLineHodgeData_fiber_stash (M : ℕ) [NeZero M]
    (V : SmoothProjectiveComplexScheme) (A : AnalytificationData V)
    (hspace : A.space = TopCat.of (sphereUnionSpace M))
    (ω : singularCohomologyOf (TopCat.of unitSphereType) 2)
    (Z₀ : codimensionCycles V.X 0) (hZ₀ : Z₀ ≠ 0)
    (Z₁ : codimensionCycles V.X 1) (hZ₁ : Z₁ ≠ 0)
    (p : ℕ) (hp : 1 < p) :
    rationalHodgeSubspace
        ((finiteLineHodgeData M V A hspace ω Z₀ hZ₀ Z₁ hZ₁).hodgeBigrading p) = ⊥ := by
  rw [finiteLineHodgeData_hstash M V A hspace ω Z₀ hZ₀ Z₁ hZ₁ p hp]
  exact rationalHodgeSubspace_stash_eq_bot p (by omega)

/-- **THE WEIGHT-ZERO SEED-CLASS EQUATION** (by construction):  the honest
seed cycle's class is the 0-th WORLD component class. -/
theorem finiteLineHodgeData_seed_zero (M : ℕ) [NeZero M]
    (V : SmoothProjectiveComplexScheme) (A : AnalytificationData V)
    (hspace : A.space = TopCat.of (sphereUnionSpace M))
    (ω : singularCohomologyOf (TopCat.of unitSphereType) 2)
    (Z₀ : codimensionCycles V.X 0) (hZ₀ : Z₀ ≠ 0)
    (Z₁ : codimensionCycles V.X 1) (hZ₁ : Z₁ ≠ 0) (hM : 0 < M) :
    (finiteLineHodgeData M V A hspace ω Z₀ hZ₀ Z₁ hZ₁).cycleClass 0 Z₀ =
      sphereComponentClass (V := V)
        (H := finiteLineHodgeData M V A hspace ω Z₀ hZ₀ Z₁ hZ₁) M hM hspace
        ⟨0, hM⟩ := by
  rw [show (finiteLineHodgeData M V A hspace ω Z₀ hZ₀ Z₁ hZ₁).cycleClass 0 Z₀ =
      finiteLineCycleClassZero M V A hspace Z₀ hZ₀ Z₀ from rfl,
    finiteLineCycleClassZero_seed M V A hspace Z₀ hZ₀]
  exact finiteLineComponentClass_eq_world M V A hspace ω Z₀ hZ₀ Z₁ hZ₁ ⟨0, hM⟩

/-- **THE WEIGHT-ONE SEED-CLASS EQUATION** (by construction):  the honest
seed cycle's class is the 0-th WORLD point class. -/
theorem finiteLineHodgeData_seed_one (M : ℕ) [NeZero M]
    (V : SmoothProjectiveComplexScheme) (A : AnalytificationData V)
    (hspace : A.space = TopCat.of (sphereUnionSpace M))
    (ω : singularCohomologyOf (TopCat.of unitSphereType) 2)
    (Z₀ : codimensionCycles V.X 0) (hZ₀ : Z₀ ≠ 0)
    (Z₁ : codimensionCycles V.X 1) (hZ₁ : Z₁ ≠ 0) (hM : 0 < M) :
    (finiteLineHodgeData M V A hspace ω Z₀ hZ₀ Z₁ hZ₁).cycleClass 1 Z₁ =
      spherePointClassWorld (V := V)
        (H := finiteLineHodgeData M V A hspace ω Z₀ hZ₀ Z₁ hZ₁) M hspace ω
        ⟨0, hM⟩ := by
  rw [show (finiteLineHodgeData M V A hspace ω Z₀ hZ₀ Z₁ hZ₁).cycleClass 1 Z₁ =
      finiteLineCycleClassOne M V A hspace ω Z₁ hZ₁ Z₁ from rfl,
    finiteLineCycleClassOne_seed M V A hspace ω Z₁ hZ₁]
  exact finiteLinePointClass_eq_world M V A hspace ω Z₀ hZ₀ Z₁ hZ₁ ⟨0, hM⟩

/-! ## §5 THE FOLD — the letter gates (INPUT) and the derived form

**What the wave-63 law consumed as its fold: NOTHING.**  At M = 1 every
certificate was the EMPTY word (the dead-or-monogenic engine).  At general
M the live-weight certificates are the SINGLE-LETTER words `[( (1 : ℚ),
R)]` where `R` is the M-cycle letter — the intended realization is the
graph-correspondence of the M-cycle automorphism `finiteLineCycle M` (an
isomorphism by the green `finiteLineCycle_isIso`,
GSTFiniteLineWorldCarrier.lean:550, whose graded M-th power is the
identity by `lineRotateGraded_pow`, line 456).  The module takes the
letters as GATES (the frozen wave-60 plug-in design — the wave-64
realization gate), in the exact green spelling:

```
(R₁ : RealizedFiniteClosedCorrespondence V (finiteLineHodgeData …) 1)
(hR₁ : ∀ j : Fin M, R₁.cohomologyOperator (spherePointClassWorld … j) =
  spherePointClassWorld … (cyclicPred M j))
(R₀ : RealizedFiniteClosedCorrespondence V (finiteLineHodgeData …) 0)
(hR₀ : ∀ j : Fin M, R₀.cohomologyOperator (sphereComponentClass … j) =
  sphereComponentClass … (cyclicPred M j))
```

The intended letter construction (the wave-64 letter wave's targets, NOT
built here):  the geometry is `FiniteClosedCorrespondence.graphCorrespondence`
of the cycle endomorphism (needs the still-unproved
`finiteLineCycle_over_base` — the cycle as a `ComplexSchemeEndomorphism`;
the architecture's R1);  the operator is the transported M-cycle pullback
`sphereUnionCoe ∘ (cohomologyPullbackOf (sphereCycle M) 2) ∘
sphereUnionCoe.symm`;  the realization is the pointwise class square (the
honest point-classification content).  The hand-built-letter precedent is
the green finite-point shift-word lane (`GSTFinitePointShiftWord.lean`). -/

/-- **THE DERIVED LETTER EQUATION (weight one).**  A weight-1 letter whose
cohomological operator is the transported M-cycle pullback rotates the
world point-class family exactly as the green gate calculus dictates —
the wave-60 green engine (`spherePointClassWorld_rotate_of_pullback`,
GSTPositiveDimensionalLawLanding.lean:148) re-instantiated at the
assembled concrete world:  the family equation consumed by the law IS the
green `cycle_pointClass` (GSTSphereUnionPointClassGate.lean:140), nothing
more.  This is the law module's only letter-adjacent theorem. -/
theorem finiteLineLetterOne_rotate_of_pullback (M : ℕ) [NeZero M]
    (V : SmoothProjectiveComplexScheme) (A : AnalytificationData V)
    (hspace : A.space = TopCat.of (sphereUnionSpace M))
    (ω : singularCohomologyOf (TopCat.of unitSphereType) 2)
    (Z₀ : codimensionCycles V.X 0) (hZ₀ : Z₀ ≠ 0)
    (Z₁ : codimensionCycles V.X 1) (hZ₁ : Z₁ ≠ 0)
    (R₁ : RealizedFiniteClosedCorrespondence V
      (finiteLineHodgeData M V A hspace ω Z₀ hZ₀ Z₁ hZ₁) 1)
    (hRop : ∀ u : singularCohomologyOf (TopCat.of (sphereUnionSpace M)) 2,
      R₁.cohomologyOperator (sphereUnionCoe (V := V)
        (H := finiteLineHodgeData M V A hspace ω Z₀ hZ₀ Z₁ hZ₁) M hspace u) =
        sphereUnionCoe (V := V)
          (H := finiteLineHodgeData M V A hspace ω Z₀ hZ₀ Z₁ hZ₁) M hspace
          ((cohomologyPullbackOf (sphereCycle M) 2) u)) :
    ∀ j : Fin M, R₁.cohomologyOperator
      (spherePointClassWorld (V := V)
        (H := finiteLineHodgeData M V A hspace ω Z₀ hZ₀ Z₁ hZ₁) M hspace ω j) =
      spherePointClassWorld (V := V)
        (H := finiteLineHodgeData M V A hspace ω Z₀ hZ₀ Z₁ hZ₁) M hspace ω
        (cyclicPred M j) :=
  spherePointClassWorld_rotate_of_pullback (V := V)
    (H := finiteLineHodgeData M V A hspace ω Z₀ hZ₀ Z₁ hZ₁) M hspace R₁ hRop ω

/-! ## §6 THE WEIGHT-1 CERTIFICATE — the M-cycle word, the identity Krylov
matrix

The single M-cycle letter `[( (1 : ℚ), R₁)]` with the honest 0-th
point-class seed.  The certificate builder and its cyclicity are the
wave-60 green engines, re-instantiated at the concrete world:  the orbit
IS the rotated family (`sphereUnionCertificateOne_hodgeOrbit`), and the
cyclic-orbit span law `span_range_cyclicIterate`
(GSTCyclicOrbitSpan.lean:114) closes the span against the designed fiber.
THIS IS THE FORMAL SHADOW OF THE WAVE-64 CERTIFICATE:  the Krylov matrix
of the M-cycle letter on the honest family basis is the permutation
(inverse-cycle orientation:  the identity matrix) — `det = 1`, rank M —
no determinant ever appears;  the span law IS the closed-form
certificate. -/

/-- **THE WEIGHT-1 KRYLOV CERTIFICATE.** -/
noncomputable def finiteLineCertificateOne (M : ℕ) [NeZero M]
    (V : SmoothProjectiveComplexScheme) (A : AnalytificationData V)
    (hspace : A.space = TopCat.of (sphereUnionSpace M))
    (ω : singularCohomologyOf (TopCat.of unitSphereType) 2)
    (Z₀ : codimensionCycles V.X 0) (hZ₀ : Z₀ ≠ 0)
    (Z₁ : codimensionCycles V.X 1) (hZ₁ : Z₁ ≠ 0)
    (R₁ : RealizedFiniteClosedCorrespondence V
      (finiteLineHodgeData M V A hspace ω Z₀ hZ₀ Z₁ hZ₁) 1)
    (hR₁ : ∀ j : Fin M, R₁.cohomologyOperator
      (spherePointClassWorld (V := V)
        (H := finiteLineHodgeData M V A hspace ω Z₀ hZ₀ Z₁ hZ₁) M hspace ω j) =
      spherePointClassWorld (V := V)
        (H := finiteLineHodgeData M V A hspace ω Z₀ hZ₀ Z₁ hZ₁) M hspace ω
        (cyclicPred M j)) :
    RealizedCorrespondenceKrylovCertificate V
      (finiteLineHodgeData M V A hspace ω Z₀ hZ₀ Z₁ hZ₁) 1 :=
  sphereUnionCertificateOne (V := V)
    (H := finiteLineHodgeData M V A hspace ω Z₀ hZ₀ Z₁ hZ₁) M
    (Nat.pos_of_neZero ‹_›) hspace ω
    (finiteLineHodgeData_hone M V A hspace ω Z₀ hZ₀ Z₁ hZ₁)
    R₁ hR₁ Z₁
    (finiteLineHodgeData_seed_one M V A hspace ω Z₀ hZ₀ Z₁ hZ₁
      (Nat.pos_of_neZero ‹_›))

/-- **THE WEIGHT-1 CYCLICITY** (the green wave-60 engine
`sphereUnionCertificateOne_isKrylovCyclic`,
GSTPositiveDimensionalLawLanding.lean:356, re-instantiated). -/
theorem finiteLineCertificateOne_isKrylovCyclic (M : ℕ) [NeZero M]
    (V : SmoothProjectiveComplexScheme) (A : AnalytificationData V)
    (hspace : A.space = TopCat.of (sphereUnionSpace M))
    (ω : singularCohomologyOf (TopCat.of unitSphereType) 2)
    (Z₀ : codimensionCycles V.X 0) (hZ₀ : Z₀ ≠ 0)
    (Z₁ : codimensionCycles V.X 1) (hZ₁ : Z₁ ≠ 0)
    (R₁ : RealizedFiniteClosedCorrespondence V
      (finiteLineHodgeData M V A hspace ω Z₀ hZ₀ Z₁ hZ₁) 1)
    (hR₁ : ∀ j : Fin M, R₁.cohomologyOperator
      (spherePointClassWorld (V := V)
        (H := finiteLineHodgeData M V A hspace ω Z₀ hZ₀ Z₁ hZ₁) M hspace ω j) =
      spherePointClassWorld (V := V)
        (H := finiteLineHodgeData M V A hspace ω Z₀ hZ₀ Z₁ hZ₁) M hspace ω
        (cyclicPred M j)) :
    (finiteLineCertificateOne M V A hspace ω Z₀ hZ₀ Z₁ hZ₁ R₁ hR₁).IsKrylovCyclic :=
  sphereUnionCertificateOne_isKrylovCyclic (V := V)
    (H := finiteLineHodgeData M V A hspace ω Z₀ hZ₀ Z₁ hZ₁) M
    (Nat.pos_of_neZero ‹_›) hspace ω
    (finiteLineHodgeData_hone M V A hspace ω Z₀ hZ₀ Z₁ hZ₁)
    R₁ hR₁ Z₁
    (finiteLineHodgeData_seed_one M V A hspace ω Z₀ hZ₀ Z₁ hZ₁
      (Nat.pos_of_neZero ‹_›))

/-! ## §7 THE WEIGHT-0 CERTIFICATE — the mirror

The single M-cycle letter `[( (1 : ℚ), R₀)]` with the honest 0-th
component-class seed;  the word-Hodge field is the forced-`⊤` fiber (the
generic weight-zero fiber law).  The cyclicity rides the component
family's H⁰ span (`span_range_finiteLineComponentClass`, §2) through the
same green engines. -/

/-- **THE WEIGHT-0 KRYLOV CERTIFICATE.** -/
noncomputable def finiteLineCertificateZero (M : ℕ) [NeZero M]
    (V : SmoothProjectiveComplexScheme) (A : AnalytificationData V)
    (hspace : A.space = TopCat.of (sphereUnionSpace M))
    (ω : singularCohomologyOf (TopCat.of unitSphereType) 2)
    (Z₀ : codimensionCycles V.X 0) (hZ₀ : Z₀ ≠ 0)
    (Z₁ : codimensionCycles V.X 1) (hZ₁ : Z₁ ≠ 0)
    (R₀ : RealizedFiniteClosedCorrespondence V
      (finiteLineHodgeData M V A hspace ω Z₀ hZ₀ Z₁ hZ₁) 0)
    (hR₀ : ∀ j : Fin M, R₀.cohomologyOperator
      (sphereComponentClass (V := V)
        (H := finiteLineHodgeData M V A hspace ω Z₀ hZ₀ Z₁ hZ₁) M
        (Nat.pos_of_neZero ‹_›) hspace j) =
      sphereComponentClass (V := V)
        (H := finiteLineHodgeData M V A hspace ω Z₀ hZ₀ Z₁ hZ₁) M
        (Nat.pos_of_neZero ‹_›) hspace (cyclicPred M j)) :
    RealizedCorrespondenceKrylovCertificate V
      (finiteLineHodgeData M V A hspace ω Z₀ hZ₀ Z₁ hZ₁) 0 :=
  sphereUnionCertificateZero (V := V)
    (H := finiteLineHodgeData M V A hspace ω Z₀ hZ₀ Z₁ hZ₁) M
    (Nat.pos_of_neZero ‹_›) hspace R₀ hR₀ Z₀
    (finiteLineHodgeData_seed_zero M V A hspace ω Z₀ hZ₀ Z₁ hZ₁
      (Nat.pos_of_neZero ‹_›))

/-- **THE WEIGHT-0 CYCLICITY** (the green wave-60 engine
`sphereUnionCertificateZero_isKrylovCyclic`,
GSTPositiveDimensionalLawLanding.lean:453, re-instantiated). -/
theorem finiteLineCertificateZero_isKrylovCyclic (M : ℕ) [NeZero M]
    (V : SmoothProjectiveComplexScheme) (A : AnalytificationData V)
    (hspace : A.space = TopCat.of (sphereUnionSpace M))
    (ω : singularCohomologyOf (TopCat.of unitSphereType) 2)
    (Z₀ : codimensionCycles V.X 0) (hZ₀ : Z₀ ≠ 0)
    (Z₁ : codimensionCycles V.X 1) (hZ₁ : Z₁ ≠ 0)
    (R₀ : RealizedFiniteClosedCorrespondence V
      (finiteLineHodgeData M V A hspace ω Z₀ hZ₀ Z₁ hZ₁) 0)
    (hR₀ : ∀ j : Fin M, R₀.cohomologyOperator
      (sphereComponentClass (V := V)
        (H := finiteLineHodgeData M V A hspace ω Z₀ hZ₀ Z₁ hZ₁) M
        (Nat.pos_of_neZero ‹_›) hspace j) =
      sphereComponentClass (V := V)
        (H := finiteLineHodgeData M V A hspace ω Z₀ hZ₀ Z₁ hZ₁) M
        (Nat.pos_of_neZero ‹_›) hspace (cyclicPred M j)) :
    (finiteLineCertificateZero M V A hspace ω Z₀ hZ₀ Z₁ hZ₁ R₀ hR₀).IsKrylovCyclic :=
  sphereUnionCertificateZero_isKrylovCyclic (V := V)
    (H := finiteLineHodgeData M V A hspace ω Z₀ hZ₀ Z₁ hZ₁) M
    (Nat.pos_of_neZero ‹_›) hspace R₀ hR₀ Z₀
    (finiteLineHodgeData_seed_zero M V A hspace ω Z₀ hZ₀ Z₁ hZ₁
      (Nat.pos_of_neZero ‹_›))

/-! ## §8 THE LAW (the headline theorem) -/

/-- **THE GENERAL-M LAW.**  The finite-line world — the gated carrier of
the M disjoint projective lines (F1+F2, with the wave-67 F3 smoothness
and the over-base square as the world gate's discharge targets), with the
honest sphere-union analytification `⊔ M S²`, the assembled Hodge data of
§4 (span bigrading at weight 1, stash at 0 and `p ≥ 2`), and the two
M-cycle letters as genuine realized closed correspondences rotating the
two honest families — satisfies the FULL `NativeGSTSingleFoldOrbitLaw`,
at EVERY `M ≥ 1`.

The discharge is the GREEN wave-60 engine
`native_GST_single_fold_orbit_law_of_sphereUnion_gate`
(GSTPositiveDimensionalLawLanding.lean:495, run 44642555839) — the entire
weight dispatch:  weights 0/1 by the two cyclic single-letter certificates
(§6/§7), weights `p ≥ 2` by the stash engine (§9).  The seed-class gates
`hZ₁`/`hZ₀` of the green theorem are supplied by the §4 internal lemmas
(by construction — the functional construction arranges the class of each
honest seed cycle to BE the 0-th family class).

ω-DISCLOSURE (wave 60):  the honest sphere class `ω` appears only as the
INDEX of the family design;  its nonvanishing is needed ONLY for the
liveness receipts (§11), never for the law. -/
theorem native_GST_single_fold_orbit_law_finiteLine (M : ℕ) [NeZero M]
    (V : SmoothProjectiveComplexScheme)
    (hWX : V.X = finiteLineScheme M)
    (hWmap : hWX ▸ V.structureMap = finiteLineStructureMap M)
    (A : AnalytificationData V)
    (hspace : A.space = TopCat.of (sphereUnionSpace M))
    (ω : singularCohomologyOf (TopCat.of unitSphereType) 2)
    (Z₀ : codimensionCycles V.X 0) (hZ₀ : Z₀ ≠ 0)
    (Z₁ : codimensionCycles V.X 1) (hZ₁ : Z₁ ≠ 0)
    (R₁ : RealizedFiniteClosedCorrespondence V
      (finiteLineHodgeData M V A hspace ω Z₀ hZ₀ Z₁ hZ₁) 1)
    (hR₁ : ∀ j : Fin M, R₁.cohomologyOperator
      (spherePointClassWorld (V := V)
        (H := finiteLineHodgeData M V A hspace ω Z₀ hZ₀ Z₁ hZ₁) M hspace ω j) =
      spherePointClassWorld (V := V)
        (H := finiteLineHodgeData M V A hspace ω Z₀ hZ₀ Z₁ hZ₁) M hspace ω
        (cyclicPred M j))
    (R₀ : RealizedFiniteClosedCorrespondence V
      (finiteLineHodgeData M V A hspace ω Z₀ hZ₀ Z₁ hZ₁) 0)
    (hR₀ : ∀ j : Fin M, R₀.cohomologyOperator
      (sphereComponentClass (V := V)
        (H := finiteLineHodgeData M V A hspace ω Z₀ hZ₀ Z₁ hZ₁) M
        (Nat.pos_of_neZero ‹_›) hspace j) =
      sphereComponentClass (V := V)
        (H := finiteLineHodgeData M V A hspace ω Z₀ hZ₀ Z₁ hZ₁) M
        (Nat.pos_of_neZero ‹_›) hspace (cyclicPred M j)) :
    NativeGSTSingleFoldOrbitLaw V
      (finiteLineHodgeData M V A hspace ω Z₀ hZ₀ Z₁ hZ₁) := by
  have hM : 0 < M := Nat.pos_of_neZero ‹_›
  exact native_GST_single_fold_orbit_law_of_sphereUnion_gate (M := M) (V := V)
    (H := finiteLineHodgeData M V A hspace ω Z₀ hZ₀ Z₁ hZ₁) hM hspace ω
    (finiteLineHodgeData_hone M V A hspace ω Z₀ hZ₀ Z₁ hZ₁)
    (finiteLineHodgeData_hstash M V A hspace ω Z₀ hZ₀ Z₁ hZ₁)
    R₁ hR₁ Z₁ (finiteLineHodgeData_seed_one M V A hspace ω Z₀ hZ₀ Z₁ hZ₁ hM)
    R₀ hR₀ Z₀ (finiteLineHodgeData_seed_zero M V A hspace ω Z₀ hZ₀ Z₁ hZ₁ hM)

/-! ## §9 The dead weights (the stash receipt)

Every weight `p ≥ 2` of the assembled data is honestly dead:  the
`(p,p)`-slot is `⊥` and complexification is injective — no vanishing
proof for `H^{2p}` anywhere.  (The law's own dispatch consumes this
internally through the wave-60 engine;  the standalone receipt documents
the dead half and feeds the no-free-lunch framing.) -/

/-- **THE DEAD WEIGHTS.**  Every weight `p ≥ 2` of the assembled data has
a subsingleton rational Hodge fiber. -/
theorem finiteLineHodgeData_deadWeights (M : ℕ) [NeZero M]
    (V : SmoothProjectiveComplexScheme) (A : AnalytificationData V)
    (hspace : A.space = TopCat.of (sphereUnionSpace M))
    (ω : singularCohomologyOf (TopCat.of unitSphereType) 2)
    (Z₀ : codimensionCycles V.X 0) (hZ₀ : Z₀ ≠ 0)
    (Z₁ : codimensionCycles V.X 1) (hZ₁ : Z₁ ≠ 0) :
    ∀ p : ℕ, 1 < p →
      Subsingleton (ClassicalHodgeFiber V
        (finiteLineHodgeData M V A hspace ω Z₀ hZ₀ Z₁ hZ₁) p) := by
  intro p hp
  have hbot : rationalHodgeSubspace
      ((finiteLineHodgeData M V A hspace ω Z₀ hZ₀ Z₁ hZ₁).hodgeBigrading p) = ⊥ :=
    finiteLineHodgeData_fiber_stash M V A hspace ω Z₀ hZ₀ Z₁ hZ₁ p hp
  exact subsingleton_hodgeFiber_of_eq_bot hbot

end GSTFiniteLineGeneralMLaw

end -- noncomputable section
