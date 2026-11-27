/-
Copyright (c) 2026. The HC-Proof owner's GST hypothesis program.
-/
import HCUniverse2.GSTHodgeSingleHypothesisConditional
import HCUniverse2.GSTHypothesisSpanningCompilerFace

/-!
# THE NATIVE GST SINGLE-FOLD ORBIT LAW — COST CLASSIFICATION AND FIRST DISCHARGE

The main target of the GST hypothesis program is
`GSTHodgeSingleHypothesisConditional.NativeGSTSingleFoldOrbitLaw`:

```
∀ p : Nat, ∃ C : RealizedCorrespondenceKrylovCertificate V H p, C.IsKrylovCyclic
```

— ONE genuinely realized native/cohomological correspondence word and ONE genuine
algebraic native seed at every Hodge weight, with a cyclic orbit.  Until now this
law appeared in the repository only as a hypothesis: it was assumed in
`exactHodge_of_one_GST_fold_orbit`, never discharged for any `(V, H)`.

This module classifies the cost of every Hodge weight and discharges the law
**unconditionally for the entire cheap class**, while proving the law is never
vacuous at a live weight:

* **DEAD WEIGHTS** (`Subsingleton (ClassicalHodgeFiber V H p)`, in particular
  `rationalHodgeSubspace (H.hodgeBigrading p) = ⊥`): the law is FREE.  The
  empty correspondence word `[]` (a genuine `RealizedCorrespondenceWord`) with
  the zero seed cycle is a fully valid certificate, and its cyclicity is
  discharged by the subsingleton argument (`isKrylovCyclic_of_subsingleton`).

* **MONOGENIC LIVE WEIGHTS** (the fiber is generated, as a submodule, by the
  cycle class of ONE genuine algebraic cycle): the law is again FREE — the
  empty word with that cycle as the seed is cyclic
  (`isKrylovCyclic_of_monogenic`), because the Krylov orbit contains the
  generator and spans close under rational multiples.

* **LIVE WEIGHTS OF RANK ≥ 2**: the genuine geometric core, untouched here.
  The no-free-lunch theorem `exists_nonzero_algebraic_hodge_class_of_isKrylovCyclic`
  proves the law is never vacuous at a live weight: cyclicity FORCES a nonzero
  algebraic Hodge class (`cl Z ≠ 0`) at that weight — the seed itself.  So any
  discharge here carries genuine algebraicity content; this is where the
  owner's twelve-cell cyclic fold carries its content (in the typed wave
  framework; no bridge to `(V, H)` worlds is constructed here).

The two discharge theorems:

* `native_GST_single_fold_orbit_law_of_subsingleton_weights` — the law for
  every world all of whose Hodge fibers are subsingletons;
* `native_GST_single_fold_orbit_law_of_dead_or_monogenic_weights` — the law
  for every world whose every weight is dead or monogenic-by-algebraic-class.

Composing with the repository's conditional chain gives
`every_hodge_class_is_rational_algebraic_of_dead_or_monogenic_weights`: for
this entire class of worlds, `EveryHodgeClassIsRationalAlgebraic H` — obtained
through the single-fold orbit law.  **Full disclosure:** at monogenic weights
the class hypothesis already implies the same conclusion directly by
ℚ-linearity (`α = r • cl Z = cl (r • Z)`); the direct route is recorded as
`exists_cycle_of_mem_hodgeFiber_of_monogenic`.  The composition through the
law adds no Hodge content beyond the hypothesis — it closes the LAW's status
on this class of worlds, which was previously open (the law had never been
discharged for any `(V, H)`).

## Relationship to the twelve-cell spanning faces

The owner's twelve-cell world (`GSTHypothesisSpanningProof.lean`) proves the
cyclicity core itself — `span_range_worldOrbit_eq_top`, the exact Krylov
determinant certificate `-1149656584000 ≠ 0` — for a LIVE RANK-12 fiber in the
typed wave framework (`GSTFold`), and
`GSTHypothesisSpanningCompilerFace.lean` transports it to every certified
`IntersectionChowFrame (Fin 12) A B`.  That is the rank-≥-2 content, in a
formally different law.  This module is the native `(V, H)`-world counterpart
within the same spanning-law program: it kills every dead and monogenic weight
for genuine `HodgeBigradedBettiData` worlds, and proves (no-free-lunch) that
nothing else can be killed cheaply.  The two laws are formally distinct; the
same-day bridge round (see
`research/records/2026-11-14-gst-native-law-to-fs-hypothesis-bridge.md`)
then constructed the native-to-typed bridge in this module (Â§7 below:
`gst_FS_of_native_law` â native â typed only; no typed â native transport
exists anywhere in the repository).  No concrete `(V, H)` pair is
constructed in this module; constructing one, and realizing the twelve-cell
cyclic fold as a `RealizedCorrespondenceWord` on it, remains the open
geometric instantiation task of the program.

## Non-claims (exact scope)

* The law is NOT discharged for arbitrary `(V, H)`: live weights of rank ≥ 2
  (the Hodge-conjecture core) are untouched.
* No concrete `(V, H)` pair is constructed anywhere in this module.
* At monogenic weights the hypothesis package already implies
  `EveryHodgeClassIsRationalAlgebraic` directly by ℚ-linearity; the
  composition through the law closes the law's status, not new Hodge content.
* The results are restricted lemmas in the sense of the AGENTS.md acceptance
  test, not the Hodge solution.

No `sorry`, no new axioms, no analysis, no `native_decide`; the GitHub CI
lane `gst-native-single-fold-orbit-law-landing` owns the kernel check.
-/

set_option maxHeartbeats 100000000
set_option maxRecDepth 1000000

noncomputable section

open AlgebraicGeometry
open GSTProjectiveOverC
open GSTGeometricRealizationStage2D
open GSTGeometricRealizationStage2F
open GSTGeometricRealizationStage2G
open GSTClassicalHodgeFiberedCosmology
open GSTClassicalHodgeCycleOperatorNaturality
open GSTClassicalHodgeRealizedCorrespondenceKrylovFinale
open GSTClassicalHodgeRealizedClosedCorrespondenceAlgebra
open GSTClassicalHodgeExactClayStatement
open GSTHodgeSingleHypothesisConditional

namespace GSTNativeSingleFoldOrbitLawLanding

variable {V : SmoothProjectiveComplexScheme}
variable {H : HodgeBigradedBettiData V}
variable {p : Nat}

/-! ## §1 THE FREE CERTIFICATES -/

/-- **THE EMPTY-WORD KRYLOV CERTIFICATE.**  A genuine
`RealizedCorrespondenceKrylovCertificate` with the empty correspondence word
`[]` (a valid `RealizedCorrespondenceWord` — a `List` of weighted realized
closed correspondences) and an arbitrary genuine algebraic seed cycle whose
class is Hodge.  The word's cohomological operator is the zero operator
(`realizedWordPair [] = CycleClassOperatorPair.zero`), so the Hodge-preservation
field is the zero-membership fact. -/
noncomputable def emptyWordKrylovCertificate
    (Z : codimensionCycles V.X p)
    (hZ : H.cycleClass p Z ∈ rationalHodgeSubspace (H.hodgeBigrading p)) :
    RealizedCorrespondenceKrylovCertificate V H p where
  word := []
  word_hodge := by
    intro alpha
    have hzero :
        (realizedWordPair
            ([] : RealizedCorrespondenceWord V H p)).cohomologyOperator
            (alpha : RationalSingularCohomology H.analytification (2 * p)) =
          0 := by
      simp [realizedWordPair, CycleClassOperatorPair.zero]
    rw [hzero]
    exact Submodule.zero_mem _
  seedCycle := Z
  seed_hodge := hZ

/-- The seed of the empty-word certificate is the class of the chosen cycle,
by reflexivity: `hodgeOrbit 0` is the seed by definition. -/
theorem emptyWordKrylovCertificate_hodgeOrbit_zero
    (Z : codimensionCycles V.X p)
    (hZ : H.cycleClass p Z ∈ rationalHodgeSubspace (H.hodgeBigrading p)) :
    (emptyWordKrylovCertificate Z hZ).hodgeOrbit 0
      = ⟨H.cycleClass p Z, hZ⟩ :=
  rfl

/-- The zero-cycle class is always Hodge: the zero class lies in every rational
Hodge subspace.  Stated with explicit binders so it can be applied weight by
weight inside the discharge theorems. -/
theorem zeroCycleClass_mem_hodgeFiber
    (H : HodgeBigradedBettiData V) (p : Nat) :
    H.cycleClass p 0 ∈ rationalHodgeSubspace (H.hodgeBigrading p) := by
  rw [map_zero]
  exact Submodule.zero_mem _

/-! ## §2 DEAD WEIGHTS — THE LAW IS FREE -/

/-- A rational Hodge fiber equal to `⊥` is a subsingleton.  This is the
repository's kernel-proven pattern from
`GSTClassicalHodgeGuardedFrontierConversion`. -/
theorem subsingleton_hodgeFiber_of_eq_bot
    (hbot : rationalHodgeSubspace (H.hodgeBigrading p) = ⊥) :
    Subsingleton (ClassicalHodgeFiber V H p) := by
  constructor
  intro x y
  have hx :
      (x : RationalSingularCohomology H.analytification (2 * p)) = 0 := by
    apply (Submodule.mem_bot (R := ℚ)).mp
    rw [← hbot]
    exact x.2
  have hy :
      (y : RationalSingularCohomology H.analytification (2 * p)) = 0 := by
    apply (Submodule.mem_bot (R := ℚ)).mp
    rw [← hbot]
    exact y.2
  exact Subtype.ext (by rw [hx, hy])

/-- **CYCLICITY IS FREE AT A DEAD WEIGHT.**  If the rational Hodge fiber is a
subsingleton, then EVERY certificate is Krylov-cyclic: the top of a
subsingleton module is spanned by the zero vector. -/
theorem isKrylovCyclic_of_subsingleton
    (hsub : Subsingleton (ClassicalHodgeFiber V H p))
    (C : RealizedCorrespondenceKrylovCertificate V H p) :
    C.IsKrylovCyclic := by
  apply top_unique
  intro x _
  rw [Subsingleton.elim x 0]
  exact Submodule.zero_mem _

/-! ## §3 MONOGENIC LIVE WEIGHTS — THE LAW IS FREE -/

/-- **CYCLICITY AT A MONOGENIC WEIGHT.**  If every element of the rational
Hodge fiber is a rational multiple of the certificate's seed
`C.hodgeOrbit 0`, then the certificate is Krylov-cyclic: the orbit already
contains the generator, and spans close under rational multiples. -/
theorem isKrylovCyclic_of_monogenic
    (C : RealizedCorrespondenceKrylovCertificate V H p)
    (hgen : ∀ x : ClassicalHodgeFiber V H p,
      ∃ r : ℚ, x = r • C.hodgeOrbit 0) :
    C.IsKrylovCyclic := by
  apply top_unique
  intro x _
  obtain ⟨r, hr⟩ := hgen x
  rw [hr]
  exact Submodule.smul_mem _ _
    (Submodule.subset_span (Set.mem_range_self 0))

/-! ## §4 THE LAW AT DEAD AND MONOGENIC WEIGHTS (THE CHEAP CLASS) -/

/-- **THE NATIVE GST SINGLE-FOLD ORBIT LAW, DISCHARGED FOR ALL-SUBSINGLETON
WORLDS.**  If every rational Hodge fiber of `H` is a subsingleton (in
particular, if every `rationalHodgeSubspace (H.hodgeBigrading q) = ⊥`), then
the single-fold orbit law holds — unconditionally, with the free zero-seed
empty-word certificate at every weight. -/
theorem native_GST_single_fold_orbit_law_of_subsingleton_weights
    (hsub : ∀ q : Nat, Subsingleton (ClassicalHodgeFiber V H q)) :
    NativeGSTSingleFoldOrbitLaw V H := by
  intro q
  exact ⟨emptyWordKrylovCertificate (p := q) 0
      (zeroCycleClass_mem_hodgeFiber H q),
    isKrylovCyclic_of_subsingleton (hsub q) _⟩

/-- **THE NATIVE GST SINGLE-FOLD ORBIT LAW, DISCHARGED FOR
DEAD-OR-MONOGENIC WORLDS.**  If every weight of `H` is either dead (a
subsingleton fiber) or monogenic by the cycle class of ONE genuine algebraic
cycle, then the single-fold orbit law holds — unconditionally.  At the
monogenic weights the certificate is the empty word with the algebraic
generator as the seed, and cyclicity is the one-generator spanning fact. -/
theorem native_GST_single_fold_orbit_law_of_dead_or_monogenic_weights
    (h : ∀ q : Nat,
      Subsingleton (ClassicalHodgeFiber V H q) ∨
      ∃ Z : codimensionCycles V.X q,
        H.cycleClass q Z ∈ rationalHodgeSubspace (H.hodgeBigrading q) ∧
        ∀ x : RationalSingularCohomology H.analytification (2 * q),
          x ∈ rationalHodgeSubspace (H.hodgeBigrading q) →
          ∃ r : ℚ, x = r • H.cycleClass q Z) :
    NativeGSTSingleFoldOrbitLaw V H := by
  intro q
  rcases h q with hsub | ⟨Z, hZ, hmono⟩
  · exact ⟨emptyWordKrylovCertificate (p := q) 0
        (zeroCycleClass_mem_hodgeFiber H q),
      isKrylovCyclic_of_subsingleton hsub _⟩
  · refine ⟨emptyWordKrylovCertificate Z hZ,
      isKrylovCyclic_of_monogenic _ ?_⟩
    intro x
    obtain ⟨r, hr⟩ := hmono x.1 x.2
    refine ⟨r, ?_⟩
    rw [emptyWordKrylovCertificate_hodgeOrbit_zero]
    exact Subtype.ext hr

/-! ## §5 NO FREE LUNCH — THE LAW IS NEVER VACUOUS AT LIVE WEIGHTS -/

/-- The first orbit vector is the seed, whose underlying class is the class of
the certificate's native seed cycle (by reflexivity). -/
theorem hodgeOrbit_zero_val
    (C : RealizedCorrespondenceKrylovCertificate V H p) :
    (C.hodgeOrbit 0).1 = H.cycleClass p C.seedCycle :=
  rfl

/-- **THE SEED OF A CYCLIC CERTIFICATE AT A LIVE WEIGHT IS NONZERO.**  If the
seed were zero, then by linearity the whole Krylov orbit would be zero, the
cyclic span would be `⊥`, and the fiber would be a subsingleton —
contradicting liveness. -/
theorem hodgeOrbit_zero_ne_zero_of_isKrylovCyclic
    (C : RealizedCorrespondenceKrylovCertificate V H p)
    (hcyc : C.IsKrylovCyclic)
    (hlive : ∃ a : ClassicalHodgeFiber V H p, a ≠ 0) :
    C.hodgeOrbit 0 ≠ 0 := by
  intro h0
  have hzero : ∀ n : Nat, C.hodgeOrbit n = 0 := by
    intro n
    induction n with
    | zero => exact h0
    | succ n ih =>
        show C.hodgeOperator (C.hodgeOrbit n) = 0
        rw [ih]
        exact map_zero _
  have hspanbot : Submodule.span ℚ (Set.range C.hodgeOrbit) = ⊥ := by
    refine le_antisymm ?_ bot_le
    refine Submodule.span_le.mpr ?_
    rintro x ⟨n, rfl⟩
    rw [hzero n]
    exact (Submodule.mem_bot ℚ).mpr rfl
  obtain ⟨a, ha⟩ := hlive
  have hmem : a ∈ (⊤ : Submodule ℚ (ClassicalHodgeFiber V H p)) :=
    Submodule.mem_top
  have hcyc' : Submodule.span ℚ (Set.range C.hodgeOrbit) = ⊤ := hcyc
  rw [← hcyc', hspanbot] at hmem
  exact ha ((Submodule.mem_bot ℚ).mp hmem)

/-- **NO FREE LUNCH.**  If a certificate is Krylov-cyclic at a LIVE weight
(some rational Hodge class is nonzero), then some genuine algebraic cycle has
a nonzero Hodge cycle class at that weight — namely the certificate's own
seed cycle: cyclicity at a live weight forces the seed to be nonzero, and the
seed's class is the class of a genuine native cycle.  Consequently the law
cannot be discharged cheaply at any live weight of rank ≥ 2: cyclicity there
is genuine algebraicity content. -/
theorem exists_nonzero_algebraic_hodge_class_of_isKrylovCyclic
    (C : RealizedCorrespondenceKrylovCertificate V H p)
    (hcyc : C.IsKrylovCyclic)
    (hlive : ∃ a : ClassicalHodgeFiber V H p, a ≠ 0) :
    ∃ Z : codimensionCycles V.X p,
      H.cycleClass p Z ∈ rationalHodgeSubspace (H.hodgeBigrading p) ∧
      H.cycleClass p Z ≠ 0 := by
  have hseed := hodgeOrbit_zero_ne_zero_of_isKrylovCyclic C hcyc hlive
  refine ⟨C.seedCycle, C.seed_hodge, ?_⟩
  intro hcl0
  apply hseed
  have h1 : (C.hodgeOrbit 0).1 = 0 := by
    rw [hodgeOrbit_zero_val, hcl0]
  exact Subtype.ext h1

/-- **LAW-LEVEL NO FREE LUNCH.**  If the single-fold orbit law holds at all
and some rational Hodge class at weight `p` is nonzero, then some genuine
algebraic cycle has a nonzero Hodge class at weight `p`. -/
theorem exists_nonzero_algebraic_hodge_class_of_law
    (hlaw : NativeGSTSingleFoldOrbitLaw V H)
    (hlive : ∃ a : ClassicalHodgeFiber V H p, a ≠ 0) :
    ∃ Z : codimensionCycles V.X p,
      H.cycleClass p Z ∈ rationalHodgeSubspace (H.hodgeBigrading p) ∧
      H.cycleClass p Z ≠ 0 := by
  obtain ⟨C, hcyc⟩ := hlaw p
  exact exists_nonzero_algebraic_hodge_class_of_isKrylovCyclic C hcyc hlive

/-! ## §6 THE CONSEQUENCE CHAIN — AND THE DIRECT-ROUTE DISCLOSURE -/

/-- **THE DIRECT ROUTE AT A MONOGENIC WEIGHT (disclosure theorem).**  The
class hypothesis of a monogenic weight ALREADY implies, by pure ℚ-linearity
of the cycle-class map, that every rational Hodge class at that weight is the
class of a genuine algebraic cycle: `α = r • cl Z = cl (r • Z)`.  The
composition through the single-fold orbit law in
`every_hodge_class_is_rational_algebraic_of_dead_or_monogenic_weights` adds
no Hodge content beyond this hypothesis; what it closes is the LAW's status
on this class of worlds. -/
theorem exists_cycle_of_mem_hodgeFiber_of_monogenic
    (hmono : ∃ Z : codimensionCycles V.X p,
        H.cycleClass p Z ∈ rationalHodgeSubspace (H.hodgeBigrading p) ∧
        ∀ x : RationalSingularCohomology H.analytification (2 * p),
          x ∈ rationalHodgeSubspace (H.hodgeBigrading p) →
          ∃ r : ℚ, x = r • H.cycleClass p Z)
    (alpha : RationalSingularCohomology H.analytification (2 * p))
    (halpha : alpha ∈ rationalHodgeSubspace (H.hodgeBigrading p)) :
    ∃ Y : codimensionCycles V.X p, H.cycleClass p Y = alpha := by
  obtain ⟨Z, hZ, hgen⟩ := hmono
  obtain ⟨r, hr⟩ := hgen alpha halpha
  exact ⟨r • Z, by rw [map_smul, hr]⟩

/-- **FROM THE COST PACKAGE TO THE LAW TO EXACT HODGE.**  For every world
whose weights are all dead or monogenic-by-algebraic-class, the single-fold
orbit law holds, and therefore — through the repository's conditional chain
`exactHodge_of_one_GST_fold_orbit` — every rational Hodge class of `H` is the
cycle class of a genuine algebraic cycle.  (The direct linearity route to the
same Hodge conclusion is recorded above, as
`exists_cycle_of_mem_hodgeFiber_of_monogenic`; the composition here closes
the law's status, which was previously open.) -/
theorem every_hodge_class_is_rational_algebraic_of_dead_or_monogenic_weights
    (h : ∀ q : Nat,
      Subsingleton (ClassicalHodgeFiber V H q) ∨
      ∃ Z : codimensionCycles V.X q,
        H.cycleClass q Z ∈ rationalHodgeSubspace (H.hodgeBigrading q) ∧
        ∀ x : RationalSingularCohomology H.analytification (2 * q),
          x ∈ rationalHodgeSubspace (H.hodgeBigrading q) →
          ∃ r : ℚ, x = r • H.cycleClass q Z) :
    EveryHodgeClassIsRationalAlgebraic H :=
  exactHodge_of_one_GST_fold_orbit
    (native_GST_single_fold_orbit_law_of_dead_or_monogenic_weights h)

/-- **THE COMPLETE COST PACKAGE FOR THE NATIVE GST SINGLE-FOLD ORBIT LAW.**
For every world whose weights are all dead or monogenic by an algebraic
class: the law itself, discharged; the exact-Hodge consequence through the
repository's conditional chain; and the no-free-lunch receipt at every live
weight (the law there forces a nonzero algebraic Hodge class — it is never
vacuous). -/
theorem native_GST_single_fold_orbit_law_cost_package_of_dead_or_monogenic_weights
    (h : ∀ q : Nat,
      Subsingleton (ClassicalHodgeFiber V H q) ∨
      ∃ Z : codimensionCycles V.X q,
        H.cycleClass q Z ∈ rationalHodgeSubspace (H.hodgeBigrading q) ∧
        ∀ x : RationalSingularCohomology H.analytification (2 * q),
          x ∈ rationalHodgeSubspace (H.hodgeBigrading q) →
          ∃ r : ℚ, x = r • H.cycleClass q Z) :
    NativeGSTSingleFoldOrbitLaw V H ∧
    EveryHodgeClassIsRationalAlgebraic H ∧
    (∀ q : Nat,
      ∀ hlive : ∃ a : ClassicalHodgeFiber V H q, a ≠ 0,
        ∃ Z : codimensionCycles V.X q,
          H.cycleClass q Z ∈ rationalHodgeSubspace (H.hodgeBigrading q) ∧
          H.cycleClass q Z ≠ 0) :=
  ⟨native_GST_single_fold_orbit_law_of_dead_or_monogenic_weights h,
    every_hodge_class_is_rational_algebraic_of_dead_or_monogenic_weights h,
    fun q hlive =>
      exists_nonzero_algebraic_hodge_class_of_law
        (native_GST_single_fold_orbit_law_of_dead_or_monogenic_weights h)
        hlive⟩


/-! ## §7 THE BRIDGE TO THE SPANNING FRAMEWORK

The native single-fold orbit law implies the typed FS-law of
`GSTHypothesisComplete.lean` at every weight, with the GENUINE rational
Hodge fiber: from any cyclic certificate at weight `p` we build the typed
`GSTHypothesisData` over the native cycle module and the rational singular
cohomology, with the word's own exact operator pair as the fold and
`rationalHodgeSubspace (H.hodgeBigrading p)` as the fiber.

Direction: native ⇒ typed ONLY.  No typed ⇒ native transport is
constructed here; the twelve-cell spanning faces enter below as direct
re-citations of their own typed theorems, not as consequences of the
native law.  This is the honest content boundary of the program (see the
record `research/records/2026-11-14-gst-native-law-to-fs-hypothesis-bridge.md`). -/

section Bridge

open GSTHypothesisComplete

/-- **THE TYPED FOLD CARRIED BY A CERTIFICATE.**  The realized
correspondence word's exact operator pair, with the genuine cycle-class
map as the typed carrier: the commuting square is the pair's own
`cycleClass_cycleOperator` congruence. -/
noncomputable def certFold
    (C : RealizedCorrespondenceKrylovCertificate V H p) :
    GSTFold (codimensionCycles V.X p)
      (RationalSingularCohomology H.analytification (2 * p)) where
  cycleClass := H.cycleClass p
  native := (realizedWordPair C.word).cycleOperator
  betti := (realizedWordPair C.word).cohomologyOperator
  natural z := (realizedWordPair C.word).cycleClass_cycleOperator z

/-- **THE CERTIFICATE'S TYPED HYPOTHESIS DATA.**  The designated fiber is
the GENUINE rational Hodge subspace of the weight. -/
noncomputable def certData
    (C : RealizedCorrespondenceKrylovCertificate V H p) :
    GSTHypothesisData (codimensionCycles V.X p)
      (RationalSingularCohomology H.analytification (2 * p)) where
  fold := certFold C
  hodgeFiber := rationalHodgeSubspace (H.hodgeBigrading p)
  seed := C.seedCycle

/-- The fold orbit of the certificate's seed IS the certificate's own
native orbit. -/
theorem certFold_nativeOrbit
    (C : RealizedCorrespondenceKrylovCertificate V H p) (n : Nat) :
    nativeOrbit (certFold C) C.seedCycle n = C.nativeOrbit n := by
  induction n with
  | zero => rfl
  | succ n ih =>
      show (certFold C).native (nativeOrbit (certFold C) C.seedCycle n) =
        (realizedWordPair C.word).cycleOperator (C.nativeOrbit n)
      rw [ih]
      rfl

/-- **THE ORBIT-CLASS TRANSPORT.**  The orbit classes of the certificate
fold are exactly the underlying classes of the certificate's Hodge orbit
(the exact commuting square `nativeOrbit_cycleClass` at every step). -/
theorem certFold_orbitClass_eq_hodgeOrbit
    (C : RealizedCorrespondenceKrylovCertificate V H p) :
    orbitClassSet (certFold C) C.seedCycle =
      Set.range fun n : Nat => (C.hodgeOrbit n).1 := by
  have hf : (fun n : Nat =>
      (certFold C).cycleClass (nativeOrbit (certFold C) C.seedCycle n)) =
      (fun n : Nat => (C.hodgeOrbit n).1) := by
    funext n
    rw [certFold_nativeOrbit C n]
    exact C.nativeOrbit_cycleClass n
  unfold orbitClassSet
  rw [hf]

/-- **THE SPAN TRANSPORT AT THE GENUINE FIBER.**  The rational span of the
orbit classes is the genuine rational Hodge fiber of the weight (the
subtype-span transport `span_range_subtype_eq_top_iff`). -/
theorem span_orbitClasses_eq_hodgeFiber
    (C : RealizedCorrespondenceKrylovCertificate V H p)
    (hcyc : C.IsKrylovCyclic) :
    Submodule.span ℚ (orbitClassSet (certFold C) C.seedCycle) =
      rationalHodgeSubspace (H.hodgeBigrading p) := by
  rw [certFold_orbitClass_eq_hodgeOrbit]
  have hcyc' : Submodule.span ℚ (Set.range fun n : Nat =>
      (⟨(C.hodgeOrbit n).1, (C.hodgeOrbit n).2⟩ :
        rationalHodgeSubspace (H.hodgeBigrading p))) = ⊤ := hcyc
  exact (Submodule.span_range_subtype_eq_top_iff
    (p := rationalHodgeSubspace (H.hodgeBigrading p))
    (s := fun n : Nat => (C.hodgeOrbit n).1)
    (fun n => (C.hodgeOrbit n).2)).mp hcyc'

/-- **FROM CYCLICITY TO THE TYPED SPANNING LAW.**  If the certificate is
Krylov-cyclic, the complete GST hypothesis holds for its typed data with
the genuine rational Hodge fiber. -/
theorem gst_hypothesis_complete_of_isKrylovCyclic
    (C : RealizedCorrespondenceKrylovCertificate V H p)
    (hcyc : C.IsKrylovCyclic) :
    GSTHypothesisComplete (certData C) := by
  show rationalHodgeSubspace (H.hodgeBigrading p) ≤
    Submodule.span ℚ (orbitClassSet (certFold C) C.seedCycle)
  rw [span_orbitClasses_eq_hodgeFiber C hcyc]

/-- **THE NATIVE-TO-TYPED BRIDGE (the FS law from the native law).**
For every weight, the native single-fold orbit law produces a genuine
typed hypothesis datum with the GENUINE rational Hodge fiber whose
spanning law holds. -/
theorem gst_FS_of_native_law
    (hlaw : NativeGSTSingleFoldOrbitLaw V H) :
    ∀ p : Nat,
      ∃ D : GSTHypothesisComplete.GSTHypothesisData
          (codimensionCycles V.X p)
          (RationalSingularCohomology H.analytification (2 * p)),
        GSTHypothesisComplete.GSTHypothesisComplete D ∧
        D.hodgeFiber = rationalHodgeSubspace (H.hodgeBigrading p) := by
  intro p
  obtain ⟨C, hcyc⟩ := hlaw p
  exact ⟨certData C, gst_hypothesis_complete_of_isKrylovCyclic C hcyc, rfl⟩

/-- **THE MASTER PACKAGE.**  The law itself gives both the exact-Hodge
conclusion through the repository's conditional chain and the per-weight
typed FS-law with the genuine fiber. -/
theorem native_GST_single_fold_orbit_law_master_package
    (hlaw : NativeGSTSingleFoldOrbitLaw V H) :
    EveryHodgeClassIsRationalAlgebraic H ∧
    (∀ p : Nat,
      ∃ D : GSTHypothesisData
          (codimensionCycles V.X p)
          (RationalSingularCohomology H.analytification (2 * p)),
        GSTHypothesisComplete D ∧
        D.hodgeFiber = rationalHodgeSubspace (H.hodgeBigrading p)) :=
  ⟨exactHodge_of_one_GST_fold_orbit hlaw, gst_FS_of_native_law hlaw⟩

/-- **THE MASTER PACKAGE, INSTANTIATED ON THE CHEAP CLASS.**  For every
dead-or-monogenic world the full master package holds unconditionally. -/
theorem master_package_of_dead_or_monogenic_weights
    (h : ∀ q : Nat,
      Subsingleton (ClassicalHodgeFiber V H q) ∨
      ∃ Z : codimensionCycles V.X q,
        H.cycleClass q Z ∈ rationalHodgeSubspace (H.hodgeBigrading q) ∧
        ∀ x : RationalSingularCohomology H.analytification (2 * q),
          x ∈ rationalHodgeSubspace (H.hodgeBigrading q) →
          ∃ r : ℚ, x = r • H.cycleClass q Z) :
    NativeGSTSingleFoldOrbitLaw V H ∧
    EveryHodgeClassIsRationalAlgebraic H ∧
    (∀ p : Nat,
      ∃ D : GSTHypothesisData
          (codimensionCycles V.X p)
          (RationalSingularCohomology H.analytification (2 * p)),
        GSTHypothesisComplete D ∧
        D.hodgeFiber = rationalHodgeSubspace (H.hodgeBigrading p)) :=
  ⟨native_GST_single_fold_orbit_law_of_dead_or_monogenic_weights h,
    every_hodge_class_is_rational_algebraic_of_dead_or_monogenic_weights h,
    gst_FS_of_native_law
      (native_GST_single_fold_orbit_law_of_dead_or_monogenic_weights h)⟩

end Bridge

section FrameWire

universe u v

open GSTOriginalXDivisorCurveCyclicChowFold

variable {A : Type u} [AddCommGroup A] [Module ℚ A]
variable {B : Type v} [AddCommGroup B] [Module ℚ B]

/-- **THE TWELVE-CELL WORLD WIRES INTO THE FS FRAMEWORK.**  The owner's
twelve-cell spanning face (Face 1) as a direct re-citation: the typed
shadow's own spanning law. -/
theorem twelve_cell_world_FS_law :
    GSTHypothesisComplete.GSTHypothesisComplete GSTHypothesisSpanning.worldData :=
  GSTHypothesisSpanning.gst_hypothesis_complete_world

/-- **EVERY CERTIFIED FRAME WIRES INTO THE FS FRAMEWORK.**  The compiler
face (Face 2) as a direct re-citation, for every certified
`IntersectionChowFrame (Fin 12) A B`. -/
theorem every_frame_FS_law
    (Fr : IntersectionChowFrame (Fin 12) A B) :
    GSTHypothesisComplete.GSTHypothesisComplete
      (GSTHypothesisSpanningCompilerFace.compilerData Fr) :=
  GSTHypothesisSpanningCompilerFace.gst_hypothesis_complete_compiler Fr

end FrameWire

/-! ## Receipts -/

#check emptyWordKrylovCertificate
#check isKrylovCyclic_of_subsingleton
#check isKrylovCyclic_of_monogenic
#check native_GST_single_fold_orbit_law_of_subsingleton_weights
#check native_GST_single_fold_orbit_law_of_dead_or_monogenic_weights
#check hodgeOrbit_zero_val
#check hodgeOrbit_zero_ne_zero_of_isKrylovCyclic
#check exists_nonzero_algebraic_hodge_class_of_isKrylovCyclic
#check exists_nonzero_algebraic_hodge_class_of_law
#check exists_cycle_of_mem_hodgeFiber_of_monogenic
#check every_hodge_class_is_rational_algebraic_of_dead_or_monogenic_weights
#check native_GST_single_fold_orbit_law_cost_package_of_dead_or_monogenic_weights

#print axioms isKrylovCyclic_of_subsingleton
#print axioms isKrylovCyclic_of_monogenic
#print axioms native_GST_single_fold_orbit_law_of_subsingleton_weights
#print axioms native_GST_single_fold_orbit_law_of_dead_or_monogenic_weights
#print axioms hodgeOrbit_zero_ne_zero_of_isKrylovCyclic
#print axioms exists_nonzero_algebraic_hodge_class_of_isKrylovCyclic
#print axioms exists_nonzero_algebraic_hodge_class_of_law
#print axioms exists_cycle_of_mem_hodgeFiber_of_monogenic
#print axioms every_hodge_class_is_rational_algebraic_of_dead_or_monogenic_weights
#print axioms native_GST_single_fold_orbit_law_cost_package_of_dead_or_monogenic_weights

#check certFold
#check certData
#check certFold_nativeOrbit
#check certFold_orbitClass_eq_hodgeOrbit
#check span_orbitClasses_eq_hodgeFiber
#check gst_hypothesis_complete_of_isKrylovCyclic
#check gst_FS_of_native_law
#check native_GST_single_fold_orbit_law_master_package
#check master_package_of_dead_or_monogenic_weights
#check twelve_cell_world_FS_law
#check every_frame_FS_law
#check Submodule.span_range_subtype_eq_top_iff

#print axioms certFold_nativeOrbit
#print axioms certFold_orbitClass_eq_hodgeOrbit
#print axioms span_orbitClasses_eq_hodgeFiber
#print axioms gst_hypothesis_complete_of_isKrylovCyclic
#print axioms gst_FS_of_native_law
#print axioms native_GST_single_fold_orbit_law_master_package
#print axioms master_package_of_dead_or_monogenic_weights
#print axioms twelve_cell_world_FS_law
#print axioms every_frame_FS_law
#print axioms native_GST_single_fold_orbit_law_cost_package_of_dead_or_monogenic_weights


end GSTNativeSingleFoldOrbitLawLanding
