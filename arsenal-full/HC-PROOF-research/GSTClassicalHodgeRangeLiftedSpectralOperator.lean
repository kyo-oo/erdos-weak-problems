import Mathlib.Algebra.Module.Projective
import GSTClassicalHodgeConstructiveCyclicLanding

/-!
# GST CLASSICAL HODGE — RANGE-LIFTED SPECTRAL OPERATORS

The classical cyclic engine does not need a separately postulated operator on
native algebraic cycles.

For a rational linear cycle-class map `cl : Cycles → Coh`, its range is a
rational vector space and therefore a projective module.  Hence the canonical
surjection `Cycles → range(cl)` admits a rational linear section.  Every
cohomology endomorphism preserving `range(cl)` can consequently be lifted to
an endomorphism of native cycles, with an exact commuting cycle-class square.

On a smooth projective carrier the repo already identifies the native
cycle-class range with the atomic point-cycle span.  Therefore the
`atomic_stable` field of `ClassicalHodgeSpectralOperator` is precisely enough
to manufacture the native cycle operator required by
`SpectralCycleOperator`.

As a consequence, every existing `LocalCyclicRealization` upgrades
constructively to `LocalCycleSpectralRealization`: the single atomic seed is
lifted to one native seed cycle, the spectral operator is lifted through the
cycle-class range, and Lagrange functional calculus constructs the individual
native basis cycles.
-/

set_option maxHeartbeats 10000000
set_option maxRecDepth 1000000

noncomputable section

open scoped BigOperators
open AlgebraicGeometry
open GSTProjectiveOverC
open GSTGeometricRealizationStage2D
open GSTGeometricRealizationStage2F
open GSTGeometricRealizationStage2G
open GSTClassicalHodgeAtomicSpan
open GSTClassicalHodgeFiberedCosmology
open GSTClassicalHodgeCyclicSpectralGeneration
open GSTClassicalHodgeLocalCyclicCriterion
open GSTClassicalHodgeCycleOperatorNaturality
open GSTClassicalHodgeConstructiveCyclicLanding
open GSTNativeCodimensionCyclePresentation

namespace GSTClassicalHodgeRangeLiftedSpectralOperator

variable {V : SmoothProjectiveComplexScheme}
variable {H : HodgeBigradedBettiData V}
variable {p : Nat}

/-- Canonical-choice rational linear section of the cycle-class map onto its
actual range.  The existence is pure projectivity of rational vector spaces. -/
noncomputable def cycleClassRangeSection
    (V : SmoothProjectiveComplexScheme)
    (H : HodgeBigradedBettiData V)
    (p : Nat) :
    LinearMap.range (H.cycleClass p) →ₗ[ℚ] codimensionCycles V.X p :=
  Classical.choose
    ((H.cycleClass p).rangeRestrict.exists_rightInverse_of_surjective
      (H.cycleClass p).range_rangeRestrict)

/-- The chosen range section is an exact right inverse of the native
cycle-class map restricted to its range. -/
theorem cycleClassRangeSection_spec
    (V : SmoothProjectiveComplexScheme)
    (H : HodgeBigradedBettiData V)
    (p : Nat) :
    (H.cycleClass p).rangeRestrict ∘ₗ cycleClassRangeSection V H p =
      LinearMap.id := by
  exact Classical.choose_spec
    ((H.cycleClass p).rangeRestrict.exists_rightInverse_of_surjective
      (H.cycleClass p).range_rangeRestrict)

/-- Restrict a cohomology operator to the native cycle-class range once that
range is invariant. -/
noncomputable def rangeStableRestriction
    (T : RationalSingularCohomology H.analytification (2 * p) →ₗ[ℚ]
      RationalSingularCohomology H.analytification (2 * p))
    (hstable : ∀ x,
      x ∈ LinearMap.range (H.cycleClass p) →
        T x ∈ LinearMap.range (H.cycleClass p)) :
    LinearMap.range (H.cycleClass p) →ₗ[ℚ]
      LinearMap.range (H.cycleClass p) where
  toFun := fun x => ⟨T x.1, hstable x.1 x.2⟩
  map_add' := by
    intro x y
    ext
    simp
  map_smul' := by
    intro q x
    ext
    simp

/-- Lift a range-preserving cohomological operator to native algebraic cycles
through the projective section of the cycle-class range. -/
noncomputable def liftedCycleOperator
    (T : RationalSingularCohomology H.analytification (2 * p) →ₗ[ℚ]
      RationalSingularCohomology H.analytification (2 * p))
    (hstable : ∀ x,
      x ∈ LinearMap.range (H.cycleClass p) →
        T x ∈ LinearMap.range (H.cycleClass p)) :
    codimensionCycles V.X p →ₗ[ℚ] codimensionCycles V.X p :=
  (cycleClassRangeSection V H p).comp
    ((rangeStableRestriction T hstable).comp
      (H.cycleClass p).rangeRestrict)

/-- **RANGE-LIFT NATURALITY.**  The manufactured native cycle operator has
exactly the prescribed cohomological action after applying cycle class. -/
theorem cycleClass_liftedCycleOperator
    (T : RationalSingularCohomology H.analytification (2 * p) →ₗ[ℚ]
      RationalSingularCohomology H.analytification (2 * p))
    (hstable : ∀ x,
      x ∈ LinearMap.range (H.cycleClass p) →
        T x ∈ LinearMap.range (H.cycleClass p))
    (Z : codimensionCycles V.X p) :
    H.cycleClass p (liftedCycleOperator T hstable Z) =
      T (H.cycleClass p Z) := by
  let y : LinearMap.range (H.cycleClass p) :=
    rangeStableRestriction T hstable ((H.cycleClass p).rangeRestrict Z)
  have hsec := LinearMap.congr_fun
    (cycleClassRangeSection_spec V H p) y
  have hval := congrArg Subtype.val hsec
  simpa [liftedCycleOperator, y, rangeStableRestriction] using hval

/-! ## Exact native class/kernel coordinates

The range section supplies coordinates on actual native cycles, independently
of whether the Hodge fiber is contained in the range.  The second coordinate
retains the complete cycle-class kernel; it is never discarded as a label.
-/

@[simp]
theorem cycleClassRangeSection_range
    (a : LinearMap.range (H.cycleClass p)) :
    (H.cycleClass p).rangeRestrict (cycleClassRangeSection V H p a) = a :=
  LinearMap.congr_fun (cycleClassRangeSection_spec V H p) a

@[simp]
theorem cycleClassRangeSection_class
    (a : LinearMap.range (H.cycleClass p)) :
    H.cycleClass p (cycleClassRangeSection V H p a) = a.1 :=
  congrArg Subtype.val (cycleClassRangeSection_range a)

/-- Project an actual cycle onto the chosen representative of its actual
class.  This projects onto the existing range, not onto the Hodge fiber. -/
noncomputable def nativeClassProjection :
    Module.End ℚ (codimensionCycles V.X p) :=
  (cycleClassRangeSection V H p).comp (H.cycleClass p).rangeRestrict

/-- Preserve every part of a cycle that its cycle class cannot observe. -/
noncomputable def nativeKernelProjection :
    Module.End ℚ (codimensionCycles V.X p) :=
  LinearMap.id - nativeClassProjection (V := V) (H := H) (p := p)

@[simp]
theorem nativeClassProjection_class (Z : codimensionCycles V.X p) :
    H.cycleClass p (nativeClassProjection (H := H) Z) =
      H.cycleClass p Z := by
  exact cycleClassRangeSection_class ((H.cycleClass p).rangeRestrict Z)

@[simp]
theorem nativeClassProjection_section
    (a : LinearMap.range (H.cycleClass p)) :
    nativeClassProjection (H := H) (cycleClassRangeSection V H p a) =
      cycleClassRangeSection V H p a := by
  simp [nativeClassProjection]

@[simp]
theorem nativeKernelProjection_class (Z : codimensionCycles V.X p) :
    H.cycleClass p (nativeKernelProjection (H := H) Z) = 0 := by
  simp [nativeKernelProjection]

theorem nativeClassProjection_eq_zero_of_class_zero
    (Z : codimensionCycles V.X p) (hZ : H.cycleClass p Z = 0) :
    nativeClassProjection (H := H) Z = 0 := by
  have hr : (H.cycleClass p).rangeRestrict Z = 0 := Subtype.ext hZ
  simp [nativeClassProjection, hr]

theorem nativeKernelProjection_eq_self_of_class_zero
    (Z : codimensionCycles V.X p) (hZ : H.cycleClass p Z = 0) :
    nativeKernelProjection (H := H) Z = Z := by
  simp [nativeKernelProjection,
    nativeClassProjection_eq_zero_of_class_zero Z hZ]

@[simp]
theorem nativeKernelProjection_section
    (a : LinearMap.range (H.cycleClass p)) :
    nativeKernelProjection (H := H) (cycleClassRangeSection V H p a) = 0 := by
  simp [nativeKernelProjection]

theorem native_projection_decomposition (Z : codimensionCycles V.X p) :
    nativeClassProjection (H := H) Z + nativeKernelProjection (H := H) Z =
      Z := by
  simp only [nativeKernelProjection, LinearMap.sub_apply, LinearMap.id_apply]
  abel

theorem nativeClassProjection_idempotent :
    (nativeClassProjection (V := V) (H := H) (p := p)).comp
      (nativeClassProjection (H := H)) = nativeClassProjection (H := H) := by
  apply LinearMap.ext
  intro Z
  exact nativeClassProjection_section ((H.cycleClass p).rangeRestrict Z)

theorem nativeKernelProjection_idempotent :
    (nativeKernelProjection (V := V) (H := H) (p := p)).comp
      (nativeKernelProjection (H := H)) = nativeKernelProjection (H := H) := by
  apply LinearMap.ext
  intro Z
  exact nativeKernelProjection_eq_self_of_class_zero _
    (nativeKernelProjection_class Z)

theorem nativeClassProjection_comp_nativeKernelProjection :
    (nativeClassProjection (V := V) (H := H) (p := p)).comp
      (nativeKernelProjection (H := H)) = 0 := by
  apply LinearMap.ext
  intro Z
  exact nativeClassProjection_eq_zero_of_class_zero _
    (nativeKernelProjection_class Z)

theorem nativeKernelProjection_comp_nativeClassProjection :
    (nativeKernelProjection (V := V) (H := H) (p := p)).comp
      (nativeClassProjection (H := H)) = 0 := by
  apply LinearMap.ext
  intro Z
  exact nativeKernelProjection_section ((H.cycleClass p).rangeRestrict Z)

/-- The entire native kernel coordinate, as a map into the kernel itself. -/
noncomputable def nativeKernelCoordinate :
    codimensionCycles V.X p →ₗ[ℚ] LinearMap.ker (H.cycleClass p) where
  toFun Z := ⟨nativeKernelProjection (H := H) Z,
    nativeKernelProjection_class Z⟩
  map_add' := by
    intro Z W
    apply Subtype.ext
    exact map_add (nativeKernelProjection (H := H)) Z W
  map_smul' := by
    intro q Z
    apply Subtype.ext
    exact map_smul (nativeKernelProjection (H := H)) q Z

@[simp]
theorem nativeKernelCoordinate_section
    (a : LinearMap.range (H.cycleClass p)) :
    nativeKernelCoordinate (H := H) (cycleClassRangeSection V H p a) = 0 := by
  apply Subtype.ext
  exact nativeKernelProjection_section a

@[simp]
theorem nativeKernelCoordinate_kernel
    (k : LinearMap.ker (H.cycleClass p)) :
    nativeKernelCoordinate (H := H) k.1 = k := by
  apply Subtype.ext
  exact nativeKernelProjection_eq_self_of_class_zero k.1 k.2

/-- **EXACT NATIVE SPLIT.** An actual cycle is uniquely its actual class
coordinate together with its complete null-class native coordinate. -/
noncomputable def nativeClassKernelEquiv :
    codimensionCycles V.X p ≃ₗ[ℚ]
      (LinearMap.range (H.cycleClass p) × LinearMap.ker (H.cycleClass p)) where
  toLinearMap := {
    toFun := fun Z => ((H.cycleClass p).rangeRestrict Z,
      nativeKernelCoordinate (H := H) Z)
    map_add' := by intro Z W; simp
    map_smul' := by intro q Z; simp
  }
  invFun a := cycleClassRangeSection V H p a.1 + a.2.1
  left_inv := by
    intro Z
    exact native_projection_decomposition Z
  right_inv := by
    intro a
    apply Prod.ext
    · apply Subtype.ext
      change H.cycleClass p (cycleClassRangeSection V H p a.1 + a.2.1) = a.1.1
      have hk : H.cycleClass p a.2.1 = 0 := a.2.2
      simp [hk]
    · change nativeKernelCoordinate (H := H)
        (cycleClassRangeSection V H p a.1 + a.2.1) = a.2
      simp

@[simp]
theorem nativeClassKernelEquiv_apply (Z : codimensionCycles V.X p) :
    nativeClassKernelEquiv (H := H) Z =
      ((H.cycleClass p).rangeRestrict Z, nativeKernelCoordinate (H := H) Z) :=
  rfl

@[simp]
theorem nativeClassKernelEquiv_symm_apply
    (a : LinearMap.range (H.cycleClass p))
    (k : LinearMap.ker (H.cycleClass p)) :
    (nativeClassKernelEquiv (H := H)).symm (a, k) =
      cycleClassRangeSection V H p a + k.1 :=
  rfl

/-! ## Composition-coherent native lifts and all their native freedom -/

theorem rangeStableRestriction_comp
    (T U : Module.End ℚ (RationalSingularCohomology H.analytification (2 * p)))
    (hT : ∀ x ∈ LinearMap.range (H.cycleClass p),
      T x ∈ LinearMap.range (H.cycleClass p))
    (hU : ∀ x ∈ LinearMap.range (H.cycleClass p),
      U x ∈ LinearMap.range (H.cycleClass p)) :
    rangeStableRestriction (T.comp U) (fun x hx => hT _ (hU x hx)) =
      (rangeStableRestriction T hT).comp (rangeStableRestriction U hU) := by
  apply LinearMap.ext
  intro a
  apply Subtype.ext
  rfl

theorem liftedCycleOperator_comp
    (T U : Module.End ℚ (RationalSingularCohomology H.analytification (2 * p)))
    (hT : ∀ x ∈ LinearMap.range (H.cycleClass p),
      T x ∈ LinearMap.range (H.cycleClass p))
    (hU : ∀ x ∈ LinearMap.range (H.cycleClass p),
      U x ∈ LinearMap.range (H.cycleClass p)) :
    (liftedCycleOperator T hT).comp (liftedCycleOperator U hU) =
      liftedCycleOperator (T.comp U) (fun x hx => hT _ (hU x hx)) := by
  apply LinearMap.ext
  intro Z
  simp only [liftedCycleOperator, LinearMap.comp_apply,
    cycleClassRangeSection_range, rangeStableRestriction_comp]

theorem liftedCycleOperator_id :
    liftedCycleOperator (LinearMap.id :
      Module.End ℚ (RationalSingularCohomology H.analytification (2 * p)))
      (fun _ hx => hx) = nativeClassProjection (H := H) := by
  apply LinearMap.ext
  intro Z
  rfl

theorem liftedCycleOperator_kills_kernel
    (T : Module.End ℚ (RationalSingularCohomology H.analytification (2 * p)))
    (hT : ∀ x ∈ LinearMap.range (H.cycleClass p),
      T x ∈ LinearMap.range (H.cycleClass p))
    (Z : codimensionCycles V.X p) (hZ : H.cycleClass p Z = 0) :
    liftedCycleOperator T hT Z = 0 := by
  have hr : (H.cycleClass p).rangeRestrict Z = 0 := Subtype.ext hZ
  simp [liftedCycleOperator, hr]

theorem liftedCycleOperator_kernelCoordinate
    (T : Module.End ℚ (RationalSingularCohomology H.analytification (2 * p)))
    (hT : ∀ x ∈ LinearMap.range (H.cycleClass p),
      T x ∈ LinearMap.range (H.cycleClass p))
    (Z : codimensionCycles V.X p) :
    nativeKernelCoordinate (H := H) (liftedCycleOperator T hT Z) = 0 := by
  exact nativeKernelCoordinate_section
    (rangeStableRestriction T hT ((H.cycleClass p).rangeRestrict Z))

/-- Every native lift is the coherent range lift plus a unique map into the
actual native kernel.  The kernel map is native data, not a missing class. -/
theorem nativeLift_iff_kernelPerturbation
    (T : Module.End ℚ (RationalSingularCohomology H.analytification (2 * p)))
    (hT : ∀ x ∈ LinearMap.range (H.cycleClass p),
      T x ∈ LinearMap.range (H.cycleClass p))
    (A : Module.End ℚ (codimensionCycles V.X p)) :
    (∀ Z, H.cycleClass p (A Z) = T (H.cycleClass p Z)) ↔
    ∃ K : codimensionCycles V.X p →ₗ[ℚ] LinearMap.ker (H.cycleClass p),
      A = liftedCycleOperator T hT + (LinearMap.ker (H.cycleClass p)).subtype.comp K := by
  constructor
  · intro hA
    refine ⟨(nativeKernelCoordinate (H := H)).comp A, ?_⟩
    apply LinearMap.ext
    intro Z
    have hp : nativeClassProjection (H := H) (A Z) =
        liftedCycleOperator T hT Z := by
      change cycleClassRangeSection V H p _ = cycleClassRangeSection V H p _
      congr 1
      apply Subtype.ext
      exact hA Z
    have hker : (H.cycleClass p).ker.subtype (nativeKernelCoordinate (H := H) (A Z)) =
        nativeKernelProjection (H := H) (A Z) := rfl
    simp only [LinearMap.add_apply, LinearMap.comp_apply, hker]
    exact (native_projection_decomposition (A Z)).symm.trans
      (congrArg (fun W => W + nativeKernelProjection (H := H) (A Z)) hp)
  · rintro ⟨K, rfl⟩ Z
    change H.cycleClass p (liftedCycleOperator T hT Z + (K Z).1) = _
    have hk : H.cycleClass p (K Z).1 = 0 := (K Z).2
    rw [map_add, cycleClass_liftedCycleOperator, hk, add_zero]

theorem nativeLift_kernelPerturbation_unique
    (T : Module.End ℚ (RationalSingularCohomology H.analytification (2 * p)))
    (hT : ∀ x ∈ LinearMap.range (H.cycleClass p),
      T x ∈ LinearMap.range (H.cycleClass p))
    (K L : codimensionCycles V.X p →ₗ[ℚ] LinearMap.ker (H.cycleClass p))
    (h : liftedCycleOperator T hT + (LinearMap.ker (H.cycleClass p)).subtype.comp K =
      liftedCycleOperator T hT + (LinearMap.ker (H.cycleClass p)).subtype.comp L) :
    K = L := by
  apply LinearMap.ext
  intro Z
  apply Subtype.ext
  exact add_left_cancel (LinearMap.congr_fun h Z)

#print axioms nativeClassKernelEquiv
#print axioms liftedCycleOperator_comp
#print axioms nativeLift_iff_kernelPerturbation
#print axioms nativeLift_kernelPerturbation_unique

end GSTClassicalHodgeRangeLiftedSpectralOperator

open GSTClassicalHodgeRangeLiftedSpectralOperator

namespace GSTClassicalHodgeCycleOperatorNaturality
namespace CycleClassOperatorPair
/-- Any range-preserving cohomology operator therefore determines a complete
native/cohomological operator pair. -/
noncomputable def ofRangeStable
    (T : RationalSingularCohomology H.analytification (2 * p) →ₗ[ℚ]
      RationalSingularCohomology H.analytification (2 * p))
    (hstable : ∀ x,
      x ∈ LinearMap.range (H.cycleClass p) →
        T x ∈ LinearMap.range (H.cycleClass p)) :
    CycleClassOperatorPair V H p where
  cycleOperator := liftedCycleOperator T hstable
  cohomologyOperator := T
  cycleClass_natural := by
    ext Z
    exact cycleClass_liftedCycleOperator T hstable Z

end CycleClassOperatorPair
end GSTClassicalHodgeCycleOperatorNaturality

namespace GSTClassicalHodgeCyclicSpectralGeneration
namespace ClassicalHodgeSpectralOperator

/-- On a smooth projective scheme, atomic-span stability is the same range
stability needed by the range-lift theorem. -/
theorem cycleClassRange_stable
    {ι : Type*} [Fintype ι] [DecidableEq ι]
    (S : ClassicalHodgeSpectralOperator V H p ι) :
    ∀ x,
      x ∈ LinearMap.range (H.cycleClass p) →
        S.observable x ∈ LinearMap.range (H.cycleClass p) := by
  intro x hx
  have hxAtomic :
      x ∈ pointCycleClassSpan p (H.cycleClass p) := by
    rwa [← smoothProjective_cycleClass_range_eq_atomic_span V H p]
  have hTxAtomic := S.atomic_stable x hxAtomic
  rwa [← smoothProjective_cycleClass_range_eq_atomic_span V H p] at hTxAtomic

/-- **AUTOMATIC NATIVE SPECTRAL LIFT.**  Every classical Hodge spectral
operator already carries enough information to become a native spectral cycle
operator; no independent native operator datum is required. -/
noncomputable def toSpectralCycleOperatorViaRange
    {ι : Type*} [Fintype ι] [DecidableEq ι]
    (S : ClassicalHodgeSpectralOperator V H p ι) :
    SpectralCycleOperator V H p ι where
  operatorPair := CycleClassOperatorPair.ofRangeStable
    S.observable S.cycleClassRange_stable
  basisIndex := S.basisIndex
  basisIndex_injective := S.basisIndex_injective
  eigenvalue := S.eigenvalue
  eigenvalue_injective := S.eigenvalue_injective
  eigenvector := S.eigenvector

/-- The automatically lifted spectral operator preserves the original selected
basis indexing exactly. -/
@[simp]
theorem toSpectralCycleOperatorViaRange_basisIndex
    {ι : Type*} [Fintype ι] [DecidableEq ι]
    (S : ClassicalHodgeSpectralOperator V H p ι) :
    S.toSpectralCycleOperatorViaRange.basisIndex = S.basisIndex :=
  rfl

end ClassicalHodgeSpectralOperator
end GSTClassicalHodgeCyclicSpectralGeneration

namespace GSTClassicalHodgeLocalCyclicCriterion
namespace LocalCyclicRealization

/-- **LOCAL CYCLIC → CONSTRUCTIVE NATIVE UPGRADE.**

A local cyclic realization already contains every mathematical ingredient
needed for explicit native cycle construction.  Its atomic seed belongs to
the actual cycle-class range, so choose one native seed cycle representing it;
its atomic-stable spectral observable automatically lifts to native cycles by
the range-lift theorem above. -/
noncomputable def toLocalCycleSpectralRealization
    {alpha : ClassicalHodgeFiber V H p}
    (R : LocalCyclicRealization V H p alpha) :
    LocalCycleSpectralRealization V H p alpha := by
  let S := R.spectral.toSpectralCycleOperatorViaRange
  have hseedRange := R.seed_mem_atomic
  rw [← smoothProjective_cycleClass_range_eq_atomic_span V H p] at hseedRange
  rw [LinearMap.mem_range] at hseedRange
  have hZ := Classical.choose_spec hseedRange
  have hSindex : S.basisIndex = HodgeSupportIndex.include := by
    exact R.spectral_basisIndex
  refine {
    spectral := S
    spectral_basisIndex := hSindex
    seed := {
      cycle := Classical.choose hseedRange
      coefficient := fun _ => 1
      coefficient_ne_zero := by
        intro i
        norm_num
      class_eq := ?_
    }
  }
  rw [hSindex]
  exact hZ.trans (Finset.sum_congr rfl fun i _ => by
    simp only [one_smul, HodgeSupportIndex.include])

/-- Every local cyclic realization therefore constructs an explicit native
cycle for the original Hodge class. -/
theorem exists_native_cycle_constructive
    {alpha : ClassicalHodgeFiber V H p}
    (R : LocalCyclicRealization V H p alpha) :
    ∃ Z : codimensionCycles V.X p,
      H.cycleClass p Z = alpha.1 :=
  R.toLocalCycleSpectralRealization.exists_native_cycle

/-- Every local cyclic realization also constructs an explicit finite
codimension-point presentation of the original Hodge class. -/
theorem exists_point_presentation_constructive
    {alpha : ClassicalHodgeFiber V H p}
    (R : LocalCyclicRealization V H p alpha) :
    ∃ φ : FiniteCodimensionPresentation V.X p,
      φ.sum (fun x q => q • H.cycleClass p
        (codimensionPointCycle V.X p x)) = alpha.1 := by
  let RC := R.toLocalCycleSpectralRealization
  exact ⟨RC.reconstructedPresentation, RC.reconstructedPresentation_spec⟩

end LocalCyclicRealization
end GSTClassicalHodgeLocalCyclicCriterion

namespace GSTClassicalHodgeRangeLiftedSpectralOperator

/-- The previous local cyclic criterion can now be upgraded from span
membership to a fully constructive native-cycle theorem without strengthening
its hypotheses. -/
theorem constructive_hodge_of_local_cyclic_realizations
    (V : SmoothProjectiveComplexScheme)
    (H : HodgeBigradedBettiData V)
    (hlocal :
      ∀ p : Nat, ∀ alpha : ClassicalHodgeFiber V H p,
        Nonempty (LocalCyclicRealization V H p alpha)) :
    BigradedBettiHodgeStatement V H
    ∧ (∀ p : Nat, ∀ alpha : ClassicalHodgeFiber V H p,
      ∃ Z : codimensionCycles V.X p,
        H.cycleClass p Z = alpha.1)
    ∧ (∀ p : Nat, ∀ alpha : ClassicalHodgeFiber V H p,
      ∃ φ : FiniteCodimensionPresentation V.X p,
        φ.sum (fun x q => q • H.cycleClass p
          (codimensionPointCycle V.X p x)) = alpha.1) := by
  have hcycle :
      ∀ p : Nat, ∀ alpha : ClassicalHodgeFiber V H p,
        Nonempty (LocalCycleSpectralRealization V H p alpha) := by
    intro q alpha
    rcases hlocal q alpha with ⟨R⟩
    exact ⟨R.toLocalCycleSpectralRealization⟩
  exact constructive_cyclic_landing_crown V H hcycle

#check cycleClassRangeSection
#check cycleClassRangeSection_spec
#check rangeStableRestriction
#check liftedCycleOperator
#check cycleClass_liftedCycleOperator
#check CycleClassOperatorPair.ofRangeStable
#check ClassicalHodgeSpectralOperator.cycleClassRange_stable
#check ClassicalHodgeSpectralOperator.toSpectralCycleOperatorViaRange
#check LocalCyclicRealization.toLocalCycleSpectralRealization
#check LocalCyclicRealization.exists_native_cycle_constructive
#check LocalCyclicRealization.exists_point_presentation_constructive
#check constructive_hodge_of_local_cyclic_realizations

#print axioms cycleClass_liftedCycleOperator
#print axioms CycleClassOperatorPair.ofRangeStable
#print axioms ClassicalHodgeSpectralOperator.toSpectralCycleOperatorViaRange
#print axioms LocalCyclicRealization.toLocalCycleSpectralRealization
#print axioms LocalCyclicRealization.exists_native_cycle_constructive
#print axioms constructive_hodge_of_local_cyclic_realizations

end GSTClassicalHodgeRangeLiftedSpectralOperator
