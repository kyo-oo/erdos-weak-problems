import GSTCompactNativeCyclePresentation
import GSTClassicalHodgePresentationLanding

/-!
# GST CLASSICAL HODGE — LIMITLESS POINT NORMAL FORM

This module is the mathematical layer above the compact/native-cycle repair.
It converts the genuine Stage-2G classical Hodge statement into one global
limitless atlas indexed by every classical rational `(p,p)` basis direction.

The construction keeps all classical multiplicities.  The base coordinate is
the GST weight `p`; the fiber coordinate is a genuine basis direction inside
the rational `(p,p)` Hodge fiber.  Each atlas atom is represented by a finite
rational combination of genuine codimension-p scheme points, and the same
atom carries the already-proved projection to the universal cosmic diagonal.
-/

set_option maxHeartbeats 10000000
set_option maxRecDepth 1000000

noncomputable section

open AlgebraicGeometry
open GSTProjectiveOverC
open GSTGeometricRealizationStage2D
open GSTGeometricRealizationStage2F
open GSTGeometricRealizationStage2G
open GSTClassicalHodgeFiberedCosmology
open GSTClassicalHodgeCycleLanding
open GSTNativeCodimensionCyclePresentation
open GSTCompactNativeCyclePresentation
open GSTClassicalHodgePresentationLanding

namespace GSTClassicalHodgePointNormalForm

universe u

open Classical in
/-- Pointwise evaluation of a realized finite codimension presentation.
The realized cycle takes at `y` exactly the finite rational combination of
the indicators of the presentation's codimension-p points. -/
theorem realizeFiniteCodimensionPresentation_apply
    (X : Scheme.{u}) [CompactSpace X] (p : Nat)
    (φ : FiniteCodimensionPresentation X p) (y : X) :
    (realizeFiniteCodimensionPresentation X p φ : AlgebraicCycle X ℚ) y
      = φ.sum (fun x q => q * (if y = x.1 then (1 : ℚ) else 0)) := by
  classical
  -- evaluation at y as a rational-linear functional on native cycles
  let ev : codimensionCycles X p →ₗ[ℚ] ℚ :=
    { toFun := fun W => (W : AlgebraicCycle X ℚ) y
      map_add' := by
        intro W₁ W₂
        show ((W₁ + W₂ : codimensionCycles X p) : AlgebraicCycle X ℚ) y
            = (W₁ : AlgebraicCycle X ℚ) y + (W₂ : AlgebraicCycle X ℚ) y
        simp [Function.locallyFinsuppWithin.coe_add, Pi.add_apply]
      map_smul' := by
        intro r W
        show ((r • W : codimensionCycles X p) : AlgebraicCycle X ℚ) y
            = (r : ℚ) * ((W : codimensionCycles X p) : AlgebraicCycle X ℚ) y
        rw [Submodule.coe_smul]
        simp [GSTGeometricRealizationStage2C.algebraicCycleRatSMul_apply,
          smul_eq_mul] }
  -- the linear image formula holds for every rational-linear functional
  have hev := linearMap_realizeFiniteCodimensionPresentation X p ev φ
  -- evaluation of a point cycle is the indicator of the point
  have hevapply : ∀ x : CodimensionPoint X p,
      ev (codimensionPointCycle X p x) = if y = x.1 then (1 : ℚ) else 0 := by
    intro x
    show (codimensionPointCycle X p x : AlgebraicCycle X ℚ) y
        = if y = x.1 then (1 : ℚ) else 0
    simp [codimensionPointCycle, Function.locallyFinsuppWithin.single_apply]
  calc (realizeFiniteCodimensionPresentation X p φ : AlgebraicCycle X ℚ) y
      = ev (realizeFiniteCodimensionPresentation X p φ) := rfl
    _ = φ.sum (fun x q => q • ev (codimensionPointCycle X p x)) := hev
    _ = φ.sum (fun x q => q * (if y = x.1 then (1 : ℚ) else 0)) := by
        simp only [hevapply, smul_eq_mul]

/-- Compact native codimension cycles are reconstructed exactly from the
finite presentation consisting of their genuine codimension-p coefficients. -/
theorem realize_presentationOfNativeCycle
    (X : Scheme.{u}) [CompactSpace X]
    (p : Nat)
    (Z : codimensionCycles X p) :
    realizeFiniteCodimensionPresentation X p
        (presentationOfNativeCycle X p Z) = Z := by
  apply Subtype.ext
  ext y
  by_cases hy : Order.coheight y = p
  · show (realizeFiniteCodimensionPresentation X p
        (presentationOfNativeCycle X p Z) : AlgebraicCycle X ℚ) y
      = (Z.1 : AlgebraicCycle X ℚ) y
    rw [realizeFiniteCodimensionPresentation_apply X p
      (presentationOfNativeCycle X p Z) y]
    simp only [Finsupp.sum, smul_eq_mul]
    refine (Finset.sum_eq_single (⟨y, hy⟩ : CodimensionPoint X p) ?_ ?_).trans ?_
    · intro b _ hb
      have hne : y ≠ b.1 := by
        intro heq
        exact hb (Subtype.ext heq.symm)
      simp [hne]
    · intro hout
      simp [Finsupp.notMem_support_iff.mp hout]
    · simp [presentationOfNativeCycle_apply]
  · have hZy : (Z.1 : AlgebraicCycle X ℚ) y = 0 := by
      by_contra hne
      have hySupport : y ∈ (Z.1 : AlgebraicCycle X ℚ).support := hne
      exact hy (Z.2 hySupport)
    show (realizeFiniteCodimensionPresentation X p
      (presentationOfNativeCycle X p Z) : AlgebraicCycle X ℚ) y
      = (Z.1 : AlgebraicCycle X ℚ) y
    rw [realizeFiniteCodimensionPresentation_apply X p
      (presentationOfNativeCycle X p Z) y, hZy]
    simp only [Finsupp.sum, smul_eq_mul]
    refine Finset.sum_eq_zero fun x _ => ?_
    have hne : y ≠ x.1 := by
      intro heq
      apply hy
      rw [heq]
      exact x.2
    simp [hne]

/-- On a bundled smooth projective complex scheme, every native Hodge-basis
cycle bridge canonically yields a finite codimension-point presentation
bridge by taking the actual coefficients of each algebraic cycle. -/
noncomputable def FiberedBasisCycleBridge.toPresentationBridge
    {V : SmoothProjectiveComplexScheme}
    {H : HodgeBigradedBettiData V}
    {p : Nat}
    (R : FiberedBasisCycleBridge V H p) :
    FiberedBasisPresentationBridge V H p := by
  letI : CompactSpace V.X := smoothProjectiveCompactSpace V
  exact {
    basisPresentation := fun i =>
      presentationOfNativeCycle V.X p (R.basisCycle i)
    basisPresentation_spec := by
      intro i
      rw [realize_presentationOfNativeCycle V.X p (R.basisCycle i)]
      exact R.basisCycle_spec i
  }

/-- Native basis-cycle witnesses and finite point-presentation witnesses are
mathematically equivalent on every smooth projective complex carrier. -/
theorem fiberedBasisCycleBridge_iff_presentationBridge
    (V : SmoothProjectiveComplexScheme)
    (H : HodgeBigradedBettiData V)
    (p : Nat) :
    Nonempty (FiberedBasisCycleBridge V H p) ↔
      Nonempty (FiberedBasisPresentationBridge V H p) := by
  constructor
  · rintro ⟨R⟩
    exact ⟨FiberedBasisCycleBridge.toPresentationBridge R⟩
  · rintro ⟨R⟩
    exact ⟨R.toBasisCycleBridge⟩

/-- Exact point-presentation normal form of the genuine Stage-2G target. -/
theorem bigradedBettiHodgeStatement_iff_finite_presentations
    (V : SmoothProjectiveComplexScheme)
    (H : HodgeBigradedBettiData V) :
    BigradedBettiHodgeStatement V H ↔
      ∀ p : Nat, Nonempty (FiberedBasisPresentationBridge V H p) := by
  rw [bigradedBettiHodgeStatement_iff_fibered_basis_cycles]
  constructor
  · intro h p
    exact (fiberedBasisCycleBridge_iff_presentationBridge V H p).mp (h p)
  · intro h p
    exact (fiberedBasisCycleBridge_iff_presentationBridge V H p).mpr (h p)

/-- Fully expanded point-class equation normal form.  No abstract cycle
existential occurs: every basis vector is exactly a finite rational sum of
cycle classes of genuine codimension-p points. -/
theorem bigradedBettiHodgeStatement_iff_point_class_equations
    (V : SmoothProjectiveComplexScheme)
    (H : HodgeBigradedBettiData V) :
    BigradedBettiHodgeStatement V H ↔
      ∀ p : Nat,
        ∃ presentation :
            ClassicalHodgeBasisIndex V H p →
              FiniteCodimensionPresentation V.X p,
          ∀ i : ClassicalHodgeBasisIndex V H p,
            (presentation i).sum (fun x q =>
                q • H.cycleClass p (codimensionPointCycle V.X p x)) =
              (classicalHodgeBasis V H p i).1 := by
  rw [bigradedBettiHodgeStatement_iff_finite_presentations V H]
  constructor
  · intro h p
    exact (fiberedBasisPresentationBridge_iff_point_class_sums V H p).mp (h p)
  · intro h p
    exact (fiberedBasisPresentationBridge_iff_point_class_sums V H p).mpr (h p)

/-- One limitless global atlas: each total Hodge address gets a finite native
point presentation in the codimension dictated by its base weight. -/
abbrev GlobalFiberedCycleAtlas
    (V : SmoothProjectiveComplexScheme)
    (H : HodgeBigradedBettiData V) :=
  ∀ s : FiberedHodgeIndex V H,
    FiniteCodimensionPresentation V.X s.1

/-- Classical cycle-class exactness of one limitless atlas. -/
def GlobalFiberedCycleAtlas.ClassExact
    {V : SmoothProjectiveComplexScheme}
    {H : HodgeBigradedBettiData V}
    (A : GlobalFiberedCycleAtlas V H) : Prop :=
  ∀ s : FiberedHodgeIndex V H,
    (A s).sum (fun x q =>
        q • H.cycleClass s.1 (codimensionPointCycle V.X s.1 x)) =
      (classicalHodgeBasis V H s.1 s.2).1

/-- Limitless GST address exactness of every atlas atom. -/
def GlobalFiberedCycleAtlas.CosmicExact
    {V : SmoothProjectiveComplexScheme}
    {H : HodgeBigradedBettiData V}
    (_A : GlobalFiberedCycleAtlas V H) : Prop :=
  ∀ s : FiberedHodgeIndex V H,
    forgetMultiplicityToGST
        (fiberedWeightCoordinates V H s.1
          (classicalHodgeBasis V H s.1 s.2)) =
      Finsupp.single
        (GSTUniversalAddressBridge.cosmicAddressEquiv (s.1, s.1)) 1

/-- The cosmic half of every global atlas is unconditional: it depends only
on the already-proved limitless fibered GST coordinate theory. -/
theorem globalFiberedCycleAtlas_cosmicExact
    (V : SmoothProjectiveComplexScheme)
    (H : HodgeBigradedBettiData V)
    (A : GlobalFiberedCycleAtlas V H) :
    A.CosmicExact := by
  intro s
  exact classical_basis_projects_to_cosmic_diagonal V H s.1 s.2

/-- **LIMITLESS GLOBAL ATLAS NORMAL FORM.**  The full classical Stage-2G
Hodge target is equivalent to the existence of one global fibered atlas whose
atoms are exact both in the actual classical cycle-class map and in the GST
cosmic address universe. -/
theorem bigradedBettiHodgeStatement_iff_limitless_global_atlas
    (V : SmoothProjectiveComplexScheme)
    (H : HodgeBigradedBettiData V) :
    BigradedBettiHodgeStatement V H ↔
      ∃ A : GlobalFiberedCycleAtlas V H,
        A.ClassExact ∧ A.CosmicExact := by
  constructor
  · intro h
    have hp :=
      (bigradedBettiHodgeStatement_iff_point_class_equations V H).mp h
    choose presentation hpresentation using hp
    let A : GlobalFiberedCycleAtlas V H :=
      fun s => presentation s.1 s.2
    refine ⟨A, ?_, globalFiberedCycleAtlas_cosmicExact V H A⟩
    intro s
    exact hpresentation s.1 s.2
  · rintro ⟨A, hclass, _hcosmic⟩
    apply (bigradedBettiHodgeStatement_iff_point_class_equations V H).mpr
    intro p
    refine ⟨fun i => A ⟨p, i⟩, ?_⟩
    intro i
    exact hclass ⟨p, i⟩

/-- The global atlas also yields the exact GST/classical algebraicity bridge
used by the capstone, now with all weights and multiplicity fibers unified in
one object. -/
theorem limitless_global_atlas_to_fibered_gst_algebraicity
    (V : SmoothProjectiveComplexScheme)
    (H : HodgeBigradedBettiData V)
    (A : GlobalFiberedCycleAtlas V H)
    (hA : A.ClassExact) :
    FiberedGSTAlgebraicityBridge V H := by
  intro p i
  let φ := A ⟨p, i⟩
  refine ⟨realizeFiniteCodimensionPresentation V.X p φ, ?_, ?_⟩
  · rw [linearMap_realizeFiniteCodimensionPresentation]
    exact hA ⟨p, i⟩
  · exact classical_basis_projects_to_cosmic_diagonal V H p i

#check realize_presentationOfNativeCycle
#check FiberedBasisCycleBridge.toPresentationBridge
#check fiberedBasisCycleBridge_iff_presentationBridge
#check bigradedBettiHodgeStatement_iff_finite_presentations
#check bigradedBettiHodgeStatement_iff_point_class_equations
#check GlobalFiberedCycleAtlas
#check GlobalFiberedCycleAtlas.ClassExact
#check GlobalFiberedCycleAtlas.CosmicExact
#check globalFiberedCycleAtlas_cosmicExact
#check bigradedBettiHodgeStatement_iff_limitless_global_atlas
#check limitless_global_atlas_to_fibered_gst_algebraicity

#print axioms realize_presentationOfNativeCycle
#print axioms fiberedBasisCycleBridge_iff_presentationBridge
#print axioms bigradedBettiHodgeStatement_iff_finite_presentations
#print axioms bigradedBettiHodgeStatement_iff_point_class_equations
#print axioms globalFiberedCycleAtlas_cosmicExact
#print axioms bigradedBettiHodgeStatement_iff_limitless_global_atlas
#print axioms limitless_global_atlas_to_fibered_gst_algebraicity

/-- Point normal form detects arbitrary rational-linear maps out of native
cycles, including the genuine cycle-class map composed with an operator. -/
theorem nativeLinearMap_eq_zero_of_points
    (V : SmoothProjectiveComplexScheme) (p : Nat)
    {M : Type*} [AddCommGroup M] [Module ℚ M]
    (F : codimensionCycles V.X p →ₗ[ℚ] M)
    (hF : ∀ x : CodimensionPoint V.X p, F (codimensionPointCycle V.X p x) = 0) :
    F = 0 := by
  letI : CompactSpace V.X := smoothProjectiveCompactSpace V
  apply LinearMap.ext
  intro Z
  change F Z = 0
  rw [← realize_presentationOfNativeCycle V.X p Z]
  rw [GSTNativeCodimensionCyclePresentation.linearMap_realizeFiniteCodimensionPresentation]
  simp [hF]

/-- Native point cycles detect every linear operator on the projective cycle
space. This uses the exact compact point normal form, with no cycle-class
surjectivity hypothesis. -/
theorem nativeOperator_eq_zero_of_points
    (V : SmoothProjectiveComplexScheme) (p : Nat)
    (A : Module.End ℚ (codimensionCycles V.X p))
    (hA : ∀ x : CodimensionPoint V.X p, A (codimensionPointCycle V.X p x) = 0) :
    A = 0 := by
  letI : CompactSpace V.X := smoothProjectiveCompactSpace V
  apply LinearMap.ext
  intro Z
  change A Z = 0
  rw [← realize_presentationOfNativeCycle V.X p Z]
  rw [GSTNativeCodimensionCyclePresentation.linearMap_realizeFiniteCodimensionPresentation]
  simp [hA]

#print axioms nativeOperator_eq_zero_of_points

end GSTClassicalHodgePointNormalForm
