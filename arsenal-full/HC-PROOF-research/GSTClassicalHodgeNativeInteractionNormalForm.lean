import GSTClassicalHodgeFiberedNativePullback

/-!
# GST native interaction normal form

The two existing marginals determine a joint state only up to an interaction.
This file constructs that interaction, proves that it is an idempotent
projection, and computes its entire image from four-atom rectangles.

All expressions are finite states in the existing GST native universe.
No target cycle, Hodge completeness, or geometric carrier existence is used.
-/

noncomputable section

open AlgebraicGeometry
open GSTProjectiveOverC
open GSTGeometricRealizationStage2G
open GSTClassicalHodgeFiberedCosmology
open GSTNativeCodimensionCyclePresentation
open GSTClassicalHodgeNativeCycleCosmicShadow
open GSTClassicalHodgeFiberedNativePullback

namespace GSTClassicalHodgeNativeInteractionNormalForm

variable {V : SmoothProjectiveComplexScheme}
variable {H : HodgeBigradedBettiData V} {p : Nat}

/-- The smallest interaction invisible to both marginals. -/
def interactionRectangle
    (i₀ i : ClassicalHodgeBasisIndex V H p)
    (x₀ x : CodimensionPoint V.X p) : FiberedNativeAddress V H p :=
  atom V H p i x - atom V H p i x₀ -
    atom V H p i₀ x + atom V H p i₀ x₀

@[simp] theorem interactionRectangle_forgetPoint
    (i₀ i : ClassicalHodgeBasisIndex V H p)
    (x₀ x : CodimensionPoint V.X p) :
    forgetPoint V H p (interactionRectangle i₀ i x₀ x) = 0 := by
  simp [interactionRectangle]

@[simp] theorem interactionRectangle_forgetMultiplicity
    (i₀ i : ClassicalHodgeBasisIndex V H p)
    (x₀ x : CodimensionPoint V.X p) :
    forgetMultiplicity V H p (interactionRectangle i₀ i x₀ x) = 0 := by
  simp [interactionRectangle]

/-- Reconstruct the marginal part using one label and one native point. -/
def marginalReconstruction
    (i₀ : ClassicalHodgeBasisIndex V H p)
    (x₀ : CodimensionPoint V.X p) :
    Module.End ℚ (FiberedNativeAddress V H p) where
  toFun Φ := glueMarginals V H p i₀ x₀
    (forgetPoint V H p Φ) (forgetMultiplicity V H p Φ)
  map_add' := by
    intro Φ Ψ
    simp only [glueMarginals, map_add, add_smul]
    abel
  map_smul' := by
    intro q Φ
    simp [glueMarginals, smul_add, smul_sub, smul_smul]

/-- The genuinely joint part of a state, after its marginals are removed. -/
def interactionProjection
    (i₀ : ClassicalHodgeBasisIndex V H p)
    (x₀ : CodimensionPoint V.X p) :
    Module.End ℚ (FiberedNativeAddress V H p) :=
  LinearMap.id - marginalReconstruction i₀ x₀

@[simp] theorem marginalReconstruction_forgetPoint
    (i₀ : ClassicalHodgeBasisIndex V H p)
    (x₀ : CodimensionPoint V.X p) (Φ : FiberedNativeAddress V H p) :
    forgetPoint V H p (marginalReconstruction i₀ x₀ Φ) =
      forgetPoint V H p Φ := by
  exact glueMarginals_forgetPoint V H p i₀ x₀ _ _
    (marginal_mass_balance V H p Φ)

@[simp] theorem marginalReconstruction_forgetMultiplicity
    (i₀ : ClassicalHodgeBasisIndex V H p)
    (x₀ : CodimensionPoint V.X p) (Φ : FiberedNativeAddress V H p) :
    forgetMultiplicity V H p (marginalReconstruction i₀ x₀ Φ) =
      forgetMultiplicity V H p Φ := by
  exact glueMarginals_forgetMultiplicity V H p i₀ x₀ _ _

@[simp] theorem interactionProjection_forgetPoint
    (i₀ : ClassicalHodgeBasisIndex V H p)
    (x₀ : CodimensionPoint V.X p) (Φ : FiberedNativeAddress V H p) :
    forgetPoint V H p (interactionProjection i₀ x₀ Φ) = 0 := by
  simp [interactionProjection]

@[simp] theorem interactionProjection_forgetMultiplicity
    (i₀ : ClassicalHodgeBasisIndex V H p)
    (x₀ : CodimensionPoint V.X p) (Φ : FiberedNativeAddress V H p) :
    forgetMultiplicity V H p (interactionProjection i₀ x₀ Φ) = 0 := by
  simp [interactionProjection]

/-- Each atom contributes precisely one four-corner interaction. -/
@[simp] theorem interactionProjection_atom
    (i₀ i : ClassicalHodgeBasisIndex V H p)
    (x₀ x : CodimensionPoint V.X p) :
    interactionProjection i₀ x₀ (atom V H p i x) =
      interactionRectangle i₀ i x₀ x := by
  simp only [interactionProjection, LinearMap.sub_apply, LinearMap.id_apply]
  show atom V H p i x -
      (attachPoint V H p x₀ (forgetPoint V H p (atom V H p i x)) +
        attachSheet V H p i₀ (forgetMultiplicity V H p (atom V H p i x)) -
        multiplicityMass V H p (forgetPoint V H p (atom V H p i x)) •
          atom V H p i₀ x₀) =
    interactionRectangle i₀ i x₀ x
  rw [forgetPoint_atom, forgetMultiplicity_atom]
  simp [multiplicityMass_single, interactionRectangle, atom,
    attachPoint, attachSheet, Finsupp.sum]
  abel

/-- **FINITE INTERACTION LAW.** Every interaction is a finite combination
of explicit four-atom rectangles, with the original state's coefficients. -/
theorem interactionProjection_finite_normal_form
    (i₀ : ClassicalHodgeBasisIndex V H p)
    (x₀ : CodimensionPoint V.X p) (Φ : FiberedNativeAddress V H p) :
    interactionProjection i₀ x₀ Φ =
      Φ.sum (fun ix q => q • interactionRectangle i₀ ix.1 x₀ ix.2) := by
  classical
  have hΦ : Φ = Φ.sum (fun ix q => q • atom V H p ix.1 ix.2) := by
    simp [atom]
  calc
    interactionProjection i₀ x₀ Φ =
        interactionProjection i₀ x₀
          (Φ.sum (fun ix q => q • atom V H p ix.1 ix.2)) := congrArg _ hΦ
    _ = _ := by
      rw [map_finsuppSum]
      simp only [map_smul, interactionProjection_atom]

/-- The joint kernel is exactly the fixed space of the interaction projection. -/
theorem interactionProjection_eq_self_iff
    (i₀ : ClassicalHodgeBasisIndex V H p)
    (x₀ : CodimensionPoint V.X p) (Φ : FiberedNativeAddress V H p) :
    interactionProjection i₀ x₀ Φ = Φ ↔
      forgetPoint V H p Φ = 0 ∧ forgetMultiplicity V H p Φ = 0 := by
  constructor
  · intro h
    constructor
    · rw [← h]; exact interactionProjection_forgetPoint i₀ x₀ Φ
    · rw [← h]; exact interactionProjection_forgetMultiplicity i₀ x₀ Φ
  · rintro ⟨ha, hb⟩
    simp [interactionProjection, marginalReconstruction, glueMarginals, ha, hb]

/-- Interaction extraction is a projection, not an iterative correction. -/
theorem interactionProjection_idempotent
    (i₀ : ClassicalHodgeBasisIndex V H p)
    (x₀ : CodimensionPoint V.X p) :
    (interactionProjection i₀ x₀).comp (interactionProjection i₀ x₀) =
      interactionProjection i₀ x₀ := by
  apply LinearMap.ext
  intro Φ
  have h := (interactionProjection_eq_self_iff i₀ x₀
    (interactionProjection i₀ x₀ Φ)).mpr
    ⟨interactionProjection_forgetPoint i₀ x₀ Φ,
      interactionProjection_forgetMultiplicity i₀ x₀ Φ⟩
  show (interactionProjection i₀ x₀) ((interactionProjection i₀ x₀) Φ) =
    (interactionProjection i₀ x₀) Φ
  exact h

/-- **EXACT JOINT-KERNEL GENERATION.** No other type of marginal-invisible
finite state is needed: four-corner interactions generate the entire kernel. -/
theorem jointKernel_eq_rectangleSpan
    (i₀ : ClassicalHodgeBasisIndex V H p)
    (x₀ : CodimensionPoint V.X p) :
    (forgetPoint V H p).ker ⊓ (forgetMultiplicity V H p).ker =
      Submodule.span ℚ (Set.range (fun ix : FiberedNativeAtom V H p =>
        interactionRectangle i₀ ix.1 x₀ ix.2)) := by
  apply le_antisymm
  · intro Φ hΦ
    have hfix := (interactionProjection_eq_self_iff i₀ x₀ Φ).mpr hΦ
    rw [← hfix, interactionProjection_finite_normal_form]
    apply Submodule.sum_mem
    intro ix _
    apply Submodule.smul_mem
    exact Submodule.subset_span (Set.mem_range_self ix)
  · apply Submodule.span_le.mpr
    rintro _ ⟨ix, rfl⟩
    exact ⟨interactionRectangle_forgetPoint i₀ ix.1 x₀ ix.2,
      interactionRectangle_forgetMultiplicity i₀ ix.1 x₀ ix.2⟩

/-- Every prescribed balanced marginal fiber is one explicit state plus the
joint kernel. This classifies all gluings, not only one chosen gluing. -/
theorem jointMarginals_iff_interaction_translate
    (i₀ : ClassicalHodgeBasisIndex V H p)
    (x₀ : CodimensionPoint V.X p)
    (a : ClassicalHodgeBasisIndex V H p →₀ ℚ)
    (b : FiniteCodimensionPresentation V.X p)
    (hm : multiplicityMass V H p a = presentationMass b)
    (Φ : FiberedNativeAddress V H p) :
    (forgetPoint V H p Φ = a ∧ forgetMultiplicity V H p Φ = b) ↔
      ∃ Ψ : FiberedNativeAddress V H p,
        forgetPoint V H p Ψ = 0 ∧ forgetMultiplicity V H p Ψ = 0 ∧
          Φ = glueMarginals V H p i₀ x₀ a b + Ψ := by
  constructor
  · rintro ⟨ha, hb⟩
    refine ⟨Φ - glueMarginals V H p i₀ x₀ a b, ?_, ?_, ?_⟩
    · simp [ha, glueMarginals_forgetPoint V H p i₀ x₀ a b hm]
    · simp [hb, glueMarginals_forgetMultiplicity V H p i₀ x₀ a b]
    · abel
  · rintro ⟨Ψ, ha, hb, rfl⟩
    constructor
    · simp [ha, glueMarginals_forgetPoint V H p i₀ x₀ a b hm]
    · simp [hb, glueMarginals_forgetMultiplicity V H p i₀ x₀ a b]

/-- Changing anchors changes a reconstruction only by a joint interaction. -/
theorem anchor_change_has_zero_marginals
    (i₀ i₁ : ClassicalHodgeBasisIndex V H p)
    (x₀ x₁ : CodimensionPoint V.X p) (Φ : FiberedNativeAddress V H p) :
    forgetPoint V H p
        (marginalReconstruction i₀ x₀ Φ - marginalReconstruction i₁ x₁ Φ) = 0 ∧
      forgetMultiplicity V H p
        (marginalReconstruction i₀ x₀ Φ - marginalReconstruction i₁ x₁ Φ) = 0 := by
  simp

/-- **TWO-FACE DISCOVERY TEST.** A linear observable ignores all joint
interactions exactly when it is recoverable from the two marginals by this
explicit anchor formula. No existential semantic factor is assumed. -/
theorem observable_marginal_formula_iff
    {M : Type*} [AddCommGroup M] [Module ℚ M]
    (i₀ : ClassicalHodgeBasisIndex V H p)
    (x₀ : CodimensionPoint V.X p)
    (F : FiberedNativeAddress V H p →ₗ[ℚ] M) :
    (∀ i x, F (interactionRectangle i₀ i x₀ x) = 0) ↔
      ∀ Φ : FiberedNativeAddress V H p,
        F Φ = F (attachPoint V H p x₀ (forgetPoint V H p Φ)) +
          F (attachSheet V H p i₀ (forgetMultiplicity V H p Φ)) -
          multiplicityMass V H p (forgetPoint V H p Φ) • F (atom V H p i₀ x₀) := by
  constructor
  · intro hF Φ
    have hz : F (interactionProjection i₀ x₀ Φ) = 0 := by
      rw [interactionProjection_finite_normal_form, map_finsuppSum]
      simp [hF]
    have heq : F Φ = F (marginalReconstruction i₀ x₀ Φ) := by
      simpa [interactionProjection, sub_eq_zero] using hz
    simpa [marginalReconstruction, glueMarginals] using heq
  · intro hF i x
    simpa using hF (interactionRectangle i₀ i x₀ x)

#print axioms jointKernel_eq_rectangleSpan
#print axioms interactionProjection_idempotent
#print axioms jointMarginals_iff_interaction_translate
#print axioms observable_marginal_formula_iff

end GSTClassicalHodgeNativeInteractionNormalForm
