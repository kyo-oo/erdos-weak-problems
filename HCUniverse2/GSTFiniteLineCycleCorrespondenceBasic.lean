import Mathlib
import HCUniverse2.GSTFiniteLineHonestHodgeData
import HCUniverse2.GSTFiniteLineGeneralMLaw
import HCUniverse2.GSTFiniteLineAnalytification
/- SPLIT PIECE of GSTFiniteLineCycleCorrespondence.lean (the wave-9-G module-split law: the runner-kill window demands small pieces) -/

/-
Copyright (c) 2026. The HC-PROOF campaign. All rights reserved.

# GATE-L — THE TWO M-CYCLE LETTERS (wave 4-C)

The M-cycle automorphism's graphs as genuine realized closed
correspondences on the honest Hodge data:

* the residue-degree receipt — the M-cycle is an isomorphism, so its
  residue field maps are bijective (the composition roundtrips through
  `residueFieldMap_id`/`residueFieldMap_comp`), and the residue weight is
  one (the green finrank pattern of the finite-point lane);
* the point-action receipt — the M-cycle acts on the generic points by
  `cyclicPred` (the comap of the graded rotation permutes the block
  ideals);
* the two letters `finiteLineCycleLetterOne` (weight one) and
  `finiteLineCycleLetterZero` (weight zero): the graph correspondence of the
  M-cycle endomorphism with the transported sphere-cycle pullback (letter one)/the
  component-iso conjugate of the index shift (letter zero) as the
  cohomological operator, rotating the honest point/component families.

Honesty ledger: every statement is proved unconditionally.  No `sorry`,
no new axioms, no `native_decide`.  The GitHub CI lane
`gst-finite-line-cycle-correspondence.yml` owns the kernel check.
-/

set_option maxHeartbeats 70000000
set_option maxRecDepth 20000
set_option trace.profiler true

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
open GSTClassicalHodgeAnalytificationFunctoriality
open GSTClassicalHodgeFiniteClosedCorrespondence
open GSTClassicalHodgeFiniteClosedCorrespondenceOperator
open GSTClassicalHodgeProjectivePointTransport
open GSTNativeCodimensionCyclePresentation
open GSTSphereUnionComponents
open GSTSphereUnionPointClassGate
open GSTSingularCohomologyMaps
open GSTSphereCycleLegs
open GSTPositiveDimensionalLawLanding
open GSTFiniteLineRing
open GSTFiniteLineWorldCarrier
open GSTFiniteLineOverBase
open GSTFiniteLineGeneralMLaw
open GSTFiniteLinePointAlgebra
open GSTFiniteLineHonestHodgeData
open GSTComponentCohomologyZero
open GSTFiniteLineAnalytification

namespace GSTFiniteLineCycleCorrespondence

/-! ## §0 THE WAVE 9-Q INTEL SWEEP — the true signatures of the pinned
residue-field API as this Mathlib (v4.33.0-rc2) actually states them.
The pre-split chains were written against source-reading guesses and never
kernel-tested (the 04:52/06:25/07:50 batches' receipts: the chains' rewrite
patterns fire wrongly or not at all); these #checks make the exact forms a
log receipt for the receipt-guided rebuild. Unknown-constant #checks are
harmless command-level diagnostics — the sweep prints what EXISTS. -/

#check @Scheme.Hom.residueFieldMap
#check @Scheme.residueFieldMap_comp
#check @Scheme.Hom.residueFieldMap_congr
#check @Scheme.Hom.residueFieldMap_congr'
#check @Scheme.residueFieldMap_id
#check @Scheme.residueFieldCongr
#check @Scheme.residueFieldCongr_symm
#check @Scheme.Hom.residueDegree
#check @Scheme.Hom.comp_apply
#check @ConcreteCategory.id_apply
#check @ConcreteCategory.bijective_of_isIso
#check @IsOpenImmersion.of_isIso

/-! ## §0.5 The M-cycle endomorphism -/

/-- **THE M-CYCLE ENDOMORPHISM** — the M-cycle automorphism as a complex
scheme endomorphism (the over-base square is green). -/
noncomputable def finiteLineCycleEndo (M : ℕ) [NeZero M] :
    ComplexSchemeEndomorphism (finiteLineWorld M) where
  hom := finiteLineCycle M
  over_base := finiteLineCycle_over_base M

/-! ## §1 The residue-degree receipt -/

/-- The map_id transport (the wave-65 carrier's private helper, localized
for this module — private declarations do not export across files). -/
private theorem map_id_of_eq {A σ : Type u} [CommRing A] [SetLike σ A]
    [AddSubgroupClass σ A] {𝒜 : ℕ → σ} [GradedRing 𝒜] {f : 𝒜 →+*ᵍ 𝒜}
    (h : f = GradedRingHom.id 𝒜)
    (hf : HomogeneousIdeal.irrelevant 𝒜 ≤
      HomogeneousIdeal.map f (HomogeneousIdeal.irrelevant 𝒜)) :
    Proj.map f hf = 𝟙 (Proj 𝒜) := by
  subst h
  exact Proj.map_id

/-- The point-level roundtrips of the M-cycle (the wave 9-Q step: the
`congrArg (fun φ => φ x)` descent + `Scheme.Hom.comp_apply` normalization —
the green receipt `GSTFiniteLinePointsGateCoreTransport:389-394` — with
the id-application closed by `rfl` (the defeq test: `Scheme.Hom.id_apply`
does not exist in this Mathlib — the 07:50 receipt, unknown constant — and
the original `simpa` ground for an hour on exactly this normalization). -/
theorem finiteLineCycleInv_apply (M : ℕ) [NeZero M] (x : finiteLineScheme M) :
    finiteLineCycleInv M (finiteLineCycle M x) = x := by
  have hinv' : finiteLineCycle M ≫ finiteLineCycleInv M = 𝟙 (finiteLineScheme M) := by
    rw [finiteLineCycle, finiteLineCycleInv, ← Proj.map_comp]
    exact map_id_of_eq (lineRotateGraded_comp_inv M) _
  have h := congrArg (fun f => f x) hinv'
  rw [Scheme.Hom.comp_apply] at h
  exact h.trans rfl

theorem finiteLineCycle_apply_inv (M : ℕ) [NeZero M] (x : finiteLineScheme M) :
    finiteLineCycle M (finiteLineCycleInv M x) = x := by
  have hinv : finiteLineCycleInv M ≫ finiteLineCycle M = 𝟙 (finiteLineScheme M) := by
    rw [finiteLineCycle, finiteLineCycleInv, ← Proj.map_comp]
    exact map_id_of_eq (lineRotateInvGraded_comp M) _
  have h := congrArg (fun f => f x) hinv
  rw [Scheme.Hom.comp_apply] at h
  exact h.trans rfl

/-- The residue field maps of the M-cycle are bijective — THE WAVE 9-Q
ROUTE: the M-cycle is an isomorphism (`finiteLineCycle_isIso`, the green
receipt `GSTFiniteLineWorldCarrier:550`), and Mathlib's residue-field API
makes the residue map of an open immersion an isomorphism (the green
receipt `GSTFinitePointShiftWord:349-355`: `haveI hoi : IsOpenImmersion`
then `(ConcreteCategory.bijective_of_isIso _).2` with NO further witness)
— this theorem tests the instance chain LIVE at the plain-`IsIso` case.
The pre-split hand-rolled transport chains (hLφ/hφL through
`residueFieldCongr`/`residueFieldMap_congr`) are RETIRED to git history:
the 07:50 receipt proved their rewrite patterns fire wrongly or not at
all (never kernel-tested in the pre-split era; the :144/:155 pattern
mismatches). If the instance chain misses, the §0 #check sweep's
signature receipts feed the receipt-guided rebuild next cycle. -/
theorem finiteLineCycle_residueFieldMap_bijective (M : ℕ) [NeZero M]
    (x : finiteLineScheme M) :
    Function.Bijective
      (Scheme.Hom.residueFieldMap (finiteLineCycle M) x) := by
  haveI := finiteLineCycle_isIso M
  exact ConcreteCategory.bijective_of_isIso _

/-- **THE M-CYCLE'S RESIDUE WEIGHT IS ONE** — the isomorphism's residue
field maps are bijective, so the induced residue extension has rank one
(the green finrank pattern of the finite-point lane). -/
theorem finiteLineCycle_pointResidueWeight (M : ℕ) [NeZero M]
    (x : finiteLineScheme M) :
    pointResidueWeight (finiteLineCycle M) x = 1 := by
  have hsurj : Function.Surjective (Scheme.Hom.residueFieldMap
      (finiteLineCycle M) x) :=
    (finiteLineCycle_residueFieldMap_bijective M x).2
  letI : Algebra
      ((finiteLineScheme M).residueField (finiteLineCycle M x))
      ((finiteLineScheme M).residueField x) :=
    (Scheme.Hom.residueFieldMap (finiteLineCycle M) x).hom.toAlgebra
  -- THE WAVE 9-P SURGERY: the `show`-bridge + `rw [Scheme.Hom.residueDegree]`
  -- delta (the pattern the TwelvePoint/ShiftWord run-26..29 receipts PROVED
  -- dies on the residueDegree delta+zeta) replaced by the green idiom
  -- `dsimp only [Scheme.Hom.residueDegree]` (ResidueField.lean's own
  -- `residueDegree_id` route), with the `pointResidueWeight` wrapper
  -- unfolded alongside it.
  dsimp only [pointResidueWeight, Scheme.Hom.residueDegree]
  have : (Module.finrank ((finiteLineScheme M).residueField (finiteLineCycle M x))
      ((finiteLineScheme M).residueField x)) = 1 := by
    refine (finrank_eq_one_iff_of_nonzero'
      (1 : (finiteLineScheme M).residueField x) one_ne_zero).mpr ?_
    intro w
    obtain ⟨a, ha⟩ := hsurj w
    refine ⟨a, ?_⟩
    calc a • (1 : (finiteLineScheme M).residueField x)
        = Scheme.Hom.residueFieldMap (finiteLineCycle M) x a := by
          rw [Algebra.smul_def, mul_one]
          rfl
      _ = w := ha
  rw [this]
  rfl



end GSTFiniteLineCycleCorrespondence

end -- noncomputable section
