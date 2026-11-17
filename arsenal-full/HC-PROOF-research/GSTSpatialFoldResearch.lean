import GSTFoldRotation
import GSTFoldPolarization
import GSTCausalFoldDefect
import GSTVariableFoldIntegrability
import GSTGraphV2GeneralSpaceRealization
import GSTLawStackRound51
import GSTCMFiniteGeometricDegreeDescent
import GSTSpectralBoundaryDefect
import GSTFoldPeriodDescent
import GSTCausalPairingGraphs
import GSTGraphV2UnboundedHigherCausality
import GSTGradedWorldAlgebra
import waves.GSTNCohomologyV3

/-!
GST spatial-fold continuation, 2026-11-02. Algebraic proof drafts, with the
constant-torus, divisor, and integrability geometry in the companion LaTeX.
The native CM coefficient-descent theorem below remains scheme-conditional;
its geometric input is not silently manufactured for an arbitrary original X.
-/

#check GSTFoldRotation.doubled_door_witness
#check GSTFoldRotation.integral_door_iff
#check GSTFoldPolarization.polarization_positive
#check GSTCausalFoldDefect.word_defect_exact
#check GSTCausalFoldDefect.endpoint_break_has_bad_edge
#check GSTCausalFoldDefect.nativeCycleTower_class
#check GSTCausalFoldDefect.nativeCycleCombination_class
#check GSTCausalFoldDefect.rational_range_saturated
#check GSTLawStackRound51Actual.rides_always_gives_constructively
#check GSTLawStackRound51Actual.rides_branching_constructively
#check GSTLawStackRound51Actual.labeled_rulings_reconstruct
#check GSTLawStackRound51Actual.rational_control_break_survives_scale
#check GSTSpectralBoundaryDefect.cyclic_cubic_orientation_numerator
#check GSTSpectralBoundaryDefect.orientation_square_zero
#check GSTGraphV2GeneralSpaceRealization.forward_pair_defect
#check GSTVariableFoldIntegrability.variableFold_square
#check GSTVariableFoldIntegrability.nijenhuisCoefficient_zero_iff
#check GSTCMFiniteGeometricDegreeDescent.native_rational_cm_cycle_of_geometric_field_expansion
#check GSTFoldPeriodDescent.affine_period_coefficients
#check GSTFoldPeriodDescent.fixed_balanced_period
#check GSTFoldPeriodDescent.three_charge_kernels
#check GSTCausalPairingGraphs.graph_special_linear_invariant
#check GSTCausalPairingGraphs.normalize_handle_return

-- Actual custom-module central-fold continuation; uncompiled drafts.
#check GSTGraphV2UnboundedHigherCausality.CentralCausalFold.cocycle_coherence
#check GSTGraphV2UnboundedHigherCausality.CentralCausalFold.centralMul_assoc
#check GSTGraphV2GeneralSpaceRealization.causalWordSpace
#check GSTGraphV2GeneralSpaceRealization.restored_endpoint_can_have_broken_prefix
#check GSTCausalFoldDefect.pure_split_iff_missing_mode_zero
#check GSTNCohomologyV3.all_channels_closed_iff_zero_curvature
#check GSTGradedWorldAlgebra.centralFold_opposedness_defect
#check GSTCausalFoldDefect.restoring_factorization_unique
#check GSTCausalFoldDefect.restoringLift_injective
#check GSTGradedWorldAlgebra.twoCurvatureBoundary_shear
#check GSTGradedWorldAlgebra.dependent_curvature_exposes_flat_handle
#check GSTNCohomologyV3.targetCurvature_zero_iff
#check GSTNCohomologyV3.targetCurvature_detects_prescribed_input

namespace GSTSpatialFoldResearch
open GSTNCohomology GSTNCohomologyV3

/-- Instantiates the split law on the actual N-channel curvature matrix. -/
theorem central_N_channels_pure_split_iff (s t : NShape)
    (K : Fin s.holes → Fin t.holes → ℚ) (u v : Fin s.holes → ℂ)
    (hu : complexCurvatureLinear s t K u=0) :
    (∃ a b : Fin s.holes → ℂ,
      complexCurvatureLinear s t K a=0 ∧ complexCurvatureLinear s t K b=0 ∧
      u=a+b ∧ v=Complex.I • (a-b)) ↔ complexCurvatureLinear s t K v=0 := by
  exact GSTCausalFoldDefect.pure_split_iff_missing_mode_zero
    (complexCurvatureLinear s t K) u v hu

#print axioms central_N_channels_pure_split_iff
end GSTSpatialFoldResearch

-- Complete finite mixed-degree clearing and minimality guards; uncompiled.
#check GSTGradedWorldAlgebra.simultaneousCupClear_all_redundant
#check GSTGradedWorldAlgebra.simultaneousCupClear_comp
#check GSTGradedWorldAlgebra.simultaneousCupClear_preserves_submodule
#check GSTGradedWorldAlgebra.nilpotent_cup_clearing_zero_iff
#check GSTGradedWorldAlgebra.augmentation_zero_row_not_unimodular

-- Marked-base kernels survive nonlinear coordinate changes on full cochains.
-- Hand derived-fiber classification and secondary operations are separate.
#check GSTGradedWorldAlgebra.baseBoundaryModule_eq_of_chainEquiv
#check GSTGradedWorldAlgebra.baseBoundaryModule_eq_curvatureRange
#check GSTGradedWorldAlgebra.nonzero_base_boundary_forbids_retraction
#check GSTGradedWorldAlgebra.twoCurvature_base_boundary_iff
#check GSTGradedWorldAlgebra.coupled_annihilator_cycle
#check GSTGradedWorldAlgebra.coupled_nonzero_u_not_boundary

-- Projective algebraization uses actual torsor-torsion, beyond curvature zero.
#check GSTCausalFoldDefect.torsionRelation_eq_kernel_saturation
#check GSTCausalFoldDefect.torsionRelation_saturated
#check GSTCausalFoldDefect.torsionRelation_le_curvatureKernel
#check GSTCausalFoldDefect.isogeny_kernel_torsion
#check GSTCausalFoldDefect.finite_torsion_common_annihilator
#check GSTCausalFoldDefect.projective_relation_factorization_unique

-- General projective folds retain every original-base rational class.
-- The actual geometric return and boundary-support theorem are hand proofs.
#check GSTCausalFoldDefect.projective_fold_nullifier_zero
#check GSTCausalFoldDefect.foldTransfer_composite
#check GSTCausalFoldDefect.fold_cycle_image_iff
#check GSTCausalFoldDefect.boundary_combination_return

-- Explicit curvature exact sequence and completed divisorial return algebra.
#check GSTCausalFoldDefect.missingModeMap_surjective
#check GSTCausalFoldDefect.missingMode_kernel_pure_split
#check GSTCausalFoldDefect.missingMode_nonzero_witness
#check GSTCausalFoldDefect.corrected_boundary_lift
#check GSTCausalFoldDefect.denominator_cleared_boundary_return
#check GSTCausalFoldDefect.ample_primitive_survives_restriction

-- Full-degree quotient/annihilator readout and first-order curvature memory.
#check GSTGradedWorldAlgebra.curvatureCycleReadout_surjective
#check GSTGradedWorldAlgebra.curvatureCycleReadout_zero_iff
#check GSTGradedWorldAlgebra.paired_curvature_dimension
#check GSTGradedWorldAlgebra.curvature_trace_orthogonal_iff
#check GSTGradedWorldAlgebra.curvature_trace_quotient_independent
#check GSTGradedWorldAlgebra.curvature_first_order_obstruction
#check GSTGradedWorldAlgebra.curvature_first_order_recovers_target
#check GSTGradedWorldAlgebra.pairedCurvaturePolynomial_exact_loss
#check GSTGradedWorldAlgebra.curvature_first_jet_faithful
