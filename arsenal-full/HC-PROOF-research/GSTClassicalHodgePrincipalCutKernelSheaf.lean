import GSTClassicalHodgePointClosurePrincipalCut
import Mathlib.AlgebraicGeometry.IdealSheaf.Functorial

/-!
# GST CLASSICAL HODGE — EXACT KERNEL SHEAF OF THE RELATIVE PRINCIPAL CUT

The closure-principal cut is the pullback of the actual principal-section
closed immersion along the point-closure immersion.  Mathlib's ideal-sheaf
functoriality therefore computes its kernel exactly: it is the pullback of the
principal-section kernel sheaf.

This is stronger and more precise than merely knowing that the cut map is a
closed immersion.  It isolates the genuine local ideal whose stalk quotient
controls the remaining ambient codimension step.
-/

set_option maxHeartbeats 40000000
set_option maxRecDepth 1000000

noncomputable section

open CategoryTheory Limits
open AlgebraicGeometry
open GSTProjectiveOverC
open GSTClassicalHodgeProjectivePrincipalSection
open GSTClassicalHodgePointClosurePrincipalCut

namespace GSTClassicalHodgePrincipalCutKernelSheaf

/-- The generator-specific principal-section ideal pulled back to the reduced
closure of the source point. -/
noncomputable def relativePrincipalCutIdeal
    (V : SmoothProjectiveComplexScheme) (x : V.X) :
    (pointClosureScheme V x).IdealSheafData :=
  (principalSectionIdeal V
      (positiveHomogeneousSeparator V.projective.n
        (V.projective.immersion x)).equation).comap
    (pointClosureι V x)

/-- **EXACT RELATIVE CUT KERNEL SHEAF.**
The kernel ideal sheaf of the actual closure-principal cut is exactly the
pullback of the source-specific principal-section ideal sheaf. -/
theorem closurePrincipalCut_kernel_eq_relativePrincipalCutIdeal
    (V : SmoothProjectiveComplexScheme) (x : V.X) :
    (closurePrincipalCutToClosure V x).ker =
      relativePrincipalCutIdeal V x := by
  have hker :
      (principalSectionAtι V x).ker =
        principalSectionIdeal V
          (positiveHomogeneousSeparator V.projective.n
            (V.projective.immersion x)).equation := by
    dsimp [principalSectionAtι, principalSectionAt,
      principalSectionι, principalSection]
    exact Scheme.IdealSheafData.ker_subschemeι _
  unfold closurePrincipalCutToClosure relativePrincipalCutIdeal
  exact
    (Scheme.IdealSheafData.ker_fst_of_isClosedImmersion
      (principalSectionAtι V x) (pointClosureι V x)).trans
      (congrArg (fun J => J.comap (pointClosureι V x)) hker)

/-- The relative cut itself is therefore the closed geometry associated to a
completely explicit pulled-back ideal sheaf, up to the canonical pullback
presentation already built in Mathlib. -/
noncomputable def relativePrincipalCutIsoPullbackSubscheme
    (V : SmoothProjectiveComplexScheme) (x : V.X) :
    (relativePrincipalCutIdeal V x).subscheme ≅
      closurePrincipalCut V x := by
  exact
    (principalSectionIdeal V
      (positiveHomogeneousSeparator V.projective.n
        (V.projective.immersion x)).equation).comapIso
      (pointClosureι V x)

/-- Kernel-sheaf crown: both the scheme-theoretic cut and its defining local
ideal are now fixed by the source point and projective separator. -/
theorem relative_principal_cut_kernel_crown
    (V : SmoothProjectiveComplexScheme) (x : V.X) :
    (closurePrincipalCutToClosure V x).ker =
      relativePrincipalCutIdeal V x :=
  closurePrincipalCut_kernel_eq_relativePrincipalCutIdeal V x

#check relativePrincipalCutIdeal
#check closurePrincipalCut_kernel_eq_relativePrincipalCutIdeal
#check relativePrincipalCutIsoPullbackSubscheme
#check relative_principal_cut_kernel_crown

#print axioms closurePrincipalCut_kernel_eq_relativePrincipalCutIdeal
#print axioms relative_principal_cut_kernel_crown

end GSTClassicalHodgePrincipalCutKernelSheaf
