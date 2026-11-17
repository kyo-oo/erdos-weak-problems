import GSTGeneralSpaceSchemeStalkComorphism
import GSTClassicalHodgePointClosurePrincipalCut
import Mathlib.RingTheory.Ideal.Quotient.Operations

/-!
# GST CLASSICAL HODGE — PRINCIPAL CUT STALK COSMOS

The closure-principal cut is an actual closed immersion.  In the fibered
General-Space language this means that, at every cut point, the ambient point-
closure stalk maps surjectively onto the cut stalk.

This file takes the first-isomorphism theorem immediately: the cut stalk is
canonically the quotient of the source stalk by the genuine stalk kernel.
Nothing about the kernel is guessed or supplied.
-/

set_option maxHeartbeats 30000000
set_option maxRecDepth 1000000

noncomputable section

open CategoryTheory
open AlgebraicGeometry
open GSTGeneralSpace
open GSTClassicalHodgePointClosurePrincipalCut

namespace GSTClassicalHodgePrincipalCutStalkCosmos

/-- The genuine local-ring homomorphism induced by the closure-principal
closed immersion. -/
noncomputable def closurePrincipalCutStalkMap
    (V : GSTProjectiveOverC.SmoothProjectiveComplexScheme)
    (x : V.X)
    (z : closurePrincipalCut V x) :
    (pointClosureScheme V x).presheaf.stalk
        (closurePrincipalCutToClosure V x z) →+*
      (closurePrincipalCut V x).presheaf.stalk z :=
  ((closurePrincipalCutToClosure V x).stalkMap z).hom

/-- Its actual kernel inside the source-closure local ring. -/
noncomputable def closurePrincipalCutStalkKernel
    (V : GSTProjectiveOverC.SmoothProjectiveComplexScheme)
    (x : V.X)
    (z : closurePrincipalCut V x) :
    Ideal ((pointClosureScheme V x).presheaf.stalk
      (closurePrincipalCutToClosure V x z)) :=
  RingHom.ker (closurePrincipalCutStalkMap V x z)

/-- Closed immersion gives surjectivity on the local GST stalk fiber. -/
theorem closurePrincipalCutStalkMap_surjective
    (V : GSTProjectiveOverC.SmoothProjectiveComplexScheme)
    (x : V.X)
    (z : closurePrincipalCut V x) :
    Function.Surjective (closurePrincipalCutStalkMap V x z) := by
  exact (closurePrincipalCutToClosure V x).stalkMap_surjective z

/-- **LOCAL FIRST-ISOMORPHISM LAW FOR THE ACTUAL CUT.**
The target cut stalk is canonically the quotient of the point-closure stalk by
the true kernel of the closed immersion. -/
noncomputable def closurePrincipalCutStalkQuotientEquiv
    (V : GSTProjectiveOverC.SmoothProjectiveComplexScheme)
    (x : V.X)
    (z : closurePrincipalCut V x) :
    ((pointClosureScheme V x).presheaf.stalk
        (closurePrincipalCutToClosure V x z) ⧸
      closurePrincipalCutStalkKernel V x z) ≃+*
        (closurePrincipalCut V x).presheaf.stalk z := by
  exact RingHom.quotientKerEquivOfSurjective
    (closurePrincipalCutStalkMap_surjective V x z)

/-- Consequently the two local rings have identical Krull dimension after
quotienting by precisely the genuine cut kernel. -/
theorem cutStalk_ringKrullDim_eq_quotientKernel
    (V : GSTProjectiveOverC.SmoothProjectiveComplexScheme)
    (x : V.X)
    (z : closurePrincipalCut V x) :
    ringKrullDim ((closurePrincipalCut V x).presheaf.stalk z) =
      ringKrullDim
        ((pointClosureScheme V x).presheaf.stalk
            (closurePrincipalCutToClosure V x z) ⧸
          closurePrincipalCutStalkKernel V x z) := by
  exact (ringKrullDim_eq_of_ringEquiv
    (closurePrincipalCutStalkQuotientEquiv V x z)).symm

#check closurePrincipalCutStalkMap
#check closurePrincipalCutStalkKernel
#check closurePrincipalCutStalkMap_surjective
#check closurePrincipalCutStalkQuotientEquiv
#check cutStalk_ringKrullDim_eq_quotientKernel

#print axioms closurePrincipalCutStalkMap_surjective
#print axioms cutStalk_ringKrullDim_eq_quotientKernel

end GSTClassicalHodgePrincipalCutStalkCosmos
