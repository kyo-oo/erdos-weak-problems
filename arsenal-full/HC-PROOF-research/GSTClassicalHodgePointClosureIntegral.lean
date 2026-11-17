import GSTClassicalHodgePointClosureIrreducible
import Mathlib.AlgebraicGeometry.IdealSheaf.Subscheme
import Mathlib.RingTheory.Ideal.Quotient.Nilpotent

/-!
# GST CLASSICAL HODGE — REDUCED / INTEGRAL POINT CLOSURE

`pointClosureScheme V x` was deliberately defined as the subscheme associated
to the vanishing ideal of the closed set `closure {x}`.  Mathlib's vanishing
ideal gives the reduced induced scheme structure.  This file exposes that fact
in the exact form needed by the local principal-cut dimension argument.

On every affine chart `U`, the vanishing ideal is a radical ring ideal.  Hence
`Gamma(U) / I(U)` is reduced.  The canonical subscheme cover consists exactly
of the spectra of those quotient rings, so the whole point-closure scheme is
reduced.  The closure is already proved irreducible; reduced + irreducible is
therefore integral.  In particular every point-closure stalk is a domain.

No Hodge data, cycle-class map, or nonvanishing assumption occurs here.
-/

set_option maxHeartbeats 80000000
set_option maxRecDepth 1000000

noncomputable section

open AlgebraicGeometry
open TopologicalSpace

namespace GSTClassicalHodgePointClosureIntegral

open GSTProjectiveOverC
open GSTClassicalHodgePointClosurePrincipalCut
open GSTClassicalHodgePointClosureIrreducible

/-- Every affine component ideal of the point-closure vanishing ideal is
radical. -/
theorem pointClosureIdeal_affine_isRadical
    (V : SmoothProjectiveComplexScheme)
    (x : V.X)
    (U : V.X.affineOpens) :
    ((pointClosureIdeal V x).ideal U).IsRadical := by
  change
    (PrimeSpectrum.vanishingIdeal
      (U.2.fromSpec ⁻¹' (pointClosureClosed V x : Set V.X))).IsRadical
  exact PrimeSpectrum.isRadical_vanishingIdeal _

/-- The reduced induced structure chosen in `pointClosureScheme` is genuinely
reduced. -/
noncomputable def pointClosureIsReduced
    (V : SmoothProjectiveComplexScheme)
    (x : V.X) :
    IsReduced (pointClosureScheme V x) := by
  let I : V.X.IdealSheafData := pointClosureIdeal V x
  letI : ∀ i : I.subschemeCover.openCover.I₀,
      IsReduced (I.subschemeCover.openCover.X i) := fun i => by
    have hrad : (I.ideal i).IsRadical := by
      simpa [I] using pointClosureIdeal_affine_isRadical V x i
    have hred : _root_.IsReduced (Γ(V.X, (i : V.X.affineOpens)) ⧸ I.ideal i) :=
      (Ideal.isRadical_iff_quotient_reduced (I.ideal i)).mp hrad
    exact (affine_isReduced_iff (CommRingCat.of (Γ(V.X, (i : V.X.affineOpens)) ⧸ I.ideal i))).mpr hred
  exact IsReduced.of_openCover (pointClosureScheme V x) I.subschemeCover.openCover

/-- A point closure is both irreducible and reduced, hence an integral scheme. -/
noncomputable def pointClosureIsIntegral
    (V : SmoothProjectiveComplexScheme)
    (x : V.X) :
    IsIntegral (pointClosureScheme V x) := by
  letI : IrreducibleSpace (pointClosureScheme V x) :=
    pointClosureIrreducibleSpace V x
  letI : IsReduced (pointClosureScheme V x) := pointClosureIsReduced V x
  exact isIntegral_of_irreducibleSpace_of_isReduced (pointClosureScheme V x)

/-- Every local ring of the reduced irreducible point closure is a domain. -/
noncomputable def pointClosureStalkIsDomain
    (V : SmoothProjectiveComplexScheme)
    (x : V.X)
    (y : pointClosureScheme V x) :
    IsDomain ((pointClosureScheme V x).presheaf.stalk y) := by
  letI : IsIntegral (pointClosureScheme V x) := pointClosureIsIntegral V x
  infer_instance

/-- Integral point-closure crown in the form consumed by the stalk cut. -/
theorem point_closure_integral_crown
    (V : SmoothProjectiveComplexScheme)
    (x : V.X) :
    Nonempty (pointClosureScheme V x)
      ∧ IsIrreducible (Set.univ : Set (pointClosureScheme V x)) := by
  letI : IrreducibleSpace (pointClosureScheme V x) :=
    pointClosureIrreducibleSpace V x
  exact ⟨⟨closureGenericPoint V x⟩, IrreducibleSpace.isIrreducible_univ (pointClosureScheme V x)⟩

#check pointClosureIdeal_affine_isRadical
#check pointClosureIsReduced
#check pointClosureIsIntegral
#check pointClosureStalkIsDomain
#check point_closure_integral_crown

#print axioms pointClosureIdeal_affine_isRadical
#print axioms pointClosureIsReduced
#print axioms pointClosureIsIntegral
#print axioms pointClosureStalkIsDomain

end GSTClassicalHodgePointClosureIntegral
