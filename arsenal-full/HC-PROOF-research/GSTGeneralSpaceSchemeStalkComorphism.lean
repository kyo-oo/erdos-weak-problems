import GSTGeneralSpaceSchemeStalkFamily
import GSTGeneralSpaceMorphisms
import Mathlib.AlgebraicGeometry.Morphisms.ClosedImmersion

/-!
# GENERAL SPACE THEORY — SCHEME STALK COMORPHISMS

Scheme morphisms act covariantly on points but contravariantly on local rings.
This file records that mixed variance explicitly inside General Space Theory.
It is the correct local-family language for closed immersions and principal
cuts: the base point moves X -> Y while the stalk map moves O_{Y,f(x)} -> O_{X,x}.
-/

universe u v u' v' w w'

namespace GSTGeneralSpace

open AlgebraicGeometry
open GSTGeneralSpace.GeneralSpace

/-- A contravariant map of local families above a covariant map of base
General Spaces. -/
structure LocalComorphism
    {G : GeneralSpace.{u,v}} {H : GeneralSpace.{u',v'}}
    (f : GeneralSpace.Hom G H)
    (F : LocalFamily.{u,v,w} G)
    (K : LocalFamily.{u',v',w'} H) where
  map : ∀ x : G.Point, K.Fiber (f.mapPoint x) → F.Fiber x

/-- Every scheme morphism induces the corresponding General-Space map on
underlying carriers. -/
def schemeHomGeneralSpace
    {X Y : Scheme.{u}} (f : X ⟶ Y) :
    GeneralSpace.Hom (schemeGeneralSpace X) (schemeGeneralSpace Y) :=
  continuousHom f f.continuous

/-- The genuine scheme stalk map as a General-Space local-family comorphism. -/
noncomputable def schemeStalkComorphism
    {X Y : Scheme.{u}} (f : X ⟶ Y) :
    LocalComorphism (schemeHomGeneralSpace f)
      (schemeStalkFamily X) (schemeStalkFamily Y) where
  map x := f.stalkMap x

/-- Evaluation is definitionally the native Mathlib stalk map. -/
@[simp]
theorem schemeStalkComorphism_apply
    {X Y : Scheme.{u}} (f : X ⟶ Y)
    (x : X) (s : Y.presheaf.stalk (f x)) :
    (schemeStalkComorphism f).map x s = f.stalkMap x s := rfl

/-- **CLOSED-IMMERSION LOCAL CONTROL.**
A closed immersion is surjective on every local GST stalk comorphism. -/
theorem closedImmersion_stalkComorphism_surjective
    {X Y : Scheme.{u}} (f : X ⟶ Y)
    [IsClosedImmersion f]
    (x : X) :
    Function.Surjective ((schemeStalkComorphism f).map x) := by
  exact f.stalkMap_surjective x

/-- Specialization to any ideal-sheaf subscheme: its inclusion produces a
surjective map from the ambient stalk onto the subscheme stalk at every point. -/
theorem subscheme_stalkComorphism_surjective
    {X : Scheme.{u}} (I : X.IdealSheafData)
    (x : I.subscheme) :
    Function.Surjective
      ((schemeStalkComorphism I.subschemeι).map x) := by
  exact closedImmersion_stalkComorphism_surjective I.subschemeι x

#check LocalComorphism
#check schemeHomGeneralSpace
#check schemeStalkComorphism
#check closedImmersion_stalkComorphism_surjective
#check subscheme_stalkComorphism_surjective

end GSTGeneralSpace
