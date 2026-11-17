import GSTGeneralSpaceTopology
import GSTGeneralSpaceFiberedCosmology
import Mathlib.AlgebraicGeometry.Properties

/-!
# GENERAL SPACE THEORY — SCHEME STALK FAMILY

A scheme is not reduced to coordinates in GST.  Its underlying topological
carrier is one General-Space realization, while its local rings form a genuine
point-dependent family above that carrier.

This is the local algebra layer needed by the Hodge principal-cut frontier:
Krull dimension is observed directly on the actual scheme stalk fiber.
-/

universe u

namespace GSTGeneralSpace

open AlgebraicGeometry

/-- Underlying topological General Space of an arbitrary Mathlib scheme. -/
abbrev schemeGeneralSpace (X : Scheme.{u}) : GeneralSpace :=
  topologicalGeneralSpace X

/-- Genuine local-ring family x ↦ O_{X,x}.  No transport between stalks is
invented: such maps require an actual scheme morphism/specialization mechanism. -/
def schemeStalkFamily (X : Scheme.{u}) : LocalFamily (schemeGeneralSpace X) where
  Fiber x := X.presheaf.stalk x

@[simp]
theorem schemeStalkFamily_fiber
    (X : Scheme.{u}) (x : X) :
    (schemeStalkFamily X).Fiber x = X.presheaf.stalk x := rfl

/-- The stalk fiber carries the genuine commutative-ring structure of the
scheme stalk; the instance bridge is definitional (the fiber IS the stalk). -/
noncomputable instance (X : Scheme.{u}) (x : X) :
    CommSemiring ((schemeStalkFamily X).Fiber x) :=
  inferInstanceAs (CommSemiring (X.presheaf.stalk x))

/-- Krull dimension of the local GST fiber is exactly the scheme-theoretic
coheight of the point.  Thus the native codimension observable is intrinsic to
the stalk realization, not an external coordinate label. -/
theorem schemeStalk_dimension_eq_coheight
    (X : Scheme.{u}) (x : X) :
    ringKrullDim ((schemeStalkFamily X).Fiber x) = Order.coheight x := by
  exact AlgebraicGeometry.ringKrullDim_stalk_eq_coheight x

/-- The local algebraic family exists for every scheme, independent of
projectivity, smoothness, finiteness, dimension, or coordinates. -/
theorem every_scheme_has_stalk_family (X : Scheme.{u}) :
    Nonempty (@LocalFamily.{u, 0, u} (schemeGeneralSpace X)) :=
  ⟨schemeStalkFamily X⟩

#check schemeGeneralSpace
#check schemeStalkFamily
#check schemeStalk_dimension_eq_coheight
#check every_scheme_has_stalk_family

end GSTGeneralSpace
