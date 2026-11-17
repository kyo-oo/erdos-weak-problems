import GSTGeneralSpaceSchemeStalkFamily
import GSTNativeCodimensionCyclePresentation

/-!
# GENERAL SPACE THEORY — SCHEME DIMENSION AS AN OBSERVATION

General Space itself has no dimension field.  Scheme-theoretic codimension is
instead an observation extracted from the local-ring family:

  x ↦ dim O_{X,x} = coheight(x).

This makes the architectural law literal: dimension describes a realization;
it does not define the underlying General Space.
-/

universe u

namespace GSTGeneralSpace

open AlgebraicGeometry
open GSTNativeCodimensionCyclePresentation

noncomputable local instance {X : Scheme.{u}} {x : X} :
    CommSemiring ((schemeStalkFamily X).Fiber x) :=
  inferInstanceAs (CommSemiring (X.presheaf.stalk x))

/-- Local Krull-dimension observation chart of an arbitrary scheme. -/
noncomputable def schemeKrullDimensionChart
    (X : Scheme.{u}) : GeneralSpace.Chart (schemeGeneralSpace X) where
  Coord := WithBot ℕ∞
  observe x := @ringKrullDim ((schemeStalkFamily X).Fiber x)
    (inferInstanceAs (CommSemiring (X.presheaf.stalk x)))

/-- The chart reads exactly the intrinsic scheme coheight. -/
theorem schemeKrullDimensionChart_observe
    (X : Scheme.{u}) (x : X) :
    (schemeKrullDimensionChart X).observe x = ((Order.coheight x : WithBot ℕ∞)) :=
  AlgebraicGeometry.ringKrullDim_stalk_eq_coheight x

/-- A native codimension-p point is precisely seen at value p by the local
General-Space dimension observation. -/
theorem codimensionPoint_observed_exactly
    (X : Scheme.{u}) (p : Nat)
    (x : CodimensionPoint X p) :
    (schemeKrullDimensionChart X).observe x.1 = ((p : WithBot ℕ∞)) := by
  rw [schemeKrullDimensionChart_observe X x.1]
  exact WithBot.coe_eq_coe.mpr x.2

/-- Observation-only crown: the codimension label is completely recovered
from local geometry and is absent from the ontological core. -/
theorem codimension_observation_crown
    (X : Scheme.{u}) (p : Nat)
    (x : CodimensionPoint X p) :
    ringKrullDim ((schemeStalkFamily X).Fiber x.1) = p
      ∧ Order.coheight x.1 = p := by
  exact ⟨by
      rw [schemeStalk_dimension_eq_coheight X x.1]
      exact WithBot.coe_eq_coe.mpr x.2,
    x.2⟩

#check schemeKrullDimensionChart
#check schemeKrullDimensionChart_observe
#check codimensionPoint_observed_exactly
#check codimension_observation_crown

end GSTGeneralSpace
