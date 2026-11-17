import GSTGeneralSpacePartialCharts

/-!
# GENERAL SPACE THEORY — REVERSIBLE PARTIAL CHARTS

A local coordinate system should not merely observe a region: on its valid
region it should recover the underlying cosmic point.  This file adds that
reversible local notion without putting coordinates into the General-Space
core.
-/

universe u v w

namespace GSTGeneralSpace

/-- A reversible local coordinatization of one General Space. -/
structure ReversiblePartialChart (G : GeneralSpace.{u,v}) where
  Coord : Type w
  domain : Set G.Point
  target : Set Coord
  coordEquiv : {x : G.Point // x ∈ domain} ≃ {c : Coord // c ∈ target}

namespace ReversiblePartialChart

/-- Forget reversibility and retain only the local observation. -/
def toPartialChart
    {G : GeneralSpace.{u,v}}
    (C : ReversiblePartialChart G) : PartialChart G where
  Coord := C.Coord
  domain := C.domain
  observe := fun x => (C.coordEquiv x).1

/-- Coordinate observation on the valid domain. -/
def observeAt
    {G : GeneralSpace.{u,v}}
    (C : ReversiblePartialChart G)
    (x : G.Point) (hx : x ∈ C.domain) : C.Coord :=
  (C.coordEquiv ⟨x, hx⟩).1

/-- Reconstruct the cosmic point from a valid coordinate. -/
def recoverAt
    {G : GeneralSpace.{u,v}}
    (C : ReversiblePartialChart G)
    (c : C.Coord) (hc : c ∈ C.target) : G.Point :=
  (C.coordEquiv.symm ⟨c, hc⟩).1

/-- Observing and recovering returns the original point. -/
theorem recover_observe
    {G : GeneralSpace.{u,v}}
    (C : ReversiblePartialChart G)
    (x : G.Point) (hx : x ∈ C.domain) :
    C.recoverAt (C.observeAt x hx)
      ((C.coordEquiv ⟨x, hx⟩).2) = x := by
  exact congrArg Subtype.val (C.coordEquiv.left_inv ⟨x, hx⟩)

/-- Recovering and observing returns the original coordinate. -/
theorem observe_recover
    {G : GeneralSpace.{u,v}}
    (C : ReversiblePartialChart G)
    (c : C.Coord) (hc : c ∈ C.target) :
    C.observeAt (C.recoverAt c hc)
      ((C.coordEquiv.symm ⟨c, hc⟩).2) = c := by
  exact congrArg Subtype.val (C.coordEquiv.right_inv ⟨c, hc⟩)

#check ReversiblePartialChart
#check toPartialChart
#check observeAt
#check recoverAt
#check recover_observe
#check observe_recover

end ReversiblePartialChart

end GSTGeneralSpace
