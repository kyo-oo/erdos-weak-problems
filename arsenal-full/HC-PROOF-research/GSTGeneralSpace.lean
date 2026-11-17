import Mathlib

/-!
# General Space Theory — carrier-independent ontology

This file is the new ontological root of GST.  A General Space has no built-in
metric, dimension, Euclidean chart, arithmetic grid, or finite observation
window.  All of those belong to optional realization/capability layers.
-/

universe u v w

namespace GSTGeneralSpace

/-- A carrier-independent space with typed composable paths. -/
structure GeneralSpace where
  Point : Type u
  Path : Point → Point → Sort v
  idPath : (x : Point) → Path x x
  compPath : {x y z : Point} → Path x y → Path y z → Path x z
  comp_id_left : ∀ {x y} (γ : Path x y), compPath (idPath x) γ = γ
  comp_id_right : ∀ {x y} (γ : Path x y), compPath γ (idPath y) = γ
  comp_assoc : ∀ {w x y z} (α : Path w x) (β : Path x y) (γ : Path y z),
    compPath (compPath α β) γ = compPath α (compPath β γ)

namespace GeneralSpace

/-- Coordinates are observations of a General Space; they are not its ontology. -/
structure Chart (G : GeneralSpace) where
  Coord : Type w
  observe : G.Point → Coord

/-- An intrinsic predicate on a General Space. -/
abbrev Predicate (G : GeneralSpace) := G.Point → Prop

/-- An intrinsic observable on a General Space. -/
abbrev Observable (G : GeneralSpace) (A : Type w) := G.Point → A

/-- Optional incidence geometry. -/
structure IncidenceGeometry (G : GeneralSpace) where
  Incides : G.Point → G.Point → Prop

/-- Optional grading data.  The grade carrier itself is arbitrary. -/
structure GradedGeometry (G : GeneralSpace) where
  Grade : Type w
  grade : G.Point → Grade

/-- A discrete General Space on an arbitrary carrier. -/
def discrete (α : Type u) : GeneralSpace where
  Point := α
  Path x y := x = y
  idPath := fun _ => rfl
  compPath := fun h₁ h₂ => h₁.trans h₂
  comp_id_left := by intro x y γ; cases γ; rfl
  comp_id_right := by intro x y γ; cases γ; rfl
  comp_assoc := by intro w x y z α β γ; cases α; cases β; cases γ; rfl

@[simp] theorem discrete_path_iff {α : Type u} {x y : α} :
    (discrete α).Path x y ↔ x = y := Iff.rfl

/-- Every type is therefore admissible as a dimensionless GST point carrier. -/
def carrierChart (α : Type u) : Chart (discrete α) where
  Coord := α
  observe := id

@[simp] theorem carrierChart_observe {α : Type u} (x : α) :
    (carrierChart α).observe x = x := rfl

end GeneralSpace

#check GeneralSpace
#check GeneralSpace.Chart
#check GeneralSpace.IncidenceGeometry
#check GeneralSpace.GradedGeometry
#check GeneralSpace.discrete

end GSTGeneralSpace
