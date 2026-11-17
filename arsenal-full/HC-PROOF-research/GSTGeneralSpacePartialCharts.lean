import GSTGeneralSpaceMorphisms

/-!
# GENERAL SPACE THEORY — PARTIAL CHARTS

Real geometric coordinates are usually local.  The original total `Chart`
remains useful for global observations, but manifolds, schemes and local
trivializations require a partial chart whose domain is part of the data.

Coordinates still do not define the General Space: a partial chart is merely
an observation on one region of it.
-/

universe u v w u' v'

namespace GSTGeneralSpace

open GSTGeneralSpace.GeneralSpace

/-- A local observation chart on a General Space. -/
structure PartialChart (G : GeneralSpace.{u,v}) where
  Coord : Type w
  domain : Set G.Point
  observe : {x : G.Point // x ∈ domain} → Coord

namespace PartialChart

/-- Evaluate a partial chart at a point with a domain witness. -/
def observeAt
    {G : GeneralSpace.{u,v}}
    (C : PartialChart G) (x : G.Point) (hx : x ∈ C.domain) : C.Coord :=
  C.observe ⟨x, hx⟩

/-- Pull a local chart back through a map of whole General Spaces. -/
def pullback
    {G : GeneralSpace.{u,v}} {H : GeneralSpace.{u',v'}}
    (f : GeneralSpace.Hom G H) (C : PartialChart H) : PartialChart G where
  Coord := C.Coord
  domain := f.mapPoint ⁻¹' C.domain
  observe := fun x => C.observe ⟨f.mapPoint x.1, x.2⟩

@[simp]
theorem pullback_domain
    {G : GeneralSpace.{u,v}} {H : GeneralSpace.{u',v'}}
    (f : GeneralSpace.Hom G H) (C : PartialChart H) :
    (pullback f C).domain = f.mapPoint ⁻¹' C.domain := rfl

/-- Re-index the coordinate language without changing the observed region. -/
def reindex
    {G : GeneralSpace.{u,v}}
    (C : PartialChart G) {β : Type*} (e : C.Coord ≃ β) :
    PartialChart G where
  Coord := β
  domain := C.domain
  observe := e ∘ C.observe

/-- The overlap region of two local charts. -/
def overlap
    {G : GeneralSpace.{u,v}}
    (C D : PartialChart G) : Set G.Point :=
  C.domain ∩ D.domain

/-- A point in an overlap carries both coordinate observations without
identifying either coordinate type with the ontology. -/
def overlapObservations
    {G : GeneralSpace.{u,v}}
    (C D : PartialChart G)
    (x : {x : G.Point // x ∈ C.overlap D}) :
    C.Coord × D.Coord :=
  ⟨C.observe ⟨x.1, x.2.1⟩, D.observe ⟨x.1, x.2.2⟩⟩

#check PartialChart
#check observeAt
#check pullback
#check reindex
#check overlap
#check overlapObservations

end PartialChart

end GSTGeneralSpace
