import GSTGeneralSpaceRecoordination

universe u v w w₁ w₂

namespace GSTGeneralSpace

/-- A concrete face/observation of one General Space. -/
structure Realization (G : GeneralSpace.{u, v}) where
  State : Type w
  realize : G.Point → State

/-- A map between two realizations of the same General Space. -/
structure RealizationMap {G : GeneralSpace.{u, v}}
    (R₁ : Realization.{u,v,w₁} G) (R₂ : Realization.{u,v,w₂} G) where
  map : R₁.State → R₂.State
  commute : ∀ x : G.Point, map (R₁.realize x) = R₂.realize x

namespace RealizationMap

variable {G : GeneralSpace}

/-- Identity comparison of a realization with itself. -/
def refl (R : Realization G) : RealizationMap R R where
  map := id
  commute := by intro x; rfl

/-- Composition of compatible realization maps. -/
def comp {R₁ : Realization.{u,v,w} G}
    {R₂ : Realization.{u,v,w₁} G}
    {R₃ : Realization.{u,v,w₂} G}
    (f : RealizationMap R₁ R₂) (g : RealizationMap R₂ R₃) :
    RealizationMap R₁ R₃ where
  map := g.map ∘ f.map
  commute := by intro x; simp [Function.comp_def, f.commute, g.commute]

end RealizationMap

/-- Two transported realization faces are synchronized when realization
commutes with every admissible General Space path. -/
structure TransportedRealization (G : GeneralSpace.{u, v}) where
  realization : Realization.{u, v, w} G
  transport : TransportGeometry.{w₁, u, v} G
  encode : realization.State → transport.State
  path_naturality : ∀ {x y : G.Point} (γ : G.Path x y),
    encode (realization.realize y) =
      transport.transport γ (encode (realization.realize x))

namespace TransportedRealization

variable {G : GeneralSpace}

/-- Naturality along a composite path is forced by General Space transport. -/
theorem composite_naturality (R : TransportedRealization G)
    {x y z : G.Point} (α : G.Path x y) (β : G.Path y z) :
    R.encode (R.realization.realize z) =
      R.transport.transport β
        (R.transport.transport α (R.encode (R.realization.realize x))) := by
  rw [← R.transport.transport_comp]
  exact R.path_naturality (G.compPath α β)

end TransportedRealization

#check Realization
#check RealizationMap
#check TransportedRealization

end GSTGeneralSpace
