import GSTGeneralSpaceRealization
import GSTGeneralSpaceMorphisms
import GSTGeneralSpaceRecoordination

/-!
# GENERAL SPACE THEORY — FUNCTORIAL REALIZATIONS

Whole-space morphisms are useful only if observations and transports can move
through them.  This module proves that realizations, charts, state transport,
and reversible recoordination all pull back/map functorially along a General
Space morphism.

This is the ontology-level mechanism used later to compare manifold, graph,
scheme, Betti, Hodge and native-cycle sectors without identifying them.
-/

universe u v u' v' w

namespace GSTGeneralSpace

open GSTGeneralSpace.GeneralSpace

namespace GeneralSpace.Chart

/-- Observe a source General Space through a chart on a target space. -/
def pullback
    {G : GeneralSpace.{u,v}} {H : GeneralSpace.{u',v'}}
    (f : GeneralSpace.Hom G H) (C : GeneralSpace.Chart H) :
    GeneralSpace.Chart G where
  Coord := C.Coord
  observe := C.observe ∘ f.mapPoint

@[simp]
theorem pullback_observe
    {G : GeneralSpace.{u,v}} {H : GeneralSpace.{u',v'}}
    (f : GeneralSpace.Hom G H) (C : GeneralSpace.Chart H)
    (x : G.Point) :
    (pullback f C).observe x = C.observe (f.mapPoint x) := rfl

end GeneralSpace.Chart

namespace Realization

/-- Pull a target realization back through a whole-space morphism. -/
def pullback
    {G : GeneralSpace.{u,v}} {H : GeneralSpace.{u',v'}}
    (f : GeneralSpace.Hom G H) (R : Realization H) : Realization G where
  State := R.State
  realize := R.realize ∘ f.mapPoint

@[simp]
theorem pullback_realize
    {G : GeneralSpace.{u,v}} {H : GeneralSpace.{u',v'}}
    (f : GeneralSpace.Hom G H) (R : Realization H)
    (x : G.Point) :
    (pullback f R).realize x = R.realize (f.mapPoint x) := rfl

end Realization

namespace TransportGeometry

/-- Pull a functorial state-transport system back through a General-Space
morphism. -/
def pullback
    {G : GeneralSpace.{u,v}} {H : GeneralSpace.{u',v'}}
    (f : GeneralSpace.Hom G H) (T : TransportGeometry H) :
    TransportGeometry G where
  State := T.State
  transport := fun γ => T.transport (f.mapPath γ)
  transport_id := by
    intro x s
    rw [f.map_id, T.transport_id]
  transport_comp := by
    intro x y z α β s
    rw [f.map_comp, T.transport_comp]

/-- Pullback transport is literally target transport along the mapped path. -/
@[simp]
theorem pullback_transport
    {G : GeneralSpace.{u,v}} {H : GeneralSpace.{u',v'}}
    (f : GeneralSpace.Hom G H) (T : TransportGeometry H)
    {x y : G.Point} (γ : G.Path x y) (s : T.State) :
    (pullback f T).transport γ s = T.transport (f.mapPath γ) s := rfl

end TransportGeometry

namespace Recoordination

/-- Every whole-space morphism sends reversible GST recoordination to
reversible recoordination in the target space. -/
def map
    {G : GeneralSpace.{u,v}} {H : GeneralSpace.{u',v'}}
    (f : GeneralSpace.Hom G H)
    {x y : G.Point} (ρ : Recoordination G x y) :
    Recoordination H (f.mapPoint x) (f.mapPoint y) where
  forward := f.mapPath ρ.forward
  backward := f.mapPath ρ.backward
  forward_backward := by
    rw [← f.map_comp, ρ.forward_backward, f.map_id]
  backward_forward := by
    rw [← f.map_comp, ρ.backward_forward, f.map_id]

end Recoordination

/-- A transported realization on a target General Space pulls back to a
synchronized transported realization on every source mapping into it. -/
def TransportedRealization.pullback
    {G : GeneralSpace.{u,v}} {H : GeneralSpace.{u',v'}}
    (f : GeneralSpace.Hom G H)
    (R : TransportedRealization H) : TransportedRealization G where
  realization := R.realization.pullback f
  transport := R.transport.pullback f
  encode := R.encode
  path_naturality := by
    intro x y γ
    exact R.path_naturality (f.mapPath γ)

/-- Naturality survives arbitrary chains of change-of-space plus path
transport. -/
theorem pulledBack_path_naturality
    {G : GeneralSpace.{u,v}} {H : GeneralSpace.{u',v'}}
    (f : GeneralSpace.Hom G H)
    (R : TransportedRealization H)
    {x y : G.Point} (γ : G.Path x y) :
    (R.pullback f).encode ((R.pullback f).realization.realize y) =
      (R.pullback f).transport.transport γ
        ((R.pullback f).encode ((R.pullback f).realization.realize x)) :=
  (R.pullback f).path_naturality γ

#check GeneralSpace.Chart.pullback
#check Realization.pullback
#check TransportGeometry.pullback
#check Recoordination.map
#check TransportedRealization.pullback
#check pulledBack_path_naturality

end GSTGeneralSpace
