import GSTGeneralSpaceMorphisms

/-!
# GENERAL SPACE THEORY — FIBERED COSMOLOGY

A single global state type is not enough for serious geometry.  Tangent spaces,
stalks, local cohomology groups, bundle fibers and local cycle spaces vary with
the base point.

This module therefore adds dependent local families and optional path transport
between their fibers.  Transport is a separate capability: a varying family
does NOT automatically possess a connection/parallel transport.
-/

universe u v w w' u' v'

namespace GSTGeneralSpace

open GSTGeneralSpace.GeneralSpace

/-- A point-dependent family of local state spaces over one General Space. -/
structure LocalFamily (G : GeneralSpace.{u,v}) where
  Fiber : G.Point → Type w

namespace LocalFamily

/-- Pull a local family back through a map of base General Spaces. -/
def pullback
    {G : GeneralSpace.{u,v}} {H : GeneralSpace.{u',v'}}
    (f : GeneralSpace.Hom G H) (F : LocalFamily H) : LocalFamily G where
  Fiber x := F.Fiber (f.mapPoint x)

/-- Fiberwise product of two local families. -/
def prod
    {G : GeneralSpace.{u,v}}
    (F : LocalFamily G) (K : LocalFamily G) : LocalFamily G where
  Fiber x := F.Fiber x × K.Fiber x

/-- A global section of a varying local family. -/
abbrev Section {G : GeneralSpace.{u,v}} (F : LocalFamily G) :=
  ∀ x : G.Point, F.Fiber x

end LocalFamily

/-- A dependent local family equipped with functorial transport along every
GST path.  This is the connection-like structure; it is never inferred merely
from the existence of the fibers. -/
structure FiberedTransport (G : GeneralSpace.{u,v}) extends LocalFamily G where
  transport : {x y : G.Point} → G.Path x y → Fiber x → Fiber y
  transport_id : ∀ (x : G.Point) (s : Fiber x),
    transport (G.idPath x) s = s
  transport_comp : ∀ {x y z : G.Point}
      (α : G.Path x y) (β : G.Path y z) (s : Fiber x),
    transport (G.compPath α β) s = transport β (transport α s)

namespace FiberedTransport

/-- Pull a dependent transport system back through a whole-space map. -/
def pullback
    {G : GeneralSpace.{u,v}} {H : GeneralSpace.{u',v'}}
    (f : GeneralSpace.Hom G H) (F : FiberedTransport H) :
    FiberedTransport G where
  Fiber x := F.Fiber (f.mapPoint x)
  transport := fun γ => F.transport (f.mapPath γ)
  transport_id := by
    intro x s
    rw [f.map_id, F.transport_id]
  transport_comp := by
    intro x y z α β s
    rw [f.map_comp, F.transport_comp]

/-- Product connection/transport on the product of two transported families. -/
def prod
    {G : GeneralSpace.{u,v}}
    (F : FiberedTransport G) (K : FiberedTransport G) :
    FiberedTransport G where
  Fiber x := F.Fiber x × K.Fiber x
  transport := fun γ s =>
    ⟨F.transport γ s.1, K.transport γ s.2⟩
  transport_id := by
    intro x s
    apply Prod.ext
    · exact F.transport_id x s.1
    · exact K.transport_id x s.2
  transport_comp := by
    intro x y z α β s
    apply Prod.ext
    · exact F.transport_comp α β s.1
    · exact K.transport_comp α β s.2

/-- A section is parallel/intrinsic when all path transports carry its value
at the source to its value at the target. -/
def IsParallel
    {G : GeneralSpace.{u,v}}
    (F : FiberedTransport G)
    (s : LocalFamily.Section F.toLocalFamily) : Prop :=
  ∀ {x y : G.Point} (γ : G.Path x y),
    F.transport γ (s x) = s y

/-- Parallelity is preserved by pullback through every map of General Spaces. -/
theorem isParallel_pullback
    {G : GeneralSpace.{u,v}} {H : GeneralSpace.{u',v'}}
    (f : GeneralSpace.Hom G H)
    (F : FiberedTransport H)
    (s : LocalFamily.Section F.toLocalFamily)
    (hs : F.IsParallel s) :
    (F.pullback f).IsParallel (fun x => s (f.mapPoint x)) := by
  intro x y γ
  exact hs (f.mapPath γ)

end FiberedTransport

/-- A natural map between two dependent transported cosmologies over the same
base. -/
structure FiberedHom
    {G : GeneralSpace.{u,v}}
    (F : FiberedTransport.{u,v,w} G)
    (K : FiberedTransport.{u,v,w'} G) where
  map : ∀ x : G.Point, F.Fiber x → K.Fiber x
  naturality : ∀ {x y : G.Point} (γ : G.Path x y) (s : F.Fiber x),
    map y (F.transport γ s) = K.transport γ (map x s)

namespace FiberedHom

/-- Identity natural map. -/
def id
    {G : GeneralSpace.{u,v}}
    (F : FiberedTransport G) : FiberedHom F F where
  map := fun _ s => s
  naturality := by intro x y γ s; rfl

/-- Composition of natural maps of fibered cosmologies. -/
def comp
    {G : GeneralSpace.{u,v}}
    {F : FiberedTransport.{u,v,w} G}
    {K : FiberedTransport.{u,v,w'} G}
    {L : FiberedTransport G}
    (a : FiberedHom F K) (b : FiberedHom K L) : FiberedHom F L where
  map := fun x s => b.map x (a.map x s)
  naturality := by
    intro x y γ s
    rw [a.naturality, b.naturality]

end FiberedHom

#check LocalFamily
#check LocalFamily.pullback
#check FiberedTransport
#check FiberedTransport.pullback
#check FiberedTransport.prod
#check FiberedTransport.IsParallel
#check FiberedTransport.isParallel_pullback
#check FiberedHom

end GSTGeneralSpace
