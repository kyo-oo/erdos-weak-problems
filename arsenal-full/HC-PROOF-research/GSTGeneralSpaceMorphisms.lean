import GSTGeneralSpace

/-!
# GENERAL SPACE THEORY — MORPHISMS OF WHOLE SPACES

The ontological root already has arbitrary points and typed composable paths.
This file adds the next level of control: maps between entire General Spaces.

A morphism transports points and paths and preserves identity/composition.
Nothing about coordinates, topology, dimension, metrics, manifolds, schemes or
arithmetic is assumed.
-/

universe u v u' v' u'' v''

namespace GSTGeneralSpace

namespace GeneralSpace

/-- A structure-preserving map of complete General Spaces. -/
structure Hom (G : GeneralSpace.{u,v}) (H : GeneralSpace.{u',v'}) where
  mapPoint : G.Point → H.Point
  mapPath : {x y : G.Point} → G.Path x y →
    H.Path (mapPoint x) (mapPoint y)
  map_id : ∀ x : G.Point,
    mapPath (G.idPath x) = H.idPath (mapPoint x)
  map_comp : ∀ {x y z : G.Point}
      (α : G.Path x y) (β : G.Path y z),
    mapPath (G.compPath α β) =
      H.compPath (mapPath α) (mapPath β)

namespace Hom

/-- Identity map of a General Space. -/
def id (G : GeneralSpace.{u,v}) : Hom G G where
  mapPoint := fun x => x
  mapPath := fun γ => γ
  map_id := by intro x; rfl
  map_comp := by intro x y z α β; rfl

/-- Composition of whole-space maps. -/
def comp
    {G : GeneralSpace.{u,v}}
    {H : GeneralSpace.{u',v'}}
    {K : GeneralSpace.{u'',v''}}
    (f : Hom G H) (g : Hom H K) : Hom G K where
  mapPoint := g.mapPoint ∘ f.mapPoint
  mapPath := fun γ => g.mapPath (f.mapPath γ)
  map_id := by
    intro x
    rw [f.map_id, g.map_id]
    rfl
  map_comp := by
    intro x y z α β
    rw [f.map_comp, g.map_comp]

@[simp]
theorem id_mapPoint (G : GeneralSpace.{u,v}) (x : G.Point) :
    (id G).mapPoint x = x := rfl

@[simp]
theorem comp_mapPoint
    {G : GeneralSpace.{u,v}}
    {H : GeneralSpace.{u',v'}}
    {K : GeneralSpace.{u'',v''}}
    (f : Hom G H) (g : Hom H K) (x : G.Point) :
    (comp f g).mapPoint x = g.mapPoint (f.mapPoint x) := rfl

end Hom

/-- Product of two General Spaces.  Product paths are simultaneous paths in
both factors. -/
def prod
    (G : GeneralSpace.{u,v})
    (H : GeneralSpace.{u',v'}) :
    GeneralSpace.{max u u', max (max 1 v) v'} where
  Point := G.Point × H.Point
  Path x y := @PSigma.{v, v'} (G.Path x.1 y.1) (fun _ => H.Path x.2 y.2)
  idPath := fun x => ⟨G.idPath x.1, H.idPath x.2⟩
  compPath := fun α β =>
    ⟨G.compPath α.1 β.1, H.compPath α.2 β.2⟩
  comp_id_left := by
    intro x y γ
    show (⟨G.compPath (G.idPath x.1) γ.1, H.compPath (H.idPath x.2) γ.2⟩ :
      @PSigma.{v, v'} (G.Path x.1 y.1) (fun _ => H.Path x.2 y.2)) = γ
    rw [G.comp_id_left, H.comp_id_left]
  comp_id_right := by
    intro x y γ
    show (⟨G.compPath γ.1 (G.idPath y.1), H.compPath γ.2 (H.idPath y.2)⟩ :
      @PSigma.{v, v'} (G.Path x.1 y.1) (fun _ => H.Path x.2 y.2)) = γ
    rw [G.comp_id_right, H.comp_id_right]
  comp_assoc := by
    intro w x y z α β γ
    show (⟨G.compPath (G.compPath α.1 β.1) γ.1,
      H.compPath (H.compPath α.2 β.2) γ.2⟩ :
      @PSigma.{v, v'} (G.Path w.1 z.1) (fun _ => H.Path w.2 z.2)) =
      (⟨G.compPath α.1 (G.compPath β.1 γ.1),
        H.compPath α.2 (H.compPath β.2 γ.2)⟩ :
      @PSigma.{v, v'} (G.Path w.1 z.1) (fun _ => H.Path w.2 z.2))
    rw [G.comp_assoc, H.comp_assoc]

/-- First projection is a General-Space morphism. -/
def fstHom
    (G : GeneralSpace.{u,v})
    (H : GeneralSpace.{u',v'}) : Hom (prod G H) G where
  mapPoint := Prod.fst
  mapPath := fun γ => γ.1
  map_id := by intro x; rfl
  map_comp := by intro x y z α β; rfl

/-- Second projection is a General-Space morphism. -/
def sndHom
    (G : GeneralSpace.{u,v})
    (H : GeneralSpace.{u',v'}) : Hom (prod G H) H where
  mapPoint := Prod.snd
  mapPath := fun γ => γ.2
  map_id := by intro x; rfl
  map_comp := by intro x y z α β; rfl

/-- Pair two maps with common source to obtain a map into the product. -/
def pairHom
    {G : GeneralSpace.{u,v}}
    {H : GeneralSpace.{u',v'}}
    {K : GeneralSpace.{u'',v''}}
    (f : Hom G H) (g : Hom G K) : Hom G (prod H K) where
  mapPoint := fun x => ⟨f.mapPoint x, g.mapPoint x⟩
  mapPath := fun γ => ⟨f.mapPath γ, g.mapPath γ⟩
  map_id := by
    intro x
    show (⟨f.mapPath (G.idPath x), g.mapPath (G.idPath x)⟩ :
      @PSigma.{v', v''} (H.Path (f.mapPoint x) (f.mapPoint x))
        (fun _ => K.Path (g.mapPoint x) (g.mapPoint x))) =
      (⟨H.idPath (f.mapPoint x), K.idPath (g.mapPoint x)⟩ :
      @PSigma.{v', v''} (H.Path (f.mapPoint x) (f.mapPoint x))
        (fun _ => K.Path (g.mapPoint x) (g.mapPoint x)))
    rw [f.map_id, g.map_id]
  map_comp := by
    intro x y z α β
    show (⟨f.mapPath (G.compPath α β), g.mapPath (G.compPath α β)⟩ :
      @PSigma.{v', v''} (H.Path (f.mapPoint x) (f.mapPoint z))
        (fun _ => K.Path (g.mapPoint x) (g.mapPoint z))) =
      (⟨H.compPath (f.mapPath α) (f.mapPath β),
        K.compPath (g.mapPath α) (g.mapPath β)⟩ :
      @PSigma.{v', v''} (H.Path (f.mapPoint x) (f.mapPoint z))
        (fun _ => K.Path (g.mapPoint x) (g.mapPoint z)))
    rw [f.map_comp, g.map_comp]

/-- Every arbitrary function is a General-Space morphism between discrete
General Spaces.  Thus the abstract category contains ordinary types/functions
as a fully unconstrained sector. -/
def discreteHom {α : Type u} {β : Type u'} (f : α → β) :
    Hom (discrete α) (discrete β) where
  mapPoint := f
  mapPath := by
    intro x y h
    cases h
    rfl
  map_id := by intro x; rfl
  map_comp := by intro x y z α β; cases α; cases β; rfl

#check Hom
#check Hom.id
#check Hom.comp
#check prod
#check fstHom
#check sndHom
#check pairHom
#check discreteHom

end GeneralSpace

end GSTGeneralSpace
