import GSTGeneralSpaceMorphisms
import Mathlib.Topology.Path

/-!
# GENERAL SPACE THEORY — TOPOLOGICAL REALIZATION

Every topological space enters GST without becoming the definition of GST.
The path witness is *existence* of a genuine Mathlib continuous path.

This choice is deliberate.  Raw parametrized path concatenation is naturally
associative/unital only up to reparametrization.  Propositional path
reachability keeps the genuine continuous path content while making the
General-Space categorical laws strict by proof irrelevance.
-/

universe u u'

namespace GSTGeneralSpace

open GSTGeneralSpace.GeneralSpace

/-- Genuine continuous-path reachability in an arbitrary topological space. -/
def TopologicalReachability
    {X : Type u} [TopologicalSpace X] (x y : X) : Prop :=
  Nonempty (Path x y)

/-- Every topological space canonically determines a General Space. -/
def topologicalGeneralSpace
    (X : Type u) [TopologicalSpace X] : GeneralSpace where
  Point := X
  Path := TopologicalReachability
  idPath := fun x => ⟨Path.refl x⟩
  compPath := by
    intro x y z hxy hyz
    rcases hxy with ⟨γ⟩
    rcases hyz with ⟨δ⟩
    exact ⟨γ.trans δ⟩
  comp_id_left := by
    intros
    apply Subsingleton.elim
  comp_id_right := by
    intros
    apply Subsingleton.elim
  comp_assoc := by
    intros
    apply Subsingleton.elim

/-- A continuous map acts functorially on the corresponding General Spaces. -/
def continuousHom
    {X : Type u} {Y : Type u'}
    [TopologicalSpace X] [TopologicalSpace Y]
    (f : X → Y) (hf : Continuous f) :
    GeneralSpace.Hom (topologicalGeneralSpace X) (topologicalGeneralSpace Y) where
  mapPoint := f
  mapPath := by
    intro x y h
    rcases h with ⟨γ⟩
    exact ⟨γ.map hf⟩
  map_id := by
    intro x
    apply Subsingleton.elim
  map_comp := by
    intro x y z α β
    apply Subsingleton.elim

/-- Continuous maps preserve GST topological reachability. -/
theorem topologicalReachability_map
    {X : Type u} {Y : Type u'}
    [TopologicalSpace X] [TopologicalSpace Y]
    (f : X → Y) (hf : Continuous f)
    {x y : X} :
    TopologicalReachability x y →
      TopologicalReachability (f x) (f y) := by
  intro h
  exact (continuousHom f hf).mapPath h

/-- A homeomorphism preserves and reflects the full topological GST path
relation.  Recoordination by homeomorphism therefore changes presentation,
not intrinsic reachability. -/
theorem homeomorph_reachability_iff
    {X : Type u} {Y : Type u'}
    [TopologicalSpace X] [TopologicalSpace Y]
    (e : X ≃ₜ Y) (x y : X) :
    TopologicalReachability x y ↔
      TopologicalReachability (e x) (e y) := by
  constructor
  · exact topologicalReachability_map e e.continuous
  · intro h
    have h' := topologicalReachability_map e.symm e.symm.continuous h
    simpa using h'

/-- The forward General-Space map induced by a homeomorphism. -/
def homeomorphForward
    {X : Type u} {Y : Type u'}
    [TopologicalSpace X] [TopologicalSpace Y]
    (e : X ≃ₜ Y) :
    GeneralSpace.Hom (topologicalGeneralSpace X) (topologicalGeneralSpace Y) :=
  continuousHom e e.continuous

/-- The inverse General-Space map induced by a homeomorphism. -/
def homeomorphBackward
    {X : Type u} {Y : Type u'}
    [TopologicalSpace X] [TopologicalSpace Y]
    (e : X ≃ₜ Y) :
    GeneralSpace.Hom (topologicalGeneralSpace Y) (topologicalGeneralSpace X) :=
  continuousHom e.symm e.symm.continuous

/-- The identity observation chart on an arbitrary topological realization. -/
def topologicalCarrierChart
    (X : Type u) [TopologicalSpace X] :
    GeneralSpace.Chart (topologicalGeneralSpace X) where
  Coord := X
  observe := id

@[simp]
theorem topologicalCarrierChart_observe
    {X : Type u} [TopologicalSpace X] (x : X) :
    (topologicalCarrierChart X).observe x = x := rfl

#check TopologicalReachability
#check topologicalGeneralSpace
#check continuousHom
#check topologicalReachability_map
#check homeomorph_reachability_iff
#check homeomorphForward
#check homeomorphBackward

end GSTGeneralSpace
