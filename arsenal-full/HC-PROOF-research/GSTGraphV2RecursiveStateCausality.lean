import GSTGraphV2SelfExpandingCosmology

/-!
# GST GRAPH V2 — RECURSIVE STATE CAUSALITY

`GSTGraphV2SelfExpandingCosmology` lets events generate new worlds.  The next
layer lets mathematical objects move inside and between those worlds.

A packed state remembers both its world and its world-specific internal state.
Primitive steps are either local events inside one world or transports between
two worlds.  Their transitive closure therefore describes an object whose
ambient geometry may itself change while the object evolves.

This is the intended setting for constructions such as

scheme point → cycle → cycle class → Hodge state,

where the intermediate objects do not live in one fixed carrier.
-/

universe u v w z

namespace GSTGraphV2RecursiveStateCausality

open GSTGraphV2SelfExpandingCosmology

variable (C : SelfExpandingCosmos.{u,v,w,z})

/-- A state together with the world in which that state lives. -/
abbrev PackedState := Sigma C.State

/-- One primitive object-level causal step. -/
inductive StateStep : PackedState C → PackedState C → Type (max (max u v) z)
  | stepLocal
      {W : C.World} {x y : C.State W}
      (e : C.LocalEvent x y) :
      StateStep ⟨W,x⟩ ⟨W,y⟩
  | transport
      {A B : C.World} {x : C.State A} {y : C.State B}
      (e : C.Transport x y) :
      StateStep ⟨A,x⟩ ⟨B,y⟩

/-- A finite composable history of state evolution through possibly different
worlds.  There is no fixed bound on path length. -/
inductive StatePath : PackedState C → PackedState C → Type (max (max u v) z)
  | nil (x : PackedState C) : StatePath x x
  | cons {x y z : PackedState C}
      (e : StateStep C x y)
      (tail : StatePath y z) :
      StatePath x z

namespace StatePath

/-- Concatenate object histories. -/
def comp {x y z : PackedState C} :
    StatePath C x y → StatePath C y z → StatePath C x z
  | .nil _, q => q
  | .cons e p, q => .cons e (comp p q)

@[simp] theorem comp_nil
    {x y : PackedState C} (p : StatePath C x y) :
    comp C p (.nil y) = p := by
  induction p with
  | nil => rfl
  | cons e tail ih => simp [comp, ih]

end StatePath

/-- State reachability through arbitrary finite compositions of local and
cross-world transitions. -/
def StateReachable (x y : PackedState C) : Prop :=
  Nonempty (StatePath C x y)

@[simp] theorem stateReachable_refl (x : PackedState C) :
    StateReachable C x x :=
  ⟨StatePath.nil x⟩

/-- Every primitive state step gives reachability. -/
theorem stateReachable_of_step
    {x y : PackedState C} (e : StateStep C x y) :
    StateReachable C x y :=
  ⟨StatePath.cons e (StatePath.nil y)⟩

/-- State reachability composes. -/
theorem stateReachable_trans
    {x y z : PackedState C}
    (hxy : StateReachable C x y)
    (hyz : StateReachable C y z) :
    StateReachable C x z := by
  rcases hxy with ⟨p⟩
  rcases hyz with ⟨q⟩
  exact ⟨StatePath.comp C p q⟩

/-- Least reachability closure of a family of object-level seed states. -/
def StateClosure (Seed : PackedState C → Prop) (y : PackedState C) : Prop :=
  ∃ x : PackedState C, Seed x ∧ StateReachable C x y

/-- A semantic property is stable when every local event and cross-world
transport preserves it. -/
def StateStable (P : PackedState C → Prop) : Prop :=
  ∀ {x y : PackedState C}, StateStep C x y → P x → P y

/-- Stable semantics propagate through arbitrary object histories. -/
theorem StatePath.preserves
    {P : PackedState C → Prop}
    (hP : StateStable C P)
    {x y : PackedState C}
    (p : StatePath C x y) :
    P x → P y := by
  induction p with
  | nil => exact fun hx => hx
  | cons e tail ih =>
      intro hx
      exact ih (hP e hx)

/-- Object-level semantic closure principle inside the recursively changing
cosmos. -/
theorem stateClosure_sound
    {Seed P : PackedState C → Prop}
    (hSeed : ∀ x, Seed x → P x)
    (hStable : StateStable C P) :
    ∀ x, StateClosure C Seed x → P x := by
  intro x hx
  rcases hx with ⟨s, hs, ⟨p⟩⟩
  exact StatePath.preserves C hStable p (hSeed s hs)

/-- The world supporting a packed state. -/
def supportWorld (x : PackedState C) : C.World := x.1

/-- A state lies in the generated cosmos when its supporting world does. -/
def InGeneratedWorld (x : PackedState C) : Prop :=
  C.Generated (supportWorld C x)

/-- A compatibility condition saying that cross-world transport never jumps
from the generated cosmos into an unrelated external world. -/
def TransportRespectsGeneration : Prop :=
  ∀ {A B : C.World} {x : C.State A} {y : C.State B},
    C.Transport x y →
    C.Generated A →
    C.Generated B

/-- Under generation-respecting transport, every primitive state step preserves
membership in the recursively generated universe of worlds. -/
theorem stateStep_preserves_generatedWorld
    (hTransport : TransportRespectsGeneration C) :
    StateStable C (InGeneratedWorld C) := by
  intro x y e hx
  cases e with
  | stepLocal e =>
      exact hx
  | transport e =>
      exact hTransport e hx

/-- Therefore any state causally generated from a state in a generated world
continues to live somewhere inside the self-expanding GST cosmos. -/
theorem stateClosure_stays_in_generatedWorld
    (hTransport : TransportRespectsGeneration C)
    {Seed : PackedState C → Prop}
    (hSeed : ∀ x, Seed x → InGeneratedWorld C x) :
    ∀ x, StateClosure C Seed x → InGeneratedWorld C x := by
  exact stateClosure_sound C hSeed
    (stateStep_preserves_generatedWorld C hTransport)

#check PackedState
#check StateStep
#check StatePath
#check StateReachable
#check StateClosure
#check StateStable
#check stateClosure_sound
#check TransportRespectsGeneration
#check stateClosure_stays_in_generatedWorld

end GSTGraphV2RecursiveStateCausality
