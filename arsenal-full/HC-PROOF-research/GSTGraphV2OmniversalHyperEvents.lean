import GSTGraphV2OmniversalCore

/-!
# GST GRAPH V2 — OMNIVERSAL HIGHER-ARITY EVENT CLOSURE

Ordinary directed edges are not enough for geometry.  Cup products,
intersections, fiber products, tensor operations, finite linear synthesis, and
many correspondence constructions consume several inputs simultaneously.

This file therefore extends the carrier-agnostic three-sector graph by typed
higher-arity rules.  The arity itself is an arbitrary type: no finite bound,
coordinate dimension, or numerical shape is built into the ontology.

A generated state may arise from a seed, from one ordinary causal event, or
from a higher-arity event whose every premise has already been generated.
This is the closure object intended for number theory, manifold geometry,
scheme geometry, Hodge constructions, and future cosmological realizations.
-/

universe u v w p

namespace GSTGraphV2OmniversalHyperEvents

open GSTGraphV2OmniversalCore

/-- Higher-arity event system over an omniversal three-sector graph.
Each rule chooses its own premise type, so different rules may have completely
different and unbounded arities. -/
structure HyperEventSystem (G : OmniversalGraph.{u,v}) where
  Rule : Type w
  Premise : Rule → Type p
  input : (r : Rule) → Premise r → G.Node
  output : Rule → G.Node

namespace HyperEventSystem

variable {G : OmniversalGraph.{u,v}}
variable (H : HyperEventSystem.{u,v,w,p} G)

/-- Closure generated jointly by primitive unary events and arbitrary
higher-arity events. -/
inductive Generated (Seed : G.Node → Prop) : G.Node → Prop
  | seed {x : G.Node} : Seed x → Generated Seed x
  | unary {x y : G.Node} :
      Generated Seed x → G.Event x y → Generated Seed y
  | hyper (r : H.Rule) :
      (∀ i : H.Premise r, Generated Seed (H.input r i)) →
        Generated Seed (H.output r)

/-- A semantic predicate is stable under every unary event and every
higher-arity rule. -/
def SemanticallyStable (P : G.Node → Prop) : Prop :=
  OmniversalGraph.EventStable G P ∧
    ∀ r : H.Rule,
      (∀ i : H.Premise r, P (H.input r i)) →
        P (H.output r)

/-- **HIGHER-EVENT SEMANTIC CLOSURE.**
Any property true on the seeds and preserved by every unary and higher-arity
event is true on every state generated anywhere in the unbounded closure. -/
theorem generated_sound
    {Seed P : G.Node → Prop}
    (hSeed : ∀ x, Seed x → P x)
    (hStable : SemanticallyStable H P) :
    ∀ {x : G.Node}, Generated H Seed x → P x := by
  intro x hx
  induction hx with
  | seed hs =>
      exact hSeed _ hs
  | unary hgen e ih =>
      exact hStable.1 e ih
  | hyper r hgen ih =>
      exact hStable.2 r ih

/-- Every seed is generated. -/
theorem seed_generated
    (Seed : G.Node → Prop) {x : G.Node} (hx : Seed x) :
    Generated H Seed x :=
  Generated.seed hx

/-- One primitive event extends the generated universe. -/
theorem unary_generated
    (Seed : G.Node → Prop)
    {x y : G.Node}
    (hx : Generated H Seed x)
    (e : G.Event x y) :
    Generated H Seed y :=
  Generated.unary hx e

/-- One higher-arity rule extends the generated universe as soon as all of its
premises have already entered the closure. -/
theorem hyper_generated
    (Seed : G.Node → Prop)
    (r : H.Rule)
    (h : ∀ i : H.Premise r, Generated H Seed (H.input r i)) :
    Generated H Seed (H.output r) :=
  Generated.hyper r h

/-- Monotonicity of higher-event generation in the seed family. -/
theorem generated_mono
    {Seed₁ Seed₂ : G.Node → Prop}
    (hSeed : ∀ x, Seed₁ x → Seed₂ x) :
    ∀ {x : G.Node}, Generated H Seed₁ x → Generated H Seed₂ x := by
  intro x hx
  induction hx with
  | seed hs =>
      exact Generated.seed (hSeed _ hs)
  | unary hgen e ih =>
      exact Generated.unary ih e
  | hyper r hgen ih =>
      exact Generated.hyper r ih

/-- The higher-event closure itself is stable under all primitive event forms. -/
theorem generated_semanticallyStable (Seed : G.Node → Prop) :
    SemanticallyStable H (Generated H Seed) := by
  constructor
  · intro x y e hx
    exact Generated.unary hx e
  · intro r h
    exact Generated.hyper r h

/-- Re-closing the generated predicate cannot produce a semantic escape:
anything generated from already-generated seeds remains generated from the
original seeds. -/
theorem generated_of_generated_seed
    (Seed : G.Node → Prop) :
    ∀ {x : G.Node},
      Generated H (Generated H Seed) x → Generated H Seed x :=
  generated_sound H (fun _ hx => hx)
    (generated_semanticallyStable H Seed)

/-- Higher-arity closure crown. -/
theorem hyper_event_closure_crown
    (Seed : G.Node → Prop) :
    (∀ x, Seed x → Generated H Seed x)
      ∧ SemanticallyStable H (Generated H Seed)
      ∧ (∀ x, Generated H (Generated H Seed) x → Generated H Seed x) := by
  exact ⟨
    fun _ hx => seed_generated H Seed hx,
    generated_semanticallyStable H Seed,
    fun _ hx => generated_of_generated_seed H Seed hx⟩

#check HyperEventSystem
#check HyperEventSystem.Generated
#check HyperEventSystem.SemanticallyStable
#check HyperEventSystem.generated_sound
#check HyperEventSystem.generated_mono
#check HyperEventSystem.generated_semanticallyStable
#check HyperEventSystem.hyper_event_closure_crown

end HyperEventSystem
end GSTGraphV2OmniversalHyperEvents
