import GSTGraphV2OmniversalCore

/-!
# GST Graph V2 — causal components and dimension-independent worlds

A General Space need not be acyclic.  Two distinct states can have
oppositely directed causal histories without creating a contradiction in
classical logic.  Their *causal component* records mutual reachability.

Mutual reachability is an equivalence relation.  The quotient has a
canonical antisymmetric reachability order, even if the original cosmos
contains feedback loops.  Genuine GST event-preserving folds induce
well-defined, reachability-monotone maps on these components.

This makes an exact, coordinate-free distinction between:
* reversible causal feedback **inside** a component;
* genuine directional causal growth **between** components.

An independent infinite successor example shows that no finite horizon
or maximum dimension is imposed by the core ontology.  The example is a
realization, not an assertion that every GST graph is infinite.
-/

universe u v

namespace GSTGraphV2CausalComponents

open GSTGraphV2OmniversalCore

variable (G : OmniversalGraph.{u,v})

/-- Mutual causal reachability; this permits feedback but does not assert
that two distinct source nodes are equal. -/
def MutualReachability (x y : G.Node) : Prop :=
  OmniversalGraph.Reachable G x y ∧ OmniversalGraph.Reachable G y x

theorem mutual_refl (x : G.Node) : MutualReachability G x x :=
  ⟨OmniversalGraph.reachable_refl G x,
   OmniversalGraph.reachable_refl G x⟩

theorem mutual_symm {x y : G.Node} (h : MutualReachability G x y) :
    MutualReachability G y x :=
  ⟨h.2, h.1⟩

theorem mutual_trans {x y z : G.Node}
    (hxy : MutualReachability G x y)
    (hyz : MutualReachability G y z) :
    MutualReachability G x z :=
  ⟨OmniversalGraph.reachable_trans G hxy.1 hyz.1,
   OmniversalGraph.reachable_trans G hyz.2 hxy.2⟩

/-- Strongly connected causal worlds, without a metric or a dimension. -/
def causalSetoid : Setoid G.Node where
  r := MutualReachability G
  iseqv := ⟨mutual_refl G, mutual_symm G, mutual_trans G⟩

/-- A world is one strongly connected causal component, not a chosen chart. -/
abbrev CausalWorld := Quotient (causalSetoid G)

/-- Directed reachability between causal worlds.  The witnesses may be
chosen arbitrarily within each component: the answer is unchanged. -/
def WorldReachable (a b : CausalWorld G) : Prop :=
  Quotient.liftOn₂ a b
    (fun x y => OmniversalGraph.Reachable G x y)
    (by
      intro x x' y y' hxx' hyy'
      apply propext
      constructor
      · intro hxy
        exact OmniversalGraph.reachable_trans G hxx'.2
          (OmniversalGraph.reachable_trans G hxy hyy'.1)
      · intro hx'y'
        exact OmniversalGraph.reachable_trans G hxx'.1
          (OmniversalGraph.reachable_trans G hx'y' hyy'.2))

theorem world_refl (a : CausalWorld G) : WorldReachable G a a := by
  induction a using Quotient.inductionOn with
  | h x =>
      exact OmniversalGraph.reachable_refl G x

theorem world_trans {a b c : CausalWorld G}
    (hab : WorldReachable G a b)
    (hbc : WorldReachable G b c) :
    WorldReachable G a c := by
  induction a using Quotient.inductionOn with
  | h x =>
    induction b using Quotient.inductionOn with
    | h y =>
      induction c using Quotient.inductionOn with
      | h z =>
        exact OmniversalGraph.reachable_trans G hab hbc

/-- The quotient removes feedback cycles: mutual world reachability is
genuine world equality. -/
theorem world_antisymm {a b : CausalWorld G}
    (hab : WorldReachable G a b)
    (hba : WorldReachable G b a) : a = b := by
  induction a using Quotient.inductionOn with
  | h x =>
    induction b using Quotient.inductionOn with
    | h y =>
      apply Quotient.sound
      exact ⟨hab, hba⟩

/-- The directional order on components exists even when the point-level
event graph is cyclic. -/
noncomputable instance worldPartialOrder : PartialOrder (CausalWorld G) where
  le := WorldReachable G
  le_refl := world_refl G
  le_trans := fun _ _ _ => world_trans G
  le_antisymm := fun _ _ => world_antisymm G

/-- An actual event-preserving fold descends to causal worlds. -/
def worldMap (F : OmniversalGraph.EventHom G G) :
    CausalWorld G → CausalWorld G :=
  fun a =>
    Quotient.liftOn a
      (fun x => (Quotient.mk (causalSetoid G) (F.toFun x) : CausalWorld G))
      (by
        intro x y h
        apply Quotient.sound
        exact ⟨OmniversalGraph.EventHom.reachable_map G F h.1,
               OmniversalGraph.EventHom.reachable_map G F h.2⟩)

/-- A GST causal fold cannot reverse the induced component order when
the fold transports every primitive event. -/
theorem worldMap_monotone (F : OmniversalGraph.EventHom G G)
    {a b : CausalWorld G} (hab : WorldReachable G a b) :
    WorldReachable G (worldMap G F a) (worldMap G F b) := by
  induction a using Quotient.inductionOn with
  | h x =>
    induction b using Quotient.inductionOn with
    | h y =>
      exact OmniversalGraph.EventHom.reachable_map G F hab

/-- An infinite successor realization, independent of geometry or radix. -/
def infiniteSuccessorCosmos : OmniversalGraph where
  Node := Nat
  sector := fun _ => .null
  Event := fun x y => y = x + 1

theorem infiniteSuccessor_event (n : Nat) :
    infiniteSuccessorCosmos.Event n (n + 1) := rfl

theorem infiniteSuccessor_reachable (n k : Nat) :
    OmniversalGraph.Reachable infiniteSuccessorCosmos n (n + k) := by
  induction k with
  | zero =>
      simpa using OmniversalGraph.reachable_refl infiniteSuccessorCosmos n
  | succ k ih =>
      have step : infiniteSuccessorCosmos.Event (n + k) (n + k + 1) := rfl
      have reach := OmniversalGraph.reachable_trans infiniteSuccessorCosmos ih
        (OmniversalGraph.reachable_of_event infiniteSuccessorCosmos step)
      simpa only [Nat.add_succ] using reach

theorem infiniteSuccessor_no_terminal_node (n : Nat) :
    ∃ m : Nat, n < m ∧
      OmniversalGraph.Reachable infiniteSuccessorCosmos n m := by
  refine ⟨n + 1, Nat.lt_succ_self n, ?_⟩
  exact OmniversalGraph.reachable_of_event infiniteSuccessorCosmos
    (infiniteSuccessor_event n)

/-- A consistent example with two distinct mutually reachable states. -/
def reversibleTwoStateCosmos : OmniversalGraph where
  Node := Bool
  sector := fun _ => .null
  Event := fun x y => x ≠ y

theorem reversibleTwoState_mutual :
    MutualReachability reversibleTwoStateCosmos true false := by
  constructor
  · exact OmniversalGraph.reachable_of_event reversibleTwoStateCosmos (by change (true : Bool) ≠ false; decide)
  · exact OmniversalGraph.reachable_of_event reversibleTwoStateCosmos (by change (false : Bool) ≠ true; decide)

/-- Distinct states can belong to one causal world; this is not a proof of
an inconsistent proposition such as True = False. -/
theorem reversibleTwoState_sameWorld :
    (Quotient.mk (causalSetoid reversibleTwoStateCosmos) true :
      CausalWorld reversibleTwoStateCosmos) =
    (Quotient.mk (causalSetoid reversibleTwoStateCosmos) false :
      CausalWorld reversibleTwoStateCosmos) := by
  apply Quotient.sound
  exact reversibleTwoState_mutual

theorem reversibleTwoState_notAcyclic :
    ¬ OmniversalGraph.CausallyAcyclic reversibleTwoStateCosmos := by
  intro h
  have hEq : (true : Bool) = false :=
    h reversibleTwoState_mutual.1 reversibleTwoState_mutual.2
  cases hEq

#check causalSetoid
#check world_refl
#check world_trans
#check world_antisymm
#check worldMap_monotone
#check infiniteSuccessor_no_terminal_node
#check reversibleTwoState_sameWorld
#print axioms world_antisymm
#print axioms worldMap_monotone

end GSTGraphV2CausalComponents
