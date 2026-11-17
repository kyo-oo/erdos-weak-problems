import GSTGeneralSpace

universe u v w

namespace GSTGeneralSpace

/-- A state system transported functorially along General Space paths. -/
structure TransportGeometry (G : GeneralSpace) where
  State : Type w
  transport : {x y : G.Point} → G.Path x y → State → State
  transport_id : ∀ (x : G.Point) (s : State), transport (G.idPath x) s = s
  transport_comp : ∀ {x y z : G.Point}
      (α : G.Path x y) (β : G.Path y z) (s : State),
    transport (G.compPath α β) s = transport β (transport α s)

namespace TransportGeometry

variable {G : GeneralSpace} (T : TransportGeometry G)

/-- Transport along three composable paths is independent of parenthesization. -/
theorem transport_assoc {w x y z : G.Point}
    (α : G.Path w x) (β : G.Path x y) (γ : G.Path y z) (s : T.State) :
    T.transport (G.compPath (G.compPath α β) γ) s =
      T.transport γ (T.transport β (T.transport α s)) := by
  rw [T.transport_comp, T.transport_comp]

/-- An invariant observable is unchanged by every admissible path transport. -/
structure InvariantObservable (A : Type u) where
  eval : T.State → A
  invariant : ∀ {x y : G.Point} (γ : G.Path x y) (s : T.State),
    eval (T.transport γ s) = eval s

/-- An invariant predicate is preserved exactly by every admissible path. -/
structure InvariantPredicate where
  pred : T.State → Prop
  invariant : ∀ {x y : G.Point} (γ : G.Path x y) (s : T.State),
    pred (T.transport γ s) ↔ pred s

end TransportGeometry

#check TransportGeometry
#check TransportGeometry.InvariantObservable
#check TransportGeometry.InvariantPredicate

end GSTGeneralSpace
