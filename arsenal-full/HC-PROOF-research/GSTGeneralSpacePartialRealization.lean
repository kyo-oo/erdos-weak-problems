import GSTGeneralSpaceRealization

universe u v w

namespace GSTGeneralSpace

/-- A realization defined only on a geometric locus of General Space.
This is the correct abstraction for algebraic cycles inside a larger Betti/Hodge
state space: algebraicity is a domain predicate, not a totality axiom. -/
structure PartialRealization (G : GeneralSpace) where
  Domain : G.Point → Prop
  State : Type w
  realize : ∀ x : G.Point, Domain x → State

namespace PartialRealization

variable {G : GeneralSpace}

/-- A path preserves a partial realization domain. -/
def PathClosed (R : PartialRealization G) : Prop :=
  ∀ {x y : G.Point}, G.Path x y → R.Domain x → R.Domain y

/-- Restrict a total realization to any predicate-defined locus. -/
def ofTotal (R : Realization G) (P : G.Point → Prop) : PartialRealization G where
  Domain := P
  State := R.State
  realize := fun x _ => R.realize x

/-- If a partial realization is path-closed, every reachable point from a live
source remains in its geometric locus. -/
theorem domain_of_path
    (R : PartialRealization G) (hclosed : R.PathClosed)
    {x y : G.Point} (γ : G.Path x y) (hx : R.Domain x) :
    R.Domain y :=
  hclosed γ hx

end PartialRealization

#check PartialRealization
#check PartialRealization.PathClosed
#check PartialRealization.domain_of_path

end GSTGeneralSpace
