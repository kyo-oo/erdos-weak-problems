import GSTGeneralSpaceTransport

universe u v w

namespace GSTGeneralSpace

/-- A reversible General Space path: two coordinate presentations of one state. -/
structure Recoordination (G : GeneralSpace) (x y : G.Point) where
  forward : G.Path x y
  backward : G.Path y x
  forward_backward : G.compPath forward backward = G.idPath x
  backward_forward : G.compPath backward forward = G.idPath y

namespace Recoordination

variable {G : GeneralSpace}

/-- Identity recoordination. -/
def refl (x : G.Point) : Recoordination G x x where
  forward := G.idPath x
  backward := G.idPath x
  forward_backward := G.comp_id_left (G.idPath x)
  backward_forward := G.comp_id_left (G.idPath x)

/-- Reverse a recoordination. -/
def symm {x y : G.Point} (ρ : Recoordination G x y) : Recoordination G y x where
  forward := ρ.backward
  backward := ρ.forward
  forward_backward := ρ.backward_forward
  backward_forward := ρ.forward_backward

/-- Compose recoordination witnesses. -/
def trans {x y z : G.Point}
    (ρ : Recoordination G x y) (σ : Recoordination G y z) :
    Recoordination G x z where
  forward := G.compPath ρ.forward σ.forward
  backward := G.compPath σ.backward ρ.backward
  forward_backward := by
    rw [G.comp_assoc]
    rw [← G.comp_assoc σ.forward σ.backward ρ.backward]
    rw [σ.forward_backward]
    rw [G.comp_id_left]
    exact ρ.forward_backward
  backward_forward := by
    rw [G.comp_assoc]
    rw [← G.comp_assoc ρ.backward ρ.forward σ.forward]
    rw [ρ.backward_forward]
    rw [G.comp_id_left]
    exact σ.backward_forward

/-- Any functorial state transport sends a recoordination to an equivalence. -/
def transportEquiv {x y : G.Point}
    (T : TransportGeometry G) (ρ : Recoordination G x y) : T.State ≃ T.State where
  toFun := T.transport ρ.forward
  invFun := T.transport ρ.backward
  left_inv := by
    intro s
    rw [← T.transport_comp, ρ.forward_backward, T.transport_id]
  right_inv := by
    intro s
    rw [← T.transport_comp, ρ.backward_forward, T.transport_id]

end Recoordination

#check Recoordination
#check Recoordination.refl
#check Recoordination.symm
#check Recoordination.trans
#check Recoordination.transportEquiv

end GSTGeneralSpace
