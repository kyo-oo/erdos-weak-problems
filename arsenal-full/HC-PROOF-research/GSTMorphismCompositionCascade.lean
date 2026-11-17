import Mathlib
import GSTTowerMorphismTransport

/-!
# GST Round 60 — the morphism composition and the cascade's functoriality

Round 59 (`GSTTowerMorphismTransport`) opened the functorial world:
the tower morphism, the curvature transport, the naturality of the
differential and the square, the carrier tower's functoriality. This
round completes the functorial structure:

* **THE MORPHISM COMPOSITION** (`TowerMorphism.comp`): morphisms of
  towers compose — the base and jet compatibilities chain — and the
  levelwise jet-space extension of the composite IS the composite of
  the extensions (`jetMap_comp`): the jet-space construction is a
  FUNCTOR on the tower category.

* **THE CYCLES AND BOUNDARIES TRANSFER** (`map_cycles`,
  `map_boundaries`): a morphism carries cycles to cycles and
  boundaries to boundaries — the flat complex of Round 58 is natural
  under the morphisms.

* **THE ITERATED CARRIER MORPHISM** (`carrierPowerMorphism`): the
  `m`-fold carrier tower of a morphism — the cascade's functoriality
  iterated, with the underlying map unchanged through every iterate
  (`carrierPowerMorphism_map`).

All statements are exact algebraic identities over supplied data
(linear-map identities and finite ℚ-linear-map sum identities),
kernel-verified by the module's own CI lane on the pinned toolchain
`leanprover/lean4:v4.33.0-rc2` with Mathlib. Zero `sorry`, zero axiom
declarations, zero `native_decide`. The geometric identification of
the tower with actual cohomology stays hand-level; no original-X
algebraic-source existence is claimed, assumed, or concluded.
-/

namespace GSTFoldTowerSquare.JetTowerInf

variable {V : Type*} [AddCommGroup V] [Module ℚ V]
variable {W : Type*} [AddCommGroup W] [Module ℚ W]
variable {U : Type*} [AddCommGroup U] [Module ℚ U]
variable {T : JetTowerInf V}
variable {T' : JetTowerInf W}
variable {T'' : JetTowerInf U}

/-! ## Face 1 — the composition and the jet-space functor -/

/-- **THE MORPHISM COMPOSITION.** Morphisms of towers compose: the
base and jet compatibilities chain through the composite. -/
def comp (g : TowerMorphism T' T'') (f : TowerMorphism T T') :
    TowerMorphism T T'' where
  map := g.map.comp f.map
  map_base := by
    ext x
    show g.map (f.map (T.base x)) = T''.base (g.map (f.map x))
    rw [map_base_apply f x, map_base_apply g (f.map x)]
  map_jet := by
    intro k
    ext x
    show g.map (f.map (T.jet k x)) = T''.jet k (g.map (f.map x))
    rw [map_jet_apply f k x, map_jet_apply g k (f.map x)]

/-- **THE JETMAP'S FUNCTORIALITY.** The levelwise extension of the
composite is the composite of the extensions: the jet-space
construction is a functor on the tower category. -/
theorem jetMap_comp (g : TowerMorphism T' T'') (f : TowerMorphism T T') :
    jetMap (comp g f) = (jetMap g).comp (jetMap f) := by
  ext u j
  show (comp g f).map (u j) = jetMap g (jetMap f u) j
  rfl

/-- **The jet-space extension of the identity is the identity,
pointwise.** -/
theorem jetMap_identity (u : ℕ → V) (j : ℕ) :
    jetMap (identityMorphism T) u j = u j := rfl

/-! ## Face 2 — the complex transfer and the cascade functoriality -/

/-- **THE CYCLES TRANSFER.** A morphism carries cycles to cycles: the
D-closed jets map to D'-closed jets — the cycles of the flat complex
are natural under the morphisms. -/
theorem map_cycles (f : TowerMorphism T T') (u : ℕ → V) (h : u ∈ cycles T) :
    jetMap f u ∈ cycles T' := by
  rw [mem_cycles]
  intro j
  rw [← jetMap_differential f u j]
  show f.map (T.jetInfDifferential u j) = 0
  rw [mem_cycles] at h
  rw [h j, map_zero]

/-- **THE BOUNDARIES TRANSFER.** A morphism carries boundaries to
boundaries: the D-exact jets map to D'-exact jets — the boundaries of
the flat complex are natural under the morphisms. -/
theorem map_boundaries (f : TowerMorphism T T') (u : ℕ → V)
    (h : u ∈ boundaries T) : jetMap f u ∈ boundaries T' := by
  obtain ⟨v, hv⟩ := LinearMap.mem_range.mp h
  rw [← hv]
  refine LinearMap.mem_range.mpr ⟨jetMap f v, ?_⟩
  funext j
  exact (jetMap_differential f v j).symm

/-- **THE ITERATED CARRIER MORPHISM.** The `m`-fold carrier tower of a
morphism: the cascade's functoriality iterated — the morphism of the
towers is a morphism of the `m`-fold carrier towers, at every order
of the cascade. -/
def carrierPowerMorphism (m : ℕ) (f : TowerMorphism T T') :
    TowerMorphism (carrierPower T m) (carrierPower T' m) :=
  match m with
  | 0 => f
  | m + 1 => carrierTowerMorphism (carrierPowerMorphism m f)

/-- **The cascade morphism's underlying map is the original's.** The
iterates never change the map — only the towers around it grow. -/
theorem carrierPowerMorphism_map (m : ℕ) (f : TowerMorphism T T') :
    (carrierPowerMorphism m f).map = f.map := by
  induction m with
  | zero => rfl
  | succ m ih =>
    show (carrierPowerMorphism m f).map = f.map
    exact ih

end GSTFoldTowerSquare.JetTowerInf

#print axioms GSTFoldTowerSquare.JetTowerInf.jetMap_comp
#print axioms GSTFoldTowerSquare.JetTowerInf.jetMap_identity
#print axioms GSTFoldTowerSquare.JetTowerInf.map_cycles
#print axioms GSTFoldTowerSquare.JetTowerInf.map_boundaries
#print axioms GSTFoldTowerSquare.JetTowerInf.carrierPowerMorphism_map
