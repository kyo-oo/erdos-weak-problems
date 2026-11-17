import Mathlib
import GSTCarrierAlgebraFlatComplex

/-!
# GST Round 59 — the tower morphisms and the transport laws

Round 58 (`GSTCarrierAlgebraFlatComplex`) closed the carrier algebra
(associativity) and the flat complex (cycles, boundaries, the
boundary-inclusion). This round opens the functorial world: a
MORPHISM of towers transports the whole machinery — the
differential, the square, the carriers — from one tower to another.

* **THE TOWER MORPHISM** (`TowerMorphism`): a ℚ-linear map between
  the underlying spaces commuting with the base differential and
  every memory jet — the map of ε-families. The identity is a
  morphism.

* **THE TRANSPORT LAWS.** THE CURVATURE TRANSPORT
  (`map_curv`): a morphism commutes with every curvature carrier —
  `f ∘ K_k = K'_k ∘ f` — the memory law's chase: both memory laws
  transport term by term through the base and jet compatibilities.
  THE NATURALITY OF THE DIFFERENTIAL (`jetMap_differential`): the
  levelwise extension of a morphism to the jet spaces commutes with
  the infinite differentials — `F (D u) = D' (F u)` at every level.
  THE NATURALITY OF THE SQUARE (`jetMap_square`): `F (D² u) =
  D'² (F u)` — both sides the curvature ladder, the terms matched by
  the curvature transport.

* **THE FUNCTORIALITY.** THE CARRIER TOWER'S FUNCTORIALITY
  (`carrierTowerMorphism`): the SAME map is a morphism of the
  carrier towers — the curvature cascade is functorial. THE FLAT
  TRANSFER (`map_curv_flat`): a morphism carries flat towers to
  flat towers pointwise — every carrier of the target vanishes on
  the image.

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
variable {T : JetTowerInf V}
variable {T' : JetTowerInf W}

/-! ## Face 1 — the tower morphism and the transports -/

/-- **THE TOWER MORPHISM.** A ℚ-linear map between the underlying
spaces of two infinite memory towers, commuting with the base
differential and every memory jet — the map of ε-families
`d + ∑ ε^(k+1) φ_k`. -/
structure TowerMorphism (T : JetTowerInf V) (T' : JetTowerInf W) where
  /-- The underlying linear map. -/
  map : V →ₗ[ℚ] W
  /-- Compatibility with the base differential. -/
  map_base : map.comp T.base = T'.base.comp map
  /-- Compatibility with every memory jet. -/
  map_jet : ∀ k : ℕ, map.comp (T.jet k) = (T'.jet k).comp map

/-- **The identity morphism.** Every tower is a morphism of itself. -/
def identityMorphism (T : JetTowerInf V) : TowerMorphism T T where
  map := LinearMap.id
  map_base := by rw [LinearMap.id_comp, LinearMap.comp_id]
  map_jet := fun _ => by rw [LinearMap.id_comp, LinearMap.comp_id]

/-- **The pointwise base transport.** -/
theorem map_base_apply (m : TowerMorphism T T') (y : V) :
    m.map (T.base y) = T'.base (m.map y) := by
  simpa only [LinearMap.comp_apply] using
    congrArg (fun f : V →ₗ[ℚ] W => f y) m.map_base

/-- **The pointwise jet transport.** -/
theorem map_jet_apply (m : TowerMorphism T T') (k : ℕ) (y : V) :
    m.map (T.jet k y) = T'.jet k (m.map y) := by
  simpa only [LinearMap.comp_apply] using
    congrArg (fun f : V →ₗ[ℚ] W => f y) (m.map_jet k)

/-- **THE CURVATURE TRANSPORT.** A morphism commutes with every
curvature carrier: `f ∘ K_k = K'_k ∘ f`. The proof is the memory
law's chase — both memory laws transport term by term through the
base and jet compatibilities, so the carriers (their common value)
transport too. -/
theorem map_curv (m : TowerMorphism T T') (k : ℕ) :
    m.map.comp (T.curv k) = (T'.curv k).comp m.map := by
  ext x
  show m.map (T.curv k x) = T'.curv k (m.map x)
  rw [← memoryInf_apply T k x, ← memoryInf_apply T' k (m.map x)]
  simp only [map_add, map_sum]
  have h1 : m.map (T.base (T.jet k x)) = T'.base (T'.jet k (m.map x)) := by
    rw [map_base_apply m (T.jet k x), map_jet_apply m k x]
  have h2 : m.map (T.jet k (T.base x)) = T'.jet k (T'.base (m.map x)) := by
    rw [map_jet_apply m k (T.base x), map_base_apply m x]
  have h3 : ∀ r ∈ Finset.range k,
      m.map (T.jet r (T.jet (k - 1 - r) x))
        = T'.jet r (T'.jet (k - 1 - r) (m.map x)) := by
    intro r _
    rw [map_jet_apply m r (T.jet (k - 1 - r) x),
      map_jet_apply m (k - 1 - r) x]
  rw [h1, h2, Finset.sum_congr rfl h3]

/-- **The induced jet-space map.** The levelwise extension of a
morphism to the infinite jet spaces. -/
def jetMap (m : TowerMorphism T T') : (ℕ → V) →ₗ[ℚ] (ℕ → W) where
  toFun u := fun j => m.map (u j)
  map_add' := by
    intro u w
    funext j
    show m.map ((u + w) j) = m.map (u j) + m.map (w j)
    rw [Pi.add_apply, map_add]
  map_smul' := by
    intro r u
    funext j
    show m.map ((r • u) j) = (r : ℚ) • m.map (u j)
    rw [Pi.smul_apply, map_smul]

/-- **The induced map's computation rule.** -/
theorem jetMap_apply (m : TowerMorphism T T') (u : ℕ → V) (j : ℕ) :
    jetMap m u j = m.map (u j) := rfl

/-- **THE NATURALITY OF THE DIFFERENTIAL.** The levelwise extension
of a morphism commutes with the infinite differentials at every
level: `F (D u) = D' (F u)` — the base and jet compatibilities,
transported level by level. -/
theorem jetMap_differential (m : TowerMorphism T T') (u : ℕ → V) (j : ℕ) :
    jetMap m (T.jetInfDifferential u) j
      = T'.jetInfDifferential (jetMap m u) j := by
  have hbase : m.map (T.base (u j)) = T'.base (m.map (u j)) :=
    map_base_apply m (u j)
  have hjet : ∀ i ∈ Finset.range j,
      m.map (T.jet i (u (j - 1 - i))) = T'.jet i (m.map (u (j - 1 - i))) := by
    intro i _
    exact map_jet_apply m i (u (j - 1 - i))
  show m.map (T.base (u j) + ∑ i ∈ Finset.range j, T.jet i (u (j - 1 - i)))
      = T'.base (m.map (u j)) + ∑ i ∈ Finset.range j, T'.jet i (m.map (u (j - 1 - i)))
  rw [map_add, map_sum, hbase, Finset.sum_congr rfl hjet]

/-! ## Face 2 — the functoriality -/

/-- **THE NATURALITY OF THE SQUARE.** The levelwise extension of a
morphism commutes with the squares of the infinite differentials:
`F (D² u) = D'² (F u)` — both sides the curvature ladder, the terms
matched by the curvature transport. -/
theorem jetMap_square (m : TowerMorphism T T') (u : ℕ → V) (j : ℕ) :
    jetMap m (T.jetInfDifferential (T.jetInfDifferential u)) j
      = T'.jetInfDifferential (T'.jetInfDifferential (jetMap m u)) j := by
  have hL : jetMap m (T.jetInfDifferential (T.jetInfDifferential u)) j
      = ∑ i ∈ Finset.range j, m.map (T.curv i (u (j - 1 - i))) := by
    show m.map (T.jetInfDifferential (T.jetInfDifferential u) j)
      = ∑ i ∈ Finset.range j, m.map (T.curv i (u (j - 1 - i)))
    rw [jetInfDifferential_square_apply T u j, map_sum]
  have hR : T'.jetInfDifferential (T'.jetInfDifferential (jetMap m u)) j
      = ∑ i ∈ Finset.range j, T'.curv i (m.map (u (j - 1 - i))) :=
    jetInfDifferential_square_apply T' (jetMap m u) j
  rw [hL, hR]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [← LinearMap.comp_apply, map_curv m i]
  rfl

/-- **THE FLAT TRANSFER, POINTWISE.** A morphism carries flat towers
to flat towers on its image: every curvature carrier of the target
vanishes at every image point. -/
theorem map_curv_flat (m : TowerMorphism T T') (hflat : T.IsFlat)
    (k : ℕ) (y : V) :
    T'.curv k (m.map y) = 0 := by
  have happly : m.map (T.curv k y) = T'.curv k (m.map y) := by
    simpa only [LinearMap.comp_apply] using
      congrArg (fun f : V →ₗ[ℚ] W => f y) (map_curv m k)
  rw [← happly, hflat k, LinearMap.zero_apply, map_zero]

/-- **THE CARRIER TOWER'S FUNCTORIALITY.** The same map is a morphism
of the carrier towers: the curvature cascade is functorial — a map
commuting with the family commutes with its curvature, hence with
the curvature of its curvature, at every order of the cascade. -/
def carrierTowerMorphism (m : TowerMorphism T T') :
    TowerMorphism (carrierTower T) (carrierTower T') where
  map := m.map
  map_base := by
    show m.map.comp (0 : V →ₗ[ℚ] V) = (0 : W →ₗ[ℚ] W).comp m.map
    ext x
    simp [LinearMap.comp_apply, LinearMap.zero_apply, map_zero]
  map_jet := fun k => map_curv m k

end GSTFoldTowerSquare.JetTowerInf

#print axioms GSTFoldTowerSquare.JetTowerInf.map_base_apply
#print axioms GSTFoldTowerSquare.JetTowerInf.map_jet_apply
#print axioms GSTFoldTowerSquare.JetTowerInf.map_curv
#print axioms GSTFoldTowerSquare.JetTowerInf.jetMap_apply
#print axioms GSTFoldTowerSquare.JetTowerInf.jetMap_differential
#print axioms GSTFoldTowerSquare.JetTowerInf.jetMap_square
#print axioms GSTFoldTowerSquare.JetTowerInf.map_curv_flat
