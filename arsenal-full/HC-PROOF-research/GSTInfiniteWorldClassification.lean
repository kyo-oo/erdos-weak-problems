import GSTWorldCosmology
import Mathlib
import GSTCoherentCosmology

/-!
# GST INFINITE WORLD CLASSIFICATION

The coherent cosmology already proves:
* every ternary innovation stream builds a coherent WindowTower;
* every WindowTower reconstructs a unique innovation stream.

This file upgrades those inverse statements to an actual equivalence

    WindowTower ≃ (Nat → Fin 3),

and derives complete-observation theorems from it.

Thus controlled GST infinity is not merely inhabited by stream-built examples:
it is exactly the full ternary stream space.  The finite level K is the first
K trits, and the complete two-current trace is a faithful coordinate system
for the entire infinite world.
-/

set_option maxHeartbeats 20000000
set_option maxRecDepth 1000000

namespace GSTInfiniteWorldClassification

open GSTCoherentCosmology

/-- Extensionality of coherent worlds by their finite residue levels. -/
theorem windowTower_ext
    (X Y : WindowTower)
    (h : X.level = Y.level) :
    X = Y := by
  cases X with
  | mk lx bx cx =>
    cases Y with
    | mk ly byd cy =>
      cases h
      congr

/-- Reconstructing a coherent world from its innovation stream returns the
world itself, not just an isomorphic observation trace. -/
theorem streamTower_innovationStream
    (X : WindowTower) :
    streamTower (innovationStream X) = X := by
  apply windowTower_ext
  funext K
  exact innovation_reconstructs X K

/-- Reading the innovation stream of a stream-built world returns the
original stream exactly. -/
theorem innovationStream_streamTower
    (a : Nat → Fin 3) :
    innovationStream (streamTower a) = a := by
  funext p
  apply Fin.ext
  exact stream_digit_exact a p

/-- **COMPLETE CLASSIFICATION OF COHERENT GST INFINITY.**
Every coherent world is exactly one infinite ternary innovation stream. -/
def windowTowerEquivStream :
    WindowTower ≃ (Nat → Fin 3) where
  toFun := innovationStream
  invFun := streamTower
  left_inv := streamTower_innovationStream
  right_inv := innovationStream_streamTower

/-- Equality of coherent worlds is exactly equality of innovation streams. -/
theorem windowTower_eq_iff_stream_eq
    (X Y : WindowTower) :
    X = Y ↔ innovationStream X = innovationStream Y := by
  constructor
  · intro h
    simpa [h]
  · intro h
    apply windowTowerEquivStream.injective
    exact h

/-- Agreement of level K is exactly agreement of the first K reconstructed
base-3 prefixes. -/
theorem level_eq_iff_prefix_eq
    (X Y : WindowTower) (K : Nat) :
    X.level K = Y.level K ↔
      streamPrefix (innovationStream X) K =
        streamPrefix (innovationStream Y) K := by
  rw [innovation_reconstructs X K, innovation_reconstructs Y K]

/-- If two innovation streams agree below K, their finite level-K worlds
are identical. -/
theorem level_eq_of_stream_prefix
    (X Y : WindowTower) (K : Nat)
    (h : ∀ p, p < K → innovationStream X p = innovationStream Y p) :
    X.level K = Y.level K := by
  rw [← innovation_reconstructs X K, ← innovation_reconstructs Y K]
  induction K with
  | zero =>
      rfl
  | succ K ih =>
      simp only [streamPrefix]
      rw [ih (fun p hp => h p (by omega)), h K (by omega)]

/-- Conversely, a finite level determines every innovation trit below that
level. -/
theorem stream_prefix_of_level_eq
    (X Y : WindowTower) (K : Nat)
    (h : X.level K = Y.level K) :
    ∀ p, p < K → innovationStream X p = innovationStream Y p := by
  intro p hp
  apply Fin.ext
  unfold innovationStream
  have hobs :=
    (finite_observation_equivalence X Y K).mp h 0 p hp
  exact (dual_current_separation
    _ _ _ _
    (tower_carry_bound X 0 p)
    (tower_digit_bound X 0 p)
    (tower_carry_bound Y 0 p)
    (tower_digit_bound Y 0 p)
    hobs).2

/-- **FINITE PREFIX CLASSIFICATION.**
Level K equality and equality of the first K innovation trits are equivalent. -/
theorem level_eq_iff_stream_prefix
    (X Y : WindowTower) (K : Nat) :
    X.level K = Y.level K ↔
      ∀ p, p < K → innovationStream X p = innovationStream Y p := by
  constructor
  · exact stream_prefix_of_level_eq X Y K
  · exact level_eq_of_stream_prefix X Y K

/-- The complete two-current trace at horizontal time zero is injective on
all coherent worlds, not merely stream-built examples. -/
theorem towerCurrent_trace_injective :
    Function.Injective (fun X : WindowTower => towerCurrent X 0) := by
  intro X Y h
  apply windowTower_ext
  funext K
  apply current_trace_reconstructs X Y K
  intro p hp
  exact congrFun h p

/-- Equality of coherent worlds is exactly equality of their entire current
trace at one horizontal time. -/
theorem windowTower_eq_iff_current_trace
    (X Y : WindowTower) :
    X = Y ↔ towerCurrent X 0 = towerCurrent Y 0 := by
  constructor
  · intro h
    simpa [h]
  · intro h
    exact towerCurrent_trace_injective h

/-- One horizontal slice already determines every finite world level, hence
the entire coherent world. -/
theorem current_trace_complete
    (X Y : WindowTower)
    (h : ∀ p, towerCurrent X 0 p = towerCurrent Y 0 p) :
    X = Y := by
  apply towerCurrent_trace_injective
  funext p
  exact h p

/-- Full spacetime observations are therefore also a complete invariant. -/
theorem windowTower_eq_iff_all_observations
    (X Y : WindowTower) :
    X = Y ↔
      ∀ t p, towerCurrent X t p = towerCurrent Y t p := by
  constructor
  · intro h t p
    simpa [h]
  · intro h
    exact current_trace_complete X Y (fun p => h 0 p)

/-- The stream coordinate and current coordinate determine one another
injectively. -/
theorem stream_to_current_injective :
    Function.Injective
      (fun a : Nat → Fin 3 => towerCurrent (streamTower a) 0) := by
  intro a b h
  have hw : streamTower a = streamTower b :=
    towerCurrent_trace_injective h
  have hs := congrArg innovationStream hw
  rw [innovationStream_streamTower a, innovationStream_streamTower b] at hs
  exact hs

/-- Capstone: coherent GST infinity is exactly ternary stream space and the
two-current trace is a complete global observable. -/
theorem infinite_world_classification_crown :
    Function.Bijective innovationStream
    ∧ Function.Bijective streamTower
    ∧ Function.Injective (fun X : WindowTower => towerCurrent X 0)
    ∧ (∀ X Y : WindowTower,
        X = Y ↔
          ∀ t p, towerCurrent X t p = towerCurrent Y t p) := by
  exact ⟨
    windowTowerEquivStream.bijective,
    windowTowerEquivStream.symm.bijective,
    towerCurrent_trace_injective,
    windowTower_eq_iff_all_observations⟩

#check windowTowerEquivStream
#check level_eq_iff_stream_prefix
#check towerCurrent_trace_injective
#check windowTower_eq_iff_current_trace
#check windowTower_eq_iff_all_observations
#check infinite_world_classification_crown

#print axioms windowTowerEquivStream
#print axioms level_eq_iff_stream_prefix
#print axioms towerCurrent_trace_injective
#print axioms windowTower_eq_iff_all_observations
#print axioms infinite_world_classification_crown


/-! ## Topology of completed observation -/
open GSTWorldCosmology

instance (A B : ℕ) : TopologicalSpace (WorldCoef A B) :=
  inferInstanceAs (TopologicalSpace (WorldCell A B → ℤ))

theorem continuous_observe (A B : ℕ) : Continuous (observe A B) := by
  apply continuous_pi
  intro c
  exact continuous_apply (c.1.val, c.2.val)

/-- Continuity is detected exactly by all finite observation maps. -/
theorem continuous_iff_all_windows {T : Type*} [TopologicalSpace T]
    (f : T → CompletedCosmos) :
    Continuous f ↔ ∀ A B, Continuous (fun t => observe A B (f t)) := by
  constructor
  · intro hf A B
    exact (continuous_observe A B).comp hf
  · intro h
    apply continuous_pi
    rintro ⟨i, j⟩
    let hc' : WorldCell (i+1) (j+1) :=
      (⟨i, by omega⟩, ⟨j, by omega⟩)
    exact (continuous_apply hc').comp (h (i+1) (j+1))

instance : TopologicalSpace WindowTower :=
  TopologicalSpace.induced innovationStream inferInstance

/-- Stream classification is also a topological classification. -/
def windowTowerHomeomorph : WindowTower ≃ₜ (ℕ → Fin 3) where
  toEquiv := windowTowerEquivStream
  continuous_toFun := continuous_induced_dom
  continuous_invFun := by
    apply continuous_induced_rng.mpr
    change Continuous (innovationStream ∘ streamTower)
    have h : innovationStream ∘ streamTower = id := by
      funext a
      exact innovationStream_streamTower a
    rw [h]
    exact continuous_id

end GSTInfiniteWorldClassification
