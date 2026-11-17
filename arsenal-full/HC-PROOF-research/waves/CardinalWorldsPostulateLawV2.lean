import Mathlib
import waves.CardinalWorldsPostulateLaw

/-!
# POSTULATE III V2 — NONDEGENERATE CONTROLLED EMERGENCE

The original ControlledTower used a stationary-point controller equation
and the ledger equation simultaneously. Those two equations force every
successive level to equal the previous level. This upgrade separates
control from transition: control is now an admissibility invariant,
while the ledger remains the exact bridge evolution.

The result is a genuinely evolving controlled tower with exact finite
transport, composition, reconstruction, and admissibility propagation.
-/

set_option maxHeartbeats 10000000
set_option maxRecDepth 1000000

namespace CardinalWorldsPostulateLawV2

open CardinalWorldsPostulateLaw

theorem legacy_tower_succ_eq (T : ControlledTower Nat) (j : Nat) :
    T.level (j + 1) = T.level j := by
  calc
    T.level (j + 1) = T.bridge j (T.level j) := T.ledger j
    _ = T.level j := (T.controller j).symm

theorem legacy_tower_add_eq (T : ControlledTower Nat) (j n : Nat) :
    T.level (j + n) = T.level j := by
  induction n with
  | zero => simp
  | succ n ih =>
      rw [Nat.add_succ, legacy_tower_succ_eq T (j+n), ih]

structure ControlledTowerV2 (α : Type) where
  level : Nat → α
  bridge : Nat → α → α
  admissible : Nat → α → Prop
  level_admissible : ∀ j, admissible j (level j)
  ledger : ∀ j, level (j+1) = bridge j (level j)
  control_preserved :
    ∀ j x, admissible j x → admissible (j+1) (bridge j x)

def transport {α : Type} (T : ControlledTowerV2 α) :
    Nat → Nat → α → α
  | _, 0, x => x
  | j, n+1, x => transport T (j+1) n (T.bridge j x)

theorem transport_zero {α : Type} (T : ControlledTowerV2 α)
    (j : Nat) (x : α) :
    transport T j 0 x = x := rfl

theorem transport_one {α : Type} (T : ControlledTowerV2 α)
    (j : Nat) (x : α) :
    transport T j 1 x = T.bridge j x := by
  rfl

theorem transport_add {α : Type} (T : ControlledTowerV2 α)
    (j m n : Nat) (x : α) :
    transport T j (m+n) x =
      transport T (j+m) n (transport T j m x) := by
  induction m generalizing j x with
  | zero => simp [transport]
  | succ m ih =>
      simp only [Nat.succ_add, transport]
      simpa [Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using
        (ih (j := j+1) (x := T.bridge j x))

theorem level_transport_exact {α : Type} (T : ControlledTowerV2 α)
    (j n : Nat) :
    T.level (j+n) = transport T j n (T.level j) := by
  induction n generalizing j with
  | zero => simp [transport]
  | succ n ih =>
      rw [Nat.add_succ]
      calc
        T.level (j+n+1)
            = T.bridge (j+n) (T.level (j+n)) := T.ledger (j+n)
        _ = T.bridge (j+n) (transport T j n (T.level j)) := by rw [ih]
        _ = transport T j (n+1) (T.level j) := by
              have ht := (transport_add T j n 1 (T.level j)).symm
              simpa [transport] using ht

theorem admissible_transport {α : Type} (T : ControlledTowerV2 α)
    (j n : Nat) (x : α) (hx : T.admissible j x) :
    T.admissible (j+n) (transport T j n x) := by
  induction n generalizing j x with
  | zero => simpa [transport] using hx
  | succ n ih =>
      rw [show j + (n+1) = (j+1)+n from by omega]
      exact ih (j := j+1) (x := T.bridge j x)
        (T.control_preserved j x hx)

theorem finite_presentation_v2 {α : Type} (T : ControlledTowerV2 α)
    (k : Nat) :
    T.level k = transport T 0 k (T.level 0) := by
  simpa using level_transport_exact T 0 k

theorem tower_ext_of_initial_and_bridge
    {α : Type} (T₁ T₂ : ControlledTowerV2 α)
    (h0 : T₁.level 0 = T₂.level 0)
    (hb : ∀ j x, T₁.bridge j x = T₂.bridge j x) :
    ∀ n, T₁.level n = T₂.level n := by
  intro n
  induction n with
  | zero => exact h0
  | succ n ih =>
      rw [T₁.ledger n, T₂.ledger n, hb, ih]

def legacyEmbed (T : ControlledTower Nat) : ControlledTowerV2 Nat where
  level := T.level
  bridge := T.bridge
  admissible := fun _ x => x = x
  level_admissible := by
    intro j
    rfl
  ledger := T.ledger
  control_preserved := by
    intro j x hx
    rfl

def successorTower : ControlledTowerV2 Nat where
  level := fun j => j
  bridge := fun _ x => x + 1
  admissible := fun j x => x = j
  level_admissible := by intro j; rfl
  ledger := by intro j; rfl
  control_preserved := by
    intro j x hx
    omega

theorem successorTower_not_stationary :
    successorTower.level 1 ≠ successorTower.level 0 := by
  decide

theorem controlled_emergence_v2_crown :
    (∀ j n, successorTower.level (j+n) =
      transport successorTower j n (successorTower.level j))
    ∧ (∀ j m n x,
      transport successorTower j (m+n) x =
        transport successorTower (j+m) n
          (transport successorTower j m x))
    ∧ successorTower.level 1 ≠ successorTower.level 0 := by
  refine ⟨?_, ?_, successorTower_not_stationary⟩
  · intro j n
    exact level_transport_exact successorTower j n
  · intro j m n x
    exact transport_add successorTower j m n x

#check legacy_tower_succ_eq
#check legacy_tower_add_eq
#check ControlledTowerV2
#check transport_add
#check level_transport_exact
#check admissible_transport
#check tower_ext_of_initial_and_bridge
#check successorTower_not_stationary
#check controlled_emergence_v2_crown

#print axioms transport_add
#print axioms level_transport_exact
#print axioms admissible_transport
#print axioms tower_ext_of_initial_and_bridge
#print axioms controlled_emergence_v2_crown

end CardinalWorldsPostulateLawV2
