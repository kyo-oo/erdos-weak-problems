import Mathlib
import GSTMultiChannelHodgeCosmology

/-!
# GST HODGE CHANNEL ADDRESS BRIDGE

Wave-II channel multiplicity is finite inside each shape, but the channel
addresses themselves live in Nat and are injective.  Stage-2's rank-free
realization route also uses a natural-number address universe.

This file proves the exact bridge: every fixed-weight channel vector embeds
faithfully into an unbounded Nat-indexed coordinate field by placing each
channel coefficient at its physical Wave-II address and zero elsewhere.

No Hodge conclusion and no algebraic-cycle statement occurs here.  This is
pure address geometry for the new multi-channel sector.
-/

set_option maxHeartbeats 10000000
set_option maxRecDepth 1000000

noncomputable section

namespace GSTHodgeChannelAddressBridge

open GSTNCohomology
open GSTMultiChannelHodgeCosmology

/-- Lift a finite fixed-weight channel vector into the unbounded natural
address universe.  Injectivity of Wave-II channel addresses prevents
collisions. -/
def channelAddressLift
    (S : NShape) (p : Nat)
    (a : FixedWeightChannelCoordinates S p) : Nat -> ℚ :=
  fun n =>
    ∑ i : HodgeChannel S,
      if channelAddress S i = n then a i else 0

/-- Reading the lifted field at a physical channel address recovers exactly
the original channel coefficient. -/
theorem channelAddressLift_at
    (S : NShape) (p : Nat)
    (a : FixedWeightChannelCoordinates S p)
    (i : HodgeChannel S) :
    channelAddressLift S p a (channelAddress S i) = a i := by
  classical
  unfold channelAddressLift
  rw [Finset.sum_eq_single i]
  · simp
  · intro j hj hji
    have haddr : channelAddress S j ≠ channelAddress S i := by
      intro h
      exact hji (channelAddress_injective S h)
    simp [haddr]
  · simp

/-- The Nat-address lift is faithful. -/
theorem channelAddressLift_injective
    (S : NShape) (p : Nat) :
    Function.Injective (channelAddressLift S p) := by
  intro a b hab
  funext i
  have hi := congrArg (fun f => f (channelAddress S i)) hab
  rw [channelAddressLift_at S p a i,
      channelAddressLift_at S p b i] at hi
  exact hi

/-- A canonical channel basis vector reads as one at its own physical address. -/
theorem channelBasis_address_self
    (S : NShape) (p : Nat) (i : HodgeChannel S) :
    channelAddressLift S p (channelBasis S p i) (channelAddress S i) = 1 := by
  rw [channelAddressLift_at]
  exact channelBasis_self S p i

/-- A canonical channel basis vector vanishes at every other physical channel
address. -/
theorem channelBasis_address_other
    (S : NShape) (p : Nat) (i j : HodgeChannel S)
    (hji : j ≠ i) :
    channelAddressLift S p (channelBasis S p i) (channelAddress S j) = 0 := by
  rw [channelAddressLift_at]
  exact channelBasis_other S p i j hji

/-- **CHANNEL ADDRESS BRIDGE CROWN.**
Every fixed-weight Wave-II channel universe sits faithfully inside one common
unbounded Nat-address field, with the canonical channel basis remaining
Kronecker on the physical channel addresses. -/
theorem channel_address_bridge_crown
    (S : NShape) (p : Nat) :
    Function.Injective (channelAddressLift S p)
      ∧ (∀ i : HodgeChannel S,
          channelAddressLift S p (channelBasis S p i)
            (channelAddress S i) = 1)
      ∧ (∀ i j : HodgeChannel S, j ≠ i ->
          channelAddressLift S p (channelBasis S p i)
            (channelAddress S j) = 0) := by
  exact ⟨channelAddressLift_injective S p,
    channelBasis_address_self S p,
    channelBasis_address_other S p⟩

#check channelAddressLift
#check channelAddressLift_at
#check channelAddressLift_injective
#check channelBasis_address_self
#check channelBasis_address_other
#check channel_address_bridge_crown

#print axioms channelAddressLift_at
#print axioms channelAddressLift_injective
#print axioms channel_address_bridge_crown

end GSTHodgeChannelAddressBridge
