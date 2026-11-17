import Mathlib
import GSTMultiChannelHodgeCosmology
import GSTGeometricRealizationStage2G

/-!
# GST HODGE CHANNEL MATERIALIZATION

This is the geometric bridge for the multi-channel Hodge cosmology.

The theorem does NOT assume cycle-class surjectivity.  For one fixed Hodge
weight p it asks only for:

* a Wave-II `NShape` of independent channels;
* a linear equivalence from the intended rational Hodge submodule onto the
  fixed-weight channel coordinates;
* one actual cycle for each canonical channel generator;
* proof that the cycle-class of that generator lies in the Hodge submodule;
* proof that its channel coordinates are exactly the Kronecker basis vector.

From those generator-level data the whole Hodge sector is materialized by a
finite channel superposition.  This is the missing braid:

  Wave-II multiplicity
      -> same-weight Hodge multiplicity
      -> algebraic channel generators
      -> every Hodge class.

The final section specializes the generic theorem directly to Stage 2G,
where the Hodge subspace is derived from the genuine complex bigrading and
the cycle carrier is the native codimension-p cycle space.
-/

set_option maxHeartbeats 10000000
set_option maxRecDepth 1000000

noncomputable section

open GSTNCohomology
open GSTMultiChannelHodgeCosmology
open GSTGeometricRealizationStage2D
open GSTGeometricRealizationStage2F
open GSTGeometricRealizationStage2G

namespace GSTHodgeChannelMaterialization

/-- Generator-level realization of one rational Hodge submodule by Wave-II
channels at one fixed weight p.

Crucially, no field asks for a cycle representing an arbitrary Hodge class.
Only the canonical channel generators must be materialized geometrically. -/
structure ChannelHodgeRealization
    (p : Nat)
    (Coh CycleQ : Type*)
    [AddCommGroup Coh] [Module ℚ Coh]
    [AddCommGroup CycleQ] [Module ℚ CycleQ]
    (hodge : Submodule ℚ Coh)
    (cycleClass : CycleQ →ₗ[ℚ] Coh) where
  shape : NShape
  coordinates :
    hodge ≃ₗ[ℚ] FixedWeightChannelCoordinates shape p
  channelCycle : HodgeChannel shape -> CycleQ
  channelCycle_mem :
    ∀ i : HodgeChannel shape,
      cycleClass (channelCycle i) ∈ hodge
  channelCycle_coordinate :
    ∀ i : HodgeChannel shape,
      coordinates
        ⟨cycleClass (channelCycle i), channelCycle_mem i⟩
        = channelBasis shape p i

variable {p : Nat}
variable {Coh CycleQ : Type*}
variable [AddCommGroup Coh] [Module ℚ Coh]
variable [AddCommGroup CycleQ] [Module ℚ CycleQ]
variable {hodge : Submodule ℚ Coh}
variable {cycleClass : CycleQ →ₗ[ℚ] Coh}

/-- The cohomology class of one materialized channel, packaged inside the
Hodge submodule. -/
noncomputable def channelClassInHodge
    (R : ChannelHodgeRealization p Coh CycleQ hodge cycleClass)
    (i : HodgeChannel R.shape) : hodge :=
  ⟨cycleClass (R.channelCycle i), R.channelCycle_mem i⟩

/-- Materialize one Hodge class by summing its channel coordinates against
the algebraic cycle attached to each canonical channel. -/
noncomputable def channelCycleWitness
    (R : ChannelHodgeRealization p Coh CycleQ hodge cycleClass)
    (alpha : hodge) : CycleQ :=
  ∑ i : HodgeChannel R.shape,
    (R.coordinates alpha i) • R.channelCycle i

/-- The parallel superposition performed inside the Hodge submodule. -/
noncomputable def channelHodgeWitness
    (R : ChannelHodgeRealization p Coh CycleQ hodge cycleClass)
    (alpha : hodge) : hodge :=
  ∑ i : HodgeChannel R.shape,
    (R.coordinates alpha i) • channelClassInHodge R i

/-- The Hodge-side superposition has exactly the original channel vector. -/
theorem channelHodgeWitness_coordinates
    (R : ChannelHodgeRealization p Coh CycleQ hodge cycleClass)
    (alpha : hodge) :
    R.coordinates (channelHodgeWitness R alpha) = R.coordinates alpha := by
  classical
  calc
    R.coordinates (channelHodgeWitness R alpha)
        = ∑ i : HodgeChannel R.shape,
            (R.coordinates alpha i) •
              R.coordinates (channelClassInHodge R i) := by
            simp [channelHodgeWitness]
    _ = ∑ i : HodgeChannel R.shape,
          (R.coordinates alpha i) • channelBasis R.shape p i := by
          apply Finset.sum_congr rfl
          intro i hi
          simp only [channelClassInHodge]
          rw [R.channelCycle_coordinate i]
    _ = R.coordinates alpha :=
      (channel_reconstruct R.shape p (R.coordinates alpha)).symm

/-- The Hodge-side channel superposition is literally the original Hodge
class, by injectivity of the channel coordinate equivalence. -/
theorem channelHodgeWitness_eq
    (R : ChannelHodgeRealization p Coh CycleQ hodge cycleClass)
    (alpha : hodge) :
    channelHodgeWitness R alpha = alpha := by
  apply R.coordinates.injective
  exact channelHodgeWitness_coordinates R alpha

/-- **CHANNEL MATERIALIZATION THEOREM.**
The finite superposition of the generator cycles has cycle class exactly the
original Hodge class.  No arbitrary-class cycle witness was assumed. -/
theorem channelCycleWitness_spec
    (R : ChannelHodgeRealization p Coh CycleQ hodge cycleClass)
    (alpha : hodge) :
    cycleClass (channelCycleWitness R alpha) = alpha.1 := by
  classical
  calc
    cycleClass (channelCycleWitness R alpha)
        = (channelHodgeWitness R alpha).1 := by
          simp [channelCycleWitness, channelHodgeWitness,
            channelClassInHodge]
    _ = alpha.1 := by
      exact congrArg Subtype.val (channelHodgeWitness_eq R alpha)

/-- Elementwise geometric witness form. -/
theorem hodge_class_has_channel_cycle
    (R : ChannelHodgeRealization p Coh CycleQ hodge cycleClass)
    (alpha : Coh) (halpha : alpha ∈ hodge) :
    ∃ Z : CycleQ, cycleClass Z = alpha := by
  let a : hodge := ⟨alpha, halpha⟩
  exact ⟨channelCycleWitness R a, channelCycleWitness_spec R a⟩

/-- **GENERATOR ALGEBRAICITY IMPLIES HODGE-SURJECTIVITY.**
The entire Hodge submodule lies in the range of the cycle-class map once the
canonical Wave-II channel generators are materialized. -/
theorem channel_hodge_le_cycleClass_range
    (R : ChannelHodgeRealization p Coh CycleQ hodge cycleClass) :
    hodge ≤ LinearMap.range cycleClass := by
  intro alpha halpha
  obtain ⟨Z,hZ⟩ := hodge_class_has_channel_cycle R alpha halpha
  exact ⟨Z,hZ⟩

/-- Stage-2G specialization: the Hodge submodule is the one derived from the
actual supplied Hodge bigrading, and cycles are native codimension-p cycles. -/
abbrev Stage2GChannelMaterialization
    (V : GSTProjectiveOverC.SmoothProjectiveComplexScheme)
    (H : HodgeBigradedBettiData V)
    (p : Nat) :=
  ChannelHodgeRealization
    p
    (RationalSingularCohomology H.analytification (2 * p))
    (codimensionCycles V.X p)
    (rationalHodgeSubspace (H.hodgeBigrading p))
    (H.cycleClass p)

/-- One Stage-2G channel materialization gives a genuine codimension-p cycle
for every rational class whose complexification lies in H^(p,p). -/
theorem hodge_class_has_stage2g_channel_cycle
    (V : GSTProjectiveOverC.SmoothProjectiveComplexScheme)
    (H : HodgeBigradedBettiData V)
    {p : Nat}
    (R : Stage2GChannelMaterialization V H p)
    (alpha : RationalSingularCohomology H.analytification (2 * p))
    (halpha : alpha ∈ rationalHodgeSubspace (H.hodgeBigrading p)) :
    ∃ Z : codimensionCycles V.X p,
      H.cycleClass p Z = alpha := by
  exact hodge_class_has_channel_cycle R alpha halpha

/-- **STAGE-2G MULTI-CHANNEL LANDING.**
If every codimension p admits generator-level channel materialization, the
full derived rational `(p,p)` Hodge statement follows. -/
theorem bigraded_betti_hodge_of_channel_materialization_family
    (V : GSTProjectiveOverC.SmoothProjectiveComplexScheme)
    (H : HodgeBigradedBettiData V)
    (R : ∀ p : Nat, Stage2GChannelMaterialization V H p) :
    BigradedBettiHodgeStatement V H := by
  intro p alpha halpha
  exact channel_hodge_le_cycleClass_range (R p) halpha

/-- Exact new geometric obligation exposed by the channel theorem.  It asks
for one materialized canonical channel basis in each codimension, not a cycle
representative for every Hodge class. -/
def Stage2GChannelMaterializationObligation
    (V : GSTProjectiveOverC.SmoothProjectiveComplexScheme)
    (H : HodgeBigradedBettiData V) : Prop :=
  ∀ p : Nat, Nonempty (Stage2GChannelMaterialization V H p)

/-- The channel obligation alone closes the Stage-2G target. -/
theorem bigraded_betti_hodge_of_channel_materialization_obligation
    (V : GSTProjectiveOverC.SmoothProjectiveComplexScheme)
    (H : HodgeBigradedBettiData V)
    (hR : Stage2GChannelMaterializationObligation V H) :
    BigradedBettiHodgeStatement V H := by
  exact bigraded_betti_hodge_of_channel_materialization_family
    V H (fun p => (hR p).some)

/-- Capstone: fixed-weight channel generator algebraicity is sufficient for
the full Stage-2G rational Hodge target. -/
theorem hodge_channel_materialization_crown
    (V : GSTProjectiveOverC.SmoothProjectiveComplexScheme)
    (H : HodgeBigradedBettiData V) :
    Stage2GChannelMaterializationObligation V H ->
      BigradedBettiHodgeStatement V H :=
  bigraded_betti_hodge_of_channel_materialization_obligation V H

#check ChannelHodgeRealization
#check channelClassInHodge
#check channelCycleWitness
#check channelHodgeWitness
#check channelHodgeWitness_coordinates
#check channelCycleWitness_spec
#check hodge_class_has_channel_cycle
#check channel_hodge_le_cycleClass_range
#check Stage2GChannelMaterialization
#check hodge_class_has_stage2g_channel_cycle
#check bigraded_betti_hodge_of_channel_materialization_family
#check Stage2GChannelMaterializationObligation
#check bigraded_betti_hodge_of_channel_materialization_obligation
#check hodge_channel_materialization_crown

#print axioms channelHodgeWitness_coordinates
#print axioms channelCycleWitness_spec
#print axioms channel_hodge_le_cycleClass_range
#print axioms bigraded_betti_hodge_of_channel_materialization_family
#print axioms hodge_channel_materialization_crown

end GSTHodgeChannelMaterialization
