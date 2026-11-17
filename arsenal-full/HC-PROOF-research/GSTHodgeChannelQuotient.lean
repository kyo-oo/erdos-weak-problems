import Mathlib
import GSTHodgeChannelRetract

/-!
# GST HODGE CHANNEL QUOTIENT

The split-retract architecture is stronger than the materialization argument
actually needs.  The minimal datum is a SURJECTIVE decoder from a finite
same-weight Wave-II channel universe onto the rational Hodge sector.

For one fixed weight p:

    Channels(S,p)  --decode-->>  H^(p,p)_Q.

Every canonical channel basis vector is required to decode to the class of
one algebraic cycle.  Surjectivity then supplies channel coordinates for an
arbitrary Hodge class; exact finite channel reconstruction superposes the
corresponding algebraic cycles.

No encoder, no splitting, and no arbitrary-class cycle witness is assumed.
-/

set_option maxHeartbeats 10000000
set_option maxRecDepth 1000000

noncomputable section

open GSTNCohomology
open GSTMultiChannelHodgeCosmology
open GSTHodgeChannelRetract
open GSTGeometricRealizationStage2D
open GSTGeometricRealizationStage2F
open GSTGeometricRealizationStage2G

namespace GSTHodgeChannelQuotient

/-- Minimal generator-level Hodge architecture: a surjective Wave-II channel
decoder whose canonical generators are algebraic cycle classes. -/
structure ChannelHodgeQuotient
    (p : Nat)
    (Coh CycleQ : Type*)
    [AddCommGroup Coh] [Module ℚ Coh]
    [AddCommGroup CycleQ] [Module ℚ CycleQ]
    (hodge : Submodule ℚ Coh)
    (cycleClass : CycleQ →ₗ[ℚ] Coh) where
  shape : NShape
  decode :
    FixedWeightChannelCoordinates shape p →ₗ[ℚ] hodge
  decode_surjective : Function.Surjective decode
  channelCycle : HodgeChannel shape → CycleQ
  channelCycle_decodes :
    ∀ i : HodgeChannel shape,
      cycleClass (channelCycle i) =
        (decode (channelBasis shape p i)).1

variable {p : Nat}
variable {Coh CycleQ : Type*}
variable [AddCommGroup Coh] [Module ℚ Coh]
variable [AddCommGroup CycleQ] [Module ℚ CycleQ]
variable {hodge : Submodule ℚ Coh}
variable {cycleClass : CycleQ →ₗ[ℚ] Coh}

/-- Choose one channel lift of a Hodge class.  This choice is purely linear:
no algebraic-cycle witness is used here. -/
noncomputable def quotientCoordinates
    (Q : ChannelHodgeQuotient p Coh CycleQ hodge cycleClass)
    (alpha : hodge) : FixedWeightChannelCoordinates Q.shape p :=
  Classical.choose (Q.decode_surjective alpha)

@[simp]
theorem quotientCoordinates_spec
    (Q : ChannelHodgeQuotient p Coh CycleQ hodge cycleClass)
    (alpha : hodge) :
    Q.decode (quotientCoordinates Q alpha) = alpha :=
  Classical.choose_spec (Q.decode_surjective alpha)

/-- Algebraic cycle produced by superposing the algebraic channel generators
with the chosen channel coordinates of alpha. -/
noncomputable def quotientCycleWitness
    (Q : ChannelHodgeQuotient p Coh CycleQ hodge cycleClass)
    (alpha : hodge) : CycleQ :=
  ∑ i : HodgeChannel Q.shape,
    (quotientCoordinates Q alpha i) • Q.channelCycle i

/-- **QUOTIENT MATERIALIZATION THEOREM.**
Surjective channel decoding plus algebraicity of the canonical channel
generators represents every Hodge class exactly. -/
theorem quotientCycleWitness_spec
    (Q : ChannelHodgeQuotient p Coh CycleQ hodge cycleClass)
    (alpha : hodge) :
    cycleClass (quotientCycleWitness Q alpha) = alpha.1 := by
  classical
  let a := quotientCoordinates Q alpha
  have ha : Q.decode a = alpha := quotientCoordinates_spec Q alpha
  calc
    cycleClass (quotientCycleWitness Q alpha)
        = ∑ i : HodgeChannel Q.shape,
            (a i) • cycleClass (Q.channelCycle i) := by
              simp [quotientCycleWitness, a]
    _ = ∑ i : HodgeChannel Q.shape,
          (a i) • (Q.decode (channelBasis Q.shape p i)).1 := by
          apply Finset.sum_congr rfl
          intro i hi
          rw [Q.channelCycle_decodes i]
    _ = (Q.decode
          (∑ i : HodgeChannel Q.shape,
            (a i) • channelBasis Q.shape p i)).1 := by
          simp
    _ = (Q.decode a).1 := by
          rw [← channel_reconstruct Q.shape p a]
    _ = alpha.1 := by
          exact congrArg Subtype.val ha

/-- Elementwise witness form of the quotient theorem. -/
theorem hodge_class_has_quotient_cycle
    (Q : ChannelHodgeQuotient p Coh CycleQ hodge cycleClass)
    (alpha : Coh) (halpha : alpha ∈ hodge) :
    ∃ Z : CycleQ, cycleClass Z = alpha := by
  let a : hodge := ⟨alpha, halpha⟩
  exact ⟨quotientCycleWitness Q a, quotientCycleWitness_spec Q a⟩

/-- Submodule form: the whole Hodge sector lies in the cycle-class range. -/
theorem quotient_hodge_le_cycleClass_range
    (Q : ChannelHodgeQuotient p Coh CycleQ hodge cycleClass) :
    hodge ≤ LinearMap.range cycleClass := by
  intro alpha halpha
  obtain ⟨Z, hZ⟩ := hodge_class_has_quotient_cycle Q alpha halpha
  exact ⟨Z, hZ⟩

/-- Every split channel retract canonically forgets to the weaker quotient
architecture.  Thus the quotient theorem strictly subsumes the retract
materialization route. -/
noncomputable def ChannelHodgeRetract.toQuotient
    (R : ChannelHodgeRetract p Coh CycleQ hodge cycleClass) :
    ChannelHodgeQuotient p Coh CycleQ hodge cycleClass where
  shape := R.shape
  decode := R.decode
  decode_surjective := by
    intro alpha
    exact ⟨R.encode alpha, R.decode_encode alpha⟩
  channelCycle := R.channelCycle
  channelCycle_decodes := by
    intro i
    exact congrArg Subtype.val (R.channelCycle_decodes i)

/-- Stage-2G specialization of the minimal quotient architecture. -/
abbrev Stage2GChannelQuotient
    (V : GSTProjectiveOverC.SmoothProjectiveComplexScheme)
    (H : HodgeBigradedBettiData V)
    (p : Nat) :=
  ChannelHodgeQuotient
    p
    (RationalSingularCohomology H.analytification (2 * p))
    (codimensionCycles V.X p)
    (rationalHodgeSubspace (H.hodgeBigrading p))
    (H.cycleClass p)

/-- One quotient at codimension p materializes every derived rational
(p,p)-class. -/
theorem hodge_class_has_stage2g_quotient_cycle
    (V : GSTProjectiveOverC.SmoothProjectiveComplexScheme)
    (H : HodgeBigradedBettiData V)
    {p : Nat}
    (Q : Stage2GChannelQuotient V H p)
    (alpha : RationalSingularCohomology H.analytification (2 * p))
    (halpha : alpha ∈ rationalHodgeSubspace (H.hodgeBigrading p)) :
    ∃ Z : codimensionCycles V.X p,
      H.cycleClass p Z = alpha := by
  exact hodge_class_has_quotient_cycle Q alpha halpha

/-- **STAGE-2G QUOTIENT LANDING.** -/
theorem bigraded_betti_hodge_of_channel_quotient_family
    (V : GSTProjectiveOverC.SmoothProjectiveComplexScheme)
    (H : HodgeBigradedBettiData V)
    (Q : ∀ p : Nat, Stage2GChannelQuotient V H p) :
    BigradedBettiHodgeStatement V H := by
  intro p alpha halpha
  exact quotient_hodge_le_cycleClass_range (Q p) halpha

/-- Exact minimal channel obligation. -/
def Stage2GChannelQuotientObligation
    (V : GSTProjectiveOverC.SmoothProjectiveComplexScheme)
    (H : HodgeBigradedBettiData V) : Prop :=
  ∀ p : Nat, Nonempty (Stage2GChannelQuotient V H p)

/-- The minimal channel obligation closes the Stage-2G target. -/
theorem bigraded_betti_hodge_of_channel_quotient_obligation
    (V : GSTProjectiveOverC.SmoothProjectiveComplexScheme)
    (H : HodgeBigradedBettiData V)
    (hQ : Stage2GChannelQuotientObligation V H) :
    BigradedBettiHodgeStatement V H := by
  exact bigraded_betti_hodge_of_channel_quotient_family
    V H (fun p => (hQ p).some)

/-- Capstone for the minimal quotient architecture. -/
theorem hodge_channel_quotient_crown
    (V : GSTProjectiveOverC.SmoothProjectiveComplexScheme)
    (H : HodgeBigradedBettiData V) :
    Stage2GChannelQuotientObligation V H →
      BigradedBettiHodgeStatement V H :=
  bigraded_betti_hodge_of_channel_quotient_obligation V H

#check ChannelHodgeQuotient
#check quotientCoordinates
#check quotientCoordinates_spec
#check quotientCycleWitness
#check quotientCycleWitness_spec
#check hodge_class_has_quotient_cycle
#check quotient_hodge_le_cycleClass_range
#check ChannelHodgeRetract.toQuotient
#check Stage2GChannelQuotient
#check hodge_class_has_stage2g_quotient_cycle
#check bigraded_betti_hodge_of_channel_quotient_family
#check Stage2GChannelQuotientObligation
#check hodge_channel_quotient_crown

#print axioms quotientCoordinates_spec
#print axioms quotientCycleWitness_spec
#print axioms quotient_hodge_le_cycleClass_range
#print axioms bigraded_betti_hodge_of_channel_quotient_family
#print axioms hodge_channel_quotient_crown

end GSTHodgeChannelQuotient
