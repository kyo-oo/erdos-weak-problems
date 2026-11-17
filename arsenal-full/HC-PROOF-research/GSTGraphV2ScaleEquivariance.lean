import Mathlib
import GSTGraphV2CanonicalNWave
import GSTGraphV2Ontological

/-!
# GST GRAPH V2 — SCALE EQUIVARIANCE CROWN

The canonical U-cut already transports a perfect-power graph through an
arbitrary finite ternary-origin cut.  This layer promotes that pointwise
transport to a compositional law.

The central result is that U-cuts form an exact finite-cut action:
a K-cut followed by an L-cut is identical to one (K+L)-cut.  The consumed
origin prefixes add as horizontal phase, the residual origin composes by
successive suffix, and the complete physical Graph-V2 packet is transported
on the entire Nat x Nat observation plane.

No terminal cutoff and no finite support hypothesis is used.
-/

set_option maxHeartbeats 20000000
set_option maxRecDepth 1000000

namespace GSTGraphV2ScaleEquivariance

open GSTGraphV2InfiniteControl
open GSTGraphV2HandwrittenExponentialCascade
open GSTGraphV2PerfectPowerBlock
open GSTGraphV2CanonicalNWave
open GSTCanonicalSevenAxisBridge

/-- Successive origin suffixes compose exactly. -/
theorem originSuffix_add (n K L : Nat) :
    originSuffix n (K + L) =
      originSuffix (originSuffix n K) L := by
  unfold originSuffix
  rw [pow_add, ← Nat.div_div_eq_div_mul]

/-- A long consumed origin prefix is the old prefix plus the newly exposed
prefix of the old suffix, placed at its exact ternary depth. -/
theorem originPrefix_add (n K L : Nat) :
    originPrefix n (K + L) =
      originPrefix n K +
        3^K * originPrefix (originSuffix n K) L := by
  unfold originPrefix originSuffix
  rw [pow_add, Nat.mod_mul]

/-- **PHASE COCYCLE.**  Horizontal phase accumulated by a (K+L)-cut is
exactly the K-phase plus the L-phase seen from the K-times renormalized
world. -/
theorem uPhaseShift_add (t n K L : Nat) :
    uPhaseShift t n (K + L) =
      uPhaseShift t n K +
        uPhaseShift (t + K) (originSuffix n K) L := by
  unfold uPhaseShift
  rw [originPrefix_add, pow_add]
  ring

/-- Residual exponents compose under successive cuts. -/
theorem uTailExponent_add (t n K L : Nat) :
    uTailExponent t n (K + L) =
      uTailExponent (t + K) (originSuffix n K) L := by
  unfold uTailExponent
  rw [originSuffix_add]
  simp [Nat.add_assoc]

/-- **RESIDUAL-WORLD SEMIGROUP LAW.**  Cutting K+L origin trits in one move
produces exactly the same live world as cutting K first and L afterwards. -/
theorem uTailEnergy_add (t n K L : Nat) :
    uTailEnergy t n (K + L) =
      uTailEnergy (t + K) (originSuffix n K) L := by
  unfold uTailEnergy
  rw [uTailExponent_add]

/-- The absolute perfect-power energy admits the exact two-stage cut
factorization. -/
theorem u_absolute_energy_two_stage
    (t n K L x : Nat) :
    4^x * 4^(3^t * n) =
      4^(uPhaseShift t n K +
          uPhaseShift (t + K) (originSuffix n K) L + x) *
        uTailEnergy (t + K) (originSuffix n K) L := by
  have h := u_absolute_energy_exact t n (K + L) x
  rw [uPhaseShift_add, uTailEnergy_add] at h
  simpa [Nat.add_assoc] using h

/-- The complete Graph-V2 information that is invariant under horizontal
re-coordination.  Coordinate labels themselves are deliberately excluded;
all arithmetic/physical observables are retained. -/
@[ext] structure PhysicalPacket where
  carry : Nat
  digit : Nat
  space : Space
  descent : Nat
  nextDescent : Nat
  eventCode : Nat
  uCharge : Int
  mixedCharge : Int
  crossingCharge : Int
  survive : Int
  deriving Repr

/-- Physical packet at one point of the enriched infinite graph. -/
def physicalPacket (E x p : Nat) : PhysicalPacket :=
  let c := graph E x p
  {
    carry := c.seven.carry
    digit := c.seven.digit
    space := c.seven.space
    descent := c.seven.descent
    nextDescent := c.seven.nextDescent
    eventCode := c.eventCode
    uCharge := c.uCharge
    mixedCharge := c.mixedCharge
    crossingCharge := c.crossingCharge
    survive := c.survive
  }

/-- Every physical observable, not merely carry/digit, is transported by one
arbitrary U-cut. -/
theorem physicalPacket_u_cut_exact
    (t n K x p : Nat) :
    physicalPacket (4^(3^t*n)) x p =
      physicalPacket (uTailEnergy t n K)
        (uPhaseShift t n K + x) p := by
  have h := graph_u_block_observables_exact t n K x p
  rcases h with
    ⟨hcarry, hdigit, hspace, hdescent, hnext, hevent,
      hu, hmixed, hcross, hsurvive⟩
  ext <;>
    simp [physicalPacket, hcarry, hdigit, hspace, hdescent, hnext,
      hevent, hu, hmixed, hcross, hsurvive]

/-- **GLOBAL PLANE EQUIVARIANCE.**  An arbitrary U-cut transports the
complete physical packet on the entire infinite horizontal/vertical graph,
not just at a chosen cell. -/
theorem u_cut_plane_equivariance
    (t n K : Nat) :
    (fun x p => physicalPacket (4^(3^t*n)) x p) =
      (fun x p => physicalPacket (uTailEnergy t n K)
        (uPhaseShift t n K + x) p) := by
  funext x p
  exact physicalPacket_u_cut_exact t n K x p

/-- **TWO-STAGE GRAPH ACTION.**  Applying a K-cut and then an L-cut to the
residual world transports the same physical packet as one coherent action,
with the two phase contributions accumulated explicitly. -/
theorem physicalPacket_u_cut_two_stage
    (t n K L x p : Nat) :
    physicalPacket (4^(3^t*n)) x p =
      physicalPacket
        (uTailEnergy (t + K) (originSuffix n K) L)
        (uPhaseShift t n K +
          uPhaseShift (t + K) (originSuffix n K) L + x) p := by
  have h1 := physicalPacket_u_cut_exact t n K x p
  have h2 := physicalPacket_u_cut_exact
    (t + K) (originSuffix n K) L
    (uPhaseShift t n K + x) p
  calc
    physicalPacket (4^(3^t*n)) x p
        = physicalPacket (uTailEnergy t n K)
            (uPhaseShift t n K + x) p := h1
    _ = physicalPacket
          (uTailEnergy (t + K) (originSuffix n K) L)
          (uPhaseShift (t + K) (originSuffix n K) L +
            (uPhaseShift t n K + x)) p := by
          simpa [uTailEnergy, uTailExponent] using h2
    _ = physicalPacket
          (uTailEnergy (t + K) (originSuffix n K) L)
          (uPhaseShift t n K +
            uPhaseShift (t + K) (originSuffix n K) L + x) p := by
          simp [Nat.add_assoc, Nat.add_comm, Nat.add_left_comm]

/-- **CUT SEMIGROUP COHERENCE.**  The direct (K+L)-cut and the two-stage
K-then-L cut are literally the same Graph-V2 physical re-coordination. -/
theorem u_cut_semigroup_coherence
    (t n K L x p : Nat) :
    physicalPacket (uTailEnergy t n (K + L))
        (uPhaseShift t n (K + L) + x) p =
      physicalPacket
        (uTailEnergy (t + K) (originSuffix n K) L)
        (uPhaseShift t n K +
          uPhaseShift (t + K) (originSuffix n K) L + x) p := by
  rw [uTailEnergy_add, uPhaseShift_add]

/-- Canonical perfect-power worlds inherit the complete packet transport, not
only the carry/digit projection of the earlier n-wave theorem. -/
theorem canonical_n_wave_packet_exact
    (s n K x p : Nat) :
    physicalPacket (canonicalEnergy s n) x p =
      physicalPacket (nWaveEnergy s n K)
        (nWaveShift s n K + x) p := by
  simpa [canonicalEnergy, nWaveEnergy, nWaveShift] using
    (physicalPacket_u_cut_exact (s+1) n K x p)

/-- **CANONICAL N-WAVE PLANE EQUIVARIANCE.**  Every finite canonical
renormalization depth is an exact re-coordinate of the full infinite physical
Graph-V2 plane. -/
theorem canonical_n_wave_plane_equivariance
    (s n K : Nat) :
    (fun x p => physicalPacket (canonicalEnergy s n) x p) =
      (fun x p => physicalPacket (nWaveEnergy s n K)
        (nWaveShift s n K + x) p) := by
  funext x p
  exact canonical_n_wave_packet_exact s n K x p

/-- **UNIVERSAL OBSERVABLE TRANSPORT.**
Every observable of the physical packet is automatically invariant under an
arbitrary finite U-cut.  No new proof is needed for future observables: packet
equality transports them all at once. -/
theorem u_cut_observable_exact
    {α : Type} (F : PhysicalPacket → α)
    (t n K x p : Nat) :
    F (physicalPacket (4^(3^t*n)) x p) =
      F (physicalPacket (uTailEnergy t n K)
        (uPhaseShift t n K + x) p) :=
  congrArg F (physicalPacket_u_cut_exact t n K x p)

/-- **UNIVERSAL PREDICATE TRANSPORT.**
Every proposition depending only on the physical packet is preserved exactly
by arbitrary finite U-cuts. -/
theorem u_cut_predicate_iff
    (P : PhysicalPacket → Prop)
    (t n K x p : Nat) :
    P (physicalPacket (4^(3^t*n)) x p) ↔
      P (physicalPacket (uTailEnergy t n K)
        (uPhaseShift t n K + x) p) := by
  rw [physicalPacket_u_cut_exact]

/-- Every binary relation on two physical packets is transported
simultaneously by the same finite U-cut. -/
theorem u_cut_binary_relation_iff
    (R : PhysicalPacket → PhysicalPacket → Prop)
    (t n K x₁ p₁ x₂ p₂ : Nat) :
    R
        (physicalPacket (4^(3^t*n)) x₁ p₁)
        (physicalPacket (4^(3^t*n)) x₂ p₂)
      ↔
    R
        (physicalPacket (uTailEnergy t n K)
          (uPhaseShift t n K + x₁) p₁)
        (physicalPacket (uTailEnergy t n K)
          (uPhaseShift t n K + x₂) p₂) := by
  rw [physicalPacket_u_cut_exact, physicalPacket_u_cut_exact]

/-- Two-stage cuts preserve every predicate on the physical packet, so
semigroup coherence is inherited by arbitrary packet-defined laws. -/
theorem u_cut_two_stage_predicate_iff
    (P : PhysicalPacket → Prop)
    (t n K L x p : Nat) :
    P (physicalPacket (4^(3^t*n)) x p) ↔
      P (physicalPacket
        (uTailEnergy (t + K) (originSuffix n K) L)
        (uPhaseShift t n K +
          uPhaseShift (t + K) (originSuffix n K) L + x) p) := by
  rw [physicalPacket_u_cut_two_stage]

/-- Canonical N-wave renormalization preserves every observable of the
physical packet, not merely the coordinates explicitly named today. -/
theorem canonical_n_wave_observable_exact
    {α : Type} (F : PhysicalPacket → α)
    (s n K x p : Nat) :
    F (physicalPacket (canonicalEnergy s n) x p) =
      F (physicalPacket (nWaveEnergy s n K)
        (nWaveShift s n K + x) p) :=
  congrArg F (canonical_n_wave_packet_exact s n K x p)

/-- Canonical N-wave renormalization preserves every packet-defined
predicate. -/
theorem canonical_n_wave_predicate_iff
    (P : PhysicalPacket → Prop)
    (s n K x p : Nat) :
    P (physicalPacket (canonicalEnergy s n) x p) ↔
      P (physicalPacket (nWaveEnergy s n K)
        (nWaveShift s n K + x) p) := by
  rw [canonical_n_wave_packet_exact]

/-- Universal capstone: the finite-cut action transports arbitrary
observables, arbitrary predicates, and arbitrary binary relations on the
physical state space. -/
theorem scale_equivariance_universal_observable_crown :
    (∀ (α : Type) (F : PhysicalPacket → α) t n K x p,
      F (physicalPacket (4^(3^t*n)) x p) =
        F (physicalPacket (uTailEnergy t n K)
          (uPhaseShift t n K + x) p))
    ∧ (∀ (P : PhysicalPacket → Prop) t n K x p,
      P (physicalPacket (4^(3^t*n)) x p) ↔
        P (physicalPacket (uTailEnergy t n K)
          (uPhaseShift t n K + x) p))
    ∧ (∀ (R : PhysicalPacket → PhysicalPacket → Prop)
        t n K x₁ p₁ x₂ p₂,
      R (physicalPacket (4^(3^t*n)) x₁ p₁)
          (physicalPacket (4^(3^t*n)) x₂ p₂) ↔
        R
          (physicalPacket (uTailEnergy t n K)
            (uPhaseShift t n K + x₁) p₁)
          (physicalPacket (uTailEnergy t n K)
            (uPhaseShift t n K + x₂) p₂)) := by
  exact ⟨fun α => @u_cut_observable_exact α, u_cut_predicate_iff,
    u_cut_binary_relation_iff⟩

/-- One capstone receipt for the strengthened scale-equivariant cosmology. -/
theorem scale_equivariance_crown :
    (∀ t n K L,
      uPhaseShift t n (K+L) =
        uPhaseShift t n K +
          uPhaseShift (t+K) (originSuffix n K) L)
    ∧ (∀ t n K L,
      uTailEnergy t n (K+L) =
        uTailEnergy (t+K) (originSuffix n K) L)
    ∧ (∀ t n K,
      (fun x p => physicalPacket (4^(3^t*n)) x p) =
        (fun x p => physicalPacket (uTailEnergy t n K)
          (uPhaseShift t n K + x) p))
    ∧ (∀ s n K,
      (fun x p => physicalPacket (canonicalEnergy s n) x p) =
        (fun x p => physicalPacket (nWaveEnergy s n K)
          (nWaveShift s n K + x) p)) :=
  ⟨uPhaseShift_add, uTailEnergy_add,
    u_cut_plane_equivariance, canonical_n_wave_plane_equivariance⟩

#check originSuffix_add
#check originPrefix_add
#check uPhaseShift_add
#check uTailExponent_add
#check uTailEnergy_add
#check u_absolute_energy_two_stage
#check physicalPacket_u_cut_exact
#check u_cut_plane_equivariance
#check physicalPacket_u_cut_two_stage
#check u_cut_semigroup_coherence
#check canonical_n_wave_packet_exact
#check canonical_n_wave_plane_equivariance
#check u_cut_observable_exact
#check u_cut_predicate_iff
#check u_cut_binary_relation_iff
#check u_cut_two_stage_predicate_iff
#check canonical_n_wave_observable_exact
#check canonical_n_wave_predicate_iff
#check scale_equivariance_universal_observable_crown
#check scale_equivariance_crown

#print axioms uPhaseShift_add
#print axioms uTailEnergy_add
#print axioms physicalPacket_u_cut_exact
#print axioms u_cut_plane_equivariance
#print axioms physicalPacket_u_cut_two_stage
#print axioms u_cut_semigroup_coherence
#print axioms canonical_n_wave_plane_equivariance
#print axioms u_cut_observable_exact
#print axioms u_cut_predicate_iff
#print axioms u_cut_binary_relation_iff
#print axioms scale_equivariance_universal_observable_crown
#print axioms scale_equivariance_crown


/-! ## Scale-ontological invariance absorbed into the parent module -/


open GST2DMixedEmergence
open GSTGraphV2InfiniteControl
open GSTGraphV2CanonicalNWave
open GSTGraphV2Ontological

/-- Carry is an exact scale invariant under every finite U-cut. -/
theorem u_cut_carry_exact
    (t n K x p : Nat) :
    (graph (4^(3^t*n)) x p).seven.carry =
      (graph (uTailEnergy t n K)
        (uPhaseShift t n K + x) p).seven.carry := by
  have h := congrArg PhysicalPacket.carry
    (physicalPacket_u_cut_exact t n K x p)
  simpa [physicalPacket] using h

/-- Digit is an exact scale invariant under every finite U-cut. -/
theorem u_cut_digit_exact
    (t n K x p : Nat) :
    (graph (4^(3^t*n)) x p).seven.digit =
      (graph (uTailEnergy t n K)
        (uPhaseShift t n K + x) p).seven.digit := by
  have h := congrArg PhysicalPacket.digit
    (physicalPacket_u_cut_exact t n K x p)
  simpa [physicalPacket] using h

/-- **ARBITRARY-CUT HAPPY INVARIANCE.**
Happy status is not tied to one presentation of a perfect-power world:
every finite U-cut preserves it exactly. -/
theorem u_cut_happy_iff
    (t n K x p : Nat) :
    GSTU2DEventTransport.HappyCell
        (graph (4^(3^t*n)) x p).seven.carry
        (graph (4^(3^t*n)) x p).seven.digit
      ↔
    GSTU2DEventTransport.HappyCell
        (graph (uTailEnergy t n K)
          (uPhaseShift t n K + x) p).seven.carry
        (graph (uTailEnergy t n K)
          (uPhaseShift t n K + x) p).seven.digit := by
  have hc := u_cut_carry_exact t n K x p
  have hd := u_cut_digit_exact t n K x p
  rw [hc, hd]

/-- **ONTOLOGICAL CURRENT SCALE INVARIANCE.**
The pure ontological density itself, not merely its sign, is exactly
preserved by arbitrary finite U-cuts. -/
theorem u_cut_ontDensity_exact
    (t n K x p : Nat) :
    ontDensity
        (graph (4^(3^t*n)) x p).seven.carry
        (graph (4^(3^t*n)) x p).seven.digit
      =
    ontDensity
        (graph (uTailEnergy t n K)
          (uPhaseShift t n K + x) p).seven.carry
        (graph (uTailEnergy t n K)
          (uPhaseShift t n K + x) p).seven.digit := by
  rw [u_cut_carry_exact, u_cut_digit_exact]

/-- Positivity of the ontological current is therefore an exact scale
invariant on the entire Graph-V2 plane. -/
theorem u_cut_ontDensity_positive_iff
    (t n K x p : Nat) :
    0 <
      ontDensity
        (graph (4^(3^t*n)) x p).seven.carry
        (graph (4^(3^t*n)) x p).seven.digit
      ↔
    0 <
      ontDensity
        (graph (uTailEnergy t n K)
          (uPhaseShift t n K + x) p).seven.carry
        (graph (uTailEnergy t n K)
          (uPhaseShift t n K + x) p).seven.digit := by
  rw [u_cut_ontDensity_exact]

/-- The ontological characterization of Happy is itself compatible with every
finite U-cut. -/
theorem u_cut_happy_iff_positive_iff
    (t n K x p : Nat) :
    GSTU2DEventTransport.HappyCell
        (graph (4^(3^t*n)) x p).seven.carry
        (graph (4^(3^t*n)) x p).seven.digit
      ↔
    0 <
      ontDensity
        (graph (uTailEnergy t n K)
          (uPhaseShift t n K + x) p).seven.carry
        (graph (uTailEnergy t n K)
          (uPhaseShift t n K + x) p).seven.digit := by
  rw [u_cut_happy_iff]
  apply happy_iff_ontDensity_positive
  · exact graph_carry_lt_four _ _ _
  · exact graph_digit_lt_three _ _ _

/-- Carry is coherent under the exact two-stage K-then-L scale action. -/
theorem u_cut_two_stage_carry_exact
    (t n K L x p : Nat) :
    (graph (4^(3^t*n)) x p).seven.carry =
      (graph
        (uTailEnergy (t+K) (originSuffix n K) L)
        (uPhaseShift t n K +
          uPhaseShift (t+K) (originSuffix n K) L + x) p).seven.carry := by
  have h := congrArg PhysicalPacket.carry
    (physicalPacket_u_cut_two_stage t n K L x p)
  simpa [physicalPacket] using h

/-- Digit is coherent under the exact two-stage K-then-L scale action. -/
theorem u_cut_two_stage_digit_exact
    (t n K L x p : Nat) :
    (graph (4^(3^t*n)) x p).seven.digit =
      (graph
        (uTailEnergy (t+K) (originSuffix n K) L)
        (uPhaseShift t n K +
          uPhaseShift (t+K) (originSuffix n K) L + x) p).seven.digit := by
  have h := congrArg PhysicalPacket.digit
    (physicalPacket_u_cut_two_stage t n K L x p)
  simpa [physicalPacket] using h

/-- **SEMIGROUP HAPPY COHERENCE.**
Happy status is preserved by the full two-stage scale action. -/
theorem u_cut_two_stage_happy_iff
    (t n K L x p : Nat) :
    GSTU2DEventTransport.HappyCell
        (graph (4^(3^t*n)) x p).seven.carry
        (graph (4^(3^t*n)) x p).seven.digit
      ↔
    GSTU2DEventTransport.HappyCell
        (graph
          (uTailEnergy (t+K) (originSuffix n K) L)
          (uPhaseShift t n K +
            uPhaseShift (t+K) (originSuffix n K) L + x) p).seven.carry
        (graph
          (uTailEnergy (t+K) (originSuffix n K) L)
          (uPhaseShift t n K +
            uPhaseShift (t+K) (originSuffix n K) L + x) p).seven.digit := by
  rw [u_cut_two_stage_carry_exact, u_cut_two_stage_digit_exact]

/-- Ontological density is coherent under the full two-stage scale action. -/
theorem u_cut_two_stage_ontDensity_exact
    (t n K L x p : Nat) :
    ontDensity
        (graph (4^(3^t*n)) x p).seven.carry
        (graph (4^(3^t*n)) x p).seven.digit
      =
    ontDensity
        (graph
          (uTailEnergy (t+K) (originSuffix n K) L)
          (uPhaseShift t n K +
            uPhaseShift (t+K) (originSuffix n K) L + x) p).seven.carry
        (graph
          (uTailEnergy (t+K) (originSuffix n K) L)
          (uPhaseShift t n K +
            uPhaseShift (t+K) (originSuffix n K) L + x) p).seven.digit := by
  rw [u_cut_two_stage_carry_exact, u_cut_two_stage_digit_exact]

/-- Canonical N-wave renormalization preserves the ontological density
exactly, upgrading the earlier carry/digit and Happy projections. -/
theorem canonical_n_wave_ontDensity_exact
    (s n K x p : Nat) :
    ontDensity
        (graph (canonicalEnergy s n) x p).seven.carry
        (graph (canonicalEnergy s n) x p).seven.digit
      =
    ontDensity
        (graph (nWaveEnergy s n K)
          (nWaveShift s n K + x) p).seven.carry
        (graph (nWaveEnergy s n K)
          (nWaveShift s n K + x) p).seven.digit := by
  simpa [canonicalEnergy, nWaveEnergy, nWaveShift] using
    (u_cut_ontDensity_exact (s+1) n K x p)

/-- Canonical N-wave renormalization preserves the positive ontological
sector exactly. -/
theorem canonical_n_wave_ontDensity_positive_iff
    (s n K x p : Nat) :
    0 <
      ontDensity
        (graph (canonicalEnergy s n) x p).seven.carry
        (graph (canonicalEnergy s n) x p).seven.digit
      ↔
    0 <
      ontDensity
        (graph (nWaveEnergy s n K)
          (nWaveShift s n K + x) p).seven.carry
        (graph (nWaveEnergy s n K)
          (nWaveShift s n K + x) p).seven.digit := by
  rw [canonical_n_wave_ontDensity_exact]

/-- Capstone: the complete scale action preserves both the physical Happy
sector and its exact ontological-current certificate. -/
theorem scale_ontological_invariance_crown :
    (∀ t n K x p,
      GSTU2DEventTransport.HappyCell
          (graph (4^(3^t*n)) x p).seven.carry
          (graph (4^(3^t*n)) x p).seven.digit
        ↔
      GSTU2DEventTransport.HappyCell
          (graph (uTailEnergy t n K)
            (uPhaseShift t n K + x) p).seven.carry
          (graph (uTailEnergy t n K)
            (uPhaseShift t n K + x) p).seven.digit)
    ∧ (∀ t n K x p,
      ontDensity
          (graph (4^(3^t*n)) x p).seven.carry
          (graph (4^(3^t*n)) x p).seven.digit
        =
      ontDensity
          (graph (uTailEnergy t n K)
            (uPhaseShift t n K + x) p).seven.carry
          (graph (uTailEnergy t n K)
            (uPhaseShift t n K + x) p).seven.digit)
    ∧ (∀ t n K L x p,
      GSTU2DEventTransport.HappyCell
          (graph (4^(3^t*n)) x p).seven.carry
          (graph (4^(3^t*n)) x p).seven.digit
        ↔
      GSTU2DEventTransport.HappyCell
          (graph
            (uTailEnergy (t+K) (originSuffix n K) L)
            (uPhaseShift t n K +
              uPhaseShift (t+K) (originSuffix n K) L + x) p).seven.carry
          (graph
            (uTailEnergy (t+K) (originSuffix n K) L)
            (uPhaseShift t n K +
              uPhaseShift (t+K) (originSuffix n K) L + x) p).seven.digit) := by
  exact ⟨u_cut_happy_iff, u_cut_ontDensity_exact,
    u_cut_two_stage_happy_iff⟩

#check u_cut_carry_exact
#check u_cut_digit_exact
#check u_cut_happy_iff
#check u_cut_ontDensity_exact
#check u_cut_ontDensity_positive_iff
#check u_cut_happy_iff_positive_iff
#check u_cut_two_stage_happy_iff
#check u_cut_two_stage_ontDensity_exact
#check canonical_n_wave_ontDensity_exact
#check canonical_n_wave_ontDensity_positive_iff
#check scale_ontological_invariance_crown

#print axioms u_cut_happy_iff
#print axioms u_cut_ontDensity_exact
#print axioms u_cut_happy_iff_positive_iff
#print axioms u_cut_two_stage_happy_iff
#print axioms canonical_n_wave_ontDensity_exact
#print axioms scale_ontological_invariance_crown


end GSTGraphV2ScaleEquivariance
