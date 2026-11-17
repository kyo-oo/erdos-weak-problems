import GSTGraphV2CanonicalSignedPrefixBridge
import GSTInfiniteCoupledLedger

set_option maxRecDepth 1000000
set_option maxHeartbeats 20000000

namespace GSTGraphV2CanonicalInfiniteCycle

open GSTV2
open GSTGraphV2InfiniteControl
open GSTGraphV2PerfectPowerBlock
open GSTGraphV2CanonicalEscape
open GSTGraphV2InfiniteControllerBridge
open GSTGraphV2HandwrittenAnchoredCocycle
open GSTGraphV2CoupledUFlux

/-- The literal all-depth controller attached to the canonical perfect-power
block.  No terminal height is selected. -/
def canonicalController (s n : Nat) : CoupledState :=
  graphCoupledState
    (canonicalEnergy s n)
    (canonicalWidth s)
    (s + 2)

/-- Iterating for `a+b` rows is exactly iteration for `a` rows followed by
iteration for `b` rows. -/
theorem coupledOrbit_add_exact
    (A : Nat) (initial : CoupledState) (a b : Nat) :
    coupledOrbit A initial (a + b) =
      coupledOrbit A (coupledOrbit A initial a) b := by
  induction b with
  | zero => simp [coupledOrbit]
  | succ b ih =>
      rw [show a + (b + 1) = (a + b) + 1 by omega]
      rw [coupledOrbit, ih, coupledOrbit]

/-- A repeated complete live controller state repeats at every further turn of
the same cycle.  The theorem retains all five coordinates; it does not project
the controller to a carry/digit label and it does not assume termination. -/
theorem coupledOrbit_cycle_all_turns
    (A : Nat) (initial : CoupledState) (a L : Nat)
    (hcycle :
      coupledOrbit A initial a =
        coupledOrbit A initial (a + L)) :
    ∀ m : Nat,
      coupledOrbit A initial (a + m * L) =
        coupledOrbit A initial a := by
  intro m
  induction m with
  | zero => simp
  | succ m ih =>
      calc
        coupledOrbit A initial (a + (m + 1) * L) =
            coupledOrbit A initial ((a + m * L) + L) := by
              simp [Nat.succ_mul, Nat.add_assoc]
        _ = coupledOrbit A (coupledOrbit A initial (a + m * L)) L :=
              coupledOrbit_add_exact A initial (a + m * L) L
        _ = coupledOrbit A (coupledOrbit A initial a) L := by rw [ih]
        _ = coupledOrbit A initial (a + L) :=
              (coupledOrbit_add_exact A initial a L).symm
        _ = coupledOrbit A initial a := hcycle.symm

/-- Canonical specialization of the exact infinite-cycle theorem. -/
theorem canonical_controller_cycle_all_turns
    (s n a L : Nat)
    (hcycle :
      coupledOrbit (4^(canonicalWidth s)) (canonicalController s n) a =
        coupledOrbit (4^(canonicalWidth s))
          (canonicalController s n) (a + L)) :
    ∀ m : Nat,
      coupledOrbit (4^(canonicalWidth s))
          (canonicalController s n) (a + m * L) =
        coupledOrbit (4^(canonicalWidth s))
          (canonicalController s n) a :=
  coupledOrbit_cycle_all_turns
    (4^(canonicalWidth s)) (canonicalController s n) a L hcycle

/-- The exact Past/Future ledger remains available at every turn of a canonical
cycle.  This is the lossless packet required by recurrence-based surgery. -/
theorem canonical_cycle_ledger_packet
    (s n a L : Nat)
    (hcycle :
      coupledOrbit (4^(canonicalWidth s)) (canonicalController s n) a =
        coupledOrbit (4^(canonicalWidth s))
          (canonicalController s n) (a + L)) :
    ∀ m : Nat,
      let initial := canonicalController s n
      initial.parentPast (4^(canonicalWidth s)) (a + m * L) +
          3^(a + m * L) *
            (coupledOrbit (4^(canonicalWidth s)) initial
              (a + m * L)).childResidue =
        initial.childResidue +
          4^(canonicalWidth s) *
            initial.childPast (a + m * L) := by
  intro m
  dsimp only
  exact (infinite_coupled_ledger
    (4^(canonicalWidth s)) (canonicalController s n)
    (by positivity)
    (by
      dsimp [canonicalController]
      exact graphCoupledState_invariant
        (canonicalEnergy s n) (canonicalWidth s) (s + 2))).pastSynchronized
          (a + m * L)


/-- A repeated controller packet is literally a repeated rectangle on the
canonical Graph-V2 spacetime sheet at every turn of the cycle. -/
theorem canonical_graph_state_cycle_all_turns
    (s n a L : Nat)
    (hcycle :
      graphCoupledState (canonicalEnergy s n) (canonicalWidth s)
          (s + 2 + a) =
        graphCoupledState (canonicalEnergy s n) (canonicalWidth s)
          (s + 2 + (a + L))) :
    ∀ m : Nat,
      graphCoupledState (canonicalEnergy s n) (canonicalWidth s)
          (s + 2 + (a + m * L)) =
        graphCoupledState (canonicalEnergy s n) (canonicalWidth s)
          (s + 2 + a) := by
  intro m
  have hcycleOrbit :
      coupledOrbit (4^(canonicalWidth s)) (canonicalController s n) a =
        coupledOrbit (4^(canonicalWidth s))
          (canonicalController s n) (a + L) := by
    simp only [canonicalController]
    rw [graphCoupledOrbit_exact, graphCoupledOrbit_exact]
    simpa [Nat.add_assoc] using hcycle
  have hturn :=
    canonical_controller_cycle_all_turns s n a L hcycleOrbit m
  simp only [canonicalController] at hturn
  rw [graphCoupledOrbit_exact, graphCoupledOrbit_exact] at hturn
  simpa [Nat.add_assoc] using hturn

/-- Observable form of the same theorem.  Both endpoint cells and the retained
horizontal U potential repeat on the literal Graph-V2 sheet; the result is not
a projected carry-only automaton. -/
theorem canonical_graph_observables_cycle_all_turns
    (s n a L : Nat)
    (hcycle :
      graphCoupledState (canonicalEnergy s n) (canonicalWidth s)
          (s + 2 + a) =
        graphCoupledState (canonicalEnergy s n) (canonicalWidth s)
          (s + 2 + (a + L))) :
    ∀ m : Nat,
      let p := s + 2 + (a + m * L)
      let p0 := s + 2 + a
      (graph (canonicalEnergy s n) 0 p).seven.carry =
          (graph (canonicalEnergy s n) 0 p0).seven.carry ∧
      (graph (canonicalEnergy s n) 0 p).seven.digit =
          (graph (canonicalEnergy s n) 0 p0).seven.digit ∧
      (graph (canonicalEnergy s n) (canonicalWidth s) p).seven.carry =
          (graph (canonicalEnergy s n) (canonicalWidth s) p0).seven.carry ∧
      (graph (canonicalEnergy s n) (canonicalWidth s) p).seven.digit =
          (graph (canonicalEnergy s n) (canonicalWidth s) p0).seven.digit ∧
      graphUPotential (canonicalEnergy s n) 0 (canonicalWidth s) p =
        graphUPotential (canonicalEnergy s n) 0 (canonicalWidth s) p0 := by
  intro m
  dsimp only
  let E := canonicalEnergy s n
  let N := canonicalWidth s
  let p := s + 2 + (a + m * L)
  let p0 := s + 2 + a
  have hst :
      graphCoupledState E N p = graphCoupledState E N p0 := by
    dsimp [E, N, p, p0]
    exact canonical_graph_state_cycle_all_turns s n a L hcycle m
  have hLeftCarry :=
    congrArg (fun st : CoupledState => st.childCarry) hst
  have hRightCarry :=
    congrArg (fun st : CoupledState => st.parentSeed) hst
  have hLeftDigitState :=
    congrArg (fun st : CoupledState => st.childTail % 3) hst
  have hRightDigitState :=
    congrArg (fun st : CoupledState =>
      (st.parentOffset + 4^N * (st.childTail % 3)) % 3) hst
  have hPotential :=
    congrArg (fun st : CoupledState =>
      gstUChargeExact st.parentSeed -
        (((4^N : Nat) : Int)) * gstUChargeExact st.childCarry +
        24 * (st.parentOffset : Int)) hst
  refine ⟨?_, ?_, ?_, ?_, ?_⟩
  · simpa [graphCoupledState] using hLeftCarry
  · rw [← graphCoupledState_childDigit_exact E N p,
        ← graphCoupledState_childDigit_exact E N p0]
    exact hLeftDigitState
  · simpa [graphCoupledState] using hRightCarry
  · rw [← graphCoupledState_parentDigit_exact E N p,
        ← graphCoupledState_parentDigit_exact E N p0]
    exact hRightDigitState
  · simpa [graphUPotential, graphCoupledState] using hPotential


/-! ## Full recurrence class generated by one cycle -/

/-- A single repeated state generates pairwise equality across the entire
arithmetic progression of cycle turns, not merely equality with the base
turn. -/
theorem coupledOrbit_cycle_pairwise
    (A : Nat) (initial : CoupledState) (a L : Nat)
    (hcycle :
      coupledOrbit A initial a =
        coupledOrbit A initial (a + L)) :
    ∀ m n : Nat,
      coupledOrbit A initial (a + m * L) =
        coupledOrbit A initial (a + n * L) := by
  intro m n
  rw [coupledOrbit_cycle_all_turns A initial a L hcycle m,
      coupledOrbit_cycle_all_turns A initial a L hcycle n]

/-- Every natural multiple of a witnessed period is itself an exact period
at the same recurrence base. -/
theorem coupledOrbit_cycle_multiple
    (A : Nat) (initial : CoupledState) (a L q : Nat)
    (hcycle :
      coupledOrbit A initial a =
        coupledOrbit A initial (a + L)) :
    coupledOrbit A initial a =
      coupledOrbit A initial (a + q * L) := by
  symm
  exact coupledOrbit_cycle_all_turns A initial a L hcycle q

/-- Canonical graph recurrence is pairwise on every two turns of the same
cycle class.  The equality is of the complete coupled state. -/
theorem canonical_graph_state_cycle_pairwise
    (s n a L : Nat)
    (hcycle :
      graphCoupledState (canonicalEnergy s n) (canonicalWidth s)
          (s + 2 + a) =
        graphCoupledState (canonicalEnergy s n) (canonicalWidth s)
          (s + 2 + (a + L))) :
    ∀ m r : Nat,
      graphCoupledState (canonicalEnergy s n) (canonicalWidth s)
          (s + 2 + (a + m * L)) =
        graphCoupledState (canonicalEnergy s n) (canonicalWidth s)
          (s + 2 + (a + r * L)) := by
  intro m r
  rw [canonical_graph_state_cycle_all_turns s n a L hcycle m,
      canonical_graph_state_cycle_all_turns s n a L hcycle r]

/-- Every multiple of the canonical period repeats the complete Graph-V2
rectangle state at the original recurrence base. -/
theorem canonical_graph_state_cycle_multiple
    (s n a L q : Nat)
    (hcycle :
      graphCoupledState (canonicalEnergy s n) (canonicalWidth s)
          (s + 2 + a) =
        graphCoupledState (canonicalEnergy s n) (canonicalWidth s)
          (s + 2 + (a + L))) :
    graphCoupledState (canonicalEnergy s n) (canonicalWidth s)
        (s + 2 + a) =
      graphCoupledState (canonicalEnergy s n) (canonicalWidth s)
        (s + 2 + (a + q * L)) := by
  symm
  exact canonical_graph_state_cycle_all_turns s n a L hcycle q


/-! ## Period algebra of the all-depth controller -/

/-- A period of the coupled controller measured from recurrence base `a`. -/
def IsCoupledPeriod
    (A : Nat) (initial : CoupledState) (a L : Nat) : Prop :=
  coupledOrbit A initial a =
    coupledOrbit A initial (a + L)

/-- Zero is always a controller period. -/
theorem isCoupledPeriod_zero
    (A : Nat) (initial : CoupledState) (a : Nat) :
    IsCoupledPeriod A initial a 0 := by
  simp [IsCoupledPeriod]

/-- **ADDITIVE PERIOD CLOSURE.**  Two periods at the same recurrence base
compose to a period of their sum.  Thus recurrence lengths form an additive
submonoid of the natural-time action. -/
theorem isCoupledPeriod_add
    (A : Nat) (initial : CoupledState) (a L M : Nat)
    (hL : IsCoupledPeriod A initial a L)
    (hM : IsCoupledPeriod A initial a M) :
    IsCoupledPeriod A initial a (L+M) := by
  unfold IsCoupledPeriod at hL hM ⊢
  calc
    coupledOrbit A initial a
        = coupledOrbit A (coupledOrbit A initial a) M := by
            rw [← coupledOrbit_add_exact A initial a M]
            exact hM
    _ = coupledOrbit A (coupledOrbit A initial (a+L)) M := by
          rw [← hL]
    _ = coupledOrbit A initial ((a+L)+M) :=
          (coupledOrbit_add_exact A initial (a+L) M).symm
    _ = coupledOrbit A initial (a+(L+M)) := by
          congr 2
          omega

/-- Every natural multiple of a period remains a period. -/
theorem isCoupledPeriod_nsmul
    (A : Nat) (initial : CoupledState) (a L q : Nat)
    (hL : IsCoupledPeriod A initial a L) :
    IsCoupledPeriod A initial a (q*L) := by
  unfold IsCoupledPeriod at hL ⊢
  simpa [Nat.mul_comm] using
    (coupledOrbit_cycle_multiple A initial a L q hL)

/-- Period-algebra crown for the infinite controller. -/
theorem coupled_period_additive_crown
    (A : Nat) (initial : CoupledState) (a : Nat) :
    IsCoupledPeriod A initial a 0
    ∧ (∀ L M,
      IsCoupledPeriod A initial a L →
      IsCoupledPeriod A initial a M →
      IsCoupledPeriod A initial a (L+M))
    ∧ (∀ L q,
      IsCoupledPeriod A initial a L →
      IsCoupledPeriod A initial a (q*L)) := by
  exact ⟨isCoupledPeriod_zero A initial a,
    fun L M => isCoupledPeriod_add A initial a L M,
    fun L q => isCoupledPeriod_nsmul A initial a L q⟩

#check IsCoupledPeriod
#check isCoupledPeriod_zero
#check isCoupledPeriod_add
#check isCoupledPeriod_nsmul
#check coupled_period_additive_crown
#print axioms isCoupledPeriod_add
#print axioms coupled_period_additive_crown

#check coupledOrbit_add_exact
#check coupledOrbit_cycle_all_turns
#check coupledOrbit_cycle_pairwise
#check coupledOrbit_cycle_multiple
#check canonical_graph_state_cycle_pairwise
#check canonical_graph_state_cycle_multiple
#check canonical_controller_cycle_all_turns
#check canonical_cycle_ledger_packet
#check canonical_graph_state_cycle_all_turns
#check canonical_graph_observables_cycle_all_turns
#print axioms coupledOrbit_cycle_all_turns
#print axioms coupledOrbit_cycle_pairwise
#print axioms canonical_graph_state_cycle_pairwise
#print axioms canonical_cycle_ledger_packet
#print axioms canonical_graph_state_cycle_all_turns
#print axioms canonical_graph_observables_cycle_all_turns

end GSTGraphV2CanonicalInfiniteCycle
