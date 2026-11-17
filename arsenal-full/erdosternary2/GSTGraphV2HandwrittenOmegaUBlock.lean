import GSTGraphV2PerfectPowerBlockProbe

set_option maxRecDepth 1000000
set_option maxHeartbeats 10000000

namespace GSTGraphV2HandwrittenOmegaUBlock

open GSTGraphV2InfiniteControl
open GSTGraphV2PerfectPowerAncestry
open GSTGraphV2PerfectPowerBlock
open GSTU2DEventTransport

/-!
# Handwritten Omega/U exponential operator on the canonical Graph-V2 sheet

The raw handwritten simultaneous multiply/divide U operation is used here only
through its exact finite-natural core: consume the least ternary origin trit
into the perfect-power multiplier while dividing the remaining origin by 3.
No analytic limit, terminal-space axiom, or residual-Omega termination theorem
is used.
-/

def originTrit (n : Nat) : Nat := n % 3

def originTail (n : Nat) : Nat := n / 3

/-- Exact one-trit decomposition of an ordinary natural origin. -/
theorem origin_split_exact (n : Nat) :
    n = originTrit n + 3 * originTail n := by
  unfold originTrit originTail
  have h := Nat.mod_add_div n 3
  omega

/-- The kernel-grade content of the handwritten simultaneous x/div U symbol:
all perfect-power energy is conserved while one ternary origin trit is consumed
into the left phase factor and the remaining origin moves to level `t+1`. -/
theorem perfect_power_u_mul_div_exact (t n : Nat) :
    4^(3^t * n) =
      4^(3^t * originTrit n) *
        4^(3^(t+1) * originTail n) := by
  have hs := origin_split_exact n
  have hexp :
      3^t * n =
        3^t * originTrit n + 3^(t+1) * originTail n := by
    calc
      3^t * n = 3^t * (originTrit n + 3 * originTail n) :=
        congrArg (fun x : Nat => 3^t * x) hs
      _ = 3^t * originTrit n + 3^(t+1) * originTail n := by
        rw [Nat.pow_succ]
        ring
  rw [hexp, Nat.pow_add]

/-- Exact residual child energy used by the production prefix/cascade socket. -/
def residualEnergy (s k m : Nat) : Nat :=
  4^(3^(s+k) * m)

/-- One canonical horizontal parent block has width `3^s`. -/
def residualWidth (s : Nat) : Nat := 3^s

/-- Absolute perfect-power exponent of the residual child. -/
def residualChildExponent (s k m : Nat) : Nat := 3^(s+k) * m

/-- Absolute exponent after crossing the one-block parent displacement. -/
def residualParentExponent (s k m : Nat) : Nat :=
  3^s * (1 + 3^k * m)

/-- Handwritten U factorization specialized to the residual child energy. -/
theorem residual_energy_u_mul_div_exact (s k m : Nat) :
    residualEnergy s k m =
      4^(3^(s+k) * originTrit m) *
        4^(3^(s+k+1) * originTail m) := by
  simpa [residualEnergy] using perfect_power_u_mul_div_exact (s+k) m

/-- The right edge of the physical width-`3^s` rectangle is exactly the
canonical parent perfect power `4^(3^s*(1+3^k*m))`. -/
theorem residual_parent_energy_exact (s k m : Nat) :
    4^(residualWidth s) * residualEnergy s k m =
      4^(residualParentExponent s k m) := by
  unfold residualWidth residualEnergy residualParentExponent
  rw [← Nat.pow_add]
  congr 1
  rw [Nat.pow_add]
  ring

/-- Advanced handwritten application: after the parent block is attached, the
same exact U split survives.  The consumed origin trit is retained in the left
perfect-power phase; the unconsumed tail remains an exact level-`s+k+1` power. -/
theorem residual_parent_u_mul_div_exact (s k m : Nat) :
    4^(residualParentExponent s k m) =
      (4^(3^s) * 4^(3^(s+k) * originTrit m)) *
        4^(3^(s+k+1) * originTail m) := by
  calc
    4^(residualParentExponent s k m) =
        4^(residualWidth s) * residualEnergy s k m :=
      (residual_parent_energy_exact s k m).symm
    _ = 4^(3^s) *
        (4^(3^(s+k) * originTrit m) *
          4^(3^(s+k+1) * originTail m)) := by
      rw [residualWidth, residual_energy_u_mul_div_exact]
    _ = (4^(3^s) * 4^(3^(s+k) * originTrit m)) *
        4^(3^(s+k+1) * originTail m) := by
      ac_rfl

/-- Full Graph-V2 realization of the same identity.  Every physical observable
at the alleged all-bad right boundary is literally the absolute perfect-power
sheet at the canonical parent exponent. -/
theorem residual_parent_observables_exact
    (s k m p : Nat) :
    (graph (residualEnergy s k m) (residualWidth s) p).seven.carry =
        (graph 1 (residualParentExponent s k m) p).seven.carry ∧
    (graph (residualEnergy s k m) (residualWidth s) p).seven.digit =
        (graph 1 (residualParentExponent s k m) p).seven.digit ∧
    (graph (residualEnergy s k m) (residualWidth s) p).eventCode =
        (graph 1 (residualParentExponent s k m) p).eventCode ∧
    (graph (residualEnergy s k m) (residualWidth s) p).uCharge =
        (graph 1 (residualParentExponent s k m) p).uCharge ∧
    (graph (residualEnergy s k m) (residualWidth s) p).mixedCharge =
        (graph 1 (residualParentExponent s k m) p).mixedCharge ∧
    (graph (residualEnergy s k m) (residualWidth s) p).crossingCharge =
        (graph 1 (residualParentExponent s k m) p).crossingCharge ∧
    (graph (residualEnergy s k m) (residualWidth s) p).survive =
        (graph 1 (residualParentExponent s k m) p).survive := by
  have h := power_origin_observables_exact
    (residualChildExponent s k m) (residualWidth s) p
  have hexp :
      residualChildExponent s k m + residualWidth s =
        residualParentExponent s k m := by
    unfold residualChildExponent residualWidth residualParentExponent
    rw [Nat.pow_add]
    ring
  rw [hexp] at h
  simpa [residualEnergy, residualChildExponent] using h

/-- Happy/event-eight transport at the actual residual parent boundary. -/
theorem residual_parent_happy_iff
    (s k m p : Nat) :
    HappyCell
        (graph (residualEnergy s k m) (residualWidth s) p).seven.carry
        (graph (residualEnergy s k m) (residualWidth s) p).seven.digit ↔
      HappyCell
        (graph 1 (residualParentExponent s k m) p).seven.carry
        (graph 1 (residualParentExponent s k m) p).seven.digit := by
  rw [(residual_parent_observables_exact s k m p).1,
      (residual_parent_observables_exact s k m p).2.1]

#check origin_split_exact
#check perfect_power_u_mul_div_exact
#check residual_energy_u_mul_div_exact
#check residual_parent_energy_exact
#check residual_parent_u_mul_div_exact
#check residual_parent_observables_exact
#check residual_parent_happy_iff
#print axioms perfect_power_u_mul_div_exact
#print axioms residual_parent_u_mul_div_exact
#print axioms residual_parent_observables_exact

end GSTGraphV2HandwrittenOmegaUBlock
