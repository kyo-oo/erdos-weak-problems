import GSTGraphV2HandwrittenOmegaUBlock

set_option maxRecDepth 1000000
set_option maxHeartbeats 10000000

namespace GSTGraphV2HandwrittenExponentialCascade

open GSTCanonicalSevenAxisBridge
open GSTGraphV2InfiniteControl
open GSTGraphV2PerfectPowerAncestry
open GSTGraphV2HandwrittenOmegaUBlock

/-!
# Advanced handwritten exponential cascade

The leading repeated/exponential operator from the handwritten theorem is
formalized as a finite family indexed by `K : Nat`.  For an ordinary natural
origin this is stronger than postulating an analytic limit: after enough
iterations the remaining ternary origin tail is literally zero.

At depth `K` the already-consumed ternary prefix becomes a horizontal
perfect-power phase, while the unconsumed suffix becomes a level-`t+K`
perfect-power energy.  Equation I (navigation/nullspace flux) is then applied
to the same arithmetic energy, producing one exact 2D horizontal/vertical
certificate on the full Graph-V2 sheet.
-/

def originPrefix (n K : Nat) : Nat := n % 3^K

def originSuffix (n K : Nat) : Nat := n / 3^K

def uPhaseShift (t n K : Nat) : Nat := 3^t * originPrefix n K

def uTailExponent (t n K : Nat) : Nat := 3^(t+K) * originSuffix n K

def uTailEnergy (t n K : Nat) : Nat := 4^(uTailExponent t n K)

/-- Exact K-trit decomposition of a natural origin. -/
theorem origin_block_split_exact (n K : Nat) :
    n = originPrefix n K + 3^K * originSuffix n K := by
  unfold originPrefix originSuffix
  have h := Nat.mod_add_div n (3^K)
  omega

/-- Exponent form of the repeated handwritten U operation. -/
theorem u_exponent_block_split_exact (t n K : Nat) :
    3^t * n = uPhaseShift t n K + uTailExponent t n K := by
  have hs := origin_block_split_exact n K
  unfold uPhaseShift uTailExponent
  calc
    3^t * n =
        3^t * (originPrefix n K + 3^K * originSuffix n K) :=
      congrArg (fun x : Nat => 3^t * x) hs
    _ = 3^t * originPrefix n K +
        3^(t+K) * originSuffix n K := by
      rw [Nat.pow_add]
      ring

/-- Advanced finite product form of the handwritten exponential operator.
Every consumed origin trit has been accumulated into the left phase factor;
the right factor is the still-live higher-level origin. -/
theorem perfect_power_u_block_exact (t n K : Nat) :
    4^(3^t * n) =
      4^(uPhaseShift t n K) * uTailEnergy t n K := by
  rw [u_exponent_block_split_exact, Nat.pow_add]
  rfl

/-- The same U split after an arbitrary Graph-V2 horizontal displacement. -/
theorem u_absolute_energy_exact (t n K x : Nat) :
    4^x * 4^(3^t * n) =
      4^(uPhaseShift t n K + x) * uTailEnergy t n K := by
  rw [perfect_power_u_block_exact]
  rw [Nat.pow_add]
  ring

/-- Full physical-observable transport on the enriched Graph-V2 sheet.

The seven-axis horizontal coordinate is translated by `uPhaseShift`; all
physical state observables (carry/space information through carry, digit,
event, U, mixed, crossing and SURVIVE) are unchanged because both sides are
the same absolute perfect-power energy. -/
theorem graph_u_block_observables_exact
    (t n K x p : Nat) :
    (graph (4^(3^t*n)) x p).seven.carry =
        (graph (uTailEnergy t n K) (uPhaseShift t n K + x) p).seven.carry ∧
    (graph (4^(3^t*n)) x p).seven.digit =
        (graph (uTailEnergy t n K) (uPhaseShift t n K + x) p).seven.digit ∧
    (graph (4^(3^t*n)) x p).seven.space =
        (graph (uTailEnergy t n K) (uPhaseShift t n K + x) p).seven.space ∧
    (graph (4^(3^t*n)) x p).seven.descent =
        (graph (uTailEnergy t n K) (uPhaseShift t n K + x) p).seven.descent ∧
    (graph (4^(3^t*n)) x p).seven.nextDescent =
        (graph (uTailEnergy t n K) (uPhaseShift t n K + x) p).seven.nextDescent ∧
    (graph (4^(3^t*n)) x p).eventCode =
        (graph (uTailEnergy t n K) (uPhaseShift t n K + x) p).eventCode ∧
    (graph (4^(3^t*n)) x p).uCharge =
        (graph (uTailEnergy t n K) (uPhaseShift t n K + x) p).uCharge ∧
    (graph (4^(3^t*n)) x p).mixedCharge =
        (graph (uTailEnergy t n K) (uPhaseShift t n K + x) p).mixedCharge ∧
    (graph (4^(3^t*n)) x p).crossingCharge =
        (graph (uTailEnergy t n K) (uPhaseShift t n K + x) p).crossingCharge ∧
    (graph (4^(3^t*n)) x p).survive =
        (graph (uTailEnergy t n K) (uPhaseShift t n K + x) p).survive := by
  have hE := u_absolute_energy_exact t n K x
  simp [graph, cell, GSTCanonicalSevenAxisBridge.vertex,
    uTailEnergy, hE]

/-- Exact horizontal-axis part of the same seven-axis transport. -/
theorem graph_u_block_horizontal_axes_exact
    (t n K x p : Nat) :
    (graph (uTailEnergy t n K) (uPhaseShift t n K + x) p).seven.horizontal =
        uPhaseShift t n K + (graph (4^(3^t*n)) x p).seven.horizontal ∧
    (graph (uTailEnergy t n K) (uPhaseShift t n K + x) p).seven.horizontalNext =
        uPhaseShift t n K + (graph (4^(3^t*n)) x p).seven.horizontalNext ∧
    (graph (uTailEnergy t n K) (uPhaseShift t n K + x) p).seven.vertical =
        (graph (4^(3^t*n)) x p).seven.vertical := by
  simp [graph, cell, GSTCanonicalSevenAxisBridge.vertex, Nat.add_assoc]

/-- Equation-I nullspace residue for one exact absolute graph energy. -/
def navigationNullspace (R p : Nat) : Nat :=
  (4 * (R % 3^p)) % 3^p

/-- Handwritten Equation I on an arbitrary Graph-V2 cell: the visible x4
remainder splits exactly into the vertical carry and unresolved nullspace. -/
theorem graph_navigation_nullspace_flux_exact
    (E x p : Nat) :
    4 * ((4^x * E) % 3^p) =
      navigationNullspace (4^x * E) p +
        3^p * (graph E x p).seven.carry := by
  unfold navigationNullspace
  change 4 * ((4^x * E) % 3^p) =
    (4 * ((4^x * E) % 3^p)) % 3^p +
      3^p * ((4 * ((4^x * E) % 3^p)) / 3^p)
  exact (Nat.mod_add_div (4 * ((4^x * E) % 3^p)) (3^p)).symm

/-- **Combined advanced application.**  The repeated handwritten exponential
operator performs the horizontal origin-prefix phase shift, while Equation I
reads the vertical navigation/nullspace flux of that exact same transported
energy.  This is a genuine 2D Graph-V2 identity rather than an isolated
factorization. -/
theorem handwritten_exponential_navigation_flux_exact
    (t n K x p : Nat) :
    4 * ((4^(uPhaseShift t n K + x) * uTailEnergy t n K) % 3^p) =
      navigationNullspace
          (4^(uPhaseShift t n K + x) * uTailEnergy t n K) p +
        3^p * (graph (4^(3^t*n)) x p).seven.carry := by
  have hAbs := u_absolute_energy_exact t n K x
  have hFlux := graph_navigation_nullspace_flux_exact (4^(3^t*n)) x p
  rw [hAbs] at hFlux
  exact hFlux

/-- Every natural origin is exhausted by a finite member of the handwritten
K→∞ family.  This is ordinary finite-support arithmetic, not a terminal-space
axiom. -/
theorem nat_lt_three_pow_succ : ∀ n : Nat, n < 3^(n+1)
  | 0 => by decide
  | n+1 => by
      have ih := nat_lt_three_pow_succ n
      rw [show n+1+1 = (n+1)+1 by omega, Nat.pow_succ]
      have hp : 0 < 3^(n+1) := Nat.pow_pos (by decide)
      omega

/-- The unconsumed natural origin tail is literally zero by depth n+1. -/
theorem originSuffix_eventually_zero (n : Nat) :
    originSuffix n (n+1) = 0 := by
  unfold originSuffix
  exact Nat.div_eq_of_lt (nat_lt_three_pow_succ n)

/-- Therefore the remaining perfect-power factor of the repeated U operation
is exactly one at that finite depth. -/
theorem uTailEnergy_eventually_one (t n : Nat) :
    uTailEnergy t n (n+1) = 1 := by
  simp [uTailEnergy, uTailExponent, originSuffix_eventually_zero]


/-! ## Intrinsic finite-cut semigroup -/

/-- Successive origin suffixes compose exactly at arbitrary cut depths. -/
theorem originSuffix_add_exact (n K L : Nat) :
    originSuffix n (K+L) =
      originSuffix (originSuffix n K) L := by
  unfold originSuffix
  rw [pow_add, ← Nat.div_div_eq_div_mul]

/-- The consumed prefix of a composite cut is the old prefix plus the newly
exposed prefix of the old suffix at its exact ternary weight. -/
theorem originPrefix_add_exact (n K L : Nat) :
    originPrefix n (K+L) =
      originPrefix n K +
        3^K * originPrefix (originSuffix n K) L := by
  unfold originPrefix originSuffix
  rw [pow_add, Nat.mod_mul]

/-- Horizontal U phase is a cocycle under successive finite cuts. -/
theorem uPhaseShift_add_exact (t n K L : Nat) :
    uPhaseShift t n (K+L) =
      uPhaseShift t n K +
        uPhaseShift (t+K) (originSuffix n K) L := by
  unfold uPhaseShift
  rw [originPrefix_add_exact, pow_add]
  ring

/-- Tail exponents form the corresponding residual semigroup. -/
theorem uTailExponent_add_exact (t n K L : Nat) :
    uTailExponent t n (K+L) =
      uTailExponent (t+K) (originSuffix n K) L := by
  unfold uTailExponent
  rw [originSuffix_add_exact]
  simp [Nat.add_assoc]

/-- Tail energies therefore compose by literal equality under successive
renormalization. -/
theorem uTailEnergy_add_exact (t n K L : Nat) :
    uTailEnergy t n (K+L) =
      uTailEnergy (t+K) (originSuffix n K) L := by
  unfold uTailEnergy
  rw [uTailExponent_add_exact]

/-- Any cut beyond the explicit natural support depth consumes the whole
origin. -/
theorem originSuffix_zero_of_large_cut
    (n K : Nat) (hK : n+1 ≤ K) :
    originSuffix n K = 0 := by
  unfold originSuffix
  have hpow0 : n < 3^(n+1) := nat_lt_three_pow_succ n
  have hpowle : 3^(n+1) ≤ 3^K :=
    Nat.pow_le_pow_right (by decide) hK
  exact Nat.div_eq_of_lt (lt_of_lt_of_le hpow0 hpowle)

/-- Consequently every sufficiently deep residual U world is the unit world. -/
theorem uTailEnergy_one_of_large_cut
    (t n K : Nat) (hK : n+1 ≤ K) :
    uTailEnergy t n K = 1 := by
  simp [uTailEnergy, uTailExponent, originSuffix_zero_of_large_cut n K hK]


#check origin_block_split_exact
#check perfect_power_u_block_exact
#check graph_u_block_observables_exact
#check graph_u_block_horizontal_axes_exact
#check graph_navigation_nullspace_flux_exact
#check handwritten_exponential_navigation_flux_exact
#check originSuffix_eventually_zero
#check uTailEnergy_eventually_one
#check originSuffix_add_exact
#check originPrefix_add_exact
#check uPhaseShift_add_exact
#check uTailExponent_add_exact
#check uTailEnergy_add_exact
#check originSuffix_zero_of_large_cut
#check uTailEnergy_one_of_large_cut
#print axioms perfect_power_u_block_exact
#print axioms graph_u_block_observables_exact
#print axioms handwritten_exponential_navigation_flux_exact
#print axioms uPhaseShift_add_exact
#print axioms uTailEnergy_add_exact
#print axioms uTailEnergy_one_of_large_cut

end GSTGraphV2HandwrittenExponentialCascade
