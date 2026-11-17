import GSTGraphV2InfiniteControl
import GSTGraphV2HandwrittenExponentialLTE
import GSTGraphV2PerfectPowerBlockCollision

set_option maxRecDepth 1000000
set_option maxHeartbeats 10000000

namespace GSTPrefixOneU2DCollisionProof

open GSTCanonicalSevenAxisBridge
open GSTU2DEventTransport
open GSTGraphV2InfiniteControl
open GSTGraphV2HandwrittenExponentialLTE
open GSTGraphV2PerfectPowerBlock

/-- Canonical child full power used by the prefix-one descent seam. -/
def childEnergy (s n : Nat) : Nat := 4^(3^(s+1) * n)

/-- Tail exposed at the production cut `s+2`. -/
def childTail (s n : Nat) : Nat := childEnergy s n / 3^(s+2)

/-- The pure child power has literal low prefix one at the production cut. -/
theorem child_energy_decomposition (s n : Nat) :
    childEnergy s n = 1 + 3^(s+2) * childTail s n := by
  have hmod : childEnergy s n % 3^(s+2) = 1 := by
    dsimp [childEnergy]
    simpa [Nat.add_assoc] using
      (pow4_scaled_mod_next (s+1) n)
  have hsplit := (Nat.mod_add_div (childEnergy s n) (3^(s+2))).symm
  rw [hmod] at hsplit
  simpa [childTail] using hsplit

/-- First production adapter: a Happy gate of the quotient child is literally
    a Happy cell on the full-power graph at vertical coordinate `s+2+q`. -/
theorem child_tail_happy_to_graph
    (s n q : Nat) (hs : 1 ≤ s)
    (hHappy : HappyCell (carry4 (childTail s n) q) (digit3 (childTail s n) q)) :
    HappyCell
      (graph (childEnergy s n) 0 (s+2+q)).seven.carry
      (graph (childEnergy s n) 0 (s+2+q)).seven.digit := by
  have hE :
      4^0 * childEnergy s n = 1 + 3^(s+2) * childTail s n := by
    simpa using child_energy_decomposition s n
  have hpow : 3^3 ≤ 3^(s+2) := by
    exact Nat.pow_le_pow_of_le (by decide : 1 < 3) (by omega)
  have hP : 1 < 3^(s+2) := by omega
  have h4 : 4 < 3^(s+2) := by
    norm_num at hpow ⊢
    omega
  have hiff :=
    graph_prefix_slice_happy_iff
      (childEnergy s n) 0 (s+2) 1 (childTail s n) q hE hP
  apply hiff.mpr
  rcases hHappy with ⟨hd, hc⟩
  constructor
  · exact hd
  · have hseed : (4 * 1) / 3^(s+2) = 0 := Nat.div_eq_of_lt (by simpa using h4)
    simpa [hseed, seededCarry, carry4] using hc

/-- The child production slice begins with the true zero x4 carry. -/
theorem child_base_carry_zero
    (s n : Nat) (hs : 1 ≤ s) :
    (graph (childEnergy s n) 0 (s+2)).seven.carry = 0 := by
  have hmod : childEnergy s n % 3^(s+2) = 1 := by
    dsimp [childEnergy]
    simpa [Nat.add_assoc] using
      (pow4_scaled_mod_next (s+1) n)
  have hpow : 3^3 ≤ 3^(s+2) := by
    exact Nat.pow_le_pow_of_le (by decide : 1 < 3) (by omega)
  have h4 : 4 < 3^(s+2) := by
    norm_num at hpow ⊢
    omega
  simp [graph, cell, GSTCanonicalSevenAxisBridge.vertex, carry4, hmod,
    Nat.div_eq_of_lt h4]

/-- Abstract parent adapter.  Whenever a low prefix generates seed one at the
    production cut, complete seed-one badness of the exposed tail is exactly
    complete physical badness of that Graph-V2 right edge. -/
theorem seeded_one_bad_to_graph_right_bad
    (E t b P tail : Nat)
    (hE : 4^t * E = P + 3^b * tail)
    (hP : P < 3^b)
    (hseed : (4 * P) / 3^b = 1)
    (hBad : ∀ q,
      ¬ HappyCell (seededCarry 1 tail q) (digit3 tail q)) :
    ∀ q,
      ¬ HappyCell
        (graph E t (b+q)).seven.carry
        (graph E t (b+q)).seven.digit := by
  intro q hGraph
  have hiff := graph_prefix_slice_happy_iff E t b P tail q hE hP
  have hTail := hiff.mp hGraph
  apply hBad q
  simpa [HappyCell, hseed] using hTail

/-- The low prefix of the canonical phase-one/right boundary. -/
def rightPrefix (s : Nat) : Nat := 1 + 3^(s+1)

/-- The exact seed-one information tail exposed on the phase-one/right edge. -/
def rightTail (s n z : Nat) : Nat :=
  z + 4^(3^s) * childTail s n

/-- Exact canonical phase-one decomposition.  The hypotheses are precisely the
    frozen LTE/unit-prefix identities used by the monolith, so no coefficient
    identification theorem or surrogate tail is required. -/
theorem right_energy_decomposition
    (s n c z : Nat)
    (hLTE : 4^(3^s) = 1 + 3^(s+1) * c)
    (hc : c = 1 + 3*z) :
    4^(3^s) * childEnergy s n =
      rightPrefix s + 3^(s+2) * rightTail s n z := by
  rw [child_energy_decomposition]
  unfold rightPrefix rightTail
  rw [hLTE, hc, show s + 2 = (s+1)+1 by omega, Nat.pow_succ]
  ring

/-- The canonical right prefix lies strictly below its production cut. -/
theorem rightPrefix_lt_cut
    (s : Nat) (hs : 1 ≤ s) :
    rightPrefix s < 3^(s+2) := by
  unfold rightPrefix
  rw [show s + 2 = (s+1)+1 by omega, Nat.pow_succ]
  have hpos : 0 < 3^(s+1) := Nat.pow_pos (by decide)
  omega

/-- Four times the canonical right prefix generates exactly incoming seed one
    at the production cut. -/
theorem rightPrefix_seed_one
    (s : Nat) (hs : 1 ≤ s) :
    (4 * rightPrefix s) / 3^(s+2) = 1 := by
  have h9 : 9 ≤ 3^(s+1) := by
    rw [show (9:Nat) = 3^2 by decide]
    exact Nat.pow_le_pow_of_le (by decide : 1 < 3) (by omega)
  have hden : 0 < 3^(s+2) := Nat.pow_pos (by decide)
  have hlo : 3^(s+2) ≤ 4 * rightPrefix s := by
    unfold rightPrefix
    rw [show s + 2 = (s+1)+1 by omega, Nat.pow_succ]
    omega
  have hhi : 4 * rightPrefix s < 2 * 3^(s+2) := by
    unfold rightPrefix
    rw [show s + 2 = (s+1)+1 by omega, Nat.pow_succ]
    omega
  have hlo' : 1 ≤ (4 * rightPrefix s) / 3^(s+2) := by
    exact (Nat.le_div_iff_mul_le hden).2 (by simpa using hlo)
  have hhi' : (4 * rightPrefix s) / 3^(s+2) < 2 := by
    exact (Nat.div_lt_iff_lt_mul hden).2 (by simpa using hhi)
  omega

/-- Canonical specialization of the abstract right-edge adapter.  A complete
    seed-one bad language of the actual phase-one tail is exactly an all-depth
    bad physical right boundary of the same finite-width perfect-power sheet. -/
theorem canonical_right_bad_to_graph_right_bad
    (s n c z : Nat) (hs : 1 ≤ s)
    (hLTE : 4^(3^s) = 1 + 3^(s+1) * c)
    (hc : c = 1 + 3*z)
    (hBad : ∀ q,
      ¬ HappyCell
        (seededCarry 1 (rightTail s n z) q)
        (digit3 (rightTail s n z) q)) :
    ∀ q,
      ¬ HappyCell
        (graph (childEnergy s n) (3^s) (s+2+q)).seven.carry
        (graph (childEnergy s n) (3^s) (s+2+q)).seven.digit := by
  apply seeded_one_bad_to_graph_right_bad
    (childEnergy s n) (3^s) (s+2)
    (rightPrefix s) (rightTail s n z)
  · exact right_energy_decomposition s n c z hLTE hc
  · exact rightPrefix_lt_cut s hs
  · exact rightPrefix_seed_one s hs
  · exact hBad

/-- Truthful prefix-one adapter into the certified terminal n-wave packet.
No collision or contradiction is asserted. -/
theorem canonical_prefix_one_u2d_terminal_packet
    (s n c z q : Nat) (hs : 1 ≤ s) (hn : 1 ≤ n)
    (hLTE : 4^(3^s) = 1 + 3^(s+1) * c)
    (hc : c = 1 + 3*z)
    (hChild : HappyCell
      (carry4 (childTail s n) q)
      (digit3 (childTail s n) q))
    (hBad : ∀ j,
      ¬ HappyCell
        (seededCarry 1 (rightTail s n z) j)
        (digit3 (rightTail s n z) j)) :
    HappyCell
        (graph 1
          (GSTGraphV2CanonicalNWave.nWaveShift s n (n+1)) (s+2+q)).seven.carry
        (graph 1
          (GSTGraphV2CanonicalNWave.nWaveShift s n (n+1)) (s+2+q)).seven.digit ∧
      ∀ j, ¬ HappyCell
        (graph 1
          (GSTGraphV2CanonicalNWave.nWaveShift s n (n+1) + canonicalWidth s)
          (s+2+j)).seven.carry
        (graph 1
          (GSTGraphV2CanonicalNWave.nWaveShift s n (n+1) + canonicalWidth s)
          (s+2+j)).seven.digit := by
  have hChildGraph := child_tail_happy_to_graph s n q hs hChild
  have hRightGraph :=
    canonical_right_bad_to_graph_right_bad s n c z hs hLTE hc hBad
  exact GSTGraphV2PerfectPowerBlockCollision.canonical_perfect_power_block_terminal_packet
    s n q hs hn
    (by
      simpa [childEnergy, canonicalEnergy] using hChildGraph)
    (by
      intro j
      simpa [childEnergy, canonicalEnergy, canonicalWidth] using hRightGraph j)

#print axioms child_energy_decomposition
#print axioms child_tail_happy_to_graph
#print axioms child_base_carry_zero
#print axioms seeded_one_bad_to_graph_right_bad
#print axioms right_energy_decomposition
#print axioms rightPrefix_lt_cut
#print axioms rightPrefix_seed_one
#print axioms canonical_right_bad_to_graph_right_bad
#print axioms canonical_prefix_one_u2d_terminal_packet

end GSTPrefixOneU2DCollisionProof
