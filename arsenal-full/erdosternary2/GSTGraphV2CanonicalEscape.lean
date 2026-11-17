import GSTGraphV2CanonicalRenormalization
import GSTGraphV2InfiniteControllerBridge
import GSTFinalPrefixOneStep6Infinite
import GSTGraphV2CanonicalDescentOntology
import GSTGraphV2HandwrittenAnchoredCocycle

set_option maxRecDepth 1000000
set_option maxHeartbeats 20000000

namespace GSTGraphV2CanonicalEscape

open GSTCanonicalSevenAxisBridge
open GSTU2DEventTransport
open GSTPerfectPowerTailNavigation
open GSTPrefixOneSeedCore
open GSTGraphV2InfiniteControl
open GSTGraphV2InfiniteControllerBridge
open GSTGraphV2CoupledUFlux
open GSTGraphV2SeededPrefix
open GSTGraphV2CanonicalRenormalization
open GSTGraphV2CanonicalDescentOntology
open GSTGraphV2PerfectPowerBlock
open GSTGraphV2HandwrittenExponentialCascade
open GSTGraphV2HandwrittenAnchoredCocycle

/-- The canonical child after removing its forced low prefix. -/
def canonicalChildTail (s n : Nat) : Nat :=
  canonicalTail (s+1) n

/-- The exact unconsumed seed-one parent tail. -/
def canonicalParentTail (s n : Nat) : Nat :=
  prefixOffset s + 4^(3^s) * canonicalChildTail s n

/-- Exact low-prefix decomposition at the child boundary. -/
theorem canonical_child_energy_decomposition
    (s n : Nat) :
    4^(3^(s+1) * n) =
      1 + 3^(s+2) * canonicalChildTail s n := by
  simpa [canonicalChildTail, Nat.add_assoc] using
    canonical_tail_decomposition (s+1) n

/-- Exact low-prefix decomposition one canonical horizontal block to the
right.  This is the arithmetic adapter consumed by the all-depth controller. -/
theorem canonical_parent_energy_decomposition
    (s n : Nat) :
    4^(3^s) * 4^(3^(s+1) * n) =
      (1 + 3^(s+1)) + 3^(s+2) * canonicalParentTail s n := by
  have hpow :
      4^(3^s) * 4^(3^(s+1) * n) =
        4^(3^s * (1 + 3*n)) := by
    rw [← Nat.pow_add]
    congr 1
    rw [Nat.pow_succ]
    ring
  have hcanon := canonical_tail_decomposition s (1 + 3*n)
  rw [canonicalTail_one_strip] at hcanon
  rw [hpow, hcanon]
  unfold canonicalParentTail canonicalChildTail
  rw [show s+2 = (s+1)+1 by omega, Nat.pow_succ]
  ring


private theorem canonical_cut_gt_four
    (s : Nat) (hs : 1 ≤ s) :
    4 < 3^(s+2) := by
  have h27 : 27 ≤ 3^(s+2) := by
    rw [show (27 : Nat) = 3^3 by decide]
    exact Nat.pow_le_pow_of_le (by decide : 1 < 3) (by omega)
  omega

private theorem canonical_right_prefix_lt_cut
    (s : Nat) (hs : 1 ≤ s) :
    1 + 3^(s+1) < 3^(s+2) := by
  rw [show s+2 = (s+1)+1 by omega, Nat.pow_succ]
  have hp : 0 < 3^(s+1) := by positivity
  omega

private theorem canonical_right_prefix_seed_one
    (s : Nat) (hs : 1 ≤ s) :
    (4 * (1 + 3^(s+1))) / 3^(s+2) = 1 := by
  have h9 : 9 ≤ 3^(s+1) := by
    rw [show (9 : Nat) = 3^2 by decide]
    exact Nat.pow_le_pow_of_le (by decide : 1 < 3) (by omega)
  have hden : 0 < 3^(s+2) := by positivity
  have hlo : 3^(s+2) ≤ 4 * (1 + 3^(s+1)) := by
    rw [show s+2 = (s+1)+1 by omega, Nat.pow_succ]
    omega
  have hhi : 4 * (1 + 3^(s+1)) < 2 * 3^(s+2) := by
    rw [show s+2 = (s+1)+1 by omega, Nat.pow_succ]
    omega
  have hlo' : 1 ≤ (4 * (1 + 3^(s+1))) / 3^(s+2) := by
    exact (Nat.le_div_iff_mul_le hden).2 (by simpa using hlo)
  have hhi' : (4 * (1 + 3^(s+1))) / 3^(s+2) < 2 := by
    exact (Nat.div_lt_iff_lt_mul hden).2 (by simpa using hhi)
  omega

/-- The physical canonical left boundary is exactly the lossless seed-zero
child state. -/
theorem canonical_left_seed_adapter
    (s n q : Nat) (hs : 1 ≤ s) :
    HappyCell
        (graph (4^(3^(s+1) * n)) 0 (s+2+q)).seven.carry
        (graph (4^(3^(s+1) * n)) 0 (s+2+q)).seven.digit ↔
      SeedHappy 0 0 (canonicalChildTail s n) q := by
  have hE :
      4^0 * 4^(3^(s+1) * n) =
        1 + 3^(s+2) * canonicalChildTail s n := by
    simpa using canonical_child_energy_decomposition s n
  have hP : 1 < 3^(s+2) := by
    exact lt_trans (by decide : 1 < 4) (canonical_cut_gt_four s hs)
  have h := graph_prefix_slice_happy_iff
    (4^(3^(s+1) * n)) 0 (s+2) 1 (canonicalChildTail s n) q hE hP
  have hseed : (4 * 1) / 3^(s+2) = 0 :=
    Nat.div_eq_of_lt (canonical_cut_gt_four s hs)
  rw [hseed] at h
  rw [seedHappy_zero_iff]
  simpa [HappyCell, GSTGraphV2InfiniteControl.seededCarry,
    GSTCanonicalSevenAxisBridge.carry4,
    GSTCanonicalSevenAxisBridge.digit3] using h

/-- The physical canonical right boundary is exactly the lossless seed-one
parent state; the complete low prefix is retained. -/
theorem canonical_right_seed_adapter
    (s n q : Nat) (hs : 1 ≤ s) :
    HappyCell
        (graph (4^(3^(s+1) * n)) (3^s) (s+2+q)).seven.carry
        (graph (4^(3^(s+1) * n)) (3^s) (s+2+q)).seven.digit ↔
      SeedHappy 1 1 (canonicalParentTail s n) q := by
  have hE :
      4^(3^s) * 4^(3^(s+1) * n) =
        (1 + 3^(s+1)) + 3^(s+2) * canonicalParentTail s n :=
    canonical_parent_energy_decomposition s n
  have h := graph_prefix_slice_happy_iff
    (4^(3^(s+1) * n)) (3^s) (s+2)
    (1 + 3^(s+1)) (canonicalParentTail s n) q hE
    (canonical_right_prefix_lt_cut s hs)
  have hseed := canonical_right_prefix_seed_one s hs
  rw [seedHappy_one_iff]
  simpa [HappyCell, hseed] using h


/-- Exact U-jump adapter for the physical canonical left boundary. -/
theorem canonical_left_u_jump_adapter
    (s n j : Nat) (hs : 1 ≤ s) :
    gstUJumpExact
        (graph (4^(3^(s+1) * n)) 0 (s+2+j)).seven.carry
        (graph (4^(3^(s+1) * n)) 0 (s+2+j)).seven.digit =
      gstUJumpExact
        (GSTV2.affineCarry 0 (canonicalChildTail s n) j)
        (GSTV2.digit (canonicalChildTail s n) j) := by
  have hE :
      4^0 * 4^(3^(s+1) * n) =
        1 + 3^(s+2) * canonicalChildTail s n := by
    simpa using canonical_child_energy_decomposition s n
  have hP : 1 < 3^(s+2) :=
    lt_trans (by decide : 1 < 4) (canonical_cut_gt_four s hs)
  have hslice := graph_prefix_slice_exact
    (4^(3^(s+1) * n)) 0 (s+2) 1 (canonicalChildTail s n) j hE hP
  have hseed : (4 * 1) / 3^(s+2) = 0 :=
    Nat.div_eq_of_lt (canonical_cut_gt_four s hs)
  rw [hslice.1, hslice.2, hseed]
  rfl

/-- Exact U-jump adapter for the physical canonical right boundary. -/
theorem canonical_right_u_jump_adapter
    (s n j : Nat) (hs : 1 ≤ s) :
    gstUJumpExact
        (graph (4^(3^(s+1) * n)) (3^s) (s+2+j)).seven.carry
        (graph (4^(3^(s+1) * n)) (3^s) (s+2+j)).seven.digit =
      gstUJumpExact
        (GSTV2.affineCarry 1 (canonicalParentTail s n) j)
        (GSTV2.digit (canonicalParentTail s n) j) := by
  have hE :
      4^(3^s) * 4^(3^(s+1) * n) =
        (1 + 3^(s+1)) + 3^(s+2) * canonicalParentTail s n :=
    canonical_parent_energy_decomposition s n
  have hslice := graph_prefix_slice_exact
    (4^(3^(s+1) * n)) (3^s) (s+2)
      (1 + 3^(s+1)) (canonicalParentTail s n) j hE
      (canonical_right_prefix_lt_cut s hs)
  have hseed := canonical_right_prefix_seed_one s hs
  rw [hslice.1, hslice.2, hseed]
  rfl

/-- The canonical child begins the coupled controller with the true zero
carry, derived from the exact low prefix rather than assumed. -/
theorem canonical_base_carry_zero
    (s n : Nat) (hs : 1 ≤ s) :
    (graph (4^(3^(s+1) * n)) 0 (s+2)).seven.carry = 0 := by
  have hE :
      4^0 * 4^(3^(s+1) * n) =
        1 + 3^(s+2) * canonicalChildTail s n := by
    simpa using canonical_child_energy_decomposition s n
  have hP : 1 < 3^(s+2) := by
    exact lt_trans (by decide : 1 < 4) (canonical_cut_gt_four s hs)
  have hslice := graph_prefix_slice_exact
    (4^(3^(s+1) * n)) 0 (s+2) 1 (canonicalChildTail s n) 0 hE hP
  have hseed : (4 * 1) / 3^(s+2) = 0 :=
    Nat.div_eq_of_lt (canonical_cut_gt_four s hs)
  rw [hseed] at hslice
  simpa [GSTGraphV2InfiniteControl.seededCarry, Nat.mod_one] using hslice.2

/-- Existing all-depth bad control plus the exact canonical adapters produces
the live latent gate packet.  This is the certified controller input to the
remaining renormalized-escape step. -/
theorem canonical_latent_gate_packet
    (s n q : Nat) (hs : 1 ≤ s)
    (hChild : SeedHappy 0 0 (canonicalChildTail s n) q)
    (hRightBad : ∀ j,
      ¬ SeedHappy 1 1 (canonicalParentTail s n) j) :
    GSTV2.LatentGateTransfer
      (4^(3^s))
      (graphCoupledState
        (4^(3^(s+1) * n)) (3^s) (s+2))
      q := by
  apply graph_child_happy_latent_transfer
  · exact canonical_base_carry_zero s n hs
  · intro j hGraph
    exact hRightBad j ((canonical_right_seed_adapter s n j hs).mp hGraph)
  · exact (canonical_left_seed_adapter s n q hs).mpr hChild



/-- The exact low canonical contribution retained after cutting `K` origin
trits. -/
def canonicalCutOffset (r n K : Nat) : Nat :=
  canonicalTail r (n % 3^K) / 3^K

/-- Arbitrary-cutoff quotient form of canonical renormalization. -/
theorem canonicalTail_cut_quotient_exact
    (r n K : Nat) :
    canonicalTail r n / 3^K =
      canonicalCutOffset r n K +
        4^((n % 3^K) * 3^r) *
          canonicalTail (r+K) (n / 3^K) := by
  let d : Nat := 3^K
  let a : Nat := n % d
  let m : Nat := n / d
  have hpos : 0 < d := by
    dsimp [d]
    positivity
  have hn : n = a + d * m := by
    dsimp [a, m, d]
    exact (Nat.mod_add_div n (3^K)).symm
  have hRec :
      canonicalTail r n =
        canonicalTail r a +
          d * (4^(a * 3^r) * canonicalTail (r+K) m) := by
    rw [hn]
    simpa [d, Nat.mul_assoc] using
      canonicalTail_power_block_recurrence r a m K
  rw [hRec]
  change
    (canonicalTail r a +
      d * (4^(a * 3^r) * canonicalTail (r+K) m)) / d =
      canonicalCutOffset r n K +
        4^((n % 3^K) * 3^r) *
          canonicalTail (r+K) (n / 3^K)
  rw [Nat.add_mul_div_left _ _ hpos]
  rfl

/-- Graph-V2 ontological identification of the controller's live child packet
at every cutoff.  The finite low offset and renormalized canonical upper
origin remain explicit. -/
theorem canonical_controller_childTail_cut_exact
    (s n K : Nat) :
    let st := graphCoupledState
      (4^(3^(s+1) * n)) (3^s) (s+2)
    (GSTV2.coupledOrbit (4^(3^s)) st K).childTail =
      canonicalCutOffset (s+1) n K +
        4^((n % 3^K) * 3^(s+1)) *
          canonicalTail (s+1+K) (n / 3^K) := by
  dsimp only
  rw [GSTV2.coupledOrbit_childTail_exact]
  have hInitial :=
    canonical_graph_childTail_cut_exact s n
  have hInitial' :
      (graphCoupledState
        (4^(3^(s+1) * n)) (3^s) (s+2)).childTail =
        canonicalTail (s+1) n := by
    simpa [canonicalEnergy, canonicalWidth] using hInitial
  rw [hInitial']
  exact canonicalTail_cut_quotient_exact (s+1) n K

/-- Arbitrary-origin-cut re-coordination of both physical endpoints onto
one residual Graph-V2 sheet.  The consumed origin prefix remains as the exact
horizontal phase rather than being projected away. -/
theorem canonical_graph_u_cut_recoordinate_exact
    (s n K x p : Nat) :
    (graph (canonicalEnergy s n) x p).seven.carry =
        (graph (uTailEnergy (s+1) n K)
          (uPhaseShift (s+1) n K + x) p).seven.carry ∧
    (graph (canonicalEnergy s n) x p).seven.digit =
        (graph (uTailEnergy (s+1) n K)
          (uPhaseShift (s+1) n K + x) p).seven.digit := by
  have h := graph_u_block_observables_exact (s+1) n K x p
  simpa [canonicalEnergy] using ⟨h.1, h.2.1⟩

/-- Once the canonical origin suffix has terminated, the residual sheet is
literally the unit-energy Graph-V2 sheet.  The child/right endpoints and the
entire retained U potential are still connected by the exact horizontal
cocycle; no terminal boundary term is discarded. -/
theorem canonical_terminal_graph_u_packet
    (s n K p : Nat) (hterm : n / 3^K = 0) :
    let P := uPhaseShift (s+1) n K
    let N := canonicalWidth s
    (graph (canonicalEnergy s n) 0 p).seven.carry =
        (graph 1 P p).seven.carry ∧
    (graph (canonicalEnergy s n) 0 p).seven.digit =
        (graph 1 P p).seven.digit ∧
    (graph (canonicalEnergy s n) N p).seven.carry =
        (graph 1 (P+N) p).seven.carry ∧
    (graph (canonicalEnergy s n) N p).seven.digit =
        (graph 1 (P+N) p).seven.digit ∧
    graphUPotential 1 0 (P+N) p =
      graphUPotential 1 P N p +
        (((4^N : Nat) : Int)) * graphUPotential 1 0 P p := by
  dsimp only
  have hTail : uTailEnergy (s+1) n K = 1 := by
    simp [uTailEnergy, uTailExponent, originSuffix, hterm]
  have hChild := canonical_graph_u_cut_recoordinate_exact s n K 0 p
  have hRight :=
    canonical_graph_u_cut_recoordinate_exact s n K (canonicalWidth s) p
  refine ⟨?_, ?_, ?_, ?_, ?_⟩
  · simpa [hTail] using hChild.1
  · simpa [hTail] using hChild.2
  · simpa [hTail, Nat.add_assoc] using hRight.1
  · simpa [hTail, Nat.add_assoc] using hRight.2
  · simpa using graph_u_potential_cocycle_exact
      1 0 (uPhaseShift (s+1) n K) (canonicalWidth s) p

/-- The origin of the terminal unit-energy sheet is physically neutral above
the low two ternary places. -/
theorem terminal_unit_origin_neutral
    (p : Nat) (hp : 2 ≤ p) :
    (graph 1 0 p).seven.carry = 0 ∧
      (graph 1 0 p).seven.digit = 0 := by
  have h9 : 9 ≤ 3^p := by
    rw [show (9 : Nat) = 3^2 by decide]
    exact Nat.pow_le_pow_of_le (by decide : 1 < 3) hp
  have h4 : 4 < 3^p := by omega
  have h1 : 1 < 3^p := by omega
  constructor
  · simp [graph, cell, GSTCanonicalSevenAxisBridge.vertex, carry4,
      Nat.mod_eq_of_lt h1, Nat.div_eq_of_lt h4]
  · simp [graph, cell, GSTCanonicalSevenAxisBridge.vertex, digit3,
      Nat.div_eq_of_lt h1]

/-- The live controller packet has an exact arithmetic consequence: the child
canonical tail retains a nonzero residue through the row immediately after
the supplied Happy gate. -/
theorem canonical_child_residue_packet_nonzero
    (s n q : Nat) (hs : 1 ≤ s)
    (hChild : SeedHappy 0 0 (canonicalChildTail s n) q)
    (hRightBad : ∀ j,
      ¬ SeedHappy 1 1 (canonicalParentTail s n) j) :
    canonicalChildTail s n % 3^(q+1) ≠ 0 := by
  let E : Nat := 4^(3^(s+1) * n)
  let N : Nat := 3^s
  let b : Nat := s+2
  let st := graphCoupledState E N b
  have hRightGraph : ∀ j,
      ¬ HappyCell
        (graph E N (b+j)).seven.carry
        (graph E N (b+j)).seven.digit := by
    intro j hGraph
    apply hRightBad j
    apply (canonical_right_seed_adapter s n j hs).mp
    simpa [E, N, b, Nat.add_assoc] using hGraph
  have hControl : GSTV2.InfiniteBadCoupledControl (4^N) st := by
    dsimp [st]
    apply graph_infinite_bad_control
    · simpa [E, b] using canonical_base_carry_zero s n hs
    · exact hRightGraph
  have hLatent := canonical_latent_gate_packet s n q hs hChild hRightBad
  have hTail :
      E / 3^b = canonicalChildTail s n := by
    have hden : 0 < 3^b := by positivity
    have hsmall : 1 < 3^b := by
      dsimp [b]
      exact lt_trans (by decide : 1 < 4) (canonical_cut_gt_four s hs)
    rw [show E = 1 + 3^b * canonicalChildTail s n by
      simpa [E, b] using canonical_child_energy_decomposition s n]
    rw [Nat.add_mul_div_left _ _ hden]
    rw [Nat.div_eq_of_lt hsmall, Nat.zero_add]
  have hExact := hControl.childCarryExact (q+1)
  have hNonOrbit :
      (GSTV2.coupledOrbit (4^N) st (q+1)).childCarry ≠ 0 := by
    simpa [E, N, b, st] using hLatent.nextCarryNonzero
  have hNaturalState :
      GSTV2.naturalCarry st.childTail (q+1) ≠ 0 := by
    rw [← hExact]
    exact hNonOrbit
  have hNatural :
      GSTV2.naturalCarry (canonicalChildTail s n) (q+1) ≠ 0 := by
    simpa [st, graphCoupledState, hTail] using hNaturalState
  intro hzero
  apply hNatural
  simp [GSTV2.naturalCarry, hzero]


/-- Exact zero-phase iteration: every ternary power dividing the canonical
origin divides its canonical tail at the same depth. -/
theorem canonicalTail_pow_dvd_of_origin_pow_dvd
    (r n K : Nat) (hdiv : 3^K ∣ n) :
    3^K ∣ canonicalTail r n := by
  induction K generalizing r n with
  | zero => simp
  | succ K ih =>
      obtain ⟨m, rfl⟩ := hdiv
      have hshape :
          3^(K+1) * m = 3 * (3^K * m) := by
        rw [Nat.pow_succ]
        ring
      rw [hshape, canonicalTail_zero_strip]
      have hinner : 3^K ∣ canonicalTail (r+1) (3^K * m) :=
        ih (r+1) (3^K * m) ⟨m, rfl⟩
      obtain ⟨z, hz⟩ := hinner
      refine ⟨z, ?_⟩
      rw [hz, Nat.pow_succ]
      ring

/-- Nonzero canonical-tail residue therefore certifies nonzero origin support
below the same cutoff. -/
theorem canonical_origin_prefix_nonzero_of_tail_prefix_nonzero
    (r n K : Nat)
    (htail : canonicalTail r n % 3^K ≠ 0) :
    n % 3^K ≠ 0 := by
  intro hzero
  have horigin : 3^K ∣ n := Nat.dvd_of_mod_eq_zero hzero
  have htailDiv :=
    canonicalTail_pow_dvd_of_origin_pow_dvd r n K horigin
  exact htail (Nat.mod_eq_zero_of_dvd htailDiv)

/-- The combined controller and canonical renormalizer reach the actual
origin: the origin has nonzero ternary support below the child-gate cutoff. -/
theorem canonical_origin_packet_nonzero
    (s n q : Nat) (hs : 1 ≤ s)
    (hChild : SeedHappy 0 0 (canonicalChildTail s n) q)
    (hRightBad : ∀ j,
      ¬ SeedHappy 1 1 (canonicalParentTail s n) j) :
    n % 3^(q+1) ≠ 0 := by
  apply canonical_origin_prefix_nonzero_of_tail_prefix_nonzero (s+1)
  simpa [canonicalChildTail] using
    canonical_child_residue_packet_nonzero s n q hs hChild hRightBad

private theorem index_le_three_pow (r : Nat) :
    r ≤ 3^r := by
  induction r with
  | zero => simp
  | succ r ih =>
      rw [Nat.pow_succ]
      have hp : 0 < 3^r := by positivity
      omega

/-- A natural number cannot have nonzero ternary digits beyond every cutoff. -/
theorem nat_no_unbounded_ternary_support
    (n : Nat) :
    ¬ (∀ K : Nat,
      ∃ r : Nat, K ≤ r ∧ (n / 3^r) % 3 ≠ 0) := by
  intro h
  obtain ⟨r, hr, hnonzero⟩ := h (n+1)
  have hnr : n < r := by omega
  have hpow : n < 3^r := lt_of_lt_of_le hnr (index_le_three_pow r)
  have hdiv : n / 3^r = 0 := Nat.div_eq_of_lt hpow
  simp [hdiv] at hnonzero

#check canonical_child_energy_decomposition
#check canonical_left_seed_adapter
#check canonical_right_seed_adapter
#check canonical_left_u_jump_adapter
#check canonical_right_u_jump_adapter
#check canonical_base_carry_zero
#check canonical_latent_gate_packet
#check canonicalTail_cut_quotient_exact
#check canonical_controller_childTail_cut_exact
#check canonical_child_residue_packet_nonzero
#check canonicalTail_pow_dvd_of_origin_pow_dvd
#check canonical_origin_packet_nonzero
#check canonical_parent_energy_decomposition
#check nat_no_unbounded_ternary_support
#print axioms canonical_parent_energy_decomposition
#print axioms nat_no_unbounded_ternary_support

end GSTGraphV2CanonicalEscape
