import GSTGraphV2DescentOntology
import GSTPrefixOneSeedCore
import GSTGraphV2PerfectPowerBlockProbe

set_option maxRecDepth 1000000
set_option maxHeartbeats 10000000

namespace GSTGraphV2CanonicalDescentOntology

open GSTCanonicalSevenAxisBridge
open GSTGraphV2InfiniteControl
open GSTGraphV2UnifiedPowerRectangle
open GSTGraphV2InfiniteControllerBridge
open GSTGraphV2DescentOntology
open GSTGraphV2PerfectPowerBlock
open GSTPerfectPowerTailNavigation
open GSTPrefixOneSeedCore
open GSTCanonicalTailStateIso
open GSTV2

/-- The left canonical energy has the exact low prefix `1` at the production
cut `s+2`. -/
theorem canonicalEnergy_cut_decomposition (s n : Nat) :
    canonicalEnergy s n =
      1 + 3^(s+2) * canonicalTail (s+1) n := by
  simpa [canonicalEnergy, show (s+1)+1 = s+2 by omega] using
    (canonical_tail_decomposition (s+1) n)

/-- The right edge one perfect-power block later has the exact prefix
`1 + 3^(s+1)` and exposed descent
`prefixOffset s + 4^(3^s) * canonicalTail (s+1) n`. -/
theorem canonical_right_energy_cut_decomposition (s n : Nat) :
    4^(canonicalWidth s) * canonicalEnergy s n =
      (1 + 3^(s+1)) + 3^(s+2) *
        (prefixOffset s + 4^(3^s) * canonicalTail (s+1) n) := by
  have hExp :
      3^s + 3^(s+1) * n = 3^s * (1 + 3*n) := by
    rw [Nat.pow_succ]
    ring
  have hPow :
      4^(canonicalWidth s) * canonicalEnergy s n =
        4^(3^s * (1 + 3*n)) := by
    rw [canonicalWidth, canonicalEnergy, ← Nat.pow_add, hExp]
  have hTail := canonical_tail_decomposition s (1 + 3*n)
  have hShape := prefix_one_tail_shape s n
  rw [hPow, hTail, hShape]
  rw [show s+2 = (s+1)+1 by omega, Nat.pow_succ]
  ring

/-- The low right prefix is genuinely below the production cut. -/
theorem canonical_right_low_prefix_lt_cut
    (s : Nat) :
    1 + 3^(s+1) < 3^(s+2) := by
  have hpow : 0 < 3^(s+1) := Nat.pow_pos (by decide)
  rw [show s+2 = (s+1)+1 by omega, Nat.pow_succ]
  omega

/-- For `s≥1`, four times the right low prefix has quotient exactly one by the
production modulus.  This is the literal origin of the seed-one parent carry. -/
theorem canonical_right_low_prefix_seed_one
    (s : Nat) (hs : 1 ≤ s) :
    (4 * (1 + 3^(s+1))) / 3^(s+2) = 1 := by
  let u := 3^(s+1)
  have hu9 : 9 ≤ u := by
    dsimp [u]
    have h := Nat.pow_le_pow_of_le (by decide : 1 < (3:Nat))
      (show 2 ≤ s+1 by omega)
    norm_num at h ⊢
    exact h
  have hu0 : 0 < u := by omega
  have hM : 3^(s+2) = 3*u := by
    dsimp [u]
    rw [show s+2 = (s+1)+1 by omega, Nat.pow_succ]
    ring
  have hrem : 4 + u < 3*u := by omega
  rw [hM]
  have hshape : 4 * (1 + u) = (4 + u) + (3*u) * 1 := by ring
  rw [hshape]
  have hMpos : 0 < 3*u := by positivity
  rw [Nat.add_mul_div_left _ _ hMpos, Nat.div_eq_of_lt hrem]

/-- Left child carry at the canonical production cut is exactly zero. -/
theorem canonical_graph_childCarry_cut_zero
    (s n : Nat) (hs : 1 ≤ s) :
    (graph (canonicalEnergy s n) 0 (s+2)).seven.carry = 0 := by
  have hE := canonicalEnergy_cut_decomposition s n
  have hb : 2 ≤ s+2 := by omega
  have hbounds := one_prefix_bounds (s+2) hb
  have hc :
      GSTCanonicalSevenAxisBridge.carry4 (canonicalEnergy s n) (s+2) = 0 := by
    rw [hE]
    unfold GSTCanonicalSevenAxisBridge.carry4
    have hmod :
        (1 + 3^(s+2) * canonicalTail (s+1) n) % 3^(s+2) = 1 := by
      simp [Nat.add_mod, Nat.mod_eq_of_lt hbounds.1]
    rw [hmod, Nat.div_eq_of_lt hbounds.2]
  simpa [graph, cell, GSTCanonicalSevenAxisBridge.vertex] using hc

/-- The controller child tail is literally the next-scale canonical tail. -/
theorem canonical_graph_childTail_cut_exact
    (s n : Nat) :
    (graphCoupledState (canonicalEnergy s n) (canonicalWidth s) (s+2)).childTail =
      canonicalTail (s+1) n := by
  simp [graphCoupledState, canonicalEnergy, canonicalTail,
    show (s+1)+1 = s+2 by omega]

/-- The right Graph-V2 descent at the canonical cut is the exact affine parent
word `z_s + A_s T`. -/
theorem canonical_graph_right_descent_cut_exact
    (s n : Nat) :
    (graph (canonicalEnergy s n) (canonicalWidth s) (s+2)).seven.descent =
      prefixOffset s + 4^(3^s) * canonicalTail (s+1) n := by
  let X := prefixOffset s + 4^(3^s) * canonicalTail (s+1) n
  let P := 1 + 3^(s+1)
  have hShape := canonical_right_energy_cut_decomposition s n
  have hP : P < 3^(s+2) := by
    simpa [P] using canonical_right_low_prefix_lt_cut s
  change
    (4^(canonicalWidth s) * canonicalEnergy s n) / 3^(s+2) = X
  rw [hShape]
  have hq := GSTCanonicalTailStateIso.prefix_slice_quotient_exact
    (s+2) P X 0 hP
  simpa [P, X] using hq

/-- The parent seed at the production cut is exactly one. -/
theorem canonical_graph_parentSeed_cut_one
    (s n : Nat) (hs : 1 ≤ s) :
    (graph (canonicalEnergy s n) (canonicalWidth s) (s+2)).seven.carry = 1 := by
  let X := prefixOffset s + 4^(3^s) * canonicalTail (s+1) n
  let P := 1 + 3^(s+1)
  have hShape := canonical_right_energy_cut_decomposition s n
  have hP : P < 3^(s+2) := by
    simpa [P] using canonical_right_low_prefix_lt_cut s
  have hseed : (4 * P) / 3^(s+2) = 1 := by
    simpa [P] using canonical_right_low_prefix_seed_one s hs
  have hc :
      GSTCanonicalSevenAxisBridge.carry4
        (4^(canonicalWidth s) * canonicalEnergy s n) (s+2) = 1 := by
    rw [hShape]
    unfold GSTCanonicalSevenAxisBridge.carry4
    have hmod : (P + 3^(s+2) * X) % 3^(s+2) = P := by
      simp [Nat.add_mod, Nat.mod_eq_of_lt hP]
    rw [hmod, hseed]
  simpa [graph, cell, GSTCanonicalSevenAxisBridge.vertex] using hc

/-- The horizontal carry word at the production cut is exactly the canonical
prefix offset `z_s`. -/
theorem canonical_graph_parentOffset_cut_exact
    (s n : Nat) :
    (graphCoupledState (canonicalEnergy s n) (canonicalWidth s) (s+2)).parentOffset =
      prefixOffset s := by
  let E := canonicalEnergy s n
  let N := canonicalWidth s
  let T := canonicalTail (s+1) n
  let z := prefixOffset s
  have hDesc := graphCoupledState_parentOffset_descent_exact E N (s+2)
  have hRight :
      (graph E N (s+2)).seven.descent = z + 4^N * T := by
    dsimp [E, N, T, z]
    simpa [canonicalWidth] using canonical_graph_right_descent_cut_exact s n
  have hLeft : (graph E 0 (s+2)).seven.descent = T := by
    rw [← graphCoupledState_childTail_eq_left_descent E N (s+2)]
    dsimp [E, N, T]
    exact canonical_graph_childTail_cut_exact s n
  have hEq :
      z + 4^N * T =
        (graphCoupledState E N (s+2)).parentOffset + 4^N * T := by
    calc
      z + 4^N * T = (graph E N (s+2)).seven.descent := hRight.symm
      _ = (graphCoupledState E N (s+2)).parentOffset +
            4^N * (graph E 0 (s+2)).seven.descent := hDesc
      _ = (graphCoupledState E N (s+2)).parentOffset + 4^N * T := by rw [hLeft]
  have hz : z = (graphCoupledState E N (s+2)).parentOffset :=
    Nat.add_right_cancel hEq
  exact hz.symm

/-- The fifth controller coordinate is the canonical affine remainder
`1 + 4 z_s`. -/
theorem canonical_graph_childResidue_cut_exact
    (s n : Nat) (hs : 1 ≤ s) :
    (graphCoupledState (canonicalEnergy s n) (canonicalWidth s) (s+2)).childResidue =
      1 + 4 * prefixOffset s := by
  let st := graphCoupledState (canonicalEnergy s n) (canonicalWidth s) (s+2)
  have hInv := graphCoupledState_invariant
    (canonicalEnergy s n) (canonicalWidth s) (s+2)
  have hD : st.parentSeed = 1 := by
    dsimp [st, graphCoupledState]
    exact canonical_graph_parentSeed_cut_one s n hs
  have hZ : st.parentOffset = prefixOffset s := by
    dsimp [st]
    exact canonical_graph_parentOffset_cut_exact s n
  have hC : st.childCarry = 0 := by
    dsimp [st, graphCoupledState]
    exact canonical_graph_childCarry_cut_zero s n hs
  rcases hInv with ⟨hEq, hResidue⟩
  rw [hD, hZ, hC] at hEq
  simp at hEq
  omega

/-- The controller parent word is exactly the canonical affine parent tail. -/
theorem canonical_graph_parentWord_cut_exact
    (s n : Nat) :
    (graphCoupledState (canonicalEnergy s n) (canonicalWidth s) (s+2)).parentWord
        (4^(canonicalWidth s)) =
      prefixOffset s + 4^(3^s) * canonicalTail (s+1) n := by
  have h := graphCoupledState_parentWord_eq_right_descent
    (canonicalEnergy s n) (canonicalWidth s) (s+2)
  rw [h]
  simpa [canonicalWidth] using canonical_graph_right_descent_cut_exact s n

/-- Complete canonical production-cut state.  Every controller coordinate is
now identified with the actual seven-axis arithmetic sheet. -/
theorem canonical_graphCoupledState_cut_packet
    (s n : Nat) (hs : 1 ≤ s) :
    let st := graphCoupledState (canonicalEnergy s n) (canonicalWidth s) (s+2)
    st.parentSeed = 1 ∧
    st.parentOffset = prefixOffset s ∧
    st.childResidue = 1 + 4 * prefixOffset s ∧
    st.childCarry = 0 ∧
    st.childTail = canonicalTail (s+1) n ∧
    st.parentWord (4^(canonicalWidth s)) =
      prefixOffset s + 4^(3^s) * canonicalTail (s+1) n := by
  dsimp only
  constructor
  · exact canonical_graph_parentSeed_cut_one s n hs
  constructor
  · exact canonical_graph_parentOffset_cut_exact s n
  constructor
  · exact canonical_graph_childResidue_cut_exact s n hs
  constructor
  · exact canonical_graph_childCarry_cut_zero s n hs
  constructor
  · exact canonical_graph_childTail_cut_exact s n
  · exact canonical_graph_parentWord_cut_exact s n

#check canonical_right_energy_cut_decomposition
#check canonical_graph_childCarry_cut_zero
#check canonical_graph_parentSeed_cut_one
#check canonical_graph_parentOffset_cut_exact
#check canonical_graph_childResidue_cut_exact
#check canonical_graph_parentWord_cut_exact
#check canonical_graphCoupledState_cut_packet
#print axioms canonical_graphCoupledState_cut_packet

end GSTGraphV2CanonicalDescentOntology
