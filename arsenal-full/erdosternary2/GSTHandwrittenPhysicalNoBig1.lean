import GSTGraphV2InfiniteBigNDichotomyScratch
import GSTGraphV2PhysicalSignedKernelTelescopeScratch

set_option maxRecDepth 1000000
set_option maxHeartbeats 10000000

open GSTInfiniteV2

/-- Every literal binary row is an actual infinite handwritten bridge path. -/
theorem gpt56_binary_row_path
    (R p : Nat) :
    GSTInfiniteBridgePathS
      (fun r => GSTPhysicalKernel.binaryColumnCarry R p r)
      (fun r => GSTPhysicalKernel.binaryColumnDigit R p r) := by
  refine ⟨?_, ?_, ?_⟩
  · intro r
    exact GSTPhysicalKernel.binaryColumnCarry_lt_two R p r
  · intro r
    exact GSTPhysicalKernel.binaryColumnDigit_lt_three R p r
  · intro r
    simpa [GSTInfiniteV2.gstBinaryBridgeOutputS,
      GSTPhysicalKernel.microOutput] using
      GSTPhysicalKernel.microOutput_eq_next_binaryColumnDigit R p r

/-- If the physical x2 carry at one binary column is one, the positive gap
between the low residue and the row modulus doubles at the next column. -/
theorem gpt56_binary_residue_gap_doubles
    (R p r : Nat)
    (ha : GSTPhysicalKernel.binaryColumnCarry R p r = 1) :
    3^p - ((2^(r+1) * R) % 3^p) =
      2 * (3^p - ((2^r * R) % 3^p)) := by
  let M := 3^p
  let L := (2^r * R) % M
  have hM : 0 < M := by
    dsimp [M]
    exact Nat.pow_pos (by decide)
  have hL : L < M := by
    dsimp [L]
    exact Nat.mod_lt _ hM
  have hcarry : (2 * L) / M = 1 := by
    simpa [GSTPhysicalKernel.binaryColumnCarry, L, M] using ha
  have hpow : 2^(r+1) * R = 2 * (2^r * R) := by
    rw [Nat.pow_succ]
    ring
  have hmod :
      (2^(r+1) * R) % M = (2 * L) % M := by
    rw [hpow]
    dsimp [L]
    simp [Nat.mul_mod]
  have hdecomp := Nat.mod_add_div (2 * L) M
  rw [hcarry] at hdecomp
  rw [show 3^p = M by rfl, hmod]
  omega

/-- Elementary growth used at the physical row modulus. -/
theorem gpt56_succ_le_two_pow : ∀ n : Nat, n + 1 ≤ 2^n
  | 0 => by decide
  | n+1 => by
      have ih := gpt56_succ_le_two_pow n
      rw [Nat.pow_succ]
      omega

/-- A literal finite natural cannot realize the handwritten I!=BIG1/SURVIVE
fixed state on every binary column of one ternary row. -/
theorem gpt56_physical_noBig1_impossible
    (R p : Nat)
    (hclear : GSTBig1ClearInfinitePathS
      (fun r => GSTPhysicalKernel.binaryColumnCarry R p r)
      (fun r => GSTPhysicalKernel.binaryColumnDigit R p r))
    (h0 : GSTPhysicalKernel.binaryColumnDigit R p 0 ≠ 0) : False := by
  let M := 3^p
  let a : Nat → Nat := fun r => GSTPhysicalKernel.binaryColumnCarry R p r
  let d : Nat → Nat := fun r => GSTPhysicalKernel.binaryColumnDigit R p r
  have hM : 0 < M := by
    dsimp [M]
    exact Nat.pow_pos (by decide)
  have hallCarry : ∀ r, a r = 1 := by
    intro r
    have hs := gst_big1_clear_infinite_edges_are_surviveS
      a d (by simpa [a, d] using hclear) (by simpa [d] using h0) r
    exact hs.1
  have hgap : ∀ r, 2^r ≤ M - ((2^r * R) % M) := by
    intro r
    induction r with
    | zero =>
        have hres : (R % M) < M := Nat.mod_lt _ hM
        simp only [Nat.pow_zero, Nat.one_mul]
        omega
    | succ r ih =>
        have hdoubleM :
            M - ((2^(r+1) * R) % M) =
              2 * (M - ((2^r * R) % M)) := by
          simpa [M] using gpt56_binary_residue_gap_doubles R p r (by
            simpa [a] using hallCarry r)
        have hpow : 2^(r+1) = 2 * 2^r := by
          rw [Nat.pow_succ]
          ring
        have hmul :
            2 * 2^r ≤ 2 * (M - ((2^r * R) % M)) :=
          Nat.mul_le_mul_left 2 ih
        have hle :
            2^(r+1) ≤ 2 * (M - ((2^r * R) % M)) := by
          rw [hpow]
          exact hmul
        exact hle.trans_eq hdoubleM.symm
  have hAt := hgap M
  have hresM : (2^M * R) % M < M := Nat.mod_lt _ hM
  have hgapLe : M - ((2^M * R) % M) ≤ M := Nat.sub_le _ _
  have hgrowth : M + 1 ≤ 2^M := gpt56_succ_le_two_pow M
  omega

/-- Therefore every physical child gate's binary-column path must hit BIG1 at
a finite first column; the infinite no-BIG1 branch is eliminated physically. -/
theorem gpt56_physical_path_forces_first_big1
    (R p : Nat)
    (h0 : GSTPhysicalKernel.binaryColumnDigit R p 0 ≠ 0) :
    ∃ N, GSTFirstBig1AtS
      (fun r => GSTPhysicalKernel.binaryColumnDigit R p r) N := by
  let a : Nat → Nat := fun r => GSTPhysicalKernel.binaryColumnCarry R p r
  let d : Nat → Nat := fun r => GSTPhysicalKernel.binaryColumnDigit R p r
  have hpath : GSTInfiniteBridgePathS a d := by
    simpa [a, d] using gpt56_binary_row_path R p
  rcases gst_infinite_two_case_controlS a d hpath (by simpa [d] using h0) with hbig | hclear
  · simpa [d] using hbig
  · exact False.elim (gpt56_physical_noBig1_impossible R p
      (by simpa [a, d] using hclear) h0)

#check gpt56_binary_residue_gap_doubles
#check gpt56_physical_noBig1_impossible
#check gpt56_physical_path_forces_first_big1
#print axioms gpt56_binary_residue_gap_doubles
#print axioms gpt56_physical_noBig1_impossible
#print axioms gpt56_physical_path_forces_first_big1
