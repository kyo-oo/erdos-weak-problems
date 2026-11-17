import GSTGraphV2InfiniteControllerBridge

set_option maxRecDepth 1000000
set_option maxHeartbeats 10000000

namespace GSTGraphV2DescentOntology

open GSTCanonicalSevenAxisBridge
open GSTGraphV2InfiniteControl
open GSTGraphV2UnifiedPowerRectangle
open GSTGraphV2InfiniteControllerBridge
open GSTV2

/-!
# Graph V2 descent ontology

The seven-axis graph carries more than the local `(carry,digit)` projection.
Its `descent` coordinate is the exact quotient field

  Q(t,p) = floor(4^t E / 3^p).

The theorems below identify the horizontal carry word and the transplanted
coupled controller as exact affine defects of this quotient field.  This is the
full arithmetic memory that is invisible in the twelve-state local chart.
-/

/-- Exact vertical quotient decomposition of one seven-axis vertex. -/
theorem graph_descent_vertical_exact (E t p : Nat) :
    (graph E t p).seven.descent =
      (graph E t p).seven.digit +
        3 * (graph E t p).seven.nextDescent := by
  change (4^t * E) / 3^p =
    ((4^t * E) / 3^p) % 3 + 3 * ((4^t * E) / 3^(p+1))
  rw [Nat.pow_succ, ← Nat.div_div_eq_div_mul]
  exact (Nat.mod_add_div ((4^t * E) / 3^p) 3).symm

/-- One horizontal x4 step acts affinely on the descent field.  The local carry
is exactly the affine defect between adjacent horizontal quotient values. -/
theorem graph_descent_horizontal_step_exact (E t p : Nat) :
    (graph E (t+1) p).seven.descent =
      (graph E t p).seven.carry +
        4 * (graph E t p).seven.descent := by
  let R : Nat := 4^t * E
  change (4^(t+1) * E) / 3^p =
    (4 * (R % 3^p)) / 3^p + 4 * (R / 3^p)
  have hp : 0 < 3^p := Nat.pow_pos (by decide)
  have hrem : R % 3^p < 3^p := Nat.mod_lt R hp
  have hpow : 4^(t+1) * E = 4 * R := by
    dsimp [R]
    rw [Nat.pow_succ]
    ring
  have hsplit : R = R % 3^p + 3^p * (R / 3^p) := by
    exact (Nat.mod_add_div R (3^p)).symm
  have hshape :
      4 * (R % 3^p + 3^p * (R / 3^p)) =
        4 * (R % 3^p) + 3^p * (4 * (R / 3^p)) := by ring
  have hmod :
      (R % 3^p + 3^p * (R / 3^p)) % 3^p = R % 3^p := by
    simp [Nat.add_mod, Nat.mul_mod, Nat.mod_eq_of_lt hrem]
  have hdiv :
      (R % 3^p + 3^p * (R / 3^p)) / 3^p = R / 3^p := by
    rw [Nat.add_mul_div_left _ _ hp, Nat.div_eq_of_lt hrem, Nat.zero_add]
  rw [hpow, hsplit, hshape, Nat.add_mul_div_left _ _ hp, hmod, hdiv]

/-- Width-`N` horizontal transport of the full quotient field.  `carryWord` is
literally the affine defect left after multiplying the left descent by `4^N`. -/
theorem graph_descent_horizontal_block_exact
    (E p start : Nat) : ∀ N : Nat,
    (graph E (start+N) p).seven.descent =
      carryWord E p start N +
        4^N * (graph E start p).seven.descent := by
  intro N
  induction N with
  | zero =>
      simp [carryWord]
  | succ N ih =>
      have hstep := graph_descent_horizontal_step_exact E (start+N) p
      have hidx : (start+N)+1 = start+(N+1) := by omega
      rw [hidx] at hstep
      rw [hstep, ih, carryWord, Nat.pow_succ]
      ring

/-- The coupled invariant is an exact Euclidean quotient/remainder encoding by
its macro multiplier `A`: child carry is the quotient sector and child residue
is the exact remainder of `parentSeed + 4*parentOffset`. -/
theorem coupledInvariant_euclidean_decode
    (A : Nat) (st : CoupledState)
    (hA : 0 < A) (hInv : CoupledInvariant A st) :
    st.childCarry =
        (st.parentSeed + 4 * st.parentOffset) / A ∧
      st.childResidue =
        (st.parentSeed + 4 * st.parentOffset) % A := by
  rcases hInv with ⟨hEq, hResidue⟩
  constructor
  · rw [hEq, Nat.add_mul_div_left _ _ hA,
      Nat.div_eq_of_lt hResidue, Nat.zero_add]
  · rw [hEq]
    simp [Nat.add_mod, Nat.mod_eq_of_lt hResidue]

/-- Equivalent sector bounds: carry `C` means the shared affine word lies in
its `C`-th width-`A` sector. -/
theorem coupledInvariant_sector_bounds
    (A : Nat) (st : CoupledState)
    (hInv : CoupledInvariant A st) :
    A * st.childCarry ≤ st.parentSeed + 4 * st.parentOffset ∧
      st.parentSeed + 4 * st.parentOffset < A * (st.childCarry + 1) := by
  rcases hInv with ⟨hEq, hResidue⟩
  constructor
  · rw [hEq]
    omega
  · rw [hEq]
    calc
      st.childResidue + A * st.childCarry <
          A + A * st.childCarry := Nat.add_lt_add_right hResidue _
      _ = A * (st.childCarry + 1) := by ring

/-- A child Happy gate therefore occupies one of the two extreme quotient
sectors, not merely one of two local carry labels. -/
theorem child_happy_extreme_sector
    (A : Nat) (st : CoupledState)
    (hInv : CoupledInvariant A st)
    (hHappy : Happy st.childCarry (st.childTail % 3)) :
    ((st.childTail % 3 = 2) ∧ st.childCarry = 0 ∧
        st.parentSeed + 4 * st.parentOffset < A) ∨
      ((st.childTail % 3 = 2) ∧ st.childCarry = 3 ∧
        3 * A ≤ st.parentSeed + 4 * st.parentOffset ∧
        st.parentSeed + 4 * st.parentOffset < 4 * A) := by
  have hSector := coupledInvariant_sector_bounds A st hInv
  rcases hHappy with ⟨hd, h0 | h3⟩
  · left
    refine ⟨hd, h0, ?_⟩
    have h := hSector.2
    rw [h0] at h
    norm_num at h
    simpa using h
  · right
    refine ⟨hd, h3, ?_, ?_⟩
    · have h := hSector.1
      rw [h3] at h
      simpa [Nat.mul_comm] using h
    · have h := hSector.2
      rw [h3] at h
      norm_num at h
      simpa [Nat.mul_comm] using h

/-- In the transplanted Graph-V2 controller, `childTail` is literally the left
boundary descent field. -/
theorem graphCoupledState_childTail_eq_left_descent
    (E N p : Nat) :
    (graphCoupledState E N p).childTail =
      (graph E 0 p).seven.descent := by
  simp [graphCoupledState, graph, cell,
    GSTCanonicalSevenAxisBridge.vertex]

/-- `parentOffset` is exactly the affine defect between right and left descent
fields across the width-`N` Graph-V2 rectangle. -/
theorem graphCoupledState_parentOffset_descent_exact
    (E N p : Nat) :
    (graph E N p).seven.descent =
      (graphCoupledState E N p).parentOffset +
        4^N * (graph E 0 p).seven.descent := by
  simpa [graphCoupledState] using
    (graph_descent_horizontal_block_exact E p 0 N)

/-- The controller's represented `parentWord` is not an abstract surrogate: it
is exactly the right-boundary seven-axis descent coordinate. -/
theorem graphCoupledState_parentWord_eq_right_descent
    (E N p : Nat) :
    (graphCoupledState E N p).parentWord (4^N) =
      (graph E N p).seven.descent := by
  rw [CoupledState.parentWord,
    graphCoupledState_childTail_eq_left_descent]
  exact (graphCoupledState_parentOffset_descent_exact E N p).symm

/-- The fifth coordinate `childResidue` is the corresponding affine defect for
the horizontally shifted rectangle beginning at column one. -/
theorem graphCoupledState_childResidue_descent_exact
    (E N p : Nat) :
    (graph E (N+1) p).seven.descent =
      (graphCoupledState E N p).childResidue +
        4^N * (graph E 1 p).seven.descent := by
  have h := graph_descent_horizontal_block_exact E p 1 N
  simpa [graphCoupledState, Nat.add_comm] using h

/-- Graph-V2 specialization of the Euclidean sector decoder. -/
theorem graphCoupledState_euclidean_decode
    (E N p : Nat) :
    (graphCoupledState E N p).childCarry =
        ((graphCoupledState E N p).parentSeed +
          4 * (graphCoupledState E N p).parentOffset) / 4^N ∧
      (graphCoupledState E N p).childResidue =
        ((graphCoupledState E N p).parentSeed +
          4 * (graphCoupledState E N p).parentOffset) % 4^N := by
  exact coupledInvariant_euclidean_decode
    (4^N) (graphCoupledState E N p)
    (Nat.pow_pos (by decide))
    (graphCoupledState_invariant E N p)

#check graph_descent_vertical_exact
#check graph_descent_horizontal_step_exact
#check graph_descent_horizontal_block_exact
#check coupledInvariant_euclidean_decode
#check child_happy_extreme_sector
#check graphCoupledState_parentWord_eq_right_descent
#check graphCoupledState_childResidue_descent_exact
#check graphCoupledState_euclidean_decode
#print axioms graph_descent_horizontal_block_exact
#print axioms coupledInvariant_euclidean_decode
#print axioms graphCoupledState_parentWord_eq_right_descent
#print axioms graphCoupledState_euclidean_decode

end GSTGraphV2DescentOntology
