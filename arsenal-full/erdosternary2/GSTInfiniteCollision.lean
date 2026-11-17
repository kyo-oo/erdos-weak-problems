import GSTV2InfiniteCore

set_option maxRecDepth 1000000
set_option maxHeartbeats 10000000

namespace GSTV2

/-!
# GST V2 all-depth coupled information transport

This is the production transport layer between the finite natural child word
and the parent affine information word. Nothing terminates here: the state is
iterated on every `K : Nat` and the exact shared-state equation is preserved.
-/

def affineCarry (D X k : Nat) : Nat :=
  (D + 4 * (X % 3^k)) / 3^k

def naturalCarry (Y k : Nat) : Nat :=
  (4 * (Y % 3^k)) / 3^k

theorem affineCarry_forward (D X k : Nat) :
    affineCarry D X (k+1) =
      cellNextCarry (affineCarry D X k) (digit X k) := by
  simp only [affineCarry, digit, cellNextCarry, cellMass, Nat.pow_succ]
  have hk : 0 < 3^k := Nat.pow_pos (by decide)
  have hsplit : X % (3^k * 3) =
      X % 3^k + 3^k * (X / 3^k % 3) := by
    rw [Nat.mod_mul]
  rw [hsplit]
  have hshape :
      D + 4 * (X % 3^k + 3^k * (X / 3^k % 3)) =
        (D + 4 * (X % 3^k)) +
          3^k * (4 * (X / 3^k % 3)) := by ring
  rw [hshape, ← Nat.div_div_eq_div_mul,
    Nat.add_mul_div_left _ _ hk]

theorem naturalCarry_forward (Y k : Nat) :
    naturalCarry Y (k+1) =
      cellNextCarry (naturalCarry Y k) (digit Y k) := by
  simpa [naturalCarry, affineCarry, Nat.zero_add] using affineCarry_forward 0 Y k

theorem digit_shift (Y q j : Nat) :
    digit Y (q+j) = digit (Y / 3^q) j := by
  simp only [digit]
  rw [Nat.pow_add, ← Nat.div_div_eq_div_mul]

structure CoupledState where
  parentSeed : Nat
  parentOffset : Nat
  childResidue : Nat
  childCarry : Nat
  childTail : Nat
  deriving Repr

def CoupledState.parentWord (A : Nat) (st : CoupledState) : Nat :=
  st.parentOffset + A * st.childTail

def CoupledInvariant (A : Nat) (st : CoupledState) : Prop :=
  st.parentSeed + 4 * st.parentOffset =
      st.childResidue + A * st.childCarry ∧
    st.childResidue < A

def coupledStep (A : Nat) (st : CoupledState) : CoupledState :=
  let r := st.childTail % 3
  let e := (st.parentOffset + A*r) % 3
  let u := cellOutput st.childCarry r
  {
    parentSeed := cellNextCarry st.parentSeed e
    parentOffset := (st.parentOffset + A*r) / 3
    childResidue := (st.childResidue + A*u) / 3
    childCarry := cellNextCarry st.childCarry r
    childTail := st.childTail / 3
  }

theorem coupled_low_regenerates
    (A D Z r : Nat) :
    (D + 4*Z + 4*A*r) / 3 =
      cellNextCarry D ((Z + A*r) % 3) +
        4 * ((Z + A*r) / 3) := by
  let E := Z + A*r
  have hE : E = E % 3 + 3*(E/3) := by
    have h := Nat.mod_add_div E 3
    omega
  have hshape : D + 4*Z + 4*A*r = D + 4*E := by
    dsimp [E]
    ring
  rw [hshape, hE]
  have hnum :
      D + 4 * (E % 3 + 3 * (E / 3)) =
        (D + 4*(E%3)) + 3*(4*(E/3)) := by ring
  rw [hnum]
  have h3 : 0 < (3:Nat) := by decide
  rw [Nat.add_mul_div_left _ _ h3]
  rfl

theorem coupled_high_regenerates
    (A W C r : Nat) :
    (W + A*C + 4*A*r) / 3 =
      (W + A*cellOutput C r) / 3 +
        A * cellNextCarry C r := by
  let U := C + 4*r
  have hU : U = U % 3 + 3*(U/3) := by
    have h := Nat.mod_add_div U 3
    omega
  have hshape0 : W + A*C + 4*A*r = W + A*U := by
    dsimp [U]
    ring
  rw [hshape0, hU]
  have hshape1 :
      W + A*(U % 3 + 3*(U/3)) =
        (W + A*(U%3)) + 3*(A*(U/3)) := by ring
  rw [hshape1]
  have h3 : 0 < (3:Nat) := by decide
  rw [Nat.add_mul_div_left _ _ h3]
  simp [cellOutput, cellNextCarry, cellMass, U]

theorem coupled_high_residue_lt
    (A W C r : Nat) (hA : 0 < A) (hW : W < A) :
    (W + A*cellOutput C r) / 3 < A := by
  have hu : cellOutput C r < 3 := by
    unfold cellOutput
    exact Nat.mod_lt _ (by decide)
  have hu1 : cellOutput C r + 1 ≤ 3 := Nat.succ_le_of_lt hu
  have hnum : W + A*cellOutput C r < 3*A := by
    calc
      W + A*cellOutput C r < A + A*cellOutput C r :=
        Nat.add_lt_add_right hW _
      _ = A * (cellOutput C r + 1) := by ring
      _ ≤ A*3 := Nat.mul_le_mul_left A hu1
      _ = 3*A := by ring
  exact Nat.div_lt_of_lt_mul hnum

theorem coupledStep_preserves_invariant
    (A : Nat) (st : CoupledState)
    (hA : 0 < A) (hInv : CoupledInvariant A st) :
    CoupledInvariant A (coupledStep A st) := by
  rcases hInv with ⟨hEq, hW⟩
  unfold CoupledInvariant coupledStep
  dsimp only
  let r := st.childTail % 3
  have hlow := coupled_low_regenerates
    A st.parentSeed st.parentOffset r
  have hhigh := coupled_high_regenerates
    A st.childResidue st.childCarry r
  have hEq' :
      cellNextCarry st.parentSeed ((st.parentOffset + A*r) % 3) +
          4*((st.parentOffset + A*r)/3) =
        (st.childResidue + A*cellOutput st.childCarry r)/3 +
          A*cellNextCarry st.childCarry r := by
    rw [← hlow, ← hhigh]
    rw [hEq]
  refine ⟨?_, ?_⟩
  · simpa [r] using hEq'
  · exact coupled_high_residue_lt A st.childResidue st.childCarry r hA hW

theorem coupledStep_parentWord_div_three
    (A : Nat) (st : CoupledState) :
    (coupledStep A st).parentWord A = st.parentWord A / 3 := by
  let r := st.childTail % 3
  have hY : st.childTail = r + 3 * (st.childTail / 3) := by
    dsimp [r]
    exact (Nat.mod_add_div st.childTail 3).symm
  have hmul :
      A * st.childTail = A * r + 3 * (A * (st.childTail / 3)) := by
    calc
      A * st.childTail = A * (r + 3 * (st.childTail / 3)) :=
        congrArg (fun x : Nat => A * x) hY
      _ = A * r + 3 * (A * (st.childTail / 3)) := by ring
  have hshape :
      st.parentOffset + A * st.childTail =
        (st.parentOffset + A * r) + 3 * (A * (st.childTail / 3)) := by
    rw [hmul]
    omega
  change (st.parentOffset + A * r) / 3 + A * (st.childTail / 3) =
    (st.parentOffset + A * st.childTail) / 3
  rw [hshape]
  have h3 : 0 < (3 : Nat) := by decide
  rw [Nat.add_mul_div_left _ _ h3]

def coupledOrbit (A : Nat) (initial : CoupledState) : Nat → CoupledState
  | 0 => initial
  | K+1 => coupledStep A (coupledOrbit A initial K)

theorem coupledOrbit_invariant_all
    (A : Nat) (initial : CoupledState)
    (hA : 0 < A) (h0 : CoupledInvariant A initial) :
    ∀ K, CoupledInvariant A (coupledOrbit A initial K) := by
  intro K
  induction K with
  | zero => exact h0
  | succ K ih =>
      exact coupledStep_preserves_invariant A (coupledOrbit A initial K) hA ih

theorem coupledOrbit_childTail_exact
    (A : Nat) (initial : CoupledState) :
    ∀ K, (coupledOrbit A initial K).childTail = initial.childTail / 3^K := by
  intro K
  induction K with
  | zero => simp [coupledOrbit]
  | succ K ih =>
      rw [coupledOrbit]
      change (coupledOrbit A initial K).childTail / 3 = _
      rw [ih, Nat.pow_succ, ← Nat.div_div_eq_div_mul]

theorem coupledOrbit_parentWord_exact
    (A : Nat) (initial : CoupledState) :
    ∀ K,
      (coupledOrbit A initial K).parentWord A =
        initial.parentWord A / 3^K := by
  intro K
  induction K with
  | zero => simp [coupledOrbit]
  | succ K ih =>
      rw [coupledOrbit, coupledStep_parentWord_div_three, ih,
        Nat.pow_succ, ← Nat.div_div_eq_div_mul]

theorem coupledOrbit_childCarry_exact
    (A : Nat) (initial : CoupledState)
    (hC0 : initial.childCarry = 0) :
    ∀ K, (coupledOrbit A initial K).childCarry =
      naturalCarry initial.childTail K := by
  intro K
  induction K with
  | zero =>
      change initial.childCarry = 4 * (initial.childTail % 1) / 1
      rw [hC0, Nat.mod_one]
  | succ K ih =>
      rw [coupledOrbit]
      change cellNextCarry (coupledOrbit A initial K).childCarry
        ((coupledOrbit A initial K).childTail % 3) = _
      rw [ih, naturalCarry_forward]
      congr 1
      rw [coupledOrbit_childTail_exact A initial K]
      rfl

theorem coupledOrbit_childDigit_exact
    (A : Nat) (initial : CoupledState) :
    ∀ K, (coupledOrbit A initial K).childTail % 3 =
      digit initial.childTail K := by
  intro K
  rw [coupledOrbit_childTail_exact]
  rfl

structure InfiniteCoupledControl
    (A : Nat) (initial : CoupledState) : Prop where
  multiplierPositive : 0 < A
  initialInvariant : CoupledInvariant A initial
  invariantAll : ∀ K, CoupledInvariant A (coupledOrbit A initial K)
  childTailExact : ∀ K,
    (coupledOrbit A initial K).childTail = initial.childTail / 3^K
  parentWordExact : ∀ K,
    (coupledOrbit A initial K).parentWord A =
      initial.parentWord A / 3^K

theorem infinite_coupled_control
    (A : Nat) (initial : CoupledState)
    (hA : 0 < A) (h0 : CoupledInvariant A initial) :
    InfiniteCoupledControl A initial := by
  exact {
    multiplierPositive := hA
    initialInvariant := h0
    invariantAll := coupledOrbit_invariant_all A initial hA h0
    childTailExact := coupledOrbit_childTail_exact A initial
    parentWordExact := coupledOrbit_parentWord_exact A initial
  }

end GSTV2
