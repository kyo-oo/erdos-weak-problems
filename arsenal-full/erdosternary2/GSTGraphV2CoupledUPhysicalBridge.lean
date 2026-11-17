import GSTGraphV2CoupledUFlux

set_option maxRecDepth 1000000
set_option maxHeartbeats 10000000

namespace GSTGraphV2CoupledUPhysicalBridge

open GSTGraphV2CoupledUFlux

/-- The missing fifth coordinate of the physical coupled state.  The four-field
Equation-III state is retained verbatim; `childResidue` is the finite high-end
remainder needed to identify that potential with the actual horizontal carry
word. -/
structure PhysicalState where
  core : State
  childResidue : Nat
  deriving Repr

/-- Exact two-endpoint shared-information equation. -/
def PhysicalInvariant (A : Nat) (st : PhysicalState) : Prop :=
  st.core.parentSeed + 4 * st.core.parentOffset =
    st.childResidue + A * st.core.childCarry

/-- The charge after removing the linear six-world carry mass. -/
def reducedChargeWith (charge : Nat → Int) (C : Nat) : Int :=
  charge C - 6 * (C : Int)

/-- Equation III's potential, now read through the conserved fifth coordinate. -/
theorem potential_shared_rewrite
    (charge : Nat → Int) (A : Nat) (st : PhysicalState)
    (hInv : PhysicalInvariant A st) :
    potentialWith charge A st.core =
      reducedChargeWith charge st.core.parentSeed -
        (A : Int) * reducedChargeWith charge st.core.childCarry +
        6 * (st.childResidue : Int) := by
  unfold PhysicalInvariant at hInv
  have hInvZ :
      (st.core.parentSeed : Int) + 4 * (st.core.parentOffset : Int) =
        (st.childResidue : Int) + (A : Int) * (st.core.childCarry : Int) := by
    exact_mod_cast hInv
  unfold potentialWith reducedChargeWith
  ring_nf at hInvZ ⊢
  linarith

/-- `i`-th least-significant base-four digit of a finite carry word. -/
def base4Digit (S i : Nat) : Nat := S / 4^i % 4

/-- Exact base-four prefix reconstruction at every finite observation width. -/
theorem base4_prefix_value (S N : Nat) :
    Finset.sum (Finset.range N) (fun i => 4^i * base4Digit S i) =
      S % 4^N := by
  induction N with
  | zero =>
      simp only [Finset.range_zero, Finset.sum_empty, Nat.pow_zero, Nat.mod_one]
  | succ N ih =>
      rw [Finset.sum_range_succ, ih]
      unfold base4Digit
      rw [Nat.pow_succ, Nat.mod_mul]

/-- One local horizontal charge between adjacent base-four carry coordinates.
Its form is forced by `charge = reducedCharge + 6*carry`. -/
def horizontalFluxWith (charge : Nat → Int) (S i : Nat) : Int :=
  charge (base4Digit S i) -
    4 * reducedChargeWith charge (base4Digit S (i+1))

/-- Horizontal telescope before substituting the finite-word prefix. -/
theorem horizontal_flux_telescope_raw
    (charge : Nat → Int) (S N : Nat) :
    Finset.sum (Finset.range N) (fun i =>
      ((4^i : Nat) : Int) * horizontalFluxWith charge S i) =
      reducedChargeWith charge (base4Digit S 0) -
        ((4^N : Nat) : Int) * reducedChargeWith charge (base4Digit S N) +
        6 * (Finset.sum (Finset.range N) (fun i =>
          ((4^i : Nat) : Int) * (base4Digit S i : Int))) := by
  induction N with
  | zero =>
      simp [reducedChargeWith]
  | succ N ih =>
      rw [Finset.sum_range_succ, ih]
      simp only [horizontalFluxWith, reducedChargeWith]
      rw [Finset.sum_range_succ, Nat.pow_succ]
      push_cast
      ring

/-- Horizontal telescope in closed finite-word form. -/
theorem horizontal_flux_telescope
    (charge : Nat → Int) (S N : Nat) :
    Finset.sum (Finset.range N) (fun i =>
      ((4^i : Nat) : Int) * horizontalFluxWith charge S i) =
      reducedChargeWith charge (base4Digit S 0) -
        ((4^N : Nat) : Int) * reducedChargeWith charge (base4Digit S N) +
        6 * ((S % 4^N : Nat) : Int) := by
  rw [horizontal_flux_telescope_raw]
  have hp := base4_prefix_value S N
  have hpZ :
      Finset.sum (Finset.range N) (fun i =>
        ((4^i : Nat) : Int) * (base4Digit S i : Int)) =
        ((S % 4^N : Nat) : Int) := by
    exact_mod_cast hp
  rw [hpZ]

/-- **Physical bridge for Equation III.**

When `A = 4^N`, the coupled U potential is not an abstract extra quantity: it
is exactly the weighted horizontal flux of the `N` base-four carry coordinates
of the same shared information word.  The live high remainder is retained via
`childResidue < A`; no terminal, support-horizon, or origin-exhaustion premise
appears. -/
theorem coupled_potential_is_horizontal_base4_flux
    (charge : Nat → Int) (A N : Nat) (st : PhysicalState)
    (hA : A = 4^N)
    (hInv : PhysicalInvariant A st)
    (hResidue : st.childResidue < A)
    (hParent : st.core.parentSeed < 4)
    (hChild : st.core.childCarry < 4) :
    potentialWith charge A st.core =
      Finset.sum (Finset.range N) (fun i =>
        ((4^i : Nat) : Int) *
          horizontalFluxWith charge
            (st.core.parentSeed + 4 * st.core.parentOffset) i) := by
  subst A
  let S := st.core.parentSeed + 4 * st.core.parentOffset
  have hApos : 0 < 4^N := Nat.pow_pos (by decide)
  have hShared : S = st.childResidue + 4^N * st.core.childCarry := by
    dsimp [S]
    exact hInv
  have hLow : base4Digit S 0 = st.core.parentSeed := by
    unfold base4Digit
    simp only [Nat.pow_zero, Nat.div_one]
    dsimp [S]
    rw [Nat.add_mod]
    simp [Nat.mod_eq_of_lt hParent]
  have hHigh : base4Digit S N = st.core.childCarry := by
    unfold base4Digit
    rw [hShared, Nat.add_mul_div_left _ _ hApos]
    rw [Nat.div_eq_of_lt hResidue]
    simp [Nat.mod_eq_of_lt hChild]
  have hPrefix : S % 4^N = st.childResidue := by
    rw [hShared, Nat.add_mod, Nat.mul_mod]
    simp [Nat.mod_eq_of_lt hResidue]
  have htel := horizontal_flux_telescope charge S N
  rw [hLow, hHigh] at htel
  have hPrefixZ : ((S % 4^N : Nat) : Int) = (st.childResidue : Int) := by
    exact_mod_cast hPrefix
  rw [hPrefixZ] at htel
  have hpot := potential_shared_rewrite charge (4^N) st hInv
  dsimp [S] at htel
  exact hpot.trans htel.symm

/-- GST handwritten-U specialization of the physical bridge. -/
theorem gst_u_potential_is_horizontal_base4_flux
    (A N : Nat) (st : PhysicalState)
    (hA : A = 4^N)
    (hInv : PhysicalInvariant A st)
    (hResidue : st.childResidue < A)
    (hParent : st.core.parentSeed < 4)
    (hChild : st.core.childCarry < 4) :
    potentialWith gstUChargeExact A st.core =
      Finset.sum (Finset.range N) (fun i =>
        ((4^i : Nat) : Int) *
          horizontalFluxWith gstUChargeExact
            (st.core.parentSeed + 4 * st.core.parentOffset) i) := by
  exact coupled_potential_is_horizontal_base4_flux
    gstUChargeExact A N st hA hInv hResidue hParent hChild

#check potential_shared_rewrite
#check base4_prefix_value
#check horizontal_flux_telescope
#check coupled_potential_is_horizontal_base4_flux
#check gst_u_potential_is_horizontal_base4_flux
#print axioms coupled_potential_is_horizontal_base4_flux
#print axioms gst_u_potential_is_horizontal_base4_flux

end GSTGraphV2CoupledUPhysicalBridge
