import HCUniverse2.GSTSingularCohomologyMaps

/-
Copyright (c) 2026. The HC-PROOF campaign. All rights reserved.

# GST SPHERE CYCLE LEGS (Wave 58, file F1)

The carrier-free leg algebra of the sphere-union world that the weight-1
point-class gate consumes: the cyclic predecessor (the inverse of the
wave-57 `cyclicSucc`), the cycle/collapse leg identity (the M-cycle
permutes the collapse targets), and the const-factorization of the
off-slice composite.  Together with the wave-57 module's `incl_comp_collapse`
(the on-slice identity) these are the two restriction equations that make
the honest point classes of the planned finite-line world linearly
independent (the gate's third field) and the cycle-equivariance equation
that makes the M-cycle letter's Krylov orbit visit every line class.

Honesty ledger: every statement is proved unconditionally.  No `sorry`, no
new axioms, no `native_decide`.  The GitHub CI lane
`gst-sphere-point-class-gate.yml` owns the kernel check.
-/

set_option maxHeartbeats 200000000
set_option maxRecDepth 1000000

noncomputable section

open CategoryTheory
open GSTSphereUnionComponents
open GSTSingularCohomologyMaps

namespace GSTSphereCycleLegs

/-! ## §1 The cyclic predecessor -/

/-- The cyclic predecessor on `Fin M` (the inverse of `cyclicSucc`). -/
def cyclicPred (M : ℕ) (k : Fin M) : Fin M :=
  ⟨(k.val + (M - 1)) % M,
    Nat.mod_lt (k.val + (M - 1))
      (Nat.lt_of_le_of_lt (Nat.zero_le k.val) k.isLt)⟩

/-- The roundtrip: the successor of the predecessor is the identity. -/
theorem cyclicSucc_cyclicPred (M : ℕ) (j : Fin M) :
    cyclicSucc M (cyclicPred M j) = j := by
  have hj : j.val < M := j.isLt
  have hM : 0 < M := Nat.lt_of_le_of_lt (Nat.zero_le j.val) hj
  apply Fin.ext
  show ((j.val + (M - 1)) % M + 1) % M = j.val
  rw [Nat.mod_add_mod]
  have hadd : j.val + (M - 1) + 1 = j.val + M := by omega
  -- WAVE 58.1: the pin's `Nat.add_mod_left` is `(m + n) % m = n % m`
  -- (modulus = LEFT summand); the needed form is `add_mod_right`.
  rw [hadd, Nat.add_mod_right]
  exact Nat.mod_eq_of_lt hj

/-- The roundtrip: the predecessor of the successor is the identity. -/
theorem cyclicPred_cyclicSucc (M : ℕ) (j : Fin M) :
    cyclicPred M (cyclicSucc M j) = j := by
  have hj : j.val < M := j.isLt
  have hM : 0 < M := Nat.lt_of_le_of_lt (Nat.zero_le j.val) hj
  apply Fin.ext
  show ((j.val + 1) % M + (M - 1)) % M = j.val
  rw [Nat.mod_add_mod]
  have hadd : j.val + 1 + (M - 1) = j.val + M := by omega
  rw [hadd, Nat.add_mod_right]
  exact Nat.mod_eq_of_lt hj

/-- The successor is injective (through the predecessor roundtrip). -/
theorem cyclicSucc_inj (M : ℕ) {a b : Fin M}
    (h : cyclicSucc M a = cyclicSucc M b) : a = b := by
  rw [← cyclicPred_cyclicSucc M a, ← cyclicPred_cyclicSucc M b, h]

/-! ## §2 The constant sphere map -/

/-- The constant sphere endomap at the base point. -/
def constSphereMap (M : ℕ) :
    TopCat.of unitSphereType ⟶ TopCat.of unitSphereType :=
  TopCat.ofHom ⟨fun _ => sphereBase, continuous_const⟩

/-! ## §3 The leg identities -/

/-- **THE CYCLE/COLLAPSE LEG IDENTITY.**  Cycling the union and then
collapsing to the j-th slice is collapsing to the predecessor slice. -/
theorem cycle_comp_collapse (M : ℕ) (j : Fin M) :
    sphereCycle M ≫ sphereCollapse M j =
      sphereCollapse M (cyclicPred M j) := by
  apply TopCat.ext
  intro z
  show (if cyclicSucc M z.1 = j then z.2 else sphereBase) =
      (if z.1 = cyclicPred M j then z.2 else sphereBase)
  by_cases h : cyclicSucc M z.1 = j
  · have hcond : z.1 = cyclicPred M j := by
      rw [← h, cyclicPred_cyclicSucc]
    rw [if_pos h, if_pos hcond]
  · have hcond : ¬ (z.1 = cyclicPred M j) := by
      intro hc
      exact h (by rw [hc, cyclicSucc_cyclicPred])
    rw [if_neg h, if_neg hcond]

/-- **THE OFF-SLICE LEG IDENTITY.**  Including the j-th slice and then
collapsing to a DIFFERENT slice is the constant base-point map. -/
theorem incl_comp_collapse_const (M : ℕ) (i j : Fin M) (hji : j ≠ i) :
    sphereIncl M j ≫ sphereCollapse M i = constSphereMap M := by
  apply TopCat.ext
  intro x
  show (if (Sigma.mk (β := fun _ : Fin M => unitSphereType) j x).1 = i
      then (Sigma.mk (β := fun _ : Fin M => unitSphereType) j x).2
      else sphereBase) = sphereBase
  have hne : ¬ ((Sigma.mk (β := fun _ : Fin M => unitSphereType) j x).1 = i) := by
    show ¬ (j = i)
    exact hji
  rw [if_neg hne]

/-! ## §4 The cohomology-level cycle calculus -/

/-- **THE CYCLIC PERMUTATION ACTION ON COLLAPSE PULLBACKS.**  Pulling back
along the M-cycle and then along the j-th collapse is the collapse at the
predecessor slice — the cohomology-level form of the leg identity. -/
theorem cycle_collapse_calculus (M : ℕ) (j : Fin M) (n : ℕ) :
    (cohomologyPullbackOf (sphereCycle M) n).comp
      (cohomologyPullbackOf (sphereCollapse M j) n) =
        cohomologyPullbackOf (sphereCollapse M (cyclicPred M j)) n := by
  rw [← cohomologyPullbackOf_comp (sphereCycle M) (sphereCollapse M j) n,
    cycle_comp_collapse M j]

/-- **THE OFF-SLICE COLLAPSE PULLBACK.**  The composite restriction along
the off-slice leg is the restriction along the constant map. -/
theorem incl_collapse_const_calculus (M : ℕ) (i j : Fin M) (hji : j ≠ i)
    (n : ℕ) :
    (cohomologyPullbackOf (sphereIncl M j) n).comp
      (cohomologyPullbackOf (sphereCollapse M i) n) =
        cohomologyPullbackOf (constSphereMap M) n := by
  rw [← cohomologyPullbackOf_comp (sphereIncl M j) (sphereCollapse M i) n,
    incl_comp_collapse_const M i j hji]

end GSTSphereCycleLegs
