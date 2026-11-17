import Mathlib
import GSTWorldCosmology
import GSTLefschetzCrown

/-!
# GST WORLD CROWN BRIDGE — old twelve-cell cups absorbed by native transport

This layer proves that the original twelve-cell cup operators are not
independent laws.  Under the exact chart equivalence of
`GSTWorldCosmology`, they are the one-step native axis transports.

Consequently commutation and the 3/4 boundary nilpotence are inherited
from the dimension-free world laws.
-/

set_option maxHeartbeats 10000000
set_option maxRecDepth 1000000

namespace GSTWorldCrownBridge

open GSTWaveCohomology
open GSTWorldCosmology
open GSTLefschetzCrown

/-- Export into the native 4 × 3 chart is injective. -/
theorem liftWave_injective : Function.Injective liftWave := by
  intro f g h
  calc
    f = lowerWave (liftWave f) := (lowerWave_liftWave f).symm
    _ = lowerWave (liftWave g) := congrArg lowerWave h
    _ = g := lowerWave_liftWave g

/-- The old digit-cup is exactly one native digit-axis transport. -/
theorem liftWave_cupDigit (g : WaveCoef) :
    liftWave (cupDigit g) = digitShiftN 1 (liftWave g) := by
  funext c
  rcases c with ⟨⟨C,hC⟩,⟨d,hd⟩⟩
  interval_cases C <;> interval_cases d <;> rfl

/-- The old carry-cup is exactly one native carry-axis transport. -/
theorem liftWave_cupCarry (g : WaveCoef) :
    liftWave (cupCarry g) = carryShiftN 1 (liftWave g) := by
  funext c
  rcases c with ⟨⟨C,hC⟩,⟨d,hd⟩⟩
  interval_cases C <;> interval_cases d <;> rfl

/-- **ABSORBED COMMUTATION.**  The old cup commutation is a chart theorem
of the native rectangle law, not a separate twelve-case fact. -/
theorem cup_comm_from_native (g : WaveCoef) :
    cupDigit (cupCarry g) = cupCarry (cupDigit g) := by
  apply liftWave_injective
  calc
    liftWave (cupDigit (cupCarry g))
        = digitShiftN 1 (liftWave (cupCarry g)) :=
            liftWave_cupDigit (cupCarry g)
    _ = digitShiftN 1 (carryShiftN 1 (liftWave g)) := by
          rw [liftWave_cupCarry]
    _ = carryShiftN 1 (digitShiftN 1 (liftWave g)) :=
          axes_commute 1 1 (liftWave g)
    _ = carryShiftN 1 (liftWave (cupDigit g)) := by
          rw [liftWave_cupDigit]
    _ = liftWave (cupCarry (cupDigit g)) :=
          (liftWave_cupCarry (cupDigit g)).symm

/-- Three old digit cups vanish because the native digit depth of this chart
is three. -/
theorem cupDigit_cubed_native_zero (g : WaveCoef) :
    cupDigit (cupDigit (cupDigit g)) = fun _ => 0 := by
  apply liftWave_injective
  have hchain :
      liftWave (cupDigit (cupDigit (cupDigit g))) =
        digitShiftN 3 (liftWave g) := by
    calc
      liftWave (cupDigit (cupDigit (cupDigit g)))
          = digitShiftN 1 (liftWave (cupDigit (cupDigit g))) :=
              liftWave_cupDigit (cupDigit (cupDigit g))
      _ = digitShiftN 1 (digitShiftN 1 (liftWave (cupDigit g))) := by
            rw [liftWave_cupDigit]
      _ = digitShiftN 1 (digitShiftN 1 (digitShiftN 1 (liftWave g))) := by
            rw [liftWave_cupDigit]
      _ = digitShiftN 2 (digitShiftN 1 (liftWave g)) :=
            digitShiftN_add 1 1 (digitShiftN 1 (liftWave g))
      _ = digitShiftN 3 (liftWave g) := by
            simpa using digitShiftN_add 2 1 (liftWave g)
  have hzero :
      digitShiftN 3 (liftWave g) =
        liftWave (fun _ : WaveCell => (0 : ℤ)) := by
    rw [digit_boundary_extinction]
    rfl
  exact hchain.trans hzero

/-- Four old carry cups vanish because the native carry depth of this chart
is four. -/
theorem cupCarry_fourth_native_zero (g : WaveCoef) :
    cupCarry (cupCarry (cupCarry (cupCarry g))) = fun _ => 0 := by
  apply liftWave_injective
  have hchain :
      liftWave (cupCarry (cupCarry (cupCarry (cupCarry g)))) =
        carryShiftN 4 (liftWave g) := by
    calc
      liftWave (cupCarry (cupCarry (cupCarry (cupCarry g))))
          = carryShiftN 1 (liftWave (cupCarry (cupCarry (cupCarry g)))) :=
              liftWave_cupCarry (cupCarry (cupCarry (cupCarry g)))
      _ = carryShiftN 1 (carryShiftN 1 (liftWave (cupCarry (cupCarry g)))) := by
            rw [liftWave_cupCarry]
      _ = carryShiftN 1 (carryShiftN 1 (carryShiftN 1 (liftWave (cupCarry g)))) := by
            rw [liftWave_cupCarry]
      _ = carryShiftN 1
            (carryShiftN 1 (carryShiftN 1 (carryShiftN 1 (liftWave g)))) := by
            rw [liftWave_cupCarry]
      _ = carryShiftN 2
            (carryShiftN 1 (carryShiftN 1 (liftWave g))) :=
            carryShiftN_add 1 1
              (carryShiftN 1 (carryShiftN 1 (liftWave g)))
      _ = carryShiftN 3 (carryShiftN 1 (liftWave g)) := by
            simpa using carryShiftN_add 2 1 (carryShiftN 1 (liftWave g))
      _ = carryShiftN 4 (liftWave g) := by
            simpa using carryShiftN_add 3 1 (liftWave g)
  have hzero :
      carryShiftN 4 (liftWave g) =
        liftWave (fun _ : WaveCell => (0 : ℤ)) := by
    rw [carry_boundary_extinction]
    rfl
  exact hchain.trans hzero

/-- The original pointwise cubed theorem, now derived from the native
dimension-free boundary law. -/
theorem cupDigit_cubed_from_native (g : WaveCoef) :
    ∀ (C : Nat) (d : Nat) (hC : C < 4) (hd : d < 3),
      (Nat.iterate cupDigit 3 g) ⟨C, d, hC, hd⟩ = 0 := by
  intro C d hC hd
  change cupDigit (cupDigit (cupDigit g)) ⟨C, d, hC, hd⟩ = 0
  rw [cupDigit_cubed_native_zero]

/-- The original pointwise fourth theorem, now derived from the native
dimension-free boundary law. -/
theorem cupCarry_fourth_from_native (g : WaveCoef) :
    ∀ (C : Nat) (d : Nat) (hC : C < 4) (hd : d < 3),
      (Nat.iterate cupCarry 4 g) ⟨C, d, hC, hd⟩ = 0 := by
  intro C d hC hd
  change cupCarry (cupCarry (cupCarry (cupCarry g))) ⟨C, d, hC, hd⟩ = 0
  rw [cupCarry_fourth_native_zero]

/-- **THE CROWN ABSORPTION RECEIPT.**  The three foundational cup laws of
the old 4 × 3 crown are consequences of the dimension-free GST world. -/
theorem crown_laws_absorbed :
    (∀ g : WaveCoef,
      cupDigit (cupCarry g) = cupCarry (cupDigit g))
    ∧ (∀ g : WaveCoef,
      cupDigit (cupDigit (cupDigit g)) = fun _ => 0)
    ∧ (∀ g : WaveCoef,
      cupCarry (cupCarry (cupCarry (cupCarry g))) = fun _ => 0) :=
  ⟨cup_comm_from_native, cupDigit_cubed_native_zero,
    cupCarry_fourth_native_zero⟩

#check liftWave_cupDigit
#check liftWave_cupCarry
#check cup_comm_from_native
#check cupDigit_cubed_native_zero
#check cupCarry_fourth_native_zero
#check cupDigit_cubed_from_native
#check cupCarry_fourth_from_native
#check crown_laws_absorbed

#print axioms liftWave_cupDigit
#print axioms liftWave_cupCarry
#print axioms cup_comm_from_native
#print axioms cupDigit_cubed_native_zero
#print axioms cupCarry_fourth_native_zero
#print axioms crown_laws_absorbed

end GSTWorldCrownBridge
