import Mathlib
import GST2DMixedEmergenceUpgrade
import GSTWorldCosmology

/-!
# GST MIXED-RADIX WORLD DYNAMICS

The physical x4/base-3 transition

  C + 4*d = e + 3*C'

is one chart of a dimension-free arithmetic law.

For arbitrary world widths s and b, the same integer has two canonical
mixed-radix coordinate systems:

  input  : n = C + s*d,
  output : n = e + b*C'.

The transition between those coordinate systems is an actual equivalence
of Fin s x Fin b.  Thus exact balance, uniqueness, invertibility and finite
world closure are structural consequences of mixed-radix representation,
not twelve-cell accidents.
-/

set_option maxHeartbeats 10000000
set_option maxRecDepth 1000000

namespace GSTRadixWorldDynamics

open GST2DMixedEmergence
open GST2DMixedEmergenceUpgrade

/-- Native finite state world for scale s and radix b. -/
abbrev RadixState (s b : Nat) : Type :=
  Fin s × Fin b

/-- Input-chart integer represented by a state (C,d). -/
def inputCode {s b : Nat} (x : RadixState s b) : Nat :=
  x.1.1 + s * x.2.1

/-- Output-chart integer represented by a state (C',e). -/
def outputCode {s b : Nat} (x : RadixState s b) : Nat :=
  x.2.1 + b * x.1.1

/-- Input mixed-radix chart:
(C,d) is read as the integer C + s*d. -/
def inputCodeEquiv (s b : Nat) :
    RadixState s b ≃ Fin (s*b) :=
  (Equiv.prodComm (Fin s) (Fin b)).trans
    ((finProdFinEquiv : Fin b × Fin s ≃ Fin (b*s)).trans
      (finCongr (Nat.mul_comm b s)))

/-- Output mixed-radix chart:
(C',e) is read as the integer e + b*C'. -/
def outputCodeEquiv (s b : Nat) :
    RadixState s b ≃ Fin (s*b) :=
  (finProdFinEquiv : Fin s × Fin b ≃ Fin (s*b))

@[simp]
theorem inputCodeEquiv_val
    {s b : Nat} (x : RadixState s b) :
    (inputCodeEquiv s b x).1 = inputCode x := by
  rfl

@[simp]
theorem outputCodeEquiv_val
    {s b : Nat} (x : RadixState s b) :
    (outputCodeEquiv s b x).1 = outputCode x := by
  rfl

/-- **MIXED-RADIX TRANSPOSE.**

This is the exact coordinate change from the s-low input chart to the
b-low output chart.  It is an equivalence for every finite s,b; positivity
is not required because zero-width worlds are handled vacuously by Fin. -/
def mixedRadixTranspose (s b : Nat) :
    RadixState s b ≃ RadixState s b :=
  (inputCodeEquiv s b).trans (outputCodeEquiv s b).symm

/-- The transition preserves the represented integer exactly. -/
theorem mixedRadixTranspose_balance
    {s b : Nat} (x : RadixState s b) :
    outputCode (mixedRadixTranspose s b x) = inputCode x := by
  have h :
      outputCodeEquiv s b (mixedRadixTranspose s b x) =
        inputCodeEquiv s b x := by
    simp [mixedRadixTranspose]
  exact congrArg Fin.val h

/-- Expanded conservation law. -/
theorem mixedRadixTranspose_conservation
    {s b : Nat} (x : RadixState s b) :
    (mixedRadixTranspose s b x).2.1 +
        b * (mixedRadixTranspose s b x).1.1 =
      x.1.1 + s * x.2.1 := by
  exact mixedRadixTranspose_balance x

/-- A target state satisfying the same mixed-radix conservation equation
is necessarily the canonical transpose. -/
theorem mixedRadixTranspose_unique
    {s b : Nat} (x y : RadixState s b)
    (h : outputCode y = inputCode x) :
    mixedRadixTranspose s b x = y := by
  apply (outputCodeEquiv s b).injective
  apply Fin.ext
  change outputCode (mixedRadixTranspose s b x) = outputCode y
  rw [mixedRadixTranspose_balance, h]

/-- The transition is bijective without any case split. -/
theorem mixedRadixTranspose_bijective (s b : Nat) :
    Function.Bijective (mixedRadixTranspose s b) :=
  (mixedRadixTranspose s b).bijective

/-- Every state has a unique successor satisfying the balance equation. -/
theorem existsUnique_balanced_successor
    {s b : Nat} (x : RadixState s b) :
    ∃! y : RadixState s b,
      outputCode y = inputCode x := by
  refine ⟨mixedRadixTranspose s b x,
    mixedRadixTranspose_balance x, ?_⟩
  intro y hy
  exact (mixedRadixTranspose_unique x y hy).symm

/-- Every output state has a unique predecessor. -/
theorem existsUnique_balanced_predecessor
    {s b : Nat} (y : RadixState s b) :
    ∃! x : RadixState s b,
      outputCode y = inputCode x := by
  refine ⟨(mixedRadixTranspose s b).symm y, ?_, ?_⟩
  · simpa using
      (mixedRadixTranspose_balance
        ((mixedRadixTranspose s b).symm y))
  · intro x hx
    apply (mixedRadixTranspose s b).injective
    simpa using (mixedRadixTranspose_unique x y hx)

/-- The canonical quotient/remainder transition on unrestricted naturals. -/
def radixOut (s b C d : Nat) : Nat :=
  (C + s*d) % b

def radixCarry (s b C d : Nat) : Nat :=
  (C + s*d) / b

/-- Universal quotient/remainder balance, with no physical bounds. -/
theorem radix_balance (s b C d : Nat) :
    b * radixCarry s b C d + radixOut s b C d =
      C + s*d := by
  simpa [radixCarry, radixOut, Nat.mul_comm] using
    Nat.div_add_mod (C + s*d) b

/-- Output digit closure in every positive radix. -/
theorem radixOut_lt
    {s b C d : Nat} (hb : 0 < b) :
    radixOut s b C d < b := by
  exact Nat.mod_lt _ hb

/-- **FINITE-WORLD CLOSURE.**
If the input lies in the s x b world, quotient/remainder transition remains
inside the same s x b world. -/
theorem radixCarry_lt
    {s b C d : Nat}
    (hs : 0 < s) (hb : 0 < b)
    (hC : C < s) (hd : d < b) :
    radixCarry s b C d < s := by
  apply (Nat.div_lt_iff_lt_mul hb).2
  nlinarith

/-- Concrete quotient/remainder state inside a positive finite world. -/
def radixSuccessor
    {s b : Nat} (hs : 0 < s) (hb : 0 < b)
    (x : RadixState s b) :
    RadixState s b :=
  (⟨radixCarry s b x.1.1 x.2.1,
      radixCarry_lt hs hb x.1.2 x.2.2⟩,
   ⟨radixOut s b x.1.1 x.2.1,
      radixOut_lt hb⟩)

/-- The abstract mixed-radix equivalence is exactly ordinary quotient and
remainder on every positive world. -/
theorem mixedRadixTranspose_eq_radixSuccessor
    {s b : Nat} (hs : 0 < s) (hb : 0 < b)
    (x : RadixState s b) :
    mixedRadixTranspose s b x = radixSuccessor hs hb x := by
  apply mixedRadixTranspose_unique
  unfold outputCode inputCode radixSuccessor
  simp only
  rw [show
      radixOut s b x.1.1 x.2.1 +
          b * radixCarry s b x.1.1 x.2.1 =
        b * radixCarry s b x.1.1 x.2.1 +
          radixOut s b x.1.1 x.2.1 by omega]
  exact radix_balance s b x.1.1 x.2.1

/-- The old x4/base-3 output digit is one specialization. -/
theorem outDigit_is_radixOut (C d : Nat) :
    outDigit C d = radixOut 4 3 C d := by
  rfl

/-- The old x4/base-3 carry is one specialization. -/
theorem nextCarry_is_radixCarry (C d : Nat) :
    nextCarry C d = radixCarry 4 3 C d := by
  rfl

/-- Exact specialization of the original twelve-cell transition to the
dimension-free mixed-radix transpose. -/
theorem twelve_cell_transition_is_mixedRadixTranspose
    (C d : Nat) (hC : C < 4) (hd : d < 3) :
    mixedRadixTranspose 4 3
        (⟨C,hC⟩, ⟨d,hd⟩) =
      (⟨nextCarry C d, by
          simpa [nextCarry_is_radixCarry] using
            (radixCarry_lt (s:=4) (b:=3) (C:=C) (d:=d)
              (by decide) (by decide) hC hd)⟩,
       ⟨outDigit C d, by
          simpa [outDigit_is_radixOut] using
            (radixOut_lt (s:=4) (b:=3) (C:=C) (d:=d)
              (by decide))⟩) := by
  have h :=
    mixedRadixTranspose_eq_radixSuccessor
      (s:=4) (b:=3) (by decide) (by decide)
      (⟨C,hC⟩, ⟨d,hd⟩)
  rw [h]
  apply Prod.ext
  · apply Fin.ext
    rfl
  · apply Fin.ext
    rfl

/-- Capstone: exact balance, unique solvability, bijectivity, finite-world
closure, and recovery of the physical 4x3 GST cell are all consequences of
one mixed-radix coordinate-change law. -/
theorem mixed_radix_world_crown :
    (∀ s b, Function.Bijective (mixedRadixTranspose s b))
    ∧ (∀ s b (x : RadixState s b),
        outputCode (mixedRadixTranspose s b x) = inputCode x)
    ∧ (∀ s b (x : RadixState s b),
        ∃! y : RadixState s b, outputCode y = inputCode x)
    ∧ (∀ s b C d, 0 < s → 0 < b → C < s → d < b →
        radixCarry s b C d < s ∧ radixOut s b C d < b) := by
  refine ⟨mixedRadixTranspose_bijective,
    ?_, ?_, ?_⟩
  · intro s b x
    exact mixedRadixTranspose_balance x
  · intro s b x
    exact existsUnique_balanced_successor x
  · intro s b C d hs hb hC hd
    exact ⟨radixCarry_lt hs hb hC hd, radixOut_lt hb⟩

#check mixedRadixTranspose
#check mixedRadixTranspose_conservation
#check mixedRadixTranspose_unique
#check mixedRadixTranspose_bijective
#check existsUnique_balanced_successor
#check existsUnique_balanced_predecessor
#check radix_balance
#check radixCarry_lt
#check mixedRadixTranspose_eq_radixSuccessor
#check twelve_cell_transition_is_mixedRadixTranspose
#check mixed_radix_world_crown

#print axioms mixedRadixTranspose_conservation
#print axioms mixedRadixTranspose_unique
#print axioms existsUnique_balanced_successor
#print axioms radixCarry_lt
#print axioms twelve_cell_transition_is_mixedRadixTranspose
#print axioms mixed_radix_world_crown

end GSTRadixWorldDynamics
