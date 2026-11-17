import GSTHodgeGSTWaveGeometricCompiler
import Mathlib

/-!
# GST Wave-to-native cyclic fold completion: actual cycle operator and Betti square

The combined Wave-I/II/CM graph supplies explicit finite orbital source
vectors. The 2026-11-09 exact sixfold computation found that the first nine
primitive wave-projected Chow vectors form a rational independent frame,
but their 12-dimensional Wave fold does NOT descend to the nine-dimensional
primitive quotient. This module gives the rigorous correct replacement:

Given any nonempty finite family of ACTUAL original-X rational algebraic
cycles together with geometrically compatible rational dual readouts,
construct a NEW native cyclic endomorphism, plus a cohomology action
automatically commuting with the canonical cycle-class map. This is a
finite-prefix geometric completion, NOT an invalid all-wave quotient.
The duals must actually arise from geometry in each application; the
sixfold example supplies them by complementary divisor intersections.

The construction is dimension-independent in rank (n+1) and works with
any rational modules and any canonical cycle-class linear map.
-/

namespace GSTHodgeWaveFiniteCyclicCompletion

open scoped BigOperators

/-- The cyclic information address of a nonempty n+1-channel world.
It does not assign a spatial dimension to the underlying GST carrier. -/
def nextIndex (n : ℕ) (i : Fin (n+1)) : Fin (n+1) :=
  ⟨(i.val+1) % (n+1), Nat.mod_lt _ (Nat.succ_pos n)⟩

@[simp] theorem nextIndex_last (n : ℕ) :
    nextIndex n ⟨n, Nat.lt_succ_self n⟩ = 0 := by
  apply Fin.ext
  simp [nextIndex]

/-- Exact information-index evolution by one cyclic step. -/
theorem nextIndex_mod (n k : ℕ) :
    nextIndex n ⟨k % (n+1), Nat.mod_lt _ (Nat.succ_pos n)⟩ =
    ⟨(k+1) % (n+1), Nat.mod_lt _ (Nat.succ_pos n)⟩ := by
  apply Fin.ext
  simp [nextIndex, Nat.add_mod, Nat.mod_mod]

section GenericFold

variable {A : Type*} [AddCommGroup A] [Module ℚ A]
variable {B : Type*} [AddCommGroup B] [Module ℚ B]

/-- A cyclic native fold reconstructed from a finite algebraic frame,
using independently geometric rational dual functionals. -/
def rotateFold (n : ℕ)
    (atoms : Fin (n+1) → A)
    (dual : Fin (n+1) → (A →ₗ[ℚ] ℚ)) : A →ₗ[ℚ] A where
  toFun x := ∑ i : Fin (n+1), (dual i x) • atoms (nextIndex n i)
  map_add' := by
    intro x y
    simp only [map_add, add_smul, Finset.sum_add_distrib]
  map_smul' := by
    intro r x
    simp [map_smul, smul_smul, Finset.smul_sum, smul_eq_mul]

@[simp] theorem rotateFold_apply (n : ℕ)
    (atoms : Fin (n+1) → A)
    (dual : Fin (n+1) → (A →ₗ[ℚ] ℚ)) (x : A) :
    rotateFold n atoms dual x =
      ∑ i : Fin (n+1), (dual i x) • atoms (nextIndex n i) := rfl

/-- Finite native cycles, dual source readouts, and the Betti-compatible
intersection duals needed to transport the newly synthesized fold. -/
structure GeometricCyclicFrame (n : ℕ)
    (cl : A →ₗ[ℚ] B) where
  atom : Fin (n+1) → A
  nativeDual : Fin (n+1) → (A →ₗ[ℚ] ℚ)
  bettiDual : Fin (n+1) → (B →ₗ[ℚ] ℚ)
  dual_atom : ∀ i j, nativeDual i (atom j) = if i=j then 1 else 0
  dual_class : ∀ i (z : A), bettiDual i (cl z) = nativeDual i z

namespace GeometricCyclicFrame

variable {n : ℕ} {cl : A →ₗ[ℚ] B}

/-- The new actual original-carrier native fold. -/
def nativeFold (F : GeometricCyclicFrame n cl) : A →ₗ[ℚ] A :=
  rotateFold n F.atom F.nativeDual

/-- The cohomological operator is *constructed* from the same frame;
its action is not postulated independently from the cycles. -/
def bettiFold (F : GeometricCyclicFrame n cl) : B →ₗ[ℚ] B :=
  rotateFold n (fun i => cl (F.atom i)) F.bettiDual

/-- The important exact commuting square for every native cycle. -/
theorem nativeFold_cycleClass (F : GeometricCyclicFrame n cl) (z : A) :
    cl (F.nativeFold z) = F.bettiFold (cl z) := by
  simp [nativeFold, bettiFold, rotateFold_apply, map_sum, map_smul,
    F.dual_class]

/-- Linear-map naturality, allowing a genuine CycleClassOperatorPair on
the original smooth projective variety, given its actual Betti map. -/
theorem cycleClass_square (F : GeometricCyclicFrame n cl) :
    cl.comp F.nativeFold = F.bettiFold.comp cl := by
  ext z
  exact F.nativeFold_cycleClass z

/-- The constructed fold actually moves the j-th algebraic class to
the following one, rather than merely producing an operator diagram. -/
theorem nativeFold_atom (F : GeometricCyclicFrame n cl)
    (j : Fin (n+1)) :
    F.nativeFold (F.atom j) = F.atom (nextIndex n j) := by
  simp [nativeFold, rotateFold_apply, F.dual_atom]

/-- The same property holds for the genuine Betti classes. -/
theorem bettiFold_atom (F : GeometricCyclicFrame n cl)
    (j : Fin (n+1)) :
    F.bettiFold (cl (F.atom j)) =
      cl (F.atom (nextIndex n j)) := by
  rw [← F.nativeFold_cycleClass]
  exact congrArg cl (F.nativeFold_atom j)

/-- The precise wave-born finite prefix, extended cyclically by the
NEW native geometric operator rather than the old wave quotient. -/
def atomOrbit (F : GeometricCyclicFrame n cl) (k : ℕ) : A :=
  F.atom ⟨k % (n+1), Nat.mod_lt _ (Nat.succ_pos n)⟩

theorem nativeFold_atomOrbit_succ (F : GeometricCyclicFrame n cl)
    (k : ℕ) :
    F.nativeFold (F.atomOrbit k) = F.atomOrbit (k+1) := by
  unfold atomOrbit
  rw [F.nativeFold_atom]
  exact congrArg F.atom (nextIndex_mod n k)

theorem atomOrbit_period (F : GeometricCyclicFrame n cl) :
    F.atomOrbit (n+1) = F.atomOrbit 0 := by
  simp [atomOrbit]

end GeometricCyclicFrame
end GenericFold

#check nextIndex_mod
#check GeometricCyclicFrame.nativeFold_cycleClass
#check GeometricCyclicFrame.nativeFold_atomOrbit_succ
#check GeometricCyclicFrame.atomOrbit_period
#print axioms GeometricCyclicFrame.nativeFold_cycleClass
#print axioms GeometricCyclicFrame.nativeFold_atomOrbit_succ

end GSTHodgeWaveFiniteCyclicCompletion
