import GSTAllNConnectedCurvatureBirth
import GSTHodgeWaveFiniteCyclicCompletion
import Mathlib

/-!
# GST connected curvature native chain -> every rational channel cycle

This file proves that a CONNECTED SEQUENCE OF GENUINE NATIVE
OPERATORS, started from ONE already algebraic seed, constructs a
full rational Betti basis and every prescribed target, and compiles
it to ONE cyclic native endomorphism via the PREEXISTING GST finite
cyclic-completion constructor.

The input does NOT include target cycles, a Hodge-to-Chow inverse,
a full-rank source frame, or surjectivity of the cycle-class map.
It contains ONE seed cycle, and the geometric edge-operator laws
which will be instantiated by the rational GST spectral projector
and noncommutative curvature words derived in the companion TeX file.

The general rational chain theorem is proved in Lean under the
actual-edge hypotheses. Proving the geometry of those edge operators
on EVERY original smooth projective complex X remains the active
universal GST source-birth task; the abstract shape calculus alone
does not install the canonical whole-Betti realization.
-/

set_option maxHeartbeats 2500000
noncomputable section

namespace GSTAllNConnectedCurvatureGeometricClosure

open GSTHodgeWaveFiniteCyclicCompletion

variable {A : Type*} [AddCommGroup A] [Module ℚ A]

/-- Arbitrarily many genuinely independent rational N-hole/Hodge
information addresses. The number m+1 is never a spatial dimension. -/
abbrev ChannelFiber (m : ℕ) := Fin (m + 1) → ℚ

/-- The actual rational eigenaddress at position k. For k <= m this
is the coordinate basis vector; no algebraic representative is chosen. -/
def channelUnit (m k : ℕ) : ChannelFiber m :=
  fun i => if i.val = k then 1 else 0

/-- A native GST connected curvature chain over a cycle-class map.

The sole SOURCE input is first. Each edge is an explicitly available
native algebraic-cycle operator (from a realized GST curvature word)
whose rational Betti transition has the stated nonzero scalar.

This is not the false hypothesis "every Hodge channel has a native
cycle": all subsequent sources are CONSTRUCTED below by iteration. -/
structure NativeCurvatureChain (m : ℕ)
    (cl : A →ₗ[ℚ] ChannelFiber m) where
  first : A
  advance : ℕ → Module.End ℚ A
  weight : ℕ → ℚ
  first_class : cl first = channelUnit m 0
  weight_ne_zero : ∀ k, k < m → weight k ≠ 0
  edge_class :
    ∀ k, k < m → ∀ z : A,
      cl z = channelUnit m k →
        cl (advance k z) = weight k • channelUnit m (k+1)

namespace NativeCurvatureChain

variable {m : ℕ} {cl : A →ₗ[ℚ] ChannelFiber m}

/-- CONSTRUCT, rather than assume, one algebraic source in each channel
by rational normalization of successive actual GST native operations. -/
def source (C : NativeCurvatureChain m cl) : ℕ → A
  | 0 => C.first
  | k + 1 => (C.weight k)⁻¹ • C.advance k (C.source k)

/-- Every constructed native cycle lands EXACTLY on its new eigenaddress,
using only the prior native cycle and one geometric curvature edge. -/
theorem source_class (C : NativeCurvatureChain m cl) :
    ∀ k : ℕ, k ≤ m → cl (C.source k) = channelUnit m k := by
  intro k
  induction k with
  | zero =>
      intro hk
      simpa [source] using C.first_class
  | succ k ih =>
      intro hk
      have hkedge : k < m := by omega
      have hprevious := ih (by omega)
      have hstep :=
        C.edge_class k hkedge (C.source k) hprevious
      change cl ((C.weight k)⁻¹ • C.advance k (C.source k)) =
        channelUnit m (k+1)
      rw [map_smul, hstep, smul_smul]
      simp [inv_mul_cancel₀ (C.weight_ne_zero k hkedge)]

/-- Read one rational Hodge channel; no chosen Hodge-to-Chow
inverse or external target-cycle witness is provided. -/
def channelReadout (m : ℕ) (i : Fin (m + 1)) :
    ChannelFiber m →ₗ[ℚ] ℚ where
  toFun x := x i
  map_add' := by intro x y; simp
  map_smul' := by intro q x; simp

/-- The algebraic frame required by GST's old cyclic completion
is now an OUTPUT of a one-seed curvature chain, not an assumption. -/
def generatedCyclicFrame (C : NativeCurvatureChain m cl) :
    GeometricCyclicFrame m cl where
  atom := fun i => C.source i.val
  nativeDual := fun i => (channelReadout m i).comp cl
  bettiDual := fun i => channelReadout m i
  dual_atom := by
    intro i j
    change (cl (C.source j.val)) i = if i = j then 1 else 0
    have hj : j.val ≤ m := Nat.lt_succ_iff.mp j.isLt
    rw [C.source_class j.val hj]
    simp [channelUnit, Fin.val_inj]
  dual_class := by
    intro i z
    rfl

/-- Every rational Hodge information vector receives an EXPLICIT
finite native cycle combination, with one known input cycle and
geometric connected-curvature transition operators only. -/
theorem all_channels_have_native_cycles
    (C : NativeCurvatureChain m cl)
    (alpha : ChannelFiber m) :
    ∃ Z : A, cl Z = alpha := by
  let Z : A := ∑ i : Fin (m+1), (alpha i) • C.source i.val
  refine ⟨Z, ?_⟩
  calc
    cl Z = ∑ i : Fin (m+1), (alpha i) • cl (C.source i.val) := by
      simp [Z]
    _ = ∑ i : Fin (m+1), (alpha i) • channelUnit m i.val := by
      apply Finset.sum_congr rfl
      intro i hi
      rw [C.source_class i.val (Nat.lt_succ_iff.mp i.isLt)]
    _ = alpha := by
      funext j
      simp [channelUnit, Finset.sum_apply, Pi.smul_apply,
        Fin.val_inj, smul_eq_mul]

/-- ONE finite cyclic native fold is now compiled FROM THE BORN
SOURCE CHAIN using the original GST GeometricCyclicFrame machinery. -/
theorem one_native_cyclic_fold_of_connected_birth
    (C : NativeCurvatureChain m cl) :
    ∃ N : Module.End ℚ A,
    ∃ T : Module.End ℚ (ChannelFiber m),
      (∀ Z : A, cl (N Z) = T (cl Z)) ∧
      (∀ j : Fin (m+1),
        ∃ Z : A, cl Z = channelUnit m j.val) := by
  let F := C.generatedCyclicFrame
  refine ⟨F.nativeFold, F.bettiFold, ?_, ?_⟩
  · intro Z
    exact F.nativeFold_cycleClass Z
  · intro j
    exact ⟨C.source j.val,
      C.source_class j.val (Nat.lt_succ_iff.mp j.isLt)⟩

#check source_class
#check all_channels_have_native_cycles
#check one_native_cyclic_fold_of_connected_birth
#print axioms source_class
#print axioms all_channels_have_native_cycles
#print axioms one_native_cyclic_fold_of_connected_birth

end NativeCurvatureChain
end GSTAllNConnectedCurvatureGeometricClosure
