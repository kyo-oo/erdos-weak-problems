import GSTGraphV2CMWaveFusion
import Mathlib

/-!
# GST Image 3 — arbitrary finite-N companion native source transport

The ORIGINAL Wave-I U, CM J, real SURVIVE M and arbitrary
independent N-hole coordinates remain unchanged. The new
companion source has off-diagonal source couplings and ZERO
diagonal when the source polynomial trace coefficient is zero.

The complete all-finite-N cyclicity proof, using the existing
original rational-source determinant theorem and polynomial CRT,
is recorded in the companion mathematical derivation. This file
formalizes its new native operator and the zero-local-M law.
-/

set_option maxHeartbeats 2000000
noncomputable section

namespace GSTImageThreeCompanionSourceTransport

open GSTGraphV2CMWaveFusion

/-- Rational companion N-hole source transport, with a forward
navigation spine and a polynomial return column. -/
def companionSource (N : Nat) (coeff : Nat → ℚ) :
    Matrix (Fin N) (Fin N) ℚ :=
  fun i j =>
    if i.val = j.val + 1 then 1
    else if j.val + 1 = N then -coeff i.val
    else 0

/-- Every nonterminal native hole is connected to its successor
by an exact rational source-transport coefficient ONE. -/
theorem companionSource_forward_edge
    (N : Nat) (coeff : Nat → ℚ)
    (j : Fin N) (hj : j.val + 1 < N) :
    companionSource N coeff
      (⟨j.val + 1, hj⟩ : Fin N) j = 1 := by
  simp [companionSource]

/-- EXACT no-local-SURVIVE-source condition for all N:
zero coefficient of the next-to-leading source polynomial
forces all companion diagonal entries to be zero. -/
theorem companionSource_zero_diagonal
    (N : Nat) (coeff : Nat → ℚ)
    (htrace : coeff (N - 1) = 0)
    (i : Fin N) :
    companionSource N coeff i i = 0 := by
  have hneq : i.val ≠ i.val + 1 := by omega
  by_cases hlast : i.val + 1 = N
  · have hi : i.val = N - 1 := by omega
    simp [companionSource, hneq, hlast, hi, htrace]
  · simp [companionSource, hneq, hlast]

/-- Extend the TRUE original U+J+SURVIVE native operator to arbitrary
independent finite N-cohomology holes. Cross-hole source uses M itself. -/
def globalSourceF (N : Nat)
    (source address : Matrix (Fin N) (Fin N) ℚ)
    (v : Fin N → WaveSignal) : Fin N → WaveSignal :=
  fun i =>
    U (v i) + J (v i)
      + (∑ j : Fin N, source i j • M (v j))
      + (∑ j : Fin N, address i j • v j)

/-- Use the canonical rational companion for source generation;
address is the polynomial navigation readout f(companion) of the
self-contained mathematical derivation. -/
def nativeCompanionF (N : Nat) (coeff : Nat → ℚ)
    (address : Matrix (Fin N) (Fin N) ℚ)
    (v : Fin N → WaveSignal) : Fin N → WaveSignal :=
  globalSourceF N (companionSource N coeff) address v

/-- All original GST holes are local-SURVIVE-free; their source
activation arises only through cross-world native transport. -/
theorem nativeCompanionF_local_source_coefficient_zero
    (N : Nat) (coeff : Nat → ℚ)
    (htrace : coeff (N - 1) = 0) (i : Fin N) :
    companionSource N coeff i i = 0 :=
  companionSource_zero_diagonal N coeff htrace i

#check companionSource
#check companionSource_forward_edge
#check companionSource_zero_diagonal
#check globalSourceF
#check nativeCompanionF
#check nativeCompanionF_local_source_coefficient_zero

#print axioms companionSource_forward_edge
#print axioms companionSource_zero_diagonal
#print axioms nativeCompanionF_local_source_coefficient_zero

end GSTImageThreeCompanionSourceTransport
