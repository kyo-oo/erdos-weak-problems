import Mathlib

set_option maxRecDepth 1000000
set_option maxHeartbeats 10000000

namespace GSTV2

/-!
# GST V2 production infinite-control core

This module is intentionally independent of `ErdosTernary2.lean`.
It contains only all-Nat information/control primitives that can be imported
by the monolith without creating a circular proof dependency.
-/

inductive Space
  | null
  | altMinus
  | gstPlus
  deriving DecidableEq, Repr

def digit (N k : Nat) : Nat := N / 3^k % 3

def cellMass (carry d : Nat) : Nat := carry + 4*d

def cellOutput (carry d : Nat) : Nat := cellMass carry d % 3

def cellNextCarry (carry d : Nat) : Nat := cellMass carry d / 3

theorem cell_mass_conservation (carry d : Nat) :
    cellMass carry d = cellOutput carry d + 3 * cellNextCarry carry d := by
  unfold cellMass cellOutput cellNextCarry
  exact (Nat.mod_add_div (carry + 4*d) 3).symm

def omegaTransfer (t N k : Nat) : Nat := 3^(t+1+k) * digit N k

def omegaPast (t N K : Nat) : Nat :=
  Finset.sum (Finset.range K) (fun k => omegaTransfer t N k)

def omegaFuture (t N K : Nat) : Nat := 3^(t+1+K) * (N / 3^K)

theorem digit_prefix_value (N K : Nat) :
    Finset.sum (Finset.range K) (fun k => 3^k * digit N k) = N % 3^K := by
  induction K with
  | zero =>
      change 0 = N % 1
      exact (Nat.mod_one N).symm
  | succ K ih =>
      rw [Finset.sum_range_succ, ih]
      unfold digit
      rw [Nat.pow_succ, Nat.mod_mul]

theorem omega_past_closed (t N K : Nat) :
    omegaPast t N K = 3^(t+1) * (N % 3^K) := by
  unfold omegaPast omegaTransfer
  calc
    Finset.sum (Finset.range K) (fun k => 3^(t+1+k) * digit N k) =
        Finset.sum (Finset.range K) (fun k => 3^(t+1) * (3^k * digit N k)) := by
          apply Finset.sum_congr rfl
          intro k hk
          rw [Nat.pow_add]
          ring
    _ = 3^(t+1) * Finset.sum (Finset.range K) (fun k => 3^k * digit N k) := by
          rw [Finset.mul_sum]
    _ = 3^(t+1) * (N % 3^K) := by
          rw [digit_prefix_value]

theorem omega_past_future_conservation (t N K : Nat) :
    omegaPast t N K + omegaFuture t N K = 3^(t+1) * N := by
  rw [omega_past_closed]
  unfold omegaFuture
  have hpow : 3^(t+1+K) = 3^(t+1) * 3^K := by
    rw [Nat.pow_add]
  rw [hpow]
  have hsplit : N = N % 3^K + 3^K * (N / 3^K) := by
    have h := Nat.mod_add_div N (3^K)
    omega
  calc
    3^(t+1) * (N % 3^K) +
        (3^(t+1) * 3^K) * (N / 3^K) =
      3^(t+1) * (N % 3^K + 3^K * (N / 3^K)) := by ring
    _ = 3^(t+1) * N := by rw [← hsplit]

theorem omega_past_step (t N K : Nat) :
    omegaPast t N (K+1) = omegaPast t N K + omegaTransfer t N K := by
  unfold omegaPast
  rw [Finset.sum_range_succ]

end GSTV2
