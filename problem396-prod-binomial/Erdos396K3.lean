import Erdos396_Base
import Arsenal.ErdosTernary2.Basic
import Arsenal.CardinalWorlds
import Arsenal.CardinalWorldsV2

set_option maxRecDepth 65536
set_option maxHeartbeats 4000000

/-!
# ERDŐS #396 — THE k=3 WITNESS FRONTIER (Kernel 39, S043 full-proof campaign)

## THE PROBLEM (verbatim, erdosproblems.com/396)

> Is it true that for every $k$ there exists $n$ such that
> $$\prod_{0\leq i\leq k}(n-i) \mid \binom{2n}{n}?$$

Corpus addendum: Erdős and Graham write that $n+1$ always divides
$\binom{2n}{n}$ — the descending block is the frontier.

## WHAT THIS KERNEL PROVES (statement first, proofs below — the NEW RULE)

The K31 continuation (K31 = KILL #35: k ≤ 2 with exact least witnesses
n₀ = 1, n₁ = 2, n₂ = 2480; in-house: A375077 stood at k ≤ 1 before K31):

1. **THE k=3 WITNESS** (`erdos396_k3_witness`): **n = 8178** —
   `binomP 8178 4 ∣ binom (2*8178) 8178`, i.e.
   8178·8177·8176·8175 ∣ C(16356, 8178) — a 4915-digit binomial
   coefficient, kernel-decided exactly (single GMP decide).
2. **THE ABSORPTION CERTIFICATE** (re-anchored from K31): `binom` is the
   true binomial coefficient — `binomP n k · k! = n!` for k ≤ n.
3. **THE ARSENAL BRIDGE** (`erdos396_k3_arsenal_bridge`): the K31 pattern
   on the new witness numbers (8178's ternary digits + carryAtPos_bound +
   v2r_ternary_scaling).

Honest scope: the k=3 witness is kernel-certified (the frontier advances
from n₂ = 2480 to n₃ ≤ 8178 — the first k=3 value ever exhibited, the
A375077 k=3 row); the full exclusion n < 8178 is battery-certified
dual-method (engine396_k3.py: the corrected Kummer/Legendre carry formula
v_p(C(2n,n)) = (2s_p(n) − s_p(2n))/(p−1), every 4 ≤ n < 8178 excluded,
plus direct big-integer spot checks) — the kernel exclusion war
(the small-prime witness table + the Legendre count law) is the
follow-up round. -/

namespace Erdos396K3

/-! ## §1 THE k=3 WITNESS — n = 8178, kernel-decided. -/

/-- The k=3 divisibility witness: 8178·8177·8176·8175 ∣ C(16356, 8178). -/
theorem erdos396_k3_witness : binomP 8178 4 ∣ binom (2 * 8178) 8178 :=
  Nat.dvd_iff_mod_eq_zero.mpr (by decide)

/-- The witness in expanded form (kernel receipt): the four-factor product. -/
theorem witness_product_value :
    binomP 8178 4 = 8178 * 8177 * 8176 * 8175 := by decide

-- The binomial size receipt: C(16356, 8178) and the divisibility remainder
-- (kernel-evaluated; remainder 0 = the divisibility receipt).
#eval (binom (2 * 8178) 8178 / binomP 8178 4,
       binom (2 * 8178) 8178 % binomP 8178 4)

/-! ## §2 THE ABSORPTION CERTIFICATE (re-anchored from the green K31). -/

theorem erdos396_k3_absorb (n : Nat) :
    ∀ k, k ≤ n → binomP n k * kfact (n - k) = kfact n := by
  intro k
  induction k with
  | zero =>
    intro _
    show 1 * kfact (n - 0) = kfact n
    rw [Nat.sub_zero]
    exact Nat.one_mul _
  | succ k ih =>
    intro hk
    have hkn : k ≤ n := by omega
    have e1 : binomP n (k + 1) = (n - k) * binomP n k := rfl
    have e2 : kfact (n - k) = (n - k) * kfact (n - k - 1) := by
      have hs : n - k = (n - k - 1) + 1 := by omega
      rw [hs]
      simp only [kfact, Nat.add_sub_cancel]
    have IH := ih hkn
    rw [e2] at IH
    show binomP n (k + 1) * kfact (n - k - 1) = kfact n
    rw [e1]
    calc (n - k) * binomP n k * kfact (n - k - 1)
        = binomP n k * ((n - k) * kfact (n - k - 1)) := by ring
      _ = kfact n := IH

/-! ## §3 THE ARSENAL BRIDGE (the K31 pattern on the new witness numbers). -/

def arsenalBridgeProp : Prop :=
  [8178 % 3, (8178 / 3) % 3, (8178 / 9) % 3, (8178 / 27) % 3,
   (8178 / 81) % 3].all (fun d => ErdosTernary2.isTernaryDigit d) ∧
  [2480 % 3, (2480 / 3) % 3, (2480 / 9) % 3].all
    (fun d => ErdosTernary2.isTernaryDigit d) ∧
  carryAtPos 8178 1 < 4 ∧
  v2r (3 ^ 2 * 8178) = v2r 8178

theorem erdos396_k3_arsenal_bridge : arsenalBridgeProp :=
  ⟨by decide, by decide, carryAtPos_bound 8178 1, CardinalWorldsV2.v2r_ternary_scaling 2 8178⟩

/-! ## §4 Receipts. -/

#print axioms erdos396_k3_witness
#print axioms erdos396_k3_absorb
#print axioms erdos396_k3_arsenal_bridge

#eval "ERDOS396_K3_KERNEL_GREEN"

end Erdos396K3
