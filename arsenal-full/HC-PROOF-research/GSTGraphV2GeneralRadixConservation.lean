import Mathlib
import GSTGraphV2InformationRecovery

/-!
# GST dimensionless information transformations: arbitrary-radix law

The original seven-axis x4/base3 primitive cell is a special member
of a family of information-preserving digit/carry coordinate changes.

For every pair of positive radices m,n and every natural information
code t, the exact reordered-code equation is

  F_{m,n}(t) + (m*n - 1) * floor(t/n) = m*t,

where F_{m,n}(t)=floor(t/n)+m*(t mod n).

Consequently the GST rearrangement acts as multiplication by m modulo
m*n-1.  This gives a structural explanation of the local x4/base3
fivefold period (4 has order five modulo 11). No spatial dimension,
analytic limit or cohomology class is introduced by the equation.
-/

namespace GSTGraphV2GeneralRadixConservation

/-- The generalized arithmetic information reshuffle. -/
def reshuffleCode (m n t : Nat) : Nat :=
  t / n + m * (t % n)

/-- Exact conservation/balance at arbitrary positive radix pair.
The quotient is retained, not erased. -/
theorem reshuffle_mass_balance (m n t : Nat)
    (hm : 0 < m) (hn : 0 < n) :
    reshuffleCode m n t + (m*n - 1)*(t/n) = m*t := by
  have hmn : 1 ≤ m*n := by exact Nat.mul_pos hm hn
  have hprod : (m*n - 1)+1 = m*n := Nat.sub_add_cancel hmn
  unfold reshuffleCode
  calc
    t/n + m*(t%n) + (m*n - 1)*(t/n) =
        ((m*n - 1)+1)*(t/n)+m*(t%n) := by ring
    _ = (m*n)*(t/n)+m*(t%n) := by rw [hprod]
    _ = m*((t%n)+n*(t/n)) := by ring
    _ = m*t := by rw [Nat.mod_add_div]

/-- The universal modular shadow of the information transformation.
The modulus is mn-1, not a spatial coordinate or physical distance. -/
theorem reshuffle_modulus (m n t : Nat)
    (hm : 0 < m) (hn : 0 < n) :
    reshuffleCode m n t % (m*n - 1) =
      (m*t) % (m*n - 1) := by
  have h := reshuffle_mass_balance m n t hm hn
  calc
    reshuffleCode m n t % (m*n - 1) =
        (reshuffleCode m n t + (m*n - 1)*(t/n)) % (m*n - 1) := by
          simp [Nat.add_mod, Nat.mul_mod]
    _ = (m*t) % (m*n - 1) := by rw [h]

/-- The original x4/base3 GST graph is multiplication by four modulo 11
at the level of the rearranged information code. -/
theorem original_four_three_mod_eleven (t : Nat) :
    reshuffleCode 4 3 t % 11 = (4*t) % 11 := by
  simpa using reshuffle_modulus 4 3 t (by decide) (by decide)

/-- The precise arithmetic explanation of the observed five-step
information law: 4^5 is one modulo 11. -/
theorem four_fifth_power_mod_eleven : (4^5 : Nat) % 11 = 1 := by
  norm_num

/-- Every information residue is unchanged after multiplication by
4^5. This is a purely arithmetic statement at arbitrary code size. -/
theorem four_five_preserves_every_residue (t : Nat) :
    ((4^5 : Nat)*t) % 11 = t % 11 := by
  rw [Nat.mul_mod, four_fifth_power_mod_eleven]
  simp

#check reshuffle_mass_balance
#check reshuffle_modulus
#check original_four_three_mod_eleven
#check four_five_preserves_every_residue
#print axioms reshuffle_modulus

end GSTGraphV2GeneralRadixConservation
