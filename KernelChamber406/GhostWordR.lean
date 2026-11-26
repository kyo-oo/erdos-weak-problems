import KernelChamber406.GhostWord

-- S089v THE DIAGNOSTIC SPLIT (ghost side).

set_option maxRecDepth 262144
set_option maxHeartbeats 4000000
set_option exponentiation.threshold 1000

namespace GhostExtinction406

/-- **W100** — the unit word at depth 100 (dual-verified by the assault
engine: the cMod recursion ∥ the direct modular division
`4^(3^99) mod 3^200`; `% 9 = 7`, `% 3 = 1` — the three-adic unit). -/
def W100 : Nat := 79542728300108260269642213640611567864276448732

theorem W100_receipt : cMod 100 99 = W100 := by decide

theorem W100_mod_three : W100 % 3 = 1 := by decide

theorem W100_lt : W100 < 3^100 := by decide

theorem lteCoeff_99_mod : lteCoeff 99 % 3^100 = W100 := by
  rw [← W100_receipt]
  exact (cMod_eq 100 99).symm

/-- The coefficient split at depth 100 (the congrArg idiom). -/
theorem coeff_split100 (u : Nat) :
    lteCoeff 99 * u
      = 3^100 * ((lteCoeff 99 / 3^100) * u) + W100 * u := by
  have hc := Nat.div_add_mod (lteCoeff 99) (3^100)
  rw [lteCoeff_99_mod] at hc
  calc lteCoeff 99 * u
      = (3^100 * (lteCoeff 99 / 3^100) + W100) * u := by
        conv => lhs; rw [<- hc]
    _ = 3^100 * ((lteCoeff 99 / 3^100) * u) + W100 * u := by ring

/-- **THE THREE FIXED POINTS AT DEPTH 100** — the assault engine's π
family extended from 61 to 100 trits (dual-verified: pow-inverse ∥
independent Hensel lift; the 61-trit prefixes match the S080 kernel
constants byte-for-byte; all three solve the rider sheet `π % 3 = 1`,
heads 1/4/7 respectively). -/
def pi100_fam4 : Nat := 442963202118286149036278158734808096675605174274  -- head 1
def pi100_fam7 : Nat := 284156537759188591735094506861667416397418248611  -- head 4
def pi100_fam1 : Nat := 125349873400091034433910854988526736119231322948  -- head 7

theorem pi100_fam4_lt : pi100_fam4 < 3^100 := by decide
theorem pi100_fam7_lt : pi100_fam7 < 3^100 := by decide
theorem pi100_fam1_lt : pi100_fam1 < 3^100 := by decide

theorem pi100_fam4_receipt :
    (2 * W100 * pi100_fam4 + 7) % 3^100 = 0 := by decide

theorem pi100_fam7_receipt :
    (2 * W100 * pi100_fam7 + 1) % 3^100 = 0 := by decide

theorem pi100_fam1_receipt :
    (2 * W100 * pi100_fam1 + (3^100 - 5)) % 3^100 = 0 := by decide

/-- **THE DEEP 2-TRIT RECEIPTS** — the three points are not eventually
zero through depth 100: fam4 carries 18 twos in positions 61..99, fam7
13, fam1 12 (kernel-decided witnesses at the deepest positions). -/
theorem pi100_fam4_trit99 : digit3 pi100_fam4 99 = 2 := by decide
theorem pi100_fam4_trit97 : digit3 pi100_fam4 97 = 2 := by decide
theorem pi100_fam4_trit92 : digit3 pi100_fam4 92 = 2 := by decide
theorem pi100_fam7_trit97 : digit3 pi100_fam7 97 = 2 := by decide
theorem pi100_fam7_trit96 : digit3 pi100_fam7 96 = 2 := by decide
theorem pi100_fam7_trit94 : digit3 pi100_fam7 94 = 2 := by decide
theorem pi100_fam7_trit93 : digit3 pi100_fam7 93 = 2 := by decide
theorem pi100_fam1_trit98 : digit3 pi100_fam1 98 = 2 := by decide
theorem pi100_fam1_trit95 : digit3 pi100_fam1 95 = 2 := by decide
theorem pi100_fam1_trit91 : digit3 pi100_fam1 91 = 2 := by decide

#print axioms GhostExtinction406.coeff_split100  -- CK75 word layer receipt
