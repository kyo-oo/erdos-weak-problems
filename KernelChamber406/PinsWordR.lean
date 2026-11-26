import KernelChamber406.PinsWord

-- S089v THE DIAGNOSTIC SPLIT: the receipts half (unit word, fixed points,
-- native_decides, prints) as its own module/build — isolates whichever
-- half carries the memory bomb against the real environment.

set_option maxRecDepth 262144
set_option maxHeartbeats 4000000
set_option exponentiation.threshold 1000

namespace PiCollapse406

/-- **THE UNIT WORD MOD 3^61** — the stabilized tower coefficient at
depth 60, computed by the certified recursion (dual-verified against
the independent S078 Hensel lift: `W ≡ 7 (mod 9)`, `W ≡ 16 (mod 27)`). -/
def W61 : Nat := 60776643992856088575557123854

theorem W61_receipt : cMod 61 60 = W61 := by decide

theorem W61_mod_nine : W61 % 9 = 7 := by decide

theorem W61_mod_three : W61 % 3 = 1 := by decide

theorem W61_lt : W61 < 3^61 := by decide

theorem lteCoeff_sixty_mod : lteCoeff 60 % 3^61 = W61 := by
  rw [← W61_receipt]
  exact (cMod_eq 61 60).symm

theorem three_pow_61_pos : 5 ≤ 3^61 := by decide

/-- The coefficient split at depth 61 (the congrArg idiom — no rw loop). -/
theorem coeff_split (u : Nat) :
    lteCoeff 60 * u
      = 3^61 * ((lteCoeff 60 / 3^61) * u) + W61 * u := by
  have hc := Nat.div_add_mod (lteCoeff 60) (3^61)
  rw [lteCoeff_sixty_mod] at hc
  calc lteCoeff 60 * u
      = (3^61 * (lteCoeff 60 / 3^61) + W61) * u := by
        conv => lhs; rw [<- hc]
    _ = 3^61 * ((lteCoeff 60 / 3^61) * u) + W61 * u := by ring

/-- **THE THREE FIXED POINTS** (the assault engine's `π₄, π₇, π₁`,
dual-verified against the independent Hensel lift of `2·W·π = T` for
`T ∈ {-7, -1, +5}` in `ℤ₃`; all three carry scattered 2-trits through
60 positions — 13, 20 and 18 respectively). -/
def pi_fam4 : Nat := 68350949682967876566738142093  -- head 1, T = -7
def pi_fam7 : Nat := 64267339165701958313626862986  -- head 4, T = -1
def pi_fam1 : Nat := 60183728648436040060515583879  -- head 7, T = +5

theorem pi_fam4_lt : pi_fam4 < 3^61 := by decide
theorem pi_fam7_lt : pi_fam7 < 3^61 := by decide
theorem pi_fam1_lt : pi_fam1 < 3^61 := by decide

theorem pi_fam4_receipt :
    (2 * W61 * pi_fam4 + 7) % 3^61 = 0 := by decide

theorem pi_fam7_receipt :
    (2 * W61 * pi_fam7 + 1) % 3^61 = 0 := by decide

theorem pi_fam1_receipt :
    (2 * W61 * pi_fam1 + (3^61 - 5)) % 3^61 = 0 := by decide

/-- **THE 2-TRIT RECEIPTS** — the three fixed points are not eventually
zero: each carries ternary digit twos deep in its expansion
(kernel-decided positions from the assault engine's certified list). -/
theorem pi_fam4_trit3 : digit3 pi_fam4 3 = 2 := by decide
theorem pi_fam4_trit14 : digit3 pi_fam4 14 = 2 := by decide
theorem pi_fam7_trit1 : digit3 pi_fam7 1 = 2 := by decide
theorem pi_fam7_trit6 : digit3 pi_fam7 6 = 2 := by decide
theorem pi_fam1_trit8 : digit3 pi_fam1 8 = 2 := by decide
theorem pi_fam1_trit13 : digit3 pi_fam1 13 = 2 := by decide

#print axioms PiCollapse406.W61  -- CK74 SECTION BOUNDARY (word layer done)
