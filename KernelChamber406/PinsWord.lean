import KernelChamber406.PinsSpine

-- KernelChamber406 split (S089k, the split-of-the-split): olean-cached part
-- of the monolith kernel Pins 2a/5: the cMod machinery, THE UNIT WORD W61,
-- the three fixed points + all kernel-decided receipts (§6 receipts half).
-- Pure module surgery: every declaration byte-identical to the monolith
-- (PiCollapse406Pins.lean §6 up to the §6b boundary).
-- Rationale: the half-module elaboration (10-17 min) raced the hosted-runner
-- reaper strike window (11-18 min) and lost stochastically; each word/pins
-- sub-module targets <9 min.

-- Family pattern (green kernels): explicit depth headroom.
set_option profiler true
set_option maxRecDepth 262144
set_option maxHeartbeats 4000000
set_option exponentiation.threshold 1000

namespace PiCollapse406

/-! ## §6 The π-points, kernel-decided -/
#print axioms PiCollapse406.ghost_congruent_all_depths  -- CK74 SECTION BOUNDARY

/-- The certified mod-recursion: `cMod k s = lteCoeff s % 3^k`, computed
without ever forming the astronomically large tower coefficient. -/
def cMod : Nat → Nat → Nat
  | k, 0 => 1 % 3^k
  | k, s+1 =>
      let c := cMod k s
      (c + 3^(s+1) * c^2 + 3^(2*s+1) * c^3) % 3^k

/-- Congruence respects addition (hardened S083: explicit lemma
applications — the double-rw form re-matches the outer term under the
W82 Mathlib and left double-mods). -/
theorem mod_add_congr (k a b c d : Nat) (h1 : a % k = b % k)
    (h2 : c % k = d % k) : (a + c) % k = (b + d) % k := by
  calc (a + c) % k = ((a % k) + (c % k)) % k := Nat.add_mod a c k
    _ = ((b % k) + (d % k)) % k := by rw [h1, h2]
    _ = (b + d) % k := (Nat.add_mod b d k).symm

/-- Congruence respects multiplication (hardened the same way). -/
theorem mod_mul_congr (k a b c d : Nat) (h1 : a % k = b % k)
    (h2 : c % k = d % k) : (a * c) % k = (b * d) % k := by
  calc (a * c) % k = ((a % k) * (c % k)) % k := Nat.mul_mod a c k
    _ = ((b % k) * (d % k)) % k := by rw [h1, h2]
    _ = (b * d) % k := (Nat.mul_mod b d k).symm

/-- Congruence respects powers (hardened: explicit pow_succ shapes). -/
theorem mod_pow_congr (k : Nat) : ∀ (n a b : Nat), a % k = b % k →
    (a^n) % k = (b^n) % k
  | 0, a, b, _ => by simp
  | n+1, a, b, h => by
      have ih := mod_pow_congr k n a b h
      have pa : a^(n+1) = a^n * a := Nat.pow_succ a n
      have pb : b^(n+1) = b^n * b := Nat.pow_succ b n
      rw [pa, pb]
      exact mod_mul_congr k (a^n) (b^n) a b ih h

-- S089u THE IMPORT-EXPLOSION FIX (locally proven, forensics V11/V12):
-- 'simp only [cMod, lteCoeff]' on the IMPORTED recursive lteCoeff explodes
-- (300+s hang locally, the CI's 25-min 15GB burn). Single-shot helper
-- equations with shared subterms replace the simp unfold.
theorem cMod_succ (k s : Nat) : cMod k (s+1) =
    (cMod k s + 3^(s+1) * (cMod k s)^2 + 3^(2*s+1) * (cMod k s)^3) % 3^k := by
  rw [cMod]

theorem lteCoeff_succ_eq (s : Nat) : lteCoeff (s+1) =
    lteCoeff s + 3^(s+1) * (lteCoeff s)^2 + 3^(2*s+1) * (lteCoeff s)^3 := by
  rw [lteCoeff]

theorem cMod_eq (k : Nat) : ∀ s : Nat, cMod k s = lteCoeff s % 3^k
  | 0 => by
      rw [cMod, lteCoeff]
  | s+1 => by
      have ih := cMod_eq k s
      rw [cMod_succ, lteCoeff_succ_eq]
      have e2 : (3^(s+1) * (lteCoeff s)^2) % 3^k
          = (3^(s+1) * (cMod k s)^2) % 3^k := by
        have ihm : (lteCoeff s)^2 % 3^k = (cMod k s)^2 % 3^k := by
          rw [ih]
          exact mod_pow_congr (3^k) 2 _ _ (Nat.mod_mod _ _).symm
        exact mod_mul_congr (3^k) _ _ _ _ rfl ihm
      have e3 : (3^(2*s+1) * (lteCoeff s)^3) % 3^k
          = (3^(2*s+1) * (cMod k s)^3) % 3^k := by
        have ihm : (lteCoeff s)^3 % 3^k = (cMod k s)^3 % 3^k := by
          rw [ih]
          exact mod_pow_congr (3^k) 3 _ _ (Nat.mod_mod _ _).symm
        exact mod_mul_congr (3^k) _ _ _ _ rfl ihm
      have ihb : lteCoeff s % 3^k = cMod k s % 3^k :=
        (Nat.mod_mod (lteCoeff s) (3^k)).symm.trans (congrArg (fun x => x % 3^k) ih.symm)
      have eL : ((lteCoeff s + 3^(s+1) * (lteCoeff s)^2)
          + 3^(2*s+1) * (lteCoeff s)^3) % 3^k
          = ((cMod k s + 3^(s+1) * (cMod k s)^2)
          + 3^(2*s+1) * (cMod k s)^3) % 3^k :=
        mod_add_congr (3^k) _ _ _ _
          (mod_add_congr (3^k) _ _ _ _ ihb e2) e3
      calc (cMod k s + 3^(s+1) * (cMod k s)^2 + 3^(2*s+1) * (cMod k s)^3) % 3^k
          = ((cMod k s + 3^(s+1) * (cMod k s)^2)
              + 3^(2*s+1) * (cMod k s)^3) % 3^k := rfl
        _ = ((lteCoeff s + 3^(s+1) * (lteCoeff s)^2)
              + 3^(2*s+1) * (lteCoeff s)^3) % 3^k := eL.symm
        _ = (lteCoeff s + 3^(s+1) * (lteCoeff s)^2
              + 3^(2*s+1) * (lteCoeff s)^3) % 3^k := rfl

/-- **THE UNIT WORD MOD 3^61** — the stabilized tower coefficient at
depth 60, computed by the certified recursion (dual-verified against
the independent S078 Hensel lift: `W ≡ 7 (mod 9)`, `W ≡ 16 (mod 27)`). -/
def W61 : Nat := 60776643992856088575557123854

theorem W61_receipt : cMod 61 60 = W61 := by native_decide

theorem W61_mod_nine : W61 % 9 = 7 := by native_decide

theorem W61_mod_three : W61 % 3 = 1 := by native_decide

theorem W61_lt : W61 < 3^61 := by native_decide

theorem lteCoeff_sixty_mod : lteCoeff 60 % 3^61 = W61 := by
  rw [← W61_receipt]
  exact (cMod_eq 61 60).symm

theorem three_pow_61_pos : 5 ≤ 3^61 := by native_decide

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

theorem pi_fam4_lt : pi_fam4 < 3^61 := by native_decide
theorem pi_fam7_lt : pi_fam7 < 3^61 := by native_decide
theorem pi_fam1_lt : pi_fam1 < 3^61 := by native_decide

theorem pi_fam4_receipt :
    (2 * W61 * pi_fam4 + 7) % 3^61 = 0 := by native_decide

theorem pi_fam7_receipt :
    (2 * W61 * pi_fam7 + 1) % 3^61 = 0 := by native_decide

theorem pi_fam1_receipt :
    (2 * W61 * pi_fam1 + (3^61 - 5)) % 3^61 = 0 := by native_decide

/-- **THE 2-TRIT RECEIPTS** — the three fixed points are not eventually
zero: each carries ternary digit twos deep in its expansion
(kernel-decided positions from the assault engine's certified list). -/
theorem pi_fam4_trit3 : digit3 pi_fam4 3 = 2 := by native_decide
theorem pi_fam4_trit14 : digit3 pi_fam4 14 = 2 := by native_decide
theorem pi_fam7_trit1 : digit3 pi_fam7 1 = 2 := by native_decide
theorem pi_fam7_trit6 : digit3 pi_fam7 6 = 2 := by native_decide
theorem pi_fam1_trit8 : digit3 pi_fam1 8 = 2 := by native_decide
theorem pi_fam1_trit13 : digit3 pi_fam1 13 = 2 := by native_decide

#print axioms PiCollapse406.W61  -- CK74 SECTION BOUNDARY (word layer done)
end PiCollapse406
