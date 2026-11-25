import KernelChamber406.GhostSpine

-- KernelChamber406 split (S089k, the split-of-the-split): olean-cached part
-- of the monolith kernel Ghost 2a/5: the cMod machinery, THE UNIT WORD W100,
-- the three depth-100 fixed points + all kernel-decided receipts.
-- Pure module surgery: every declaration byte-identical to the monolith
-- (GhostExtinction406.lean §6 up to the pin-engine boundary).
-- Rationale: the half-module elaboration (10-17 min) raced the hosted-runner
-- reaper strike window (11-18 min) and lost stochastically; each word/pins
-- sub-module targets <9 min.

-- Family pattern (green kernels): explicit depth headroom.
set_option maxRecDepth 262144
set_option maxHeartbeats 4000000
set_option exponentiation.threshold 1000

namespace GhostExtinction406

/-! ## §6 The depth-100 pins — the three π-points, kernel-decided -/
#print axioms GhostExtinction406.ghost_uniqueness  -- CK75 SECTION BOUNDARY

/-- The certified mod-recursion: `cMod k s = lteCoeff s % 3^k`, computed
without ever forming the astronomically large tower coefficient. -/
def cMod : Nat → Nat → Nat
  | k, 0 => 1 % 3^k
  | k, s+1 =>
      let c := cMod k s
      (c + 3^(s+1) * c^2 + 3^(2*s+1) * c^3) % 3^k

/-- Congruence respects addition (hardened: explicit lemma applications —
the double-rw form re-matches the outer term under the W82 Mathlib). -/
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
      have pa : a^(n+1) = a * a^n := Nat.pow_succ a n
      have pb : b^(n+1) = b * b^n := Nat.pow_succ b n
      rw [pa, pb]
      exact mod_mul_congr k (a * a^n) (b * b^n) a b ih h

theorem cMod_eq (k : Nat) : ∀ s : Nat, cMod k s = lteCoeff s % 3^k
  | 0 => by
      simp only [cMod, lteCoeff]
  | s+1 => by
      have ih := cMod_eq k s
      simp only [cMod, lteCoeff]
      have e2 : (3^(s+1) * (lteCoeff s)^2) % 3^k
          = (3^(s+1) * (cMod k s)^2) % 3^k :=
        mod_mul_congr k _ _ _ _ rfl (mod_pow_congr k 2 _ _ ih)
      have e3 : (3^(2*s+1) * (lteCoeff s)^3) % 3^k
          = (3^(2*s+1) * (cMod k s)^3) % 3^k :=
        mod_mul_congr k _ _ _ _ rfl (mod_pow_congr k 3 _ _ ih)
      have eL : ((lteCoeff s + 3^(s+1) * (lteCoeff s)^2)
          + 3^(2*s+1) * (lteCoeff s)^3) % 3^k
          = ((cMod k s + 3^(s+1) * (cMod k s)^2)
          + 3^(2*s+1) * (cMod k s)^3) % 3^k :=
        mod_add_congr k _ _ _ _
          (mod_add_congr k _ _ _ _ rfl e2) e3
      rw [eL, ← ih]

/-- **W100** — the unit word at depth 100 (dual-verified by the assault
engine: the cMod recursion ∥ the direct modular division
`4^(3^99) mod 3^200`; `% 9 = 7`, `% 3 = 1` — the three-adic unit). -/
def W100 : Nat := 79542728300108260269642213640611567864276448732

theorem W100_receipt : cMod 100 99 = W100 := by native_decide

theorem W100_mod_three : W100 % 3 = 1 := by native_decide

theorem W100_lt : W100 < 3^100 := by native_decide

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
        conv_lhs => rw [hc]
    _ = 3^100 * ((lteCoeff 99 / 3^100) * u) + W100 * u := by ring

/-- **THE THREE FIXED POINTS AT DEPTH 100** — the assault engine's π
family extended from 61 to 100 trits (dual-verified: pow-inverse ∥
independent Hensel lift; the 61-trit prefixes match the S080 kernel
constants byte-for-byte; all three solve the rider sheet `π % 3 = 1`,
heads 1/4/7 respectively). -/
def pi100_fam4 : Nat := 442963202118286149036278158734808096675605174274  -- head 1
def pi100_fam7 : Nat := 284156537759188591735094506861667416397418248611  -- head 4
def pi100_fam1 : Nat := 125349873400091034433910854988526736119231322948  -- head 7

theorem pi100_fam4_lt : pi100_fam4 < 3^100 := by native_decide
theorem pi100_fam7_lt : pi100_fam7 < 3^100 := by native_decide
theorem pi100_fam1_lt : pi100_fam1 < 3^100 := by native_decide

theorem pi100_fam4_receipt :
    (2 * W100 * pi100_fam4 + 7) % 3^100 = 0 := by native_decide

theorem pi100_fam7_receipt :
    (2 * W100 * pi100_fam7 + 1) % 3^100 = 0 := by native_decide

theorem pi100_fam1_receipt :
    (2 * W100 * pi100_fam1 + (3^100 - 5)) % 3^100 = 0 := by native_decide

/-- **THE DEEP 2-TRIT RECEIPTS** — the three points are not eventually
zero through depth 100: fam4 carries 18 twos in positions 61..99, fam7
13, fam1 12 (kernel-decided witnesses at the deepest positions). -/
theorem pi100_fam4_trit99 : digit3 pi100_fam4 99 = 2 := by native_decide
theorem pi100_fam4_trit97 : digit3 pi100_fam4 97 = 2 := by native_decide
theorem pi100_fam4_trit92 : digit3 pi100_fam4 92 = 2 := by native_decide
theorem pi100_fam7_trit97 : digit3 pi100_fam7 97 = 2 := by native_decide
theorem pi100_fam7_trit96 : digit3 pi100_fam7 96 = 2 := by native_decide
theorem pi100_fam7_trit94 : digit3 pi100_fam7 94 = 2 := by native_decide
theorem pi100_fam7_trit93 : digit3 pi100_fam7 93 = 2 := by native_decide
theorem pi100_fam1_trit98 : digit3 pi100_fam1 98 = 2 := by native_decide
theorem pi100_fam1_trit95 : digit3 pi100_fam1 95 = 2 := by native_decide
theorem pi100_fam1_trit91 : digit3 pi100_fam1 91 = 2 := by native_decide

#print axioms GhostExtinction406.coeff_split100  -- CK75 word layer receipt
end GhostExtinction406
