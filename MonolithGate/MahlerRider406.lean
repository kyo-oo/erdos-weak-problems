import Mathlib
import MonolithGate.GSTTowerFire
import MonolithGate.GSTGhostRayExclusion
import MonolithGate.GSTWorldtraceMahler
import MonolithGate.MahlerDiagonal406

/-!
# KERNEL S095 — THE RIDER-CLASS COLLAPSE (the S094 council's named engine, built)

The S094 council record named the main line for the HFTAIL kill: the
Mahler diagonal lane — `MahlerSharp` (the remaining named input of the
#406 crown chain) is, by the S093 kernel's green equivalence, the
statement that no admissible `(a, u)` rides the exact diagonal forever.
This module builds the council's named first piece — the
periodicity-obstruction engine's skeleton — and lands FOUR new
unconditional laws, every one composed from the campaign's own green
chambers (BOSS's standing order: USE MY MATHS, no classical methods,
no external inputs):

## §1 THE GLOBAL PIN (the late-entry illusion dies)

Every rider rides from depth ZERO: if `3^(s+1) ∣ D a u s` holds for all
`s ≥ S₀`, then it holds for EVERY `s` — including all `s < S₀`.  The
coherent tower (the green stabilization law `c_stable`, through the
cumulative form `c_diff_dvd`) pulls the divisibility back through the
entry depth.  A rider cannot appear late: the trajectory either rides
the whole diagonal or never rides it.

## §2 THE RIDER-CLASS COLLAPSE (at most ONE rider per head)

At every depth `s`, all same-head riders are congruent modulo
`3^(s+1)` — because `2 * c s` is invertible mod `3^(s+1)` (the green
`c_not_three`), the divisibility `3^(s+1) ∣ 2u·c s − (2a−9)` pins `u`
to a SINGLE residue class.  With §1, two riders of the same head are
pinned at EVERY depth, hence equal as natural numbers.  The admissible
heads are exactly six (`a ∈ {1,2,4,5,7,8}`), so THE ENTIRE ADMISSIBLE
RIDER UNIVERSE HAS AT MOST SIX ELEMENTS — at most one `u` per head.

## §3 THE SHARPENED SOCKET

`MahlerSharp` is EQUIVALENT to "no admissible rider, from depth zero"
— a pure ∀-divisibility statement with no `S₀`, no eventual clause,
no p-adic object: for every admissible `(a,u)` there EXISTS a depth
`s` with `3^(s+1) ∤ D a u s`.  The socket in its most elementary form.

## §4 THE SIX-FAMILY PIN (the depth-0/1/2/3 congruences)

Every admissible rider satisfies the explicit congruence ladder:
depth 0 pins `u ≡ a (mod 3)`; depth 1 (through `c 1 = 7`) pins
`u ≡ 4a (mod 9)`; depth 2 (through `c 2 = 9709 ≡ 16 mod 27`) pins
`u ≡ 11(2a−9) (mod 27)`; every depth `s ≥ 3` (through the green
`c_mod81`) pins `32u ≡ 2a−9 (mod 81)`.  Specialized to the six heads:
the entire rider universe lives in the six depth-2 classes
`u mod 27 ∈ {4, 26, 16, 11, 1, 23}` — one class per head, forever.

The remaining content of the HFTAIL problem, after this module: the
six explicit residue streams `û(a)` (one per head, computable to any
depth by §4's ladder — the accompanying two-method receipt
`rider_stream406.py` computes them to depth 40 and cross-checks them
against the independent log-series evaluation of the frozen diagonal)
must be shown NON-TERMINATING — equivalently, no admissible rider
exists.  The socket is now six explicit streams, machine-checked at
every depth.
-/

namespace MahlerRider406

open GSTTowerFire (c c_zero c_mod81)
open MahlerDiagonal406 (D trajectory_dichotomy diagonal_chain_of_lock
  mahler_sharp_iff_no_diagonal_chain c_not_three coe_not_three_dvd)

set_option maxHeartbeats 2000000
set_option maxRecDepth 500000

/-! ## §0 Integer helpers -/

/-- A factor coprime to three can be cancelled from a triple divisibility. -/
theorem three_dvd_of_not_dvd_mul (x y : ℤ) (hx : ¬ (3:ℤ) ∣ x)
    (h : (3:ℤ) ∣ x * y) : (3:ℤ) ∣ y := by
  rw [Int.dvd_iff_emod_eq_zero] at h ⊢
  rw [Int.mul_emod] at h
  have hxb : 0 ≤ x % 3 ∧ x % 3 < 3 :=
    ⟨Int.emod_nonneg _ (by norm_num), Int.emod_lt_of_pos _ (by norm_num)⟩
  have hyb : 0 ≤ y % 3 ∧ y % 3 < 3 :=
    ⟨Int.emod_nonneg _ (by norm_num), Int.emod_lt_of_pos _ (by norm_num)⟩
  rcases (by omega : x % 3 = 0 ∨ x % 3 = 1 ∨ x % 3 = 2) with hx0 | hx1 | hx2
  · exact absurd (Int.dvd_iff_emod_eq_zero.mpr hx0) hx
  · rcases (by omega : y % 3 = 0 ∨ y % 3 = 1 ∨ y % 3 = 2) with hy0 | hy1 | hy2
    · exact hy0
    · rw [hx1, hy1] at h; norm_num at h
    · rw [hx1, hy2] at h; norm_num at h
  · rcases (by omega : y % 3 = 0 ∨ y % 3 = 1 ∨ y % 3 = 2) with hy0 | hy1 | hy2
    · exact hy0
    · rw [hx2, hy1] at h; norm_num at h
    · rw [hx2, hy2] at h; norm_num at h

/-- Cancellation of a three-coprime factor from a full power:
if `3^(s+1) ∣ x·y` and `3 ∤ x`, then `3^(s+1) ∣ y`. -/
theorem pow_three_cancel_aux : ∀ (s : Nat) (x y : ℤ), ¬ (3:ℤ) ∣ x →
    (3:ℤ)^(s+1) ∣ x * y → (3:ℤ)^(s+1) ∣ y := by
  intro s
  induction s with
  | zero =>
      intro x y hx h
      rw [show (3:ℤ)^(0+1) = 3 from by norm_num] at h
      exact three_dvd_of_not_dvd_mul x y hx h
  | succ s ih =>
      intro x y hx h
      have h1 : (3:ℤ)^(s+1) ∣ x * y := (pow_dvd_pow 3 (by omega)).trans h
      have h2 : (3:ℤ)^(s+1) ∣ y := ih x y hx h1
      obtain ⟨k, hk⟩ := h
      obtain ⟨j, hj⟩ := h2
      have hpow : (3:ℤ)^((s+1)+1) = 3 * (3:ℤ)^(s+1) := by rw [pow_succ]
      rw [hpow] at hk
      have hcan : (3:ℤ)^(s+1) * (x * j) = (3:ℤ)^(s+1) * (3 * k) := by
        linear_combination hk - x * hj
      have hxj : x * j = 3 * k :=
        Int.eq_of_mul_eq_mul_left (by positivity) hcan
      have hj3 : (3:ℤ) ∣ j := three_dvd_of_not_dvd_mul x j hx ⟨k, hxj⟩
      obtain ⟨m, hm⟩ := hj3
      refine ⟨m, ?_⟩
      rw [hj, hm, hpow]
      ring

/-- The packaged form of the cancellation law. -/
theorem pow_three_cancel (s : Nat) {x y : ℤ} (hx : ¬ (3:ℤ) ∣ x)
    (h : (3:ℤ)^(s+1) ∣ x * y) : (3:ℤ)^(s+1) ∣ y :=
  pow_three_cancel_aux s x y hx h

/-- Every natural number is smaller than the next power of three. -/
theorem three_pow_succ_gt (n : Nat) : n < 3^(n+1) := by
  induction n with
  | zero => norm_num
  | succ n ih =>
      have hp : 0 < 3^(n+1) := by positivity
      rw [Nat.pow_succ]
      omega

/-- A natural number divisible by a larger natural number is zero. -/
theorem nat_eq_zero_of_dvd_of_lt {a b : Nat} (h : a ∣ b) (hlt : b < a) :
    b = 0 := by
  obtain ⟨k, hk⟩ := h
  rcases Nat.eq_zero_or_pos k with hk0 | hkpos
  · rw [hk0, Nat.mul_zero] at hk; exact hk
  · have hle : a * 1 ≤ a * k := Nat.mul_le_mul_left a hkpos
    rw [← hk] at hle
    have h1 : a * 1 = a := by ring
    rw [h1] at hle
    exact absurd hle (Nat.not_le.mpr hlt)

/-- The cast of a power of three is the power of the cast. -/
theorem int_pow_three_cast (t : Nat) : ((3^(t+1) : ℕ) : ℤ) = (3:ℤ)^(t+1) := by
  induction t with
  | zero => norm_num
  | succ t ih =>
      rw [Nat.pow_succ 3 (t+1), Nat.pow_succ (3:ℤ) (t+1)]
      push_cast
      rw [ih]

/-- An integer power of three dividing a natural cast divides the
natural number. -/
theorem int_pow_dvd_nat_cast {s n : Nat}
    (h : (3:ℤ)^(s+1) ∣ ((n : ℕ) : ℤ)) : 3^(s+1) ∣ n := by
  obtain ⟨k, hk⟩ := h
  have hp : (0:ℤ) < (3:ℤ)^(s+1) := by positivity
  have hn : (0:ℤ) ≤ ((n : ℕ) : ℤ) := by exact_mod_cast Nat.zero_le n
  have hk0 : (0:ℤ) ≤ k := by
    by_contra hc
    push_neg at hc
    have hneg : (3:ℤ)^(s+1) * k < 0 := Int.mul_neg_of_pos_of_neg hp hc
    rw [← hk] at hneg
    omega
  have hkN : k = ((k.natAbs : ℕ) : ℤ) := by
    have hna := Int.natAbs_of_nonneg hk0
    exact hna.symm
  rw [hkN] at hk
  rw [(int_pow_three_cast s).symm] at hk
  push_cast at hk
  exact ⟨k.natAbs, Int.natCast_inj.mp hk⟩

/-! ## §1 The tower's cumulative stabilization and the GLOBAL PIN -/

/-- The tower coefficient is monotone. -/
theorem c_le_succ (n : Nat) : c n ≤ c (n+1) := by
  have h := GSTTowerFire.c_succ_eq n
  have hp : 0 < 3^(n+1) * (c n * c n + 3^n * (c n * c n * c n)) := by
    positivity
  omega

/-- Monotonicity, iterated. -/
theorem c_mono (t s : Nat) (hts : t ≤ s) : c t ≤ c s := by
  induction hts with
  | refl => le_refl _
  | step s hts ih => exact le_trans ih (c_le_succ s)

/-- **THE CUMULATIVE STABILIZATION.**  For `t ≤ s`, the tower
coefficients agree modulo `3^(t+1)`, as an integer divisibility. -/
theorem c_diff_dvd (t s : Nat) (hts : t ≤ s) :
    (3:ℤ)^(t+1) ∣ ((c s : ℤ) - (c t : ℤ)) := by
  have hst := GSTGhostRayExclusion.c_stable t s hts
  have hds := Nat.div_add_mod (c s) (3^(t+1))
  have hdt := Nat.div_add_mod (c t) (3^(t+1))
  rw [hst] at hds
  refine ⟨((c s / 3^(t+1) : ℕ) : ℤ) - ((c t / 3^(t+1) : ℕ) : ℤ), ?_⟩
  have hds' : (c s : ℤ) = ((3^(t+1) : ℕ) : ℤ) * ((c s / 3^(t+1) : ℕ) : ℤ)
      + ((c t % 3^(t+1) : ℕ) : ℤ) := by
    exact_mod_cast hds
  have hdt' : (c t : ℤ) = ((3^(t+1) : ℕ) : ℤ) * ((c t / 3^(t+1) : ℕ) : ℤ)
      + ((c t % 3^(t+1) : ℕ) : ℤ) := by
    exact_mod_cast hdt
  rw [int_pow_three_cast t] at hds' hdt'
  linear_combination hds' - hdt'

/-- The rider, in its eventual form: the cofactor divisibility holds
at every depth. -/
def RiderGE (a u : Nat) : Prop :=
  ∀ s : Nat, (3:ℤ)^(s+1) ∣ D a u s

/-- **THE GLOBAL PIN.**  Every rider rides from depth zero: eventual
divisibility of the cofactor is divisibility at EVERY depth.  The
coherent tower pulls the lock back through the entry depth — a rider
cannot appear late. -/
theorem rider_global_pin (a u : Nat)
    (hS : ∃ S₀ : Nat, ∀ s : Nat, S₀ ≤ s → (3:ℤ)^(s+1) ∣ D a u s) :
    RiderGE a u := by
  intro t
  obtain ⟨S₀, hS₀⟩ := hS
  have hgeS : S₀ ≤ max S₀ t := le_max_left _ _
  have hget : t ≤ max S₀ t := le_max_right _ _
  have hDs : (3:ℤ)^((max S₀ t)+1) ∣ D a u (max S₀ t) := hS₀ _ hgeS
  have hcd : (3:ℤ)^(t+1) ∣ ((c (max S₀ t) : ℤ) - (c t : ℤ)) :=
    c_diff_dvd t (max S₀ t) hget
  have hDt_eq : D a u t
      = D a u (max S₀ t)
        - 2 * (u:ℤ) * ((c (max S₀ t) : ℤ) - (c t : ℤ)) := by
    unfold D
    ring
  have hmul : (3:ℤ)^(t+1)
      ∣ 2 * (u:ℤ) * ((c (max S₀ t) : ℤ) - (c t : ℤ)) :=
    hcd.mul_left _
  have hDs' : (3:ℤ)^(t+1) ∣ D a u (max S₀ t) :=
    (pow_dvd_pow 3 (by omega)).trans hDs
  rw [hDt_eq]
  exact hDs'.sub hmul

/-! ## §2 The rider-class collapse -/

/-- The factor `2 * c s` is coprime to three. -/
theorem two_mul_c_not_dvd_three (s : Nat) :
    ¬ (3:ℤ) ∣ (2 * (c s : ℤ)) := by
  intro h
  rw [Int.dvd_iff_emod_eq_zero, Int.mul_emod] at h
  norm_num at h
  rcases mul_eq_zero.mp h with h2 | hX
  · norm_num at h2
  · exact coe_not_three_dvd (c_not_three s) hX

/-- **THE CLASS COLLAPSE.**  At every depth `s`, all same-head riders
are congruent modulo `3^(s+1)`: the cofactor divisibility pins `u` to a
single residue class per depth. -/
theorem rider_class_unique (a u₁ u₂ s : Nat)
    (h1 : (3:ℤ)^(s+1) ∣ D a u₁ s) (h2 : (3:ℤ)^(s+1) ∣ D a u₂ s) :
    (3:ℤ)^(s+1) ∣ ((u₁:ℤ) - (u₂:ℤ)) := by
  have hdiff : (3:ℤ)^(s+1) ∣ D a u₁ s - D a u₂ s := h1.sub h2
  have hEq : D a u₁ s - D a u₂ s
      = (2 * (c s : ℤ)) * ((u₁:ℤ) - (u₂:ℤ)) := by
    unfold D
    ring
  rw [hEq] at hdiff
  exact pow_three_cancel s (two_mul_c_not_dvd_three s) hdiff

/-- **AT MOST ONE RIDER PER HEAD.**  Two riders of the same head are
pinned at every depth, hence equal. -/
theorem rider_eq_of_same_head (a u₁ u₂ : Nat)
    (h1 : RiderGE a u₁) (h2 : RiderGE a u₂) : u₁ = u₂ := by
  by_cases hle : u₂ ≤ u₁
  · have hcoesub : ((u₁ - u₂ : ℕ) : ℤ) = (u₁:ℤ) - (u₂:ℤ) := by
      push_cast
      omega
    have hd : (3:ℤ)^((u₁ - u₂)+1) ∣ ((u₁ - u₂ : ℕ) : ℤ) := by
      rw [hcoesub]
      exact rider_class_unique a u₁ u₂ (u₁ - u₂) (h1 _) (h2 _)
    have hnat : 3^((u₁ - u₂)+1) ∣ (u₁ - u₂) := int_pow_dvd_nat_cast hd
    have hlt : (u₁ - u₂) < 3^((u₁ - u₂)+1) := three_pow_succ_gt _
    have hz : u₁ - u₂ = 0 := nat_eq_zero_of_dvd_of_lt hnat hlt
    omega
  · have hcoesub : ((u₂ - u₁ : ℕ) : ℤ) = (u₂:ℤ) - (u₁:ℤ) := by
      push_cast
      omega
    have hd : (3:ℤ)^((u₂ - u₁)+1) ∣ ((u₂ - u₁ : ℕ) : ℤ) := by
      rw [hcoesub]
      exact rider_class_unique a u₂ u₁ (u₂ - u₁) (h2 _) (h1 _)
    have hnat : 3^((u₂ - u₁)+1) ∣ (u₂ - u₁) := int_pow_dvd_nat_cast hd
    have hlt : (u₂ - u₁) < 3^((u₂ - u₁)+1) := three_pow_succ_gt _
    have hz : u₂ - u₁ = 0 := nat_eq_zero_of_dvd_of_lt hnat hlt
    omega

/-! ## §3 The sharpened socket -/

/-- Every rider's trajectory is the exact diagonal (the frozen branch
contradicts the rider's all-depths divisibility). -/
theorem chain_of_riderGE (a u : Nat) (hu : ¬ 3 ∣ u) (h : RiderGE a u) :
    ∃ S₀ : Nat, ∀ s : Nat, S₀ ≤ s →
      ((3:ℤ)^(s+1) ∣ D a u s ∧ ¬ (3:ℤ)^(s+2) ∣ D a u s) := by
  rcases trajectory_dichotomy a u hu with hchain | hfroz
  · exact hchain
  · exfalso
    obtain ⟨S₀, t, hf⟩ := hfroz
    have hmS : S₀ ≤ max S₀ t := le_max_left _ _
    have hmt : t ≤ max S₀ t := le_max_right _ _
    have hGE : (3:ℤ)^((max S₀ t)+1) ∣ D a u (max S₀ t) :=
      h (max S₀ t) hmS
    have hF : ¬ (3:ℤ)^(t+1) ∣ D a u (max S₀ t) :=
      (hf (max S₀ t) hmS).2
    exact hF ((pow_dvd_pow 3 (by omega)).trans hGE)

/-- **THE SHARPENED SOCKET.**  `MahlerSharp` — the one remaining named
input of the #406 crown chain — is EQUIVALENT to: no admissible pair
`(a, u)` satisfies the cofactor divisibility at every depth.  No `S₀`,
no eventual clause: for every admissible pair there EXISTS a depth
where the divisibility fails. -/
theorem mahler_sharp_iff_no_rider :
    GSTWorldtraceMahler.MahlerSharp ↔
      (∀ (a u : Nat), a < 9 → ¬ 3 ∣ a → ¬ 3 ∣ u → ¬ RiderGE a u) := by
  constructor
  · intro H a u ha hA hu hR
    obtain ⟨S₀, hS₀⟩ := chain_of_riderGE a u hu hR
    exact (mahler_sharp_iff_no_diagonal_chain.mp H) a u ha hA hu ⟨S₀, hS₀⟩
  · intro H
    intro hK
    obtain ⟨a, u, hadm, hu, hlock⟩ := hK
    obtain ⟨S₀, hS₀⟩ := diagonal_chain_of_lock a u hu hlock
    have hR : RiderGE a u :=
      rider_global_pin a u ⟨S₀, fun s hs => (hS₀ s hs).1⟩
    exact H a u hadm.1 hadm.2 hu hR

/-- The admissible heads are exactly the six. -/
theorem six_head_iff (a : Nat) : (a < 9 ∧ ¬ 3 ∣ a) ↔
    (a = 1 ∨ a = 2 ∨ a = 4 ∨ a = 5 ∨ a = 7 ∨ a = 8) := by
  constructor
  · intro ⟨h1, h2⟩
    have ha3 : a % 3 ≠ 0 := fun hc => h2 (Nat.dvd_iff_mod_eq_zero.mpr hc)
    omega
  · intro h
    rcases h with rfl | rfl | rfl | rfl | rfl | rfl <;>
      exact ⟨by norm_num, by decide⟩

/-- **THE SOCKET, SIX-FAMILY FORM.**  `MahlerSharp` is equivalent to:
no rider at any of the six heads `{1, 2, 4, 5, 7, 8}`. -/
theorem mahler_sharp_iff_no_six_family_rider :
    GSTWorldtraceMahler.MahlerSharp ↔
      (∀ (a u : Nat), (a = 1 ∨ a = 2 ∨ a = 4 ∨ a = 5 ∨ a = 7 ∨ a = 8) →
        ¬ 3 ∣ u → ¬ RiderGE a u) := by
  rw [mahler_sharp_iff_no_rider]
  constructor
  · intro H a u ha hu
    exact H a u (six_head_iff a |>.mpr ha).1 (six_head_iff a |>.mpr ha).2 hu
  · intro H a u ha1 ha2 hu
    exact H a u (six_head_iff a |>.mp ⟨ha1, ha2⟩) hu

/-! ## §4 The depth pins — the six-family congruence ladder -/

theorem c_one : c 1 = 7 := by decide

theorem c_two : c 2 = 9709 := by decide

/-- **DEPTH 0.**  A rider satisfies `u ≡ a (mod 3)`. -/
theorem rider_depth_zero (a u : Nat) (h : RiderGE a u) :
    (3:ℤ) ∣ ((u:ℤ) - (a:ℤ)) := by
  have hD : (3:ℤ)^(0+1) ∣ D a u 0 := h 0
  rw [show (3:ℤ)^(0+1) = 3 from by norm_num] at hD
  have hDeq : D a u 0 = 2 * ((u:ℤ) - (a:ℤ)) + 9 := by
    unfold D
    rw [c_zero]
    push_cast
    ring
  obtain ⟨k, hk⟩ := hD
  rw [hDeq] at hk
  have h2 : (3:ℤ) ∣ 2 * ((u:ℤ) - (a:ℤ)) := ⟨k - 3, by linear_combination hk⟩
  exact three_dvd_of_not_dvd_mul 2 _ (by norm_num) h2

/-- **DEPTH 1.**  A rider satisfies `u ≡ 4a (mod 9)`. -/
theorem rider_depth_one (a u : Nat) (h : RiderGE a u) :
    (9:ℤ) ∣ ((u:ℤ) - 4 * (a:ℤ)) := by
  have hD : (3:ℤ)^(1+1) ∣ D a u 1 := h 1
  rw [show (3:ℤ)^(1+1) = 9 from by norm_num] at hD
  have hDeq : D a u 1 = 14 * (u:ℤ) - 2 * (a:ℤ) + 9 := by
    unfold D
    rw [c_one]
    push_cast
    ring
  obtain ⟨k, hk⟩ := hD
  rw [hDeq] at hk
  refine ⟨2 * k - (3 * (u:ℤ) + 2), ?_⟩
  rw [show ((u:ℤ) - 4 * (a:ℤ))
      = 2 * (14 * (u:ℤ) - 2 * (a:ℤ) + 9) - 9 * (3 * (u:ℤ) + 2) from by
      ring]
  linear_combination 2 * hk

/-- **DEPTH 2.**  A rider satisfies `u ≡ 11(2a−9) (mod 27)`. -/
theorem rider_depth_two (a u : Nat) (h : RiderGE a u) :
    (27:ℤ) ∣ ((u:ℤ) - 11 * (2 * (a:ℤ) - 9)) := by
  have hD : (3:ℤ)^(2+1) ∣ D a u 2 := h 2
  rw [show (3:ℤ)^(2+1) = 27 from by norm_num] at hD
  have hDeq : D a u 2 = 2 * 9709 * (u:ℤ) - 2 * (a:ℤ) + 9 := by
    unfold D
    rw [c_two]
    push_cast
    ring
  obtain ⟨k, hk⟩ := hD
  rw [hDeq] at hk
  refine ⟨11 * k - 7911 * (u:ℤ), ?_⟩
  rw [show ((u:ℤ) - 11 * (2 * (a:ℤ) - 9))
      = 11 * (2 * 9709 * (u:ℤ) - 2 * (a:ℤ) + 9) - 27 * 7911 * (u:ℤ) from by
      ring]
  linear_combination 11 * hk

/-- The tower coefficient's fourth-power congruence, as divisibility. -/
theorem c_int_mod81 (s : Nat) (hs : 3 ≤ s) :
    (3:ℤ)^(3+1) ∣ ((c s : ℤ) - 16) := by
  have hc := c_mod81 s hs
  have hdm := Nat.div_add_mod (c s) 81
  rw [hc] at hdm
  refine ⟨((c s / 81 : ℕ) : ℤ), ?_⟩
  have hcast : ((81 : ℕ) : ℤ) = (3:ℤ)^(3+1) := by norm_num
  have hdm' : (c s : ℤ) = ((81 : ℕ) : ℤ) * ((c s / 81 : ℕ) : ℤ) + 16 := by
    exact_mod_cast hdm
  rw [hcast] at hdm'
  linear_combination hdm'

/-- **DEPTH 3 AND BEYOND.**  At every depth `s ≥ 3`, a rider satisfies
`32u ≡ 2a−9 (mod 81)` — the modulus-81 pin, uniform in `s`, through
the green `c_mod81` law. -/
theorem rider_c_mod81_pin (a u s : Nat) (hs : 3 ≤ s) (h : RiderGE a u) :
    (3:ℤ)^(3+1) ∣ (32 * (u:ℤ) - (2 * (a:ℤ) - 9)) := by
  have hD : (3:ℤ)^(s+1) ∣ D a u s := h s
  have h4 : (3:ℤ)^4 ∣ (3:ℤ)^(s+1) := pow_dvd_pow 3 (by omega)
  have hD4 : (3:ℤ)^4 ∣ D a u s := h4.trans hD
  rw [show (3:ℤ)^4 = (3:ℤ)^(3+1) from by norm_num] at hD4
  obtain ⟨k, hk⟩ := hD4
  have hcs := c_int_mod81 s hs
  obtain ⟨w, hw⟩ := hcs
  refine ⟨k - 2 * (u:ℤ) * w, ?_⟩
  have hId : (32:ℤ) * (u:ℤ) - (2 * (a:ℤ) - 9)
      = D a u s - 2 * (u:ℤ) * ((c s : ℤ) - 16) := by
    unfold D
    ring
  rw [hId, hk, hw]
  ring

/-- **THE SIX-FAMILY PIN.**  The entire admissible rider universe lives
in six explicit depth-2 classes — one class per head, forever:
`u mod 27 ∈ {4, 26, 16, 11, 1, 23}` for heads `{1,2,4,5,7,8}`. -/
theorem rider_six_family_pin (a u : Nat) (ha : a < 9) (hA : ¬ 3 ∣ a)
    (h : RiderGE a u) :
    (a = 1 ∧ (27:ℤ) ∣ ((u:ℤ) - 4)) ∨ (a = 2 ∧ (27:ℤ) ∣ ((u:ℤ) - 26)) ∨
    (a = 4 ∧ (27:ℤ) ∣ ((u:ℤ) - 16)) ∨ (a = 5 ∧ (27:ℤ) ∣ ((u:ℤ) - 11)) ∨
    (a = 7 ∧ (27:ℤ) ∣ ((u:ℤ) - 1)) ∨ (a = 8 ∧ (27:ℤ) ∣ ((u:ℤ) - 23)) := by
  have hd2 := rider_depth_two a u h
  rcases (six_head_iff a |>.mp ⟨ha, hA⟩) with rfl | rfl | rfl | rfl | rfl | rfl
  · refine Or.inl ⟨rfl, ?_⟩
    have heq : ((u:ℤ) - 11 * (2 * ((1:Nat):ℤ) - 9)) = ((u:ℤ) + 77) := by
      norm_num
    rw [heq] at hd2
    have h81 : (27:ℤ) ∣ (81:ℤ) := ⟨3, by norm_num⟩
    rw [show ((u:ℤ) - 4) = ((u:ℤ) + 77) - 81 from by ring]
    exact hd2.sub h81
  · refine Or.inr (Or.inl ⟨rfl, ?_⟩)
    have heq : ((u:ℤ) - 11 * (2 * ((2:Nat):ℤ) - 9)) = ((u:ℤ) + 55) := by
      norm_num
    rw [heq] at hd2
    have h81 : (27:ℤ) ∣ (81:ℤ) := ⟨3, by norm_num⟩
    rw [show ((u:ℤ) - 26) = ((u:ℤ) + 55) - 81 from by ring]
    exact hd2.sub h81
  · refine Or.inr (Or.inr (Or.inl ⟨rfl, ?_⟩))
    have heq : ((u:ℤ) - 11 * (2 * ((4:Nat):ℤ) - 9)) = ((u:ℤ) + 11) := by
      norm_num
    rw [heq] at hd2
    have h27 : (27:ℤ) ∣ (27:ℤ) := ⟨1, by norm_num⟩
    rw [show ((u:ℤ) - 16) = ((u:ℤ) + 11) - 27 from by ring]
    exact hd2.sub h27
  · refine Or.inr (Or.inr (Or.inr (Or.inl ⟨rfl, ?_⟩)))
    have heq : ((u:ℤ) - 11 * (2 * ((5:Nat):ℤ) - 9)) = ((u:ℤ) - 11) := by
      norm_num
    rw [heq] at hd2
    exact hd2
  · refine Or.inr (Or.inr (Or.inr (Or.inr (Or.inl ⟨rfl, ?_⟩))))
    have heq : ((u:ℤ) - 11 * (2 * ((7:Nat):ℤ) - 9)) = ((u:ℤ) - 55) := by
      norm_num
    rw [heq] at hd2
    have h54 : (27:ℤ) ∣ (54:ℤ) := ⟨2, by norm_num⟩
    rw [show ((u:ℤ) - 1) = ((u:ℤ) - 55) + 54 from by ring]
    exact hd2.add h54
  · refine Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl ⟨rfl, ?_⟩)))))
    have heq : ((u:ℤ) - 11 * (2 * ((8:Nat):ℤ) - 9)) = ((u:ℤ) - 77) := by
      norm_num
    rw [heq] at hd2
    have h54 : (27:ℤ) ∣ (54:ℤ) := ⟨2, by norm_num⟩
    rw [show ((u:ℤ) - 23) = ((u:ℤ) - 77) + 54 from by ring]
    exact hd2.add h54

/-- **THE HEAD-UNIQUENESS RECEIPT.**  Any two admissible riders with
the same head are the same rider — with `six_head_iff` and
`rider_six_family_pin`, the entire admissible rider universe has AT
MOST SIX ELEMENTS (at most one `u` per head, one head family each). -/
theorem rider_universe_at_most_six (a u₁ u₂ : Nat)
    (h₁ : a < 9 ∧ ¬ 3 ∣ a ∧ ¬ 3 ∣ u₁ ∧ RiderGE a u₁)
    (h₂ : a < 9 ∧ ¬ 3 ∣ a ∧ ¬ 3 ∣ u₂ ∧ RiderGE a u₂) : u₁ = u₂ :=
  rider_eq_of_same_head a u₁ u₂ h₁.2.2.1 h₂.2.2.1

/-! ## Receipts -/

#print axioms three_dvd_of_not_dvd_mul
#print axioms pow_three_cancel_aux
#print axioms pow_three_cancel
#print axioms three_pow_succ_gt
#print axioms nat_eq_zero_of_dvd_of_lt
#print axioms int_pow_three_cast
#print axioms int_pow_dvd_nat_cast
#print axioms c_le_succ
#print axioms c_mono
#print axioms c_diff_dvd
#print axioms rider_global_pin
#print axioms two_mul_c_not_dvd_three
#print axioms rider_class_unique
#print axioms rider_eq_of_same_head
#print axioms chain_of_riderGE
#print axioms mahler_sharp_iff_no_rider
#print axioms six_head_iff
#print axioms mahler_sharp_iff_no_six_family_rider
#print axioms c_one
#print axioms c_two
#print axioms rider_depth_zero
#print axioms rider_depth_one
#print axioms rider_depth_two
#print axioms c_int_mod81
#print axioms rider_c_mod81_pin
#print axioms rider_six_family_pin
#print axioms rider_universe_at_most_six

end MahlerRider406

#eval "ERDOS406_MAHLER_RIDER_GREEN"
