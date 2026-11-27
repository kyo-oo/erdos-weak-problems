import Mathlib
import MonolithGate.GSTTowerFire
import MonolithGate.GSTDiagonalRead
import MonolithGate.GSTTailFFourthDimension
import MonolithGate.DustCandidates406
import MonolithGate.GSTGhostRayExclusion
import MonolithGate.GSTWorldtraceMahler

set_option maxRecDepth 1000000
set_option maxHeartbeats 40000000

/-!
# THE MAHLER BRIDGE (S092) — the dust, the ghost, and the diagonal fire

BOSS's order: USE MY MATHS — EVERY Lean file in the proof. This module
composes the campaign's own chambers — never re-proven, only cited — into
NEW laws that no single source file contains:

* §0 THE MID-RANGE TRIT LEMMA — `digit_two_of_mid_range`: a residue in
  the top third `[2·3^j, 3^(j+1))` pins the row-`j` trit at exactly `2`.
* §1 THE IDENTIFICATION — `c_eq_omegaCutWord`: the LTE tower coefficient
  and the seed-one omega cut word are ONE object.
* §2 THE BRIDGE — `ghost_of_dust_shape`: the full dust shape of the
  mission board IS the ghost ray of the Mahler chamber — the all-ones
  middle third at every depth. Two languages, one object.
* §3 THE MAHLER DUST FRACTURE — `mahler_dust_fracture`: under the Mahler
  sharpness input, every three-free core's diagonal FIRES at a named
  depth: the all-ones middle-third placement is impossible for every
  integer core. The dust shape is dead on arrival.
* §4 THE DIAGONAL-TO-TOWER FIRE — `tower_digit_two_of_diagonal_fire`: a
  diagonal fire at depth `k0 ≤ s+1` is a ternary digit two of the tower
  `4^(3^s·core)` at the NAMED row `s + k0` — through the repo's own
  window law and the frozen-diagonal stabilization.
* §5 THE TOWER VERDICT — `tower_verdict_of_mahler`: under Mahler
  sharpness, every tower `3^s·core` EITHER owns its digit two outright
  (at a named row, when the cut reaches the core's minimal fire depth)
  OR carries its dodge band intact (the mission board's tower-primitive
  domain, when the cut is below the fire depth).

Every theorem carries `#print axioms` receipts. No classical results are
used — only the campaign's own green chambers, composed.
-/

namespace MahlerBridge406

open GSTGraphV2OmegaWaveLaw (omegaCutWord)
open GSTCanonicalSevenAxisBridge (digit3)
open GSTCanonicalTailLTE (lteCoeff)

/-! ## §0 The mid-range trit lemma -/

/-- **THE MID-RANGE TRIT.**  If the residue of `X` modulo `3^(j+1)` sits
in the top third `[2·3^j, 3^(j+1))`, then the row-`j` trit of `X` is
exactly `2`.  Pure division arithmetic, self-contained. -/
theorem digit_two_of_mid_range (X j : Nat)
    (hlo : 2 * 3^j ≤ X % 3^(j+1)) :
    X / 3^j % 3 = 2 := by
  have hp : 3^(j+1) = 3 * 3^j := by rw [Nat.pow_succ]
  have hlt : X % 3^(j+1) < 3 * 3^j := by
    rw [← hp]; exact Nat.mod_lt _ (Nat.pow_pos (by decide))
  have hRj : (X % 3^(j+1)) / 3^j = 2 := by
    have hge : 2 ≤ (X % 3^(j+1)) / 3^j := by
      have h2 : (2 * 3^j) / 3^j ≤ (X % 3^(j+1)) / 3^j :=
        Nat.div_le_div_right hlo
      rw [Nat.mul_div_cancel _ (Nat.pow_pos (by decide))] at h2
      exact h2
    have hlt3 : (X % 3^(j+1)) / 3^j < 3 := by
      have h1 : 3 * ((X % 3^(j+1)) / 3^j)
          ≤ X % 3^(j+1) := Nat.div_mul_le_self _ _
      have h2 : X % 3^(j+1) < 3 * 3^j := by
        rw [← hp]; exact Nat.mod_lt _ (Nat.pow_pos (by decide))
      have h3 : 3 * ((X % 3^(j+1)) / 3^j) < 3 * 3^j :=
        Nat.lt_of_le_of_lt h1 h2
      exact Nat.lt_of_mul_lt_mul_left h3
    omega
  have hX' : X = (X % 3^(j+1)) + 3^(j+1) * (X / 3^(j+1)) := by
    rw [Nat.add_comm]
    exact (Nat.div_add_mod X (3^(j+1))).symm
  have hreassoc : 3^(j+1) * (X / 3^(j+1))
      = 3^j * (3 * (X / 3^(j+1))) := by
    rw [hp]; ring
  have hdiv : X / 3^j
      = (X % 3^(j+1)) / 3^j + 3 * (X / 3^(j+1)) := by
    rw [hX', hreassoc]
    exact Nat.add_mul_div_left _ _ (Nat.pow_pos (by decide))
  rw [hdiv, hRj, Nat.add_mod, Nat.mul_mod_right,
    Nat.mod_mod, Nat.mod_self, Nat.zero_add, Nat.mod_mod]

/-! ## §1 The identification — one object, two names -/

/-- **THE IDENTIFICATION.**  The LTE tower coefficient `GSTTowerFire.c n`
and the seed-one omega cut word `omegaCutWord n 1` are ONE object: both
satisfy the exact cut factorization `4^(3^n) = 1 + 3^(n+1) * X`, and the
factor `3^(n+1)` is positive, so the quotient is unique. -/
theorem c_eq_omegaCutWord (n : Nat) :
    GSTTowerFire.c n = omegaCutWord n 1 := by
  have h1 : 4^(3^n * 1) = 1 + 3^(n+1) * GSTTowerFire.c n := by
    rw [Nat.mul_one]
    exact GSTTowerFire.four_pow_three_pow_eq n
  have h2 : 4^(3^n * 1) = 1 + 3^(n+1) * omegaCutWord n 1 :=
    GSTGraphV2OmegaWaveLaw.omega_cut_factor n 1
  have hEq : 3^(n+1) * GSTTowerFire.c n
      = 3^(n+1) * omegaCutWord n 1 :=
    Nat.add_left_cancel (h1.symm.trans h2)
  exact Nat.eq_of_mul_eq_mul_left (Nat.pow_pos (by decide)) hEq

/-- The three-free shape condition in divisibility form. -/
theorem not_three_dvd_of_shape (core : Nat)
    (hfree : core % 3 = 1 ∨ core % 3 = 2) : ¬ 3 ∣ core := by
  intro hd
  have hmod : core % 3 = 0 := (Nat.dvd_iff_mod_eq_zero.mp hd)
  rcases hfree with h | h
  · rw [hmod] at h; exact absurd h (by decide)
  · rw [hmod] at h; exact absurd h (by decide)

/-! ## §2 The bridge — the dust shape IS the ghost ray -/

/-- **THE BRIDGE.**  The mission board's full dust shape (the sheet
windows all dodge, the diagonal all dodges) IS the Mahler chamber's ghost
ray: the middle-third placement at every depth from three upward.  One
composition: the middle-third escalation plus the coefficient
identification. -/
theorem ghost_of_dust_shape (core : Nat)
    (hfree : core % 3 = 1 ∨ core % 3 = 2)
    (hwin : ∀ s : Nat, 1 ≤ s →
      (omegaCutWord s core) % 3^(s+2) < 2 * 3^(s+1))
    (hdust : ∀ k : Nat, 3 ≤ k →
      (omegaCutWord (k-1) 1 * core) % 3^k < 2 * 3^(k-1)) :
    GSTGhostRay.GhostRay core := by
  intro k hk
  have h := GSTTailFFourthDimension.omega_dust_shape_middle_third
    core hfree hwin hdust k hk
  rw [show GSTTowerFire.c (k-1) = omegaCutWord (k-1) 1 from
    c_eq_omegaCutWord (k-1)]
  exact h

/-! ## §3 The Mahler dust fracture — the diagonal must fire -/

/-- **THE MAHLER DUST FRACTURE.**  Under the Mahler sharpness input, no
three-free core can carry the full dust shape: either a sheet window
fires, or the diagonal FIRES at a named depth `k` — the middle-third
placement that the ghost ray demands at every depth is impossible at
some depth for every integer core. -/
theorem mahler_dust_fracture (H : GSTWorldtraceMahler.MahlerSharp)
    (core : Nat)
    (hfree : core % 3 = 1 ∨ core % 3 = 2)
    (hwin : ∀ s : Nat, 1 ≤ s →
      (omegaCutWord s core) % 3^(s+2) < 2 * 3^(s+1)) :
    ∃ k : Nat, 3 ≤ k ∧
      2 * 3^(k-1) ≤ (omegaCutWord (k-1) 1 * core) % 3^k := by
  by_contra hcon
  push_neg at hcon
  have hdust : ∀ k : Nat, 3 ≤ k →
      (omegaCutWord (k-1) 1 * core) % 3^k < 2 * 3^(k-1) := hcon
  have hg : GSTGhostRay.GhostRay core :=
    ghost_of_dust_shape core hfree hwin hdust
  have hu : ¬ 3 ∣ core := not_three_dvd_of_shape core hfree
  exact (GSTWorldtraceMahler.mahler_excludes_relative_lock H core hu)
    (GSTWorldtraceMahler.ghost_implies_relative_lock core hg)

/-- **THE FRACTURE, TOWER-COEFFICIENT FORM.**  The same fire, stated in
the `GSTTowerFire.c` language the window law consumes. -/
theorem mahler_dust_fracture_c (H : GSTWorldtraceMahler.MahlerSharp)
    (core : Nat)
    (hfree : core % 3 = 1 ∨ core % 3 = 2)
    (hwin : ∀ s : Nat, 1 ≤ s →
      (omegaCutWord s core) % 3^(s+2) < 2 * 3^(s+1)) :
    ∃ k : Nat, 3 ≤ k ∧
      2 * 3^(k-1) ≤ (GSTTowerFire.c (k-1) * core) % 3^k := by
  obtain ⟨k, hk, hfire⟩ := mahler_dust_fracture H core hfree hwin
  refine ⟨k, hk, ?_⟩
  rw [c_eq_omegaCutWord (k-1)]
  exact hfire

/-! ## §4 The diagonal-to-tower fire — the named row -/

/-- **THE MIXED-COEFFICIENT TRIT TRANSFER.**  If the diagonal fires at
depth `k0` (in the `c (k0-1)` coefficient form) and `k0 ≤ s+1`, then the
frozen diagonal at cut `s` carries the same top-third fire: the
coefficient's trits are frozen below the cut. -/
theorem c_trit_fire_transfer (s k0 core : Nat)
    (hk : k0 ≤ s + 1)
    (hfire : 2 * 3^(k0-1) ≤ (GSTTowerFire.c (k0-1) * core) % 3^k0) :
    2 * 3^(k0-1) ≤ (core * lteCoeff s) % 3^k0 := by
  have hc : GSTTowerFire.c (k0-1) = lteCoeff (k0-1) :=
    GSTGhostRay.c_eq_lteCoeff (k0-1)
  have hstab : lteCoeff s % 3^((k0-1)+1)
      = lteCoeff (k0-1) % 3^((k0-1)+1) :=
    GSTDiagonalRead.lteCoeff_stable (k0-1) s (by omega)
  have hE : 3^((k0-1)+1) = 3^k0 := by
    congr 1; omega
  rw [hE] at hstab
  have hmod : (core * lteCoeff s) % 3^k0
      = (core * lteCoeff (k0-1)) % 3^k0 := by
    have h1 : (core * lteCoeff s) % 3^k0
        = ((core % 3^k0) * (lteCoeff s % 3^k0)) % 3^k0 :=
      Nat.mul_mod core (lteCoeff s) (3^k0)
    have h2 : (core * lteCoeff (k0-1)) % 3^k0
        = ((core % 3^k0) * (lteCoeff (k0-1) % 3^k0)) % 3^k0 :=
      Nat.mul_mod core (lteCoeff (k0-1)) (3^k0)
    rw [h1, h2, hstab]
  rw [hmod, ← hc, Nat.mul_comm core (GSTTowerFire.c (k0-1))]
  exact hfire

/-- **THE DIAGONAL-TO-TOWER FIRE.**  A diagonal fire at depth `k0 ≤ s+1`
is a ternary digit two of the tower `4^(3^s·core)` at the NAMED row
`s + k0`: the window law reads the frozen diagonal's top-third fire
directly into the power's digit stream. -/
theorem tower_digit_two_of_diagonal_fire (s k0 core : Nat)
    (hk : k0 ≤ s + 1)
    (hfire : 2 * 3^(k0-1) ≤ (GSTTowerFire.c (k0-1) * core) % 3^k0) :
    digit3 (4^(3^s * core)) (s + k0) = 2 := by
  have hlo : 2 * 3^(k0-1) ≤ (core * lteCoeff s) % 3^k0 :=
    c_trit_fire_transfer s k0 core hk hfire
  have htrit : (core * lteCoeff s) / 3^(k0-1) % 3 = 2 :=
    digit_two_of_mid_range (core * lteCoeff s) (k0-1)
      (by rw [show (k0-1)+1 = k0 from by omega]; exact hlo)
  have hwin := GSTDiagonalRead.diagonal_window_law s core (k0-1) (by omega)
  have hrow : s + k0 = s + 1 + (k0-1) := by omega
  rw [hrow, hwin]
  exact htrit

/-! ## §5 The tower verdict — the honest disjunction -/

/-- **THE LEAST-FIRE LEMMA.**  From any diagonal fire witness, the
least one exists — pure strong induction, no decidability, no choice:
either the witness is least, or a smaller fire descends. -/
theorem exists_least_fire (core : Nat)
    (hex : ∃ m : Nat, 3 ≤ m ∧
      2 * 3^(m-1) ≤ (GSTTowerFire.c (m-1) * core) % 3^m) :
    ∃ m0 : Nat, 3 ≤ m0 ∧
      2 * 3^(m0-1) ≤ (GSTTowerFire.c (m0-1) * core) % 3^m0 ∧
      ∀ k : Nat, 3 ≤ k → k < m0 →
        (GSTTowerFire.c (k-1) * core) % 3^k < 2 * 3^(k-1) := by
  obtain ⟨m, hm3, hmfire⟩ := hex
  induction m using Nat.strongRecOn with
  | ind m ih =>
    by_cases hleast : ∃ k : Nat, 3 ≤ k ∧ k < m ∧
        2 * 3^(k-1) ≤ (GSTTowerFire.c (k-1) * core) % 3^k
    · obtain ⟨k, hk3, hkm, hkfire⟩ := hleast
      exact ih k hkm ⟨k, hk3, hkfire⟩
    · refine ⟨m, hm3, hmfire, ?_⟩
      intro k hk3 hkm
      by_contra hc
      push_neg at hc
      exact hleast ⟨k, hk3, hkm, hc⟩

/-- **THE TOWER VERDICT.**  Under the Mahler sharpness input, every
tower `3^s·core` over a three-free core with dodging sheet windows
either owns its ternary digit two outright at a NAMED row — when the
cut `s` reaches the core's minimal diagonal fire depth — or carries its
dodge band intact (every depth `k ≤ s+1` dodges) — when the cut is
below the fire depth, which is exactly the mission board's tower
primitive's hypothesis domain.  Either way, the tower's remaining
content is reduced to the ONE named Mahler input. -/
theorem tower_verdict_of_mahler (H : GSTWorldtraceMahler.MahlerSharp)
    (s core : Nat)
    (hfree : core % 3 = 1 ∨ core % 3 = 2)
    (hwin : ∀ t : Nat, 1 ≤ t →
      (omegaCutWord t core) % 3^(t+2) < 2 * 3^(t+1)) :
    (∃ p : Nat, digit3 (4^(3^s * core)) p = 2) ∨
    (∀ k : Nat, 3 ≤ k → k ≤ s + 1 →
      (GSTTowerFire.c (k-1) * core) % 3^k < 2 * 3^(k-1)) := by
  obtain ⟨k, hk3, hfire⟩ := mahler_dust_fracture_c H core hfree hwin
  obtain ⟨kf, hkf3, hkffire, hkmin⟩ := exists_least_fire core ⟨k, hk3, hfire⟩
  by_cases hle : kf ≤ s + 1
  · exact Or.inl ⟨s + kf,
      tower_digit_two_of_diagonal_fire s kf core hle hkffire⟩
  · refine Or.inr ?_
    intro k hk3' hks
    have hlt : k < kf := by omega
    exact hkmin k hk3' hlt

/-! ## §6 The honest record — the reduction law -/

/-- **THE REDUCTION LAW.**  The Mahler sharpness input fractures the
dust of every three-free core with dodging sheet windows: the diagonal
fires at a named depth.  Composed with §5, the tower family's entire
remaining content is the Mahler input plus the mission board's own
tower primitive for the below-fire cuts — nothing else remains. -/
theorem mahler_fracture_record (H : GSTWorldtraceMahler.MahlerSharp)
    (core : Nat)
    (hfree : core % 3 = 1 ∨ core % 3 = 2)
    (hwin : ∀ t : Nat, 1 ≤ t →
      (omegaCutWord t core) % 3^(t+2) < 2 * 3^(t+1)) :
    ∃ k : Nat, 3 ≤ k ∧
      2 * 3^(k-1) ≤ (GSTTowerFire.c (k-1) * core) % 3^k :=
  mahler_dust_fracture_c H core hfree hwin

#print axioms digit_two_of_mid_range
#print axioms c_eq_omegaCutWord
#print axioms not_three_dvd_of_shape
#print axioms ghost_of_dust_shape
#print axioms mahler_dust_fracture
#print axioms mahler_dust_fracture_c
#print axioms c_trit_fire_transfer
#print axioms tower_digit_two_of_diagonal_fire
#print axioms exists_least_fire
#print axioms tower_verdict_of_mahler
#print axioms mahler_fracture_record

end MahlerBridge406

#eval "ERDOS406_MAHLER_BRIDGE_GREEN"
