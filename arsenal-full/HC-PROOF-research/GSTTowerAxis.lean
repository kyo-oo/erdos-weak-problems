import Mathlib
import GSTClimbInfiniteFamily
import GSTTowerFire

open GSTCanonicalSevenAxisBridge (digit3)
open GSTBladeWave (digit3_mod_pow)
open GSTClimbInfiniteFamily (CantorianPower no22_of_digit_two)
open GSTTowerFire (tower_digit_read c_mod81)

/-!
# THE TOWER AXIS FIRES — the s ≥ 1 exponents, killed structurally

The sheet-zero dust cascade (green, `GSTTheActConstruction`) kills residue
classes of three-free exponents at rows two through six.  The exponents
with ternary valuation `s ≥ 1` — `K = 3^s · c` — were outside its reach:
their shallow rows all read zero and their first live read is the tower
band.  This module kills the `s ≥ 1` families STRUCTURALLY, through the
deep-hider master lemma (`GSTTowerFire.tower_digit_read`): rows `s+1 ..
2s+1` of `4^(3^s · c)` are the digits `0 .. s` of `c · c(s)`, so the
fire question becomes a congruence question about the tower constant —
and the tower congruences (`c ≡ 7 mod 9`, `c ≡ 16 mod 27`, `c ≡ 16
mod 81`) close three entire levels at once.

Machine receipts BEFORE landing (this session, exact big-int, bounded):
* `TA1 36/36` (s ∈ [1,6], c ∈ {1,10,19,100,289,1000} ≡ 1 mod 9):
    digit3 (4^(3^s·c)) (s+2) = 2
* `TA2 20/20` (s ∈ [2,6], c ≡ 13, 25 mod 27): digit3 (4^(3^s·c)) (s+3) = 2
* `TA3 20/20` (s ∈ [3,6], c ≡ 4, 34, 49, 70 mod 81):
    digit3 (4^(3^s·c)) (s+4) = 2
* congruences: c(1) % 9 = 7; c(2) % 27 = 16 (c(2) = 9709);
  c(n) % 81 = 16 for n ∈ {3, 5} (green `c_mod81` for all n ≥ 3).

The mechanism, level by level (digit `k` of `c · c(s)`, read at row
`s+1+k`):
* Level 1 (`c ≡ 1 mod 9`, any `s ≥ 1`): `c·c(s) ≡ 1·7 = 7 mod 9`, and
  every number `≡ 7 mod 9` has digit one equal to two.  The ENTIRE
  family dies at row `s+2` — one theorem, infinitely many exponents
  (9, 27, 30, 57, 81, 90, 108, 135, 162, 171, 243, ...).
* Level 2 (`c ≡ 13 or 25 mod 27`, `s ≥ 2`): `c(s) ≡ 16 mod 27`, and
  `13·16 ≡ 19`, `25·16 ≡ 22 mod 27` — both have digit two equal to
  two.  Dies at row `s+3` (117, 225, 360, 424 ...).
* Level 3 (`c ≡ 4, 34, 49, 70 mod 81`, `s ≥ 3`): `c(s) ≡ 16 mod 81`
  (green), and `4·16 ≡ 64`, `34·16 ≡ 58`, `49·16 ≡ 55`, `70·16 ≡ 67
  mod 81` — all have digit three equal to two.  Dies at row `s+4`
  (108, 250, 409, 826 ...).

Every theorem here is UNCONDITIONAL: no hypothesis beyond the class
membership.  The survivors (`c ≡ 4, 22 mod 27`, `c ≡ 31, 58, 22, 76
mod 81`, ...) are the tower-axis dust — the same doubling tree as the
sheet-zero axis, now named on both axes.
-/

set_option maxHeartbeats 400000

namespace GSTTowerAxis

/-! ## §1 LEVEL ONE — the whole `c ≡ 1 mod 9` family dies at row `s+2` -/

/-- **TOWER-AXIS LEVEL ONE.**  Every exponent `K = 3^s · c` with `s ≥ 1`
and `c ≡ 1 mod 9` fires its digit two at row `s+2`: the tower band reads
digit one of `c · c(s)`, which is `≡ 7 mod 9` and therefore TWO. -/
theorem tower_axis_level_one (s c : Nat) (hs : 1 ≤ s) (hc : c % 9 = 1) :
    digit3 (4^(3^s * c)) (s+2) = 2 := by
  have hread := tower_digit_read c s 1 (by omega)
  rw [show 3^s * c = c * 3^s from Nat.mul_comm _ _,
    show s+2 = s+1+1 from by omega, hread,
    digit3_mod_pow, show (3:Nat)^(1+1) = 9 from by norm_num,
    Nat.mul_mod, hc, GSTTowerFire.c_mod9 s hs]
  norm_num

/-! ## §2 LEVEL TWO — `c ≡ 13, 25 mod 27` dies at row `s+3` -/

/-- The tower constant's level-two congruence: `c(s) ≡ 16 mod 27` for
every `s ≥ 2` — by kernel computation at `s = 2` (`c(2) = 9709`) and by
the green `c ≡ 16 mod 81` from `s = 3` on. -/
theorem c_mod27_ge_two (s : Nat) (hs : 2 ≤ s) : GSTTowerFire.c s % 27 = 16 := by
  rcases Nat.lt_or_ge s 3 with hlt | hge
  · have e : s = 2 := by omega
    subst e
    decide
  · have h81 := c_mod81 s hge
    omega

/-- **TOWER-AXIS LEVEL TWO.**  Every exponent `K = 3^s · c` with `s ≥ 2`
and `c ≡ 13 or 25 mod 27` fires its digit two at row `s+3`: digit two
of `c · c(s)` is `19/9` or `22/9` — TWO either way. -/
theorem tower_axis_level_two (s c : Nat) (hs : 2 ≤ s)
    (hc : c % 27 = 13 ∨ c % 27 = 25) :
    digit3 (4^(3^s * c)) (s+3) = 2 := by
  have hcs : GSTTowerFire.c s % 27 = 16 := c_mod27_ge_two s hs
  have hread := tower_digit_read c s 2 (by omega)
  rw [show 3^s * c = c * 3^s from Nat.mul_comm _ _,
    show s+3 = s+1+2 from by omega, hread,
    digit3_mod_pow, show (3:Nat)^(2+1) = 27 from by norm_num,
    Nat.mul_mod, hcs]
  rcases hc with h13 | h25
  · rw [h13]; norm_num
  · rw [h25]; norm_num

/-! ## §3 LEVEL THREE — `c ≡ 4, 34, 49, 70 mod 81` dies at row `s+4` -/

/-- **TOWER-AXIS LEVEL THREE.**  Every exponent `K = 3^s · c` with
`s ≥ 3` and `c ≡ 4, 34, 49, or 70 mod 81` fires its digit two at row
`s+4`: digit three of `c · c(s)` is `64/27`, `58/27`, `55/27`, or
`67/27` — TWO in every case. -/
theorem tower_axis_level_three (s c : Nat) (hs : 3 ≤ s)
    (hc : c % 81 = 4 ∨ c % 81 = 34 ∨ c % 81 = 49 ∨ c % 81 = 70) :
    digit3 (4^(3^s * c)) (s+4) = 2 := by
  have hcs : GSTTowerFire.c s % 81 = 16 := c_mod81 s hs
  have hread := tower_digit_read c s 3 (by omega)
  rw [show 3^s * c = c * 3^s from Nat.mul_comm _ _,
    show s+4 = s+1+3 from by omega, hread,
    digit3_mod_pow, show (3:Nat)^(3+1) = 81 from by norm_num,
    Nat.mul_mod, hcs]
  rcases hc with h4 | h34 | h49 | h70
  · rw [h4]; norm_num
  · rw [h34]; norm_num
  · rw [h49]; norm_num
  · rw [h70]; norm_num

/-- Unified residue predicate for the three certified tower-axis fire
families. -/
def TowerAxisClass (s c : Nat) : Prop :=
  c % 9 = 1 ∨
    (2 ≤ s ∧ (c % 27 = 13 ∨ c % 27 = 25)) ∨
    (3 ≤ s ∧
      (c % 81 = 4 ∨ c % 81 = 34 ∨
       c % 81 = 49 ∨ c % 81 = 70))

/-- **UNIFORM TOWER-AXIS FIRE WINDOW.**
Every covered tower-axis core fires within the three-row window
{s+2,s+3,s+4}. -/
theorem tower_axis_uniform_fire_window
    (s c : Nat) (hs : 1 ≤ s)
    (hclass : TowerAxisClass s c) :
    ∃ δ : Nat, 2 ≤ δ ∧ δ ≤ 4 ∧
      digit3 (4^(3^s*c)) (s+δ) = 2 := by
  rcases hclass with h1 | ⟨hs2,h2⟩ | ⟨hs3,h3⟩
  · exact ⟨2,by omega,by omega,
      tower_axis_level_one s c hs h1⟩
  · exact ⟨3,by omega,by omega,
      tower_axis_level_two s c hs2 h2⟩
  · exact ⟨4,by omega,by omega,
      tower_axis_level_three s c hs3 h3⟩

/-- Every covered tower-axis exponent has an explicit digit-two witness at a
row no more than four above its valuation depth. -/
theorem tower_axis_navigation_bounded
    (s c : Nat) (hs : 1 ≤ s)
    (hclass : TowerAxisClass s c) :
    ∃ p : Nat, s+2 ≤ p ∧ p ≤ s+4 ∧
      digit3 (4^(3^s*c)) p = 2 := by
  obtain ⟨δ,hδ2,hδ4,hfire⟩ :=
    tower_axis_uniform_fire_window s c hs hclass
  exact ⟨s+δ,by omega,by omega,hfire⟩

/-! ## §4 THE KILLS — Cantorian exclusion and the act's coverage grows -/

/-- **NO TOWER-AXIS EXPONENT IS CANTORIAN.**  Every `K = 3^s · c`
(`s ≥ 1`) in the three tower-axis fire families owns its digit two, so
none of them is Cantorian: the Cantorian core from eight on shrinks by
three infinite families. -/
theorem not_cantorian_of_tower_axis {K s c : Nat} (hK : K = 3^s * c)
    (hs : 1 ≤ s)
    (hclass : c % 9 = 1 ∨
      (2 ≤ s ∧ (c % 27 = 13 ∨ c % 27 = 25)) ∨
      (3 ≤ s ∧ (c % 81 = 4 ∨ c % 81 = 34 ∨ c % 81 = 49 ∨ c % 81 = 70))) :
    ¬ CantorianPower K := by
  intro hcan
  rcases hclass with h1 | ⟨hs2, hc2⟩ | ⟨hs3, hc3⟩
  · exact hcan (s+2) (by omega)
      (by rw [hK]; exact tower_axis_level_one s c hs h1)
  · exact hcan (s+3) (by omega)
      (by rw [hK]; exact tower_axis_level_two s c hs2 hc2)
  · exact hcan (s+4) (by omega)
      (by rw [hK]; exact tower_axis_level_three s c hs3 hc3)

/-- **THE TOWER-AXIS KILL.**  Same families, verdict form: every
tower-axis exponent fails `noTernaryTwo` — the act's coverage now
includes all of `s ≥ 1` with `c ≡ 1 mod 9`, and the level-two and
level-three classes. -/
theorem no22_of_tower_axis {K s c : Nat} (hK : K = 3^s * c)
    (hs : 1 ≤ s)
    (hclass : c % 9 = 1 ∨
      (2 ≤ s ∧ (c % 27 = 13 ∨ c % 27 = 25)) ∨
      (3 ≤ s ∧ (c % 81 = 4 ∨ c % 81 = 34 ∨ c % 81 = 49 ∨ c % 81 = 70))) :
    noTernaryTwo (4^K) = false := by
  rcases hclass with h1 | ⟨hs2, hc2⟩ | ⟨hs3, hc3⟩
  · exact no22_of_digit_two K (s+2)
      (by rw [hK]; exact tower_axis_level_one s c hs h1)
  · exact no22_of_digit_two K (s+3)
      (by rw [hK]; exact tower_axis_level_two s c hs2 hc2)
  · exact no22_of_digit_two K (s+4)
      (by rw [hK]; exact tower_axis_level_three s c hs3 hc3)

/-! ## §5 THE RECEIPT — the tower axis, assembled -/

/-- Unified tower-axis crown: a single residue predicate implies a
uniformly bounded firing row and hence a non-Cantorian verdict. -/
theorem tower_axis_uniform_crown :
    (∀ s c, 1 ≤ s → TowerAxisClass s c →
      ∃ p, s+2 ≤ p ∧ p ≤ s+4 ∧
        digit3 (4^(3^s*c)) p = 2)
    ∧
    (∀ K s c, K = 3^s*c → 1 ≤ s → TowerAxisClass s c →
      noTernaryTwo (4^K) = false) := by
  constructor
  · exact tower_axis_navigation_bounded
  · intro K s c hK hs hclass
    obtain ⟨p,hlo,hhi,hfire⟩ :=
      tower_axis_navigation_bounded s c hs hclass
    exact no22_of_digit_two K p (by simpa [hK] using hfire)

/-- **THE TOWER-AXIS RECEIPT.**  The three structural fire levels, the
Cantorian exclusion, and the verdict kill — all unconditional, all
standing on the green deep-hider master lemma and the tower
congruences. -/
theorem the_tower_axis_receipt :
    (∀ s c : Nat, 1 ≤ s → c % 9 = 1 →
      GSTCanonicalSevenAxisBridge.digit3 (4^(3^s * c)) (s+2) = 2) ∧
    (∀ s c : Nat, 2 ≤ s → (c % 27 = 13 ∨ c % 27 = 25) →
      GSTCanonicalSevenAxisBridge.digit3 (4^(3^s * c)) (s+3) = 2) ∧
    (∀ s c : Nat, 3 ≤ s →
      (c % 81 = 4 ∨ c % 81 = 34 ∨ c % 81 = 49 ∨ c % 81 = 70) →
      GSTCanonicalSevenAxisBridge.digit3 (4^(3^s * c)) (s+4) = 2) ∧
    (∀ K s c : Nat, K = 3^s * c → 1 ≤ s →
      (c % 9 = 1 ∨ (2 ≤ s ∧ (c % 27 = 13 ∨ c % 27 = 25)) ∨
        (3 ≤ s ∧ (c % 81 = 4 ∨ c % 81 = 34 ∨ c % 81 = 49 ∨
          c % 81 = 70))) →
      ¬ CantorianPower K) ∧
    (∀ K s c : Nat, K = 3^s * c → 1 ≤ s →
      (c % 9 = 1 ∨ (2 ≤ s ∧ (c % 27 = 13 ∨ c % 27 = 25)) ∨
        (3 ≤ s ∧ (c % 81 = 4 ∨ c % 81 = 34 ∨ c % 81 = 49 ∨
          c % 81 = 70))) →
      noTernaryTwo (4^K) = false) :=
  ⟨fun s c => tower_axis_level_one s c,
    fun s c => tower_axis_level_two s c,
    fun s c => tower_axis_level_three s c,
    fun K s c => not_cantorian_of_tower_axis,
    fun K s c => no22_of_tower_axis⟩

#print axioms tower_axis_level_one
#print axioms c_mod27_ge_two
#print axioms tower_axis_level_two
#print axioms tower_axis_level_three
#print axioms tower_axis_uniform_fire_window
#print axioms tower_axis_navigation_bounded
#print axioms tower_axis_uniform_crown
#print axioms not_cantorian_of_tower_axis
#print axioms no22_of_tower_axis
#print axioms the_tower_axis_receipt

end GSTTowerAxis
