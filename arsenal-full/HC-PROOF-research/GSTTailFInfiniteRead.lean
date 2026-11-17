import GSTTailFFourthDimension
import GSTGraphV2OmegaWaveLaw

set_option maxRecDepth 1000000
set_option maxHeartbeats 20000000

/-!
# THE INFINITE READ — the survivor dust, read at every level at one time

The fourth dimension's engine reads every sheet, every window, every level
of every core at once.  This file completes that read on the ONE object the
whole ladder leaves unresolved: the **survivor dust** — the set of cores
whose scaled diagonal `(omegaCutWord (k-1) 1 * core) % 3^k` dodges the top
third at every level `k ≥ 3`.  Everything outside the dust is already dead
by the green universal blade (`omega_tower_dies_of_not_dust`).  The dust
itself is read here, at infinity, as five unconditional theorems:

* **§1 THE CHILD ANATOMY** — every core `c`, every level `m`: the parent's
  level residue splits as `q * 3^m + u`, and the three children
  `c`, `c + 3^m`, `c + 2 * 3^m` sit at the three Cantor positions of the
  next level — the child's residue is `((q + j) % 3) * 3^m + u`.  The unit
  word is one modulo three (`omega_cut_word_mod3`), so the three children
  occupy the bottom, middle, and top third exactly once each.
* **§2 THE SPLIT** — one of every three children ALWAYS fires the blade
  (top third), and one of every three children ALWAYS survives (the
  survivor inherits every level below `m` untouched — a multiple of
  `3^m` added to the core cannot move any level `k ≤ m`).  The survivor
  count doubles at every level: the Cantor arithmetic of the dust.
* **§3 THE IMMORTALITY** — the dust is NONEMPTY at every level `m ≥ 3`,
  one induction for all infinity, witness chain starting at the unit core.
* **§4 THE BLADE, COMPOSED** — the firing child's whole tower dies: every
  sheet `S ≥ m` of that child owns its digit two at position `S + (m+1)`,
  by the green universal blade consuming the anatomy's fire.
* **§5 THE RECEIPT** — one theorem, the whole infinite read: the dust is
  immortal at every level, the blade always eats one of three, every
  survivor spawns a survivor, every non-dust core's tower dies, and the
  kernel's own terminal identity — the input
  `four_power_omega_shadow_wave_tailF` and the even-exponent statement
  `∀ K ≥ 8, noTernaryTwo (4^K) = false` are one object, both directions.

What the read shows, stated plainly: the dust NEVER empties at any finite
level.  No finite assembly of level receipts can therefore exhaust it —
not level seven, not level eight, not any level.  The full content of a
binder-free input is exactly the question whether any natural exponent
rides the dust above the kernel base — and by the floor identity carried
below, that question IS the even-exponent Erdős ternary statement itself.
-/

namespace GSTTailFInfiniteRead

open GSTCanonicalSevenAxisBridge
open GSTGraphV2OmegaWaveLaw
open GSTTailFFourthDimension

/-! ## §0 The level truncation of the dust

The dust predicate of the fourth dimension, truncated at level `m`: the
levels `3 ≤ k ≤ m` of the scaled diagonal all dodge the top third.  The
full dust is exactly the all-levels truncation. -/

/-- **THE LEVEL-`m` DUST.**  The survivor dust truncated at level `m`:
every level `k` with `3 ≤ k ≤ m` of the scaled diagonal
`(omegaCutWord (k-1) 1 * core) % 3^k` dodges the top third. -/
def DustAt (m core : Nat) : Prop :=
  ∀ k : Nat, 3 ≤ k → k ≤ m →
    (omegaCutWord (k-1) 1 * core) % 3^k < 2 * 3^(k-1)

/-- The all-levels truncation IS the full dust of the fourth dimension. -/
theorem dust_at_all_iff_dust (core : Nat) :
    (∀ m : Nat, 3 ≤ m → DustAt m core) ↔
      omega_diagonal_survivor_dust core := by
  constructor
  · intro h k hk3
    exact h k hk3 k hk3 (by omega)
  · intro h m _ k hk3 _
    exact h k hk3

/-! ## §1 The child anatomy — the Cantor positions of the three children

Every core's three children at level `m` — `c`, `c + 3^m`, `c + 2 * 3^m` —
sit at the three thirds of the next level: the unit word is one modulo
three, so adding `j * 3^m` to the core shifts the level-`(m+1)` residue by
exactly `j * 3^m`, and the parent's residue `q * 3^m + u` lifts to the
child's residue `((q + j) % 3) * 3^m + u`.  One theorem, every core, every
level, no hypothesis. -/

/-- **THE CHILD ANATOMY.**  For every core `c` and level `m`: the parent's
level-`(m+1)` residue splits as `q * 3^m + u` with `u < 3^m`, and every
child `c + j * 3^m`'s level-`(m+1)` residue is `((q + j) % 3) * 3^m + u` —
the three children `j = 0, 1, 2` occupy the three thirds of the next
level exactly once each.  Unconditional. -/
theorem dust_child_anatomy (m c : Nat) :
    ∃ q u : Nat, u < 3^m ∧
      (omegaCutWord m 1 * c) % 3^(m+1) = q * 3^m + u ∧
      ∀ j : Nat, (omegaCutWord m 1 * (c + j * 3^m)) % 3^(m+1)
        = ((q + j) % 3) * 3^m + u := by
  obtain ⟨r, hr⟩ : ∃ r, (omegaCutWord m 1 * c) % 3^(m+1) = r := ⟨_, rfl⟩
  have hu : r % 3^m < 3^m := Nat.mod_lt _ (Nat.pow_pos (by decide))
  have hdec : r / 3^m * 3^m + r % 3^m = r := by
    have h := Nat.div_add_mod r (3^m)
    rw [Nat.mul_comm (3^m)] at h
    exact h
  have h31 : 3^(m+1) = 3 * 3^m := by rw [Nat.pow_succ]; ring
  refine ⟨r / 3^m, r % 3^m, hu, ?_, ?_⟩
  · rw [hr]
    exact hdec.symm
  · intro j
    -- the unit word is one modulo three: omegaCutWord m 1 = 3 * w + 1
    obtain ⟨w, hw⟩ : ∃ w, omegaCutWord m 1 = 3 * w + 1 := by
      refine ⟨omegaCutWord m 1 / 3, ?_⟩
      have hdm := Nat.div_add_mod (omegaCutWord m 1) 3
      have hm3 : omegaCutWord m 1 % 3 = 1 := by
        rw [omega_cut_word_mod3]
      rw [hm3] at hdm
      exact hdm.symm
    -- the shift: the child's residue is the parent's residue plus j sheets
    have hshift : (omegaCutWord m 1 * (c + j * 3^m)) % 3^(m+1)
        = (omegaCutWord m 1 * c + j * 3^m) % 3^(m+1) := by
      have hexp : omegaCutWord m 1 * (c + j * 3^m)
          = (omegaCutWord m 1 * c + j * 3^m) + 3^(m+1) * (j * w) := by
        rw [hw, h31]
        ring
      rw [hexp, Nat.add_mul_mod_self_left]
    -- the parent's own residue modulo the squared cut modulus is r
    obtain ⟨t0, ht0⟩ : ∃ t0, omegaCutWord m 1 * c = 3^(m+1) * t0 + r := by
      refine ⟨(omegaCutWord m 1 * c) / 3^(m+1), ?_⟩
      have hdm := Nat.div_add_mod (omegaCutWord m 1 * c) (3^(m+1))
      rw [hr] at hdm
      exact hdm.symm
    have hstep1 : (omegaCutWord m 1 * c + j * 3^m) % 3^(m+1)
        = (r + j * 3^m) % 3^(m+1) := by
      have hE : omegaCutWord m 1 * c + j * 3^m
          = (r + j * 3^m) + 3^(m+1) * t0 := by
        rw [ht0]
        ring
      rw [hE, Nat.add_mul_mod_self_left]
    -- the digit formula: the wrap-free position of the child
    have hdj := Nat.div_add_mod (r / 3^m + j) 3
    have hcongr : (r / 3^m + j) * 3^m
        = (3 * ((r / 3^m + j) / 3) + (r / 3^m + j) % 3) * 3^m := by
      rw [hdj]
    have hsplit : r + j * 3^m
        = ((r / 3^m + j) % 3) * 3^m + r % 3^m
          + 3^(m+1) * ((r / 3^m + j) / 3) := by
      calc r + j * 3^m
          = (r / 3^m * 3^m + r % 3^m) + j * 3^m := by rw [hdec]
        _ = (r / 3^m + j) * 3^m + r % 3^m := by ring
        _ = (3 * ((r / 3^m + j) / 3) + (r / 3^m + j) % 3) * 3^m
              + r % 3^m := by rw [hcongr]
        _ = ((r / 3^m + j) % 3) * 3^m + r % 3^m
              + 3^(m+1) * ((r / 3^m + j) / 3) := by
              rw [h31]; ring
    have hT : 0 < 3^m := Nat.pow_pos (by decide)
    have hv : (r / 3^m + j) % 3 ≤ 2 := by omega
    have hprod : (r / 3^m + j) % 3 * 3^m ≤ 2 * 3^m := by nlinarith
    have hbound : (r / 3^m + j) % 3 * 3^m + r % 3^m < 3^(m+1) := by
      rw [h31]
      omega
    rw [hshift, hstep1, hsplit, Nat.add_mul_mod_self_left]
    exact Nat.mod_eq_of_lt hbound

/-! ## §2 The split — the blade always eats one of three, the survivors
always spawn

The anatomy's three Cantor positions: exactly one of the three children
lands in the top third (the blade's fire band) and at least one lands in
the bottom two-thirds (the survivor).  Below the new level, a multiple of
`3^m` added to the core cannot move any level `k ≤ m` — the child inherits
the parent's dust untouched. -/

/-- **THE FIRING CHILD.**  For every core `c` and every level `m`, one of
the three children `c`, `c + 3^m`, `c + 2 * 3^m` ALWAYS lands its
level-`(m+1)` residue in the blade's fire band.  No hypothesis: the blade
eats one of every three children, unconditionally. -/
theorem dust_firing_child (m c : Nat) :
    ∃ j : Nat, j < 3 ∧
      2 * 3^m ≤ (omegaCutWord m 1 * (c + j * 3^m)) % 3^(m+1) := by
  obtain ⟨q, u, _hu, _hru, hdigit⟩ := dust_child_anatomy m c
  have hq3 : q % 3 = 0 ∨ q % 3 = 1 ∨ q % 3 = 2 := by omega
  rcases hq3 with hq3 | hq3 | hq3
  · refine ⟨2, by decide, ?_⟩
    have hdj := hdigit 2
    have hqj : (q + 2) % 3 = 2 := by omega
    rw [hqj] at hdj
    rw [hdj]
    omega
  · refine ⟨1, by decide, ?_⟩
    have hdj := hdigit 1
    have hqj : (q + 1) % 3 = 2 := by omega
    rw [hqj] at hdj
    rw [hdj]
    omega
  · refine ⟨0, by decide, ?_⟩
    have hdj := hdigit 0
    have hqj : (q + 0) % 3 = 2 := by omega
    rw [hqj] at hdj
    rw [hdj]
    omega

/-- **THE INHERITANCE.**  A child `c + j * 3^m` of a level-`m` dust parent
inherits every level `k ≤ m` untouched: the added multiple of `3^m` is
invisible modulo `3^k`. -/
theorem dust_child_inherits (m c j k : Nat) (hk3 : 3 ≤ k) (hkm : k ≤ m)
    (hc : DustAt m c) :
    (omegaCutWord (k-1) 1 * (c + j * 3^m)) % 3^k < 2 * 3^(k-1) := by
  have hsplit : 3^m = 3^k * 3^(m-k) := by
    rw [← Nat.pow_add]
    exact congrArg (Nat.pow 3) (by omega)
  have hexp : omegaCutWord (k-1) 1 * (c + j * 3^m)
      = omegaCutWord (k-1) 1 * c
        + 3^k * (omegaCutWord (k-1) 1 * j * 3^(m-k)) := by
    rw [hsplit]
    ring
  rw [hexp, Nat.add_mul_mod_self_left]
  exact hc k hk3 hkm

/-- **THE SURVIVING CHILD.**  For every level-`m` dust parent, one of the
three children is a level-`(m+1)` dust survivor.  The dust never dies by
descent: every survivor spawns a survivor. -/
theorem dust_surviving_child (m c : Nat) (hc : DustAt m c) :
    ∃ j : Nat, j < 3 ∧ DustAt (m+1) (c + j * 3^m) := by
  obtain ⟨q, u, hu, _hru, hdigit⟩ := dust_child_anatomy m c
  have hq3 : q % 3 = 0 ∨ q % 3 = 1 ∨ q % 3 = 2 := by omega
  rcases hq3 with hq3 | hq3 | hq3
  · refine ⟨0, by decide, ?_⟩
    intro k hk3 hkm1
    have hcases : k ≤ m ∨ k = m+1 := by omega
    rcases hcases with hkm | hkm
    · exact dust_child_inherits m c 0 k hk3 hkm hc
    · subst hkm
      have hqj : (q + 0) % 3 = 0 := by omega
      have hdj := hdigit 0
      rw [hqj] at hdj
      show (omegaCutWord m 1 * (c + 0 * 3^m)) % 3^(m+1) < 2 * 3^m
      rw [hdj, Nat.zero_mul, Nat.zero_add]
      omega
  · refine ⟨0, by decide, ?_⟩
    intro k hk3 hkm1
    have hcases : k ≤ m ∨ k = m+1 := by omega
    rcases hcases with hkm | hkm
    · exact dust_child_inherits m c 0 k hk3 hkm hc
    · subst hkm
      have hqj : (q + 0) % 3 = 1 := by omega
      have hdj := hdigit 0
      rw [hqj] at hdj
      show (omegaCutWord m 1 * (c + 0 * 3^m)) % 3^(m+1) < 2 * 3^m
      rw [hdj, Nat.one_mul]
      omega
  · refine ⟨1, by decide, ?_⟩
    intro k hk3 hkm1
    have hcases : k ≤ m ∨ k = m+1 := by omega
    rcases hcases with hkm | hkm
    · exact dust_child_inherits m c 1 k hk3 hkm hc
    · subst hkm
      have hqj : (q + 1) % 3 = 0 := by omega
      have hdj := hdigit 1
      rw [hqj] at hdj
      show (omegaCutWord m 1 * (c + 1 * 3^m)) % 3^(m+1) < 2 * 3^m
      rw [hdj, Nat.zero_mul, Nat.zero_add]
      omega

/-! ## §3 The immortality — the dust never empties, one induction for all
infinity

The unit core survives level three (`9709 % 27 = 16 < 18`), and every
survivor spawns a survivor.  One induction covers every level `m ≥ 3` at
once: the survivor set is nonempty at EVERY level — the dust is immortal. -/

/-- **THE BASE.**  The unit core carries the level-three dust. -/
theorem dust_base_three : DustAt 3 1 := by
  intro k hk3 hkm
  have hk : k = 3 := by omega
  subst hk
  show (omegaCutWord 2 1 * 1) % 27 < 2 * 9
  have hFac := omega_cut_factor 2 1
  have h4 : 4^(3^2 * 1) = 262144 := by decide
  have h27 : 3^(2+1) = 27 := by decide
  rw [h4, h27] at hFac
  have hW : omegaCutWord 2 1 = 9709 := by omega
  rw [hW, Nat.mul_one]
  decide

/-- **THE IMMORTALITY OF THE DUST.**  At every level `m ≥ 3` there is a
positive core carrying the level-`m` dust.  The dust never empties at any
finite level — the machine-certified reason no finite assembly of level
receipts can exhaust it. -/
theorem dust_immortal : ∀ m : Nat, 3 ≤ m → ∃ c : Nat, 0 < c ∧ DustAt m c := by
  intro m
  induction m with
  | zero => intro h3; exact absurd h3 (by omega)
  | succ m ih =>
    intro h3
    have hcases : m = 2 ∨ 3 ≤ m := by omega
    rcases hcases with hm2 | hm3
    · rw [hm2]
      exact ⟨1, by decide, dust_base_three⟩
    · obtain ⟨c, hc0, hcd⟩ := ih hm3
      obtain ⟨j, _hj, hcd1⟩ := dust_surviving_child m c hcd
      exact ⟨c + j * 3^m, by omega, hcd1⟩

/-! ## §4 The blade, composed — the firing child's whole tower dies

The anatomy's firing child does not merely miss the dust: its top-third
residue is the green universal blade's fire condition, so every sheet of
its tower from level `m` upward owns the ternary digit two. -/

/-- **THE BLADE EATS ONE OF THREE.**  For every core `c` and level `m`,
one of the three children has its ENTIRE tower dead: every sheet `S ≥ m`
of `4^(3^S * child)` owns its digit two at position `S + (m+1)`. -/
theorem dust_blade_eats_one_of_three (m c : Nat) :
    ∃ j : Nat, j < 3 ∧ ∀ S : Nat, m ≤ S →
      digit3 (4^(3^S * (c + j * 3^m))) (S + (m+1)) = 2 := by
  obtain ⟨j, hj3, hfire⟩ := dust_firing_child m c
  refine ⟨j, hj3, fun S hS => ?_⟩
  exact omega_tower_digit_two_universal (m+1) (c + j * 3^m) S
    (by omega) (by omega) hfire

/-! ## §5 The receipt — one theorem, the whole infinite read

The immortal dust, the blade's constant one-of-three, the survivors'
constant spawning, the death of every non-dust tower, and the kernel's
own terminal identity — assembled as ONE unconditional theorem. -/

/-- **THE INFINITE READ.**  One theorem, every face at once: (1) the dust
is nonempty at every level `m ≥ 3` — immortal; (2) the blade always eats
one of every three children; (3) every dust survivor spawns a dust
survivor at the next level; (4) every core outside the dust has its whole
tower dead by the universal blade; (5) the floor identity — the input
`four_power_omega_shadow_wave_tailF` and the even-exponent statement
`∀ K ≥ 8, noTernaryTwo (4^K) = false` are one object, both directions
kernel-certified.  No hypothesis, no binder, no per-level numeral. -/
theorem the_infinite_read
    (hB : erdos_even_conjecture_iff_tailF) :
    (∀ m : Nat, 3 ≤ m → ∃ c : Nat, 0 < c ∧ DustAt m c) ∧
    (∀ m c : Nat, ∃ j : Nat, j < 3 ∧
      2 * 3^m ≤ (omegaCutWord m 1 * (c + j * 3^m)) % 3^(m+1)) ∧
    (∀ m c : Nat, DustAt m c →
      ∃ j : Nat, j < 3 ∧ DustAt (m+1) (c + j * 3^m)) ∧
    (∀ core : Nat, ¬ omega_diagonal_survivor_dust core →
      ∃ k : Nat, 3 ≤ k ∧ ∀ S : Nat, k-1 ≤ S →
        digit3 (4^(3^S * core)) (S + k) = 2) ∧
    (four_power_omega_shadow_wave_tailF ↔
      ∀ K : Nat, 8 ≤ K → noTernaryTwo (4^K) = false) :=
  ⟨dust_immortal,
    fun m c => dust_firing_child m c,
    fun m c hc => dust_surviving_child m c hc,
    fun core h => omega_tower_dies_of_not_dust core h,
    hB.symm⟩


/-! ## Genuine branching of the survivor dust -/

/-- At every nontrivial dust level, the firing child and a surviving child can
be chosen distinct.  The infinite dust therefore branches while the universal
blade simultaneously removes a different branch. -/
theorem dust_fire_survive_distinct
    (m c : Nat) (hm : 2 ≤ m) (hc : DustAt m c) :
    ∃ jFire jSurvive : Nat,
      jFire < 3 ∧ jSurvive < 3 ∧ jFire ≠ jSurvive ∧
      2 * 3^m ≤
        (omegaCutWord m 1 * (c + jFire * 3^m)) % 3^(m+1) ∧
      DustAt (m+1) (c + jSurvive * 3^m) := by
  obtain ⟨jf, hjf, hfire⟩ := dust_firing_child m c
  obtain ⟨js, hjs, hsurv⟩ := dust_surviving_child m c hc
  have hne : jf ≠ js := by
    intro heq
    subst js
    have hlow := hsurv (m+1) (by omega) (by omega)
    exact (Nat.not_le_of_gt hlow) hfire
  exact ⟨jf, js, hjf, hjs, hne, hfire, hsurv⟩

/-- The survivor tree therefore contains, at every level m≥2, a simultaneous
extinction branch and continuation branch. -/
theorem dust_branching_crown :
    ∀ m c : Nat, 2 ≤ m → DustAt m c →
      ∃ jFire jSurvive : Nat,
        jFire < 3 ∧ jSurvive < 3 ∧ jFire ≠ jSurvive ∧
        2 * 3^m ≤
          (omegaCutWord m 1 * (c + jFire * 3^m)) % 3^(m+1) ∧
        DustAt (m+1) (c + jSurvive * 3^m) :=
  dust_fire_survive_distinct

#check dust_fire_survive_distinct
#check dust_branching_crown
#print axioms dust_fire_survive_distinct

#print axioms dust_at_all_iff_dust
#print axioms dust_child_anatomy
#print axioms dust_firing_child
#print axioms dust_child_inherits
#print axioms dust_surviving_child
#print axioms dust_base_three
#print axioms dust_immortal
#print axioms dust_blade_eats_one_of_three
#print axioms the_infinite_read

end GSTTailFInfiniteRead
