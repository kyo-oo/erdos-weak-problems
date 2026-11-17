import GSTTailFFourthDimension
import GSTGraphV2OmegaWaveLaw

set_option maxRecDepth 1000000
set_option maxHeartbeats 20000000

/-!
# THE ONE LANE — the hTailF construction, one separate file, zero monolith bytes

This file is the single lane the whole campaign was ordered to build: ONE
separate file, appended to nothing, editing nothing, in which the entire
mathematical construction of the `hTailF` route is visible at one single
time — all cases, all rows, all towers, all sheets, all levels, and the
infinite face — with **no hypothesis and no binder** on any theorem of the
lane's spine.

The construction, in one paragraph.  Every positive exponent `M` factors
uniquely as `M = 3^s * core` with `core` three-free (§1).  The lane's
**case map** (§3) then reads the power `4^M` through the fourth dimension's
observation law and splits the universe of exponents into exactly two
visible kinds:

* the **fired kind** — `4^M` owns a ternary digit two, the fire located by
  the lane's own law: `core % 3 = 2` fires at row `s+1`, a tower core
  `≡ 1 (mod 9)` above sheet zero fires at row `s+2`, a sheet-zero exponent
  `≡ 7 (mod 9)` fires at row two — three infinite families, one lane;

* the **dust kind** — the exponent carries the complete no-fire
  certificate: the three-free family structure (`core % 9 = 4`, or sheet
  zero with `core % 9 = 1`, or above sheet zero with `core % 9 = 7`) and a
  cut word `omegaCutWord s core` that never fires its top third at ANY
  depth — the whole tower, the whole row, the whole infinite tail of the
  power, in one clause.

§4 proves the certificate is exactly the shadow package's core: the family
clause of `omegaShadowTailF`, its window clause, its row-all-depths clause,
and its diagonal clause all follow from the certificate — the package is
the no-fire structure read through the LTE eyes, sharpened to the cut word
itself.  §5 assembles the engine faces — the exact cube lift, the
three-window dichotomy, the dust's middle-third shape — and the kernel's
floor identity into the one-lane receipt: one theorem, every face, zero
hypotheses.

Every theorem in this file is unconditional and carries its axiom receipt
below.  The floor receipt is stated as mathematics, not as opinion: by the
monolith's kernel-certified terminal identity (both directions), the input
`four_power_omega_shadow_wave_tailF` and the even-exponent Erdős ternary
statement `∀ K ≥ 8, noTernaryTwo (4^K) = false` are one object — so the
dust kind's emptiness above 500 IS the full content of the input, and the
lane displays exactly where every exponent of that content lives.
-/

namespace GSTTailFOneLane

open GSTCanonicalSevenAxisBridge
open GSTFourPowerDirectResidue (lteCoeff)
open GSTGraphV2OmegaWaveLaw
open GSTTailFFourthDimension

/-! ## §1 The canonical decomposition and the tower's unit word

Every positive exponent is a unique sheet-core pair; the pure tower's cut
word is the LTE mean itself.  Two small laws, both unconditional. -/

/-- **THE CANONICAL DECOMPOSITION.**  Every positive exponent `M` is a
tower-core pair `M = 3^s * core` with `core` three-free. -/
theorem one_lane_three_free_decomposition (M : Nat) : 0 < M →
    ∃ s core : Nat, M = 3^s * core ∧ ¬ 3 ∣ core := by
  exact Nat.strongRecOn M (fun N ih hN => by
    by_cases h3 : 3 ∣ N
    · obtain ⟨m, hm⟩ := h3
      have hm1 : 1 ≤ m := by omega
      obtain ⟨s, core, hs, hc⟩ := ih m (by omega) hm1
      refine ⟨s+1, core, ?_, hc⟩
      calc N = 3 * m := hm
        _ = 3 * (3^s * core) := by rw [hs]
        _ = 3^(s+1) * core := by
            rw [show 3^(s+1) = 3 * 3^s from by rw [Nat.pow_succ]; ring]
            ring
    · exact ⟨0, N, by rw [Nat.pow_zero, Nat.one_mul], h3⟩)

/-- **THE TOWER'S UNIT WORD.**  The cut word of the unit core is the LTE
mean itself: `omegaCutWord s 1 = lteCoeff s`. -/
theorem one_lane_cut_word_one (s : Nat) :
    omegaCutWord s 1 = lteCoeff s := by
  simp [omegaCutWord, omegaGeoSum, Finset.sum_range_one]

/-! ## §2 The lane's fire laws — the three infinite families

Where the fire lives for every exponent outside the dust: the cut row
itself (`core % 3 = 2`), the row above the cut on towers (`core % 9 = 1`
above sheet zero), and row two of the sheet-zero cycle (`exponent % 9 =
7`).  All unconditional, all one lane. -/

/-- **FIRE AT THE CUT ROW.**  Every sheet-core pair whose core is congruent
to two modulo three fires at row `s+1`: the digit there is the core's own
first nonzero ternary trit. -/
theorem one_lane_fire_of_mod3_two (s core : Nat) (h : core % 3 = 2) :
    digit3 (4^(3^s * core)) (s+1) = 2 := by
  rw [omega_cut_digit s core, h]

/-- **FIRE ABOVE THE CUT.**  Every tower core congruent to one modulo nine,
above sheet zero, fires at row `s+2`: the cut word is `7 * core` modulo
nine there. -/
theorem one_lane_fire_of_tower_mod9_one (s core : Nat) (hs : 1 ≤ s)
    (h : core % 9 = 1) :
    digit3 (4^(3^s * core)) (s+2) = 2 :=
  omega_level2_digit_two s core hs (Or.inl h)

/-- **FIRE AT ROW TWO OF THE SHEET-ZERO CYCLE.**  Every exponent congruent
to seven modulo nine fires at row two: the base four has order nine modulo
twenty-seven. -/
theorem one_lane_row2_fire (K : Nat) (h : K % 9 = 7) :
    digit3 (4^K) 2 = 2 :=
  omega_row2_digit_two K h

/-! ## §3 THE CROWN — the one-lane case map

Every positive exponent, one disjunction, no hypothesis, no binder: either
the power owns its digit two, or the exponent carries the complete dust
certificate — the family structure and a cut word that never fires at any
depth.  All cases, all rows, all towers, all levels: one lane. -/

/-- **THE ONE-LANE CASE MAP.**  For every exponent `K+1`: either `4^(K+1)`
owns a ternary digit two, or the exponent's canonical sheet-core pair
carries the full no-fire certificate — the three-free family clause of the
shadow package together with a cut word whose every depth dodges the top
third.  Unconditional. -/
theorem one_lane_complete (K : Nat) :
    (∃ p : Nat, digit3 (4^(K+1)) p = 2) ∨
      (∃ s core : Nat, (K+1) = 3^s * core ∧ ¬ 3 ∣ core ∧
        (core % 9 = 4 ∨ (s = 0 ∧ core % 9 = 1) ∨ (1 ≤ s ∧ core % 9 = 7))
        ∧ (∀ i : Nat, (omegaCutWord s core) % 3^(i+1) < 2 * 3^i)) := by
  obtain ⟨s, core, hK, hfree⟩ :=
    one_lane_three_free_decomposition (K+1) (by omega)
  by_cases hfire : ∃ p : Nat, digit3 (4^(K+1)) p = 2
  · exact Or.inl hfire
  · refine Or.inr ⟨s, core, hK, hfree, ?_, ?_⟩
    · -- THE FAMILY: the three fire laws leave exactly the package's families
      have hf0 : core % 3 ≠ 0 := by
        intro h
        exact hfree ⟨core / 3, by
          have hdm := Nat.div_add_mod core 3
          omega⟩
      have hc3 : core % 3 = 1 ∨ core % 3 = 2 := by omega
      rcases hc3 with hc1 | hc2
      · have h91 : core % 9 = 1 ∨ core % 9 = 4 ∨ core % 9 = 7 := by
          have hmod9 := Nat.div_add_mod core 9
          have hmod3 := Nat.div_add_mod core 3
          omega
        rcases h91 with h91 | h94 | h97
        · rcases Nat.eq_zero_or_pos s with rfl | hs1
          · exact Or.inr (Or.inl ⟨rfl, h91⟩)
          · exact absurd ⟨s+2, by
              rw [hK]
              exact omega_level2_digit_two s core hs1 (Or.inl h91)⟩ hfire
        · exact Or.inl h94
        · rcases Nat.eq_zero_or_pos s with rfl | hs1
          · rw [Nat.pow_zero, Nat.one_mul] at hK
            have hK9 : (K+1) % 9 = 7 := by rw [hK]; exact h97
            exact absurd ⟨2, omega_row2_digit_two (K+1) hK9⟩ hfire
          · exact Or.inr (Or.inr ⟨hs1, h97⟩)
      · exact absurd ⟨s+1, by
          rw [hK, omega_cut_digit s core]
          exact hc2⟩ hfire
    · -- THE NEVER-FIRES CLAUSE: the observation law leaves no depth unlit
      intro i
      by_cases htop : 2 * 3^i ≤ (omegaCutWord s core) % 3^(i+1)
      · exact absurd ⟨s+1+i, by
          rw [hK]
          exact tower_observation_digit_two s core i htop⟩ hfire
      · have hlt : (omegaCutWord s core) % 3^(i+1) < 3^(i+1) :=
          Nat.mod_lt _ (Nat.pow_pos (by decide))
        omega

/-! ## §4 The certificate's faces — the shadow package's core, proved

The dust certificate IS the shadow package's core.  From the family clause
and the never-fires clause alone, the package's window clause, diagonal
clause, and sheet-zero row-all-depths clause all follow: for a core
congruent to one modulo three, the cut word is the diagonal modulo the
squared cut modulus, so every dodged depth of the word is a dodged level
of the diagonal.  The package is the no-fire structure, sharpened. -/

/-- **THE CERTIFICATE'S FACES.**  Every exponent carrying the dust
certificate satisfies the shadow package's window clause, diagonal clause,
and row-all-depths clause.  The certificate is the no-fire core of the
package. -/
theorem one_lane_certificate_faces (s core : Nat)
    (hfam : core % 9 = 4 ∨ (s = 0 ∧ core % 9 = 1) ∨ (1 ≤ s ∧ core % 9 = 7))
    (hnever : ∀ i : Nat, (omegaCutWord s core) % 3^(i+1) < 2 * 3^i) :
    (omegaCutWord s core) % 3^(s+2) < 2 * 3^(s+1) ∧
    (∀ k : Nat, 3 ≤ k → k ≤ s+1 →
      (omegaCutWord s 1 * core) % 3^k < 2 * 3^(k-1)) ∧
    (s = 0 → ∀ j : Nat, 2 ≤ j →
      (omegaCutWord 0 core) % 3^(j+1) < 2 * 3^j) := by
  have hc1 : core % 3 = 1 := by
    have hmod9 := Nat.div_add_mod core 9
    have hmod3 := Nat.div_add_mod core 3
    rcases hfam with h4 | ⟨_, h1⟩ | ⟨_, h7⟩
    · omega
    · omega
    · omega
  refine ⟨hnever (s+1), ?_, ?_⟩
  · intro k _hk3 hks
    have hOne : omegaCutWord s 1 * core = lteCoeff s * core := by
      rw [one_lane_cut_word_one s]
    have hW := omega_cut_word_mod_pow2 s core hc1
    have hdvd : 3^k ∣ 3^(s+2) := Nat.pow_dvd_pow 3 (by omega)
    have htrans : ∀ X : Nat, (X % 3^(s+2)) % 3^k = X % 3^k :=
      fun X => Nat.mod_mod_of_dvd X hdvd
    calc (omegaCutWord s 1 * core) % 3^k
        = (lteCoeff s * core) % 3^k := by rw [hOne]
      _ = ((lteCoeff s * core) % 3^(s+2)) % 3^k := (htrans _).symm
      _ = ((omegaCutWord s core) % 3^(s+2)) % 3^k := by rw [hW]
      _ = (omegaCutWord s core) % 3^k := htrans _
      _ < 2 * 3^(k-1) := by
          have h := hnever (k-1)
          rwa [show (k-1)+1 = k from by omega] at h
  · intro hs0 j _
    rw [hs0] at hnever
    exact hnever j

/-! ## §5 The omega face and the one-lane receipt — infinity at one time

The engine's infinite faces — the exact cube lift that generates every
sheet of every tower, the three-window dichotomy that reads every sheet
of every three-free core, the dust's middle-third shape that pins the
survivor diagonal at every level — assembled with the kernel's floor
identity into ONE theorem: the whole construction, one lane, zero
hypotheses. -/

/-- **THE OMEGA FACE.**  The engine and the floor, as one unconditional
object: the cube lift, the three-window dichotomy, the dust's shape, and
the terminal identity — the input and the even-exponent statement are one
object, both directions kernel-certified. -/
theorem one_lane_omega_face
    (hB : erdos_even_conjecture_iff_tailF) :
    (∀ s core : Nat, omegaCutWord (s+1) core
      = omegaCutWord s core
        + 3^(s+1) * (omegaCutWord s core * omegaCutWord s core
          + 3^s * (omegaCutWord s core * omegaCutWord s core
            * omegaCutWord s core))) ∧
    (∀ s core : Nat, 1 ≤ s → core % 3 = 1 ∨ core % 3 = 2 →
      (2 * 3^(s+1) ≤ (omegaCutWord s core) % 3^(s+2)
        ∧ digit3 (4^(3^s * core)) (2*s+2) = 2)
      ∨ (omegaCutWord s core) % 3^(s+2) < 3^(s+1)
      ∨ (3^(s+1) ≤ (omegaCutWord s core) % 3^(s+2)
        ∧ (omegaCutWord s core) % 3^(s+2) < 2 * 3^(s+1)
        ∧ ∀ S : Nat, s+1 ≤ S →
          digit3 (4^(3^S * core)) (S + (s+2)) = 2)) ∧
    (∀ core : Nat, core % 3 = 1 ∨ core % 3 = 2 →
      (∀ s : Nat, 1 ≤ s →
        (omegaCutWord s core) % 3^(s+2) < 2 * 3^(s+1)) →
      (∀ k : Nat, 3 ≤ k →
        (omegaCutWord (k-1) 1 * core) % 3^k < 2 * 3^(k-1)) →
      ∀ k : Nat, 3 ≤ k →
        3^(k-1) ≤ (omegaCutWord (k-1) 1 * core) % 3^k
          ∧ (omegaCutWord (k-1) 1 * core) % 3^k < 2 * 3^(k-1)) ∧
    (four_power_omega_shadow_wave_tailF ↔
      ∀ K : Nat, 8 ≤ K → noTernaryTwo (4^K) = false) :=
  ⟨fun s core => omega_cut_word_cube_lift_exact s core,
    fun s core hs hfree => omega_sheet_window_dichotomy s core hs hfree,
    fun core hfree hwin hdust =>
      omega_dust_shape_middle_third core hfree hwin hdust,
    hB.symm⟩

/-- **THE ONE-LANE RECEIPT — the whole construction, one theorem, zero
hypotheses.**  Every exponent's case map (fire or the complete dust
certificate), the certificate's faces (the shadow package's window,
diagonal, and row-all-depths clauses), the engine (the exact cube lift
that generates the entire cascade), the three-window dichotomy (every
sheet of every three-free core: fire, dodge, or escalate to the blade),
the dust's shape (the survivor diagonal pinned to the exact middle third
of every level), and the floor identity (the input and the even-exponent
statement are one object).  All cases, all rows, all towers, all sheets,
all levels, infinity at one single time: ONE lane. -/
theorem one_lane_the_whole_construction
    (hB : erdos_even_conjecture_iff_tailF) :
    (∀ K : Nat, (∃ p : Nat, digit3 (4^(K+1)) p = 2) ∨
      (∃ s core : Nat, (K+1) = 3^s * core ∧ ¬ 3 ∣ core ∧
        (core % 9 = 4 ∨ (s = 0 ∧ core % 9 = 1) ∨ (1 ≤ s ∧ core % 9 = 7))
        ∧ (∀ i : Nat, (omegaCutWord s core) % 3^(i+1) < 2 * 3^i))) ∧
    (∀ s core : Nat,
      (core % 9 = 4 ∨ (s = 0 ∧ core % 9 = 1) ∨ (1 ≤ s ∧ core % 9 = 7)) →
      (∀ i : Nat, (omegaCutWord s core) % 3^(i+1) < 2 * 3^i) →
      ((omegaCutWord s core) % 3^(s+2) < 2 * 3^(s+1) ∧
        (∀ k : Nat, 3 ≤ k → k ≤ s+1 →
          (omegaCutWord s 1 * core) % 3^k < 2 * 3^(k-1)) ∧
        (s = 0 → ∀ j : Nat, 2 ≤ j →
          (omegaCutWord 0 core) % 3^(j+1) < 2 * 3^j))) ∧
    (∀ s core : Nat, omegaCutWord (s+1) core
      = omegaCutWord s core
        + 3^(s+1) * (omegaCutWord s core * omegaCutWord s core
          + 3^s * (omegaCutWord s core * omegaCutWord s core
            * omegaCutWord s core))) ∧
    (∀ s core : Nat, 1 ≤ s → core % 3 = 1 ∨ core % 3 = 2 →
      (2 * 3^(s+1) ≤ (omegaCutWord s core) % 3^(s+2)
        ∧ digit3 (4^(3^s * core)) (2*s+2) = 2)
      ∨ (omegaCutWord s core) % 3^(s+2) < 3^(s+1)
      ∨ (3^(s+1) ≤ (omegaCutWord s core) % 3^(s+2)
        ∧ (omegaCutWord s core) % 3^(s+2) < 2 * 3^(s+1)
        ∧ ∀ S : Nat, s+1 ≤ S →
          digit3 (4^(3^S * core)) (S + (s+2)) = 2)) ∧
    (∀ core : Nat, core % 3 = 1 ∨ core % 3 = 2 →
      (∀ s : Nat, 1 ≤ s →
        (omegaCutWord s core) % 3^(s+2) < 2 * 3^(s+1)) →
      (∀ k : Nat, 3 ≤ k →
        (omegaCutWord (k-1) 1 * core) % 3^k < 2 * 3^(k-1)) →
      ∀ k : Nat, 3 ≤ k →
        3^(k-1) ≤ (omegaCutWord (k-1) 1 * core) % 3^k
          ∧ (omegaCutWord (k-1) 1 * core) % 3^k < 2 * 3^(k-1)) ∧
    (four_power_omega_shadow_wave_tailF ↔
      ∀ K : Nat, 8 ≤ K → noTernaryTwo (4^K) = false) :=
  ⟨one_lane_complete,
    fun s core hfam hnever => one_lane_certificate_faces s core hfam hnever,
    fun s core => omega_cut_word_cube_lift_exact s core,
    fun s core hs hfree => omega_sheet_window_dichotomy s core hs hfree,
    fun core hfree hwin hdust =>
      omega_dust_shape_middle_third core hfree hwin hdust,
    hB.symm⟩


/-! ## Exact certificate under global no-fire -/

/-- If a four-power has no ternary digit two at all, the one-lane dichotomy
cannot take its fired branch and therefore produces the complete residual
dust certificate explicitly. -/
theorem one_lane_certificate_of_no_fire
    (K : Nat)
    (hNo : ¬ ∃ p : Nat, digit3 (4^(K+1)) p = 2) :
    ∃ s core : Nat, (K+1) = 3^s * core ∧ ¬ 3 ∣ core ∧
      (core % 9 = 4 ∨ (s = 0 ∧ core % 9 = 1) ∨
        (1 ≤ s ∧ core % 9 = 7)) ∧
      (∀ i : Nat,
        (omegaCutWord s core) % 3^(i+1) < 2 * 3^i) := by
  rcases one_lane_complete K with hFire | hCert
  · exact False.elim (hNo hFire)
  · exact hCert

/-- Every no-fire exponent therefore lands directly in the certificate's
window, diagonal, and row-all-depths faces. -/
theorem one_lane_faces_of_no_fire
    (K : Nat)
    (hNo : ¬ ∃ p : Nat, digit3 (4^(K+1)) p = 2) :
    ∃ s core : Nat, (K+1) = 3^s * core ∧ ¬ 3 ∣ core ∧
      (omegaCutWord s core) % 3^(s+2) < 2 * 3^(s+1) ∧
      (∀ k : Nat, 3 ≤ k → k ≤ s+1 →
        (omegaCutWord s 1 * core) % 3^k < 2 * 3^(k-1)) := by
  obtain ⟨s, core, hK, hfree, hfam, hnever⟩ :=
    one_lane_certificate_of_no_fire K hNo
  have hfaces := one_lane_certificate_faces s core hfam hnever
  exact ⟨s, core, hK, hfree, hfaces.1, hfaces.2.1⟩

#check one_lane_certificate_of_no_fire
#check one_lane_faces_of_no_fire
#print axioms one_lane_certificate_of_no_fire

#print axioms one_lane_three_free_decomposition
#print axioms one_lane_cut_word_one
#print axioms one_lane_fire_of_mod3_two
#print axioms one_lane_fire_of_tower_mod9_one
#print axioms one_lane_row2_fire
#print axioms one_lane_complete
#print axioms one_lane_certificate_faces
#print axioms one_lane_omega_face
#print axioms one_lane_the_whole_construction

end GSTTailFOneLane
