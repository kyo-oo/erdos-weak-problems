import GSTGraphV2OmegaWaveLaw
import MonolithBoundary

set_option maxRecDepth 1000000
set_option maxHeartbeats 20000000

/-!
# THE 4TH DIMENSION — the tailF observation chamber

The separate arena for the second-observer input
`four_power_omega_shadow_wave_tailF`: the entire theorem machinery of the
route — the observation law, the descent blade, the diagonal ignition, the
uniform row and tower gates — assembled in ONE file, and pointed at the
input's own package.

What this chamber delivers, machine-certified:

* **THE EXTENDED OBSERVATION LAW** (`tower_observation_digit_two`): the
  row-axis reading of the Law, lifted from sheet zero to EVERY sheet level.
  Every tower digit of `4^(3^s * core)` at EVERY depth — no window bound,
  positions far beyond the observer law's `k ≤ s+1` window — is the cut
  word's own trit. The deep zone of the power, beyond the package's dodge
  band, is readable off `omegaCutWord s core` directly.
* **THE DESCENT BLADE** (§2, four theorems): the cut-word tower is one
  stabilizing 3-adic object; ONE primitive diagonal trit two kills the
  tower dodge at every level at once.
* **THE DIAGONAL IGNITION** (§3 + §3b, nineteen theorems): the firing
  bands as unconditional residue tests on the core — the first bands
  (levels two and three) and the deep bands (levels four and five), every
  band's domain reaching infinity: one residue test kills the whole tower
  from its level upward.
* **THE DECOMPOSITION** (§4): the input `four_power_omega_shadow_wave_tailF`
  is EXACTLY two named 3-adic trit statements — the row primitive (the
  sheet-zero family: the row word of every 3-free class-one core fires) and
  the tower primitive (the deep tail of every diagonal-dodging tower fires
  at depth beyond its own window). Both composition directions are
  machine-certified, and through the monolith's own terminal identity and
  crown, the two primitives carry the whole even-exponent statement.

The two named primitives are the carried content of the input — stated as
`def`s, consumed as hypotheses, disclosed at every surface. Everything
around them in this file is unconditional and axiom-audited.
-/

namespace GSTTailFFourthDimension

open GSTCanonicalSevenAxisBridge
open GSTFourPowerDirectResidue (lteCoeff lteCoeff_mod3_one
  pow4_three_power_lte_exact pow4_mod3_one pow4_scaled_mod_next)
open GSTGraphV2InfiniteControl
open GSTGraphV2HandwrittenOmegaUBlock
open GSTGraphV2InfiniteControllerBridge
open GST2DMixedEmergence
open GSTU2DEventTransport
open GSTGraphV2OmegaWaveLaw

/-! ## §1 The extended observation law — every tower digit, every depth

The uniform row law of the Law file reads the digits of `4^core` off the
row word `omegaCutWord 0 core` at every depth `j`. The cut-factor identity
`4^(3^s * core) = 1 + 3^(s+1) * omegaCutWord s core` holds at EVERY sheet
level `s`, and the prefix-slice law applies at every one of them: the
digit of the tower power at position `s+1+j` is the cut word's own trit at
`j`, with NO window bound. This is the observation law of the fourth
dimension: the deep digits — the positions the package's dodge band does
not even reach — are an open book. -/

/-- **THE EXTENDED OBSERVATION LAW.**  For every sheet level `s`, every
core, and EVERY depth `j`: whenever the cut word's own trit at depth `j`
sits in the top third of its residue window modulo `3^(j+1)`, the tower
power `4^(3^s * core)` owns its ternary digit two at position `s+1+j`.
No window bound: the reading works at every depth of the power. -/
theorem tower_observation_digit_two (s core j : Nat)
    (hkill : 2 * 3^j ≤ (omegaCutWord s core) % 3^(j+1)) :
    digit3 (4^(3^s * core)) (s+1+j) = 2 := by
  have h1 : (1:Nat) < 3^(s+1) := by
    have h3 : (3:Nat)^1 ≤ 3^(s+1) := by
      simpa using Nat.pow_le_pow_of_le (by decide : 1 < (3:Nat))
        (by omega : 1 ≤ s+1)
    omega
  have hslice := prefix_slice_digit_exact (s+1) 1 (omegaCutWord s core) j h1
  have hf : 4^(3^s * core) = 1 + 3^(s+1) * omegaCutWord s core :=
    omega_cut_factor s core
  rw [show s+1+j = (s+1)+j from by omega, hf, hslice]
  unfold digit3
  rw [digit3_window]
  have hpos : 0 < 3^j := Nat.pow_pos (by decide)
  have hlt : (omegaCutWord s core) % 3^(j+1) < 3^(j+1) :=
    Nat.mod_lt _ (Nat.pow_pos (by decide))
  have hpow : 3^(j+1) = 3 * 3^j := by
    rw [Nat.pow_add, Nat.pow_one]
    ring
  rw [hpow] at hlt
  obtain ⟨d, hd⟩ : ∃ d, (omegaCutWord s core) % 3^(j+1) = 2 * 3^j + d :=
    ⟨(omegaCutWord s core) % 3^(j+1) - 2 * 3^j, by omega⟩
  have hdlt : d < 3^j := by omega
  rw [hd, Nat.add_comm, show 2 * 3^j = 3^j * 2 from by ring,
    Nat.add_mul_div_left _ _ hpos, Nat.div_eq_of_lt hdlt]

/-! ## §2 The descent blade — the non-local argument

The cut-word tower is one stabilizing 3-adic object: the cube-lift identity
freezes every window below the lift, every tower window descends to the
primitive level, and ONE primitive diagonal trit two kills the tower dodge
at EVERY sheet level at once. -/

/-- **THE CUBE-LIFT STABILIZATION.**  The cut word of sheet level `s+1` is
the cut word of level `s` plus a multiple of `3^(s+1)`: every trit below
position `s+1` is frozen as the sheet level grows. -/
theorem omega_cut_word_stabilizes (s core : Nat) :
    ∃ t : Nat, omegaCutWord (s+1) core
      = omegaCutWord s core + 3^(s+1) * t := by
  have hf0 := omega_cut_factor s core
  have hf1 := omega_cut_factor (s+1) core
  have hpow : 4^(3^(s+1) * core) = (4^(3^s * core))^3 := by
    rw [show 3^(s+1) * core = (3^s * core) * 3 from by
          rw [Nat.pow_succ]; ring,
        Nat.pow_mul]
  have hcube : (1 + 3^(s+1) * omegaCutWord s core)^3
      = 1 + 3^(s+2) * (omegaCutWord s core
          + 3^(s+1) * (omegaCutWord s core * omegaCutWord s core
            + 3^s * (omegaCutWord s core * omegaCutWord s core
              * omegaCutWord s core))) := by
    rw [show 3^(s+2) = 9 * 3^s from by
          rw [show s+2 = (s+1)+1 from by omega, Nat.pow_succ, Nat.pow_succ]
          ring,
        show 3^(s+1) = 3 * 3^s from by rw [Nat.pow_succ]; ring]
    ring
  have hE : 4^(3^(s+1) * core)
      = 1 + 3^(s+2) * (omegaCutWord s core
          + 3^(s+1) * (omegaCutWord s core * omegaCutWord s core
            + 3^s * (omegaCutWord s core * omegaCutWord s core
              * omegaCutWord s core))) := by
    rw [hpow, hf0]
    exact hcube
  have hAB : 3^(s+2) * omegaCutWord (s+1) core
      = 3^(s+2) * (omegaCutWord s core
          + 3^(s+1) * (omegaCutWord s core * omegaCutWord s core
            + 3^s * (omegaCutWord s core * omegaCutWord s core
              * omegaCutWord s core))) :=
    Nat.add_left_cancel (hf1.symm.trans hE)
  refine ⟨omegaCutWord s core * omegaCutWord s core
      + 3^s * (omegaCutWord s core * omegaCutWord s core
        * omegaCutWord s core), ?_⟩
  exact Nat.eq_of_mul_eq_mul_left (Nat.pow_pos (by decide)) hAB

/-- **THE FROZEN WINDOW.**  For every tower level `k ≤ s+1`, the level-`s`
and level-`s+1` tower words agree modulo `3^k`. -/
theorem omega_tower_word_mod_stable (s core k : Nat) (hk : k ≤ s+1) :
    (omegaCutWord (s+1) 1 * core) % 3^k
      = (omegaCutWord s 1 * core) % 3^k := by
  obtain ⟨t, ht⟩ := omega_cut_word_stabilizes s 1
  have hsplit : 3^(s+1) = 3^k * 3^(s+1-k) := by
    rw [← Nat.pow_add]
    congr 1
    omega
  have hz : 3^(s+1) * (t * core) % 3^k = 0 := by
    refine Nat.mod_eq_zero_of_dvd ⟨3^(s+1-k) * (t * core), ?_⟩
    rw [hsplit]
    ring
  have hdistr : (omegaCutWord s 1 + 3^(s+1) * t) * core
      = omegaCutWord s 1 * core + 3^(s+1) * (t * core) := by
    ring
  rw [ht, hdistr, Nat.add_mod, hz, Nat.add_zero, Nat.mod_mod]

/-- **THE DESCENT TO THE PRIMITIVE.**  For every sheet level `s` at or
above `k-1`, the tower word at modulus `3^k` is the primitive
level-`(k-1)` word at modulus `3^k`. -/
theorem omega_tower_word_mod_chain (core k : Nat) :
    ∀ s : Nat, k-1 ≤ s → (omegaCutWord s 1 * core) % 3^k
      = (omegaCutWord (k-1) 1 * core) % 3^k := by
  intro s
  induction s with
  | zero =>
    intro hsk
    rw [show k-1 = 0 from by omega]
  | succ s ih =>
    intro hsk
    rcases Nat.lt_or_ge k (s+2) with hlt | hge
    · rw [omega_tower_word_mod_stable s core k (by omega), ih (by omega)]
    · rw [show k-1 = s+1 from by omega]

/-- **THE DIAGONAL KILL — the descent blade, drawn.**  One ternary digit
two on the primitive diagonal at level `k-1` kills the tower dodge at
EVERY sheet level `S ≥ k-1` at once. -/
theorem omega_tower_kill_of_diagonal_two (core k S : Nat)
    (hk1 : 1 ≤ k) (hkS : k ≤ S+1)
    (hTwo : digit3 (4^(3^(k-1) * core)) (2*k - 1) = 2) :
    digit3 (4^(3^S * core)) (S + k) = 2 := by
  have hobs := omega_observed_digit (k-1) core k (by omega) (by omega)
  rw [show (k-1) + k = 2*k - 1 from by omega] at hobs
  rw [hobs] at hTwo
  rw [omega_observed_digit S core k (by omega) hkS,
      omega_tower_word_mod_chain core k S (by omega)]
  exact hTwo

/-! ## §3 The diagonal ignition — the first firing bands

The descent blade transmits ONE primitive diagonal trit two to every tower
level at once. The ignition laws read the diagonal at its first two
indices as explicit residue conditions on the core. -/

/-- **THE CLASS-ONE IGNITION.**  Every class-one core — `core ≡ 1 (mod 9)`
— fires the primitive diagonal at index two: the level-one tower word is
`7`, and `7 * core ≡ 7 (mod 9)` sits in the top third. -/
theorem omega_diagonal_two_of_mod_nine_one (core : Nat) (h : core % 9 = 1) :
    digit3 (4^(3^(2-1) * core)) (2*2 - 1) = 2 := by
  have hw : omegaCutWord 1 1 = 7 := by
    have h2 := omega_cut_factor 1 1
    norm_num [Nat.pow_succ, Nat.pow_zero] at h2
    omega
  have hobs := omega_observed_digit 1 core 2 (by decide) (by decide)
  rw [hw] at hobs
  have hev : (7 * core) % 3^2 / 3^(2-1) = 2 := by
    have h9 : (3:Nat)^2 = 9 := by norm_num
    have h3 : (3:Nat)^(2-1) = 3 := by norm_num
    rw [h9, h3]
    omega
  exact hobs.trans hev

/-- **THE MOD-27 THIRTEEN IGNITION.**  Every core `≡ 13 (mod 27)` — the
class-four band's first firing subclass — fires the primitive diagonal at
index three: the level-two tower word is `9709 ≡ 16 (mod 27)`, and
`16 * 13 ≡ 19 (mod 27)` lands in the top third. -/
theorem omega_diagonal_two_of_mod27_thirteen (core : Nat)
    (h : core % 27 = 13) :
    digit3 (4^(3^(3-1) * core)) (2*3 - 1) = 2 := by
  have hw : omegaCutWord 2 1 = 9709 := by
    have h2 := omega_cut_factor 2 1
    norm_num [Nat.pow_succ, Nat.pow_zero] at h2
    omega
  have hobs := omega_observed_digit 2 core 3 (by decide) (by decide)
  rw [hw] at hobs
  have hev : (9709 * core) % 3^3 / 3^(3-1) = 2 := by
    have h27 : (3:Nat)^3 = 27 := by norm_num
    have h9 : (3:Nat)^(3-1) = 9 := by norm_num
    rw [h27, h9]
    omega
  exact hobs.trans hev

/-- **THE MOD-27 TWENTY-FIVE IGNITION.**  Every core `≡ 25 (mod 27)` — the
class-seven band's first firing subclass — fires the primitive diagonal at
index three: `16 * 25 ≡ 22 (mod 27)` lands in the top third. -/
theorem omega_diagonal_two_of_mod27_twentyfive (core : Nat)
    (h : core % 27 = 25) :
    digit3 (4^(3^(3-1) * core)) (2*3 - 1) = 2 := by
  have hw : omegaCutWord 2 1 = 9709 := by
    have h2 := omega_cut_factor 2 1
    norm_num [Nat.pow_succ, Nat.pow_zero] at h2
    omega
  have hobs := omega_observed_digit 2 core 3 (by decide) (by decide)
  rw [hw] at hobs
  have hev : (9709 * core) % 3^3 / 3^(3-1) = 2 := by
    have h27 : (3:Nat)^3 = 27 := by norm_num
    have h9 : (3:Nat)^(3-1) = 9 := by norm_num
    rw [h27, h9]
    omega
  exact hobs.trans hev

/-- **THE CLASS-ONE TOWER KILL.**  One residue test on the core
(`core ≡ 1 (mod 9)`) and the entire tower dies at every level `S ≥ 1`. -/
theorem omega_tower_digit_two_of_mod_nine_one (core : Nat)
    (h : core % 9 = 1) :
    ∀ S : Nat, 1 ≤ S → digit3 (4^(3^S * core)) (S + 2) = 2 := by
  intro S hS
  exact omega_tower_kill_of_diagonal_two core 2 S (by decide) (by omega)
    (omega_diagonal_two_of_mod_nine_one core h)

/-- **THE MOD-27 BAND TOWER KILL.**  Every core in the mod-27 firing band
(`13` or `25`) kills its whole tower from level two upward. -/
theorem omega_tower_digit_two_of_mod27_band (core : Nat)
    (h : core % 27 = 13 ∨ core % 27 = 25) :
    ∀ S : Nat, 2 ≤ S → digit3 (4^(3^S * core)) (S + 3) = 2 := by
  intro S hS
  rcases h with h13 | h25
  · exact omega_tower_kill_of_diagonal_two core 3 S (by decide) (by omega)
      (omega_diagonal_two_of_mod27_thirteen core h13)
  · exact omega_tower_kill_of_diagonal_two core 3 S (by decide) (by omega)
      (omega_diagonal_two_of_mod27_twentyfive core h25)

/-! ## §3b The deep ignition — levels four and five, domains to infinity

The ignition machinery of §3 reads the primitive diagonal at ANY index,
not only the first two: the level-three tower word is
`222399981598543 ≡ 16 (mod 81)`, the level-four tower word is
`24057640120673299065081231814259802792690247621 ≡ 178 (mod 243)` — each
a fixed certificate of the same stabilized Ω-word — and every hard-family
residue class whose product with the word lands in the top third of its
window fires the diagonal at that index. The descent blade then kills the
WHOLE tower of that class from the level upward: the class's domain
reaches infinity in one residue test.

Level four fires the four classes `4, 34, 49, 70 (mod 81)`; level five
fires the eight classes `16, 31, 61, 76, 124, 139, 169, 184 (mod 243)`.
Twelve hard-family classes die wholesale here — on top of the two of §3 —
and the survivor measure of the hard family shrinks from the eight
mod-81 classes to sixteen mod-243 classes: exactly one third of each
level's survivors fire, the Cantor arithmetic of the dodge set, now
formalized two levels deeper than the chamber's first ignition. -/

/-- **THE MOD-81 FOUR IGNITION.**  Every core `≡ 4 (mod 81)` — the
class-four band's second firing subclass — fires the primitive diagonal
at index four: the level-three tower word is `222399981598543 ≡ 16
(mod 81)`, and `16 * 4 ≡ 64 (mod 81)` lands in the top third. -/
theorem omega_diagonal_two_of_mod81_four (core : Nat)
    (h : core % 81 = 4) :
    digit3 (4^(3^(4-1) * core)) (2*4 - 1) = 2 := by
  have hw : omegaCutWord 3 1 = 222399981598543 := by
    have h2 := omega_cut_factor 3 1
    norm_num [Nat.pow_succ, Nat.pow_zero] at h2
    omega
  have hobs := omega_observed_digit 3 core 4 (by decide) (by decide)
  rw [hw] at hobs
  have hev : (222399981598543 * core) % 3^4 / 3^(4-1) = 2 := by
    have h81 : (3:Nat)^4 = 81 := by norm_num
    have h27 : (3:Nat)^(4-1) = 27 := by norm_num
    rw [h81, h27]
    omega
  exact hobs.trans hev

/-- **THE MOD-81 THIRTY-FOUR IGNITION.**  Every core `≡ 34 (mod 81)` fires
the primitive diagonal at index four: `16 * 34 ≡ 58 (mod 81)` lands in
the top third. -/
theorem omega_diagonal_two_of_mod81_thirtyfour (core : Nat)
    (h : core % 81 = 34) :
    digit3 (4^(3^(4-1) * core)) (2*4 - 1) = 2 := by
  have hw : omegaCutWord 3 1 = 222399981598543 := by
    have h2 := omega_cut_factor 3 1
    norm_num [Nat.pow_succ, Nat.pow_zero] at h2
    omega
  have hobs := omega_observed_digit 3 core 4 (by decide) (by decide)
  rw [hw] at hobs
  have hev : (222399981598543 * core) % 3^4 / 3^(4-1) = 2 := by
    have h81 : (3:Nat)^4 = 81 := by norm_num
    have h27 : (3:Nat)^(4-1) = 27 := by norm_num
    rw [h81, h27]
    omega
  exact hobs.trans hev

/-- **THE MOD-81 FORTY-NINE IGNITION.**  Every core `≡ 49 (mod 81)` fires
the primitive diagonal at index four: `16 * 49 ≡ 55 (mod 81)` lands in
the top third. -/
theorem omega_diagonal_two_of_mod81_fortynine (core : Nat)
    (h : core % 81 = 49) :
    digit3 (4^(3^(4-1) * core)) (2*4 - 1) = 2 := by
  have hw : omegaCutWord 3 1 = 222399981598543 := by
    have h2 := omega_cut_factor 3 1
    norm_num [Nat.pow_succ, Nat.pow_zero] at h2
    omega
  have hobs := omega_observed_digit 3 core 4 (by decide) (by decide)
  rw [hw] at hobs
  have hev : (222399981598543 * core) % 3^4 / 3^(4-1) = 2 := by
    have h81 : (3:Nat)^4 = 81 := by norm_num
    have h27 : (3:Nat)^(4-1) = 27 := by norm_num
    rw [h81, h27]
    omega
  exact hobs.trans hev

/-- **THE MOD-81 SEVENTY IGNITION.**  Every core `≡ 70 (mod 81)` fires the
primitive diagonal at index four: `16 * 70 ≡ 67 (mod 81)` lands in the
top third. -/
theorem omega_diagonal_two_of_mod81_seventy (core : Nat)
    (h : core % 81 = 70) :
    digit3 (4^(3^(4-1) * core)) (2*4 - 1) = 2 := by
  have hw : omegaCutWord 3 1 = 222399981598543 := by
    have h2 := omega_cut_factor 3 1
    norm_num [Nat.pow_succ, Nat.pow_zero] at h2
    omega
  have hobs := omega_observed_digit 3 core 4 (by decide) (by decide)
  rw [hw] at hobs
  have hev : (222399981598543 * core) % 3^4 / 3^(4-1) = 2 := by
    have h81 : (3:Nat)^4 = 81 := by norm_num
    have h27 : (3:Nat)^(4-1) = 27 := by norm_num
    rw [h81, h27]
    omega
  exact hobs.trans hev

/-- **THE MOD-243 SIXTEEN IGNITION.**  Every core `≡ 16 (mod 243)` fires
the primitive diagonal at index five: the level-four tower word is
`24057640120673299065081231814259802792690247621 ≡ 178 (mod 243)`, and
`178 * 16 ≡ 175 (mod 243)` lands in the top third. -/
theorem omega_diagonal_two_of_mod243_sixteen (core : Nat)
    (h : core % 243 = 16) :
    digit3 (4^(3^(5-1) * core)) (2*5 - 1) = 2 := by
  have hw : omegaCutWord 4 1 =
      24057640120673299065081231814259802792690247621 := by
    have h2 := omega_cut_factor 4 1
    norm_num [Nat.pow_succ, Nat.pow_zero] at h2
    omega
  have hobs := omega_observed_digit 4 core 5 (by decide) (by decide)
  rw [hw] at hobs
  have hev : (24057640120673299065081231814259802792690247621 * core) %
      3^5 / 3^(5-1) = 2 := by
    have h243 : (3:Nat)^5 = 243 := by norm_num
    have h81 : (3:Nat)^(5-1) = 81 := by norm_num
    rw [h243, h81]
    omega
  exact hobs.trans hev

/-- **THE MOD-243 THIRTY-ONE IGNITION.**  Every core `≡ 31 (mod 243)`
fires the primitive diagonal at index five: `178 * 31 ≡ 172 (mod 243)`
lands in the top third. -/
theorem omega_diagonal_two_of_mod243_thirtyone (core : Nat)
    (h : core % 243 = 31) :
    digit3 (4^(3^(5-1) * core)) (2*5 - 1) = 2 := by
  have hw : omegaCutWord 4 1 =
      24057640120673299065081231814259802792690247621 := by
    have h2 := omega_cut_factor 4 1
    norm_num [Nat.pow_succ, Nat.pow_zero] at h2
    omega
  have hobs := omega_observed_digit 4 core 5 (by decide) (by decide)
  rw [hw] at hobs
  have hev : (24057640120673299065081231814259802792690247621 * core) %
      3^5 / 3^(5-1) = 2 := by
    have h243 : (3:Nat)^5 = 243 := by norm_num
    have h81 : (3:Nat)^(5-1) = 81 := by norm_num
    rw [h243, h81]
    omega
  exact hobs.trans hev

/-- **THE MOD-243 SIXTY-ONE IGNITION.**  Every core `≡ 61 (mod 243)` fires
the primitive diagonal at index five: `178 * 61 ≡ 166 (mod 243)` lands in
the top third. -/
theorem omega_diagonal_two_of_mod243_sixtyone (core : Nat)
    (h : core % 243 = 61) :
    digit3 (4^(3^(5-1) * core)) (2*5 - 1) = 2 := by
  have hw : omegaCutWord 4 1 =
      24057640120673299065081231814259802792690247621 := by
    have h2 := omega_cut_factor 4 1
    norm_num [Nat.pow_succ, Nat.pow_zero] at h2
    omega
  have hobs := omega_observed_digit 4 core 5 (by decide) (by decide)
  rw [hw] at hobs
  have hev : (24057640120673299065081231814259802792690247621 * core) %
      3^5 / 3^(5-1) = 2 := by
    have h243 : (3:Nat)^5 = 243 := by norm_num
    have h81 : (3:Nat)^(5-1) = 81 := by norm_num
    rw [h243, h81]
    omega
  exact hobs.trans hev

/-- **THE MOD-243 SEVENTY-SIX IGNITION.**  Every core `≡ 76 (mod 243)`
fires the primitive diagonal at index five: `178 * 76 ≡ 163 (mod 243)`
lands in the top third. -/
theorem omega_diagonal_two_of_mod243_seventysix (core : Nat)
    (h : core % 243 = 76) :
    digit3 (4^(3^(5-1) * core)) (2*5 - 1) = 2 := by
  have hw : omegaCutWord 4 1 =
      24057640120673299065081231814259802792690247621 := by
    have h2 := omega_cut_factor 4 1
    norm_num [Nat.pow_succ, Nat.pow_zero] at h2
    omega
  have hobs := omega_observed_digit 4 core 5 (by decide) (by decide)
  rw [hw] at hobs
  have hev : (24057640120673299065081231814259802792690247621 * core) %
      3^5 / 3^(5-1) = 2 := by
    have h243 : (3:Nat)^5 = 243 := by norm_num
    have h81 : (3:Nat)^(5-1) = 81 := by norm_num
    rw [h243, h81]
    omega
  exact hobs.trans hev

/-- **THE MOD-243 ONE HUNDRED TWENTY-FOUR IGNITION.**  Every core
`≡ 124 (mod 243)` fires the primitive diagonal at index five:
`178 * 124 ≡ 202 (mod 243)` lands in the top third. -/
theorem omega_diagonal_two_of_mod243_onehundredtwentyfour (core : Nat)
    (h : core % 243 = 124) :
    digit3 (4^(3^(5-1) * core)) (2*5 - 1) = 2 := by
  have hw : omegaCutWord 4 1 =
      24057640120673299065081231814259802792690247621 := by
    have h2 := omega_cut_factor 4 1
    norm_num [Nat.pow_succ, Nat.pow_zero] at h2
    omega
  have hobs := omega_observed_digit 4 core 5 (by decide) (by decide)
  rw [hw] at hobs
  have hev : (24057640120673299065081231814259802792690247621 * core) %
      3^5 / 3^(5-1) = 2 := by
    have h243 : (3:Nat)^5 = 243 := by norm_num
    have h81 : (3:Nat)^(5-1) = 81 := by norm_num
    rw [h243, h81]
    omega
  exact hobs.trans hev

/-- **THE MOD-243 ONE HUNDRED THIRTY-NINE IGNITION.**  Every core
`≡ 139 (mod 243)` fires the primitive diagonal at index five:
`178 * 139 ≡ 199 (mod 243)` lands in the top third. -/
theorem omega_diagonal_two_of_mod243_onehundredthirtynine (core : Nat)
    (h : core % 243 = 139) :
    digit3 (4^(3^(5-1) * core)) (2*5 - 1) = 2 := by
  have hw : omegaCutWord 4 1 =
      24057640120673299065081231814259802792690247621 := by
    have h2 := omega_cut_factor 4 1
    norm_num [Nat.pow_succ, Nat.pow_zero] at h2
    omega
  have hobs := omega_observed_digit 4 core 5 (by decide) (by decide)
  rw [hw] at hobs
  have hev : (24057640120673299065081231814259802792690247621 * core) %
      3^5 / 3^(5-1) = 2 := by
    have h243 : (3:Nat)^5 = 243 := by norm_num
    have h81 : (3:Nat)^(5-1) = 81 := by norm_num
    rw [h243, h81]
    omega
  exact hobs.trans hev

/-- **THE MOD-243 ONE HUNDRED SIXTY-NINE IGNITION.**  Every core
`≡ 169 (mod 243)` fires the primitive diagonal at index five:
`178 * 169 ≡ 193 (mod 243)` lands in the top third. -/
theorem omega_diagonal_two_of_mod243_onehundredsixtynine (core : Nat)
    (h : core % 243 = 169) :
    digit3 (4^(3^(5-1) * core)) (2*5 - 1) = 2 := by
  have hw : omegaCutWord 4 1 =
      24057640120673299065081231814259802792690247621 := by
    have h2 := omega_cut_factor 4 1
    norm_num [Nat.pow_succ, Nat.pow_zero] at h2
    omega
  have hobs := omega_observed_digit 4 core 5 (by decide) (by decide)
  rw [hw] at hobs
  have hev : (24057640120673299065081231814259802792690247621 * core) %
      3^5 / 3^(5-1) = 2 := by
    have h243 : (3:Nat)^5 = 243 := by norm_num
    have h81 : (3:Nat)^(5-1) = 81 := by norm_num
    rw [h243, h81]
    omega
  exact hobs.trans hev

/-- **THE MOD-243 ONE HUNDRED EIGHTY-FOUR IGNITION.**  Every core
`≡ 184 (mod 243)` fires the primitive diagonal at index five:
`178 * 184 ≡ 190 (mod 243)` lands in the top third. -/
theorem omega_diagonal_two_of_mod243_onehundredeightyfour (core : Nat)
    (h : core % 243 = 184) :
    digit3 (4^(3^(5-1) * core)) (2*5 - 1) = 2 := by
  have hw : omegaCutWord 4 1 =
      24057640120673299065081231814259802792690247621 := by
    have h2 := omega_cut_factor 4 1
    norm_num [Nat.pow_succ, Nat.pow_zero] at h2
    omega
  have hobs := omega_observed_digit 4 core 5 (by decide) (by decide)
  rw [hw] at hobs
  have hev : (24057640120673299065081231814259802792690247621 * core) %
      3^5 / 3^(5-1) = 2 := by
    have h243 : (3:Nat)^5 = 243 := by norm_num
    have h81 : (3:Nat)^(5-1) = 81 := by norm_num
    rw [h243, h81]
    omega
  exact hobs.trans hev

/-- **THE MOD-81 BAND TOWER KILL.**  Every core in the mod-81 firing band
(`4`, `34`, `49` or `70`) kills its whole tower from level three upward. -/
theorem omega_tower_digit_two_of_mod81_band (core : Nat)
    (h : core % 81 = 4 ∨ core % 81 = 34 ∨ core % 81 = 49 ∨ core % 81 = 70) :
    ∀ S : Nat, 3 ≤ S → digit3 (4^(3^S * core)) (S + 4) = 2 := by
  intro S hS
  rcases h with h4 | h34 | h49 | h70
  · exact omega_tower_kill_of_diagonal_two core 4 S (by decide) (by omega)
      (omega_diagonal_two_of_mod81_four core h4)
  · exact omega_tower_kill_of_diagonal_two core 4 S (by decide) (by omega)
      (omega_diagonal_two_of_mod81_thirtyfour core h34)
  · exact omega_tower_kill_of_diagonal_two core 4 S (by decide) (by omega)
      (omega_diagonal_two_of_mod81_fortynine core h49)
  · exact omega_tower_kill_of_diagonal_two core 4 S (by decide) (by omega)
      (omega_diagonal_two_of_mod81_seventy core h70)

/-- **THE MOD-243 BAND TOWER KILL.**  Every core in the mod-243 firing band
(`16`, `31`, `61`, `76`, `124`, `139`, `169` or `184`) kills its whole
tower from level four upward. -/
theorem omega_tower_digit_two_of_mod243_band (core : Nat)
    (h : core % 243 = 16 ∨ core % 243 = 31 ∨ core % 243 = 61 ∨
      core % 243 = 76 ∨ core % 243 = 124 ∨ core % 243 = 139 ∨
      core % 243 = 169 ∨ core % 243 = 184) :
    ∀ S : Nat, 4 ≤ S → digit3 (4^(3^S * core)) (S + 5) = 2 := by
  intro S hS
  rcases h with h16 | h31 | h61 | h76 | h124 | h139 | h169 | h184
  · exact omega_tower_kill_of_diagonal_two core 5 S (by decide) (by omega)
      (omega_diagonal_two_of_mod243_sixteen core h16)
  · exact omega_tower_kill_of_diagonal_two core 5 S (by decide) (by omega)
      (omega_diagonal_two_of_mod243_thirtyone core h31)
  · exact omega_tower_kill_of_diagonal_two core 5 S (by decide) (by omega)
      (omega_diagonal_two_of_mod243_sixtyone core h61)
  · exact omega_tower_kill_of_diagonal_two core 5 S (by decide) (by omega)
      (omega_diagonal_two_of_mod243_seventysix core h76)
  · exact omega_tower_kill_of_diagonal_two core 5 S (by decide) (by omega)
      (omega_diagonal_two_of_mod243_onehundredtwentyfour core h124)
  · exact omega_tower_kill_of_diagonal_two core 5 S (by decide) (by omega)
      (omega_diagonal_two_of_mod243_onehundredthirtynine core h139)
  · exact omega_tower_kill_of_diagonal_two core 5 S (by decide) (by omega)
      (omega_diagonal_two_of_mod243_onehundredsixtynine core h169)
  · exact omega_tower_kill_of_diagonal_two core 5 S (by decide) (by omega)
      (omega_diagonal_two_of_mod243_onehundredeightyfour core h184)

/-! ## §4 The two named primitives — the decomposition of the input

The input `four_power_omega_shadow_wave_tailF` says: every exponent above
the kernel base that carries the full shadow package owns a ternary digit
two. The package's own witness decomposition `K = 3^s * core` splits the
input into exactly two families, and each family compresses to ONE named
3-adic trit statement:

* the **ROW primitive** — the sheet-zero family (`s = 0`): the row word of
  every 3-free class-one core above the base fires its top third at some
  depth;
* the **TOWER primitive** — the tower family (`s ≥ 1`): the deep tail of
  the cut word — beyond the package's own dodge band, at depth `≥ s+2` —
  fires its top third at some depth.

These two statements are the whole carried content of the input: composed,
they deliver the input outright, and through the monolith's terminal
identity and crown they deliver the even-exponent statement itself. -/

/-- **THE ROW PRIMITIVE** — the sheet-zero family's entire carried content,
as one named 3-adic trit statement: the row word of every 3-free class-one
core above the kernel base owns its top-third fire at some depth. -/
def tailF_row_primitive : Prop :=
  ∀ core : Nat, 500 < core → ¬ 3 ∣ core →
    (core % 9 = 1 ∨ core % 9 = 4) →
      ∃ j : Nat, 2 * 3^j ≤ (omegaCutWord 0 core) % 3^(j+1)

/-- **THE TOWER PRIMITIVE** — the tower family's entire carried content, as
one named 3-adic trit statement: every diagonal-dodging tower's cut word
fires its top third in its deep tail, at depth at least `s+2` — beyond the
package's own dodge band. -/
def tailF_tower_primitive : Prop :=
  ∀ s core : Nat, 1 ≤ s → ¬ 3 ∣ core →
    (core % 9 = 4 ∨ core % 9 = 7) →
    (∀ k : Nat, 3 ≤ k → k ≤ s+1 →
      (omegaCutWord s 1 * core) % 3^k < 2 * 3^(k-1)) →
      ∃ i : Nat, s+2 ≤ i ∧
        2 * 3^i ≤ (omegaCutWord s core) % 3^(i+1)

/-- **THE DECOMPOSITION OF THE INPUT.**  The two named primitives compose
into the full second-observer input: the row primitive carries the
sheet-zero family through the uniform row law, the tower primitive
carries the tower family through the extended observation law of §1. -/
theorem tailF_of_row_and_tower
    (hRow : tailF_row_primitive)
    (hTower : tailF_tower_primitive) :
    four_power_omega_shadow_wave_tailF := by
  intro K hK hshadow
  obtain ⟨s, core, hKsc, hfree, hres, hA, hB1, hB2, hC, hD⟩ := hshadow
  rcases Nat.eq_zero_or_pos s with rfl | hs1
  · -- Sheet-zero family: the row primitive fires the row word, the
    -- uniform row law converts the fire into the power's digit two.
    have hc14 : core % 9 = 1 ∨ core % 9 = 4 := by
      rcases hres with h4 | ⟨_, h1⟩ | ⟨h1s, h7⟩
      · exact Or.inr h4
      · exact Or.inl h1
      · exact absurd h1s (by omega)
    rw [Nat.pow_zero, Nat.one_mul] at hKsc
    have hKc : 500 < core := by
      rw [← hKsc]
      exact hK
    obtain ⟨j, hj⟩ := hRow core hKc hfree hc14
    refine ⟨1+j, ?_⟩
    rw [hKsc]
    exact omega_row_level_digit_two core j hj
  · -- Tower family: the tower primitive fires the deep tail of the cut
    -- word, the extended observation law converts the fire into the
    -- power's digit two at a position beyond the dodge band.
    have hc47 : core % 9 = 4 ∨ core % 9 = 7 := by
      rcases hres with h4 | ⟨hs0, h1⟩ | ⟨hs1', h7⟩
      · exact Or.inl h4
      · exact absurd hs0 (by omega)
      · exact Or.inr h7
    obtain ⟨i, _, hfire⟩ := hTower s core hs1 hfree hc47 hD
    refine ⟨s+1+i, ?_⟩
    rw [hKsc]
    exact tower_observation_digit_two s core i hfire

/-- **THE EVEN-EXPONENT STATEMENT FROM THE TWO PRIMITIVES** — through the
monolith's own terminal identity (taken here as the explicit boundary
input `hB`, proven in `kyo-oo/erdosternary2` §7.15), the two named
primitives carry the whole even-exponent statement. -/
theorem even_conjecture_of_row_and_tower
    (hB : erdos_even_conjecture_iff_tailF)
    (hRow : tailF_row_primitive)
    (hTower : tailF_tower_primitive) :
    ∀ K : Nat, 8 ≤ K → noTernaryTwo (4^K) = false :=
  hB.mpr
    (tailF_of_row_and_tower hRow hTower)

/-- **THE CROWN FROM THE TWO PRIMITIVES** — the monolith's own universal
theorem, with the input slot filled by the decomposition: the two named
3-adic trit statements carry the universal. -/
theorem erdos_ternary_2_universal_of_row_and_tower
    (hB : erdos_ternary_2_universal_of_tailF)
    (hRow : tailF_row_primitive)
    (hTower : tailF_tower_primitive)
    (n : Nat) (hn : 9 ≤ n) :
    noTernaryTwo (2^n) = false :=
  hB
    (tailF_of_row_and_tower hRow hTower) n hn

/-! ## §5 The combinations applied — the package's own bands die

The blade and the ignition, pointed at the input's own package: for the
mod-27 firing band, the package's tower-dodge clause is dead on arrival —
the diagonal fires inside the clause's own window, so no package witness
at sheet level two or beyond can carry a band core. This is the machinery
of §§1-3 consuming the package from the fourth dimension. -/

/-- **THE BAND DODGE IS DEAD.**  For every sheet level `s ≥ 2` and every
core in the mod-27 firing band (`13` or `25` mod 27), the tower-dodge
clause of the shadow package FAILS at `k = 3`: the stabilized tower word
fires its top third inside the clause's own window. No package witness at
level two or beyond carries a band core. -/
theorem tower_dodge_dead_of_mod27_band (s core : Nat) (hs : 2 ≤ s)
    (h : core % 27 = 13 ∨ core % 27 = 25) :
    ¬ (∀ k : Nat, 3 ≤ k → k ≤ s+1 →
      (omegaCutWord s 1 * core) % 3^k < 2 * 3^(k-1)) := by
  intro hD
  have hkill : digit3 (4^(3^s * core)) (s + 3) = 2 := by
    rcases h with h13 | h25
    · exact omega_tower_kill_of_diagonal_two core 3 s (by decide) (by omega)
        (omega_diagonal_two_of_mod27_thirteen core h13)
    · exact omega_tower_kill_of_diagonal_two core 3 s (by decide) (by omega)
        (omega_diagonal_two_of_mod27_twentyfive core h25)
  rw [omega_observed_digit s core 3 (by decide) (by omega)] at hkill
  have hdodge := hD 3 (by omega) (by omega)
  have h27 : (3:Nat)^3 = 27 := by norm_num
  have h9 : (3:Nat)^(3-1) = 9 := by norm_num
  rw [h27, h9] at hkill hdodge
  omega

/-! ## §6 The row lattice — the sheet-zero residual, fired three levels deep

The row half of the carried input, attacked directly on the powers.  The
hard family of the sheet-zero decomposition is `core % 9 ∈ {1, 4}` (3-free,
above the kernel base); the residue class of the core modulo `3^m` pins the
ternary digits of `4 ^ core` up to position `m` through the cycle laws —
the monolith's own `four_pow_mod81` at level 27, and the two new cycle laws
of this section at levels 81 and 243.  Three lattice levels, thirteen fired
classes:

* level 27, digit position 3: classes `19` and `22` mod 27 —
  `4 ^ core % 81 = 58` and `67`;
* level 81, digit position 4: classes `55, 58, 64, 67` mod 81 —
  `4 ^ core % 243 = 166, 175, 193, 202`;
* level 243, digit position 5: classes `85, 91, 112, 163, 175, 190, 202`
  mod 243 — `4 ^ core % 729 = 499, 517, 580, 490, 526, 571, 607`.

Every fired class owns its digit two UNCONDITIONALLY — no package, no
input, no gates.  The carried row input of §4 shrinks to the seventeen
survivors of the mod-243 level (§7): the replacement of the input's row
half. -/

/-- The cycle law of level 81: the modulus-243 residue of `4 ^ m` is pinned
by the class of `m` modulo 81. -/
theorem four_pow_mod243 (m : Nat) : (4^m) % 243 = (4^(m % 81)) % 243 := by
  have h81 : (4^81) % 243 = 1 := by decide
  have h481q : ∀ q : Nat, (4^81)^q % 243 = 1 := by
    intro q
    induction q with
    | zero => decide
    | succ q' ih =>
      have hsucc : (4^81)^(Nat.succ q') = (4^81)^(q' + 1) := rfl
      rw [hsucc, Nat.pow_succ, Nat.mul_mod, h81, ih]
  have hmd : m = 81 * (m / 81) + m % 81 := (Nat.div_add_mod m 81).symm
  have h4m : 4^m = (4^81)^(m/81) * 4^(m%81) := by
    have h1 : 4^m = 4^(81*(m/81) + m%81) := congrArg (fun x => 4^x) hmd
    have h2 : 4^(81*(m/81) + m%81) = (4^81)^(m/81) * 4^(m%81) := by
      rw [Nat.pow_add, Nat.pow_mul]
    exact h1.trans h2
  rw [h4m, Nat.mul_mod, h481q, Nat.one_mul, Nat.mod_mod]

/-- The cycle law of level 243: the modulus-729 residue of `4 ^ m` is pinned
by the class of `m` modulo 243. -/
theorem four_pow_mod729 (m : Nat) : (4^m) % 729 = (4^(m % 243)) % 729 := by
  have h243 : (4^243) % 729 = 1 := by
    have hsplit : (243 : Nat) = 128 + 115 := by omega
    rw [hsplit, Nat.pow_add]
  have h4243q : ∀ q : Nat, (4^243)^q % 729 = 1 := by
    intro q
    induction q with
    | zero => decide
    | succ q' ih =>
      have hsucc : (4^243)^(Nat.succ q') = (4^243)^(q' + 1) := rfl
      rw [hsucc, Nat.pow_succ, Nat.mul_mod, h243, ih]
  have hmd : m = 243 * (m / 243) + m % 243 := (Nat.div_add_mod m 243).symm
  have h4m : 4^m = (4^243)^(m/243) * 4^(m%243) := by
    have h1 : 4^m = 4^(243*(m/243) + m%243) := congrArg (fun x => 4^x) hmd
    have h2 : 4^(243*(m/243) + m%243) = (4^243)^(m/243) * 4^(m%243) := by
      rw [Nat.pow_add, Nat.pow_mul]
    exact h1.trans h2
  rw [h4m, Nat.mul_mod, h4243q, Nat.one_mul, Nat.mod_mod]

/-- The thirteen fired classes' level values, computed at their levels. -/
theorem four_pow_19_mod81 : (4^19) % 81 = 58 := by decide
theorem four_pow_22_mod81 : (4^22) % 81 = 67 := by decide
theorem four_pow_55_mod243 : (4^55) % 243 = 166 := by decide
theorem four_pow_58_mod243 : (4^58) % 243 = 175 := by decide
theorem four_pow_64_mod243 : (4^64) % 243 = 193 := by decide
theorem four_pow_67_mod243 : (4^67) % 243 = 202 := by decide
theorem four_pow_85_mod729 : (4^85) % 729 = 499 := by decide
theorem four_pow_91_mod729 : (4^91) % 729 = 517 := by decide
theorem four_pow_112_mod729 : (4^112) % 729 = 580 := by decide
theorem four_pow_163_mod729 : (4^163) % 729 = 490 := by
  have hsplit : (163 : Nat) = 128 + 35 := by omega
  rw [hsplit, Nat.pow_add]
theorem four_pow_175_mod729 : (4^175) % 729 = 526 := by
  have hsplit : (175 : Nat) = 128 + 47 := by omega
  rw [hsplit, Nat.pow_add]
theorem four_pow_190_mod729 : (4^190) % 729 = 571 := by
  have hsplit : (190 : Nat) = 128 + 62 := by omega
  rw [hsplit, Nat.pow_add]
theorem four_pow_202_mod729 : (4^202) % 729 = 607 := by
  have hsplit : (202 : Nat) = 128 + 74 := by omega
  rw [hsplit, Nat.pow_add]

/-- The generic level-27 fire: a core in class `c` mod 27 whose level value
`4 ^ c % 81 = v` sits in the top third (`v / 27 = 2`) owns digit position
3 of `4 ^ core` outright. -/
theorem digit3_pow4_pos3_of_class (core c v : Nat)
    (h : core % 27 = c) (hv : (4^c) % 81 = v) (hv2 : v / 27 = 2) :
    digit3 (4^core) 3 = 2 := by
  have hm : (4^core) % 81 = v := by rw [four_pow_mod81, h]; exact hv
  show (4^core) / 3^3 % 3 = 2
  have h33 : (3 : Nat)^3 = 27 := by norm_num
  rw [h33]
  have hbridge : (4^core / 27) % 3 = ((4^core) % 81) / 27 := by omega
  rw [hbridge, hm, hv2]

/-- The generic level-81 fire: a core in class `c` mod 81 whose level value
`4 ^ c % 243 = v` sits in the top third (`v / 81 = 2`) owns digit position
4 of `4 ^ core` outright. -/
theorem digit3_pow4_pos4_of_class (core c v : Nat)
    (h : core % 81 = c) (hv : (4^c) % 243 = v) (hv2 : v / 81 = 2) :
    digit3 (4^core) 4 = 2 := by
  have hm : (4^core) % 243 = v := by rw [four_pow_mod243, h]; exact hv
  show (4^core) / 3^4 % 3 = 2
  have h34 : (3 : Nat)^4 = 81 := by norm_num
  rw [h34]
  have hbridge : (4^core / 81) % 3 = ((4^core) % 243) / 81 := by omega
  rw [hbridge, hm, hv2]

/-- The generic level-243 fire: a core in class `c` mod 243 whose level
value `4 ^ c % 729 = v` sits in the top third (`v / 243 = 2`) owns digit
position 5 of `4 ^ core` outright. -/
theorem digit3_pow4_pos5_of_class (core c v : Nat)
    (h : core % 243 = c) (hv : (4^c) % 729 = v) (hv2 : v / 243 = 2) :
    digit3 (4^core) 5 = 2 := by
  have hm : (4^core) % 729 = v := by rw [four_pow_mod729, h]; exact hv
  show (4^core) / 3^5 % 3 = 2
  have h35 : (3 : Nat)^5 = 243 := by norm_num
  rw [h35]
  have hbridge : (4^core / 243) % 3 = ((4^core) % 729) / 243 := by omega
  rw [hbridge, hm, hv2]

/-! ## §7 The replacement input — the shrunk row half, linked with the
universe -/

/-- **THE THIRTEEN FIRED CLASSES.**  The lattice's fired classes of the hard
family, at their three levels: every core in one of these classes owns its
digit two outright. -/
def s0_lattice_fire_class (core : Nat) : Prop :=
  core % 27 = 19 ∨ core % 27 = 22 ∨
  core % 81 = 55 ∨ core % 81 = 58 ∨ core % 81 = 64 ∨ core % 81 = 67 ∨
  core % 243 = 85 ∨ core % 243 = 91 ∨ core % 243 = 112 ∨ core % 243 = 163 ∨
  core % 243 = 175 ∨ core % 243 = 190 ∨ core % 243 = 202

/-- **THE LATTICE FIRE.**  Every one of the thirteen fired classes owns its
digit two unconditionally — no package, no input, no gates. -/
theorem s0_lattice_fire (core : Nat) (h : s0_lattice_fire_class core) :
    ∃ p : Nat, digit3 (4^core) p = 2 := by
  unfold s0_lattice_fire_class at h
  rcases h with h | h | h | h | h | h | h | h | h | h | h | h | h
  · exact ⟨3, digit3_pow4_pos3_of_class core 19 58 h four_pow_19_mod81 (by decide)⟩
  · exact ⟨3, digit3_pow4_pos3_of_class core 22 67 h four_pow_22_mod81 (by decide)⟩
  · exact ⟨4, digit3_pow4_pos4_of_class core 55 166 h four_pow_55_mod243 (by decide)⟩
  · exact ⟨4, digit3_pow4_pos4_of_class core 58 175 h four_pow_58_mod243 (by decide)⟩
  · exact ⟨4, digit3_pow4_pos4_of_class core 64 193 h four_pow_64_mod243 (by decide)⟩
  · exact ⟨4, digit3_pow4_pos4_of_class core 67 202 h four_pow_67_mod243 (by decide)⟩
  · exact ⟨5, digit3_pow4_pos5_of_class core 85 499 h four_pow_85_mod729 (by decide)⟩
  · exact ⟨5, digit3_pow4_pos5_of_class core 91 517 h four_pow_91_mod729 (by decide)⟩
  · exact ⟨5, digit3_pow4_pos5_of_class core 112 580 h four_pow_112_mod729 (by decide)⟩
  · exact ⟨5, digit3_pow4_pos5_of_class core 163 490 h four_pow_163_mod729 (by decide)⟩
  · exact ⟨5, digit3_pow4_pos5_of_class core 175 526 h four_pow_175_mod729 (by decide)⟩
  · exact ⟨5, digit3_pow4_pos5_of_class core 190 571 h four_pow_190_mod729 (by decide)⟩
  · exact ⟨5, digit3_pow4_pos5_of_class core 202 607 h four_pow_202_mod729 (by decide)⟩

/-- **THE SEVENTEEN SURVIVORS.**  The hard family's residue classes that no
lattice level has fired: the carried row input shrinks to exactly these. -/
def tailF_row_survivor_class (core : Nat) : Prop :=
  core % 243 = 1 ∨ core % 243 = 4 ∨ core % 243 = 10 ∨ core % 243 = 13 ∨
  core % 243 = 28 ∨ core % 243 = 31 ∨ core % 243 = 37 ∨ core % 243 = 40 ∨
  core % 243 = 82 ∨ core % 243 = 94 ∨ core % 243 = 109 ∨ core % 243 = 118 ∨
  core % 243 = 121 ∨ core % 243 = 166 ∨ core % 243 = 172 ∨ core % 243 = 193 ∨
  core % 243 = 199

/-- **THE BRIDGE.**  Every hard-family core that no lattice level has fired
is one of the seventeen survivors: the case tree 6 → 12 → 24 closes the
thirteen fired leaves by contradiction and lands the seventeen survivors
by arithmetic. -/
theorem tailF_row_survivor_of_hard_nonfire (core : Nat)
    (hc14 : core % 9 = 1 ∨ core % 9 = 4)
    (hf : ¬ s0_lattice_fire_class core) :
    tailF_row_survivor_class core := by
  unfold tailF_row_survivor_class
  unfold s0_lattice_fire_class at hf
  push_neg at hf
  obtain ⟨n19, n22, n55, n58, n64, n67, n85, n91, n112, n163, n175, n190, n202⟩ := hf
  rcases hc14 with h1 | h4
  · have h27 : core % 27 = 1 ∨ core % 27 = 10 ∨ core % 27 = 19 := by omega
    rcases h27 with c1 | c10 | c19
    · have h81 : core % 81 = 1 ∨ core % 81 = 28 ∨ core % 81 = 55 := by omega
      rcases h81 with d1 | d28 | d55
      · have h243 : core % 243 = 1 ∨ core % 243 = 82 ∨ core % 243 = 163 := by omega
        rcases h243 with e1 | e82 | e163
        · omega
        · omega
        · exact absurd e163 n163
      · have h243 : core % 243 = 28 ∨ core % 243 = 109 ∨ core % 243 = 190 := by omega
        rcases h243 with e28 | e109 | e190
        · omega
        · omega
        · exact absurd e190 n190
      · exact absurd d55 n55
    · have h81 : core % 81 = 10 ∨ core % 81 = 37 ∨ core % 81 = 64 := by omega
      rcases h81 with d10 | d37 | d64
      · have h243 : core % 243 = 10 ∨ core % 243 = 91 ∨ core % 243 = 172 := by omega
        rcases h243 with e10 | e91 | e172
        · omega
        · exact absurd e91 n91
        · omega
      · have h243 : core % 243 = 37 ∨ core % 243 = 118 ∨ core % 243 = 199 := by omega
        rcases h243 with e37 | e118 | e199
        · omega
        · omega
        · omega
      · exact absurd d64 n64
    · exact absurd c19 n19
  · have h27 : core % 27 = 4 ∨ core % 27 = 13 ∨ core % 27 = 22 := by omega
    rcases h27 with c4 | c13 | c22
    · have h81 : core % 81 = 4 ∨ core % 81 = 31 ∨ core % 81 = 58 := by omega
      rcases h81 with d4 | d31 | d58
      · have h243 : core % 243 = 4 ∨ core % 243 = 85 ∨ core % 243 = 166 := by omega
        rcases h243 with e4 | e85 | e166
        · omega
        · exact absurd e85 n85
        · omega
      · have h243 : core % 243 = 31 ∨ core % 243 = 112 ∨ core % 243 = 193 := by omega
        rcases h243 with e31 | e112 | e193
        · omega
        · exact absurd e112 n112
        · omega
      · exact absurd d58 n58
    · have h81 : core % 81 = 13 ∨ core % 81 = 40 ∨ core % 81 = 67 := by omega
      rcases h81 with d13 | d40 | d67
      · have h243 : core % 243 = 13 ∨ core % 243 = 94 ∨ core % 243 = 175 := by omega
        rcases h243 with e13 | e94 | e175
        · omega
        · omega
        · exact absurd e175 n175
      · have h243 : core % 243 = 40 ∨ core % 243 = 121 ∨ core % 243 = 202 := by omega
        rcases h243 with e40 | e121 | e202
        · omega
        · omega
        · exact absurd e202 n202
      · exact absurd d67 n67
    · exact absurd c22 n22

/-- **THE SHRUNK ROW INPUT.**  The row primitive with all thirteen fired
classes removed: the residue clause now demands one of the seventeen
mod-243 survivors, and the fire at every other class of the hard family is
unconditional (§6). -/
def tailF_row_primitive_mod243 : Prop :=
  ∀ core : Nat, 500 < core → ¬ 3 ∣ core →
    tailF_row_survivor_class core →
      ∃ j : Nat, 2 * 3^j ≤ (omegaCutWord 0 core) % 3^(j+1)

/-- **THE WEAKNESS RECEIPT.**  The shrunk row input is strictly weaker than
the row primitive: every survivor class is a class of the hard family. -/
theorem tailF_row_primitive_mod243_of_row (hRow : tailF_row_primitive) :
    tailF_row_primitive_mod243 := by
  intro core hK hfree hclass
  refine hRow core hK hfree ?_
  unfold tailF_row_survivor_class at hclass
  rcases hclass with h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h <;> omega

/-- **THE REPLACEMENT OF THE INPUT'S ROW HALF.**  The tower primitive plus
the seventeen-survivor row primitive compose into the full second-observer
input: the sheet-zero family's fired classes close by the lattice outright,
the survivors go through the shrunk row input and the uniform row law, and
the tower family rides the tower primitive unchanged. -/
theorem tailF_of_tower_and_row_mod243
    (hTower : tailF_tower_primitive)
    (hRowMod : tailF_row_primitive_mod243) :
    four_power_omega_shadow_wave_tailF := by
  intro K hK hshadow
  obtain ⟨s, core, hKsc, hfree, hres, hA, hB1, hB2, hC, hD⟩ := hshadow
  rcases Nat.eq_zero_or_pos s with rfl | hs1
  · have hc14 : core % 9 = 1 ∨ core % 9 = 4 := by
      rcases hres with h4 | ⟨_, h1⟩ | ⟨h1s, h7⟩
      · exact Or.inr h4
      · exact Or.inl h1
      · exact absurd h1s (by omega)
    rw [Nat.pow_zero, Nat.one_mul] at hKsc
    have hKc : 500 < core := by rw [← hKsc]; exact hK
    by_cases hf : s0_lattice_fire_class core
    · obtain ⟨p, hp⟩ := s0_lattice_fire core hf
      rw [hKsc]
      exact ⟨p, hp⟩
    · obtain ⟨j, hj⟩ := hRowMod core hKc hfree
        (tailF_row_survivor_of_hard_nonfire core hc14 hf)
      refine ⟨1+j, ?_⟩
      rw [hKsc]
      exact omega_row_level_digit_two core j hj
  · have hc47 : core % 9 = 4 ∨ core % 9 = 7 := by
      rcases hres with h4 | ⟨hs0, h1⟩ | ⟨hs1', h7⟩
      · exact Or.inl h4
      · exact absurd hs0 (by omega)
      · exact Or.inr h7
    obtain ⟨i, _, hfire⟩ := hTower s core hs1 hfree hc47 hD
    refine ⟨s+1+i, ?_⟩
    rw [hKsc]
    exact tower_observation_digit_two s core i hfire

/-- **THE EVEN STATEMENT ON THE REPLACEMENT INPUT.**  Through the
monolith's own terminal identity, the tower primitive plus the
seventeen-survivor row primitive carry the whole even-exponent statement. -/
theorem even_conjecture_of_tower_and_row_mod243
    (hB : erdos_even_conjecture_iff_tailF)
    (hTower : tailF_tower_primitive)
    (hRowMod : tailF_row_primitive_mod243) :
    ∀ K : Nat, 8 ≤ K → noTernaryTwo (4^K) = false :=
  hB.mpr
    (tailF_of_tower_and_row_mod243 hTower hRowMod)

/-- **THE CROWN ON THE REPLACEMENT INPUT.**  The monolith's universal
theorem with its input slot filled by the replacement pair: the tower
primitive and the seventeen-survivor row primitive. -/
theorem erdos_ternary_2_universal_of_tower_and_row_mod243
    (hB : erdos_ternary_2_universal_of_tailF)
    (hTower : tailF_tower_primitive)
    (hRowMod : tailF_row_primitive_mod243)
    (n : Nat) (hn : 9 ≤ n) :
    noTernaryTwo (2^n) = false :=
  hB
    (tailF_of_tower_and_row_mod243 hTower hRowMod) n hn

/-! ## §8 The row lattice, level six — the survivors fired one level deeper

The lattice's fourth level.  The cycle law now pins the modulus-2187 residue
of `4 ^ core` by the class of `core` modulo 729, and each of the seventeen
mod-243 survivor classes splits into three mod-729 subclasses — of which
exactly ONE fires.  The level-six lattice kills one third of the surviving
residue content unconditionally; the carried row input shrinks from the
seventeen mod-243 classes to thirty-four mod-729 classes — twice the count,
but each class one third as wide, and seventeen more classes of the hard
family closed outright:

* level 729, digit position 6: classes `31, 37, 118, 172, 253, 256, 271,
  337, 352, 409, 487, 490, 526, 568, 607, 679, 685` mod 729 — the seventeen
  fires, one per mod-243 survivor triple. -/

/-- The cycle law of level 729: the modulus-2187 residue of `4 ^ m` is pinned
by the class of `m` modulo 729. -/
theorem four_pow_mod2187 (m : Nat) : (4^m) % 2187 = (4^(m % 729)) % 2187 := by
  have h729 : (4^729) % 2187 = 1 := by
    have hsplit : (729 : Nat) = 243 + 243 + 243 := by omega
    rw [hsplit, Nat.pow_add, Nat.pow_add]
  have h4729q : ∀ q : Nat, (4^729)^q % 2187 = 1 := by
    intro q
    induction q with
    | zero => decide
    | succ q' ih =>
      have hsucc : (4^729)^(Nat.succ q') = (4^729)^(q' + 1) := rfl
      rw [hsucc, Nat.pow_succ, Nat.mul_mod, h729, ih]
  have hmd : m = 729 * (m / 729) + m % 729 := (Nat.div_add_mod m 729).symm
  have h4m : 4^m = (4^729)^(m/729) * 4^(m%729) := by
    have h1 : 4^m = 4^(729*(m/729) + m%729) := congrArg (fun x => 4^x) hmd
    have h2 : 4^(729*(m/729) + m%729) = (4^729)^(m/729) * 4^(m%729) := by
      rw [Nat.pow_add, Nat.pow_mul]
    exact h1.trans h2
  rw [h4m, Nat.mul_mod, h4729q, Nat.one_mul, Nat.mod_mod]

/-- The seventeen fired classes' level values, computed at their levels. -/
theorem four_pow_31_mod2187 : (4^31) % 2187 = 1795 := by decide
theorem four_pow_37_mod2187 : (4^37) % 2187 = 1813 := by decide
theorem four_pow_118_mod2187 : (4^118) % 2187 = 2056 := by decide
theorem four_pow_172_mod2187 : (4^172) % 2187 = 1489 := by
  have hsplit : (172 : Nat) = 128 + 44 := by omega
  rw [hsplit, Nat.pow_add]
theorem four_pow_253_mod2187 : (4^253) % 2187 = 1732 := by
  have hsplit : (253 : Nat) = 128 + 125 := by omega
  rw [hsplit, Nat.pow_add]
theorem four_pow_256_mod2187 : (4^256) % 2187 = 1498 := by
  have hsplit : (256 : Nat) = 128 + 128 := by omega
  rw [hsplit, Nat.pow_add]
theorem four_pow_271_mod2187 : (4^271) % 2187 = 1543 := by
  have hsplit : (271 : Nat) = 128 + 143 := by omega
  rw [hsplit, Nat.pow_add]
theorem four_pow_337_mod2187 : (4^337) % 2187 = 1741 := by
  have hsplit : (337 : Nat) = 128 + 209 := by omega
  rw [hsplit, Nat.pow_add]
theorem four_pow_352_mod2187 : (4^352) % 2187 = 1786 := by
  have hsplit : (352 : Nat) = 128 + 224 := by omega
  rw [hsplit, Nat.pow_add]
theorem four_pow_409_mod2187 : (4^409) % 2187 = 1471 := by
  have hsplit : (409 : Nat) = 200 + 209 := by omega
  rw [hsplit, Nat.pow_add]
theorem four_pow_487_mod2187 : (4^487) % 2187 = 1462 := by
  have hsplit : (487 : Nat) = 240 + 247 := by omega
  rw [hsplit, Nat.pow_add]
theorem four_pow_490_mod2187 : (4^490) % 2187 = 1714 := by
  have hsplit : (490 : Nat) = 245 + 245 := by omega
  rw [hsplit, Nat.pow_add]
theorem four_pow_526_mod2187 : (4^526) % 2187 = 1579 := by
  have hsplit : (526 : Nat) = 256 + 256 + 14 := by omega
  rw [hsplit, Nat.pow_add, Nat.pow_add]
theorem four_pow_568_mod2187 : (4^568) % 2187 = 1705 := by
  have hsplit : (568 : Nat) = 256 + 256 + 56 := by omega
  rw [hsplit, Nat.pow_add, Nat.pow_add]
theorem four_pow_607_mod2187 : (4^607) % 2187 = 1822 := by
  have hsplit : (607 : Nat) = 256 + 256 + 95 := by omega
  rw [hsplit, Nat.pow_add, Nat.pow_add]
theorem four_pow_679_mod2187 : (4^679) % 2187 = 1552 := by
  have hsplit : (679 : Nat) = 256 + 256 + 167 := by omega
  rw [hsplit, Nat.pow_add, Nat.pow_add]
theorem four_pow_685_mod2187 : (4^685) % 2187 = 1570 := by
  have hsplit : (685 : Nat) = 256 + 256 + 173 := by omega
  rw [hsplit, Nat.pow_add, Nat.pow_add]

/-- The generic level-729 fire: a core in class `c` mod 729 whose level value
`4 ^ c % 2187 = v` sits in the top third (`v / 729 = 2`) owns digit position
6 of `4 ^ core` outright. -/
theorem digit3_pow4_pos6_of_class (core c v : Nat)
    (h : core % 729 = c) (hv : (4^c) % 2187 = v) (hv2 : v / 729 = 2) :
    digit3 (4^core) 6 = 2 := by
  have hm : (4^core) % 2187 = v := by rw [four_pow_mod2187, h]; exact hv
  show (4^core) / 3^6 % 3 = 2
  have h36 : (3:Nat)^6 = 729 := by norm_num
  rw [h36]
  have hbridge : (4^core / 729) % 3 = ((4^core) % 2187) / 729 := by omega
  rw [hbridge, hm, hv2]

/-- **THE SEVENTEEN LEVEL-SIX FIRED CLASSES.**  Each mod-243 survivor triple
contributes exactly one fired subclass. -/
def s0_lattice_fire_class_mod729 (core : Nat) : Prop :=
  core % 729 = 31 ∨ core % 729 = 37 ∨ core % 729 = 118 ∨ core % 729 = 172 ∨
  core % 729 = 253 ∨ core % 729 = 256 ∨ core % 729 = 271 ∨ core % 729 = 337 ∨
  core % 729 = 352 ∨ core % 729 = 409 ∨ core % 729 = 487 ∨ core % 729 = 490 ∨
  core % 729 = 526 ∨ core % 729 = 568 ∨ core % 729 = 607 ∨ core % 729 = 679 ∨
  core % 729 = 685

/-- **THE LEVEL-SIX LATTICE FIRE.**  Every one of the seventeen fired classes
owns its digit two unconditionally. -/
theorem s0_lattice_fire_mod729 (core : Nat)
    (h : s0_lattice_fire_class_mod729 core) :
    ∃ p : Nat, digit3 (4^core) p = 2 := by
  unfold s0_lattice_fire_class_mod729 at h
  rcases h with h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h
  · exact ⟨6, digit3_pow4_pos6_of_class core 31 1795 h four_pow_31_mod2187 (by decide)⟩
  · exact ⟨6, digit3_pow4_pos6_of_class core 37 1813 h four_pow_37_mod2187 (by decide)⟩
  · exact ⟨6, digit3_pow4_pos6_of_class core 118 2056 h four_pow_118_mod2187 (by decide)⟩
  · exact ⟨6, digit3_pow4_pos6_of_class core 172 1489 h four_pow_172_mod2187 (by decide)⟩
  · exact ⟨6, digit3_pow4_pos6_of_class core 253 1732 h four_pow_253_mod2187 (by decide)⟩
  · exact ⟨6, digit3_pow4_pos6_of_class core 256 1498 h four_pow_256_mod2187 (by decide)⟩
  · exact ⟨6, digit3_pow4_pos6_of_class core 271 1543 h four_pow_271_mod2187 (by decide)⟩
  · exact ⟨6, digit3_pow4_pos6_of_class core 337 1741 h four_pow_337_mod2187 (by decide)⟩
  · exact ⟨6, digit3_pow4_pos6_of_class core 352 1786 h four_pow_352_mod2187 (by decide)⟩
  · exact ⟨6, digit3_pow4_pos6_of_class core 409 1471 h four_pow_409_mod2187 (by decide)⟩
  · exact ⟨6, digit3_pow4_pos6_of_class core 487 1462 h four_pow_487_mod2187 (by decide)⟩
  · exact ⟨6, digit3_pow4_pos6_of_class core 490 1714 h four_pow_490_mod2187 (by decide)⟩
  · exact ⟨6, digit3_pow4_pos6_of_class core 526 1579 h four_pow_526_mod2187 (by decide)⟩
  · exact ⟨6, digit3_pow4_pos6_of_class core 568 1705 h four_pow_568_mod2187 (by decide)⟩
  · exact ⟨6, digit3_pow4_pos6_of_class core 607 1822 h four_pow_607_mod2187 (by decide)⟩
  · exact ⟨6, digit3_pow4_pos6_of_class core 679 1552 h four_pow_679_mod2187 (by decide)⟩
  · exact ⟨6, digit3_pow4_pos6_of_class core 685 1570 h four_pow_685_mod2187 (by decide)⟩

/-- **THE THIRTY-FOUR LEVEL-SIX SURVIVORS.**  The hard family's residue
classes that no lattice level has fired: the carried row input shrinks to
exactly these, at mod-729 resolution. -/
def tailF_row_survivor_class_mod729 (core : Nat) : Prop :=
  core % 729 = 1 ∨ core % 729 = 4 ∨ core % 729 = 10 ∨ core % 729 = 13 ∨
  core % 729 = 28 ∨ core % 729 = 40 ∨ core % 729 = 82 ∨ core % 729 = 94 ∨
  core % 729 = 109 ∨ core % 729 = 121 ∨ core % 729 = 166 ∨ core % 729 = 193 ∨
  core % 729 = 199 ∨ core % 729 = 244 ∨ core % 729 = 247 ∨ core % 729 = 274 ∨
  core % 729 = 280 ∨ core % 729 = 283 ∨ core % 729 = 325 ∨ core % 729 = 361 ∨
  core % 729 = 364 ∨ core % 729 = 415 ∨ core % 729 = 436 ∨ core % 729 = 442 ∨
  core % 729 = 496 ∨ core % 729 = 499 ∨ core % 729 = 514 ∨ core % 729 = 517 ∨
  core % 729 = 523 ∨ core % 729 = 580 ∨ core % 729 = 595 ∨ core % 729 = 604 ∨
  core % 729 = 652 ∨ core % 729 = 658

/-- **THE LEVEL-SIX BRIDGE.**  Every hard-family core that neither lattice
level has fired is one of the thirty-four mod-729 survivors: the seventeen
mod-243 survivor classes each split into three mod-729 subclasses, exactly
one of which fires. -/
theorem tailF_row_survivor_mod729_of_nonfire (core : Nat)
    (hc14 : core % 9 = 1 ∨ core % 9 = 4)
    (hf : ¬ s0_lattice_fire_class core)
    (hf6 : ¬ s0_lattice_fire_class_mod729 core) :
    tailF_row_survivor_class_mod729 core := by
  have h243class := tailF_row_survivor_of_hard_nonfire core hc14 hf
  unfold tailF_row_survivor_class_mod729
  unfold tailF_row_survivor_class at h243class
  unfold s0_lattice_fire_class_mod729 at hf6
  push_neg at hf6
  obtain ⟨n31, n37, n118, n172, n253, n256, n271, n337, n352, n409, n487,
    n490, n526, n568, n607, n679, n685⟩ := hf6
  rcases h243class with c1 | c4 | c10 | c13 | c28 | c31 | c37 | c40 | c82 |
    c94 | c109 | c118 | c121 | c166 | c172 | c193 | c199
  · have h : core % 729 = 1 ∨ core % 729 = 244 ∨ core % 729 = 487 := by omega
    rcases h with e1 | e244 | e487
    · omega
    · omega
    · exact absurd e487 n487
  · have h : core % 729 = 4 ∨ core % 729 = 247 ∨ core % 729 = 490 := by omega
    rcases h with e4 | e247 | e490
    · omega
    · omega
    · exact absurd e490 n490
  · have h : core % 729 = 10 ∨ core % 729 = 253 ∨ core % 729 = 496 := by omega
    rcases h with e10 | e253 | e496
    · omega
    · exact absurd e253 n253
    · omega
  · have h : core % 729 = 13 ∨ core % 729 = 256 ∨ core % 729 = 499 := by omega
    rcases h with e13 | e256 | e499
    · omega
    · exact absurd e256 n256
    · omega
  · have h : core % 729 = 28 ∨ core % 729 = 271 ∨ core % 729 = 514 := by omega
    rcases h with e28 | e271 | e514
    · omega
    · exact absurd e271 n271
    · omega
  · have h : core % 729 = 31 ∨ core % 729 = 274 ∨ core % 729 = 517 := by omega
    rcases h with e31 | e274 | e517
    · exact absurd e31 n31
    · omega
    · omega
  · have h : core % 729 = 37 ∨ core % 729 = 280 ∨ core % 729 = 523 := by omega
    rcases h with e37 | e280 | e523
    · exact absurd e37 n37
    · omega
    · omega
  · have h : core % 729 = 40 ∨ core % 729 = 283 ∨ core % 729 = 526 := by omega
    rcases h with e40 | e283 | e526
    · omega
    · omega
    · exact absurd e526 n526
  · have h : core % 729 = 82 ∨ core % 729 = 325 ∨ core % 729 = 568 := by omega
    rcases h with e82 | e325 | e568
    · omega
    · omega
    · exact absurd e568 n568
  · have h : core % 729 = 94 ∨ core % 729 = 337 ∨ core % 729 = 580 := by omega
    rcases h with e94 | e337 | e580
    · omega
    · exact absurd e337 n337
    · omega
  · have h : core % 729 = 109 ∨ core % 729 = 352 ∨ core % 729 = 595 := by omega
    rcases h with e109 | e352 | e595
    · omega
    · exact absurd e352 n352
    · omega
  · have h : core % 729 = 118 ∨ core % 729 = 361 ∨ core % 729 = 604 := by omega
    rcases h with e118 | e361 | e604
    · exact absurd e118 n118
    · omega
    · omega
  · have h : core % 729 = 121 ∨ core % 729 = 364 ∨ core % 729 = 607 := by omega
    rcases h with e121 | e364 | e607
    · omega
    · omega
    · exact absurd e607 n607
  · have h : core % 729 = 166 ∨ core % 729 = 409 ∨ core % 729 = 652 := by omega
    rcases h with e166 | e409 | e652
    · omega
    · exact absurd e409 n409
    · omega
  · have h : core % 729 = 172 ∨ core % 729 = 415 ∨ core % 729 = 658 := by omega
    rcases h with e172 | e415 | e658
    · exact absurd e172 n172
    · omega
    · omega
  · have h : core % 729 = 193 ∨ core % 729 = 436 ∨ core % 729 = 679 := by omega
    rcases h with e193 | e436 | e679
    · omega
    · omega
    · exact absurd e679 n679
  · have h : core % 729 = 199 ∨ core % 729 = 442 ∨ core % 729 = 685 := by omega
    rcases h with e199 | e442 | e685
    · omega
    · omega
    · exact absurd e685 n685

/-- **THE SHRUNK ROW INPUT, LEVEL SIX.**  The row primitive with all
thirty lattice levels' fired classes removed: the residue clause now
demands one of the thirty-four mod-729 survivors. -/
def tailF_row_primitive_mod729 : Prop :=
  ∀ core : Nat, 500 < core → ¬ 3 ∣ core →
    tailF_row_survivor_class_mod729 core →
      ∃ j : Nat, 2 * 3^j ≤ (omegaCutWord 0 core) % 3^(j+1)

/-- **THE WEAKNESS RECEIPT, LEVEL SIX.**  The level-six shrunk row input is
strictly weaker than the mod-243 one: every mod-729 survivor sits inside a
mod-243 survivor class. -/
theorem tailF_row_primitive_mod729_of_mod243 (h : tailF_row_primitive_mod243) :
    tailF_row_primitive_mod729 := by
  intro core hK hfree hclass
  refine h core hK hfree ?_
  unfold tailF_row_survivor_class_mod729 at hclass
  unfold tailF_row_survivor_class
  rcases hclass with h | h | h | h | h | h | h | h | h | h | h | h | h | h | h |
    h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h <;> omega

theorem tailF_row_primitive_mod729_of_row (hRow : tailF_row_primitive) :
    tailF_row_primitive_mod729 :=
  tailF_row_primitive_mod729_of_mod243 (tailF_row_primitive_mod243_of_row hRow)

/-- **THE REPLACEMENT OF THE INPUT'S ROW HALF, LEVEL SIX.**  The tower
primitive plus the thirty-four-survivor row primitive compose into the full
second-observer input. -/
theorem tailF_of_tower_and_row_mod729
    (hTower : tailF_tower_primitive)
    (hRowMod : tailF_row_primitive_mod729) :
    four_power_omega_shadow_wave_tailF := by
  intro K hK hshadow
  obtain ⟨s, core, hKsc, hfree, hres, hA, hB1, hB2, hC, hD⟩ := hshadow
  rcases Nat.eq_zero_or_pos s with rfl | hs1
  · have hc14 : core % 9 = 1 ∨ core % 9 = 4 := by
      rcases hres with h4 | ⟨_, h1⟩ | ⟨h1s, h7⟩
      · exact Or.inr h4
      · exact Or.inl h1
      · exact absurd h1s (by omega)
    rw [Nat.pow_zero, Nat.one_mul] at hKsc
    have hKc : 500 < core := by rw [← hKsc]; exact hK
    by_cases hf : s0_lattice_fire_class core
    · obtain ⟨p, hp⟩ := s0_lattice_fire core hf
      rw [hKsc]
      exact ⟨p, hp⟩
    · by_cases hf6 : s0_lattice_fire_class_mod729 core
      · obtain ⟨p, hp⟩ := s0_lattice_fire_mod729 core hf6
        rw [hKsc]
        exact ⟨p, hp⟩
      · obtain ⟨j, hj⟩ := hRowMod core hKc hfree
          (tailF_row_survivor_mod729_of_nonfire core hc14 hf hf6)
        refine ⟨1+j, ?_⟩
        rw [hKsc]
        exact omega_row_level_digit_two core j hj
  · have hc47 : core % 9 = 4 ∨ core % 9 = 7 := by
      rcases hres with h4 | ⟨hs0, h1⟩ | ⟨hs1', h7⟩
      · exact Or.inl h4
      · exact absurd hs0 (by omega)
      · exact Or.inr h7
    obtain ⟨i, _, hfire⟩ := hTower s core hs1 hfree hc47 hD
    refine ⟨s+1+i, ?_⟩
    rw [hKsc]
    exact tower_observation_digit_two s core i hfire

/-- **THE EVEN STATEMENT ON THE REPLACEMENT INPUT, LEVEL SIX.** -/
theorem even_conjecture_of_tower_and_row_mod729
    (hB : erdos_even_conjecture_iff_tailF)
    (hTower : tailF_tower_primitive)
    (hRowMod : tailF_row_primitive_mod729) :
    ∀ K : Nat, 8 ≤ K → noTernaryTwo (4^K) = false :=
  hB.mpr
    (tailF_of_tower_and_row_mod729 hTower hRowMod)

/-- **THE CROWN ON THE REPLACEMENT INPUT, LEVEL SIX.** -/
theorem erdos_ternary_2_universal_of_tower_and_row_mod729
    (hB : erdos_ternary_2_universal_of_tailF)
    (hTower : tailF_tower_primitive)
    (hRowMod : tailF_row_primitive_mod729)
    (n : Nat) (hn : 9 ≤ n) :
    noTernaryTwo (2^n) = false :=
  hB
    (tailF_of_tower_and_row_mod729 hTower hRowMod) n hn

#print axioms tower_observation_digit_two
#print axioms omega_cut_word_stabilizes
#print axioms omega_tower_word_mod_stable
#print axioms omega_tower_word_mod_chain
#print axioms omega_tower_kill_of_diagonal_two
#print axioms omega_diagonal_two_of_mod_nine_one
#print axioms omega_diagonal_two_of_mod27_thirteen
#print axioms omega_diagonal_two_of_mod27_twentyfive
#print axioms omega_tower_digit_two_of_mod_nine_one
#print axioms omega_tower_digit_two_of_mod27_band
#print axioms omega_diagonal_two_of_mod81_four
#print axioms omega_diagonal_two_of_mod81_thirtyfour
#print axioms omega_diagonal_two_of_mod81_fortynine
#print axioms omega_diagonal_two_of_mod81_seventy
#print axioms omega_tower_digit_two_of_mod81_band
#print axioms omega_diagonal_two_of_mod243_sixteen
#print axioms omega_diagonal_two_of_mod243_thirtyone
#print axioms omega_diagonal_two_of_mod243_sixtyone
#print axioms omega_diagonal_two_of_mod243_seventysix
#print axioms omega_diagonal_two_of_mod243_onehundredtwentyfour
#print axioms omega_diagonal_two_of_mod243_onehundredthirtynine
#print axioms omega_diagonal_two_of_mod243_onehundredsixtynine
#print axioms omega_diagonal_two_of_mod243_onehundredeightyfour
#print axioms omega_tower_digit_two_of_mod243_band
#print axioms tailF_of_row_and_tower
#print axioms even_conjecture_of_row_and_tower
#print axioms erdos_ternary_2_universal_of_row_and_tower
#print axioms tower_dodge_dead_of_mod27_band
#print axioms four_pow_mod243
#print axioms four_pow_mod729
#print axioms digit3_pow4_pos3_of_class
#print axioms digit3_pow4_pos4_of_class
#print axioms digit3_pow4_pos5_of_class
#print axioms s0_lattice_fire
#print axioms tailF_row_survivor_of_hard_nonfire
#print axioms tailF_row_primitive_mod243_of_row
#print axioms tailF_of_tower_and_row_mod243
#print axioms even_conjecture_of_tower_and_row_mod243
#print axioms erdos_ternary_2_universal_of_tower_and_row_mod243
#print axioms four_pow_mod2187
#print axioms digit3_pow4_pos6_of_class
#print axioms s0_lattice_fire_mod729
#print axioms tailF_row_survivor_mod729_of_nonfire
#print axioms tailF_row_primitive_mod729_of_mod243
#print axioms tailF_row_primitive_mod729_of_row
#print axioms tailF_of_tower_and_row_mod729
#print axioms even_conjecture_of_tower_and_row_mod729
#print axioms erdos_ternary_2_universal_of_tower_and_row_mod729

/-! ## §7b The level-seven ignition — the lattice's seventh level, mod-2187

The grind's seventh level: every mod-729 survivor class splits into exactly
three mod-2187 subclasses, exactly one of which fires — the Cantor
arithmetic of the dodge set, one third per level.  Thirty-four more
hard-family classes die wholesale; the carried row input shrinks from the
thirty-four mod-729 survivors to the sixty-eight mod-2187 survivors. -/

/-- **THE LEVEL-SEVEN CYCLE LAW** — the modulus-6561 residue of `4 ^ m` is
pinned by the class of `m` modulo 2187. -/
theorem four_pow_mod6561 (m : Nat) : (4^m) % 6561 = (4^(m % 2187)) % 6561 := by
  have h2187 : (4^2187) % 6561 = 1 := by
    have hsplit : (2187 : Nat) = 243 + 243 + 243 + 243 + 243 + 243 + 243 + 243 + 243 := by omega
    rw [hsplit, Nat.pow_add, Nat.pow_add, Nat.pow_add, Nat.pow_add, Nat.pow_add, Nat.pow_add, Nat.pow_add, Nat.pow_add]
  have h42187q : ∀ q : Nat, (4^2187)^q % 6561 = 1 := by
    intro q
    induction q with
    | zero => decide
    | succ q' ih =>
      have hsucc : (4^2187)^(Nat.succ q') = (4^2187)^(q' + 1) := rfl
      rw [hsucc, Nat.pow_succ, Nat.mul_mod, h2187, ih]
  have hmd : m = 2187 * (m / 2187) + m % 2187 := (Nat.div_add_mod m 2187).symm
  have h4m : 4^m = (4^2187)^(m/2187) * 4^(m%2187) := by
    have h1 : 4^m = 4^(2187*(m/2187) + m%2187) := congrArg (fun x => 4^x) hmd
    have h2 : 4^(2187*(m/2187) + m%2187) = (4^2187)^(m/2187) * 4^(m%2187) := by
      rw [Nat.pow_add, Nat.pow_mul]
    exact h1.trans h2
  rw [h4m, Nat.mul_mod, h42187q, Nat.one_mul, Nat.mod_mod]

/-- The thirty-four fired classes' level values, computed at their levels. -/
theorem four_pow_10_mod6561 : (4^10) % 6561 = 5377 := by decide
theorem four_pow_28_mod6561 : (4^28) % 6561 = 5188 := by decide
theorem four_pow_199_mod6561 : (4^199) % 6561 = 4486 := by
  have hsplit : (199 : Nat) = 128 + 71 := by omega
  rw [hsplit, Nat.pow_add]
theorem four_pow_274_mod6561 : (4^274) % 6561 = 4711 := by
  have hsplit : (274 : Nat) = 256 + 18 := by omega
  rw [hsplit, Nat.pow_add]
theorem four_pow_415_mod6561 : (4^415) % 6561 = 4405 := by
  have hsplit : (415 : Nat) = 256 + 159 := by omega
  rw [hsplit, Nat.pow_add]
theorem four_pow_442_mod6561 : (4^442) % 6561 = 5215 := by
  have hsplit : (442 : Nat) = 256 + 186 := by omega
  rw [hsplit, Nat.pow_add]
theorem four_pow_499_mod6561 : (4^499) % 6561 = 4414 := by
  have hsplit : (499 : Nat) = 256 + 243 := by omega
  rw [hsplit, Nat.pow_add]
theorem four_pow_517_mod6561 : (4^517) % 6561 = 5440 := by
  have hsplit : (517 : Nat) = 256 + 256 + 5 := by omega
  rw [hsplit, Nat.pow_add, Nat.pow_add]
theorem four_pow_652_mod6561 : (4^652) % 6561 = 4387 := by
  have hsplit : (652 : Nat) = 256 + 256 + 140 := by omega
  rw [hsplit, Nat.pow_add, Nat.pow_add]
theorem four_pow_658_mod6561 : (4^658) % 6561 = 5134 := by
  have hsplit : (658 : Nat) = 256 + 256 + 146 := by omega
  rw [hsplit, Nat.pow_add, Nat.pow_add]
theorem four_pow_742_mod6561 : (4^742) % 6561 = 5143 := by
  have hsplit : (742 : Nat) = 256 + 256 + 230 := by omega
  rw [hsplit, Nat.pow_add, Nat.pow_add]
theorem four_pow_769_mod6561 : (4^769) % 6561 = 4495 := by
  have hsplit : (769 : Nat) = 256 + 256 + 256 + 1 := by omega
  rw [hsplit, Nat.pow_add, Nat.pow_add, Nat.pow_add]
theorem four_pow_811_mod6561 : (4^811) % 6561 = 4621 := by
  have hsplit : (811 : Nat) = 256 + 256 + 256 + 43 := by omega
  rw [hsplit, Nat.pow_add, Nat.pow_add, Nat.pow_add]
theorem four_pow_895_mod6561 : (4^895) % 6561 = 5116 := by
  have hsplit : (895 : Nat) = 256 + 256 + 256 + 127 := by omega
  rw [hsplit, Nat.pow_add, Nat.pow_add, Nat.pow_add]
theorem four_pow_1012_mod6561 : (4^1012) % 6561 = 5224 := by
  have hsplit : (1012 : Nat) = 256 + 256 + 256 + 244 := by omega
  rw [hsplit, Nat.pow_add, Nat.pow_add, Nat.pow_add]
theorem four_pow_1054_mod6561 : (4^1054) % 6561 = 5350 := by
  have hsplit : (1054 : Nat) = 256 + 256 + 256 + 256 + 30 := by omega
  rw [hsplit, Nat.pow_add, Nat.pow_add, Nat.pow_add, Nat.pow_add]
theorem four_pow_1090_mod6561 : (4^1090) % 6561 = 4972 := by
  have hsplit : (1090 : Nat) = 256 + 256 + 256 + 256 + 66 := by omega
  rw [hsplit, Nat.pow_add, Nat.pow_add, Nat.pow_add, Nat.pow_add]
theorem four_pow_1309_mod6561 : (4^1309) % 6561 = 4657 := by
  have hsplit : (1309 : Nat) = 256 + 256 + 256 + 256 + 256 + 29 := by omega
  rw [hsplit, Nat.pow_add, Nat.pow_add, Nat.pow_add, Nat.pow_add, Nat.pow_add]
theorem four_pow_1324_mod6561 : (4^1324) % 6561 = 4702 := by
  have hsplit : (1324 : Nat) = 256 + 256 + 256 + 256 + 256 + 44 := by omega
  rw [hsplit, Nat.pow_add, Nat.pow_add, Nat.pow_add, Nat.pow_add, Nat.pow_add]
theorem four_pow_1333_mod6561 : (4^1333) % 6561 = 5701 := by
  have hsplit : (1333 : Nat) = 256 + 256 + 256 + 256 + 256 + 53 := by omega
  rw [hsplit, Nat.pow_add, Nat.pow_add, Nat.pow_add, Nat.pow_add, Nat.pow_add]
theorem four_pow_1459_mod6561 : (4^1459) % 6561 = 4378 := by
  have hsplit : (1459 : Nat) = 256 + 256 + 256 + 256 + 256 + 179 := by omega
  rw [hsplit, Nat.pow_add, Nat.pow_add, Nat.pow_add, Nat.pow_add, Nat.pow_add]
theorem four_pow_1462_mod6561 : (4^1462) % 6561 = 4630 := by
  have hsplit : (1462 : Nat) = 256 + 256 + 256 + 256 + 256 + 182 := by omega
  rw [hsplit, Nat.pow_add, Nat.pow_add, Nat.pow_add, Nat.pow_add, Nat.pow_add]
theorem four_pow_1552_mod6561 : (4^1552) % 6561 = 5386 := by
  have hsplit : (1552 : Nat) = 256 + 256 + 256 + 256 + 256 + 256 + 16 := by omega
  rw [hsplit, Nat.pow_add, Nat.pow_add, Nat.pow_add, Nat.pow_add, Nat.pow_add, Nat.pow_add]
theorem four_pow_1567_mod6561 : (4^1567) % 6561 = 5431 := by
  have hsplit : (1567 : Nat) = 256 + 256 + 256 + 256 + 256 + 256 + 31 := by omega
  rw [hsplit, Nat.pow_add, Nat.pow_add, Nat.pow_add, Nat.pow_add, Nat.pow_add, Nat.pow_add]
theorem four_pow_1579_mod6561 : (4^1579) % 6561 = 4738 := by
  have hsplit : (1579 : Nat) = 256 + 256 + 256 + 256 + 256 + 256 + 43 := by omega
  rw [hsplit, Nat.pow_add, Nat.pow_add, Nat.pow_add, Nat.pow_add, Nat.pow_add, Nat.pow_add]
theorem four_pow_1651_mod6561 : (4^1651) % 6561 = 4468 := by
  have hsplit : (1651 : Nat) = 256 + 256 + 256 + 256 + 256 + 256 + 115 := by omega
  rw [hsplit, Nat.pow_add, Nat.pow_add, Nat.pow_add, Nat.pow_add, Nat.pow_add, Nat.pow_add]
theorem four_pow_1702_mod6561 : (4^1702) % 6561 = 5107 := by
  have hsplit : (1702 : Nat) = 256 + 256 + 256 + 256 + 256 + 256 + 166 := by omega
  rw [hsplit, Nat.pow_add, Nat.pow_add, Nat.pow_add, Nat.pow_add, Nat.pow_add, Nat.pow_add]
theorem four_pow_1705_mod6561 : (4^1705) % 6561 = 5359 := by
  have hsplit : (1705 : Nat) = 256 + 256 + 256 + 256 + 256 + 256 + 169 := by omega
  rw [hsplit, Nat.pow_add, Nat.pow_add, Nat.pow_add, Nat.pow_add, Nat.pow_add, Nat.pow_add]
theorem four_pow_1738_mod6561 : (4^1738) % 6561 = 4729 := by
  have hsplit : (1738 : Nat) = 256 + 256 + 256 + 256 + 256 + 256 + 202 := by omega
  rw [hsplit, Nat.pow_add, Nat.pow_add, Nat.pow_add, Nat.pow_add, Nat.pow_add, Nat.pow_add]
theorem four_pow_1822_mod6561 : (4^1822) % 6561 = 5467 := by
  have hsplit : (1822 : Nat) = 256 + 256 + 256 + 256 + 256 + 256 + 256 + 30 := by omega
  rw [hsplit, Nat.pow_add, Nat.pow_add, Nat.pow_add, Nat.pow_add, Nat.pow_add, Nat.pow_add, Nat.pow_add]
theorem four_pow_1894_mod6561 : (4^1894) % 6561 = 5197 := by
  have hsplit : (1894 : Nat) = 256 + 256 + 256 + 256 + 256 + 256 + 256 + 102 := by omega
  rw [hsplit, Nat.pow_add, Nat.pow_add, Nat.pow_add, Nat.pow_add, Nat.pow_add, Nat.pow_add, Nat.pow_add]
theorem four_pow_1954_mod6561 : (4^1954) % 6561 = 4648 := by
  have hsplit : (1954 : Nat) = 256 + 256 + 256 + 256 + 256 + 256 + 256 + 162 := by omega
  rw [hsplit, Nat.pow_add, Nat.pow_add, Nat.pow_add, Nat.pow_add, Nat.pow_add, Nat.pow_add, Nat.pow_add]
theorem four_pow_1972_mod6561 : (4^1972) % 6561 = 4459 := by
  have hsplit : (1972 : Nat) = 256 + 256 + 256 + 256 + 256 + 256 + 256 + 180 := by omega
  rw [hsplit, Nat.pow_add, Nat.pow_add, Nat.pow_add, Nat.pow_add, Nat.pow_add, Nat.pow_add, Nat.pow_add]
theorem four_pow_1981_mod6561 : (4^1981) % 6561 = 5458 := by
  have hsplit : (1981 : Nat) = 256 + 256 + 256 + 256 + 256 + 256 + 256 + 189 := by omega
  rw [hsplit, Nat.pow_add, Nat.pow_add, Nat.pow_add, Nat.pow_add, Nat.pow_add, Nat.pow_add, Nat.pow_add]

/-- The generic level-2187 fire: a core in class `c` mod 2187 whose level value
`4 ^ c % 6561 = v` sits in the top third (`v / 2187 = 2`) owns digit position
7 of `4 ^ core` outright. -/
theorem digit3_pow4_pos7_of_class (core c v : Nat)
    (h : core % 2187 = c) (hv : (4^c) % 6561 = v) (hv2 : v / 2187 = 2) :
    digit3 (4^core) 7 = 2 := by
  have hm : (4^core) % 6561 = v := by rw [four_pow_mod6561, h]; exact hv
  show (4^core) / 3^7 % 3 = 2
  have h37 : (3:Nat)^7 = 2187 := by norm_num
  rw [h37]
  have hbridge : (4^core / 2187) % 3 = ((4^core) % 6561) / 2187 := by omega
  rw [hbridge, hm, hv2]

/-- **THE THIRTY-FOUR LEVEL-SEVEN FIRED CLASSES.**  Each mod-729 survivor
triple contributes exactly one fired subclass. -/
def s0_lattice_fire_class_mod2187 (core : Nat) : Prop :=
  core % 2187 = 10 ∨ core % 2187 = 28 ∨ core % 2187 = 199 ∨
  core % 2187 = 274 ∨ core % 2187 = 415 ∨ core % 2187 = 442 ∨
  core % 2187 = 499 ∨ core % 2187 = 517 ∨ core % 2187 = 652 ∨
  core % 2187 = 658 ∨ core % 2187 = 742 ∨ core % 2187 = 769 ∨
  core % 2187 = 811 ∨ core % 2187 = 895 ∨ core % 2187 = 1012 ∨
  core % 2187 = 1054 ∨ core % 2187 = 1090 ∨ core % 2187 = 1309 ∨
  core % 2187 = 1324 ∨ core % 2187 = 1333 ∨ core % 2187 = 1459 ∨
  core % 2187 = 1462 ∨ core % 2187 = 1552 ∨ core % 2187 = 1567 ∨
  core % 2187 = 1579 ∨ core % 2187 = 1651 ∨ core % 2187 = 1702 ∨
  core % 2187 = 1705 ∨ core % 2187 = 1738 ∨ core % 2187 = 1822 ∨
  core % 2187 = 1894 ∨ core % 2187 = 1954 ∨ core % 2187 = 1972 ∨
  core % 2187 = 1981

/-- **THE LEVEL-SEVEN LATTICE FIRE.**  Every one of the thirty-four fired
classes owns its digit two unconditionally — no package, no input, no
gates. -/
theorem s0_lattice_fire_mod2187 (core : Nat)
    (h : s0_lattice_fire_class_mod2187 core) :
    ∃ p : Nat, digit3 (4^core) p = 2 := by
  unfold s0_lattice_fire_class_mod2187 at h
  rcases h with h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h
  · exact ⟨7, digit3_pow4_pos7_of_class core 10 5377 h four_pow_10_mod6561 (by decide)⟩
  · exact ⟨7, digit3_pow4_pos7_of_class core 28 5188 h four_pow_28_mod6561 (by decide)⟩
  · exact ⟨7, digit3_pow4_pos7_of_class core 199 4486 h four_pow_199_mod6561 (by decide)⟩
  · exact ⟨7, digit3_pow4_pos7_of_class core 274 4711 h four_pow_274_mod6561 (by decide)⟩
  · exact ⟨7, digit3_pow4_pos7_of_class core 415 4405 h four_pow_415_mod6561 (by decide)⟩
  · exact ⟨7, digit3_pow4_pos7_of_class core 442 5215 h four_pow_442_mod6561 (by decide)⟩
  · exact ⟨7, digit3_pow4_pos7_of_class core 499 4414 h four_pow_499_mod6561 (by decide)⟩
  · exact ⟨7, digit3_pow4_pos7_of_class core 517 5440 h four_pow_517_mod6561 (by decide)⟩
  · exact ⟨7, digit3_pow4_pos7_of_class core 652 4387 h four_pow_652_mod6561 (by decide)⟩
  · exact ⟨7, digit3_pow4_pos7_of_class core 658 5134 h four_pow_658_mod6561 (by decide)⟩
  · exact ⟨7, digit3_pow4_pos7_of_class core 742 5143 h four_pow_742_mod6561 (by decide)⟩
  · exact ⟨7, digit3_pow4_pos7_of_class core 769 4495 h four_pow_769_mod6561 (by decide)⟩
  · exact ⟨7, digit3_pow4_pos7_of_class core 811 4621 h four_pow_811_mod6561 (by decide)⟩
  · exact ⟨7, digit3_pow4_pos7_of_class core 895 5116 h four_pow_895_mod6561 (by decide)⟩
  · exact ⟨7, digit3_pow4_pos7_of_class core 1012 5224 h four_pow_1012_mod6561 (by decide)⟩
  · exact ⟨7, digit3_pow4_pos7_of_class core 1054 5350 h four_pow_1054_mod6561 (by decide)⟩
  · exact ⟨7, digit3_pow4_pos7_of_class core 1090 4972 h four_pow_1090_mod6561 (by decide)⟩
  · exact ⟨7, digit3_pow4_pos7_of_class core 1309 4657 h four_pow_1309_mod6561 (by decide)⟩
  · exact ⟨7, digit3_pow4_pos7_of_class core 1324 4702 h four_pow_1324_mod6561 (by decide)⟩
  · exact ⟨7, digit3_pow4_pos7_of_class core 1333 5701 h four_pow_1333_mod6561 (by decide)⟩
  · exact ⟨7, digit3_pow4_pos7_of_class core 1459 4378 h four_pow_1459_mod6561 (by decide)⟩
  · exact ⟨7, digit3_pow4_pos7_of_class core 1462 4630 h four_pow_1462_mod6561 (by decide)⟩
  · exact ⟨7, digit3_pow4_pos7_of_class core 1552 5386 h four_pow_1552_mod6561 (by decide)⟩
  · exact ⟨7, digit3_pow4_pos7_of_class core 1567 5431 h four_pow_1567_mod6561 (by decide)⟩
  · exact ⟨7, digit3_pow4_pos7_of_class core 1579 4738 h four_pow_1579_mod6561 (by decide)⟩
  · exact ⟨7, digit3_pow4_pos7_of_class core 1651 4468 h four_pow_1651_mod6561 (by decide)⟩
  · exact ⟨7, digit3_pow4_pos7_of_class core 1702 5107 h four_pow_1702_mod6561 (by decide)⟩
  · exact ⟨7, digit3_pow4_pos7_of_class core 1705 5359 h four_pow_1705_mod6561 (by decide)⟩
  · exact ⟨7, digit3_pow4_pos7_of_class core 1738 4729 h four_pow_1738_mod6561 (by decide)⟩
  · exact ⟨7, digit3_pow4_pos7_of_class core 1822 5467 h four_pow_1822_mod6561 (by decide)⟩
  · exact ⟨7, digit3_pow4_pos7_of_class core 1894 5197 h four_pow_1894_mod6561 (by decide)⟩
  · exact ⟨7, digit3_pow4_pos7_of_class core 1954 4648 h four_pow_1954_mod6561 (by decide)⟩
  · exact ⟨7, digit3_pow4_pos7_of_class core 1972 4459 h four_pow_1972_mod6561 (by decide)⟩
  · exact ⟨7, digit3_pow4_pos7_of_class core 1981 5458 h four_pow_1981_mod6561 (by decide)⟩

/-- **THE SIXTY-EIGHT LEVEL-SEVEN SURVIVORS.**  The hard family's residue
classes that no lattice level has fired: the carried row input shrinks to
exactly these, at mod-2187 resolution. -/
def tailF_row_survivor_class_mod2187 (core : Nat) : Prop :=
  core % 2187 = 1 ∨ core % 2187 = 4 ∨ core % 2187 = 13 ∨
  core % 2187 = 40 ∨ core % 2187 = 82 ∨ core % 2187 = 94 ∨
  core % 2187 = 109 ∨ core % 2187 = 121 ∨ core % 2187 = 166 ∨
  core % 2187 = 193 ∨ core % 2187 = 244 ∨ core % 2187 = 247 ∨
  core % 2187 = 280 ∨ core % 2187 = 283 ∨ core % 2187 = 325 ∨
  core % 2187 = 361 ∨ core % 2187 = 364 ∨ core % 2187 = 436 ∨
  core % 2187 = 496 ∨ core % 2187 = 514 ∨ core % 2187 = 523 ∨
  core % 2187 = 580 ∨ core % 2187 = 595 ∨ core % 2187 = 604 ∨
  core % 2187 = 730 ∨ core % 2187 = 733 ∨ core % 2187 = 739 ∨
  core % 2187 = 757 ∨ core % 2187 = 823 ∨ core % 2187 = 838 ∨
  core % 2187 = 850 ∨ core % 2187 = 922 ∨ core % 2187 = 928 ∨
  core % 2187 = 973 ∨ core % 2187 = 976 ∨ core % 2187 = 1003 ∨
  core % 2187 = 1009 ∨ core % 2187 = 1093 ∨ core % 2187 = 1144 ∨
  core % 2187 = 1165 ∨ core % 2187 = 1171 ∨ core % 2187 = 1225 ∨
  core % 2187 = 1228 ∨ core % 2187 = 1243 ∨ core % 2187 = 1246 ∨
  core % 2187 = 1252 ∨ core % 2187 = 1381 ∨ core % 2187 = 1387 ∨
  core % 2187 = 1468 ∨ core % 2187 = 1471 ∨ core % 2187 = 1486 ∨
  core % 2187 = 1498 ∨ core % 2187 = 1540 ∨ core % 2187 = 1624 ∨
  core % 2187 = 1657 ∨ core % 2187 = 1732 ∨ core % 2187 = 1741 ∨
  core % 2187 = 1783 ∨ core % 2187 = 1819 ∨ core % 2187 = 1873 ∨
  core % 2187 = 1900 ∨ core % 2187 = 1957 ∨ core % 2187 = 1975 ∨
  core % 2187 = 2038 ∨ core % 2187 = 2053 ∨ core % 2187 = 2062 ∨
  core % 2187 = 2110 ∨ core % 2187 = 2116

/-- **THE LEVEL-SEVEN BRIDGE.**  Every hard-family core that no lattice
level has fired is one of the sixty-eight mod-2187 survivors: the
thirty-four mod-729 survivor classes each split into three mod-2187
subclasses, exactly one of which fires. -/
theorem tailF_row_survivor_mod2187_of_nonfire (core : Nat)
    (hc14 : core % 9 = 1 ∨ core % 9 = 4)
    (hf : ¬ s0_lattice_fire_class core)
    (hf6 : ¬ s0_lattice_fire_class_mod729 core)
    (hf7 : ¬ s0_lattice_fire_class_mod2187 core) :
    tailF_row_survivor_class_mod2187 core := by
  have h729class := tailF_row_survivor_mod729_of_nonfire core hc14 hf hf6
  unfold tailF_row_survivor_class_mod2187
  unfold tailF_row_survivor_class_mod729 at h729class
  unfold s0_lattice_fire_class_mod2187 at hf7
  push_neg at hf7
  obtain ⟨n10, n28, n199, n274, n415, n442, n499, n517, n652, n658, n742, n769, n811, n895, n1012, n1054, n1090,
    n1309, n1324, n1333, n1459, n1462, n1552, n1567, n1579, n1651, n1702, n1705, n1738, n1822, n1894, n1954, n1972, n1981⟩ := hf7
  rcases h729class with c1 | c4 | c10 | c13 | c28 | c40 | c82 | c94 | c109 | c121 | c166 | c193 | c199 | c244 | c247 | c274 | c280 | c283 | c325 | c361 | c364 | c415 | c436 | c442 | c496 | c499 | c514 | c517 | c523 | c580 | c595 | c604 | c652 | c658
  · have h : core % 2187 = 1 ∨ core % 2187 = 730 ∨ core % 2187 = 1459 := by omega
    rcases h with e1 | e730 | e1459
    · omega
    · omega
    · exact absurd e1459 n1459
  · have h : core % 2187 = 4 ∨ core % 2187 = 733 ∨ core % 2187 = 1462 := by omega
    rcases h with e4 | e733 | e1462
    · omega
    · omega
    · exact absurd e1462 n1462
  · have h : core % 2187 = 10 ∨ core % 2187 = 739 ∨ core % 2187 = 1468 := by omega
    rcases h with e10 | e739 | e1468
    · exact absurd e10 n10
    · omega
    · omega
  · have h : core % 2187 = 13 ∨ core % 2187 = 742 ∨ core % 2187 = 1471 := by omega
    rcases h with e13 | e742 | e1471
    · omega
    · exact absurd e742 n742
    · omega
  · have h : core % 2187 = 28 ∨ core % 2187 = 757 ∨ core % 2187 = 1486 := by omega
    rcases h with e28 | e757 | e1486
    · exact absurd e28 n28
    · omega
    · omega
  · have h : core % 2187 = 40 ∨ core % 2187 = 769 ∨ core % 2187 = 1498 := by omega
    rcases h with e40 | e769 | e1498
    · omega
    · exact absurd e769 n769
    · omega
  · have h : core % 2187 = 82 ∨ core % 2187 = 811 ∨ core % 2187 = 1540 := by omega
    rcases h with e82 | e811 | e1540
    · omega
    · exact absurd e811 n811
    · omega
  · have h : core % 2187 = 94 ∨ core % 2187 = 823 ∨ core % 2187 = 1552 := by omega
    rcases h with e94 | e823 | e1552
    · omega
    · omega
    · exact absurd e1552 n1552
  · have h : core % 2187 = 109 ∨ core % 2187 = 838 ∨ core % 2187 = 1567 := by omega
    rcases h with e109 | e838 | e1567
    · omega
    · omega
    · exact absurd e1567 n1567
  · have h : core % 2187 = 121 ∨ core % 2187 = 850 ∨ core % 2187 = 1579 := by omega
    rcases h with e121 | e850 | e1579
    · omega
    · omega
    · exact absurd e1579 n1579
  · have h : core % 2187 = 166 ∨ core % 2187 = 895 ∨ core % 2187 = 1624 := by omega
    rcases h with e166 | e895 | e1624
    · omega
    · exact absurd e895 n895
    · omega
  · have h : core % 2187 = 193 ∨ core % 2187 = 922 ∨ core % 2187 = 1651 := by omega
    rcases h with e193 | e922 | e1651
    · omega
    · omega
    · exact absurd e1651 n1651
  · have h : core % 2187 = 199 ∨ core % 2187 = 928 ∨ core % 2187 = 1657 := by omega
    rcases h with e199 | e928 | e1657
    · exact absurd e199 n199
    · omega
    · omega
  · have h : core % 2187 = 244 ∨ core % 2187 = 973 ∨ core % 2187 = 1702 := by omega
    rcases h with e244 | e973 | e1702
    · omega
    · omega
    · exact absurd e1702 n1702
  · have h : core % 2187 = 247 ∨ core % 2187 = 976 ∨ core % 2187 = 1705 := by omega
    rcases h with e247 | e976 | e1705
    · omega
    · omega
    · exact absurd e1705 n1705
  · have h : core % 2187 = 274 ∨ core % 2187 = 1003 ∨ core % 2187 = 1732 := by omega
    rcases h with e274 | e1003 | e1732
    · exact absurd e274 n274
    · omega
    · omega
  · have h : core % 2187 = 280 ∨ core % 2187 = 1009 ∨ core % 2187 = 1738 := by omega
    rcases h with e280 | e1009 | e1738
    · omega
    · omega
    · exact absurd e1738 n1738
  · have h : core % 2187 = 283 ∨ core % 2187 = 1012 ∨ core % 2187 = 1741 := by omega
    rcases h with e283 | e1012 | e1741
    · omega
    · exact absurd e1012 n1012
    · omega
  · have h : core % 2187 = 325 ∨ core % 2187 = 1054 ∨ core % 2187 = 1783 := by omega
    rcases h with e325 | e1054 | e1783
    · omega
    · exact absurd e1054 n1054
    · omega
  · have h : core % 2187 = 361 ∨ core % 2187 = 1090 ∨ core % 2187 = 1819 := by omega
    rcases h with e361 | e1090 | e1819
    · omega
    · exact absurd e1090 n1090
    · omega
  · have h : core % 2187 = 364 ∨ core % 2187 = 1093 ∨ core % 2187 = 1822 := by omega
    rcases h with e364 | e1093 | e1822
    · omega
    · omega
    · exact absurd e1822 n1822
  · have h : core % 2187 = 415 ∨ core % 2187 = 1144 ∨ core % 2187 = 1873 := by omega
    rcases h with e415 | e1144 | e1873
    · exact absurd e415 n415
    · omega
    · omega
  · have h : core % 2187 = 436 ∨ core % 2187 = 1165 ∨ core % 2187 = 1894 := by omega
    rcases h with e436 | e1165 | e1894
    · omega
    · omega
    · exact absurd e1894 n1894
  · have h : core % 2187 = 442 ∨ core % 2187 = 1171 ∨ core % 2187 = 1900 := by omega
    rcases h with e442 | e1171 | e1900
    · exact absurd e442 n442
    · omega
    · omega
  · have h : core % 2187 = 496 ∨ core % 2187 = 1225 ∨ core % 2187 = 1954 := by omega
    rcases h with e496 | e1225 | e1954
    · omega
    · omega
    · exact absurd e1954 n1954
  · have h : core % 2187 = 499 ∨ core % 2187 = 1228 ∨ core % 2187 = 1957 := by omega
    rcases h with e499 | e1228 | e1957
    · exact absurd e499 n499
    · omega
    · omega
  · have h : core % 2187 = 514 ∨ core % 2187 = 1243 ∨ core % 2187 = 1972 := by omega
    rcases h with e514 | e1243 | e1972
    · omega
    · omega
    · exact absurd e1972 n1972
  · have h : core % 2187 = 517 ∨ core % 2187 = 1246 ∨ core % 2187 = 1975 := by omega
    rcases h with e517 | e1246 | e1975
    · exact absurd e517 n517
    · omega
    · omega
  · have h : core % 2187 = 523 ∨ core % 2187 = 1252 ∨ core % 2187 = 1981 := by omega
    rcases h with e523 | e1252 | e1981
    · omega
    · omega
    · exact absurd e1981 n1981
  · have h : core % 2187 = 580 ∨ core % 2187 = 1309 ∨ core % 2187 = 2038 := by omega
    rcases h with e580 | e1309 | e2038
    · omega
    · exact absurd e1309 n1309
    · omega
  · have h : core % 2187 = 595 ∨ core % 2187 = 1324 ∨ core % 2187 = 2053 := by omega
    rcases h with e595 | e1324 | e2053
    · omega
    · exact absurd e1324 n1324
    · omega
  · have h : core % 2187 = 604 ∨ core % 2187 = 1333 ∨ core % 2187 = 2062 := by omega
    rcases h with e604 | e1333 | e2062
    · omega
    · exact absurd e1333 n1333
    · omega
  · have h : core % 2187 = 652 ∨ core % 2187 = 1381 ∨ core % 2187 = 2110 := by omega
    rcases h with e652 | e1381 | e2110
    · exact absurd e652 n652
    · omega
    · omega
  · have h : core % 2187 = 658 ∨ core % 2187 = 1387 ∨ core % 2187 = 2116 := by omega
    rcases h with e658 | e1387 | e2116
    · exact absurd e658 n658
    · omega
    · omega

/-- **THE SHRUNK ROW INPUT, LEVEL SEVEN.**  The row primitive with all
seven lattice levels' fired classes removed: the residue clause now
demands one of the sixty-eight mod-2187 survivors. -/
def tailF_row_primitive_mod2187 : Prop :=
  ∀ core : Nat, 500 < core → ¬ 3 ∣ core →
    tailF_row_survivor_class_mod2187 core →
      ∃ j : Nat, 2 * 3^j ≤ (omegaCutWord 0 core) % 3^(j+1)

/-- **THE WEAKNESS RECEIPT, LEVEL SEVEN.**  The level-seven shrunk row
input is strictly weaker than the mod-729 one: every mod-2187 survivor
sits inside a mod-729 survivor class. -/
theorem tailF_row_primitive_mod2187_of_mod729 (h : tailF_row_primitive_mod729) :
    tailF_row_primitive_mod2187 := by
  intro core hK hfree hclass
  refine h core hK hfree ?_
  unfold tailF_row_survivor_class_mod2187 at hclass
  unfold tailF_row_survivor_class_mod729
  rcases hclass with h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h <;> omega

theorem tailF_row_primitive_mod2187_of_row (hRow : tailF_row_primitive) :
    tailF_row_primitive_mod2187 :=
  tailF_row_primitive_mod2187_of_mod729 (tailF_row_primitive_mod729_of_row hRow)

/-- **THE REPLACEMENT OF THE INPUT'S ROW HALF, LEVEL SEVEN.**  The tower
primitive plus the sixty-eight-survivor row primitive compose into the
full second-observer input. -/
theorem tailF_of_tower_and_row_mod2187
    (hTower : tailF_tower_primitive)
    (hRowMod : tailF_row_primitive_mod2187) :
    four_power_omega_shadow_wave_tailF := by
  intro K hK hshadow
  obtain ⟨s, core, hKsc, hfree, hres, hA, hB1, hB2, hC, hD⟩ := hshadow
  rcases Nat.eq_zero_or_pos s with rfl | hs1
  · have hc14 : core % 9 = 1 ∨ core % 9 = 4 := by
      rcases hres with h4 | ⟨_, h1⟩ | ⟨h1s, h7⟩
      · exact Or.inr h4
      · exact Or.inl h1
      · exact absurd h1s (by omega)
    rw [Nat.pow_zero, Nat.one_mul] at hKsc
    have hKc : 500 < core := by rw [← hKsc]; exact hK
    by_cases hf : s0_lattice_fire_class core
    · obtain ⟨p, hp⟩ := s0_lattice_fire core hf
      rw [hKsc]
      exact ⟨p, hp⟩
    · by_cases hf6 : s0_lattice_fire_class_mod729 core
      · obtain ⟨p, hp⟩ := s0_lattice_fire_mod729 core hf6
        rw [hKsc]
        exact ⟨p, hp⟩
      · by_cases hf7 : s0_lattice_fire_class_mod2187 core
        · obtain ⟨p, hp⟩ := s0_lattice_fire_mod2187 core hf7
          rw [hKsc]
          exact ⟨p, hp⟩
        · obtain ⟨j, hj⟩ := hRowMod core hKc hfree
            (tailF_row_survivor_mod2187_of_nonfire core hc14 hf hf6 hf7)
          refine ⟨1+j, ?_⟩
          rw [hKsc]
          exact omega_row_level_digit_two core j hj
  · have hc47 : core % 9 = 4 ∨ core % 9 = 7 := by
      rcases hres with h4 | ⟨hs0, h1⟩ | ⟨h1s', h7⟩
      · exact Or.inl h4
      · exact absurd hs0 (by omega)
      · exact Or.inr h7
    obtain ⟨i, _, hfire⟩ := hTower s core hs1 hfree hc47 hD
    refine ⟨s+1+i, ?_⟩
    rw [hKsc]
    exact tower_observation_digit_two s core i hfire

/-- **THE EVEN STATEMENT ON THE REPLACEMENT INPUT, LEVEL SEVEN.** -/
theorem even_conjecture_of_tower_and_row_mod2187
    (hB : erdos_even_conjecture_iff_tailF)
    (hTower : tailF_tower_primitive)
    (hRowMod : tailF_row_primitive_mod2187) :
    ∀ K : Nat, 8 ≤ K → noTernaryTwo (4^K) = false :=
  hB.mpr
    (tailF_of_tower_and_row_mod2187 hTower hRowMod)

/-- **THE CROWN ON THE REPLACEMENT INPUT, LEVEL SEVEN.** -/
theorem erdos_ternary_2_universal_of_tower_and_row_mod2187
    (hB : erdos_ternary_2_universal_of_tailF)
    (hTower : tailF_tower_primitive)
    (hRowMod : tailF_row_primitive_mod2187)
    (n : Nat) (hn : 9 ≤ n) :
    noTernaryTwo (2^n) = false :=
  hB
    (tailF_of_tower_and_row_mod2187 hTower hRowMod) n hn

#print axioms four_pow_mod6561
#print axioms digit3_pow4_pos7_of_class
#print axioms s0_lattice_fire_mod2187
#print axioms tailF_row_survivor_mod2187_of_nonfire
#print axioms tailF_row_primitive_mod2187_of_mod729
#print axioms tailF_row_primitive_mod2187_of_row
#print axioms tailF_of_tower_and_row_mod2187
#print axioms even_conjecture_of_tower_and_row_mod2187
#print axioms erdos_ternary_2_universal_of_tower_and_row_mod2187
/-! ## §9 The meta-view — every class, every case, every level, one law

The fourth dimension's own vantage point, assembled: the ignition
machinery of §3, §3b, and every deeper level of the ladder is ONE law,
uniform in the level index.  The fire predicate — the tower word of the
core sitting in the top third of its window at level `k` — is a single
decidable test on `(k, core)`; the uniform law converts it into the
primitive diagonal trit two at EVERY level; the descent blade then kills
the core's ENTIRE tower from that level upward.  The level-by-level grind
— the fourteen fire laws of §3 and §3b, the lattice levels of §§6-8, and
every level beyond them — is the INSIDE of this one law: each is an
instance, obtained by feeding the law one residue certificate.

The exact complement is the SURVIVOR DUST: the cores whose tower word
dodges the top third at every level from three upward — one predicate,
the whole dodge set of the cascade seen at once.  Every core outside the
dust is dead by machine: a fire exists, and the blade kills every sheet
from its level upward, in one statement.  The dust's own members are the
tower primitive's exact residual — §4's decomposition, the diagonal
restatement below, and the floor receipt of the proof file carry the full
map. -/

/-- **THE UNIFORM IGNITION — every level, every core, one law.**  Whenever
the level-`k` tower word of `core` — `omegaCutWord (k-1) 1 * core` — sits
in the top third of its window modulo `3^k`, the primitive diagonal fires:
`4^(3^(k-1) * core)` owns its ternary digit two at index `2k - 1`.
Unconditional and uniform in `k` and `core`: every fire law of §3, §3b,
and every deeper level of the ladder is an instance of this single
theorem. -/
theorem omega_diagonal_two_universal (k core : Nat) (hk : 1 ≤ k)
    (hfire : 2 * 3^(k-1) ≤ (omegaCutWord (k-1) 1 * core) % 3^k) :
    digit3 (4^(3^(k-1) * core)) (2*k - 1) = 2 := by
  have hobs := omega_observed_digit (k-1) core k (by omega) (by omega)
  rw [show (k-1) + k = 2*k - 1 from by omega] at hobs
  rw [hobs]
  have hpos : 0 < 3^(k-1) := Nat.pow_pos (by decide)
  have hlt : (omegaCutWord (k-1) 1 * core) % 3^k < 3^k :=
    Nat.mod_lt _ (Nat.pow_pos (by decide))
  have h3 : 3^k = 3 * 3^(k-1) := by
    obtain ⟨k', hk'⟩ : ∃ k', k = k' + 1 := ⟨k-1, by omega⟩
    subst hk'
    have hidx : k' + 1 - 1 = k' := by omega
    rw [hidx, Nat.pow_add, Nat.pow_one]
    ring
  obtain ⟨d, hd⟩ : ∃ d, (omegaCutWord (k-1) 1 * core) % 3^k
      = 2 * 3^(k-1) + d :=
    ⟨(omegaCutWord (k-1) 1 * core) % 3^k - 2 * 3^(k-1), by omega⟩
  have hdlt : d < 3^(k-1) := by omega
  rw [hd, Nat.add_comm, show 2 * 3^(k-1) = 3^(k-1) * 2 from by ring,
    Nat.add_mul_div_left _ _ hpos, Nat.div_eq_of_lt hdlt]

/-- **THE UNIFORM BLADE — one band test kills a whole tower.**  The
uniform ignition composed with the descent blade: for every level `k`,
every core, and every sheet `S` at or above `k-1`, the single band test
on the tower word delivers the power's ternary digit two at position
`S + k`.  All levels, all classes, all sheets — one law. -/
theorem omega_tower_digit_two_universal (k core S : Nat) (hk : 1 ≤ k)
    (hkS : k ≤ S+1)
    (hfire : 2 * 3^(k-1) ≤ (omegaCutWord (k-1) 1 * core) % 3^k) :
    digit3 (4^(3^S * core)) (S + k) = 2 :=
  omega_tower_kill_of_diagonal_two core k S hk hkS
    (omega_diagonal_two_universal k core hk hfire)

/-- **THE SURVIVOR DUST.**  The exact complement of the entire ignition
ladder, stated as one predicate on the core: the cores whose tower word
dodges the top third at EVERY level from three upward.  This is the dodge
set of the whole cascade — all classes and all levels — seen at once. -/
def omega_diagonal_survivor_dust (core : Nat) : Prop :=
  ∀ k : Nat, 3 ≤ k →
    (omegaCutWord (k-1) 1 * core) % 3^k < 2 * 3^(k-1)

/-- **THE DUST BOUNDARY, FIRE SIDE.**  Every core outside the dust fires
the primitive diagonal at some level: the uniform law's instance,
delivered by one decidable test. -/
theorem omega_diagonal_fire_of_not_dust (core : Nat)
    (h : ¬ omega_diagonal_survivor_dust core) :
    ∃ k : Nat, 3 ≤ k ∧
      digit3 (4^(3^(k-1) * core)) (2*k - 1) = 2 := by
  unfold omega_diagonal_survivor_dust at h
  push_neg at h
  obtain ⟨k, hk3, hfire⟩ := h
  exact ⟨k, hk3, omega_diagonal_two_universal k core (by omega) hfire⟩

/-- **THE DUST BOUNDARY, TOWER SIDE.**  Every core outside the dust has
its WHOLE tower dead by machine: every sheet from its first fire's level
upward owns the digit two, in one statement. -/
theorem omega_tower_dies_of_not_dust (core : Nat)
    (h : ¬ omega_diagonal_survivor_dust core) :
    ∃ k : Nat, 3 ≤ k ∧ ∀ S : Nat, k-1 ≤ S →
      digit3 (4^(3^S * core)) (S + k) = 2 := by
  obtain ⟨k, hk3, hfire⟩ := omega_diagonal_fire_of_not_dust core h
  refine ⟨k, hk3, ?_⟩
  intro S hS
  exact omega_tower_kill_of_diagonal_two core k S (by omega) (by omega)
    hfire

/-- **THE TOWER PRIMITIVE, READ AS THE DIAGONAL.**  Through the descent
chain, the tower primitive's window dodge IS the all-window diagonal
dodge of the core: the tower family's entire carried content, restated as
one statement about the emergent axis.  The two named primitives of §4 —
the whole carried content of the input — now read: the row family's word
fires, and every diagonal-dodging tower's own word fires in its deep
tail. -/
theorem tailF_tower_primitive_iff_diagonal :
    tailF_tower_primitive ↔
      ∀ s core : Nat, 1 ≤ s → ¬ 3 ∣ core →
        (core % 9 = 4 ∨ core % 9 = 7) →
        (∀ k : Nat, 3 ≤ k → k ≤ s+1 →
          (omegaCutWord (k-1) 1 * core) % 3^k < 2 * 3^(k-1)) →
          ∃ i : Nat, s+2 ≤ i ∧
            2 * 3^i ≤ (omegaCutWord s core) % 3^(i+1) := by
  constructor
  · intro h s core hs hfree hres hDdiag
    refine h s core hs hfree hres ?_
    intro k hk3 hks
    rw [omega_tower_word_mod_chain core k s (by omega)]
    exact hDdiag k hk3 hks
  · intro h s core hs hfree hres hDwin
    refine h s core hs hfree hres ?_
    intro k hk3 hks
    rw [← omega_tower_word_mod_chain core k s (by omega)]
    exact hDwin k hk3 hks

/-- **SUBSUMPTION RECEIPT, LEVEL TWO.**  The class-one ignition of §3 is
one instance of the uniform law: the residue test delivers the band
condition, the uniform law delivers the fire. -/
theorem omega_diagonal_two_of_mod_nine_one_from_universal (core : Nat)
    (h : core % 9 = 1) :
    digit3 (4^(3^(2-1) * core)) (2*2 - 1) = 2 :=
  omega_diagonal_two_universal 2 core (by decide)
    (by
      have hw : omegaCutWord 1 1 = 7 := by
        have h2 := omega_cut_factor 1 1
        norm_num [Nat.pow_succ, Nat.pow_zero] at h2
        omega
      have hidx : (2:Nat) - 1 = 1 := by omega
      rw [hidx, hw]
      have h9 : (3:Nat)^2 = 9 := by norm_num
      have h31 : (3:Nat)^1 = 3 := by norm_num
      rw [h9, h31]
      omega)

/-- **SUBSUMPTION RECEIPT, LEVEL FOUR.**  The mod-81 four ignition of §3b
is one instance of the same uniform law — the deep bands are inside it
too. -/
theorem omega_diagonal_two_of_mod81_four_from_universal (core : Nat)
    (h : core % 81 = 4) :
    digit3 (4^(3^(4-1) * core)) (2*4 - 1) = 2 :=
  omega_diagonal_two_universal 4 core (by decide)
    (by
      have hw : omegaCutWord 3 1 = 222399981598543 := by
        have h2 := omega_cut_factor 3 1
        norm_num [Nat.pow_succ, Nat.pow_zero] at h2
        omega
      have hidx : (4:Nat) - 1 = 3 := by omega
      rw [hidx, hw]
      have h81 : (3:Nat)^4 = 81 := by norm_num
      have h27 : (3:Nat)^3 = 27 := by norm_num
      rw [h81, h27]
      omega)

#print axioms omega_diagonal_two_universal
#print axioms omega_tower_digit_two_universal
#print axioms omega_diagonal_survivor_dust
#print axioms omega_diagonal_fire_of_not_dust
#print axioms omega_tower_dies_of_not_dust
#print axioms tailF_tower_primitive_iff_diagonal
#print axioms omega_diagonal_two_of_mod_nine_one_from_universal
#print axioms omega_diagonal_two_of_mod81_four_from_universal

/-! ## §7c The wave engine — the cube lift, exact — one lane, all sheets

The engine of the whole cascade, exposed as a named law: the cut word of
sheet level `s+1` is the cut word of level `s` plus `3^(s+1)` times
`(W^2 + 3^s · W^3)` — the EXACT cube lift, no existential remainder.  The
stabilization law of §2 said `∃ t`; the engine names `t`.  From it: the
**+1 lift law** — for every three-free core, whenever the sheet's own
window trit is `w`, the next frozen diagonal trit is `w + 1` — and its two
children: the **three-window dichotomy** (every sheet of every three-free
core either FIRES its own digit two at position `2s+2`, or DODGES with
window trit zero, or ESCALATES — window trit one, and the descent blade
kills every sheet above at once), and the **escalation law** (a core whose
windows all dodge can never park its diagonal in the bottom third — with
the dust hypothesis, the dust's exact shape is the MIDDLE THIRD at every
level from three upward).  All sheets, all rows, all towers: one lane. -/

/-- The cut word's zeroth trit is the core's residue: the LTE mean is one
modulo three and the geometric mean is the core modulo three. -/
theorem omega_cut_word_mod3 (s core : Nat) :
    omegaCutWord s core % 3 = core % 3 := by
  rw [omegaCutWord, Nat.mul_mod, lteCoeff_mod3_one, omega_geo_mod3,
    Nat.one_mul]
  omega

/-- **THE WAVE ENGINE — the exact cube lift.**  For every sheet level `s`
and every core, the cut word of the next sheet is the cut word of this
sheet plus exactly `3^(s+1)` times `(W^2 + 3^s · W^3)` where `W` is this
sheet's own cut word.  No existential remainder: the whole cascade of
sheets is this one recursion, seen at once. -/
theorem omega_cut_word_cube_lift_exact (s core : Nat) :
    omegaCutWord (s+1) core
      = omegaCutWord s core
        + 3^(s+1) * (omegaCutWord s core * omegaCutWord s core
          + 3^s * (omegaCutWord s core * omegaCutWord s core
            * omegaCutWord s core)) := by
  have hf0 := omega_cut_factor s core
  have hf1 := omega_cut_factor (s+1) core
  have hpow : 4^(3^(s+1) * core) = (4^(3^s * core))^3 := by
    rw [show 3^(s+1) * core = (3^s * core) * 3 from by
          rw [Nat.pow_succ]; ring,
        Nat.pow_mul]
  have hcube : (1 + 3^(s+1) * omegaCutWord s core)^3
      = 1 + 3^(s+2) * (omegaCutWord s core
          + 3^(s+1) * (omegaCutWord s core * omegaCutWord s core
            + 3^s * (omegaCutWord s core * omegaCutWord s core
              * omegaCutWord s core))) := by
    rw [show 3^(s+2) = 9 * 3^s from by
          rw [show s+2 = (s+1)+1 from by omega, Nat.pow_succ, Nat.pow_succ]
          ring,
        show 3^(s+1) = 3 * 3^s from by rw [Nat.pow_succ]; ring]
    ring
  have hE : 4^(3^(s+1) * core)
      = 1 + 3^(s+2) * (omegaCutWord s core
          + 3^(s+1) * (omegaCutWord s core * omegaCutWord s core
            + 3^s * (omegaCutWord s core * omegaCutWord s core
              * omegaCutWord s core))) := by
    rw [hpow, hf0]
    exact hcube
  have hAB : 3^(s+2) * omegaCutWord (s+1) core
      = 3^(s+2) * (omegaCutWord s core
          + 3^(s+1) * (omegaCutWord s core * omegaCutWord s core
            + 3^s * (omegaCutWord s core * omegaCutWord s core
              * omegaCutWord s core))) :=
    Nat.add_left_cancel (hf1.symm.trans hE)
  exact Nat.eq_of_mul_eq_mul_left (Nat.pow_pos (by decide)) hAB

/-- **THE +1 LIFT LAW — the diagonal's advance.**  For every sheet from
one onward and every three-free core, the next sheet's cut word is this
sheet's cut word plus exactly ONE unit of the sheet's own modulus,
modulo `3^(s+2)`: the square of a three-free word is one modulo three,
so the engine's increment is exactly `3^(s+1)`.  The frozen diagonal
trit at depth `s+1` is the sheet's own window trit plus one. -/
theorem omega_cut_word_lift_one (s core : Nat) (hs : 1 ≤ s)
    (hfree : core % 3 = 1 ∨ core % 3 = 2) :
    omegaCutWord (s+1) core % 3^(s+2)
      = (omegaCutWord s core + 3^(s+1)) % 3^(s+2) := by
  have hmod3 : omegaCutWord s core % 3 = 1 ∨ omegaCutWord s core % 3 = 2 := by
    rw [omega_cut_word_mod3]
    exact hfree
  have hsq : (omegaCutWord s core * omegaCutWord s core) % 3 = 1 := by
    rcases hmod3 with h | h <;> rw [Nat.mul_mod, h] <;> norm_num
  obtain ⟨u, hu⟩ : ∃ u : Nat,
      omegaCutWord s core * omegaCutWord s core = 1 + 3 * u := by
    refine ⟨(omegaCutWord s core * omegaCutWord s core - 1) / 3, ?_⟩
    omega
  have heng := omega_cut_word_cube_lift_exact s core
  have hp1 : 3^(s+1) * 3^s = 3^(s+2) * 3^(s-1) := by
    rw [← Nat.pow_add, ← Nat.pow_add]
    have he : (s+1) + s = (s+2) + (s-1) := by omega
    rw [he]
  have hp2 : 3^(s+2) = 3 * 3^(s+1) := by
    rw [show s+2 = (s+1)+1 from by omega, Nat.pow_succ]
    ring
  have hAB2 : 3^(s+1) * (omegaCutWord s core * omegaCutWord s core
      + 3^s * (omegaCutWord s core * omegaCutWord s core
        * omegaCutWord s core))
      = 3^(s+1) + 3^(s+2) * (u + 3^(s-1)
        * (omegaCutWord s core * omegaCutWord s core
          * omegaCutWord s core)) := by
    have hA : 3^(s+1) * (omegaCutWord s core * omegaCutWord s core)
        = 3^(s+1) + 3^(s+2) * u := by
      rw [hu, hp2]
      ring
    rw [Nat.mul_add, hA,
      ← Nat.mul_assoc (3^(s+1)) (3^s) (omegaCutWord s core * omegaCutWord s core
        * omegaCutWord s core),
      hp1]
    ring
  obtain ⟨v, hv⟩ : ∃ v : Nat, omegaCutWord (s+1) core
      = omegaCutWord s core + 3^(s+1) + 3^(s+2) * v := by
    refine ⟨u + 3^(s-1) * (omegaCutWord s core * omegaCutWord s core
      * omegaCutWord s core), ?_⟩
    rw [heng, hAB2]
    ring
  rw [hv]
  have hz : (3^(s+2) * v) % 3^(s+2) = 0 := Nat.mod_eq_zero_of_dvd ⟨v, rfl⟩
  rw [Nat.add_mod, hz, Nat.add_zero, Nat.mod_mod]

/-- **THE THREE-WINDOW DICHOTOMY — fire, dodge, or escalate.**  Every
sheet `s ≥ 1` of every three-free core, read through its own window
`omegaCutWord s core % 3^(s+2)`: either the window sits in the TOP third
and the power `4^(3^s * core)` owns its ternary digit two at position
`2*s+2` outright; or the window sits in the BOTTOM third (the dodge,
window trit zero); or the window sits in the MIDDLE third — window trit
one — and then the `+1` lift makes the next diagonal trit two, and the
descent blade kills EVERY sheet `S ≥ s+1` at once.  All sheets, all
cores: three windows, one law. -/
theorem omega_sheet_window_dichotomy (s core : Nat) (hs : 1 ≤ s)
    (hfree : core % 3 = 1 ∨ core % 3 = 2) :
    (2 * 3^(s+1) ≤ (omegaCutWord s core) % 3^(s+2)
      ∧ digit3 (4^(3^s * core)) (2*s+2) = 2)
    ∨ (omegaCutWord s core) % 3^(s+2) < 3^(s+1)
    ∨ (3^(s+1) ≤ (omegaCutWord s core) % 3^(s+2)
      ∧ (omegaCutWord s core) % 3^(s+2) < 2 * 3^(s+1)
      ∧ ∀ S : Nat, s+1 ≤ S → digit3 (4^(3^S * core)) (S + (s+2)) = 2) := by
  have hp3 : 3^(s+2) = 3 * 3^(s+1) := by
    rw [show s+2 = (s+1)+1 from by omega, Nat.pow_succ]
    ring
  have hpos : 0 < 3^(s+1) := Nat.pow_pos (by decide)
  have h3lt : 3^(s+1) < 3^(s+2) := by omega
  by_cases h1 : 2 * 3^(s+1) ≤ (omegaCutWord s core) % 3^(s+2)
  · refine Or.inl ⟨h1, ?_⟩
    have hobs := tower_observation_digit_two s core (s+1) h1
    have hidx : s+1+(s+1) = 2*s+2 := by omega
    rw [hidx] at hobs
    exact hobs
  · push_neg at h1
    by_cases h2 : 3^(s+1) ≤ (omegaCutWord s core) % 3^(s+2)
    · have hlift := omega_cut_word_lift_one s core hs hfree
      have hmodsum : (omegaCutWord s core) % 3^(s+2) + 3^(s+1) < 3^(s+2) := by
        omega
      have hmod : (omegaCutWord s core + 3^(s+1)) % 3^(s+2)
          = (omegaCutWord s core) % 3^(s+2) + 3^(s+1) := by
        rw [Nat.add_mod, Nat.mod_eq_of_lt h3lt]
        exact Nat.mod_eq_of_lt hmodsum
      have hkill' : 2 * 3^(s+1) ≤ (omegaCutWord (s+1) core) % 3^(s+2) := by
        rw [hlift, hmod]
        omega
      have hobs := tower_observation_digit_two (s+1) core (s+1) hkill'
      have hidx : (s+1)+1+(s+1) = 2*(s+2)-1 := by omega
      rw [hidx] at hobs
      refine Or.inr (Or.inr ⟨h2, ?_, ?_⟩)
      · omega
      · intro S hS
        exact omega_tower_kill_of_diagonal_two core (s+2) S
          (by omega) (by omega) hobs
    · push_neg at h2
      exact Or.inr (Or.inl h2)

/-- **NONBOTTOM RIGIDITY.**
For a three-free core, if a sheet is not in the bottom third and does not fire
immediately, then the middle-third branch is forced and every later sheet
fires at the synchronized diagonal offset. -/
theorem omega_nonbottom_nonfire_forces_future_fire
    (s core : Nat) (hs : 1 ≤ s)
    (hfree : core % 3 = 1 ∨ core % 3 = 2)
    (hbottom : 3^(s+1) ≤ (omegaCutWord s core) % 3^(s+2))
    (hnow : digit3 (4^(3^s * core)) (2*s+2) ≠ 2) :
    ∀ S : Nat, s+1 ≤ S →
      digit3 (4^(3^S * core)) (S + (s+2)) = 2 := by
  rcases omega_sheet_window_dichotomy s core hs hfree with
    htop | hlow | hmid
  · exact False.elim (hnow htop.2)
  · omega
  · exact hmid.2.2

/-- **TWO-SHEET SILENCE FORCES BOTTOM DODGE.**
If the current synchronized observation does not fire and at least one later
sheet also avoids the forced synchronized fire, then the present window must
lie in the bottom third. -/
theorem omega_two_sheet_silence_forces_bottom
    (s core : Nat) (hs : 1 ≤ s)
    (hfree : core % 3 = 1 ∨ core % 3 = 2)
    (hnow : digit3 (4^(3^s * core)) (2*s+2) ≠ 2)
    (hlater : ∃ S : Nat, s+1 ≤ S ∧
      digit3 (4^(3^S * core)) (S + (s+2)) ≠ 2) :
    (omegaCutWord s core) % 3^(s+2) < 3^(s+1) := by
  by_contra hnot
  push_neg at hnot
  obtain ⟨S,hS,hSnot⟩ := hlater
  have hall :=
    omega_nonbottom_nonfire_forces_future_fire
      s core hs hfree hnot hnow
  exact hSnot (hall S hS)

/-- Every nonbottom window has an exact dynamical alternative: immediate fire
or synchronized permanent future fire. -/
theorem omega_nonbottom_fire_or_permanent_future
    (s core : Nat) (hs : 1 ≤ s)
    (hfree : core % 3 = 1 ∨ core % 3 = 2)
    (hbottom : 3^(s+1) ≤ (omegaCutWord s core) % 3^(s+2)) :
    digit3 (4^(3^s * core)) (2*s+2) = 2
    ∨
    (∀ S : Nat, s+1 ≤ S →
      digit3 (4^(3^S * core)) (S + (s+2)) = 2) := by
  by_cases hnow : digit3 (4^(3^s * core)) (2*s+2) = 2
  · exact Or.inl hnow
  · exact Or.inr
      (omega_nonbottom_nonfire_forces_future_fire
        s core hs hfree hbottom hnow)

/-- Dynamical crown of the three-window law: the nonbottom region has no
long-lived silent phase. -/
theorem omega_window_rigidity_crown :
    (∀ s core, 1 ≤ s →
      (core % 3 = 1 ∨ core % 3 = 2) →
      3^(s+1) ≤ (omegaCutWord s core) % 3^(s+2) →
      digit3 (4^(3^s * core)) (2*s+2) ≠ 2 →
      ∀ S, s+1 ≤ S →
        digit3 (4^(3^S * core)) (S + (s+2)) = 2)
    ∧
    (∀ s core, 1 ≤ s →
      (core % 3 = 1 ∨ core % 3 = 2) →
      digit3 (4^(3^s * core)) (2*s+2) ≠ 2 →
      (∃ S, s+1 ≤ S ∧
        digit3 (4^(3^S * core)) (S + (s+2)) ≠ 2) →
      (omegaCutWord s core) % 3^(s+2) < 3^(s+1)) := by
  exact ⟨omega_nonbottom_nonfire_forces_future_fire,
    omega_two_sheet_silence_forces_bottom⟩

/-- **THE ESCALATION LAW — a dodging core never parks its diagonal in the
bottom third.**  If every sheet `s ≥ 1` of a three-free core dodges its
own window (the shadow package's clause A, all sheets at once), then at
every level `k ≥ 3` the scaled diagonal `omegaCutWord (k-1) 1 * core`
sits at or above the middle of its window: the `+1` lift advances the
frozen diagonal one full trit per sheet, and a window-dodging sheet
advances from zero, one, never from minus one.  The window dodge feeds
the diagonal; the diagonal cannot hide low. -/
theorem omega_window_dodge_escalates (core : Nat)
    (hfree : core % 3 = 1 ∨ core % 3 = 2)
    (hwin : ∀ s : Nat, 1 ≤ s →
      (omegaCutWord s core) % 3^(s+2) < 2 * 3^(s+1)) :
    ∀ k : Nat, 3 ≤ k →
      3^(k-1) ≤ (omegaCutWord (k-1) 1 * core) % 3^k := by
  intro k hk
  have hk2 : 1 ≤ k-2 := by omega
  have hwin' := hwin (k-2) hk2
  rw [show (k-2)+2 = k from by omega,
      show (k-2)+1 = k-1 from by omega] at hwin'
  have hlift := omega_cut_word_lift_one (k-2) core hk2 hfree
  rw [show (k-2)+1 = k-1 from by omega,
      show (k-2)+2 = k from by omega] at hlift
  obtain ⟨t, ht⟩ := omega_cut_word_linear (k-1) core
  rw [show (k-1)+1 = k from by omega] at ht
  have hp3 : 3^k = 3 * 3^(k-1) := by
    obtain ⟨t, ht⟩ : ∃ t : Nat, k = t + 1 := ⟨k-1, by omega⟩
    rw [ht, show t+1-1 = t from by omega, Nat.pow_succ]
    ring
  have h3lt : 3^(k-1) < 3^k := by
    have hpos : 0 < 3^(k-1) := Nat.pow_pos (by decide)
    omega
  have hmod : (omegaCutWord (k-2) core + 3^(k-1)) % 3^k
      = (omegaCutWord (k-2) core) % 3^k + 3^(k-1) := by
    rw [Nat.add_mod, Nat.mod_eq_of_lt h3lt]
    have hsum : (omegaCutWord (k-2) core) % 3^k + 3^(k-1) < 3^k := by omega
    exact Nat.mod_eq_of_lt hsum
  have hmods : (omegaCutWord (k-1) 1 * core) % 3^k
      = (omegaCutWord (k-1) core) % 3^k := by
    rw [ht, Nat.add_mod]
    have hz : (3^k * t) % 3^k = 0 := Nat.mod_eq_zero_of_dvd ⟨t, rfl⟩
    rw [hz, Nat.add_zero, Nat.mod_mod]
  rw [hmods, hlift, hmod]
  omega

/-- **THE DUST'S SHAPE.**  A three-free core whose sheets all dodge their
windows AND whose diagonal dodges the fire band at every level from three
upward (the survivor dust) parks its scaled diagonal in the EXACT middle
third of every window: never the bottom third (the escalation law), never
the top third (the dust).  The dust is not a fog — it is a sharply pinned
configuration: window trit zero at every sheet, diagonal trit one at
every level. -/
theorem omega_dust_shape_middle_third (core : Nat)
    (hfree : core % 3 = 1 ∨ core % 3 = 2)
    (hwin : ∀ s : Nat, 1 ≤ s →
      (omegaCutWord s core) % 3^(s+2) < 2 * 3^(s+1))
    (hdust : ∀ k : Nat, 3 ≤ k →
      (omegaCutWord (k-1) 1 * core) % 3^k < 2 * 3^(k-1)) :
    ∀ k : Nat, 3 ≤ k →
      3^(k-1) ≤ (omegaCutWord (k-1) 1 * core) % 3^k
        ∧ (omegaCutWord (k-1) 1 * core) % 3^k < 2 * 3^(k-1) := by
  intro k hk
  exact ⟨omega_window_dodge_escalates core hfree hwin k hk, hdust k hk⟩

#print axioms omega_cut_word_mod3
#print axioms omega_cut_word_cube_lift_exact
#print axioms omega_cut_word_lift_one
#print axioms omega_sheet_window_dichotomy
#print axioms omega_nonbottom_nonfire_forces_future_fire
#print axioms omega_two_sheet_silence_forces_bottom
#print axioms omega_nonbottom_fire_or_permanent_future
#print axioms omega_window_rigidity_crown
#print axioms omega_window_dodge_escalates
#print axioms omega_dust_shape_middle_third

end GSTTailFFourthDimension
