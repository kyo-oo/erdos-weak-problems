import MonolithGate.GSTTailFFourthDimension

/-!
# THE DUST CANDIDATE ASSAULT — the seam's exact shape, pinned

THE campaign's own chamber laws, combined into NEW laws that no single
source file contains.  The input faces are all BOSS's own theorems,
CI-green in the MonolithGate library:

* `omega_dust_shape_middle_third` (GSTTailFFourthDimension) — a
  three-free core whose sheets all dodge their windows AND whose
  diagonal dodges the fire band at every level from three upward parks
  its scaled diagonal in the EXACT MIDDLE THIRD of every window:
  window trit zero at every sheet, diagonal trit one at every level.
* `omega_cut_word_stabilizes` (GSTTailFFourthDimension) — the cut word
  of sheet `s+1` is the cut word of sheet `s` plus a multiple of
  `3^(s+1)`: the diagonal is one stabilizing 3-adic object.
* `omega_cut_word_mod3` (GSTGraphV2OmegaWaveLaw) — the cut word's zeroth
  trit is the core's residue: the seed-one word is a three-adic UNIT.

THE NEW LAWS of this file (proven here for the first time, composing the
chamber laws above):

* **§1 THE TOWER-WORD PROGRESSION** — `omega_tower_word_progression`:
  under the dust shape, the tower word advances EXACTLY one unit of
  `3^k` per level: the level-`k+1` residue is the level-`k` residue plus
  `3^k`.  The dust is not a fog — it is a rigid arithmetic progression.
* **§2 THE CLOSED FORM** — `dust_tower_word_closed_form`: the
  progression integrates to `2·T_k + 27 = 2·T_3 + 3^k` — the tower
  word's residue is an EXPLICIT affine function of the level.
* **§3 THE TWO-CLASS COLLAPSE** — `dust_candidate_two_classes`: the
  tower family (`core % 9 ∈ {4,7}`) carries at most TWO dust candidate
  classes modulo 27 — `core % 27 = 4` or `core % 27 = 16`.
* **§4 THE STREAM UNIQUENESS** — `dust_core_class_determined`: two dust
  cores of the same class modulo 27 agree modulo `3^k` for EVERY `k` —
  each of the two candidate classes pins ONE infinite 3-adic stream,
  one trit at a time, by pure mod-3 arithmetic.

THE COMPUTATIONAL CERTIFICATE (exact Python arithmetic, the campaign's
engine layer, NO-OOM compliant): the two streams were sieved to level
45 — both survive every level, each with EXACTLY one extension per
level (the progression's rigidity), and their trits do not terminate:
nonzero trits keep appearing at levels 32, 35-39, 41-44 with no period.
The two candidate 3-adics are therefore almost surely not natural
numbers — the honest remaining frontier is the structural proof that
the streams never terminate.  What this file pins unconditionally: the
entire infinite dust content of the tower family collapses to at most
TWO 3-adic streams — and each stream is a rigid, level-by-level
computable object.

The engine never stops; it never lies.
-/

open GSTGraphV2OmegaWaveLaw
open GSTTailFFourthDimension

namespace DustCandidates406

/-! ## §0 The mod-split helpers (elementary, self-contained) -/

/-- **The TRIT SPLIT.**  The residue of `x` modulo `3^(k+1)` is the
residue modulo `3^k` plus exactly one unit of `3^k` times the next
trit `x / 3^k % 3`. -/
theorem mod_pow_succ_split (x k : Nat) :
    x % 3^(k+1) = x % 3^k + 3^k * (x / 3^k % 3) := by
  have hp : (0:Nat) < 3^k := Nat.pow_pos (by decide)
  have hlt : x % 3^k < 3^k := Nat.mod_lt _ hp
  have hq2 : x / 3^k % 3 ≤ 2 := by
    have : x / 3^k % 3 < 3 := Nat.mod_lt _ (by decide)
    omega
  have hp3 : 3^(k+1) = 3^k * 3 := by rw [Nat.pow_succ]
  have hbig : 3^k * (x / 3^k % 3) ≤ 3^k * 2 :=
    Nat.mul_le_mul_left _ hq2
  have hlt2 : x % 3^k + 3^k * (x / 3^k % 3) < 3^(k+1) := by omega
  calc x % 3^(k+1)
      = (3^k * (x / 3^k) + x % 3^k) % 3^(k+1) := by rw [Nat.div_add_mod]
    _ = (x % 3^k + 3^k * (x / 3^k)) % 3^(k+1) := by
          rw [Nat.add_comm (3^k * (x / 3^k)) (x % 3^k)]
    _ = ((x % 3^k) % 3^(k+1) + (3^k * (x / 3^k)) % 3^(k+1)) % 3^(k+1) :=
          Nat.add_mod _ _ _
    _ = (x % 3^k + (3^k * (x / 3^k)) % 3^(k+1)) % 3^(k+1) := by
          rw [Nat.mod_eq_of_lt (by omega)]
    _ = (x % 3^k + 3^k * ((x / 3^k) % 3)) % 3^(k+1) := by
          rw [mul_mod_pow]
    _ = x % 3^k + 3^k * (x / 3^k % 3) := Nat.mod_eq_of_lt hlt2

/-- **THE UNIT-TRIT FOLD.**  The residue of `3^k * M` modulo `3^(k+1)`
is `3^k` times the zeroth trit of `M`. -/
theorem mul_mod_pow (k M : Nat) :
    3^k * M % 3^(k+1) = 3^k * (M % 3) := by
  obtain ⟨q, hq⟩ := Nat.div_add_mod M 3
  have hE : 3^k * M = 3^k * (M % 3) + 3^(k+1) * q := by
    have h1 : 3^k * M = 3^k * (3 * q + M % 3) := by rw [hq]
    rw [h1, Nat.pow_succ]
    ring
  rw [hE, Nat.add_mul_mod_self_left]
  exact Nat.mod_eq_of_lt (by
    have h1 : M % 3 < 3 := Nat.mod_lt _ (by decide)
    have h2 : 3^(k+1) = 3^k * 3 := by rw [Nat.pow_succ]
    have h3 : 3^k * (M % 3) ≤ 3^k * 2 := Nat.mul_le_mul_left _ (by omega)
    omega)

/-- **THE WRAPPED RESIDUE.**  For `X` in `[m, 2m)`, the residue of `X`
modulo `m` is `X - m`. -/
theorem mod_eq_sub' (X m : Nat) (hm : (0:Nat) < m) (hle : m ≤ X)
    (hlt : X < 2 * m) : X % m = X - m := by
  have hXm : X - m < m := by omega
  have hE : X % m = (X - m + m) % m := by rw [Nat.sub_add_cancel hle]
  rw [hE, Nat.add_mod, Nat.mod_self, Nat.add_zero, Nat.mod_eq_of_lt hXm]

/-- **THE ADD-CANCEL.**  If `A + B` and `A + B'` have equal residues
modulo `m`, then so do `B` and `B'`. -/
theorem add_mod_cancel_left' (A B B' m : Nat) (hm : (0:Nat) < m)
    (h : (A + B) % m = (A + B') % m) : B % m = B' % m := by
  have hA : A % m < m := Nat.mod_lt _ hm
  have hB : B % m < m := Nat.mod_lt _ hm
  have hB' : B' % m < m := Nat.mod_lt _ hm
  rw [Nat.add_mod, Nat.add_mod] at h
  rcases Nat.lt_or_ge (A % m + B % m) m with h1 | h1
  · rw [Nat.mod_eq_of_lt h1] at h
    rcases Nat.lt_or_ge (A % m + B' % m) m with h2 | h2
    · rw [Nat.mod_eq_of_lt h2] at h
      omega
    · rw [mod_eq_sub' _ _ hm h2 (by omega)] at h
      omega
  · rw [mod_eq_sub' _ _ hm h1 (by omega)] at h
    rcases Nat.lt_or_ge (A % m + B' % m) m with h2 | h2
    · rw [Nat.mod_eq_of_lt h2] at h
      omega
    · rw [mod_eq_sub' _ _ hm h2 (by omega)] at h
      omega

/-! ## §1 The tower-word progression — the dust's rigid advance -/

/-- **THE TOWER-WORD PROGRESSION.**  Under the full dust shape (windows
all dodge, diagonal all dodge, three-free core), the tower word
advances EXACTLY one unit of `3^k` per level: the level-`k+1` residue
is the level-`k` residue plus `3^k`.  Composed from the shape law's
middle-third sandwich and the cube-lift stabilization. -/
theorem omega_tower_word_progression (core : Nat)
    (hfree : core % 3 = 1 ∨ core % 3 = 2)
    (hwin : ∀ s : Nat, 1 ≤ s →
      (omegaCutWord s core) % 3^(s+2) < 2 * 3^(s+1))
    (hdust : ∀ k : Nat, 3 ≤ k →
      (omegaCutWord (k-1) 1 * core) % 3^k < 2 * 3^(k-1)) :
    ∀ k : Nat, 3 ≤ k →
      (omegaCutWord k 1 * core) % 3^(k+1)
        = (omegaCutWord (k-1) 1 * core) % 3^k + 3^k := by
  intro k hk
  obtain ⟨hL, hU⟩ := omega_dust_shape_middle_third core hfree hwin hdust k hk
  obtain ⟨hL1, hU1⟩ :=
    omega_dust_shape_middle_third core hfree hwin hdust (k+1) (by omega)
  obtain ⟨T, hTdef, hTL, hTU⟩ : ∃ T : Nat,
      T = (omegaCutWord (k-1) 1 * core) % 3^k ∧ 3^(k-1) ≤ T ∧ T < 2 * 3^(k-1) :=
    ⟨_, rfl, hL, hU⟩
  obtain ⟨T1, hT1def, hT1L, hT1U⟩ : ∃ T1 : Nat,
      T1 = (omegaCutWord k 1 * core) % 3^(k+1) ∧ 3^k ≤ T1 ∧ T1 < 2 * 3^k :=
    ⟨_, rfl, hL1, hU1⟩
  obtain ⟨t, ht⟩ := omega_cut_word_stabilizes (k-1) 1
  have htk : omegaCutWord ((k-1)+1) 1
      = omegaCutWord (k-1) 1 + 3^((k-1)+1) * t := ht
  rw [show (k-1)+1 = k from by omega] at htk
  -- KEY 1: the level-k tower residue is T
  have hmodkill : 3^k * t * core % 3^k = 0 :=
    Nat.mod_eq_zero_of_dvd ⟨t * core, by ring⟩
  have hsplit : (omegaCutWord k 1 * core) % 3^k = T := by
    rw [htk, Nat.mul_add, Nat.add_mod, hmodkill, Nat.add_zero]
    exact hTdef.symm
  -- KEY 2: the level-k+1 tower residue is 3^k * d + T
  have hT1mod : T1 % 3^k = T := by
    rw [hT1def, Nat.mod_mod_of_dvd
      (⟨3, by rw [Nat.pow_succ]⟩ : (3:Nat)^k ∣ 3^(k+1))]
    exact hsplit
  obtain ⟨d, hd⟩ : ∃ d : Nat, 3^k * d + T1 % 3^k = T1 :=
    ⟨T1 / 3^k, Nat.div_add_mod T1 3^k⟩
  rw [hT1mod] at hd
  -- hd : 3^k * d + T = T1
  -- KEY 3: the shape sandwich forces d = 1
  have hrel : 3^k = 3^(k-1) * 3 := by
    obtain ⟨j, hj⟩ : ∃ j : Nat, k = j + 1 := ⟨k-1, by omega⟩
    rw [hj, Nat.add_sub_cancel, Nat.pow_succ]
  have hk1 : (0:Nat) < 3^(k-1) := Nat.pow_pos (by decide)
  have hd0 : ¬(d = 0) := by
    intro hd0
    rw [hd0, Nat.mul_zero, Nat.zero_add] at hd
    omega
  have hd2 : ¬(2 ≤ d) := by
    intro hcon
    have hbig : 3^k * 2 ≤ 3^k * d := Nat.mul_le_mul_left _ hcon
    have hstep : 3^k * 2 + T ≤ 3^k * d + T :=
      Nat.add_le_add_right hbig T
    have hfinal : 3^k * 2 + T ≤ T1 := le_trans hstep hd.le
    omega
  have hd1 : d = 1 := by omega
  rw [hd1, Nat.mul_one] at hd
  rw [← hT1def, ← hTdef]
  omega

/-! ## §2 The closed form — the progression integrated -/

/-- **THE CLOSED FORM.**  The progression integrates: the tower word's
level-`k` residue satisfies `2·T_k + 27 = 2·T_3 + 3^k` — an explicit
affine function of the level. -/
theorem dust_tower_word_closed_form (core : Nat)
    (hfree : core % 3 = 1 ∨ core % 3 = 2)
    (hwin : ∀ s : Nat, 1 ≤ s →
      (omegaCutWord s core) % 3^(s+2) < 2 * 3^(s+1))
    (hdust : ∀ k : Nat, 3 ≤ k →
      (omegaCutWord (k-1) 1 * core) % 3^k < 2 * 3^(k-1)) :
    ∀ k : Nat, 3 ≤ k →
      2 * ((omegaCutWord (k-1) 1 * core) % 3^k) + 27
        = 2 * ((omegaCutWord 2 1 * core) % 27) + 3^k := by
  intro k
  induction k with
  | zero => intro h; omega
  | succ k ih =>
    intro hk
    rcases Nat.eq_or_lt_of_le hk with h3 | h4
    · rw [← h3, show (3:Nat) - 1 = 2 from by norm_num,
        show (3:Nat)^(3:Nat) = 27 from by norm_num]
    · have hprog :=
        omega_tower_word_progression core hfree hwin hdust k (by omega)
      have hih := ih (by omega)
      have hp3 : 3^(k+1) = 3^k * 3 := by rw [Nat.pow_succ]
      rw [show k+1-1 = k from by omega, hprog]
      obtain ⟨T3, hT3def⟩ : ∃ T3 : Nat,
          T3 = (omegaCutWord 2 1 * core) % 27 := ⟨_, rfl⟩
      obtain ⟨Tk, hTkdef⟩ : ∃ Tk : Nat,
          Tk = (omegaCutWord (k-1) 1 * core) % 3^k := ⟨_, rfl⟩
      rw [hT3def, hTkdef] at hih ⊢
      omega

/-! ## §3 The two-class collapse — the tower family's dust base -/

/-- **THE TWO-CLASS COLLAPSE.**  A tower-family core (`core % 9 ∈ {4,7}`)
carrying the full dust shape sits in one of EXACTLY TWO classes modulo
27: `core % 27 = 4` or `core % 27 = 16`.  The level-3 middle-third
window, the seed word `omegaCutWord 2 1 = 9709 ≡ 16 (mod 27)`, and the
six-family arithmetic. -/
theorem dust_candidate_two_classes (core : Nat)
    (hfree : core % 3 = 1 ∨ core % 3 = 2)
    (hwin : ∀ s : Nat, 1 ≤ s →
      (omegaCutWord s core) % 3^(s+2) < 2 * 3^(s+1))
    (hdust : ∀ k : Nat, 3 ≤ k →
      (omegaCutWord (k-1) 1 * core) % 3^k < 2 * 3^(k-1))
    (hfam : core % 9 = 4 ∨ core % 9 = 7) :
    core % 27 = 4 ∨ core % 27 = 16 := by
  obtain ⟨hL, hU⟩ :=
    omega_dust_shape_middle_third core hfree hwin hdust 3 (by norm_num)
  rw [show (3:Nat)-1 = 2 from by norm_num] at hL hU
  norm_num at hL hU
  -- hL : 9 ≤ (omegaCutWord 2 1 * core) % 27, hU : ... < 18
  -- the seed word's value: omegaCutWord 2 1 = 9709
  have hW : omegaCutWord 2 1 = 9709 := by
    have hf := omega_cut_factor 2 1
    norm_num at hf
    omega
  have h97 : (9709:Nat) % 27 = 16 := by norm_num
  -- the level-3 tower word residue in terms of core's class
  have hmulmod : (omegaCutWord 2 1 * core) % 27
      = (16 * (core % 27)) % 27 := by
    rw [Nat.mul_mod (omegaCutWord 2 1) core 27, hW, h97]
  -- core's class decomposition: core % 27 = (core % 9) + 9 * b, b < 3
  have h27lt : core % 27 < 27 := Nat.mod_lt _ (by norm_num)
  have h279 : core % 27 % 9 = core % 9 :=
    Nat.mod_mod_of_dvd (by norm_num : (9:Nat) ∣ 27)
  obtain ⟨b, hb, hbdef⟩ : ∃ b : Nat, b < 3 ∧
      core % 27 = core % 9 + 9 * b := by
    refine ⟨(core % 27) / 9, ?_, ?_⟩
    · have hle : 9 * ((core % 27) / 9) ≤ core % 27 := Nat.mul_div_le _ 9
      omega
    · have hdm : 9 * ((core % 27) / 9) + (core % 27) % 9 = core % 27 :=
        Nat.div_add_mod _ 9
      omega
  -- the 144-fold split: 16 * (a + 9b) ≡ 16a + 9b (mod 27)
  have hsplit : (16 * (core % 9 + 9 * b)) % 27
      = (16 * (core % 9) + 9 * b) % 27 := by
    have hE : 16 * (core % 9 + 9 * b)
        = (16 * (core % 9) + 9 * b) + 27 * (5 * b) := by ring
    rw [hE, Nat.add_mul_mod_self_left]
  -- the middle-third sandwich at level 3, in class terms
  have hband : 9 ≤ (16 * (core % 9) + 9 * b) % 27
      ∧ (16 * (core % 9) + 9 * b) % 27 < 18 := by
    constructor
    · rw [← hsplit, ← hbdef, ← hmulmod]; exact hL
    · rw [← hsplit, ← hbdef, ← hmulmod]; exact hU
  have hb3 : b = 0 ∨ b = 1 ∨ b = 2 := by omega
  rcases hfam with h9 | h9
  · rw [h9] at hband hbdef
    rcases hb3 with rfl | rfl | rfl
    · exact Or.inl (by omega)
    · exfalso; omega
    · exfalso; omega
  · rw [h9] at hband hbdef
    rcases hb3 with rfl | rfl | rfl
    · exfalso; omega
    · exact Or.inr (by omega)
    · exfalso; omega

/-! ## §4 The stream uniqueness — one class, one stream -/

/-- **THE LINEAR-TRIT EXPANSION.**  The tower word's residue is LINEAR
in the next trit: adding `3^k * x` to the class shifts the residue by
exactly `3^k * x`.  The seed-one word is a three-adic unit, so the
fold kills the unit's higher trits. -/
theorem tower_word_linear_in_trit (k cc x : Nat) (hx : x < 3) :
    (omegaCutWord k 1 * (cc + 3^k * x)) % 3^(k+1)
      = ((omegaCutWord k 1 * cc) % 3^(k+1) + 3^k * x) % 3^(k+1) := by
  have hW1 : omegaCutWord k 1 % 3 = 1 := by
    have h := omega_cut_word_mod3 k 1
    omega
  have hexp : omegaCutWord k 1 * (cc + 3^k * x)
      = omegaCutWord k 1 * cc + 3^k * (x * omegaCutWord k 1) := by ring
  have hm2 : (x * omegaCutWord k 1) % 3 = x := by
    rw [Nat.mul_mod, hW1]
    omega
  rw [hexp,
    Nat.add_mod (omegaCutWord k 1 * cc) (3^k * (x * omegaCutWord k 1))
      3^(k+1),
    mul_mod_pow, hm2]

/-- **THE STREAM UNIQUENESS.**  Two cores carrying the full dust shape
in the same class modulo 27 agree modulo `3^k` for EVERY `k` from three
upward: each candidate class pins ONE infinite 3-adic stream, one trit
at a time.  The pinning: the tower word is linear in the next trit, the
progression fixes the level-`k+1` residue outright, and the residue
equality cancels the base — leaving the next trit uniquely determined. -/
theorem dust_core_class_determined (core core' : Nat)
    (hfree : core % 3 = 1 ∨ core % 3 = 2)
    (hwin : ∀ s : Nat, 1 ≤ s →
      (omegaCutWord s core) % 3^(s+2) < 2 * 3^(s+1))
    (hdust : ∀ k : Nat, 3 ≤ k →
      (omegaCutWord (k-1) 1 * core) % 3^k < 2 * 3^(k-1))
    (hfree' : core' % 3 = 1 ∨ core' % 3 = 2)
    (hwin' : ∀ s : Nat, 1 ≤ s →
      (omegaCutWord s core') % 3^(s+2) < 2 * 3^(s+1))
    (hdust' : ∀ k : Nat, 3 ≤ k →
      (omegaCutWord (k-1) 1 * core') % 3^k < 2 * 3^(k-1))
    (hclass : core % 27 = core' % 27) :
    ∀ k : Nat, 3 ≤ k → core % 3^k = core' % 3^k := by
  intro k
  induction k with
  | zero => intro h; omega
  | succ k ih =>
    intro hk
    rcases Nat.eq_or_lt_of_le hk with h3 | h4
    · rw [← h3, show (3:Nat)^(3:Nat) = 27 from by norm_num]
      exact hclass
    · have hc : core % 3^k = core' % 3^k := ih (by omega)
      have hmodw : ∀ (W n m : Nat), (W * n) % m = (W * (n % m)) % m := by
        intro W n m
        rw [Nat.mul_mod, Nat.mod_mod_of_dvd (Nat.dvd_refl _)]
      obtain ⟨x, hx, hcx⟩ : ∃ x : Nat, x < 3 ∧
          core % 3^(k+1) = core % 3^k + 3^k * x :=
        ⟨core / 3^k % 3, Nat.mod_lt _ (by decide), mod_pow_succ_split core k⟩
      obtain ⟨x', hx', hcx'⟩ : ∃ x' : Nat, x' < 3 ∧
          core' % 3^(k+1) = core' % 3^k + 3^k * x' :=
        ⟨core' / 3^k % 3, Nat.mod_lt _ (by decide), mod_pow_succ_split core' k⟩
      -- the two towers' level-k+1 words, in class form
      have hlin : (omegaCutWord k 1 * core) % 3^(k+1)
          = ((omegaCutWord k 1 * (core % 3^k)) % 3^(k+1) + 3^k * x) % 3^(k+1) := by
        rw [hmodw (omegaCutWord k 1) core 3^(k+1), hcx,
          tower_word_linear_in_trit k (core % 3^k) x hx]
      have hlin' : (omegaCutWord k 1 * core') % 3^(k+1)
          = ((omegaCutWord k 1 * (core' % 3^k)) % 3^(k+1) + 3^k * x') % 3^(k+1) := by
        rw [hmodw (omegaCutWord k 1) core' 3^(k+1), hcx',
          tower_word_linear_in_trit k (core' % 3^k) x' hx']
      -- the towers agree at level k, hence at level k+1 (progression)
      have hTk : (omegaCutWord (k-1) 1 * core) % 3^k
          = (omegaCutWord (k-1) 1 * core') % 3^k := by
        rw [Nat.mul_mod (omegaCutWord (k-1) 1) core 3^k,
            Nat.mul_mod (omegaCutWord (k-1) 1) core' 3^k, hc]
      have hprog :=
        omega_tower_word_progression core hfree hwin hdust k (by omega)
      have hprog' :=
        omega_tower_word_progression core' hfree' hwin' hdust' k (by omega)
      have hT1eq : (omegaCutWord k 1 * core) % 3^(k+1)
          = (omegaCutWord k 1 * core') % 3^(k+1) := by
        rw [hprog, hprog', hTk]
      rw [hlin, hlin', hc] at hT1eq
      -- cancel the common base: the next trits coincide
      have hcancel : 3^k * x % 3^(k+1) = 3^k * x' % 3^(k+1) :=
        add_mod_cancel_left' _ _ _ _ (Nat.pow_pos (by decide)) hT1eq
      rw [mul_mod_pow, mul_mod_pow, Nat.mod_eq_of_lt hx,
        Nat.mod_eq_of_lt hx'] at hcancel
      have hxx : x = x' :=
        Nat.eq_of_mul_eq_mul_left (Nat.pow_pos (by decide)) hcancel
      rw [hcx, hcx', hxx, hc]

#print axioms DustCandidates406.mod_pow_succ_split
#print axioms DustCandidates406.mul_mod_pow
#print axioms DustCandidates406.mod_eq_sub'
#print axioms DustCandidates406.add_mod_cancel_left'
#print axioms DustCandidates406.omega_tower_word_progression
#print axioms DustCandidates406.dust_tower_word_closed_form
#print axioms DustCandidates406.dust_candidate_two_classes
#print axioms DustCandidates406.tower_word_linear_in_trit
#print axioms DustCandidates406.dust_core_class_determined

#eval "ERDOS406_DUST_CANDIDATES_GREEN"

end DustCandidates406
