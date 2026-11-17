import Mathlib
import GSTClimbInfiniteFamily
import GSTCanonicalTailLTE

set_option maxRecDepth 1000000
set_option maxHeartbeats 20000000

/-!
# THE FEEDBACK READ — the construction of the act, begun

One separate file, zero monolith bytes.  The exponent's own digit stream,
fed through the prefix-power's digit stream, IS the power's digit stream:

* **§1 THE SELF-READ LAW.**  `self_read`: for EVERY exponent `K` and EVERY
  row `j+1`, the row-`j+1` trit of `4^K` is the row-`j+1` trit of
  `4^(K mod 3^j)` PLUS the `j`-th trit of `K` itself, modulo three —
  `digit3 (4^K) (j+1) = (digit3 (4^(K % 3^j)) (j+1) + digit3 K j) % 3`.
  The power reads the exponent through the prefix-power: the whole
  ternary stream of every power of four is one feedback system.  At
  `j = 0` it is the row-one read (`row_one_read`: row one of `4^K` IS
  `K % 3`), and `row_one_kill`: every `K ≡ 2 mod 3` fires at row one.

* **§2 THE COLLAPSE INTO THE FEEDBACK TREE.**  `cantorian_iff_feedback`:
  `CantorianPower K` holds IF AND ONLY IF, at EVERY level `j`, the prefix
  noise plus the exponent trit never lands on two.  `the_act_iff_feedback`:
  the act holds IF AND ONLY IF every `K ≥ 8` fires somewhere in the
  feedback tree.  The act, as one object: NO exponent from eight on
  threads the whole tree.

* **§3 THE UNIFORM KILL ENGINE.**  `feedback_fire_of_class`: ONE law that
  fires the digit two at row `j+1` for ANY level `j`, ANY alive prefix
  `r`, and the one dead child-trit `t` — the noise receipt is a closed
  computation, the class membership is a congruence.  Every cascade level
  that has ever been run, and every level that ever will be run, is an
  instance of this single theorem.

* **§4 CASCADE LEVEL FOUR.**  `dust_fire_row_five`: eight new infinite
  uniform classes — `K ≡ 85, 91, 112, 118, 163, 175, 190, 202 mod 243` —
  fire at row five.  The first level whose noise is NONZERO (the
  prefix-powers `4^4, 4^10, 4^31, 4^37` carry trit `1` at row five): the
  feedback warps the survivor set past the Cantor shape.  The survivor
  map: `cantorian_dust_mod_9/27/81/243` — a Cantorian dust exponent's
  residue is pinned, level by level, down to the sixteen surviving nodes
  mod `243` — and `166, 172, 193, 199` among them own a trit TWO at
  position four and still live: the row-five prefix-noise of one absorbed
  the fire.  The tree is richer than the Cantor set from level five on —
  machine-named.

* **§4B CASCADE LEVEL FIVE.**  `dust_fire_row_six`: sixteen more
  infinite uniform classes fire at row six — the first level whose
  noise takes ALL THREE values (`4^31, 4^37, 4^172` carry trit TWO at
  row six).  `noise_window_law`: the noise vanishes beyond the diagonal
  window `4^r ≥ 3^(j+1)`.  `unique_dead_child`: every node owns exactly
  one dead child — the blade's one-of-three named at the feedback level,
  so the survivor map doubles (`2, 4, 8, 16, 32`) by structure:
  `cantorian_dust_mod_729` pins the dust to THIRTY-TWO nodes mod 729.

* **§5 THE SOCKET.**  `hTailF_of_feedback`: hand the tree-escape — every
  `K ≥ 8` fires at some level — and `hTailF` closes through the standing
  green bridges.  `the_construction_receipt`: everything assembled, axiom
  printouts included: the classical three only.
-/

namespace GSTTheActConstruction

open GSTCanonicalSevenAxisBridge (digit3)
open GSTClimbInfiniteFamily (CantorianPower prefaced_window_full
  dust_fire_row_two dust_fire_row_three dust_fire_row_four
  no22_of_digit_two pow4_mod3 the_act_iff_no_cantorian)

/-! ## §1 THE SELF-READ LAW — the power stream reads the exponent stream -/

/-- **THE SELF-READ LAW.**  For every exponent `K` and every level `j`, the
row-`j+1` trit of `4^K` is the row-`j+1` trit of the prefix-power
`4^(K mod 3^j)` plus the `j`-th trit of `K`, modulo three.  The power's
digit stream is the exponent's digit stream fed through the
prefix-power's digit stream — one feedback system, every row, every
exponent, no hypothesis. -/
theorem self_read (K j : Nat) :
    digit3 (4^K) (j + 1) =
      (digit3 (4^(K % 3^j)) (j + 1) + digit3 K j) % 3 := by
  have hpow : 0 < 3^j := Nat.pow_pos (by decide)
  have hmod : K % 3^j < 3^j := Nat.mod_lt _ hpow
  have hlaw := prefaced_window_full j (K / 3^j) (K % 3^j) 0 hmod (by omega)
  have hKeq : 3^j * (K / 3^j) + K % 3^j = K := Nat.div_add_mod K (3^j)
  rw [hKeq, show j + 1 + 0 = j + 1 from by omega] at hlaw
  rw [hlaw]
  unfold digit3
  rw [Nat.pow_zero, Nat.div_one, Nat.add_mod]
  have hB : (4^(K % 3^j) * GSTCanonicalTailLTE.lteCoeff j * (K / 3^j)) % 3
      = (K / 3^j) % 3 := by
    have h1 := pow4_mod3 (K % 3^j)
    have h2 := GSTCanonicalTailLTE.lteCoeff_mod3_one j
    have hpair : (4^(K % 3^j) * GSTCanonicalTailLTE.lteCoeff j) % 3 = 1 := by
      rw [Nat.mul_mod, h1, h2]
    rw [Nat.mul_mod, hpair]
    omega
  rw [hB]

/-- **THE ROW-ONE READ.**  Row one of `4^K` is exactly `K % 3`: the
feedback law's ground floor, where the prefix is empty and the power
reads the exponent's zeroth trit bare. -/
theorem row_one_read (K : Nat) : digit3 (4^K) 1 = K % 3 := by
  have h := self_read K 0
  rw [Nat.zero_add, Nat.pow_zero, Nat.mod_one] at h
  have h0 : digit3 (4^0) 1 = 0 := by decide
  have hK : digit3 K 0 = K % 3 := by
    unfold digit3
    rw [Nat.pow_zero, Nat.div_one]
  rw [h, h0, hK]
  omega

/-- **THE ROW-ONE KILL.**  Every exponent `K ≡ 2 mod 3` fires its digit
two at row one — the feedback tree's ground-floor kill. -/
theorem row_one_kill (K : Nat) (h : K % 3 = 2) : digit3 (4^K) 1 = 2 := by
  rw [row_one_read, h]

/-! ## §2 THE COLLAPSE — the act as the feedback tree's escape -/

/-- **THE CANTORIAN CONSTRAINT SYSTEM.**  `CantorianPower K` holds IF AND
ONLY IF at EVERY level `j` the prefix noise plus the exponent trit never
lands on two: the entire Cantorian core is the set of exponents that
thread the feedback tree at every level.  Every row of every power is a
level of the tree — nothing outside the tree exists. -/
theorem cantorian_iff_feedback (K : Nat) :
    CantorianPower K ↔ ∀ j : Nat,
      (digit3 (4^(K % 3^j)) (j + 1) + digit3 K j) % 3 ≠ 2 := by
  constructor
  · intro hc j
    have hrow := hc (j + 1) (by omega)
    rw [self_read K j] at hrow
    exact hrow
  · intro hfire p hp
    rcases p with _ | j
    · exact absurd hp (by omega)
    · rw [self_read K j]
      exact hfire j

/-- **THE ACT AS TREE-ESCAPE.**  The act holds IF AND ONLY IF every
exponent from eight on fires somewhere in the feedback tree: some level
`j` where the prefix noise plus the exponent trit lands on two.  The act,
the Cantorian core, and the feedback tree are one object. -/
theorem the_act_iff_feedback :
    GSTTheAct.the_act ↔
      ∀ K : Nat, 8 ≤ K → ∃ j : Nat,
        (digit3 (4^(K % 3^j)) (j + 1) + digit3 K j) % 3 = 2 := by
  rw [the_act_iff_no_cantorian]
  constructor
  · intro hnc K hK8
    by_cases hc : CantorianPower K
    · exact absurd ⟨K, hK8, hc⟩ hnc
    · unfold CantorianPower at hc
      push_neg at hc
      obtain ⟨p, hp1, hp⟩ := hc
      rcases p with _ | j
      · exact absurd hp1 (by omega)
      · refine ⟨j, ?_⟩
        rw [self_read K j] at hp
        exact hp
  · intro hfire hnc
    obtain ⟨K, hK8, hc⟩ := hnc
    obtain ⟨j, hj⟩ := hfire K hK8
    exact absurd hj ((cantorian_iff_feedback K).mp hc j)

/-! ## §3 THE UNIFORM KILL ENGINE — one law, every level -/

/-- **PREFIX UNPACKING.**  A class membership `K ≡ r + 3^j·t mod 3^(j+1)`
with `r < 3^j` and `t < 3` unpacks into the two facts the feedback law
consumes: `K`'s level-`j` prefix is `r`, and `K`'s `j`-th trit is `t`. -/
theorem prefix_unpack (K j r t : Nat) (hr : r < 3^j) (ht : t < 3)
    (hK : K % 3^(j+1) = r + 3^j * t) :
    K % 3^j = r ∧ digit3 K j = t := by
  have hp : 0 < 3^j := Nat.pow_pos (by decide)
  have hdvd : 3^j ∣ 3^(j+1) := ⟨3, Nat.pow_succ 3 j⟩
  have hmod : K % 3^j = r := by
    have h := Nat.mod_mod_of_dvd K hdvd
    rw [hK, Nat.add_mul_mod_self_left, Nat.mod_eq_of_lt hr] at h
    exact h.symm
  refine ⟨hmod, ?_⟩
  obtain ⟨q, hq⟩ : ∃ q : Nat, q = K / 3^(j+1) := ⟨K / 3^(j+1), rfl⟩
  have hdm : 3^(j+1) * q + (r + 3^j * t) = K := by
    rw [← hK, hq, Nat.div_add_mod K (3^(j+1))]
  have hshape : K = 3^j * (3 * q + t) + r := by
    rw [← hdm, Nat.pow_succ]
    ring
  unfold digit3
  rw [hshape, show 3^j * (3 * q + t) + r = r + 3^j * (3 * q + t) from by ring,
    Nat.add_mul_div_left _ _ hp, Nat.div_eq_of_lt hr]
  omega

/-- **THE UNIFORM KILL.**  At ANY level `j`, an alive prefix `r` and its
one dead child-trit `t` — certified by the closed noise receipt
`(digit3 (4^r) (j+1) + t) % 3 = 2` — kill the entire congruence class
`K ≡ r + 3^j·t mod 3^(j+1)` at row `j+1`: every member fires its digit
two.  Every cascade level, current and future, is an instance. -/
theorem feedback_fire_of_class (j r t K : Nat)
    (hr : r < 3^j) (ht : t < 3)
    (hnoise : (digit3 (4^r) (j + 1) + t) % 3 = 2)
    (hK : K % 3^(j+1) = r + 3^j * t) :
    digit3 (4^K) (j + 1) = 2 := by
  obtain ⟨hmod, htrit⟩ := prefix_unpack K j r t hr ht hK
  rw [self_read K j, hmod, htrit]
  exact hnoise

/-- **THE UNIFORM KILL, CLASS FORM.**  Same law, phrased for the level-four
modulus: `K ≡ r + 81·t mod 243` fires at row five when the noise receipt
holds.  All arithmetic literal — the class hypothesis is pure omega. -/
theorem fire_of_mod243 (K r t : Nat)
    (hr : r < 81) (ht : t < 3)
    (hnoise : (digit3 (4^r) 5 + t) % 3 = 2)
    (hclass : K % 243 = r + 81 * t) :
    digit3 (4^K) 5 = 2 := by
  have h245 : (3:Nat)^(4+1) = 243 := by decide
  have h81 : (3:Nat)^4 = 81 := by decide
  have hK : K % 3^(4+1) = r + 3^4 * t := by
    rw [h245, h81]
    exact hclass
  have hr' : r < 3^4 := by
    rw [h81]
    exact hr
  exact feedback_fire_of_class 4 r t K hr' ht hnoise hK

/-! ## §4 CASCADE LEVEL FOUR — the noise turns on -/

/-- **CASCADE LEVEL THREE (row five).**  Every exponent `K ≡ 85, 91,
112, 118, 163, 175, 190, 202 mod 243` fires its digit two at row five —
eight new infinite uniform classes.  The first cascade level whose
prefix-noise is nonzero (`4^4, 4^10, 4^31, 4^37` carry trit one at row
five): the feedback era of the cascade begins here. -/
theorem dust_fire_row_five (K : Nat)
    (hK : K % 243 = 85 ∨ K % 243 = 91 ∨ K % 243 = 112 ∨ K % 243 = 118 ∨
           K % 243 = 163 ∨ K % 243 = 175 ∨ K % 243 = 190 ∨ K % 243 = 202) :
    digit3 (4^K) 5 = 2 := by
  rcases hK with h85 | h91 | h112 | h118 | h163 | h175 | h190 | h202
  · exact fire_of_mod243 K 4 1 (by decide) (by decide) (by decide) (by omega)
  · exact fire_of_mod243 K 10 1 (by decide) (by decide) (by decide) (by omega)
  · exact fire_of_mod243 K 31 1 (by decide) (by decide) (by decide) (by omega)
  · exact fire_of_mod243 K 37 1 (by decide) (by decide) (by decide) (by omega)
  · exact fire_of_mod243 K 1 2 (by decide) (by decide) (by decide) (by omega)
  · exact fire_of_mod243 K 13 2 (by decide) (by decide) (by decide) (by omega)
  · exact fire_of_mod243 K 28 2 (by decide) (by decide) (by decide) (by omega)
  · exact fire_of_mod243 K 40 2 (by decide) (by decide) (by decide) (by omega)

/-- **THE CASCADE KILL, LEVEL FOUR.**  The eight new classes die outright
through the repo's own kill chain. -/
theorem no22_of_cascade_four (K : Nat)
    (h : K % 243 = 85 ∨ K % 243 = 91 ∨ K % 243 = 112 ∨ K % 243 = 118 ∨
         K % 243 = 163 ∨ K % 243 = 175 ∨ K % 243 = 190 ∨ K % 243 = 202) :
    noTernaryTwo (4^K) = false :=
  no22_of_digit_two K 5 (dust_fire_row_five K h)

/-- **THE DUST PINNED AT LEVEL ONE.**  A Cantorian dust exponent (`K ≡ 1
mod 3`) lives in one of the two surviving residues mod nine. -/
theorem cantorian_dust_mod_9 (K : Nat)
    (hd : K % 3 = 1) (hc : CantorianPower K) :
    K % 9 = 1 ∨ K % 9 = 4 := by
  have hrow := hc 2 (by omega)
  by_cases h7 : K % 9 = 7
  · exact absurd (dust_fire_row_two K h7) hrow
  · omega

/-- **THE DUST PINNED AT LEVEL TWO.**  Four surviving residues mod
twenty-seven. -/
theorem cantorian_dust_mod_27 (K : Nat)
    (hd : K % 3 = 1) (hc : CantorianPower K) :
    K % 27 = 1 ∨ K % 27 = 4 ∨ K % 27 = 10 ∨ K % 27 = 13 := by
  have h9 := cantorian_dust_mod_9 K hd hc
  have hrow := hc 3 (by omega)
  have h19 : K % 27 ≠ 19 :=
    fun h => absurd (dust_fire_row_three K (Or.inl h)) hrow
  have h22 : K % 27 ≠ 22 :=
    fun h => absurd (dust_fire_row_three K (Or.inr (Or.inl h))) hrow
  have h25 : K % 27 ≠ 25 :=
    fun h => absurd (dust_fire_row_three K (Or.inr (Or.inr h))) hrow
  rcases h9 with h1 | h4 <;> omega

/-- **THE DUST PINNED AT LEVEL THREE.**  Eight surviving residues mod
eighty-one — the Cantor prefixes with lowest trit one. -/
theorem cantorian_dust_mod_81 (K : Nat)
    (hd : K % 3 = 1) (hc : CantorianPower K) :
    K % 81 = 1 ∨ K % 81 = 4 ∨ K % 81 = 10 ∨ K % 81 = 13 ∨
      K % 81 = 28 ∨ K % 81 = 31 ∨ K % 81 = 37 ∨ K % 81 = 40 := by
  have h27 := cantorian_dust_mod_27 K hd hc
  have hrow := hc 4 (by omega)
  have h55 : K % 81 ≠ 55 :=
    fun h => absurd (dust_fire_row_four K (Or.inl h)) hrow
  have h58 : K % 81 ≠ 58 :=
    fun h => absurd (dust_fire_row_four K (Or.inr (Or.inl h))) hrow
  have h64 : K % 81 ≠ 64 :=
    fun h => absurd (dust_fire_row_four K (Or.inr (Or.inr (Or.inl h)))) hrow
  have h67 : K % 81 ≠ 67 :=
    fun h => absurd (dust_fire_row_four K
      (Or.inr (Or.inr (Or.inr (Or.inl h))))) hrow
  have h73 : K % 81 ≠ 73 :=
    fun h => absurd (dust_fire_row_four K
      (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h)))))) hrow
  have h76 : K % 81 ≠ 76 :=
    fun h => absurd (dust_fire_row_four K
      (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr h)))))) hrow
  rcases h27 with h1 | h4 | h10 | h13 <;> omega

/-- **THE DUST PINNED AT LEVEL FOUR — THE MAP.**  A Cantorian dust
exponent lives in one of SIXTEEN surviving residues mod 243.  The noise
era's signature: `166, 172, 193, 199` among the survivors own trit
TWO at position four and still live — the prefix-noise absorbed the fire
(their row-five prefix-noise is one, turning two into zero).
The survivor set is now RICHER than the Cantor prefixes: the feedback
tree, machine-drawn at its fifth storey. -/
theorem cantorian_dust_mod_243 (K : Nat)
    (hd : K % 3 = 1) (hc : CantorianPower K) :
    K % 243 = 1 ∨ K % 243 = 4 ∨ K % 243 = 10 ∨ K % 243 = 13 ∨
      K % 243 = 28 ∨ K % 243 = 31 ∨ K % 243 = 37 ∨ K % 243 = 40 ∨
      K % 243 = 82 ∨ K % 243 = 94 ∨ K % 243 = 109 ∨ K % 243 = 121 ∨
      K % 243 = 166 ∨ K % 243 = 172 ∨ K % 243 = 193 ∨ K % 243 = 199 := by
  have h81 := cantorian_dust_mod_81 K hd hc
  have hrow := hc 5 (by omega)
  have h85 : K % 243 ≠ 85 :=
    fun h => absurd (dust_fire_row_five K (Or.inl h)) hrow
  have h91 : K % 243 ≠ 91 :=
    fun h => absurd (dust_fire_row_five K (Or.inr (Or.inl h))) hrow
  have h112 : K % 243 ≠ 112 :=
    fun h => absurd (dust_fire_row_five K (Or.inr (Or.inr (Or.inl h)))) hrow
  have h118 : K % 243 ≠ 118 :=
    fun h => absurd (dust_fire_row_five K
      (Or.inr (Or.inr (Or.inr (Or.inl h))))) hrow
  have h163 : K % 243 ≠ 163 :=
    fun h => absurd (dust_fire_row_five K
      (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h)))))) hrow
  have h175 : K % 243 ≠ 175 :=
    fun h => absurd (dust_fire_row_five K
      (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))))) hrow
  have h190 : K % 243 ≠ 190 :=
    fun h => absurd (dust_fire_row_five K
      (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h)))))))) hrow
  have h202 : K % 243 ≠ 202 :=
    fun h => absurd (dust_fire_row_five K
      (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr h)))))))) hrow
  rcases h81 with h1 | h4 | h10 | h13 | h28 | h31 | h37 | h40 <;> omega

/-! ## §4B CASCADE LEVEL FIVE — the noise turns ternary -/

/-- **THE NOISE WINDOW LAW.**  Beyond the diagonal window the prefix
noise vanishes: when the prefix-power stays below the modulus, its
row-`j+1` trit is zero.  The feedback's noise lives in the window
`4^r ≥ 3^(j+1)` — every deeper row reads bare exponent trits. -/
theorem noise_window_law (r j : Nat) (h : 4^r < 3^(j+1)) :
    digit3 (4^r) (j + 1) = 0 := by
  unfold digit3
  rw [Nat.div_eq_of_lt h]

/-- **THE UNIQUE DEAD CHILD.**  At every level, every prefix owns
EXACTLY ONE dead child-trit: `(2 - noise) mod 3`.  The blade's
one-of-three, named at the feedback level — every node of the dust
tree has exactly two alive children, forever, by structure. -/
theorem unique_dead_child (r j : Nat) :
    ∃! t : Nat, t < 3 ∧ (digit3 (4^r) (j + 1) + t) % 3 = 2 := by
  have hd : digit3 (4^r) (j + 1) < 3 := by
    unfold digit3
    exact Nat.mod_lt _ (by decide)
  refine ⟨2 - digit3 (4^r) (j + 1), ⟨by omega, by omega⟩, ?_⟩
  intro t ht
  omega

/-- The deterministic dead-child operator of one feedback node. -/
def deadChild (r j : Nat) : Nat :=
  2 - digit3 (4^r) (j+1)

/-- The dead child is always one of the three ternary children. -/
theorem deadChild_lt_three (r j : Nat) :
    deadChild r j < 3 := by
  unfold deadChild
  have hd : digit3 (4^r) (j+1) < 3 := by
    unfold digit3
    exact Nat.mod_lt _ (by decide)
  omega

/-- The dead-child operator really lands on the firing value two. -/
theorem deadChild_fires (r j : Nat) :
    (digit3 (4^r) (j+1) + deadChild r j) % 3 = 2 := by
  unfold deadChild
  have hd : digit3 (4^r) (j+1) < 3 := by
    unfold digit3
    exact Nat.mod_lt _ (by decide)
  omega

/-- **DETERMINISTIC FEEDBACK TRANSITION.**
Among the three child trits, a child fires exactly when it is the value of the
dead-child operator.  The existential unique-dead-child theorem is therefore
promoted to a functional classifier. -/
theorem child_fires_iff_eq_deadChild
    (r j t : Nat) (ht : t < 3) :
    (digit3 (4^r) (j+1) + t) % 3 = 2 ↔
      t = deadChild r j := by
  obtain ⟨w,hw,huniq⟩ := unique_dead_child r j
  constructor
  · intro hfire
    have htw : t = w := huniq t ⟨ht,hfire⟩
    have hdw : deadChild r j = w :=
      huniq (deadChild r j)
        ⟨deadChild_lt_three r j, deadChild_fires r j⟩
    exact htw.trans hdw.symm
  · intro htdead
    subst t
    exact deadChild_fires r j

/-- A ternary child is live exactly when it differs from the deterministic
dead-child operator. -/
theorem child_live_iff_ne_deadChild
    (r j t : Nat) (ht : t < 3) :
    (digit3 (4^r) (j+1) + t) % 3 ≠ 2 ↔
      t ≠ deadChild r j := by
  constructor
  · intro hLive hDead
    exact hLive
      ((child_fires_iff_eq_deadChild r j t ht).2 hDead)
  · intro hNe hFire
    exact hNe
      ((child_fires_iff_eq_deadChild r j t ht).1 hFire)

/-- Functional feedback crown: every node carries one canonical forbidden
child and the other children are exactly its live complement. -/
theorem deterministic_feedback_crown :
    (∀ r j, deadChild r j < 3)
    ∧ (∀ r j,
      (digit3 (4^r) (j+1) + deadChild r j) % 3 = 2)
    ∧ (∀ r j t, t < 3 →
      ((digit3 (4^r) (j+1) + t) % 3 = 2 ↔
        t = deadChild r j)) := by
  exact ⟨deadChild_lt_three, deadChild_fires,
    child_fires_iff_eq_deadChild⟩

/-- **THE UNIFORM KILL, LEVEL-FIVE FORM.**  Same engine, one level
deeper: `K ≡ r + 243·t mod 729` fires at row six when the noise
receipt holds.  All arithmetic literal. -/
theorem fire_of_mod729 (K r t : Nat)
    (hr : r < 243) (ht : t < 3)
    (hnoise : (digit3 (4^r) 6 + t) % 3 = 2)
    (hclass : K % 729 = r + 243 * t) :
    digit3 (4^K) 6 = 2 := by
  have h729 : (3:Nat)^(5+1) = 729 := by decide
  have h243 : (3:Nat)^5 = 243 := by decide
  have hK : K % 3^(5+1) = r + 3^5 * t := by
    rw [h729, h243]
    exact hclass
  have hr' : r < 3^5 := by
    rw [h243]
    exact hr
  exact feedback_fire_of_class 5 r t K hr' ht hnoise hK

/-- **CASCADE LEVEL FIVE (row six).**  Every exponent `K ≡ 31, 37,
172, 253, 256, 271, 337, 352, 409, 487, 490, 526, 568, 607, 679,
685 mod 729` fires its digit two at row six — sixteen new infinite
uniform classes.  The first cascade level whose noise takes ALL
THREE values: the prefixes `4^31, 4^37, 4^172` carry trit TWO at
row six (their zeroth child dies), the noise-one prefixes kill their
first child, the noise-zero prefixes kill their second. -/
theorem dust_fire_row_six (K : Nat)
    (hK : K % 729 = 31 ∨ K % 729 = 37 ∨ K % 729 = 172 ∨ K % 729 = 253 ∨ K % 729 = 256 ∨ K % 729 = 271 ∨ K % 729 = 337 ∨ K % 729 = 352 ∨ K % 729 = 409 ∨ K % 729 = 487 ∨ K % 729 = 490 ∨ K % 729 = 526 ∨ K % 729 = 568 ∨ K % 729 = 607 ∨ K % 729 = 679 ∨ K % 729 = 685) :
    digit3 (4^K) 6 = 2 := by
  rcases hK with h31 | h37 | h172 | h253 | h256 | h271 | h337 | h352 | h409 | h487 | h490 | h526 | h568 | h607 | h679 | h685
  · exact fire_of_mod729 K 31 0 (by decide) (by decide) (by decide) (by omega)
  · exact fire_of_mod729 K 37 0 (by decide) (by decide) (by decide) (by omega)
  · exact fire_of_mod729 K 172 0 (by decide) (by decide) (by decide) (by omega)
  · exact fire_of_mod729 K 10 1 (by decide) (by decide) (by decide) (by omega)
  · exact fire_of_mod729 K 13 1 (by decide) (by decide) (by decide) (by omega)
  · exact fire_of_mod729 K 28 1 (by decide) (by decide) (by decide) (by omega)
  · exact fire_of_mod729 K 94 1 (by decide) (by decide) (by decide) (by omega)
  · exact fire_of_mod729 K 109 1 (by decide) (by decide) (by decide) (by omega)
  · exact fire_of_mod729 K 166 1 (by decide) (by decide) (by decide) (by omega)
  · exact fire_of_mod729 K 1 2 (by decide) (by decide) (by decide) (by omega)
  · exact fire_of_mod729 K 4 2 (by decide) (by decide) (by decide) (by omega)
  · exact fire_of_mod729 K 40 2 (by decide) (by decide) (by decide) (by omega)
  · exact fire_of_mod729 K 82 2 (by decide) (by decide) (by decide) (by omega)
  · exact fire_of_mod729 K 121 2 (by decide) (by decide) (by decide) (by omega)
  · exact fire_of_mod729 K 193 2 (by decide) (by decide) (by decide) (by omega)
  · exact fire_of_mod729 K 199 2 (by decide) (by decide) (by decide) (by omega)

/-- **THE CASCADE KILL, LEVEL FIVE.**  The sixteen new classes die
outright through the repo's own kill chain. -/
theorem no22_of_cascade_five (K : Nat)
    (h : K % 729 = 31 ∨ K % 729 = 37 ∨ K % 729 = 172 ∨ K % 729 = 253 ∨ K % 729 = 256 ∨ K % 729 = 271 ∨ K % 729 = 337 ∨ K % 729 = 352 ∨ K % 729 = 409 ∨ K % 729 = 487 ∨ K % 729 = 490 ∨ K % 729 = 526 ∨ K % 729 = 568 ∨ K % 729 = 607 ∨ K % 729 = 679 ∨ K % 729 = 685) :
    noTernaryTwo (4^K) = false :=
  no22_of_digit_two K 6 (dust_fire_row_six K h)

/-- **THE DUST PINNED AT LEVEL FIVE — THE MAP DOUBLES.**  A Cantorian
dust exponent lives in one of THIRTY-TWO surviving residues mod
729.  The structural law in action: every one of the sixteen level-
four nodes kept exactly two children (`unique_dead_child`), so the
alive set doubles — `2, 4, 8, 16, 32` — level by level, without
exception, by the blade's one-of-three. -/
theorem cantorian_dust_mod_729 (K : Nat)
    (hd : K % 3 = 1) (hc : CantorianPower K) :
    K % 729 = 1 ∨ K % 729 = 4 ∨ K % 729 = 10 ∨ K % 729 = 13 ∨ K % 729 = 28 ∨ K % 729 = 40 ∨ K % 729 = 82 ∨ K % 729 = 94 ∨ K % 729 = 109 ∨ K % 729 = 121 ∨ K % 729 = 166 ∨ K % 729 = 193 ∨ K % 729 = 199 ∨ K % 729 = 244 ∨ K % 729 = 247 ∨ K % 729 = 274 ∨ K % 729 = 280 ∨ K % 729 = 283 ∨ K % 729 = 325 ∨ K % 729 = 364 ∨ K % 729 = 415 ∨ K % 729 = 436 ∨ K % 729 = 442 ∨ K % 729 = 496 ∨ K % 729 = 499 ∨ K % 729 = 514 ∨ K % 729 = 517 ∨ K % 729 = 523 ∨ K % 729 = 580 ∨ K % 729 = 595 ∨ K % 729 = 652 ∨ K % 729 = 658 := by
  have h243 := cantorian_dust_mod_243 K hd hc
  have hrow := hc 6 (by omega)
  have hdead31 : K % 729 ≠ 31 :=
    fun h => absurd (dust_fire_row_six K (Or.inl h)) hrow
  have hdead37 : K % 729 ≠ 37 :=
    fun h => absurd (dust_fire_row_six K (Or.inr (Or.inl h))) hrow
  have hdead172 : K % 729 ≠ 172 :=
    fun h => absurd (dust_fire_row_six K (Or.inr (Or.inr (Or.inl h)))) hrow
  have hdead253 : K % 729 ≠ 253 :=
    fun h => absurd (dust_fire_row_six K (Or.inr (Or.inr (Or.inr (Or.inl h))))) hrow
  have hdead256 : K % 729 ≠ 256 :=
    fun h => absurd (dust_fire_row_six K (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h)))))) hrow
  have hdead271 : K % 729 ≠ 271 :=
    fun h => absurd (dust_fire_row_six K (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))))) hrow
  have hdead337 : K % 729 ≠ 337 :=
    fun h => absurd (dust_fire_row_six K (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h)))))))) hrow
  have hdead352 : K % 729 ≠ 352 :=
    fun h => absurd (dust_fire_row_six K (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))))))) hrow
  have hdead409 : K % 729 ≠ 409 :=
    fun h => absurd (dust_fire_row_six K (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h)))))))))) hrow
  have hdead487 : K % 729 ≠ 487 :=
    fun h => absurd (dust_fire_row_six K (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))))))))) hrow
  have hdead490 : K % 729 ≠ 490 :=
    fun h => absurd (dust_fire_row_six K (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h)))))))))))) hrow
  have hdead526 : K % 729 ≠ 526 :=
    fun h => absurd (dust_fire_row_six K (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))))))))))) hrow
  have hdead568 : K % 729 ≠ 568 :=
    fun h => absurd (dust_fire_row_six K (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h)))))))))))))) hrow
  have hdead607 : K % 729 ≠ 607 :=
    fun h => absurd (dust_fire_row_six K (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))))))))))))) hrow
  have hdead679 : K % 729 ≠ 679 :=
    fun h => absurd (dust_fire_row_six K (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h)))))))))))))))) hrow
  have hdead685 : K % 729 ≠ 685 :=
    fun h => absurd (dust_fire_row_six K (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr h)))))))))))))))) hrow
  rcases h243 with h1 | h4 | h10 | h13 | h28 | h31 | h37 | h40 | h82 | h94 | h109 | h121 | h166 | h172 | h193 | h199 <;> omega

/-- **THE LEVEL-FIVE RECEIPT.**  Cascade level five assembled:
the window law, the unique dead child, the sixteen fires, the
doubled survivor map, and the kill chain — with axiom printouts
below. -/
theorem the_level_five_receipt :
    (∀ r j : Nat, 4^r < 3^(j+1) → digit3 (4^r) (j+1) = 0) ∧
    (∀ r j : Nat, ∃! t : Nat, t < 3 ∧ (digit3 (4^r) (j+1) + t) % 3 = 2) ∧
    (∀ K : Nat, K % 729 = 31 ∨ K % 729 = 37 ∨ K % 729 = 172 ∨ K % 729 = 253 ∨ K % 729 = 256 ∨ K % 729 = 271 ∨ K % 729 = 337 ∨ K % 729 = 352 ∨ K % 729 = 409 ∨ K % 729 = 487 ∨ K % 729 = 490 ∨ K % 729 = 526 ∨ K % 729 = 568 ∨ K % 729 = 607 ∨ K % 729 = 679 ∨ K % 729 = 685 → digit3 (4^K) 6 = 2) ∧
    (∀ K : Nat, K % 729 = 31 ∨ K % 729 = 37 ∨ K % 729 = 172 ∨ K % 729 = 253 ∨ K % 729 = 256 ∨ K % 729 = 271 ∨ K % 729 = 337 ∨ K % 729 = 352 ∨ K % 729 = 409 ∨ K % 729 = 487 ∨ K % 729 = 490 ∨ K % 729 = 526 ∨ K % 729 = 568 ∨ K % 729 = 607 ∨ K % 729 = 679 ∨ K % 729 = 685 → noTernaryTwo (4^K) = false) ∧
    (∀ K : Nat, K % 3 = 1 → CantorianPower K →
      K % 729 = 1 ∨ K % 729 = 4 ∨ K % 729 = 10 ∨ K % 729 = 13 ∨ K % 729 = 28 ∨ K % 729 = 40 ∨ K % 729 = 82 ∨ K % 729 = 94 ∨ K % 729 = 109 ∨ K % 729 = 121 ∨ K % 729 = 166 ∨ K % 729 = 193 ∨ K % 729 = 199 ∨ K % 729 = 244 ∨ K % 729 = 247 ∨ K % 729 = 274 ∨ K % 729 = 280 ∨ K % 729 = 283 ∨ K % 729 = 325 ∨ K % 729 = 364 ∨ K % 729 = 415 ∨ K % 729 = 436 ∨ K % 729 = 442 ∨ K % 729 = 496 ∨ K % 729 = 499 ∨ K % 729 = 514 ∨ K % 729 = 517 ∨ K % 729 = 523 ∨ K % 729 = 580 ∨ K % 729 = 595 ∨ K % 729 = 652 ∨ K % 729 = 658) :=
  ⟨fun r j => noise_window_law r j,
    fun r j => unique_dead_child r j,
    dust_fire_row_six, no22_of_cascade_five, cantorian_dust_mod_729⟩

#print axioms noise_window_law
#print axioms unique_dead_child
#print axioms deadChild_lt_three
#print axioms deadChild_fires
#print axioms child_fires_iff_eq_deadChild
#print axioms deterministic_feedback_crown
#print axioms fire_of_mod729
#print axioms dust_fire_row_six
#print axioms no22_of_cascade_five
#print axioms cantorian_dust_mod_729
#print axioms the_level_five_receipt
/-! ## §5 THE SOCKET — the tree-escape closes hTailF -/

/-- **THE SOCKET.**  Hand the tree-escape — every `K ≥ 8` fires at some
level of the feedback read — and `hTailF` closes, no hypothesis, no
binder: through the standing green bridges, in one line. -/
theorem hTailF_of_feedback
    (hB : erdos_even_conjecture_iff_tailF)
    (h : ∀ K : Nat, 8 ≤ K → ∃ j : Nat,
      (digit3 (4^(K % 3^j)) (j + 1) + digit3 K j) % 3 = 2) :
    GSTGraphV2OmegaWaveLaw.four_power_omega_shadow_wave_tailF :=
  (GSTTheAct.the_act_iff_hTailF hB).mp (the_act_iff_feedback.mpr h)

/-! ## §6 THE RECEIPT — everything assembled -/

/-- **THE CONSTRUCTION, ASSEMBLED.**  (1) The self-read law: every row of
every power is prefix-noise plus exponent-trit.  (2) The act as
tree-escape.  (3) The socket: tree-escape closes `hTailF`.  (4) Cascade
level four: eight classes fire at row five.  (5) The survivor map: the
Cantorian dust pinned to sixteen nodes mod 243.  (6) The kill chain:
the eight classes die through the repo's own chain. -/
theorem the_construction_receipt
    (hB : erdos_even_conjecture_iff_tailF) :
    (∀ K j : Nat, digit3 (4^K) (j + 1) =
      (digit3 (4^(K % 3^j)) (j + 1) + digit3 K j) % 3) ∧
    (GSTTheAct.the_act ↔
      ∀ K : Nat, 8 ≤ K → ∃ j : Nat,
        (digit3 (4^(K % 3^j)) (j + 1) + digit3 K j) % 3 = 2) ∧
    (∀ h : (∀ K : Nat, 8 ≤ K → ∃ j : Nat,
        (digit3 (4^(K % 3^j)) (j + 1) + digit3 K j) % 3 = 2),
      GSTGraphV2OmegaWaveLaw.four_power_omega_shadow_wave_tailF) ∧
    (∀ K : Nat, K % 243 = 85 ∨ K % 243 = 91 ∨ K % 243 = 112 ∨
        K % 243 = 118 ∨ K % 243 = 163 ∨ K % 243 = 175 ∨ K % 243 = 190 ∨
        K % 243 = 202 →
      digit3 (4^K) 5 = 2) ∧
    (∀ K : Nat, K % 3 = 1 → CantorianPower K →
      K % 243 = 1 ∨ K % 243 = 4 ∨ K % 243 = 10 ∨ K % 243 = 13 ∨
        K % 243 = 28 ∨ K % 243 = 31 ∨ K % 243 = 37 ∨ K % 243 = 40 ∨
        K % 243 = 82 ∨ K % 243 = 94 ∨ K % 243 = 109 ∨ K % 243 = 121 ∨
        K % 243 = 166 ∨ K % 243 = 172 ∨ K % 243 = 193 ∨ K % 243 = 199) ∧
    (∀ K : Nat, K % 243 = 85 ∨ K % 243 = 91 ∨ K % 243 = 112 ∨
        K % 243 = 118 ∨ K % 243 = 163 ∨ K % 243 = 175 ∨ K % 243 = 190 ∨
        K % 243 = 202 →
      noTernaryTwo (4^K) = false) :=
  ⟨fun K j => self_read K j, the_act_iff_feedback, hTailF_of_feedback hB,
    dust_fire_row_five, cantorian_dust_mod_243, no22_of_cascade_four⟩

#print axioms self_read
#print axioms row_one_read
#print axioms row_one_kill
#print axioms cantorian_iff_feedback
#print axioms the_act_iff_feedback
#print axioms prefix_unpack
#print axioms feedback_fire_of_class
#print axioms fire_of_mod243
#print axioms dust_fire_row_five
#print axioms no22_of_cascade_four
#print axioms cantorian_dust_mod_9
#print axioms cantorian_dust_mod_27
#print axioms cantorian_dust_mod_81
#print axioms cantorian_dust_mod_243
#print axioms hTailF_of_feedback
#print axioms the_construction_receipt

end GSTTheActConstruction
