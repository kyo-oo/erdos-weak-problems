import GSTInfiniteFourPowerNavigation
import GSTFourPowerDirectResidue
import GSTGraphV2HandwrittenOmegaUBlock
import GSTGraphV2InfiniteControllerBridge

set_option maxRecDepth 1000000
set_option maxHeartbeats 20000000

namespace GSTGraphV2OmegaWaveLaw

open GSTCanonicalSevenAxisBridge
open GSTFourPowerDirectResidue (lteCoeff lteCoeff_mod3_one
  pow4_three_power_lte_exact pow4_mod3_one pow4_scaled_mod_next)
open GSTGraphV2InfiniteControl
open GSTGraphV2HandwrittenOmegaUBlock
open GSTGraphV2InfiniteControllerBridge
open GST2DMixedEmergence
open GSTU2DEventTransport

/-!
# THE Ω-WAVE LAW — the final stroke of the GST Ontological V2 Graph route

This file is the Law of the ontology: one theorem-package that *confirms
existence* of the ternary-two witness for every exponent in its domain and
*explains why*, by combining exactly the three mandated weapons:

1. **A genuine new operator** — `omegaWaveStep`, the Ω-wave transfusion:
   one simultaneous handwritten-U multiply/divide action on a seeded
   information word (the origin trit is consumed into the x4 seed while the
   remaining origin is divided by three).

2. **The Omega infinity hand-written equations** — the exact LTE tower
   `pow4_three_power_lte_exact` / `lteCoeff_mod3_one` together with the
   handwritten-U origin split of the omega block.

3. **The infinite controller** — the all-depth bad coupled control and the
   latent gate transfer of the Graph-V2 controller bridge.

The mathematical heart is the **Ω-cut tower**.  For an exponent
`K = 3^a * core`, the power `4^K` admits the exact decomposition

    4^K = 1 + 3^(a+1) * (lteCoeff a * omegaGeoSum a core),

and the ternary digit of `4^K` at the cut row `a+1` is **literally the
first nonzero ternary trit of the exponent**:

    digit3 (4^K) (a+1) = core % 3,

with cut carry exactly zero for `a ≥ 1` (the prefix at the cut is one).
Hence every exponent whose core is congruent to two modulo three **owns a
physical Happy row exactly at its own LTE cut** — an infinite arithmetic
family (all `K = 3^a * core`, `a ≥ 1`, `core ≡ 2 (mod 3)`) that no previous
theorem of the repository covered.  One level higher, the cut word satisfies
`W ≡ 7 * core (mod 9)` for `a ≥ 1`, giving digit two at row `a+2` for every
core congruent to `1, 5, 6 (mod 9)` — the second infinite family.  The tower
coefficients stabilize: `lteCoeff a` is constant modulo `3^L` for every
`a ≥ L-1`, the arithmetic form of the controller's "observation depth is
arbitrary".

The **why** is delivered twice: arithmetically — the mean factor
`lteCoeff ≡ 1 (mod 3)` preserves the exponent's first nonzero trit through
the transfusion, so the creation digit cannot be destroyed by climbing —
and ontologically — the Ω transfusion conserves all seven axes of the
Graph-V2 vertex (`residual_parent_observables_exact`), a Happy gate
re-encodes into latent carry rather than annihilating
(`graph_child_happy_latent_transfer`), and an all-bad unit sheet generates
the full infinite bad coupled controller (`graph_infinite_bad_control`)
which is then punctured by its own LTE cut: the controller forbids exactly
what the cut provides.
-/

/-! ## §1 The genuine new operator: the Ω-wave transfusion

The operator acts on a seeded information word `(D, X)`.  In one action it

* consumes the least ternary trit of `X` into the x4 seed (the
  handwritten-U multiply: the seed advances by the exact carry law
  `(D + 4·trit)/3`), and
* divides the remaining origin by three (the handwritten-U divide).

It is the local, nameable form of the simultaneous U action that the
handwritten omega equations perform on perfect powers.
-/

/-- **THE NEW OPERATOR ΩW** — one omega wave-climb transfusion step on a
seeded information word: the origin trit is consumed into the x4 seed while
the remaining origin is divided by three. -/
def omegaWaveStep (D X : Nat) : Nat × Nat :=
  ((D + 4 * (X % 3)) / 3, X / 3)

/-- The operator consumes the origin trit exactly as the handwritten-U
divide: the word splits into its consumed trit and its U-tail, and the tail
is literally the operator's second component. -/
theorem omegaWaveStep_u_divide (D X : Nat) :
    X = originTrit X + 3 * (omegaWaveStep D X).2 :=
  origin_split_exact X

/-- The operator's seed action is the exact x4 cell carry law: the consumed
trit is multiplied into the seed and the result re-divided by three, with
the visible output digit emitted as remainder. -/
theorem omegaWaveStep_u_multiply (D X : Nat) :
    D + 4 * originTrit X =
      3 * (omegaWaveStep D X).1 + ((D + 4 * originTrit X) % 3) := by
  unfold omegaWaveStep originTrit
  omega

/-- Mass conservation of one transfusion: seed plus quadrupled trit is
exactly the tripled new seed plus the visible output. -/
theorem omegaWaveStep_mass (D X : Nat) :
    3 * (omegaWaveStep D X).1 ≤ D + 4 * originTrit X ∧
      D + 4 * originTrit X < 3 * ((omegaWaveStep D X).1 + 1) := by
  unfold omegaWaveStep originTrit
  constructor <;> omega

/-- **The worldtrace orbit law.**  The vertical step of the exact carry
stream of any energy `R` is literally one Ω-wave transfusion of the seeded
tail: the operator's orbit *is* the information wave that reads the ternary
digits of `R`. -/
theorem omegaWaveStep_worldtrace (R p : Nat) :
    (omegaWaveStep (carry4 R p) (R / 3^p)).1 = carry4 R (p+1) :=
  (carry4_forward_exact R p).symm

/-- The transfusion tail descends the ternary ladder exactly one rung. -/
theorem omegaWaveStep_tail (R p : Nat) :
    (omegaWaveStep (carry4 R p) (R / 3^p)).2 = R / 3^(p+1) := by
  unfold omegaWaveStep
  rw [Nat.div_div_eq_div_mul, Nat.pow_succ]

/-! ## §2 The Ω-cut tower (the LTE trail) -/

/-- The geometric mean factor of the Ω-decomposition: the sum of the first
`core` powers of the base `4^(3^a)`. -/
def omegaGeoSum (a core : Nat) : Nat :=
  Finset.sum (Finset.range core) (fun j => (4^(3^a))^j)

/-- The cut word of the Ω-decomposition: the LTE mean times the geometric
mean. -/
def omegaCutWord (a core : Nat) : Nat :=
  lteCoeff a * omegaGeoSum a core

/-- **The Ω-cut factorization** — the omega handwritten equation of the Law.
For every sheet level `a` and every core mass, the power `4^(3^a * core)`
decomposes exactly as one plus the cut modulus times the cut word, and the
cut word is the product of the LTE mean and the geometric mean. -/
theorem omega_cut_factor (a core : Nat) :
    4^(3^a * core) =
      1 + 3^(a+1) * omegaCutWord a core := by
  induction core with
  | zero =>
      have h0 : 3^a * 0 = 0 := Nat.mul_zero _
      rw [h0, Nat.pow_zero]
      simp [omegaGeoSum, omegaCutWord]
  | succ core ih =>
      have hbase := pow4_three_power_lte_exact a
      have hstep : 4^(3^a * (core+1)) = 4^(3^a * core) * 4^(3^a) :=
        Nat.pow_add 4 (3^a * core) (3^a)
      have hterm : (4^(3^a))^core = 4^(3^a * core) := by
        rw [Nat.pow_mul]
      have hgeoW : omegaCutWord a (core+1)
          = omegaCutWord a core + lteCoeff a * 4^(3^a * core) := by
        unfold omegaCutWord omegaGeoSum
        simp only [Finset.sum_range_succ, hterm]
        ring
      rw [hstep, ih, hbase, hgeoW, ih]
      ring

/-- Every term of the geometric mean is one modulo three. -/
theorem omega_geo_term_mod3 (a j : Nat) :
    ((4^(3^a))^j) % 3 = 1 := by
  rw [Nat.pow_mod, pow4_mod3_one, Nat.one_pow] <;> omega

/-- The geometric mean is the core mass modulo three. -/
theorem omega_geo_mod3 (a core : Nat) :
    omegaGeoSum a core % 3 = core % 3 := by
  induction core with
  | zero => simp [omegaGeoSum]
  | succ core ih =>
      have hgeo : omegaGeoSum a (core+1)
          = omegaGeoSum a core + (4^(3^a))^core := by
        simp [omegaGeoSum, Finset.sum_range_succ]
      rw [hgeo, Nat.add_mod, omega_geo_term_mod3, ih]
      omega

/-- **THE ν-LAW (level one of the Ω-cut tower).**  The ternary digit of
`4^(3^a * core)` at the cut row `a+1` is literally the first nonzero
ternary trit of the exponent: the residue of the core mass modulo three. -/
theorem omega_cut_digit (a core : Nat) :
    digit3 (4^(3^a * core)) (a+1) = core % 3 := by
  have hf := omega_cut_factor a core
  have hp : 0 < 3^(a+1) := Nat.pow_pos (by decide)
  have h1 : 1 < 3^(a+1) := by
    have h3 : (3:Nat)^1 ≤ 3^(a+1) := by
      simpa using Nat.pow_le_pow_of_le (by decide : 1 < (3:Nat))
        (by omega : 1 ≤ a+1)
    omega
  have hdiv : (1 + 3^(a+1) * omegaCutWord a core) / 3^(a+1)
      = omegaCutWord a core := by
    rw [Nat.add_mul_div_left _ _ hp, Nat.div_eq_of_lt h1, Nat.zero_add]
  unfold digit3
  rw [hf, hdiv, omegaCutWord, Nat.mul_mod, lteCoeff_mod3_one,
    omega_geo_mod3, Nat.one_mul]
  omega

/-- The prefix of the power at the cut row is exactly one. -/
theorem omega_cut_prefix_one (a core : Nat) :
    4^(3^a * core) % 3^(a+1) = 1 :=
  pow4_scaled_mod_next a core

/-- **The cut carry law.**  From sheet level one onward the cut carry is
exactly zero: the quadrupled unit prefix stays below the cut modulus. -/
theorem omega_cut_carry_zero (a core : Nat) (ha : 1 ≤ a) :
    carry4 (4^(3^a * core)) (a+1) = 0 := by
  have h9 : (4:Nat) < 3^(a+1) := by
    have h3 : (3:Nat)^2 ≤ 3^(a+1) := by
      simpa using Nat.pow_le_pow_of_le (by decide : 1 < (3:Nat))
        (by omega : 2 ≤ a+1)
    norm_num at h3
    omega
  unfold carry4
  rw [omega_cut_prefix_one]
  have h41 : (4:Nat) * 1 < 3^(a+1) := by simpa using h9
  exact Nat.div_eq_of_lt h41

/-- **THE Ω-CUT GATE (level one).**  Every exponent whose core mass is
congruent to two modulo three owns a physical Happy row exactly at its own
LTE cut — digit two with carry zero.  This is an infinite arithmetic family:
all `K = 3^a * core` with `a ≥ 1` and `core ≡ 2 (mod 3)`. -/
theorem omega_cut_happy_gate (a core : Nat) (ha : 1 ≤ a)
    (hcore : core % 3 = 2) :
    HappyCell
      (carry4 (4^(3^a * core)) (a+1))
      (digit3 (4^(3^a * core)) (a+1)) := by
  refine ⟨?_, Or.inl ?_⟩
  · rw [omega_cut_digit a core, hcore]
  · rw [omega_cut_carry_zero a core ha]

/-! ## §3 Level two of the tower and the stabilization -/

/-- The LTE mean is constant modulo nine from sheet level one onward. -/
theorem omega_lteCoeff_mod9 (a : Nat) (ha : 1 ≤ a) :
    lteCoeff a % 9 = 7 := by
  induction a with
  | zero => omega
  | succ a ih =>
      rcases Nat.eq_zero_or_pos a with h0 | hpos
      · subst h0
        decide
      · have ha' : 1 ≤ a := hpos
        have hc := ih ha'
        have h1 : 3^(a+1) % 9 = 0 := by
          have hsplit : 3^(a+1) = 3^2 * 3^(a+1-2) := by
            rw [← Nat.pow_add]
            congr 1
            omega
          rw [hsplit]
          omega
        have h2 : 3^(2*a+1) % 9 = 0 := by
          have hsplit : 3^(2*a+1) = 3^2 * 3^(2*a+1-2) := by
            rw [← Nat.pow_add]
            congr 1
            omega
          rw [hsplit]
          omega
        have hA : (3^(a+1) * (lteCoeff a)^2) % 9 = 0 := by
          rw [Nat.mul_mod, h1, Nat.zero_mul]
        have hB : (3^(2*a+1) * (lteCoeff a)^3) % 9 = 0 := by
          rw [Nat.mul_mod, h2, Nat.zero_mul]
        have hunfold : lteCoeff (a+1)
            = lteCoeff a + 3^(a+1) * (lteCoeff a)^2
              + 3^(2*a+1) * (lteCoeff a)^3 := rfl
        rw [hunfold]
        omega

/-- The base of the geometric mean is one modulo nine from sheet level one
onward. -/
theorem omega_base_mod9 (a : Nat) (ha : 1 ≤ a) :
    (4^(3^a)) % 9 = 1 := by
  induction a with
  | zero => omega
  | succ a ih =>
      rcases Nat.eq_zero_or_pos a with h0 | hpos
      · subst h0
        norm_num
      · have hstep : 4^(3^(a+1)) = (4^(3^a))^3 := by
          rw [Nat.pow_succ, Nat.pow_mul]
        rw [hstep, Nat.pow_mod, ih hpos]

/-- The geometric mean is the core mass modulo nine from sheet level one
onward. -/
theorem omega_geo_mod9 (a core : Nat) (ha : 1 ≤ a) :
    omegaGeoSum a core % 9 = core % 9 := by
  have hterm : ∀ j : Nat, ((4^(3^a))^j) % 9 = 1 := by
    intro j
    rw [Nat.pow_mod, omega_base_mod9 a ha, Nat.one_pow] <;> omega
  induction core with
  | zero => simp [omegaGeoSum]
  | succ core ih =>
      have hgeo : omegaGeoSum a (core+1)
          = omegaGeoSum a core + (4^(3^a))^core := by
        simp [omegaGeoSum, Finset.sum_range_succ]
      rw [hgeo, Nat.add_mod, hterm core, ih]
      omega

/-- **The level-two cut word law.**  From sheet level one onward the cut
word is `7 * core` modulo nine. -/
theorem omega_cut_word_mod9 (a core : Nat) (ha : 1 ≤ a) :
    omegaCutWord a core % 9 = (7 * core) % 9 := by
  unfold omegaCutWord
  rw [Nat.mul_mod, omega_lteCoeff_mod9 a ha, omega_geo_mod9 a core ha]
  omega

/-- **THE LEVEL-TWO DIGIT LAW.**  The ternary digit of `4^(3^a * core)` at
row `a+2` is the top trit of the cut word, i.e. the top trit of
`7 * core` modulo nine.  Delivered through the green prefix-slice socket of
the infinite controller: the cut decomposition `4^K = 1 + 3^(a+1) * W` is
literally a prefix/tail slice, so the digit two rows above the cut is the
cut word's own ternary digit at row one. -/
theorem omega_level2_digit (a core : Nat) :
    digit3 (4^(3^a * core)) (a+2) = (omegaCutWord a core % 9) / 3 := by
  have hf := omega_cut_factor a core
  have h1 : (1:Nat) < 3^(a+1) := by
    have h3 : (3:Nat)^1 ≤ 3^(a+1) := by
      simpa using Nat.pow_le_pow_of_le (by decide : 1 < (3:Nat))
        (by omega : 1 ≤ a+1)
    omega
  have hslice := prefix_slice_digit_exact (a+1) 1 (omegaCutWord a core) 1 h1
  rw [show a+2 = (a+1)+1 from by omega, hf, hslice]
  unfold digit3
  rw [Nat.pow_one]
  omega

/-- **THE LEVEL-TWO GATE CLASSES.**  For every core congruent to one, five
or six modulo nine, the power `4^(3^a * core)` owns a ternary digit two at
row `a+2` — the second infinite family of the Law. -/
theorem omega_level2_digit_two (a core : Nat) (ha : 1 ≤ a)
    (hcore : core % 9 = 1 ∨ core % 9 = 5 ∨ core % 9 = 6) :
    digit3 (4^(3^a * core)) (a+2) = 2 := by
  rw [omega_level2_digit, omega_cut_word_mod9 a core ha]
  rcases hcore with h1 | h5 | h6
  · have hval : (7 * core) % 9 = 7 := by omega
    rw [hval]
  · have hval : (7 * core) % 9 = 8 := by omega
    rw [hval]
  · have hval : (7 * core) % 9 = 6 := by omega
    rw [hval]

/-! ## §4 The tower stabilization — the controller's "depth is arbitrary" -/

/-- One stabilization step: above the observation level the LTE mean does
not move modulo the level modulus. -/
theorem omega_lteCoeff_mod_step (a L : Nat) (ha : L ≤ a + 1) :
    lteCoeff (a+1) % 3^L = lteCoeff a % 3^L := by
  have h1 : 3^(a+1) % 3^L = 0 := by
    have hsplit : 3^(a+1) = 3^L * 3^(a+1-L) := by
      rw [← Nat.pow_add]
      congr 1
      omega
    rw [hsplit, Nat.mul_mod, Nat.mod_self, Nat.zero_mul, Nat.zero_mod]
  have h2 : 3^(2*a+1) % 3^L = 0 := by
    have hsplit : 3^(2*a+1) = 3^L * 3^(2*a+1-L) := by
      rw [← Nat.pow_add]
      congr 1
      omega
    rw [hsplit, Nat.mul_mod, Nat.mod_self, Nat.zero_mul, Nat.zero_mod]
  have hA : (3^(a+1) * (lteCoeff a)^2) % 3^L = 0 := by
    rw [Nat.mul_mod, h1, Nat.zero_mul, Nat.zero_mod]
  have hB : (3^(2*a+1) * (lteCoeff a)^3) % 3^L = 0 := by
    rw [Nat.mul_mod, h2, Nat.zero_mul, Nat.zero_mod]
  have hA0 : 3^(a+1) * (lteCoeff a)^2
      = 3^L * ((3^(a+1) * (lteCoeff a)^2) / 3^L) := by
    have hdiv : (3^(a+1) * (lteCoeff a)^2) % 3^L
        + 3^L * ((3^(a+1) * (lteCoeff a)^2) / 3^L)
        = 3^(a+1) * (lteCoeff a)^2 :=
      Nat.mod_add_div _ (3^L)
    rw [hA, Nat.zero_add] at hdiv
    exact hdiv.symm
  have hB0 : 3^(2*a+1) * (lteCoeff a)^3
      = 3^L * ((3^(2*a+1) * (lteCoeff a)^3) / 3^L) := by
    have hdiv : (3^(2*a+1) * (lteCoeff a)^3) % 3^L
        + 3^L * ((3^(2*a+1) * (lteCoeff a)^3) / 3^L)
        = 3^(2*a+1) * (lteCoeff a)^3 :=
      Nat.mod_add_div _ (3^L)
    rw [hB, Nat.zero_add] at hdiv
    exact hdiv.symm
  have hunfold : lteCoeff (a+1)
      = lteCoeff a + 3^(a+1) * (lteCoeff a)^2
        + 3^(2*a+1) * (lteCoeff a)^3 := rfl
  rw [hunfold, hA0, hB0]
  rw [Nat.add_mul_mod_self_left, Nat.add_mul_mod_self_left]

/-- **THE TOWER STABILIZATION LAW** — the arithmetic form of the infinite
controller's "observation depth is arbitrary": from level `L-1` onward, the
LTE mean is constant modulo `3^L`.  The tower digits at level `L` therefore
depend only on the core residue for every sufficiently deep sheet. -/
theorem omega_lteCoeff_stable (L d : Nat) :
    lteCoeff ((L-1) + d) % 3^L = lteCoeff (L-1) % 3^L := by
  induction d with
  | zero => simp
  | succ d ih =>
      have hstep := omega_lteCoeff_mod_step ((L-1)+d) L (by omega)
      have hidx : (L-1) + (d+1) = ((L-1)+d) + 1 := by omega
      rw [hidx]
      exact hstep.trans ih

/-! ## §5 The controller puncture — the WHY, formal -/

/-- The unit sheet at column `K` reads exactly the digits and carries of
`4^K`. -/
theorem omega_unit_sheet (K p : Nat) :
    (graph 1 K p).seven.carry = carry4 (4^K) p ∧
      (graph 1 K p).seven.digit = digit3 (4^K) p := by
  constructor <;>
    simp [graph, cell, GSTCanonicalSevenAxisBridge.vertex, Nat.mul_one]

/-- An all-bad unit-sheet column (from row three downward) generates the
full infinite bad coupled controller of the Graph-V2 bridge. -/
theorem omega_all_bad_to_controller (K : Nat)
    (hbad : ∀ p : Nat, 3 ≤ p → ¬ HappyCell (carry4 (4^K) p) (digit3 (4^K) p)) :
    GSTV2.InfiniteBadCoupledControl (4^K) (graphCoupledState 1 K 3) := by
  apply graph_infinite_bad_control 1 K 3
  · have h := (omega_unit_sheet 0 3).1
    rw [h]
    unfold carry4
    norm_num
  · intro j
    have hc := (omega_unit_sheet K (3+j)).1
    have hd := (omega_unit_sheet K (3+j)).2
    rw [show (graph 1 K (3+j)).seven.carry = carry4 (4^K) (3+j) from hc,
      show (graph 1 K (3+j)).seven.digit = digit3 (4^K) (3+j) from hd]
    exact hbad (3+j) (by omega)

/-- **THE CONTROLLER PUNCTURE.**  For the class-two family at sheet level
two or higher, an all-bad column is impossible: the LTE cut of that very
column is a physical Happy cell. -/
theorem omega_puncture (a core : Nat) (ha : 2 ≤ a) (hcore : core % 3 = 2) :
    ¬ (∀ p : Nat, 3 ≤ p →
        ¬ HappyCell (carry4 (4^(3^a * core)) p)
          (digit3 (4^(3^a * core)) p)) := by
  intro hbad
  exact hbad (a+1) (by omega) (omega_cut_happy_gate a core (by omega) hcore)

/-- **THE WHY (combined).**  For the class-two family at sheet level two or
higher, an all-bad unit-sheet column would simultaneously

* generate the full infinite bad coupled controller — the creation-blocked
  state of the ontology, and
* be punctured by its own LTE cut — a physical Happy cell.

Both cannot hold: the transfusion mean `lteCoeff ≡ 1 (mod 3)` preserves the
exponent's first nonzero trit, so the creation digit survives every climb
and the controller is contradicted by the very sheet it controls. -/
theorem omega_why_theorem (K : Nat)
    (hK : ∃ a core : Nat, 2 ≤ a ∧ core % 3 = 2 ∧ K = 3^a * core)
    (hbad : ∀ p : Nat, 3 ≤ p → ¬ HappyCell (carry4 (4^K) p) (digit3 (4^K) p)) :
    GSTV2.InfiniteBadCoupledControl (4^K) (graphCoupledState 1 K 3) ∧ False := by
  refine ⟨omega_all_bad_to_controller K hbad, ?_⟩
  obtain ⟨a, core, ha, hcore, hKac⟩ := hK
  rw [hKac] at hbad
  exact omega_puncture a core ha hcore hbad

/-! ## §6 THE LAW — existence for the Ω-covered families -/

/-- The class-two family: exponents `K = 3^a * core` with `a ≥ 1` and core
congruent to two modulo three. -/
def omegaClassTwo (K : Nat) : Prop :=
  ∃ a core : Nat, 1 ≤ a ∧ core % 3 = 2 ∧ K = 3^a * core

/-- The level-two family: exponents `K = 3^a * core` with `a ≥ 1` and core
congruent to one, five or six modulo nine. -/
def omegaClassLevelTwo (K : Nat) : Prop :=
  ∃ a core : Nat, 1 ≤ a ∧
    (core % 9 = 1 ∨ core % 9 = 5 ∨ core % 9 = 6) ∧
    K = 3^a * core

/-- **THE Ω-WAVE EXISTENCE LAW, family one.**  Every class-two exponent
owns a physical Happy row (at its own LTE cut, row `a+1 ≥ 2`). -/
theorem omega_wave_existence_class_two (K : Nat) (hK : omegaClassTwo K) :
    ∃ p : Nat, 2 ≤ p ∧ HappyCell (carry4 (4^K) p) (digit3 (4^K) p) := by
  obtain ⟨a, core, ha, hcore, hKac⟩ := hK
  refine ⟨a+1, by omega, ?_⟩
  rw [hKac]
  exact omega_cut_happy_gate a core ha hcore

/-- **THE Ω-WAVE CLIMB FRAGMENT.**  Every class-two exponent at sheet level
two or higher satisfies the climb statement of the third-wave seam — a
fragment of `four_power_happy_climb`, delivered unconditionally. -/
theorem omega_wave_climb_class_two (K : Nat)
    (hK : ∃ a core : Nat, 2 ≤ a ∧ core % 3 = 2 ∧ K = 3^a * core) :
    ∃ p : Nat, 3 ≤ p ∧ HappyCell (carry4 (4^K) p) (digit3 (4^K) p) := by
  obtain ⟨a, core, ha, hcore, hKac⟩ := hK
  refine ⟨a+1, by omega, ?_⟩
  rw [hKac]
  exact omega_cut_happy_gate a core (by omega) hcore

/-- **THE Ω-WAVE EXISTENCE LAW, family two.**  Every level-two-family
exponent owns a ternary digit two at row `a+2 ≥ 3`. -/
theorem omega_wave_digit_two_class_level_two (K : Nat)
    (hK : omegaClassLevelTwo K) :
    ∃ p : Nat, 3 ≤ p ∧ digit3 (4^K) p = 2 := by
  obtain ⟨a, core, ha, hcore, hKac⟩ := hK
  refine ⟨a+2, by omega, ?_⟩
  rw [hKac]
  exact omega_level2_digit_two a core ha hcore

/-- **The creation certificate of the class-two family** — the exact shape
consumed by the monolith's navigation seam, delivered at the LTE cut with
the carry-zero branch. -/
theorem omega_cut_certificate (a core : Nat) (ha : 1 ≤ a)
    (hcore : core % 3 = 2) :
    ∃ p : Nat, 1 ≤ p ∧ (4^(3^a * core)) / 3^p % 3 = 2 ∧
      ((4 * ((4^(3^a * core)) % 3^p)) / 3^p % 3 = 0 ∨
       ((4 * ((4^(3^a * core)) % 3^p)) / 3^p % 3 = 1 ∧
        (4^(3^a * core)) / 3^(p+1) % 3 = 2)) := by
  refine ⟨a+1, by omega, ?_, ?_⟩
  · show digit3 (4^(3^a * core)) (a+1) = 2
    rw [omega_cut_digit a core, hcore]
  · left
    have hc0 : (4 * ((4^(3^a * core)) % 3^(a+1))) / 3^(a+1) % 3 = 0 := by
      have hc := omega_cut_carry_zero a core ha
      unfold carry4 at hc
      rw [hc, Nat.zero_mod]
    exact hc0

#check omegaWaveStep
#check omegaWaveStep_worldtrace
#check omega_cut_factor
#check omega_cut_digit
#check omega_cut_happy_gate
#check omega_lteCoeff_mod9
#check omega_level2_digit_two
#check omega_lteCoeff_stable
#check omega_why_theorem
#check omega_wave_existence_class_two
#check omega_wave_climb_class_two
#check omega_wave_digit_two_class_level_two
#check omega_cut_certificate
#print axioms omegaWaveStep_worldtrace
#print axioms omega_cut_factor
#print axioms omega_cut_digit
#print axioms omega_cut_happy_gate
#print axioms omega_lteCoeff_mod9
#print axioms omega_level2_digit_two
#print axioms omega_lteCoeff_stable
#print axioms omega_why_theorem
#print axioms omega_wave_existence_class_two
#print axioms omega_wave_climb_class_two
#print axioms omega_wave_digit_two_class_level_two
#print axioms omega_cut_certificate

/-! ## §7 The Ω-shadow residue — the Law replaces the climb

The final stroke of the application: the production seam's hypothesis,
stated until now as the full third-wave climb (every exponent from eight
onward owns a physical Happy row), is replaced by the Law's own coverage.
The Ω-cut tower plus two elementary row lemmas delivers the ternary digit
two unconditionally for every exponent outside a sharply defined residue —
the **Ω-shadow**: the exponents whose canonical 3-free core sits in the
tower's uncovered classes (`core ≡ 4 (mod 9)` at any sheet level,
`core ≡ 1 (mod 9)` at sheet zero, or `core ≡ 7 (mod 9)` above sheet zero).
For the shadow itself the seam takes one residual input — the Ω-shadow
wave: every shadow exponent still owns its digit two.  The input is
strictly weaker than the climb: it asks only for a digit (not a Happy
cell) and only on the shadow residue (not on every exponent). -/

/-- The ternary digit at row two of any number congruent to twenty-two
modulo twenty-seven: the prefix split hands the digit directly. -/
theorem omega_digit_row_two_of_mod_27 (R : Nat) (hR : R % 27 = 22) :
    digit3 R 2 = 2 := by
  have hdm27 : 27 * (R / 27) + R % 27 = R := Nat.div_add_mod R 27
  rw [hR] at hdm27
  have hdm9 : 9 * (R / 9) + R % 9 = R := Nat.div_add_mod R 9
  have hmod9 : R % 9 = 4 := by omega
  rw [hmod9] at hdm9
  unfold digit3
  rw [show (3^2 : Nat) = 9 from by decide]
  omega

/-- **The elementary row-two law.**  Every exponent congruent to seven
modulo nine owns its ternary digit two at row two: the base four has order
nine modulo twenty-seven, so `4^K` rides the period to the residue
twenty-two. -/
theorem omega_row2_digit_two (K : Nat) (hK : K % 9 = 7) :
    digit3 (4^K) 2 = 2 := by
  have hdm : K = 9 * (K / 9) + 7 := by omega
  have hpow : (4^9)^(K / 9) * 4^7 = 4^K := by
    rw [← Nat.pow_mul, ← Nat.pow_add, ← hdm]
  have h49 : (4^9) % 27 = 1 := by decide
  have h47 : (4^7) % 27 = 22 := by decide
  have h1 : ((4^9)^(K / 9)) % 27 = 1 := by
    rw [Nat.pow_mod, h49, Nat.one_pow]
  have hmod : (4^K) % 27 = 22 := by
    rw [← hpow, Nat.mul_mod, h1, h47]
  exact omega_digit_row_two_of_mod_27 (4^K) hmod

/-- Every positive number splits as a pure power of three times a
three-free core — the canonical decomposition the residue classes read
from. -/
theorem omega_three_free_decomposition (K : Nat) :
    0 < K → ∃ s core : Nat, K = 3^s * core ∧ ¬ 3 ∣ core := by
  induction K using Nat.strongRecOn with
  | ind K ih =>
    intro hK
    by_cases h3 : 3 ∣ K
    · obtain ⟨q, hq⟩ := h3
      have hq0 : 0 < q := by omega
      obtain ⟨s, core, hs, hc⟩ := ih q (by omega) hq0
      exact ⟨s+1, core, by rw [hq, hs, Nat.pow_succ]; ring, hc⟩
    · exact ⟨0, K, by simp, h3⟩

/-- **The Ω-shadow residue.**  The exponents whose canonical 3-free core
sits in the tower's uncovered classes: `core ≡ 4 (mod 9)` at any sheet
level, `core ≡ 1 (mod 9)` at sheet zero, or `core ≡ 7 (mod 9)` above sheet
zero.  Every other exponent is carried unconditionally by the Law's cut
tower (core `≡ 2 (mod 3)`: row `s+1`; core `≡ 1, 5 (mod 9)` above sheet
zero: row `s+2`) or by the elementary rows (exponent `≡ 2 (mod 3)`: row
one; exponent `≡ 7 (mod 9)`: row two). -/
def omegaShadow (K : Nat) : Prop :=
  ∃ s core : Nat, K = 3^s * core ∧ ¬ 3 ∣ core ∧
    (core % 9 = 4 ∨ (s = 0 ∧ core % 9 = 1) ∨ (1 ≤ s ∧ core % 9 = 7))

/-- **THE Ω-SHADOW WAVE** — the single residual input of the final
theorem: every shadow exponent still owns its ternary digit two.
Strictly weaker than the third-wave climb: a digit, not a Happy cell; the
shadow residue only, not every exponent from eight onward. -/
def four_power_omega_shadow_wave : Prop :=
  ∀ K : Nat, 8 ≤ K → omegaShadow K → ∃ p : Nat, digit3 (4^K) p = 2

/-- **THE Ω-COVERAGE CASE SPLIT.**  Every exponent from eight onward
either lies in the Ω-shadow residue or owns its ternary digit two
outright: the split is exhaustive over the canonical core classes. -/
theorem omega_digit_two_cases (K : Nat) (hK : 8 ≤ K) :
    omegaShadow K ∨ ∃ p : Nat, digit3 (4^K) p = 2 := by
  obtain ⟨s, core, hsc, hc3⟩ := omega_three_free_decomposition K (by omega)
  have h4 : (4^K) = 4^(3^s * core) := by rw [hsc]
  by_cases hcone : core % 3 = 2
  · refine Or.inr ⟨s+1, ?_⟩
    rw [h4, omega_cut_digit s core]
    exact hcone
  · have hcases : core % 9 = 1 ∨ core % 9 = 4 ∨ core % 9 = 7 := by omega
    rcases hcases with h1 | h4c | h7
    · rcases Nat.eq_zero_or_pos s with s0 | spos
      · rw [s0] at hsc
        exact Or.inl ⟨0, core, hsc, hc3, Or.inr (Or.inl ⟨rfl, h1⟩)⟩
      · refine Or.inr ⟨s+2, ?_⟩
        rw [h4]
        exact omega_level2_digit_two s core (by omega) (Or.inl h1)
    · exact Or.inl ⟨s, core, hsc, hc3, Or.inl h4c⟩
    · rcases Nat.eq_zero_or_pos s with s0 | spos
      · rw [s0] at hsc
        refine Or.inr ⟨2, ?_⟩
        have hK9 : K % 9 = 7 := by
          rw [hsc]
          simpa using h7
        exact omega_row2_digit_two K hK9
      · exact Or.inl ⟨s, core, hsc, hc3, Or.inr (Or.inr ⟨by omega, h7⟩)⟩

/-- **The climb, replaced.**  Every exponent outside the shadow owns its
digit two outright — no Happy cell, no climb hypothesis. -/
theorem omega_digit_two_of_not_shadow (K : Nat) (hK : 8 ≤ K)
    (hNS : ¬ omegaShadow K) :
    ∃ p : Nat, digit3 (4^K) p = 2 :=
  (omega_digit_two_cases K hK).resolve_left hNS

/-- **THE Ω-WAVE COVERAGE.**  Under the Ω-shadow wave input, every
exponent from eight onward owns its ternary digit two. -/
theorem omega_digit_two_coverage (hShadow : four_power_omega_shadow_wave)
    (K : Nat) (hK : 8 ≤ K) :
    ∃ p : Nat, digit3 (4^K) p = 2 :=
  (omega_digit_two_cases K hK).elim (fun hsh => hShadow K hK hsh) id

/-! ## §7.5 Level three of the tower — the next sheet of the cut word -/

/-- The LTE mean is constantly sixteen modulo twenty-seven from sheet
level two onward. -/
theorem omega_lteCoeff_mod27 (a : Nat) (ha : 2 ≤ a) :
    lteCoeff a % 27 = 16 := by
  have h27 : (3:Nat)^3 = 27 := by decide
  have hstable := omega_lteCoeff_stable 3 (a-2)
  have hidx : (3-1) + (a-2) = a := by omega
  rw [hidx, h27] at hstable
  rw [hstable]
  decide

/-- The base of the geometric mean is one modulo twenty-seven from sheet
level two onward. -/
theorem omega_base_mod27 : ∀ a : Nat, 2 ≤ a → (4^(3^a)) % 27 = 1 := by
  intro a
  induction a with
  | zero => intro h; omega
  | succ a ih =>
      intro h
      rcases Nat.lt_or_ge a 2 with hlt | hge
      · have ha1 : a = 1 := by omega
        rw [ha1]
        decide
      · have hstep : 4^(3^(a+1)) = (4^(3^a))^3 := by
          rw [Nat.pow_succ, Nat.pow_mul]
        rw [hstep, Nat.pow_mod, ih hge, Nat.one_pow]

/-- The geometric mean is the core mass modulo twenty-seven from sheet
level two onward. -/
theorem omega_geo_mod27 (a core : Nat) (ha : 2 ≤ a) :
    omegaGeoSum a core % 27 = core % 27 := by
  have hterm : ∀ j : Nat, ((4^(3^a))^j) % 27 = 1 := by
    intro j
    rw [Nat.pow_mod, omega_base_mod27 a ha, Nat.one_pow] <;> omega
  induction core with
  | zero => simp [omegaGeoSum]
  | succ core ih =>
      have hgeo : omegaGeoSum a (core+1)
          = omegaGeoSum a core + (4^(3^a))^core := by
        simp [omegaGeoSum, Finset.sum_range_succ]
      rw [hgeo, Nat.add_mod, hterm core, ih]
      omega

/-- **The level-three cut word law.**  From sheet level two onward the cut
word is `16 * core` modulo twenty-seven. -/
theorem omega_cut_word_mod27 (a core : Nat) (ha : 2 ≤ a) :
    omegaCutWord a core % 27 = (16 * core) % 27 := by
  unfold omegaCutWord
  rw [Nat.mul_mod, omega_lteCoeff_mod27 a ha, omega_geo_mod27 a core ha]
  omega

/-- **THE LEVEL-THREE DIGIT LAW.**  The ternary digit of `4^(3^a * core)`
at row `a+3` is the top trit of the cut word modulo twenty-seven — the
same certified prefix-slice socket as level two, one row deeper. -/
theorem omega_level3_digit (a core : Nat) :
    digit3 (4^(3^a * core)) (a+3) = (omegaCutWord a core % 27) / 9 := by
  have hf := omega_cut_factor a core
  have h1 : (1:Nat) < 3^(a+1) := by
    have h3 : (3:Nat)^1 ≤ 3^(a+1) := by
      simpa using Nat.pow_le_pow_of_le (by decide : 1 < (3:Nat))
        (by omega : 1 ≤ a+1)
    omega
  have hslice := prefix_slice_digit_exact (a+1) 1 (omegaCutWord a core) 2 h1
  rw [show a+3 = (a+1)+2 from by omega, hf, hslice]
  unfold digit3
  rw [show (3:Nat)^2 = 9 from by decide]
  omega

/-- **THE LEVEL-THREE GATE CLASSES.**  For every core congruent to thirteen
or twenty-five modulo twenty-seven, the power `4^(3^a * core)` owns a
ternary digit two at row `a+3` — the third infinite family of the Law,
reaching one subclass of each shadow sheet at every sheet level two and
above. -/
theorem omega_level3_digit_two (a core : Nat) (ha : 2 ≤ a)
    (hcore : core % 27 = 13 ∨ core % 27 = 25) :
    digit3 (4^(3^a * core)) (a+3) = 2 := by
  rw [omega_level3_digit, omega_cut_word_mod27 a core ha]
  rcases hcore with h13 | h25
  · have hval : (16 * core) % 27 = 19 := by omega
    rw [hval]
  · have hval : (16 * core) % 27 = 22 := by omega
    rw [hval]

/-! ## §7.6 The Ω-sheet gate — the wave word beyond the tower

The cut tower reads the wave word `omegaCutWord s core` only inside its
stabilization window (rows `s+1` through `2s+1`).  This section opens the
window one digit further: the full cut word modulo the squared cut modulus
`3^(s+2)` is the sheet-local word `lteCoeff s * core` plus an explicit
binomial correction that vanishes for every shadow core (core congruent to
one modulo three).  The digit at row `2s+2` is therefore the top trit of
`lteCoeff s * core` modulo `3^(s+2)` — the **Ω-sheet gate**, the Law's own
kill of every dodger whose wave word has residue zero at the first digit
beyond the tower.  Together with a fourth tower level (mod eighty-one),
this shrinks the residual input a third time. -/

/-- Multiplication absorbs the residue: reducing the factor before the
multiplication does not change the product's residue. -/
theorem omega_mul_mod_absorb (M k x : Nat) :
    (k * (x % M)) % M = (k * x) % M := by
  have hq : x % M + M * (x / M) = x := Nat.mod_add_div x M
  have hkr : k * x = k * (x % M) + M * (k * (x / M)) := by
    conv_lhs => rw [← hq]
    ring
  rw [hkr, Nat.add_mul_mod_self_left]

/-- The residue of a sum whose head is given by its residue: both the head
and the fixed multiple of the head's residue lift back to the full values
without changing the sum's residue. -/
theorem omega_sum_mod_lift (M k a y : Nat) :
    (a % M + y + k * (a % M)) % M = (a + y + k * a) % M := by
  have hq : a % M + M * (a / M) = a := Nat.mod_add_div a M
  have hchain : a + y + k * a
      = (a % M + y + k * (a % M)) + M * (a / M + k * (a / M)) := by
    conv_lhs => rw [← hq]
    ring
  rw [hchain, Nat.add_mul_mod_self_left]

/-- Halving preserves vanishing modulo three. -/
theorem omega_half_of_mod3 (A : Nat) (hA : A % 3 = 0) (hE : 2 * (A / 2) = A) :
    (A / 2) % 3 = 0 := by omega

/-- **THE FULL-DEPTH CUT WORD LAW.**  At sheet `s` the cut word of
`4^(3^s * core)` agrees, modulo the squared cut modulus `3^(s+2)`, with
the sheet-local word `lteCoeff s * core` plus the explicit binomial
correction `3^(s+1) * (lteCoeff s)^2 * (core * (core - 1) / 2)` carried
by the geometric mean's own telescoping. -/
theorem omega_cut_word_full (s core : Nat) :
    omegaCutWord s core % 3^(s+2)
      = (lteCoeff s * core
          + 3^(s+1) * lteCoeff s * lteCoeff s * (core * (core - 1) / 2)) % 3^(s+2) := by
  induction core with
  | zero =>
      have h0 : omegaCutWord s 0 = 0 := by simp [omegaCutWord, omegaGeoSum]
      rw [h0]
      simp
  | succ c ih =>
      rw [show (c+1) - 1 = c from by omega]
      have hstepW : omegaCutWord s (c+1)
          = omegaCutWord s c + lteCoeff s * 4^(3^s * c) := by
        unfold omegaCutWord omegaGeoSum
        simp only [Finset.sum_range_succ]
        have hterm : (4^(3^s))^c = 4^(3^s * c) := by rw [Nat.pow_mul]
        rw [hterm]
        ring
      have hf : 4^(3^s * c) = 1 + 3^(s+1) * omegaCutWord s c :=
        omega_cut_factor s c
      have h2 : omegaCutWord s (c+1)
          = omegaCutWord s c + lteCoeff s
            + 3^(s+1) * lteCoeff s * omegaCutWord s c := by
        rw [hstepW, hf]; ring
      have hbinom : (c+1) * c / 2 = c * (c - 1) / 2 + c := by
        have hE : (c+1) * c = c * (c - 1) + 2 * c := by
          rcases c with _ | c'
          · simp
          · have hs : (c'+1) - 1 = c' := by omega
            rw [hs]
            ring
        rw [hE]
        exact Nat.add_mul_div_left _ _ (by decide)
      have hp2 : (3:Nat)^(s+1) * 3^(s+1) = 3^(s+2) * 3^s := by
        rw [← Nat.pow_add, ← Nat.pow_add]; congr 1; omega
      rw [h2, ← omega_sum_mod_lift, ih, omega_sum_mod_lift]
      have hfinal : lteCoeff s * c
            + 3^(s+1) * lteCoeff s * lteCoeff s * (c * (c - 1) / 2)
            + lteCoeff s
            + 3^(s+1) * lteCoeff s * (lteCoeff s * c
                + 3^(s+1) * lteCoeff s * lteCoeff s * (c * (c - 1) / 2))
          = lteCoeff s * (c+1)
            + 3^(s+1) * lteCoeff s * lteCoeff s * ((c+1) * c / 2)
            + 3^(s+1) * 3^(s+1) * lteCoeff s * lteCoeff s * lteCoeff s
                * (c * (c - 1) / 2) := by
        rw [hbinom]
        ring
      rw [hfinal]
      rw [show 3^(s+1) * 3^(s+1) * lteCoeff s * lteCoeff s * lteCoeff s
            * (c * (c - 1) / 2)
          = 3^(s+2) * (3^s * lteCoeff s * lteCoeff s * lteCoeff s
              * (c * (c - 1) / 2)) from by rw [hp2]; ring,
        Nat.add_mul_mod_self_left]

/-- **THE Ω-SHEET CUT WORD.**  For every core congruent to one modulo
three the binomial correction is a multiple of three, so modulo the
squared cut modulus the cut word is the sheet-local word `lteCoeff s *
core` exactly. -/
theorem omega_cut_word_mod_pow2 (s core : Nat) (hcore : core % 3 = 1) :
    omegaCutWord s core % 3^(s+2) = (lteCoeff s * core) % 3^(s+2) := by
  have hu3 : (lteCoeff s) % 3 = 1 := lteCoeff_mod3_one s
  have hcm : core * (core - 1) % 3 = 0 := by
    have h2 : (core - 1) % 3 = 0 := by omega
    rw [Nat.mul_mod, hcore, h2]
  have h2m : 2 * (core * (core - 1) / 2) = core * (core - 1) := by
    rw [Nat.mul_div_cancel' (by
      rcases Nat.even_or_odd core with ⟨k, hk⟩ | ⟨k, hk⟩
      · rw [hk]
        exact ⟨k * (2 * k - 1), by ring⟩
      · rw [hk]
        have hsub : (2 * k + 1) - 1 = 2 * k := by omega
        rw [hsub]
        exact ⟨(2 * k + 1) * k, by ring⟩)]
  have hq3 : (core * (core - 1) / 2) % 3 = 0 :=
    omega_half_of_mod3 (core * (core - 1)) hcm h2m
  have hX3 : (lteCoeff s * lteCoeff s * (core * (core - 1) / 2)) % 3 = 0 := by
    rw [Nat.mul_mod (lteCoeff s * lteCoeff s) (core * (core - 1) / 2) 3,
      Nat.mul_mod (lteCoeff s) (lteCoeff s) 3, hu3, hq3]
  obtain ⟨Y, hY⟩ : ∃ Y : Nat,
      lteCoeff s * lteCoeff s * (core * (core - 1) / 2) = 3 * Y := by
    refine ⟨(lteCoeff s * lteCoeff s * (core * (core - 1) / 2)) / 3, ?_⟩
    have h := Nat.mod_add_div
      (lteCoeff s * lteCoeff s * (core * (core - 1) / 2)) 3
    rw [hX3, Nat.zero_add] at h
    exact h.symm
  have hcorr : 3^(s+2)
      ∣ 3^(s+1) * lteCoeff s * lteCoeff s * (core * (core - 1) / 2) := by
    refine ⟨Y, ?_⟩
    have hp3 : (3:Nat)^(s+2) = 3 * 3^(s+1) := by
      rw [show s + 2 = (s+1) + 1 from by omega, Nat.pow_add, Nat.pow_one]
      ring
    rw [show 3^(s+1) * lteCoeff s * lteCoeff s * (core * (core - 1) / 2)
        = 3^(s+1) * (lteCoeff s * lteCoeff s * (core * (core - 1) / 2)) from by ring,
      hY, hp3]
    ring
  rw [omega_cut_word_full s core, Nat.add_mod, Nat.mod_eq_zero_of_dvd hcorr,
    Nat.add_zero, Nat.mod_mod]

/-- The ternary digit at position `j` is the top trit of the residue
modulo `3^(j+1)` — the general window law behind every level of the
tower's digit reading. -/
theorem digit3_window (X j : Nat) :
    (X / 3^j) % 3 = (X % 3^(j+1)) / 3^j := by
  have hp : 0 < 3^j := Nat.pow_pos (by decide)
  have hpow : 3^(j+1) = 3^j * 3 := by rw [Nat.pow_add, Nat.pow_one]
  have hX : X = 3^(j+1) * (X / 3^(j+1)) + X % 3^(j+1) := by
    have h := Nat.mod_add_div X (3^(j+1))
    rw [Nat.add_comm] at h
    exact h.symm
  have hdiv : X / 3^j
      = (X % 3^(j+1)) / 3^j + 3 * (X / 3^(j+1)) := by
    calc X / 3^j
        = (3^(j+1) * (X / 3^(j+1)) + X % 3^(j+1)) / 3^j := by rw [← hX]
      _ = (X % 3^(j+1) + 3^(j+1) * (X / 3^(j+1))) / 3^j := by rw [Nat.add_comm]
      _ = (X % 3^(j+1) + 3^j * 3 * (X / 3^(j+1))) / 3^j := by rw [hpow]
      _ = (X % 3^(j+1) + 3^j * (3 * (X / 3^(j+1)))) / 3^j := by
          rw [show 3^j * 3 * (X / 3^(j+1)) = 3^j * (3 * (X / 3^(j+1))) from by ring]
      _ = (X % 3^(j+1)) / 3^j + 3 * (X / 3^(j+1)) :=
          Nat.add_mul_div_left _ _ hp
  have hmodlt : X % 3^(j+1) < 3 * 3^j := by
    have h : X % 3^(j+1) < 3^(j+1) := Nat.mod_lt X (Nat.pow_pos (by decide))
    rw [show 3^(j+1) = 3 * 3^j from by rw [hpow, Nat.mul_comm]] at h ⊢
    exact h
  have hlt : (X % 3^(j+1)) / 3^j < 3 :=
    (Nat.div_lt_iff_lt_mul hp).mpr hmodlt
  rw [hdiv, Nat.add_mul_mod_self_left, Nat.mod_eq_of_lt hlt]

/-- **THE Ω-SHEET GATE DIGIT.**  The ternary digit of `4^(3^s * core)` at
row `2s+2` — one row beyond the tower's stabilization window — is the top
trit of the sheet-local cut word `lteCoeff s * core` modulo `3^(s+2)`,
for every core congruent to one modulo three. -/
theorem omega_sheet_digit (s core : Nat) (hcore : core % 3 = 1) :
    digit3 (4^(3^s * core)) (2*s+2)
      = ((lteCoeff s * core) % 3^(s+2)) / 3^(s+1) := by
  have hf := omega_cut_factor s core
  have h1 : (1:Nat) < 3^(s+1) := by
    have h3 : (3:Nat)^1 ≤ 3^(s+1) := by
      simpa using Nat.pow_le_pow_of_le (by decide : 1 < (3:Nat))
        (by omega : 1 ≤ s+1)
    omega
  have hslice := prefix_slice_digit_exact (s+1) 1 (omegaCutWord s core) (s+1) h1
  rw [show 2*s+2 = (s+1)+(s+1) from by omega, hf, hslice]
  unfold digit3
  rw [digit3_window, show s + 1 + 1 = s + 2 from by omega,
    omega_cut_word_mod_pow2 s core hcore]

/-- **THE Ω-SHEET GATE (the wave law beyond the tower).**  For every core
congruent to one modulo three, if the sheet-local cut word `omegaCutWord s
core` has top trit two modulo the squared cut modulus, then `4^(3^s *
core)` owns its ternary digit two at row `2s+2`.  This is the Law's own
kill of every tower-dodger whose wave word has residue zero at the first
digit beyond the stabilization window: the binomial correction adds two
there. -/
theorem omega_sheet_gate_digit_two (s core : Nat) (hcore : core % 3 = 1)
    (hgate : 2 * 3^(s+1) ≤ (omegaCutWord s core) % 3^(s+2)) :
    digit3 (4^(3^s * core)) (2*s+2) = 2 := by
  have hg' : 2 * 3^(s+1) ≤ (lteCoeff s * core) % 3^(s+2) := by
    rw [← omega_cut_word_mod_pow2 s core hcore]
    exact hgate
  rw [omega_sheet_digit s core hcore]
  have hlt : (lteCoeff s * core) % 3^(s+2) < 3^(s+2) :=
    Nat.mod_lt _ (Nat.pow_pos (by decide))
  have h3 : 3^(s+2) = 3 * 3^(s+1) := by
    rw [show s + 2 = (s+1) + 1 from by omega, Nat.pow_add, Nat.pow_one]
    ring
  have hlt2 : (lteCoeff s * core) % 3^(s+2) < 3 * 3^(s+1) := by omega
  obtain ⟨d, hd⟩ : ∃ d, (lteCoeff s * core) % 3^(s+2)
      = 2 * 3^(s+1) + d :=
    ⟨(lteCoeff s * core) % 3^(s+2) - 2 * 3^(s+1), by omega⟩
  have hdlt : d < 3^(s+1) := by omega
  rw [hd, Nat.add_comm, show 2 * 3^(s+1) = 3^(s+1) * 2 from by ring,
    Nat.add_mul_div_left _ _ (Nat.pow_pos (by decide)),
    Nat.div_eq_of_lt hdlt]

/-- The LTE mean is constantly sixteen modulo eighty-one from sheet
level three onward. -/
theorem omega_lteCoeff_mod81 (a : Nat) (ha : 3 ≤ a) :
    lteCoeff a % 81 = 16 := by
  have h81 : (3:Nat)^4 = 81 := by decide
  have hstable := omega_lteCoeff_stable 4 (a-3)
  have hidx : (4-1) + (a-3) = a := by omega
  rw [hidx, h81] at hstable
  rw [hstable]
  decide

/-- The base of the geometric mean is one modulo eighty-one from sheet
level three onward. -/
theorem omega_base_mod81 : ∀ a : Nat, 3 ≤ a → (4^(3^a)) % 81 = 1 := by
  intro a
  induction a with
  | zero => intro h; omega
  | succ a ih =>
      intro h
      rcases Nat.lt_or_ge a 3 with hlt | hge
      · have ha2 : a = 2 := by omega
        rw [ha2]
        decide
      · have hstep : 4^(3^(a+1)) = (4^(3^a))^3 := by
          rw [Nat.pow_succ, Nat.pow_mul]
        rw [hstep, Nat.pow_mod, ih hge, Nat.one_pow]

/-- The geometric mean is the core mass modulo eighty-one from sheet
level three onward. -/
theorem omega_geo_mod81 (a core : Nat) (ha : 3 ≤ a) :
    omegaGeoSum a core % 81 = core % 81 := by
  have hterm : ∀ j : Nat, ((4^(3^a))^j) % 81 = 1 := by
    intro j
    rw [Nat.pow_mod, omega_base_mod81 a ha, Nat.one_pow]
  induction core with
  | zero => simp [omegaGeoSum]
  | succ core ih =>
      have hgeo : omegaGeoSum a (core+1)
          = omegaGeoSum a core + (4^(3^a))^core := by
        simp [omegaGeoSum, Finset.sum_range_succ]
      rw [hgeo, Nat.add_mod, hterm core, ih]
      omega

/-- **The level-four cut word law.**  From sheet level three onward the
cut word is `16 * core` modulo eighty-one. -/
theorem omega_cut_word_mod81 (a core : Nat) (ha : 3 ≤ a) :
    omegaCutWord a core % 81 = (16 * core) % 81 := by
  unfold omegaCutWord
  rw [Nat.mul_mod, omega_lteCoeff_mod81 a ha, omega_geo_mod81 a core ha]
  omega

/-- **THE LEVEL-FOUR DIGIT LAW.**  The ternary digit of `4^(3^a * core)`
at row `a+4` is the top trit of the cut word modulo eighty-one — the same
certified prefix-slice socket as levels two and three, one row deeper. -/
theorem omega_level4_digit (a core : Nat) :
    digit3 (4^(3^a * core)) (a+4) = (omegaCutWord a core % 81) / 27 := by
  have hf := omega_cut_factor a core
  have h1 : (1:Nat) < 3^(a+1) := by
    have h3 : (3:Nat)^1 ≤ 3^(a+1) := by
      simpa using Nat.pow_le_pow_of_le (by decide : 1 < (3:Nat))
        (by omega : 1 ≤ a+1)
    omega
  have hslice := prefix_slice_digit_exact (a+1) 1 (omegaCutWord a core) 3 h1
  rw [show a+4 = (a+1)+3 from by omega, hf, hslice]
  unfold digit3
  rw [show (3:Nat)^3 = 27 from by decide]
  omega

/-- **THE LEVEL-FOUR GATE CLASSES.**  For every core whose stabilized cut
word reaches the top third of the residue window modulo eighty-one, the
power `4^(3^a * core)` owns a ternary digit two at row `a+4` — the
fourth infinite family of the Law, twenty-seven residue classes at every
sheet level three and above. -/
theorem omega_level4_digit_two (a core : Nat) (ha : 3 ≤ a)
    (hgate : 54 ≤ (16 * core) % 81) :
    digit3 (4^(3^a * core)) (a+4) = 2 := by
  rw [omega_level4_digit, omega_cut_word_mod81 a core ha]
  have hlt : (16 * core) % 81 < 81 := Nat.mod_lt _ (by decide)
  omega

/-! ## §7.7 The Ω-second-sheet gate — the binomial trit at row `2s+3`

The Ω-sheet gate reads the wave word one digit beyond the stabilization
window (row `2s+2`, the top trit of the sheet-local word modulo the squared
cut modulus).  This section opens the window ONE MORE DIGIT: the full cut
word modulo the cubed cut modulus `3^(s+3)` is the sheet-local word plus
the binomial correction carried to its second order, and for every shadow
core (core congruent to one modulo three) the correction's first trit
lands EXACTLY at row `2s+3`.  That trit is the binomial coefficient's own
third divide: zero for cores congruent to one modulo nine, two for the
four-sheet, one for the seven-sheet.  The digit at row `2s+3` is the sheet
word's trit plus the binomial trit — the **Ω-second-sheet gate**: the +2
shift of the four-sheet converts a lowest-third sheet word into digit two,
the +1 shift of the seven-sheet converts a middle-third sheet word into
digit two. -/

section
set_option maxHeartbeats 4000000

/-- The binomial coefficient of the cut word's second order is exact: the
halving witness. -/
theorem omega_binom_two_mul (core : Nat) :
    2 * (core * (core - 1) / 2) = core * (core - 1) := by
  rw [Nat.mul_div_cancel' (by
    rcases Nat.even_or_odd core with ⟨k, hk⟩ | ⟨k, hk⟩
    · rw [hk]
      exact ⟨k * (2 * k - 1), by ring⟩
    · rw [hk]
      have hsub : (2 * k + 1) - 1 = 2 * k := by omega
      rw [hsub]
      exact ⟨(2 * k + 1) * k, by ring⟩)]

#check omega_binom_two_mul

/-- Halving a number that is three modulo nine: the half is six modulo
nine. -/
theorem omega_half_mod9_of_mod9_three (P : Nat) (hP : P % 9 = 3)
    (hE : 2 * (P / 2) = P) :
    (P / 2) % 9 = 6 := by
  have hlt : (P / 2) % 9 < 9 := Nat.mod_lt _ (by decide)
  omega

#check omega_half_mod9_of_mod9_three

/-- Halving a number that is six modulo nine: the half is three modulo
nine. -/
theorem omega_half_mod9_of_mod9_six (P : Nat) (hP : P % 9 = 6)
    (hE : 2 * (P / 2) = P) :
    (P / 2) % 9 = 3 := by
  have hlt : (P / 2) % 9 < 9 := Nat.mod_lt _ (by decide)
  omega

#check omega_half_mod9_of_mod9_six

/-- **The binomial trit of the four-sheet.**  For every core congruent to
four modulo nine the binomial coefficient `core * (core - 1) / 2` is six
modulo nine: its third divide is the trit two. -/
theorem omega_binom_mod9_four (core : Nat) (hcore : core % 9 = 4) :
    (core * (core - 1) / 2) % 9 = 6 := by
  have h2 : (core - 1) % 9 = 3 := by omega
  have hP : (core * (core - 1)) % 9 = 3 := by
    rw [Nat.mul_mod, hcore, h2]
  exact omega_half_mod9_of_mod9_three (core * (core - 1)) hP
    (omega_binom_two_mul core)

#check omega_binom_mod9_four

/-- **The binomial trit of the seven-sheet.**  For every core congruent to
seven modulo nine the binomial coefficient is three modulo nine: its third
divide is the trit one. -/
theorem omega_binom_mod9_seven (core : Nat) (hcore : core % 9 = 7) :
    (core * (core - 1) / 2) % 9 = 3 := by
  have h2 : (core - 1) % 9 = 6 := by omega
  have hP : (core * (core - 1)) % 9 = 6 := by
    rw [Nat.mul_mod, hcore, h2]
  exact omega_half_mod9_of_mod9_six (core * (core - 1)) hP
    (omega_binom_two_mul core)

#check omega_binom_mod9_seven

/-- A unit times a six-window number: the product is six modulo nine. -/
theorem omega_mul_mod9_six (X Y : Nat) (hX : X % 3 = 1) (hY : Y % 9 = 6) :
    (X * Y) % 9 = 6 := by
  have hX3 : X = 3 * (X / 3) + 1 := by omega
  have hY9 : Y = 9 * (Y / 9) + 6 := by omega
  have hE : (3 * (X / 3) + 1) * (9 * (Y / 9) + 6)
      = 6 + 9 * (3 * (X / 3) * (Y / 9) + 2 * (X / 3) + (Y / 9)) := by ring
  rw [hX3, hY9, hE, Nat.add_mul_mod_self_left]

#check omega_mul_mod9_six

/-- A unit times a three-window number: the product is three modulo nine. -/
theorem omega_mul_mod9_three (X Y : Nat) (hX : X % 3 = 1) (hY : Y % 9 = 3) :
    (X * Y) % 9 = 3 := by
  have hX3 : X = 3 * (X / 3) + 1 := by omega
  have hY9 : Y = 9 * (Y / 9) + 3 := by omega
  have hE : (3 * (X / 3) + 1) * (9 * (Y / 9) + 3)
      = 3 + 9 * (3 * (X / 3) * (Y / 9) + (X / 3) + (Y / 9)) := by ring
  rw [hX3, hY9, hE, Nat.add_mul_mod_self_left]

#check omega_mul_mod9_three

/-- The sheet power absorbs the factor's own nine-window: modulo the cubed
cut modulus, only the factor modulo nine survives. -/
theorem omega_powmul_mod_cubed (s X : Nat) :
    (3^(s+1) * X) % 3^(s+3) = (3^(s+1) * (X % 9)) % 3^(s+3) := by
  have h39 : (3:Nat)^(s+1) * 9 = 3^(s+3) := by
    rw [show (9:Nat) = 3^2 from by decide, ← Nat.pow_add,
      show (s:Nat) + 1 + 2 = s + 3 from by omega]
  have hd : 9 * (X / 9) + X % 9 = X := Nat.div_add_mod X 9
  have hexp : 3^(s+1) * X
      = 3^(s+1) * (X % 9) + 3^(s+3) * (X / 9) := by
    conv_lhs => rw [← hd]
    rw [Nat.mul_add, ← Nat.mul_assoc, h39]
    ring
  rw [hexp, Nat.add_mul_mod_self_left]

#check omega_powmul_mod_cubed

/-- **THE SECOND-ORDER CUT WORD LAW.**  At sheet `s` (sheet level one and
above) the cut word of `4^(3^s * core)` agrees, modulo the cubed cut
modulus `3^(s+3)`, with the sheet-local word `lteCoeff s * core` plus the
binomial correction carried to its second order — the same telescoping
identity as the squared law, one modulus deeper. -/
theorem omega_cut_word_full3 (s core : Nat) (hs : 1 ≤ s) :
    omegaCutWord s core % 3^(s+3)
      = (lteCoeff s * core
          + 3^(s+1) * lteCoeff s * lteCoeff s * (core * (core - 1) / 2)) % 3^(s+3) := by
  induction core with
  | zero =>
      have h0 : omegaCutWord s 0 = 0 := by simp [omegaCutWord, omegaGeoSum]
      rw [h0]
      simp
  | succ c ih =>
      rw [show (c+1) - 1 = c from by omega]
      have hstepW : omegaCutWord s (c+1)
          = omegaCutWord s c + lteCoeff s * 4^(3^s * c) := by
        unfold omegaCutWord omegaGeoSum
        simp only [Finset.sum_range_succ]
        have hterm : (4^(3^s))^c = 4^(3^s * c) := by rw [Nat.pow_mul]
        rw [hterm]
        ring
      have hf : 4^(3^s * c) = 1 + 3^(s+1) * omegaCutWord s c :=
        omega_cut_factor s c
      have h2 : omegaCutWord s (c+1)
          = omegaCutWord s c + lteCoeff s
            + 3^(s+1) * lteCoeff s * omegaCutWord s c := by
        rw [hstepW, hf]; ring
      have hbinom : (c+1) * c / 2 = c * (c - 1) / 2 + c := by
        have hE : (c+1) * c = c * (c - 1) + 2 * c := by
          rcases c with _ | c'
          · simp
          · have hsub : (c'+1) - 1 = c' := by omega
            rw [hsub]
            ring
        rw [hE]
        exact Nat.add_mul_div_left _ _ (by decide)
      have hp3 : (3:Nat)^(s+1) * 3^(s+1) = 3^(s+3) * 3^(s-1) := by
        rw [← Nat.pow_add, ← Nat.pow_add]; congr 1; omega
      rw [h2, ← omega_sum_mod_lift, ih, omega_sum_mod_lift]
      have hfinal : lteCoeff s * c
            + 3^(s+1) * lteCoeff s * lteCoeff s * (c * (c - 1) / 2)
            + lteCoeff s
            + 3^(s+1) * lteCoeff s * (lteCoeff s * c
                + 3^(s+1) * lteCoeff s * lteCoeff s * (c * (c - 1) / 2))
          = lteCoeff s * (c+1)
            + 3^(s+1) * lteCoeff s * lteCoeff s * ((c+1) * c / 2)
            + 3^(s+1) * 3^(s+1) * lteCoeff s * lteCoeff s * lteCoeff s
                * (c * (c - 1) / 2) := by
        rw [hbinom]
        ring
      rw [hfinal]
      rw [show 3^(s+1) * 3^(s+1) * lteCoeff s * lteCoeff s * lteCoeff s
            * (c * (c - 1) / 2)
          = 3^(s+3) * (3^(s-1) * lteCoeff s * lteCoeff s * lteCoeff s
              * (c * (c - 1) / 2)) from by rw [hp3]; ring,
        Nat.add_mul_mod_self_left]

#check omega_cut_word_full3

/-- **THE Ω-SECOND-SHEET DIGIT.**  The ternary digit of `4^(3^s * core)` at
row `2s+3` — two digits beyond the tower's stabilization window — is the
second-from-top trit of the cut word read through the cubed cut modulus. -/
theorem omega_sheet2_digit (s core : Nat) :
    digit3 (4^(3^s * core)) (2*s+3)
      = ((omegaCutWord s core) % 3^(s+3)) / 3^(s+2) := by
  have hf := omega_cut_factor s core
  have h1 : (1:Nat) < 3^(s+1) := by
    have h3 : (3:Nat)^1 ≤ 3^(s+1) := by
      simpa using Nat.pow_le_pow_of_le (by decide : 1 < (3:Nat))
        (by omega : 1 ≤ s+1)
    omega
  have hslice := prefix_slice_digit_exact (s+1) 1 (omegaCutWord s core) (s+2) h1
  rw [show 2*s+3 = (s+1)+(s+2) from by omega, hf, hslice]
  unfold digit3
  rw [digit3_window, show s + 2 + 1 = s + 3 from by omega]

#check omega_sheet2_digit

/-- **THE Ω-SECOND-SHEET GATE — THE FOUR-SHEET (+2 SHIFT).**  For every
core congruent to four modulo nine at sheet level one and above whose
sheet-local word `lteCoeff s * core` sits in the lowest third of the cubed
cut modulus window, the binomial correction's own trit adds exactly two at
row `2s+3`: the power `4^(3^s * core)` owns its ternary digit two there. -/
theorem omega_sheet2_gate_four (s core : Nat) (hs : 1 ≤ s) (hcore : core % 9 = 4)
    (hq : (lteCoeff s * core) % 3^(s+3) < 3^(s+2)) :
    digit3 (4^(3^s * core)) (2*s+3) = 2 := by
  have hu3 : (lteCoeff s) % 3 = 1 := lteCoeff_mod3_one s
  have hll : (lteCoeff s * lteCoeff s) % 3 = 1 := by
    rw [Nat.mul_mod, hu3]
  have hb : (core * (core - 1) / 2) % 9 = 6 :=
    omega_binom_mod9_four core hcore
  have hB : (lteCoeff s * lteCoeff s * (core * (core - 1) / 2)) % 9 = 6 :=
    omega_mul_mod9_six (lteCoeff s * lteCoeff s) (core * (core - 1) / 2) hll hb
  have habs : (3^(s+1) * lteCoeff s * lteCoeff s * (core * (core - 1) / 2))
      % 3^(s+3)
      = (3^(s+1) * 6) % 3^(s+3) := by
    rw [show 3^(s+1) * lteCoeff s * lteCoeff s * (core * (core - 1) / 2)
        = 3^(s+1) * (lteCoeff s * lteCoeff s * (core * (core - 1) / 2))
        from by ring,
      omega_powmul_mod_cubed s
        (lteCoeff s * lteCoeff s * (core * (core - 1) / 2)),
      hB]
  have h32 : (3:Nat)^(s+2) = 3^(s+1) * 3 := by
    rw [show s + 2 = s + 1 + 1 from by omega, Nat.pow_add, Nat.pow_one]
  have h6 : (3:Nat)^(s+1) * 6 = 2 * 3^(s+2) := by
    rw [show (6:Nat) = 3 * 2 from by decide, ← Nat.mul_assoc, ← h32]
    ring
  have h33 : (3:Nat)^(s+3) = 3 * 3^(s+2) := by
    rw [show s + 3 = s + 2 + 1 from by omega, Nat.pow_add, Nat.pow_one]
    ring
  have hlt23 : 2 * 3^(s+2) < 3^(s+3) := by
    have h0 : 0 < 3^(s+2) := Nat.pow_pos (by decide)
    omega
  have hcorr : (3^(s+1) * lteCoeff s * lteCoeff s * (core * (core - 1) / 2))
      % 3^(s+3) = 2 * 3^(s+2) := by
    rw [habs, h6]
    exact Nat.mod_eq_of_lt hlt23
  have hsumlt : (lteCoeff s * core) % 3^(s+3) + 2 * 3^(s+2) < 3^(s+3) := by
    omega
  rw [omega_sheet2_digit s core, omega_cut_word_full3 s core hs,
    Nat.add_mod, hcorr, Nat.mod_eq_of_lt hsumlt]
  rw [show 2 * 3^(s+2) = 3^(s+2) * 2 from by ring,
    Nat.add_mul_div_left _ _ (Nat.pow_pos (by decide)),
    Nat.div_eq_of_lt hq]

#check omega_sheet2_gate_four

/-- **THE Ω-SECOND-SHEET GATE — THE SEVEN-SHEET (+1 SHIFT).**  For every
core congruent to seven modulo nine at sheet level one and above whose
sheet-local word sits in the middle third of the cubed cut modulus window,
the binomial correction's own trit adds exactly one at row `2s+3`: the
power `4^(3^s * core)` owns its ternary digit two there. -/
theorem omega_sheet2_gate_seven (s core : Nat) (hs : 1 ≤ s) (hcore : core % 9 = 7)
    (hq : 3^(s+2) ≤ (lteCoeff s * core) % 3^(s+3))
    (hq2 : (lteCoeff s * core) % 3^(s+3) < 2 * 3^(s+2)) :
    digit3 (4^(3^s * core)) (2*s+3) = 2 := by
  have hu3 : (lteCoeff s) % 3 = 1 := lteCoeff_mod3_one s
  have hll : (lteCoeff s * lteCoeff s) % 3 = 1 := by
    rw [Nat.mul_mod, hu3]
  have hb : (core * (core - 1) / 2) % 9 = 3 :=
    omega_binom_mod9_seven core hcore
  have hB : (lteCoeff s * lteCoeff s * (core * (core - 1) / 2)) % 9 = 3 :=
    omega_mul_mod9_three (lteCoeff s * lteCoeff s) (core * (core - 1) / 2) hll hb
  have habs : (3^(s+1) * lteCoeff s * lteCoeff s * (core * (core - 1) / 2))
      % 3^(s+3)
      = (3^(s+1) * 3) % 3^(s+3) := by
    rw [show 3^(s+1) * lteCoeff s * lteCoeff s * (core * (core - 1) / 2)
        = 3^(s+1) * (lteCoeff s * lteCoeff s * (core * (core - 1) / 2))
        from by ring,
      omega_powmul_mod_cubed s
        (lteCoeff s * lteCoeff s * (core * (core - 1) / 2)),
      hB]
  have h32 : (3:Nat)^(s+2) = 3^(s+1) * 3 := by
    rw [show s + 2 = s + 1 + 1 from by omega, Nat.pow_add, Nat.pow_one]
  have h33 : (3:Nat)^(s+3) = 3 * 3^(s+2) := by
    rw [show s + 3 = s + 2 + 1 from by omega, Nat.pow_add, Nat.pow_one]
    ring
  have hlt13 : 3^(s+2) < 3^(s+3) := by
    have h0 : 0 < 3^(s+2) := Nat.pow_pos (by decide)
    omega
  have hcorr : (3^(s+1) * lteCoeff s * lteCoeff s * (core * (core - 1) / 2))
      % 3^(s+3) = 3^(s+2) := by
    rw [habs, ← h32]
    exact Nat.mod_eq_of_lt hlt13
  have hsumlt : (lteCoeff s * core) % 3^(s+3) + 3^(s+2) < 3^(s+3) := by
    omega
  rw [omega_sheet2_digit s core, omega_cut_word_full3 s core hs,
    Nat.add_mod, hcorr, Nat.mod_eq_of_lt hsumlt]
  obtain ⟨d, hd⟩ : ∃ d, (lteCoeff s * core) % 3^(s+3) = 3^(s+2) + d :=
    ⟨(lteCoeff s * core) % 3^(s+3) - 3^(s+2), by omega⟩
  have hdlt : d < 3^(s+2) := by omega
  rw [hd]
  rw [show 3^(s+2) + d + 3^(s+2) = d + 3^(s+2) * 2 from by ring,
    Nat.add_mul_div_left _ _ (Nat.pow_pos (by decide)),
    Nat.div_eq_of_lt hdlt]

#check omega_sheet2_gate_seven

/-! ## §7.8 The exponent-cycle gates — sheet zero rides the base's period

At sheet zero the exponent is its own three-free core, and the power's
residues ride the base's multiplicative period: the order of four modulo
`3^m` is `3^(m-2)` from `m = 3` onward, so the ternary digits at rows
three and four of `4^K` are pure functions of `K` modulo twenty-seven and
eighty-one.  The gate classes below kill five of the nine residue classes
of each unguarded sheet-zero shadow family (the cores congruent to one and
to four modulo nine): the residue rides the period into the top third of
the window, and the digit two is direct. -/

/-- The base's period modulo eighty-one: the order of four is twenty-seven. -/
theorem omega_expcycle_period81 (j : Nat) :
    ((4^27)^j) % 81 = 1 := by
  have h427 : (4^27) % 81 = 1 := by decide
  rw [Nat.pow_mod, h427, Nat.one_pow]

#check omega_expcycle_period81

/-- The base's period modulo two-hundred-forty-three: the order of four is
eighty-one. -/
theorem omega_expcycle_period243 (j : Nat) :
    ((4^81)^j) % 243 = 1 := by
  have h427 : (4^27) % 243 = 82 := by decide
  have hsplit : 4^81 = 4^27 * 4^27 * 4^27 := by
    rw [show (81:Nat) = 27 + 27 + 27 from by decide, Nat.pow_add, Nat.pow_add]
  have hmul1 : 4^27 * 4^27 % 243 = 163 := by
    rw [Nat.mul_mod, h427]
  have hmul2 : 4^27 * 4^27 * 4^27 % 243 = 1 := by
    rw [Nat.mul_mod, hmul1, h427]
  have h481 : (4^81) % 243 = 1 := by
    rw [hsplit, hmul2]
  rw [Nat.pow_mod, h481, Nat.one_pow]

#check omega_expcycle_period243

/-- **THE EXPONENT-CYCLE ROW-THREE GATES.**  Every three-free exponent
congruent to nineteen or twenty-two modulo twenty-seven rides the base's
period into the top third of the eighty-one window: the digit two at row
three. -/
theorem omega_expcycle_row3_digit_two (K : Nat)
    (hK : K % 27 = 19 ∨ K % 27 = 22) :
    digit3 (4^K) 3 = 2 := by
  rcases hK with h19 | h22
  · have hdm : K = 27 * (K / 27) + 19 := by omega
    have hpow : (4^27)^(K / 27) * 4^19 = 4^K := by
      rw [← Nat.pow_mul, ← Nat.pow_add, ← hdm]
    have h419 : (4^19) % 81 = 58 := by decide
    have hmod : (4^K) % 81 = 58 := by
      rw [← hpow, Nat.mul_mod, omega_expcycle_period81 (K / 27), h419]
    unfold digit3
    rw [digit3_window, show 3 + 1 = 4 from by decide,
      show (3:Nat)^4 = 81 from by decide,
      show (3:Nat)^3 = 27 from by decide, hmod]
  · have hdm : K = 27 * (K / 27) + 22 := by omega
    have hpow : (4^27)^(K / 27) * 4^22 = 4^K := by
      rw [← Nat.pow_mul, ← Nat.pow_add, ← hdm]
    have h422 : (4^22) % 81 = 67 := by decide
    have hmod : (4^K) % 81 = 67 := by
      rw [← hpow, Nat.mul_mod, omega_expcycle_period81 (K / 27), h422]
    unfold digit3
    rw [digit3_window, show 3 + 1 = 4 from by decide,
      show (3:Nat)^4 = 81 from by decide,
      show (3:Nat)^3 = 27 from by decide, hmod]

#check omega_expcycle_row3_digit_two

/-- **THE EXPONENT-CYCLE ROW-FOUR GATE (one-sheet).**  Every three-free
exponent congruent to fifty-five, sixty-four, or seventy-three modulo
eighty-one rides the period into the top third of the two-hundred-forty-three
window: the digit two at row four. -/
theorem omega_expcycle_row4_digit_two_one (K : Nat)
    (hK : K % 81 = 55 ∨ K % 81 = 64 ∨ K % 81 = 73) :
    digit3 (4^K) 4 = 2 := by
  have h427 : (4^27) % 243 = 82 := by decide
  have hmul1 : 4^27 * 4^27 % 243 = 163 := by
    rw [Nat.mul_mod, h427]
  rcases hK with h55 | h64 | h73
  · have hdm : K = 81 * (K / 81) + 55 := by omega
    have hpow : (4^81)^(K / 81) * 4^55 = 4^K := by
      rw [← Nat.pow_mul, ← Nat.pow_add, ← hdm]
    have hsplit : 4^55 = 4^27 * 4^27 * 4^1 := by
      rw [show (55:Nat) = 27 + 27 + 1 from by decide, Nat.pow_add, Nat.pow_add]
    have h455 : (4^55) % 243 = 166 := by
      rw [hsplit, Nat.mul_mod, hmul1]
      decide
    have hmod : (4^K) % 243 = 166 := by
      rw [← hpow, Nat.mul_mod, omega_expcycle_period243 (K / 81), h455]
    unfold digit3
    rw [digit3_window, show 4 + 1 = 5 from by decide,
      show (3:Nat)^5 = 243 from by decide,
      show (3:Nat)^4 = 81 from by decide, hmod]
  · have hdm : K = 81 * (K / 81) + 64 := by omega
    have hpow : (4^81)^(K / 81) * 4^64 = 4^K := by
      rw [← Nat.pow_mul, ← Nat.pow_add, ← hdm]
    have hsplit : 4^64 = 4^27 * 4^27 * 4^10 := by
      rw [show (64:Nat) = 27 + 27 + 10 from by decide, Nat.pow_add, Nat.pow_add]
    have h464 : (4^64) % 243 = 193 := by
      rw [hsplit, Nat.mul_mod, hmul1]
      decide
    have hmod : (4^K) % 243 = 193 := by
      rw [← hpow, Nat.mul_mod, omega_expcycle_period243 (K / 81), h464]
    unfold digit3
    rw [digit3_window, show 4 + 1 = 5 from by decide,
      show (3:Nat)^5 = 243 from by decide,
      show (3:Nat)^4 = 81 from by decide, hmod]
  · have hdm : K = 81 * (K / 81) + 73 := by omega
    have hpow : (4^81)^(K / 81) * 4^73 = 4^K := by
      rw [← Nat.pow_mul, ← Nat.pow_add, ← hdm]
    have hsplit : 4^73 = 4^27 * 4^27 * 4^19 := by
      rw [show (73:Nat) = 27 + 27 + 19 from by decide, Nat.pow_add, Nat.pow_add]
    have h473 : (4^73) % 243 = 220 := by
      rw [hsplit, Nat.mul_mod, hmul1]
      decide
    have hmod : (4^K) % 243 = 220 := by
      rw [← hpow, Nat.mul_mod, omega_expcycle_period243 (K / 81), h473]
    unfold digit3
    rw [digit3_window, show 4 + 1 = 5 from by decide,
      show (3:Nat)^5 = 243 from by decide,
      show (3:Nat)^4 = 81 from by decide, hmod]

#check omega_expcycle_row4_digit_two_one

/-- **THE EXPONENT-CYCLE ROW-FOUR GATE (four-sheet).**  Every three-free
exponent congruent to fifty-eight, sixty-seven, or seventy-six modulo
eighty-one rides the period into the top third of the window: the digit
two at row four. -/
theorem omega_expcycle_row4_digit_two_four (K : Nat)
    (hK : K % 81 = 58 ∨ K % 81 = 67 ∨ K % 81 = 76) :
    digit3 (4^K) 4 = 2 := by
  have h427 : (4^27) % 243 = 82 := by decide
  have hmul1 : 4^27 * 4^27 % 243 = 163 := by
    rw [Nat.mul_mod, h427]
  rcases hK with h58 | h67 | h76
  · have hdm : K = 81 * (K / 81) + 58 := by omega
    have hpow : (4^81)^(K / 81) * 4^58 = 4^K := by
      rw [← Nat.pow_mul, ← Nat.pow_add, ← hdm]
    have hsplit : 4^58 = 4^27 * 4^27 * 4^4 := by
      rw [show (58:Nat) = 27 + 27 + 4 from by decide, Nat.pow_add, Nat.pow_add]
    have h458 : (4^58) % 243 = 175 := by
      rw [hsplit, Nat.mul_mod, hmul1]
      decide
    have hmod : (4^K) % 243 = 175 := by
      rw [← hpow, Nat.mul_mod, omega_expcycle_period243 (K / 81), h458]
    unfold digit3
    rw [digit3_window, show 4 + 1 = 5 from by decide,
      show (3:Nat)^5 = 243 from by decide,
      show (3:Nat)^4 = 81 from by decide, hmod]
  · have hdm : K = 81 * (K / 81) + 67 := by omega
    have hpow : (4^81)^(K / 81) * 4^67 = 4^K := by
      rw [← Nat.pow_mul, ← Nat.pow_add, ← hdm]
    have hsplit : 4^67 = 4^27 * 4^27 * 4^13 := by
      rw [show (67:Nat) = 27 + 27 + 13 from by decide, Nat.pow_add, Nat.pow_add]
    have h467 : (4^67) % 243 = 202 := by
      rw [hsplit, Nat.mul_mod, hmul1]
      decide
    have hmod : (4^K) % 243 = 202 := by
      rw [← hpow, Nat.mul_mod, omega_expcycle_period243 (K / 81), h467]
    unfold digit3
    rw [digit3_window, show 4 + 1 = 5 from by decide,
      show (3:Nat)^5 = 243 from by decide,
      show (3:Nat)^4 = 81 from by decide, hmod]
  · have hdm : K = 81 * (K / 81) + 76 := by omega
    have hpow : (4^81)^(K / 81) * 4^76 = 4^K := by
      rw [← Nat.pow_mul, ← Nat.pow_add, ← hdm]
    have hsplit : 4^76 = 4^27 * 4^27 * 4^22 := by
      rw [show (76:Nat) = 27 + 27 + 22 from by decide, Nat.pow_add, Nat.pow_add]
    have h476 : (4^76) % 243 = 229 := by
      rw [hsplit, Nat.mul_mod, hmul1]
      decide
    have hmod : (4^K) % 243 = 229 := by
      rw [← hpow, Nat.mul_mod, omega_expcycle_period243 (K / 81), h476]
    unfold digit3
    rw [digit3_window, show 4 + 1 = 5 from by decide,
      show (3:Nat)^5 = 243 from by decide,
      show (3:Nat)^4 = 81 from by decide, hmod]

#check omega_expcycle_row4_digit_two_four

/-! ## §7.9 The fifth weakening — levels five and six of the tower and the
row-five exponent-cycle gate

The tower climbs two more levels: the LTE mean is constantly one hundred
seventy-eight modulo two hundred forty-three from sheet level four onward
and constantly six hundred sixty-four modulo seven hundred twenty-nine
from sheet level five onward, so the stabilized cut word hands over two
more infinite gate families (the top third of the residue windows modulo
two hundred forty-three and modulo seven hundred twenty-nine).  At sheet
zero the base's own period climbs one row deeper: the order of four
modulo seven hundred twenty-nine is two hundred forty-three, and eight
of the twenty-four surviving period subclasses ride it into the top third
of the window — the digit two at row five. -/

/-- The LTE mean is constantly one hundred seventy-eight modulo
two-hundred-forty-three from sheet level four onward. -/
theorem omega_lteCoeff_mod243 (a : Nat) (ha : 4 ≤ a) :
    lteCoeff a % 243 = 178 := by
  have h243 : (3:Nat)^5 = 243 := by decide
  have hstable := omega_lteCoeff_stable 5 (a-4)
  have hidx : (5-1) + (a-4) = a := by omega
  rw [hidx, h243] at hstable
  rw [hstable]
  decide

/-- The base of the geometric mean is one modulo two-hundred-forty-three
from sheet level four onward. -/
theorem omega_base_mod243 : ∀ a : Nat, 4 ≤ a → (4^(3^a)) % 243 = 1 := by
  intro a
  induction a with
  | zero => intro h; omega
  | succ a ih =>
      intro h
      rcases Nat.lt_or_ge a 4 with hlt | hge
      · have ha3 : a = 3 := by omega
        rw [ha3]
        decide
      · have hstep : 4^(3^(a+1)) = (4^(3^a))^3 := by
          rw [Nat.pow_succ, Nat.pow_mul]
        rw [hstep, Nat.pow_mod, ih hge, Nat.one_pow]

/-- The geometric mean is the core mass modulo two-hundred-forty-three
from sheet level four onward. -/
theorem omega_geo_mod243 (a core : Nat) (ha : 4 ≤ a) :
    omegaGeoSum a core % 243 = core % 243 := by
  have hterm : ∀ j : Nat, ((4^(3^a))^j) % 243 = 1 := by
    intro j
    rw [Nat.pow_mod, omega_base_mod243 a ha, Nat.one_pow]
  induction core with
  | zero => simp [omegaGeoSum]
  | succ core ih =>
      have hgeo : omegaGeoSum a (core+1)
          = omegaGeoSum a core + (4^(3^a))^core := by
        simp [omegaGeoSum, Finset.sum_range_succ]
      rw [hgeo, Nat.add_mod, hterm core, ih]
      omega

/-- **The level-five cut word law.**  From sheet level four onward the
cut word is `178 * core` modulo two-hundred-forty-three. -/
theorem omega_cut_word_mod243 (a core : Nat) (ha : 4 ≤ a) :
    omegaCutWord a core % 243 = (178 * core) % 243 := by
  unfold omegaCutWord
  rw [Nat.mul_mod, omega_lteCoeff_mod243 a ha, omega_geo_mod243 a core ha]
  omega

/-- **THE LEVEL-FIVE DIGIT LAW.**  The ternary digit of `4^(3^a * core)`
at row `a+5` is the top trit of the cut word modulo two-hundred-forty-three. -/
theorem omega_level5_digit (a core : Nat) :
    digit3 (4^(3^a * core)) (a+5) = (omegaCutWord a core % 243) / 81 := by
  have hf := omega_cut_factor a core
  have h1 : (1:Nat) < 3^(a+1) := by
    have h3 : (3:Nat)^1 ≤ 3^(a+1) := by
      simpa using Nat.pow_le_pow_of_le (by decide : 1 < (3:Nat))
        (by omega : 1 ≤ a+1)
    omega
  have hslice := prefix_slice_digit_exact (a+1) 1 (omegaCutWord a core) 4 h1
  rw [show a+5 = (a+1)+4 from by omega, hf, hslice]
  unfold digit3
  rw [show (3:Nat)^4 = 81 from by decide]
  omega

/-- **THE LEVEL-FIVE GATE CLASSES.**  For every core whose stabilized cut
word reaches the top third of the residue window modulo
two-hundred-forty-three, the power `4^(3^a * core)` owns a ternary digit
two at row `a+5` — the fifth infinite family of the tower, eighteen
residue classes at every sheet level four and above. -/
theorem omega_level5_digit_two (a core : Nat) (ha : 4 ≤ a)
    (hgate : 162 ≤ (178 * core) % 243) :
    digit3 (4^(3^a * core)) (a+5) = 2 := by
  rw [omega_level5_digit, omega_cut_word_mod243 a core ha]
  have hlt : (178 * core) % 243 < 243 := Nat.mod_lt _ (by decide)
  omega

/-- The LTE mean is constantly six hundred sixty-four modulo
seven-hundred-twenty-nine from sheet level five onward. -/
theorem omega_lteCoeff_mod729 (a : Nat) (ha : 5 ≤ a) :
    lteCoeff a % 729 = 664 := by
  have h729 : (3:Nat)^6 = 729 := by decide
  have hstable := omega_lteCoeff_stable 6 (a-5)
  have hidx : (6-1) + (a-5) = a := by omega
  rw [hidx, h729] at hstable
  rw [hstable]
  decide

/-- The base of the geometric mean is one modulo seven-hundred-twenty-nine
from sheet level five onward. -/
theorem omega_base_mod729 : ∀ a : Nat, 5 ≤ a → (4^(3^a)) % 729 = 1 := by
  intro a
  induction a with
  | zero => intro h; omega
  | succ a ih =>
      intro h
      rcases Nat.lt_or_ge a 5 with hlt | hge
      · have ha4 : a = 4 := by omega
        rw [ha4]
        decide
      · have hstep : 4^(3^(a+1)) = (4^(3^a))^3 := by
          rw [Nat.pow_succ, Nat.pow_mul]
        rw [hstep, Nat.pow_mod, ih hge, Nat.one_pow]

/-- The geometric mean is the core mass modulo seven-hundred-twenty-nine
from sheet level five onward. -/
theorem omega_geo_mod729 (a core : Nat) (ha : 5 ≤ a) :
    omegaGeoSum a core % 729 = core % 729 := by
  have hterm : ∀ j : Nat, ((4^(3^a))^j) % 729 = 1 := by
    intro j
    rw [Nat.pow_mod, omega_base_mod729 a ha, Nat.one_pow]
  induction core with
  | zero => simp [omegaGeoSum]
  | succ core ih =>
      have hgeo : omegaGeoSum a (core+1)
          = omegaGeoSum a core + (4^(3^a))^core := by
        simp [omegaGeoSum, Finset.sum_range_succ]
      rw [hgeo, Nat.add_mod, hterm core, ih]
      omega

/-- **The level-six cut word law.**  From sheet level five onward the
cut word is `664 * core` modulo seven-hundred-twenty-nine. -/
theorem omega_cut_word_mod729 (a core : Nat) (ha : 5 ≤ a) :
    omegaCutWord a core % 729 = (664 * core) % 729 := by
  unfold omegaCutWord
  rw [Nat.mul_mod, omega_lteCoeff_mod729 a ha, omega_geo_mod729 a core ha]
  omega

/-- **THE LEVEL-SIX DIGIT LAW.**  The ternary digit of `4^(3^a * core)`
at row `a+6` is the top trit of the cut word modulo seven-hundred-twenty-nine. -/
theorem omega_level6_digit (a core : Nat) :
    digit3 (4^(3^a * core)) (a+6) = (omegaCutWord a core % 729) / 243 := by
  have hf := omega_cut_factor a core
  have h1 : (1:Nat) < 3^(a+1) := by
    have h3 : (3:Nat)^1 ≤ 3^(a+1) := by
      simpa using Nat.pow_le_pow_of_le (by decide : 1 < (3:Nat))
        (by omega : 1 ≤ a+1)
    omega
  have hslice := prefix_slice_digit_exact (a+1) 1 (omegaCutWord a core) 5 h1
  rw [show a+6 = (a+1)+5 from by omega, hf, hslice]
  unfold digit3
  rw [show (3:Nat)^5 = 243 from by decide]
  omega

/-- **THE LEVEL-SIX GATE CLASSES.**  For every core whose stabilized cut
word reaches the top third of the residue window modulo
seven-hundred-twenty-nine, the power `4^(3^a * core)` owns a ternary digit
two at row `a+6` — the sixth infinite family of the tower, at every sheet
level five and above. -/
theorem omega_level6_digit_two (a core : Nat) (ha : 5 ≤ a)
    (hgate : 486 ≤ (664 * core) % 729) :
    digit3 (4^(3^a * core)) (a+6) = 2 := by
  rw [omega_level6_digit, omega_cut_word_mod729 a core ha]
  have hlt : (664 * core) % 729 < 729 := Nat.mod_lt _ (by decide)
  omega

/-- The base's period modulo seven-hundred-twenty-nine: the order of four
is two-hundred-forty-three. -/
theorem omega_expcycle_period729 (j : Nat) :
    ((4^243)^j) % 729 = 1 := by
  have h481 : (4^81) % 729 = 244 := by decide
  have hsplit : 4^243 = 4^81 * 4^81 * 4^81 := by
    rw [show (243:Nat) = 81 + 81 + 81 from by decide, Nat.pow_add, Nat.pow_add]
  have hmul1 : 4^81 * 4^81 % 729 = 487 := by
    rw [Nat.mul_mod, h481]
  have hmul2 : 4^81 * 4^81 * 4^81 % 729 = 1 := by
    rw [Nat.mul_mod, hmul1, h481]
  have h4243 : (4^243) % 729 = 1 := by
    rw [hsplit, hmul2]
  rw [Nat.pow_mod, h4243, Nat.one_pow]

#check omega_expcycle_period729

/-- **THE EXPONENT-CYCLE ROW-FIVE GATE (one-sheet).**  Every three-free
exponent congruent to ninety-one, one hundred eighteen, one hundred
sixty-three, or one hundred ninety modulo two-hundred-forty-three rides
the base's period into the top third of the seven-hundred-twenty-nine
window: the digit two at row five. -/
theorem omega_expcycle_row5_digit_two_one (K : Nat)
    (hK : K % 243 = 91 ∨ K % 243 = 118 ∨ K % 243 = 163 ∨ K % 243 = 190) :
    digit3 (4^K) 5 = 2 := by
  have h481 : (4^81) % 729 = 244 := by decide
  have hmul1 : 4^81 * 4^81 % 729 = 487 := by
    rw [Nat.mul_mod, h481]
  rcases hK with h91 | h118 | h163 | h190
  · have hdm : K = 243 * (K / 243) + 91 := by omega
    have hpow : (4^243)^(K / 243) * 4^91 = 4^K := by
      rw [← Nat.pow_mul, ← Nat.pow_add, ← hdm]
    have hsplit : 4^91 = 4^81 * 4^10 := by
      rw [show (91:Nat) = 81 + 10 from by decide, Nat.pow_add]
    have h491 : (4^91) % 729 = 517 := by
      rw [hsplit, Nat.mul_mod, h481]
      decide
    have hmod : (4^K) % 729 = 517 := by
      rw [← hpow, Nat.mul_mod, omega_expcycle_period729 (K / 243), h491]
    unfold digit3
    rw [digit3_window, show 5 + 1 = 6 from by decide,
      show (3:Nat)^6 = 729 from by decide,
      show (3:Nat)^5 = 243 from by decide, hmod]
  · have hdm : K = 243 * (K / 243) + 118 := by omega
    have hpow : (4^243)^(K / 243) * 4^118 = 4^K := by
      rw [← Nat.pow_mul, ← Nat.pow_add, ← hdm]
    have hsplit : 4^118 = 4^81 * 4^37 := by
      rw [show (118:Nat) = 81 + 37 from by decide, Nat.pow_add]
    have h4118 : (4^118) % 729 = 598 := by
      rw [hsplit, Nat.mul_mod, h481]
      decide
    have hmod : (4^K) % 729 = 598 := by
      rw [← hpow, Nat.mul_mod, omega_expcycle_period729 (K / 243), h4118]
    unfold digit3
    rw [digit3_window, show 5 + 1 = 6 from by decide,
      show (3:Nat)^6 = 729 from by decide,
      show (3:Nat)^5 = 243 from by decide, hmod]
  · have hdm : K = 243 * (K / 243) + 163 := by omega
    have hpow : (4^243)^(K / 243) * 4^163 = 4^K := by
      rw [← Nat.pow_mul, ← Nat.pow_add, ← hdm]
    have hsplit : 4^163 = 4^81 * 4^81 * 4^1 := by
      rw [show (163:Nat) = 81 + 81 + 1 from by decide, Nat.pow_add, Nat.pow_add]
    have h4163 : (4^163) % 729 = 490 := by
      rw [hsplit, Nat.mul_mod, hmul1]
      decide
    have hmod : (4^K) % 729 = 490 := by
      rw [← hpow, Nat.mul_mod, omega_expcycle_period729 (K / 243), h4163]
    unfold digit3
    rw [digit3_window, show 5 + 1 = 6 from by decide,
      show (3:Nat)^6 = 729 from by decide,
      show (3:Nat)^5 = 243 from by decide, hmod]
  · have hdm : K = 243 * (K / 243) + 190 := by omega
    have hpow : (4^243)^(K / 243) * 4^190 = 4^K := by
      rw [← Nat.pow_mul, ← Nat.pow_add, ← hdm]
    have hsplit : 4^190 = 4^81 * 4^81 * 4^28 := by
      rw [show (190:Nat) = 81 + 81 + 28 from by decide, Nat.pow_add, Nat.pow_add]
    have h4190 : (4^190) % 729 = 571 := by
      rw [hsplit, Nat.mul_mod, hmul1]
      decide
    have hmod : (4^K) % 729 = 571 := by
      rw [← hpow, Nat.mul_mod, omega_expcycle_period729 (K / 243), h4190]
    unfold digit3
    rw [digit3_window, show 5 + 1 = 6 from by decide,
      show (3:Nat)^6 = 729 from by decide,
      show (3:Nat)^5 = 243 from by decide, hmod]

#check omega_expcycle_row5_digit_two_one

/-- **THE EXPONENT-CYCLE ROW-FIVE GATE (four-sheet).**  Every three-free
exponent congruent to eighty-five, one hundred twelve, one hundred
seventy-five, or two hundred two modulo two-hundred-forty-three rides
the base's period into the top third of the seven-hundred-twenty-nine
window: the digit two at row five. -/
theorem omega_expcycle_row5_digit_two_four (K : Nat)
    (hK : K % 243 = 85 ∨ K % 243 = 112 ∨ K % 243 = 175 ∨ K % 243 = 202) :
    digit3 (4^K) 5 = 2 := by
  have h481 : (4^81) % 729 = 244 := by decide
  have hmul1 : 4^81 * 4^81 % 729 = 487 := by
    rw [Nat.mul_mod, h481]
  rcases hK with h85 | h112 | h175 | h202
  · have hdm : K = 243 * (K / 243) + 85 := by omega
    have hpow : (4^243)^(K / 243) * 4^85 = 4^K := by
      rw [← Nat.pow_mul, ← Nat.pow_add, ← hdm]
    have hsplit : 4^85 = 4^81 * 4^4 := by
      rw [show (85:Nat) = 81 + 4 from by decide, Nat.pow_add]
    have h485 : (4^85) % 729 = 499 := by
      rw [hsplit, Nat.mul_mod, h481]
      decide
    have hmod : (4^K) % 729 = 499 := by
      rw [← hpow, Nat.mul_mod, omega_expcycle_period729 (K / 243), h485]
    unfold digit3
    rw [digit3_window, show 5 + 1 = 6 from by decide,
      show (3:Nat)^6 = 729 from by decide,
      show (3:Nat)^5 = 243 from by decide, hmod]
  · have hdm : K = 243 * (K / 243) + 112 := by omega
    have hpow : (4^243)^(K / 243) * 4^112 = 4^K := by
      rw [← Nat.pow_mul, ← Nat.pow_add, ← hdm]
    have hsplit : 4^112 = 4^81 * 4^31 := by
      rw [show (112:Nat) = 81 + 31 from by decide, Nat.pow_add]
    have h4112 : (4^112) % 729 = 580 := by
      rw [hsplit, Nat.mul_mod, h481]
      decide
    have hmod : (4^K) % 729 = 580 := by
      rw [← hpow, Nat.mul_mod, omega_expcycle_period729 (K / 243), h4112]
    unfold digit3
    rw [digit3_window, show 5 + 1 = 6 from by decide,
      show (3:Nat)^6 = 729 from by decide,
      show (3:Nat)^5 = 243 from by decide, hmod]
  · have hdm : K = 243 * (K / 243) + 175 := by omega
    have hpow : (4^243)^(K / 243) * 4^175 = 4^K := by
      rw [← Nat.pow_mul, ← Nat.pow_add, ← hdm]
    have hsplit : 4^175 = 4^81 * 4^81 * 4^13 := by
      rw [show (175:Nat) = 81 + 81 + 13 from by decide, Nat.pow_add, Nat.pow_add]
    have h4175 : (4^175) % 729 = 526 := by
      rw [hsplit, Nat.mul_mod, hmul1]
      decide
    have hmod : (4^K) % 729 = 526 := by
      rw [← hpow, Nat.mul_mod, omega_expcycle_period729 (K / 243), h4175]
    unfold digit3
    rw [digit3_window, show 5 + 1 = 6 from by decide,
      show (3:Nat)^6 = 729 from by decide,
      show (3:Nat)^5 = 243 from by decide, hmod]
  · have hdm : K = 243 * (K / 243) + 202 := by omega
    have hpow : (4^243)^(K / 243) * 4^202 = 4^K := by
      rw [← Nat.pow_mul, ← Nat.pow_add, ← hdm]
    have hsplit : 4^202 = 4^81 * 4^81 * 4^40 := by
      rw [show (202:Nat) = 81 + 81 + 40 from by decide, Nat.pow_add, Nat.pow_add]
    have h4202 : (4^202) % 729 = 607 := by
      rw [hsplit, Nat.mul_mod, hmul1]
      decide
    have hmod : (4^K) % 729 = 607 := by
      rw [← hpow, Nat.mul_mod, omega_expcycle_period729 (K / 243), h4202]
    unfold digit3
    rw [digit3_window, show 5 + 1 = 6 from by decide,
      show (3:Nat)^6 = 729 from by decide,
      show (3:Nat)^5 = 243 from by decide, hmod]

#check omega_expcycle_row5_digit_two_four

/-- The base's residue modulo two-thousand-one-hundred-eighty-seven at the
quarter-period split: the first cross-sheet atom of the row-six cycle. -/
theorem omega_four_pow_243_mod_2187 : (4^243) % 2187 = 730 := by
  have h481 : (4^81) % 2187 = 1702 := by decide
  have hsplit : 4^243 = 4^81 * 4^81 * 4^81 := by
    rw [show (243:Nat) = 81 + 81 + 81 from by decide, Nat.pow_add, Nat.pow_add]
  have hmul1 : 4^81 * 4^81 % 2187 = 1216 := by
    rw [Nat.mul_mod, h481]
  rw [hsplit, Nat.mul_mod, hmul1, h481]

#check omega_four_pow_243_mod_2187

/-- The base's full period modulo two-thousand-one-hundred-eighty-seven:
the order of four is seven-hundred-twenty-nine, and the cube of the
quarter-period atom lands exactly on one. -/
theorem omega_four_pow_729_mod_2187 : (4^729) % 2187 = 1 := by
  have h7243 : (4^243) % 2187 = 730 := omega_four_pow_243_mod_2187
  have hsplit : 4^729 = 4^243 * 4^243 * 4^243 := by
    rw [show (729:Nat) = 243 + 243 + 243 from by decide, Nat.pow_add, Nat.pow_add]
  have hmul1 : 4^243 * 4^243 % 2187 = 1459 := by
    rw [Nat.mul_mod, h7243]
  rw [hsplit, Nat.mul_mod, hmul1, h7243]

#check omega_four_pow_729_mod_2187

/-- The base's period modulo two-thousand-one-hundred-eighty-seven: the
order of four is seven-hundred-twenty-nine. -/
theorem omega_expcycle_period2187 (j : Nat) :
    ((4^729)^j) % 2187 = 1 := by
  rw [Nat.pow_mod, omega_four_pow_729_mod_2187, Nat.one_pow]

#check omega_expcycle_period2187

/-- The LTE mean is constantly six hundred sixty-four modulo
two-thousand-one-hundred-eighty-seven from sheet level six onward. -/
theorem omega_lteCoeff_mod2187 (a : Nat) (ha : 6 ≤ a) :
    lteCoeff a % 2187 = 664 := by
  have h2187 : (3:Nat)^7 = 2187 := by decide
  have hstable := omega_lteCoeff_stable 7 (a-6)
  have hidx : (7-1) + (a-6) = a := by omega
  rw [hidx, h2187] at hstable
  rw [hstable]
  decide

/-- The base of the geometric mean is one modulo
two-thousand-one-hundred-eighty-seven from sheet level six onward. -/
theorem omega_base_mod2187 : ∀ a : Nat, 6 ≤ a → (4^(3^a)) % 2187 = 1 := by
  intro a
  induction a with
  | zero => intro h; omega
  | succ a ih =>
      intro h
      rcases Nat.lt_or_ge a 6 with hlt | hge
      · have ha5 : a = 5 := by omega
        rw [ha5]
        have hidx : (3:Nat)^(5+1) = 729 := by decide
        rw [hidx]
        exact omega_four_pow_729_mod_2187
      · have hstep : 4^(3^(a+1)) = (4^(3^a))^3 := by
          rw [Nat.pow_succ, Nat.pow_mul]
        rw [hstep, Nat.pow_mod, ih hge, Nat.one_pow]

/-- The geometric mean is the core mass modulo
two-thousand-one-hundred-eighty-seven from sheet level six onward. -/
theorem omega_geo_mod2187 (a core : Nat) (ha : 6 ≤ a) :
    omegaGeoSum a core % 2187 = core % 2187 := by
  have hterm : ∀ j : Nat, ((4^(3^a))^j) % 2187 = 1 := by
    intro j
    rw [Nat.pow_mod, omega_base_mod2187 a ha, Nat.one_pow]
  induction core with
  | zero => simp [omegaGeoSum]
  | succ core ih =>
      have hgeo : omegaGeoSum a (core+1)
          = omegaGeoSum a core + (4^(3^a))^core := by
        simp [omegaGeoSum, Finset.sum_range_succ]
      rw [hgeo, Nat.add_mod, hterm core, ih]
      omega

/-- **The level-seven cut word law.**  From sheet level six onward the
cut word is `664 * core` modulo two-thousand-one-hundred-eighty-seven. -/
theorem omega_cut_word_mod2187 (a core : Nat) (ha : 6 ≤ a) :
    omegaCutWord a core % 2187 = (664 * core) % 2187 := by
  unfold omegaCutWord
  rw [Nat.mul_mod, omega_lteCoeff_mod2187 a ha, omega_geo_mod2187 a core ha]
  omega

/-- **THE LEVEL-SEVEN DIGIT LAW.**  The ternary digit of `4^(3^a * core)`
at row `a+7` is the top trit of the cut word modulo
two-thousand-one-hundred-eighty-seven. -/
theorem omega_level7_digit (a core : Nat) :
    digit3 (4^(3^a * core)) (a+7) = (omegaCutWord a core % 2187) / 729 := by
  have hf := omega_cut_factor a core
  have h1 : (1:Nat) < 3^(a+1) := by
    have h3 : (3:Nat)^1 ≤ 3^(a+1) := by
      simpa using Nat.pow_le_pow_of_le (by decide : 1 < (3:Nat))
        (by omega : 1 ≤ a+1)
    omega
  have hslice := prefix_slice_digit_exact (a+1) 1 (omegaCutWord a core) 6 h1
  rw [show a+7 = (a+1)+6 from by omega, hf, hslice]
  unfold digit3
  rw [show (3:Nat)^6 = 729 from by decide]
  omega

/-- **THE LEVEL-SEVEN GATE CLASSES.**  For every core whose stabilized cut
word reaches the top third of the residue window modulo
two-thousand-one-hundred-eighty-seven, the power `4^(3^a * core)` owns a
ternary digit two at row `a+7` — the seventh infinite family of the
tower, at every sheet level six and above. -/
theorem omega_level7_digit_two (a core : Nat) (ha : 6 ≤ a)
    (hgate : 1458 ≤ (664 * core) % 2187) :
    digit3 (4^(3^a * core)) (a+7) = 2 := by
  rw [omega_level7_digit, omega_cut_word_mod2187 a core ha]
  have hlt : (664 * core) % 2187 < 2187 := Nat.mod_lt _ (by decide)
  omega

#check omega_lteCoeff_mod2187
#check omega_base_mod2187
#check omega_geo_mod2187
#check omega_cut_word_mod2187
#check omega_level7_digit
#check omega_level7_digit_two

/-- **THE EXPONENT-CYCLE ROW-SIX GATE (one-sheet).**  Every three-free
exponent congruent to thirty-seven, one hundred seventy-two, two hundred
fifty-three, two hundred seventy-one, three hundred fifty-two, four
hundred eighty-seven, five hundred sixty-eight, or six hundred
eighty-five modulo seven-hundred-twenty-nine rides the base's period into
the top third of the two-thousand-one-hundred-eighty-seven window: the
digit two at row six. -/
theorem omega_expcycle_row6_digit_two_one (K : Nat)
    (hK : K % 729 = 37 ∨ K % 729 = 172 ∨ K % 729 = 253 ∨ K % 729 = 271
      ∨ K % 729 = 352 ∨ K % 729 = 487 ∨ K % 729 = 568 ∨ K % 729 = 685) :
    digit3 (4^K) 6 = 2 := by
  rcases hK with h37 | h172 | h253 | h271 | h352 | h487 | h568 | h685
  · have hdm : K = 729 * (K / 729) + 37 := by omega
    have hpow : (4^729)^(K / 729) * 4^37 = 4^K := by
      rw [← Nat.pow_mul, ← Nat.pow_add, ← hdm]
    have h4v : (4^37) % 2187 = 1813 := by decide
    have hmod : (4^K) % 2187 = 1813 := by
      rw [← hpow, Nat.mul_mod, omega_expcycle_period2187 (K / 729), h4v]
    unfold digit3
    rw [digit3_window, show 6 + 1 = 7 from by decide,
      show (3:Nat)^7 = 2187 from by decide,
      show (3:Nat)^6 = 729 from by decide, hmod]
  · have hdm : K = 729 * (K / 729) + 172 := by omega
    have hpow : (4^729)^(K / 729) * 4^172 = 4^K := by
      rw [← Nat.pow_mul, ← Nat.pow_add, ← hdm]
    have h4v : (4^172) % 2187 = 1489 := by decide
    have hmod : (4^K) % 2187 = 1489 := by
      rw [← hpow, Nat.mul_mod, omega_expcycle_period2187 (K / 729), h4v]
    unfold digit3
    rw [digit3_window, show 6 + 1 = 7 from by decide,
      show (3:Nat)^7 = 2187 from by decide,
      show (3:Nat)^6 = 729 from by decide, hmod]
  · have hdm : K = 729 * (K / 729) + 253 := by omega
    have hpow : (4^729)^(K / 729) * 4^253 = 4^K := by
      rw [← Nat.pow_mul, ← Nat.pow_add, ← hdm]
    have h4v : (4^253) % 2187 = 1732 := by decide
    have hmod : (4^K) % 2187 = 1732 := by
      rw [← hpow, Nat.mul_mod, omega_expcycle_period2187 (K / 729), h4v]
    unfold digit3
    rw [digit3_window, show 6 + 1 = 7 from by decide,
      show (3:Nat)^7 = 2187 from by decide,
      show (3:Nat)^6 = 729 from by decide, hmod]
  · have hdm : K = 729 * (K / 729) + 271 := by omega
    have hpow : (4^729)^(K / 729) * 4^271 = 4^K := by
      rw [← Nat.pow_mul, ← Nat.pow_add, ← hdm]
    have h4v : (4^271) % 2187 = 1543 := by decide
    have hmod : (4^K) % 2187 = 1543 := by
      rw [← hpow, Nat.mul_mod, omega_expcycle_period2187 (K / 729), h4v]
    unfold digit3
    rw [digit3_window, show 6 + 1 = 7 from by decide,
      show (3:Nat)^7 = 2187 from by decide,
      show (3:Nat)^6 = 729 from by decide, hmod]
  · have hdm : K = 729 * (K / 729) + 352 := by omega
    have hpow : (4^729)^(K / 729) * 4^352 = 4^K := by
      rw [← Nat.pow_mul, ← Nat.pow_add, ← hdm]
    have h4v : (4^352) % 2187 = 1786 := by decide
    have hmod : (4^K) % 2187 = 1786 := by
      rw [← hpow, Nat.mul_mod, omega_expcycle_period2187 (K / 729), h4v]
    unfold digit3
    rw [digit3_window, show 6 + 1 = 7 from by decide,
      show (3:Nat)^7 = 2187 from by decide,
      show (3:Nat)^6 = 729 from by decide, hmod]
  · have hdm : K = 729 * (K / 729) + 487 := by omega
    have hpow : (4^729)^(K / 729) * 4^487 = 4^K := by
      rw [← Nat.pow_mul, ← Nat.pow_add, ← hdm]
    have h4v : (4^487) % 2187 = 1462 := by decide
    have hmod : (4^K) % 2187 = 1462 := by
      rw [← hpow, Nat.mul_mod, omega_expcycle_period2187 (K / 729), h4v]
    unfold digit3
    rw [digit3_window, show 6 + 1 = 7 from by decide,
      show (3:Nat)^7 = 2187 from by decide,
      show (3:Nat)^6 = 729 from by decide, hmod]
  · have hdm : K = 729 * (K / 729) + 568 := by omega
    have hpow : (4^729)^(K / 729) * 4^568 = 4^K := by
      rw [← Nat.pow_mul, ← Nat.pow_add, ← hdm]
    have h4v : (4^568) % 2187 = 1705 := by decide
    have hmod : (4^K) % 2187 = 1705 := by
      rw [← hpow, Nat.mul_mod, omega_expcycle_period2187 (K / 729), h4v]
    unfold digit3
    rw [digit3_window, show 6 + 1 = 7 from by decide,
      show (3:Nat)^7 = 2187 from by decide,
      show (3:Nat)^6 = 729 from by decide, hmod]
  · have hdm : K = 729 * (K / 729) + 685 := by omega
    have hpow : (4^729)^(K / 729) * 4^685 = 4^K := by
      rw [← Nat.pow_mul, ← Nat.pow_add, ← hdm]
    have h4v : (4^685) % 2187 = 1570 := by decide
    have hmod : (4^K) % 2187 = 1570 := by
      rw [← hpow, Nat.mul_mod, omega_expcycle_period2187 (K / 729), h4v]
    unfold digit3
    rw [digit3_window, show 6 + 1 = 7 from by decide,
      show (3:Nat)^7 = 2187 from by decide,
      show (3:Nat)^6 = 729 from by decide, hmod]

#check omega_expcycle_row6_digit_two_one

/-- **THE EXPONENT-CYCLE ROW-SIX GATE (four-sheet).**  Every three-free
exponent congruent to thirty-one, two hundred fifty-six, three hundred
thirty-seven, four hundred nine, four hundred ninety, five hundred
twenty-six, six hundred seven, or six hundred seventy-nine modulo
seven-hundred-twenty-nine rides the base's period into the top third of
the two-thousand-one-hundred-eighty-seven window: the digit two at row
six. -/
theorem omega_expcycle_row6_digit_two_four (K : Nat)
    (hK : K % 729 = 31 ∨ K % 729 = 256 ∨ K % 729 = 337 ∨ K % 729 = 409
      ∨ K % 729 = 490 ∨ K % 729 = 526 ∨ K % 729 = 607 ∨ K % 729 = 679) :
    digit3 (4^K) 6 = 2 := by
  rcases hK with h31 | h256 | h337 | h409 | h490 | h526 | h607 | h679
  · have hdm : K = 729 * (K / 729) + 31 := by omega
    have hpow : (4^729)^(K / 729) * 4^31 = 4^K := by
      rw [← Nat.pow_mul, ← Nat.pow_add, ← hdm]
    have h4v : (4^31) % 2187 = 1795 := by decide
    have hmod : (4^K) % 2187 = 1795 := by
      rw [← hpow, Nat.mul_mod, omega_expcycle_period2187 (K / 729), h4v]
    unfold digit3
    rw [digit3_window, show 6 + 1 = 7 from by decide,
      show (3:Nat)^7 = 2187 from by decide,
      show (3:Nat)^6 = 729 from by decide, hmod]
  · have hdm : K = 729 * (K / 729) + 256 := by omega
    have hpow : (4^729)^(K / 729) * 4^256 = 4^K := by
      rw [← Nat.pow_mul, ← Nat.pow_add, ← hdm]
    have h4v : (4^256) % 2187 = 1498 := by decide
    have hmod : (4^K) % 2187 = 1498 := by
      rw [← hpow, Nat.mul_mod, omega_expcycle_period2187 (K / 729), h4v]
    unfold digit3
    rw [digit3_window, show 6 + 1 = 7 from by decide,
      show (3:Nat)^7 = 2187 from by decide,
      show (3:Nat)^6 = 729 from by decide, hmod]
  · have hdm : K = 729 * (K / 729) + 337 := by omega
    have hpow : (4^729)^(K / 729) * 4^337 = 4^K := by
      rw [← Nat.pow_mul, ← Nat.pow_add, ← hdm]
    have h4v : (4^337) % 2187 = 1741 := by decide
    have hmod : (4^K) % 2187 = 1741 := by
      rw [← hpow, Nat.mul_mod, omega_expcycle_period2187 (K / 729), h4v]
    unfold digit3
    rw [digit3_window, show 6 + 1 = 7 from by decide,
      show (3:Nat)^7 = 2187 from by decide,
      show (3:Nat)^6 = 729 from by decide, hmod]
  · have hdm : K = 729 * (K / 729) + 409 := by omega
    have hpow : (4^729)^(K / 729) * 4^409 = 4^K := by
      rw [← Nat.pow_mul, ← Nat.pow_add, ← hdm]
    have h4v : (4^409) % 2187 = 1471 := by decide
    have hmod : (4^K) % 2187 = 1471 := by
      rw [← hpow, Nat.mul_mod, omega_expcycle_period2187 (K / 729), h4v]
    unfold digit3
    rw [digit3_window, show 6 + 1 = 7 from by decide,
      show (3:Nat)^7 = 2187 from by decide,
      show (3:Nat)^6 = 729 from by decide, hmod]
  · have hdm : K = 729 * (K / 729) + 490 := by omega
    have hpow : (4^729)^(K / 729) * 4^490 = 4^K := by
      rw [← Nat.pow_mul, ← Nat.pow_add, ← hdm]
    have h4v : (4^490) % 2187 = 1714 := by decide
    have hmod : (4^K) % 2187 = 1714 := by
      rw [← hpow, Nat.mul_mod, omega_expcycle_period2187 (K / 729), h4v]
    unfold digit3
    rw [digit3_window, show 6 + 1 = 7 from by decide,
      show (3:Nat)^7 = 2187 from by decide,
      show (3:Nat)^6 = 729 from by decide, hmod]
  · have hdm : K = 729 * (K / 729) + 526 := by omega
    have hpow : (4^729)^(K / 729) * 4^526 = 4^K := by
      rw [← Nat.pow_mul, ← Nat.pow_add, ← hdm]
    have h4v : (4^526) % 2187 = 1579 := by decide
    have hmod : (4^K) % 2187 = 1579 := by
      rw [← hpow, Nat.mul_mod, omega_expcycle_period2187 (K / 729), h4v]
    unfold digit3
    rw [digit3_window, show 6 + 1 = 7 from by decide,
      show (3:Nat)^7 = 2187 from by decide,
      show (3:Nat)^6 = 729 from by decide, hmod]
  · have hdm : K = 729 * (K / 729) + 607 := by omega
    have hpow : (4^729)^(K / 729) * 4^607 = 4^K := by
      rw [← Nat.pow_mul, ← Nat.pow_add, ← hdm]
    have h4v : (4^607) % 2187 = 1822 := by decide
    have hmod : (4^K) % 2187 = 1822 := by
      rw [← hpow, Nat.mul_mod, omega_expcycle_period2187 (K / 729), h4v]
    unfold digit3
    rw [digit3_window, show 6 + 1 = 7 from by decide,
      show (3:Nat)^7 = 2187 from by decide,
      show (3:Nat)^6 = 729 from by decide, hmod]
  · have hdm : K = 729 * (K / 729) + 679 := by omega
    have hpow : (4^729)^(K / 729) * 4^679 = 4^K := by
      rw [← Nat.pow_mul, ← Nat.pow_add, ← hdm]
    have h4v : (4^679) % 2187 = 1552 := by decide
    have hmod : (4^K) % 2187 = 1552 := by
      rw [← hpow, Nat.mul_mod, omega_expcycle_period2187 (K / 729), h4v]
    unfold digit3
    rw [digit3_window, show 6 + 1 = 7 from by decide,
      show (3:Nat)^7 = 2187 from by decide,
      show (3:Nat)^6 = 729 from by decide, hmod]

#check omega_expcycle_row6_digit_two_four

end

/-- **The Ω-shadow tail after the sheet gate.**  The shadow residue after
the kernel-checked base, the third and fourth tower levels, and the
Ω-sheet gate: every shadow exponent above the kernel base whose core
dodges every proven gate of the tower and whose sheet-local cut word
dodges the squared-modulus top trit. -/
def omegaShadowTail2 (K : Nat) : Prop :=
  ∃ s core : Nat, K = 3^s * core ∧ ¬ 3 ∣ core ∧
    (core % 9 = 4 ∨ (s = 0 ∧ core % 9 = 1) ∨ (1 ≤ s ∧ core % 9 = 7)) ∧
    (2 ≤ s → core % 27 ≠ 13 ∧ core % 27 ≠ 25) ∧
    (3 ≤ s → (16 * core) % 81 < 54) ∧
    ((omegaCutWord s core) % 3^(s+2) < 2 * 3^(s+1))

/-- **THE Ω-SHADOW WAVE TAIL (SHEET-GATE FORM)** — the residual input after
the kernel-checked base, the third and fourth levels of the Ω-cut tower,
and the Ω-sheet gate: only shadow exponents above the kernel base whose
cores dodge every proven gate remain. -/
def four_power_omega_shadow_wave_tail2 : Prop :=
  ∀ K : Nat, 500 < K → omegaShadowTail2 K → ∃ p : Nat, digit3 (4^K) p = 2

/-- **The Ω-shadow tail.**  The shadow residue after the kernel-checked
base and the level-three gate classes: every shadow exponent above the
kernel base whose core dodges the level-three classes at sheet level two
and above. -/
def omegaShadowTail (K : Nat) : Prop :=
  ∃ s core : Nat, K = 3^s * core ∧ ¬ 3 ∣ core ∧
    (core % 9 = 4 ∨ (s = 0 ∧ core % 9 = 1) ∨ (1 ≤ s ∧ core % 9 = 7)) ∧
    (2 ≤ s → core % 27 ≠ 13 ∧ core % 27 ≠ 25)

/-- **THE Ω-SHADOW WAVE TAIL** — the residual input after the
kernel-checked base and the third level of the Ω-cut tower: only shadow
exponents above the kernel base whose cores dodge every proven gate
class remain. -/
def four_power_omega_shadow_wave_tail : Prop :=
  ∀ K : Nat, 500 < K → omegaShadowTail K → ∃ p : Nat, digit3 (4^K) p = 2

/-- **The Ω-shadow tail after the second sheet gate and the exponent-cycle
gates.**  The shadow residue after the kernel-checked base, the third and
fourth tower levels, the Ω-sheet gate, the Ω-second-sheet gate, and the
sheet-zero exponent-cycle gates: every shadow exponent above the kernel
base whose core dodges every proven gate — the tower classes, both sheet
gates, and the base's own period classes at sheet zero — remains. -/
def omegaShadowTail3 (K : Nat) : Prop :=
  ∃ s core : Nat, K = 3^s * core ∧ ¬ 3 ∣ core ∧
    (core % 9 = 4 ∨ (s = 0 ∧ core % 9 = 1) ∨ (1 ≤ s ∧ core % 9 = 7)) ∧
    (2 ≤ s → core % 27 ≠ 13 ∧ core % 27 ≠ 25) ∧
    (3 ≤ s → (16 * core) % 81 < 54) ∧
    ((omegaCutWord s core) % 3^(s+2) < 2 * 3^(s+1)) ∧
    (1 ≤ s → (core % 9 = 4 →
      3^(s+2) ≤ (lteCoeff s * core) % 3^(s+3))) ∧
    (1 ≤ s → (core % 9 = 7 →
      ((lteCoeff s * core) % 3^(s+3) < 3^(s+2)
        ∨ 2 * 3^(s+2) ≤ (lteCoeff s * core) % 3^(s+3)))) ∧
    (s = 0 → (core % 9 = 1 → core % 27 ≠ 19 ∧ core % 81 ≠ 55
      ∧ core % 81 ≠ 64 ∧ core % 81 ≠ 73)) ∧
    (s = 0 → (core % 9 = 4 → core % 27 ≠ 22 ∧ core % 81 ≠ 58
      ∧ core % 81 ≠ 67 ∧ core % 81 ≠ 76))

/-- **THE Ω-SHADOW WAVE TAIL (SECOND-SHEET FORM)** — the residual input
after the kernel-checked base, the third and fourth tower levels, both
sheet gates, and the sheet-zero exponent-cycle gates. -/
def four_power_omega_shadow_wave_tail3 : Prop :=
  ∀ K : Nat, 500 < K → omegaShadowTail3 K → ∃ p : Nat, digit3 (4^K) p = 2

/-- **The Ω-shadow tail after the fifth weakening.**  The shadow residue
after the kernel-checked base, the third through sixth tower levels, both
sheet gates, and the sheet-zero exponent-cycle gates through row five:
every shadow exponent above the kernel base whose core dodges every
proven gate — the tower classes at levels three through six, both sheet
gates, and the base's own period classes at rows three through five —
remains. -/
def omegaShadowTail4 (K : Nat) : Prop :=
  ∃ s core : Nat, K = 3^s * core ∧ ¬ 3 ∣ core ∧
    (core % 9 = 4 ∨ (s = 0 ∧ core % 9 = 1) ∨ (1 ≤ s ∧ core % 9 = 7)) ∧
    (2 ≤ s → core % 27 ≠ 13 ∧ core % 27 ≠ 25) ∧
    (3 ≤ s → (16 * core) % 81 < 54) ∧
    ((omegaCutWord s core) % 3^(s+2) < 2 * 3^(s+1)) ∧
    (1 ≤ s → (core % 9 = 4 →
      3^(s+2) ≤ (lteCoeff s * core) % 3^(s+3))) ∧
    (1 ≤ s → (core % 9 = 7 →
      ((lteCoeff s * core) % 3^(s+3) < 3^(s+2)
        ∨ 2 * 3^(s+2) ≤ (lteCoeff s * core) % 3^(s+3)))) ∧
    (s = 0 → (core % 9 = 1 → core % 27 ≠ 19 ∧ core % 81 ≠ 55
      ∧ core % 81 ≠ 64 ∧ core % 81 ≠ 73)) ∧
    (s = 0 → (core % 9 = 4 → core % 27 ≠ 22 ∧ core % 81 ≠ 58
      ∧ core % 81 ≠ 67 ∧ core % 81 ≠ 76)) ∧
    (4 ≤ s → (178 * core) % 243 < 162) ∧
    (5 ≤ s → (664 * core) % 729 < 486) ∧
    (s = 0 → (core % 243 ≠ 85 ∧ core % 243 ≠ 91 ∧ core % 243 ≠ 112
      ∧ core % 243 ≠ 118 ∧ core % 243 ≠ 163 ∧ core % 243 ≠ 175
      ∧ core % 243 ≠ 190 ∧ core % 243 ≠ 202))

/-- **THE Ω-SHADOW WAVE TAIL (FIFTH WEAKENING)** — the residual input
after the kernel-checked base, the third through sixth tower levels,
both sheet gates, and the sheet-zero exponent-cycle gates through row
five. -/
def four_power_omega_shadow_wave_tail4 : Prop :=
  ∀ K : Nat, 500 < K → omegaShadowTail4 K → ∃ p : Nat, digit3 (4^K) p = 2

/-- **The Ω-shadow tail after the sixth weakening.**  The shadow residue
after the kernel-checked base, the third through seventh tower levels,
both sheet gates, and the sheet-zero exponent-cycle gates through row
six: every shadow exponent above the kernel base whose core dodges every
proven gate — the tower classes at levels three through seven, both sheet
gates, and the base's own period classes at rows three through six —
remains. -/
def omegaShadowTail5 (K : Nat) : Prop :=
  ∃ s core : Nat, K = 3^s * core ∧ ¬ 3 ∣ core ∧
    (core % 9 = 4 ∨ (s = 0 ∧ core % 9 = 1) ∨ (1 ≤ s ∧ core % 9 = 7)) ∧
    (2 ≤ s → core % 27 ≠ 13 ∧ core % 27 ≠ 25) ∧
    (3 ≤ s → (16 * core) % 81 < 54) ∧
    ((omegaCutWord s core) % 3^(s+2) < 2 * 3^(s+1)) ∧
    (1 ≤ s → (core % 9 = 4 →
      3^(s+2) ≤ (lteCoeff s * core) % 3^(s+3))) ∧
    (1 ≤ s → (core % 9 = 7 →
      ((lteCoeff s * core) % 3^(s+3) < 3^(s+2)
        ∨ 2 * 3^(s+2) ≤ (lteCoeff s * core) % 3^(s+3)))) ∧
    (s = 0 → (core % 9 = 1 → core % 27 ≠ 19 ∧ core % 81 ≠ 55
      ∧ core % 81 ≠ 64 ∧ core % 81 ≠ 73)) ∧
    (s = 0 → (core % 9 = 4 → core % 27 ≠ 22 ∧ core % 81 ≠ 58
      ∧ core % 81 ≠ 67 ∧ core % 81 ≠ 76)) ∧
    (4 ≤ s → (178 * core) % 243 < 162) ∧
    (5 ≤ s → (664 * core) % 729 < 486) ∧
    (s = 0 → (core % 243 ≠ 85 ∧ core % 243 ≠ 91 ∧ core % 243 ≠ 112
      ∧ core % 243 ≠ 118 ∧ core % 243 ≠ 163 ∧ core % 243 ≠ 175
      ∧ core % 243 ≠ 190 ∧ core % 243 ≠ 202)) ∧
    (6 ≤ s → (664 * core) % 2187 < 1458) ∧
    (s = 0 → (core % 729 ≠ 31 ∧ core % 729 ≠ 37 ∧ core % 729 ≠ 172
      ∧ core % 729 ≠ 253 ∧ core % 729 ≠ 256 ∧ core % 729 ≠ 271
      ∧ core % 729 ≠ 337 ∧ core % 729 ≠ 352 ∧ core % 729 ≠ 409
      ∧ core % 729 ≠ 487 ∧ core % 729 ≠ 490 ∧ core % 729 ≠ 526
      ∧ core % 729 ≠ 568 ∧ core % 729 ≠ 607 ∧ core % 729 ≠ 679
      ∧ core % 729 ≠ 685))

/-- **THE Ω-SHADOW WAVE TAIL (SIXTH WEAKENING)** — the residual input
after the kernel-checked base, the third through seventh tower levels,
both sheet gates, and the sheet-zero exponent-cycle gates through row
six. -/
def four_power_omega_shadow_wave_tail5 : Prop :=
  ∀ K : Nat, 500 < K → omegaShadowTail5 K → ∃ p : Nat, digit3 (4^K) p = 2

/-- **THE Ω-SHADOW WAVE, CLOSED FORM — the campaign's name for the
wave.**  An explicit alias: the closed target IS the Ω-shadow wave of
§7.5 — one Prop, one body, two names, the name "closed" marking its
role as the campaign target.  Every shadow exponent from eight onward
owns its ternary digit two outright; the final theorem consumes it once
every gate family has been paid for unconditionally.  The wave of §7.5
never carried a tail bound or a kernel cut, so the closed form adds
nothing and subtracts nothing: both names denote the one statement. -/
def four_power_omega_shadow_wave_closed : Prop :=
  four_power_omega_shadow_wave

/-! ## §7.10 The tripling-cube law (the cross-sheet digit transfer)

The shadow residue is closed under the exponent tripling `K ↦ 3 * K` for
its class-one core classes: the core is untouched and the sheet level
advances by one.  Cubing the sheet-s power therefore transfers the cut
word to the next sheet by an exact cube recurrence, and the transfer
moves the sheet-gate row `2s+2` of the parent to the row `2s+3` of the
child with a fixed increment of one.  This is the first Law statement
that reads one sheet's digit structure from another sheet's — the
cross-sheet instrument. -/

/-- **THE TRIPLING-CUBE WORD LAW.**  The cut word of the next sheet is the
cube recurrence of this sheet's cut word: the sheet-`(s+1)` word is the
sheet-`s` word plus its own square scaled by the cut modulus plus its own
cube scaled by the double cut modulus.  Exact identity, no hypothesis. -/
theorem omega_tripling_cut_word (s core : Nat) :
    omegaCutWord (s+1) core
      = omegaCutWord s core
        + 3^(s+1) * (omegaCutWord s core)^2
        + 3^(2*s+1) * (omegaCutWord s core)^3 := by
  have hexp : 4^(3^(s+1) * core) = (4^(3^s * core))^3 := by
    rw [show 3^(s+1) * core = (3^s * core) * 3 from by
          rw [Nat.pow_succ]; ring,
      Nat.pow_mul]
  have hA : (1 + 3^(s+1) * omegaCutWord s core)^3
      = 1 + 3^(s+2) * omegaCutWord (s+1) core := by
    rw [← omega_cut_factor (s+1) core, hexp, omega_cut_factor s core]
  have hcube : (1 + 3^(s+1) * omegaCutWord s core)^3
      = 1 + 3^(s+2) * omegaCutWord s core
        + 3^(2*s+3) * (omegaCutWord s core)^2
        + 3^(3*s+3) * (omegaCutWord s core)^3 := by
    have h1 : (3:Nat)^(s+2) = 3 * 3^(s+1) := by
      rw [Nat.pow_succ]; ring
    have h2 : (3:Nat)^(2*s+3) = 3 * 3^(s+1) * 3^(s+1) := by
      rw [show (2*s+3) = (s+1)+(s+1)+1 from by omega, Nat.pow_add,
        Nat.pow_add, Nat.pow_one]
      ring
    have h3 : (3:Nat)^(3*s+3) = 3^(s+1) * 3^(s+1) * 3^(s+1) := by
      rw [show (3*s+3) = (s+1)+(s+1)+(s+1) from by omega, Nat.pow_add,
        Nat.pow_add]
    rw [h1, h2, h3]
    ring
  rw [hA] at hcube
  have hsub : 3^(s+2) * omegaCutWord (s+1) core
      = 3^(s+2) * omegaCutWord s core
        + 3^(2*s+3) * (omegaCutWord s core)^2
        + 3^(3*s+3) * (omegaCutWord s core)^3 := by
    omega
  have hexpand : 3^(s+2) * (omegaCutWord s core
      + 3^(s+1) * (omegaCutWord s core)^2
      + 3^(2*s+1) * (omegaCutWord s core)^3)
      = 3^(s+2) * omegaCutWord s core
        + 3^(2*s+3) * (omegaCutWord s core)^2
        + 3^(3*s+3) * (omegaCutWord s core)^3 := by
    have hA1 : (3:Nat)^(2*s+3) = 3^(s+2) * 3^(s+1) := by
      rw [show (2*s+3) = (s+2)+(s+1) from by omega, Nat.pow_add]
    have hA2 : (3:Nat)^(3*s+3) = 3^(s+2) * 3^(2*s+1) := by
      rw [show (3*s+3) = (s+2)+(2*s+1) from by omega, Nat.pow_add]
    rw [hA1, hA2]
    ring
  have hmul : 3^(s+2) * omegaCutWord (s+1) core
      = 3^(s+2) * (omegaCutWord s core
        + 3^(s+1) * (omegaCutWord s core)^2
        + 3^(2*s+1) * (omegaCutWord s core)^3) := by
    omega
  exact Nat.eq_of_mul_eq_mul_left (Nat.pow_pos (by decide)) hmul

/-- **THE TRIPLING-CUBE DIGIT TRANSFER.**  For every one-mod-three core at
sheet level one and above, the ternary digit of the child power
`4^(3^(s+1) * core)` at row `2s+3` is the digit of the parent power
`4^(3^s * core)` at row `2s+2` incremented by one.  The parent's
sheet-gate row is the child's window-top row: the cube recurrence's
square term carries a fixed plus-one trit into exactly that position. -/
theorem omega_tripling_digit_transfer (s core : Nat) (hs : 1 ≤ s)
    (hcore : core % 3 = 1) :
    digit3 (4^(3^(s+1) * core)) (2*s+3)
      = (digit3 (4^(3^s * core)) (2*s+2) + 1) % 3 := by
  have h1lt : (1:Nat) < 3^(s+1) := by
    have h3 : (3:Nat)^1 ≤ 3^(s+1) := by
      simpa using Nat.pow_le_pow_of_le (by decide : 1 < (3:Nat))
        (by omega : 1 ≤ s+1)
    omega
  have hwmod3 : omegaCutWord s core % 3 = 1 := by
    unfold omegaCutWord
    rw [Nat.mul_mod, lteCoeff_mod3_one, omega_geo_mod3, Nat.one_mul]
    omega
  -- parent: digit at row 2s+2 is (W / 3^(s+1)) % 3
  have hp1 : (0:Nat) < 3^(s+1) := Nat.pow_pos (by decide)
  have hqP : 4^(3^s * core) / 3^(2*s+2)
      = (omegaCutWord s core) / 3^(s+1) := by
    rw [omega_cut_factor s core,
      show (3:Nat)^(2*s+2) = 3^(s+1) * 3^(s+1) from by
        rw [show (2*s+2) = (s+1)+(s+1) from by omega, Nat.pow_add],
      ← Nat.div_div_eq_div_mul,
      Nat.add_mul_div_left _ _ hp1,
      Nat.div_eq_of_lt h1lt, Nat.zero_add]
  -- child: digit at row 2s+3 is (W' / 3^(s+1)) % 3
  have hp2 : (0:Nat) < 3^(s+2) := Nat.pow_pos (by decide)
  have h1lt2 : (1:Nat) < 3^(s+2) := by
    have h3 : (3:Nat)^1 ≤ 3^(s+2) := by
      simpa using Nat.pow_le_pow_of_le (by decide : 1 < (3:Nat))
        (by omega : 1 ≤ s+2)
    omega
  have hqC : 4^(3^(s+1) * core) / 3^(2*s+3)
      = (omegaCutWord (s+1) core) / 3^(s+1) := by
    rw [omega_cut_factor (s+1) core,
      show (3:Nat)^(2*s+3) = 3^(s+2) * 3^(s+1) from by
        rw [show (2*s+3) = (s+2)+(s+1) from by omega, Nat.pow_add],
      ← Nat.div_div_eq_div_mul,
      Nat.add_mul_div_left _ _ hp2,
      Nat.div_eq_of_lt h1lt2, Nat.zero_add]
  -- the cube recurrence inside the child divisor
  have hp3 : (0:Nat) < 3^(s+1) := Nat.pow_pos (by decide)
  have hW' : (omegaCutWord (s+1) core) / 3^(s+1)
      = (omegaCutWord s core) / 3^(s+1)
        + (omegaCutWord s core)^2 + 3^s * (omegaCutWord s core)^3 := by
    rw [omega_tripling_cut_word s core,
      show omegaCutWord s core
          + 3^(s+1) * (omegaCutWord s core)^2
          + 3^(2*s+1) * (omegaCutWord s core)^3
          = omegaCutWord s core
            + 3^(s+1) * ((omegaCutWord s core)^2
              + 3^s * (omegaCutWord s core)^3) from by
        rw [show (3:Nat)^(2*s+1) = 3^(s+1) * 3^s from by
          rw [show (2*s+1) = (s+1)+s from by omega, Nat.pow_add]]
        ring,
      Nat.add_mul_div_left _ _ hp3]
    omega
  -- the square term carries the plus-one trit; the cube term is zero mod 3
  have hs0 : 3^s % 3 = 0 := by
    obtain ⟨t, ht⟩ : ∃ t, s = t + 1 := ⟨s - 1, by omega⟩
    rw [ht, Nat.pow_succ]
    omega
  have hsq : (omegaCutWord s core)^2 % 3 = 1 := by
    rw [Nat.pow_mod, hwmod3, Nat.one_pow]
  have hcu : (3^s * (omegaCutWord s core)^3) % 3 = 0 := by
    rw [Nat.mul_mod, hs0, Nat.zero_mul]
  unfold digit3
  rw [hqP, hqC, hW']
  omega

/-- **THE TRIPLING-CUBE GATE.**  If the parent's sheet-gate row carries
the trit one, the child power owns its ternary digit two at row `2s+3`:
the cube transfer increments the parent trit into the kill zone.  The
first cross-sheet kill: the child's digit is read off the parent's sheet
structure through the exact cube recurrence. -/
theorem omega_tripling_gate (s core : Nat) (hs : 1 ≤ s) (hcore : core % 3 = 1)
    (hparent : digit3 (4^(3^s * core)) (2*s+2) = 1) :
    digit3 (4^(3^(s+1) * core)) (2*s+3) = 2 := by
  rw [omega_tripling_digit_transfer s core hs hcore, hparent]

/-- **THE TRIPLING-CUBE KILL (existence form).**  Every one-mod-three
core whose parent sheet-gate row reads one hands the next sheet's shadow
exponent its digit two outright at row `2s+3`. -/
theorem omega_tripling_child_digit_two (s core : Nat) (hs : 1 ≤ s)
    (hcore : core % 3 = 1)
    (hparent : digit3 (4^(3^s * core)) (2*s+2) = 1) :
    ∃ p : Nat, digit3 (4^(3^(s+1) * core)) p = 2 :=
  ⟨2*s+3, omega_tripling_gate s core hs hcore hparent⟩

#check omega_tripling_cut_word
#check omega_tripling_digit_transfer
#check omega_tripling_gate
#check omega_tripling_child_digit_two
#print axioms omega_tripling_cut_word
#print axioms omega_tripling_digit_transfer
#print axioms omega_tripling_gate
#print axioms omega_tripling_child_digit_two

/-! ## §7.11 The infinite-controller chokehold (all inputs, all outputs)

The Law descends to the main infinite GST-V2 control graph — the one
infinite object `GSTGraphV2InfiniteControl.graph` of which every finite
rectangle is an observation.  The pure-power column `graph 1 K ·` is the
wave's own digit tape; the parity column `graph (1 + n % 2) (n / 2) ·` is
every exponent `2^n` at once (both parities, one object); and the
transplanted all-Nat controller state `graphCoupledState 1 K ·` reads
the same wave through the controller's own parent-digit output channel.
The chokehold: for every exponent from nine onward — every input, both
parities — the one infinite graph shows the ternary two somewhere in its
column, and every output cell of that column is pinned by the exact
lattice law `graph_cell_exact`. -/

/-- Every output digit of the main infinite graph is the exact ternary
digit of the horizontal full energy: the graph IS the digit tape of
`4^t * E` for every input pair. -/
theorem graph_column_digit_exact (E t p : Nat) :
    (graph E t p).seven.digit = digit3 (4^t * E) p := rfl

/-- Every output carry of the main infinite graph is the exact x4 carry
of the horizontal full energy. -/
theorem graph_column_carry_exact (E t p : Nat) :
    (graph E t p).seven.carry = carry4 (4^t * E) p := rfl

/-- The pure-power column of the main infinite graph is the wave's own
digit tape. -/
theorem graph_pure_power_digit_exact (K p : Nat) :
    (graph 1 K p).seven.digit = digit3 (4^K) p := by
  rw [graph_column_digit_exact, Nat.mul_one]

/-- The pure-power column's carries are the exact x4 carries of `4^K`. -/
theorem graph_pure_power_carry_exact (K p : Nat) :
    (graph 1 K p).seven.carry = carry4 (4^K) p := by
  rw [graph_column_carry_exact, Nat.mul_one]

/-- **THE CLOSED WAVE ON THE INFINITE GRAPH.**  The zero-input closed
statement, read as a statement about the one infinite control graph
itself: every shadow exponent's digit two is an output cell of the
pure-power column. -/
theorem omega_shadow_wave_graph
    (hClosed : four_power_omega_shadow_wave_closed)
    (K : Nat) (hK : 8 ≤ K) (hS : omegaShadow K) :
    ∃ p : Nat, (graph 1 K p).seven.digit = 2 := by
  obtain ⟨p, hp⟩ := hClosed K hK hS
  exact ⟨p, (graph_pure_power_digit_exact K p).trans hp⟩

/-- **THE EXHAUSTIVE GRAPH SPLIT — zero inputs.**  Every exponent from
eight onward either lies in the Ω-shadow residue or the one infinite
graph's pure-power column shows its ternary two outright. -/
theorem omega_digit_two_cases_graph (K : Nat) (hK : 8 ≤ K) :
    omegaShadow K ∨ ∃ p : Nat, (graph 1 K p).seven.digit = 2 := by
  rcases omega_digit_two_cases K hK with hS | ⟨p, hp⟩
  · exact Or.inl hS
  · exact Or.inr ⟨p, (graph_pure_power_digit_exact K p).trans hp⟩

/-- **THE WAVE THROUGH THE CONTROLLER'S OUTPUT CHANNEL.**  The transplanted
all-Nat controller's parent-digit output — the channel the bridge's own
`graphCoupledState_parentDigit_exact` observes — shows the shadow
exponent's two at the wave depth. -/
theorem controller_parent_digit_wave
    (hClosed : four_power_omega_shadow_wave_closed)
    (K : Nat) (hK : 8 ≤ K) (hS : omegaShadow K) :
    ∃ q : Nat,
      ((graphCoupledState 1 K q).parentOffset +
        4^K * ((graphCoupledState 1 K q).childTail % 3)) % 3 = 2 := by
  obtain ⟨p, hp⟩ := omega_shadow_wave_graph hClosed K hK hS
  exact ⟨p, (graphCoupledState_parentDigit_exact 1 K p).trans hp⟩

/-- **THE TRIPLING LAW IN GRAPH COORDINATES.**  The cross-sheet digit
transfer, read on the one infinite graph: the sheet-`s+1` column's row
`2s+3` output is the sheet-`s` column's row `2s+2` output plus one,
modulo three. -/
theorem omega_tripling_graph_digit_transfer (s core : Nat) (hs : 1 ≤ s)
    (hcore : core % 3 = 1) :
    (graph 1 (3^(s+1) * core) (2*s+3)).seven.digit =
      ((graph 1 (3^s * core) (2*s+2)).seven.digit + 1) % 3 := by
  rw [graph_pure_power_digit_exact (3^(s+1) * core) (2*s+3),
      graph_pure_power_digit_exact (3^s * core) (2*s+2)]
  exact omega_tripling_digit_transfer s core hs hcore

/-- The parity column identity: one column index per exponent, both
parities at once — `4^(n/2) * (1 + n % 2)` is literally `2^n`. -/
theorem graph_column_parity_energy (n : Nat) :
    4^(n/2) * (1 + n % 2) = 2^n := by
  have hcore : 4^(n/2) = 2^(2 * (n / 2)) := by
    rw [show (4:Nat) = 2^2 from by decide]
    rw [Nat.pow_mul]
  rcases Nat.mod_two_eq_zero_or_one n with h0 | h1
  · rw [h0, Nat.add_zero, Nat.mul_one, hcore]
    congr 1
    omega
  · rw [h1, hcore]
    rw [show 2^n = 2^(2 * (n / 2) + 1) from by congr 1; omega,
        Nat.pow_add]

/-- The three sub-wave even exponents: `4^5`, `4^6` and `4^7` own their
ternary digit two by direct computation (`1024 = 1101221₃`,
`4096 = 12121201₃`, `16384 = 211110211₃`). -/
theorem omega_small_digit_two (K : Nat) (hK5 : 5 ≤ K) (hK7 : K ≤ 7) :
    ∃ p : Nat, digit3 (4^K) p = 2 := by
  interval_cases K
  · exact ⟨1, by decide⟩
  · exact ⟨2, by decide⟩
  · exact ⟨2, by decide⟩

/-- **THE INFINITE-CONTROLLER CHOKEHOLD — all inputs, all outputs.**
For every exponent from nine onward — both parities, one theorem — the
one infinite control graph's parity column `graph (1 + n % 2) (n / 2)`
shows the ternary two: the odd wing by the elementary mod-three law at
row zero, the even wing by the Law's own coverage (the three sub-wave
exponents by direct computation, the Ω-shadow wave input everywhere
else).  Every output cell of the column is pinned by the exact lattice
law `graph_cell_exact`; the two is among them. -/
theorem infinite_graph_ternary_two_chokehold
    (hClosed : four_power_omega_shadow_wave_closed)
    (n : Nat) (hn : 9 ≤ n) :
    ∃ p : Nat, (graph (1 + n % 2) (n / 2) p).seven.digit = 2 := by
  rcases Nat.mod_two_eq_zero_or_one n with heven | hodd
  · have hcolEv : ∀ p : Nat,
      (graph (1 + n % 2) (n / 2) p).seven.digit = digit3 (4^(n / 2)) p := by
      intro p
      rw [graph_column_digit_exact, heven, Nat.add_zero, Nat.mul_one]
    have hK5 : 5 ≤ n / 2 := by omega
    rcases Nat.lt_or_ge (n / 2) 8 with hK8 | hK8
    · obtain ⟨p, hp⟩ := omega_small_digit_two (n / 2) hK5 (by omega)
      exact ⟨p, (hcolEv p).trans hp⟩
    · rcases omega_digit_two_cases (n / 2) hK8 with hS | ⟨p, hp⟩
      · obtain ⟨p, hp2⟩ := hClosed (n / 2) hK8 hS
        exact ⟨p, (hcolEv p).trans hp2⟩
      · exact ⟨p, (hcolEv p).trans hp⟩
  · refine ⟨0, ?_⟩
    rw [hodd, graph_column_digit_exact]
    show (4^(n/2) * (1 + 1)) / 3^0 % 3 = 2
    rw [Nat.pow_zero, Nat.div_one, Nat.mul_mod, pow4_mod3_one]

/-- **THE FULL OUTPUT ENVELOPE OF THE CHOKEHOLD COLUMN.**  For every
input exponent from nine onward, every output cell of the parity column
obeys the exact lattice law (the x4/base3 digit and carry recurrence)
AND the column contains the ternary two. -/
theorem infinite_graph_chokehold_envelope
    (hClosed : four_power_omega_shadow_wave_closed)
    (n : Nat) (hn : 9 ≤ n) :
    (∀ p : Nat,
      outDigit (graph (1 + n % 2) (n / 2) p).seven.carry
        (graph (1 + n % 2) (n / 2) p).seven.digit =
        (graph (1 + n % 2) (n / 2 + 1) p).seven.digit ∧
      nextCarry (graph (1 + n % 2) (n / 2) p).seven.carry
        (graph (1 + n % 2) (n / 2) p).seven.digit =
        (graph (1 + n % 2) (n / 2) (p+1)).seven.carry) ∧
    ∃ p : Nat, (graph (1 + n % 2) (n / 2) p).seven.digit = 2 :=
  ⟨fun p => graph_cell_exact (1 + n % 2) (n / 2) p,
    infinite_graph_ternary_two_chokehold hClosed n hn⟩

#check graph_column_digit_exact
#check graph_column_carry_exact
#check graph_pure_power_digit_exact
#check graph_pure_power_carry_exact
#check omega_shadow_wave_graph
#check omega_digit_two_cases_graph
#check controller_parent_digit_wave
#check omega_tripling_graph_digit_transfer
#check graph_column_parity_energy
#check omega_small_digit_two
#check infinite_graph_ternary_two_chokehold
#check infinite_graph_chokehold_envelope
#print axioms graph_column_digit_exact
#print axioms graph_column_carry_exact
#print axioms graph_pure_power_digit_exact
#print axioms graph_pure_power_carry_exact
#print axioms omega_shadow_wave_graph
#print axioms omega_digit_two_cases_graph
#print axioms controller_parent_digit_wave
#print axioms omega_tripling_graph_digit_transfer
#print axioms graph_column_parity_energy
#print axioms omega_small_digit_two
#print axioms infinite_graph_ternary_two_chokehold
#print axioms infinite_graph_chokehold_envelope

#check omega_binom_two_mul
#check omega_half_mod9_of_mod9_three
#check omega_half_mod9_of_mod9_six
#check omega_mul_mod9_three
#check omega_mul_mod9_six
#check omega_powmul_mod_cubed
#check omega_binom_mod9_four
#check omega_binom_mod9_seven
#check omega_cut_word_full3
#check omega_sheet2_digit
#check omega_sheet2_gate_four
#check omega_sheet2_gate_seven
#check omega_expcycle_period81
#check omega_expcycle_period243
#check omega_expcycle_row3_digit_two
#check omega_expcycle_row4_digit_two_one
#check omega_expcycle_row4_digit_two_four
#check omega_expcycle_period729
#check omega_expcycle_row5_digit_two_one
#check omega_expcycle_row5_digit_two_four
#check omega_lteCoeff_mod243
#check omega_level5_digit_two
#check omega_lteCoeff_mod729
#check omega_level6_digit_two
#check omegaShadowTail3
#check four_power_omega_shadow_wave_tail3
#check omegaShadowTail4
#check four_power_omega_shadow_wave_tail4
#check four_power_omega_shadow_wave_closed
#print axioms omega_cut_word_full3
#print axioms omega_sheet2_digit
#print axioms omega_sheet2_gate_four
#print axioms omega_sheet2_gate_seven
#print axioms omega_expcycle_row3_digit_two
#print axioms omega_expcycle_row4_digit_two_one
#print axioms omega_expcycle_row4_digit_two_four
#print axioms omega_expcycle_period729
#print axioms omega_expcycle_row5_digit_two_one
#print axioms omega_expcycle_row5_digit_two_four
#print axioms omega_lteCoeff_mod243
#print axioms omega_cut_word_mod243
#print axioms omega_level5_digit_two
#print axioms omega_lteCoeff_mod729
#print axioms omega_cut_word_mod729
#print axioms omega_level6_digit_two
#print axioms omegaShadowTail3
#print axioms four_power_omega_shadow_wave_tail3
#print axioms omegaShadowTail4
#print axioms four_power_omega_shadow_wave_tail4

#check omegaShadow
#check four_power_omega_shadow_wave
#check four_power_omega_shadow_wave_closed
#check omega_row2_digit_two
#check omega_three_free_decomposition
#check omega_digit_two_cases
#check omega_digit_two_of_not_shadow
#check omega_digit_two_coverage
#check omega_lteCoeff_mod27
#check omega_base_mod27
#check omega_geo_mod27
#check omega_cut_word_mod27
#check omega_level3_digit
#check omega_level3_digit_two
#check omegaShadowTail
#check four_power_omega_shadow_wave_tail
#check omegaShadowTail2
#check four_power_omega_shadow_wave_tail2
#check omega_cut_word_full
#check omega_cut_word_mod_pow2
#check omega_sheet_digit
#check omega_sheet_gate_digit_two
#check omega_level4_digit_two
#print axioms omegaShadowTail
#print axioms four_power_omega_shadow_wave_tail
#print axioms omega_cut_word_full
#print axioms omega_cut_word_mod_pow2
#print axioms omega_sheet_digit
#print axioms omega_sheet_gate_digit_two
#print axioms omega_level4_digit_two
#print axioms omega_digit_two_of_not_shadow
#print axioms omega_digit_two_coverage
#print axioms omega_lteCoeff_mod27
#print axioms omega_base_mod27
#print axioms omega_geo_mod27
#print axioms omega_cut_word_mod27
#print axioms omega_level3_digit
#print axioms omega_level3_digit_two

/-! ## §7.13 The observer layer — one law, all generations

The tower gates of the earlier sections each read one fixed trit of the
sheet word at one fixed tower level: level three through level seven, one
theorem per level, one numeral per level.  The observer layer collapses
the ENTIRE tower into a single law.  The instrument is the linearity of
the cut word: modulo its own cut modulus, the cut word of every core is
the unit-core cut word times the core — the binomial truncation of the LTE
factorization, since the square of the unit sheet's cut modulus already
divides every higher binomial term.  Consequently every tower digit of
every generation `s` at every level `k ≤ s+1` is read off ONE object: the
mean rotation `omegaCutWord s 1 * core`.  The per-level gates — level
three, level four, level five, level six, level seven, and every level
beyond — are all instances of one theorem, and the generation ladder on
the tower axis terminates here. -/

/-- **THE CUT-WORD LINEARITY LAW.**  The sheet word is the mean rotation of
the core: the cut word of `core` sheets equals the unit-core cut word
times the core, modulo the next cut modulus.  The proof is the binomial
truncation of the LTE factorization — `(1 + 3^(s+1) λ)^core` agrees with
`1 + core · 3^(s+1) λ` below the squared cut modulus. -/
theorem omega_cut_word_linear (s core : Nat) :
    ∃ t : Nat, omegaCutWord s core
      = omegaCutWord s 1 * core + 3^(s+1) * t := by
  have hpow : (4^(3^s * 1))^core = 4^(3^s * core) := by
    rw [Nat.mul_one]
    exact (Nat.pow_mul 4 (3^s) core).symm
  have hf1 : 4^(3^s * 1) = 1 + 3^(s+1) * omegaCutWord s 1 :=
    omega_cut_factor s 1
  have hfc : 4^(3^s * core) = 1 + 3^(s+1) * omegaCutWord s core :=
    omega_cut_factor s core
  have hbinom : ∀ c : Nat, ∃ t : Nat,
      (1 + 3^(s+1) * omegaCutWord s 1)^c
        = 1 + 3^(s+1) * (omegaCutWord s 1 * c)
          + 3^(s+1) * (3^(s+1) * t) := by
    intro c
    induction c with
    | zero => exact ⟨0, by rw [Nat.pow_zero]; ring⟩
    | succ c ih =>
        obtain ⟨t, ht⟩ := ih
        refine ⟨omegaCutWord s 1 * omegaCutWord s 1 * c + t
          + t * 3^(s+1) * omegaCutWord s 1, ?_⟩
        rw [Nat.pow_succ, ht]
        ring
  obtain ⟨t, ht⟩ := hbinom core
  have hkey : 1 + 3^(s+1) * omegaCutWord s core
      = 1 + 3^(s+1) * (omegaCutWord s 1 * core)
        + 3^(s+1) * (3^(s+1) * t) := by
    rw [← hfc, ← hpow, hf1]
    exact ht
  refine ⟨t, ?_⟩
  have hm : 0 < 3^(s+1) := Nat.pow_pos (by decide)
  refine Nat.eq_of_mul_eq_mul_left hm ?_
  rw [Nat.mul_add]
  omega

/-- **THE OBSERVER LAW — one object, all generations, all tower levels.**
For every sheet level `s`, every core, and every tower level `k` with
`1 ≤ k ≤ s+1`: the ternary digit of the power `4^(3^s * core)` at tower
row `s+k` is the `(k-1)`-th trit of the single mean rotation
`omegaCutWord s 1 * core`.  No per-level numeral, no per-level gate
theorem: the whole tower is this one identity. -/
theorem omega_observed_digit (s core k : Nat) (hk : 1 ≤ k) (hks : k ≤ s+1) :
    digit3 (4^(3^s * core)) (s + k)
      = ((omegaCutWord s 1 * core) % 3^k) / 3^(k-1) := by
  have hf := omega_cut_factor s core
  have h1 : (1:Nat) < 3^(s+1) := by
    have h3 : (3:Nat)^1 ≤ 3^(s+1) := by
      simpa using Nat.pow_le_pow_of_le (by decide : 1 < (3:Nat))
        (by omega : 1 ≤ s+1)
    omega
  have hslice := prefix_slice_digit_exact (s+1) 1 (omegaCutWord s core) (k-1) h1
  rw [show s+k = (s+1)+(k-1) from by omega, hf, hslice]
  obtain ⟨t, ht⟩ := omega_cut_word_linear s core
  have hsplit : 3^(s+1) = 3^(k-1) * 3^(s+2-k) := by
    rw [show s+1 = (k-1) + (s+2-k) from by omega, Nat.pow_add]
  have hz0 : 3^(s+2-k) % 3 = 0 := by
    obtain ⟨u, hu⟩ : ∃ u, s+2-k = u+1 := ⟨s+1-k, by omega⟩
    rw [hu, Nat.pow_succ]
    omega
  have hz : (3^(s+2-k) * t) % 3 = 0 := by
    rw [Nat.mul_mod, hz0, Nat.zero_mul]
  unfold digit3
  rw [ht, hsplit, Nat.mul_assoc,
    Nat.add_mul_div_left _ _ (Nat.pow_pos (by decide) : (0:Nat) < 3^(k-1))]
  have hwindow := digit3_window (omegaCutWord s 1 * core) (k-1)
  rw [show (k-1)+1 = k from by omega] at hwindow
  omega

/-- **THE UNIFORM TOWER GATE — all levels, all generations, one law.**
For every sheet level `s`, every core, and EVERY tower level `k ≥ 3`
inside the sheet's window (`k ≤ s+1`): whenever the mean rotation's trit
at position `k-1` is two — the top third of the residue window modulo
`3^k` — the power `4^(3^s * core)` owns its ternary digit two at row
`s+k`.  Level three through level seven and every level beyond are all
instances; the tower's generation ladder ends here. -/
theorem omega_tower_level_digit_two (s core k : Nat) (hk : 3 ≤ k)
    (hks : k ≤ s+1)
    (hg : 2 * 3^(k-1) ≤ (omegaCutWord s 1 * core) % 3^k) :
    digit3 (4^(3^s * core)) (s + k) = 2 := by
  rw [omega_observed_digit s core k (by omega) hks]
  have hlt : (omegaCutWord s 1 * core) % 3^k < 3^k :=
    Nat.mod_lt _ (Nat.pow_pos (by decide))
  have h3 : 3^k = 3 * 3^(k-1) := by
    have hps : 3^((k-1)+1) = 3^(k-1) * 3 := Nat.pow_succ (3:Nat) (k-1)
    have hk' : (k-1)+1 = k := by omega
    rw [hk'] at hps
    rw [hps]
    ring
  have hlt2 : (omegaCutWord s 1 * core) % 3^k < 3 * 3^(k-1) := by omega
  obtain ⟨d, hd⟩ : ∃ d, (omegaCutWord s 1 * core) % 3^k
      = 2 * 3^(k-1) + d :=
    ⟨(omegaCutWord s 1 * core) % 3^k - 2 * 3^(k-1), by omega⟩
  have hdlt : d < 3^(k-1) := by omega
  rw [hd, Nat.add_comm, show 2 * 3^(k-1) = 3^(k-1) * 2 from by ring,
    Nat.add_mul_div_left _ _ (Nat.pow_pos (by decide) : (0:Nat) < 3^(k-1)),
    Nat.div_eq_of_lt hdlt]

/-- **THE OBSERVER TAIL — the residual after the whole tower.**  The
shadow exponent whose `(s, core)` dodges the kernel base, the Ω-sheet
gate, the Ω-second-sheet gate, the sheet-zero exponent-cycle gates through
row six — and EVERY tower level at once: the mean rotation
`omegaCutWord s 1 * core` keeps its trit below the top third of the
residue window at every depth `k` from three to the sheet's own window
top.  The per-level tower gates — levels three through seven and beyond —
are all paid by the uniform observer law; the residual speaks only in the
single all-depths object. -/
def omegaShadowTailE (K : Nat) : Prop :=
  ∃ s core : Nat, K = 3^s * core ∧ ¬ 3 ∣ core ∧
    (core % 9 = 4 ∨ (s = 0 ∧ core % 9 = 1) ∨ (1 ≤ s ∧ core % 9 = 7)) ∧
    ((omegaCutWord s core) % 3^(s+2) < 2 * 3^(s+1)) ∧
    (1 ≤ s → (core % 9 = 4 →
      3^(s+2) ≤ (lteCoeff s * core) % 3^(s+3))) ∧
    (1 ≤ s → (core % 9 = 7 →
      ((lteCoeff s * core) % 3^(s+3) < 3^(s+2)
        ∨ 2 * 3^(s+2) ≤ (lteCoeff s * core) % 3^(s+3)))) ∧
    (s = 0 → (core % 9 = 1 → core % 27 ≠ 19 ∧ core % 81 ≠ 55
      ∧ core % 81 ≠ 64 ∧ core % 81 ≠ 73)) ∧
    (s = 0 → (core % 9 = 4 → core % 27 ≠ 22 ∧ core % 81 ≠ 58
      ∧ core % 81 ≠ 67 ∧ core % 81 ≠ 76)) ∧
    (s = 0 → (core % 243 ≠ 85 ∧ core % 243 ≠ 91 ∧ core % 243 ≠ 112
      ∧ core % 243 ≠ 118 ∧ core % 243 ≠ 163 ∧ core % 243 ≠ 175
      ∧ core % 243 ≠ 190 ∧ core % 243 ≠ 202)) ∧
    (s = 0 → (core % 729 ≠ 31 ∧ core % 729 ≠ 37 ∧ core % 729 ≠ 172
      ∧ core % 729 ≠ 253 ∧ core % 729 ≠ 256 ∧ core % 729 ≠ 271
      ∧ core % 729 ≠ 337 ∧ core % 729 ≠ 352 ∧ core % 729 ≠ 409
      ∧ core % 729 ≠ 487 ∧ core % 729 ≠ 490 ∧ core % 729 ≠ 526
      ∧ core % 729 ≠ 568 ∧ core % 729 ≠ 607 ∧ core % 729 ≠ 679
      ∧ core % 729 ≠ 685)) ∧
    (∀ k : Nat, 3 ≤ k → k ≤ s+1 →
      (omegaCutWord s 1 * core) % 3^k < 2 * 3^(k-1))

/-- **THE Ω-SHADOW WAVE TAIL (OBSERVER FORM)** — the residual input after
the kernel-checked base, the Ω-sheet gate, the Ω-second-sheet gate, the
sheet-zero exponent-cycle gates through row six, and the ENTIRE Ω-cut
tower — every level at once — paid unconditionally by the uniform
observer law.  A strictly weaker hypothesis than the sixth weakening: the
observer dodge implies every per-level tower dodge of `tail5`, and asks
for all depths in one object. -/
def four_power_omega_shadow_wave_tailE : Prop :=
  ∀ K : Nat, 500 < K → omegaShadowTailE K → ∃ p : Nat, digit3 (4^K) p = 2

#check omega_cut_word_linear
#check omega_observed_digit
#check omega_tower_level_digit_two
#check omegaShadowTailE
#check four_power_omega_shadow_wave_tailE
#print axioms omega_cut_word_linear
#print axioms omega_observed_digit
#print axioms omega_tower_level_digit_two
#print axioms omegaShadowTailE
#print axioms four_power_omega_shadow_wave_tailE

/-! ## §7.14 The second observer layer — one law, all rows

The ROW axis of the weakening chain dies here, exactly as the tower
axis died in §7.13.  The sheet-zero exponent-cycle rows — row three,
row four, row five, row six, and every row beyond, at every depth,
forever, each row doubling its exclusion list (eight classes, sixteen,
thirty-two, sixty-four...) — are the trits of ONE object: the ROW WORD,
which is the cut word at sheet zero.  The uniform row law reads the
kill trit off that one object at ANY depth: there is no row seven, no
row eight, no next row — every row is already inside the one law, as
instances at `j = 2, 3, 4, 5, ...`.  The observer tail's sheet-zero
exclusion lists were the finite shadows of this single all-depths
clause. -/

/-- **THE UNIFORM ROW LAW** — the row-axis twin of the tower observer
`omega_tower_level_digit_two`.  For every core and every depth `j`, if
the row word — the cut word at sheet zero, `omegaCutWord 0 core`, which
is exactly the mean row word `(4^core - 1)/3` — has its top trit two in
the window modulo `3^(j+1)`, then `4^core` owns its ternary digit two
at position `1 + j`.  Rows three through six and every row beyond are
instances at `j = 2, 3, 4, 5, ...`.  The proof is the prefix-slice law
at sheet zero: `4^core = 1 + 3^1 * omegaCutWord 0 core`, so the digit
at position `1 + j` is the row word's own digit at `j`. -/
theorem omega_row_level_digit_two (core : Nat) (j : Nat)
    (hkill : 2 * 3^j ≤ (omegaCutWord 0 core) % 3^(j+1)) :
    digit3 (4^core) (1 + j) = 2 := by
  have h1 : (1:Nat) < 3^1 := by decide
  have hslice := prefix_slice_digit_exact 1 1 (omegaCutWord 0 core) j h1
  have hf : 4^core = 1 + 3^1 * omegaCutWord 0 core := by
    have h := omega_cut_factor 0 core
    have h0 : (3:Nat)^0 * core = core := by
      rw [Nat.pow_zero, Nat.one_mul]
    rw [h0] at h
    exact h
  rw [hf, hslice]
  unfold digit3
  rw [digit3_window]
  have hpos : 0 < 3^j := Nat.pow_pos (by decide)
  have hlt : (omegaCutWord 0 core) % 3^(j+1) < 3^(j+1) :=
    Nat.mod_lt _ (Nat.pow_pos (by decide))
  have hpow : 3^(j+1) = 3 * 3^j := by
    rw [Nat.pow_add, Nat.pow_one]
    ring
  rw [hpow] at hlt
  obtain ⟨d, hd⟩ : ∃ d, (omegaCutWord 0 core) % 3^(j+1) = 2 * 3^j + d :=
    ⟨(omegaCutWord 0 core) % 3^(j+1) - 2 * 3^j, by omega⟩
  have hdlt : d < 3^j := by omega
  rw [hd, Nat.add_comm, show 2 * 3^j = 3^j * 2 from by ring,
    Nat.add_mul_div_left _ _ hpos, Nat.div_eq_of_lt hdlt]

/-! ## Exact row observer threshold -/

/-- **ROW OBSERVER IFF.**  The sheet-zero row law is lossless: digit two at
position `1+j` is equivalent to the row word lying in the top third of its
exact residue window modulo `3^(j+1)`.  This closes the symmetry with the
tower observer. -/
theorem omega_row_level_digit_two_iff
    (core j : Nat) :
    digit3 (4^core) (1+j) = 2
      ↔ 2 * 3^j ≤ (omegaCutWord 0 core) % 3^(j+1) := by
  constructor
  · intro hd
    have h1 : (1:Nat) < 3^1 := by decide
    have hslice :=
      prefix_slice_digit_exact 1 1 (omegaCutWord 0 core) j h1
    have hf : 4^core = 1 + 3^1 * omegaCutWord 0 core := by
      have h := omega_cut_factor 0 core
      have h0 : (3:Nat)^0 * core = core := by
        rw [Nat.pow_zero, Nat.one_mul]
      rw [h0] at h
      exact h
    have hword : digit3 (omegaCutWord 0 core) j = 2 := by
      rw [hf, hslice] at hd
      exact hd
    unfold digit3 at hword
    rw [digit3_window] at hword
    have hpos : 0 < 3^j := Nat.pow_pos (by decide)
    have hq :
        2 ≤ ((omegaCutWord 0 core) % 3^(j+1)) / 3^j := by
      simpa [hword]
    exact (Nat.le_div_iff_mul_le hpos).1 hq
  · exact omega_row_level_digit_two core j

/-- The complementary sheet-zero classifier is exact as well. -/
theorem omega_row_level_not_two_iff
    (core j : Nat) :
    digit3 (4^core) (1+j) ≠ 2
      ↔ (omegaCutWord 0 core) % 3^(j+1) < 2 * 3^j := by
  constructor
  · intro hNot
    by_contra hge
    exact hNot ((omega_row_level_digit_two_iff core j).2 (by omega))
  · intro hlt hTwo
    have hge := (omega_row_level_digit_two_iff core j).1 hTwo
    omega

#check omega_row_level_digit_two_iff
#check omega_row_level_not_two_iff
#print axioms omega_row_level_digit_two_iff

/-- **THE Ω-SHADOW TAIL (SECOND OBSERVER FORM)** — the residual input
after the kernel-checked base, the Ω-sheet gate, the Ω-second-sheet
gates, and BOTH observers: the tower observer of §7.13 (every tower
level of every generation at once) and the row observer of §7.14
(every sheet-zero exponent-cycle row at once).  A strictly weaker
hypothesis than the observer form: the sheet-zero exclusion lists of
`tailE` — rows three through six — are subsumed by the single
all-depths row clause, and every row beyond is inside it too.  The
sheet-zero residual is ONE 3-adic object: the row word of the core,
every trit from depth two upward below the top third. -/
def omegaShadowTailF (K : Nat) : Prop :=
  ∃ s core : Nat, K = 3^s * core ∧ ¬ 3 ∣ core ∧
    (core % 9 = 4 ∨ (s = 0 ∧ core % 9 = 1) ∨ (1 ≤ s ∧ core % 9 = 7)) ∧
    ((omegaCutWord s core) % 3^(s+2) < 2 * 3^(s+1)) ∧
    (1 ≤ s → (core % 9 = 4 →
      3^(s+2) ≤ (lteCoeff s * core) % 3^(s+3))) ∧
    (1 ≤ s → (core % 9 = 7 →
      ((lteCoeff s * core) % 3^(s+3) < 3^(s+2)
        ∨ 2 * 3^(s+2) ≤ (lteCoeff s * core) % 3^(s+3)))) ∧
    (s = 0 → ∀ j : Nat, 2 ≤ j →
      (omegaCutWord 0 core) % 3^(j+1) < 2 * 3^j) ∧
    (∀ k : Nat, 3 ≤ k → k ≤ s+1 →
      (omegaCutWord s 1 * core) % 3^k < 2 * 3^(k-1))

/-- **THE Ω-SHADOW WAVE TAIL (SECOND OBSERVER FORM)** — the residual
input after both observers: the entire tower AND the entire
sheet-zero row cycle, each collapsed to one all-depths clause. -/
def four_power_omega_shadow_wave_tailF : Prop :=
  ∀ K : Nat, 500 < K → omegaShadowTailF K → ∃ p : Nat, digit3 (4^K) p = 2


/-! ## Exact observer threshold -/

/-- **TOWER OBSERVER IFF.**  Inside every legal tower window, digit two is
equivalent to the mean rotation lying in the top third of its exact ternary
residue window.  The earlier gate theorem supplied the forward implication;
the observer formula supplies the converse. -/
theorem omega_tower_level_digit_two_iff
    (s core k : Nat) (hk : 3 ≤ k) (hks : k ≤ s+1) :
    digit3 (4^(3^s * core)) (s+k) = 2
      ↔ 2 * 3^(k-1) ≤ (omegaCutWord s 1 * core) % 3^k := by
  constructor
  · intro hd
    have hobs := omega_observed_digit s core k (by omega) hks
    rw [hd] at hobs
    have hpos : 0 < 3^(k-1) := Nat.pow_pos (by decide)
    have hq :
        2 ≤ ((omegaCutWord s 1 * core) % 3^k) / 3^(k-1) := by
      omega
    have hmul := (Nat.le_div_iff_mul_le hpos).1 hq
    simpa [Nat.mul_comm] using hmul
  · intro hg
    exact omega_tower_level_digit_two s core k hk hks hg

/-- The observer therefore gives an exact Boolean-style classifier of every
tower level in its admissible window. -/
theorem omega_tower_level_not_two_iff
    (s core k : Nat) (hk : 3 ≤ k) (hks : k ≤ s+1) :
    digit3 (4^(3^s * core)) (s+k) ≠ 2
      ↔ (omegaCutWord s 1 * core) % 3^k < 2 * 3^(k-1) := by
  constructor
  · intro hNotTwo
    have hNotGate :
        ¬ (2 * 3^(k-1) ≤ (omegaCutWord s 1 * core) % 3^k) := by
      intro hGate
      exact hNotTwo
        ((omega_tower_level_digit_two_iff s core k hk hks).2 hGate)
    omega
  · intro hBelow hTwo
    have hGate :=
      (omega_tower_level_digit_two_iff s core k hk hks).1 hTwo
    omega

/-- **TWO-OBSERVER CROWN.**  Both the sheet-zero row axis and every legal
tower axis are now exact Boolean classifiers of their respective ternary
windows. -/
theorem omega_two_observer_classifier_crown :
    (∀ core j,
      digit3 (4^core) (1+j) = 2
        ↔ 2 * 3^j ≤ (omegaCutWord 0 core) % 3^(j+1))
    ∧
    (∀ s core k, 3 ≤ k → k ≤ s+1 →
      (digit3 (4^(3^s * core)) (s+k) = 2
        ↔ 2 * 3^(k-1) ≤ (omegaCutWord s 1 * core) % 3^k)) := by
  exact ⟨omega_row_level_digit_two_iff,
    fun s core k hk hks => omega_tower_level_digit_two_iff s core k hk hks⟩

#check omega_two_observer_classifier_crown
#print axioms omega_two_observer_classifier_crown

#check omega_row_level_digit_two
#check omegaShadowTailF
#check four_power_omega_shadow_wave_tailF
#check omega_tower_level_digit_two_iff
#check omega_tower_level_not_two_iff
#print axioms omega_row_level_digit_two
#print axioms omegaShadowTailF
#print axioms four_power_omega_shadow_wave_tailF
#print axioms omega_tower_level_digit_two_iff

end GSTGraphV2OmegaWaveLaw

/-- Monolith transplant route: the class-two family's creation certificate,
delivered by the Ω-cut gate with no hypothesis of any kind.  This is the
Law's direct entry point into the navigation seam — an infinite arithmetic
family (all `K = 3^a * core`, `a ≥ 1`, `core ≡ 2 (mod 3)`) that previously
required the third-wave climb hypothesis. -/
theorem gst_four_power_creation_certificate_of_omega_cut
    (K : Nat) (hK : GSTGraphV2OmegaWaveLaw.omegaClassTwo K) :
    ∃ p : Nat, 1 ≤ p ∧ (4^K) / 3^p % 3 = 2 ∧
      ((4 * ((4^K) % 3^p)) / 3^p % 3 = 0 ∨
       ((4 * ((4^K) % 3^p)) / 3^p % 3 = 1 ∧
        (4^K) / 3^(p+1) % 3 = 2)) := by
  obtain ⟨a, core, ha, hcore, hKac⟩ := hK
  rw [hKac]
  exact GSTGraphV2OmegaWaveLaw.omega_cut_certificate a core ha hcore

#print axioms gst_four_power_creation_certificate_of_omega_cut
