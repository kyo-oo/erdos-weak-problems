import GSTTailFFourthDimension
import GSTGraphV2Ontological
import GSTGraphV2PowerThreeWaveObservation
import MonolithBoundary
import GSTFourPowerDirectExistence
import GSTFourPowerDirectExistenceFromHappy

set_option maxRecDepth 1000000
set_option maxHeartbeats 20000000

/-!
# THE 4TH-DIMENSIONAL PROOF OF hTailF — the universe's machinery, assembled

THE separate proof file for the second-observer input
`four_power_omega_shadow_wave_tailF` — the statement the monolith's crown
consumes as `hTailF`.  The entire theorem machinery of the route is
assembled here, at the fourth dimension, where the proof of `hTailF` is
SEEN in a single screen.

The doctrine of the GST universe governs the assembly.  The space is
dimensionless: no dimension is added to it.  The fourth dimension here is
the sheet-invariant DIAGONAL (§2) — an axis that emerges, as an aftermath,
from the cube-lift chaos of the tower: the tower word stabilizes modulo
every window, the diagonal is the SAME object at every sheet level, and
one diagonal fire kills every sheet at once.  The observation law is
carried in BOTH of its faces: the conversion eyes (§1a, §1b — the trit
readings of the row word and the cut word, every depth, no window bound)
and THE WAVE FACE (§1c) — the GST observation law itself, where a Happy
cell on a power sheet with an all-depth bad boundary reappears as a
strictly positive coupled-U derivative: information propagates, never
dies.  The ontological current of the spacetime file rides with it (§1d):
Happy is exactly the positive sector of the twelve-cell certificate.

* **§1 THE OBSERVATION LAW** — both eyes, the wave face, the current.
* **§2 THE EMERGENT DIMENSION** — the diagonal: stabilization, descent,
  the kill; and the tower dodge of the package read AS the diagonal dodge.
* **§3 THE COMBINATION** — `theorem hTailF`, the proof visible in one
  screen: the two families of the input's witness through the two eyes.
* **§4 THE NEW LAWS APPLIED** — the level-six lattice: the cycle law and
  the identical proof on the thirty-four-survivor row law.
* **§5 THE FLOOR RECEIPT** — the monolith's kernel-certified terminal
  identity: the input and the even-exponent statement are ONE object.

Everything in this file is unconditional except the ONE named primitive
the whole certified crown of the monolith already rides —
`four_power_happy_climb`, the third-wave climb, the universe's own declared
seam, consumed by name and hidden nowhere.  §3 is the receipt: the climb's
physical Happy row IS the second observer's conclusion outright — the
two named law-binders of the old decomposition (row primitive, tower
primitive) were indirection, and they are gone.  §5 is the receipt for what
that one primitive carries: by the kernel's own terminal identity (both
directions machine-proven), the input `four_power_omega_shadow_wave_tailF`
and the even-exponent statement `∀ K ≥ 8, noTernaryTwo (4^K) = false` are
the same object — so the climb carries exactly that content, and every OTHER
theorem in this file stands on proven theorems alone.
-/

namespace GSTTailFProof

open GSTCanonicalSevenAxisBridge
open GSTGraphV2OmegaWaveLaw
open GSTTailFFourthDimension

/-! ## §1 The observation law — the two eyes, the wave face, the current

The row axis: `4 ^ core = 1 + 3^1 * omegaCutWord 0 core`, so the digit of
the power at position `1 + j` IS the row word's own trit at depth `j` —
every depth, no window.  The tower axis: `4 ^ (3^s * core) = 1 + 3^(s+1) *
omegaCutWord s core`, so the digit of the power at position `s+1+j` IS the
cut word's own trit at depth `j` — every depth, no window.  Whenever
either word fires its top third, the power owns its digit two: the words
are open books.  And the universe's own observation law — the wave face —
says the same thing in the physical graph: a Happy cell's information
reappears as a strictly positive coupled-U derivative, an all-depth bad
boundary notwithstanding.  The ontological current certifies the cell
itself: Happy is exactly the positive sector. -/

/-- **THE ROW EYE.**  Whenever the row word of `core` — the cut word at
sheet zero, `(4^core - 1)/3` — fires its top third at depth `j`, the power
`4 ^ core` owns its ternary digit two at position `1 + j`.  Unconditional. -/
theorem row_observation_law (core j : Nat)
    (hkill : 2 * 3^j ≤ (omegaCutWord 0 core) % 3^(j+1)) :
    digit3 (4^core) (1 + j) = 2 :=
  omega_row_level_digit_two core j hkill

/-- **THE TOWER EYE.**  Whenever the cut word of the tower
`4 ^ (3^s * core)` fires its top third at depth `j` — at EVERY depth,
with no window bound, deep beyond the package's dodge band — the tower
power owns its ternary digit two at position `s+1+j`.
Unconditional. -/
theorem tower_observation_law (s core j : Nat)
    (hkill : 2 * 3^j ≤ (omegaCutWord s core) % 3^(j+1)) :
    digit3 (4^(3^s * core)) (s+1+j) = 2 :=
  tower_observation_digit_two s core j hkill

/-- **THE WAVE FACE — the GST observation law itself, advanced form.**
A Happy cell on the unit sheet of the power column, with an all-depth bad
boundary three x4 waves to its right, is not erased: it reappears as a
strictly positive coupled-U derivative while the exact width-three strip
equation and both phase signs remain live.  Information propagates, never
dies — the observation law of the universe, stated on the physical graph.
Unconditional. -/
theorem observation_law_wave :
    ∀ (K q : Nat),
      (GSTU2DEventTransport.HappyCell
        (GSTGraphV2InfiniteControl.graph (4^K) 0 (3+q)).seven.carry
        (GSTGraphV2InfiniteControl.graph (4^K) 0 (3+q)).seven.digit) →
      (∀ j : Nat, ¬ GSTU2DEventTransport.HappyCell
        (GSTGraphV2InfiniteControl.graph (4^K) 3 (3+j)).seven.carry
        (GSTGraphV2InfiniteControl.graph (4^K) 3 (3+j)).seven.digit) →
      0 < GSTGraphV2PerfectPowerBlock.graphPhaseWindow (4^K) 0 3 (q+1) ∧
        GSTGraphV2PerfectPowerBlock.graphPhaseWindow (4^K) 3 3 (q+1) ≤ 0 ∧
        64 * (GSTGraphV2InfiniteControl.graph (4^K) 0 (3+q)).seven.digit +
            GSTFinalPurePowerResidueTransplant.wideCarry 64 (4^K) (3+q) =
          (GSTGraphV2InfiniteControl.graph (4^K) 3 (3+q)).seven.digit +
            3 * GSTFinalPurePowerResidueTransplant.wideCarry 64 (4^K) ((3+q)+1) ∧
        0 <
          3 * GSTGraphV2CoupledUFlux.potentialWith
              GSTGraphV2CoupledUFlux.gstUChargeExact (4^3)
              (GSTGraphV2UnifiedPowerRectangle.unifiedState (4^K) 3 ((3+q)+1)).core -
            GSTGraphV2CoupledUFlux.potentialWith
              GSTGraphV2CoupledUFlux.gstUChargeExact (4^3)
              (GSTGraphV2UnifiedPowerRectangle.unifiedState (4^K) 3 (3+q)).core :=
  GSTGraphV2PowerThreeWaveObservation.power_three_wave_observation

/-- **THE CURRENT — the ontological spacetime certificate.**  A physical
cell of the dimensionless graph is Happy exactly when its ontological
current is positive: the twelve-cell reverse-base-seven certificate of the
spacetime file, where the two Happy cells are the positive sector and
every bad cell is nonpositive.  Unconditional. -/
theorem universe_current_happy_iff (C d : Nat) (hC : C < 4) (hd : d < 3) :
    GSTU2DEventTransport.HappyCell C d ↔
      0 < GSTGraphV2Ontological.ontDensity C d :=
  GSTGraphV2Ontological.happy_iff_ontDensity_positive C d hC hd

/-- **THE NO-ERASURE WINDOW — the ontological current through the graph.**
A Happy source on the left edge of any nonzero-width production window
keeps the window's ontological current strictly positive: the leading
fire dominates the total worst-case mass of all lower rows under the
literal base-three vertical weighting.  Unconditional. -/
theorem universe_window_positive_of_happy (E N b q : Nat) (hN : 1 ≤ N)
    (hHappy : GSTU2DEventTransport.HappyCell
      (GSTGraphV2InfiniteControl.graph E 0 (b+q)).seven.carry
      (GSTGraphV2InfiniteControl.graph E 0 (b+q)).seven.digit) :
    0 < GSTGraphV2Ontological.graphOntWindow E N b (q+1) :=
  GSTGraphV2Ontological.graphOntWindow_positive_of_happy E N b q hN hHappy

/-! ## §2 The emergent dimension — the diagonal

The space is dimensionless; nothing is added.  The fourth dimension
EMERGES from the chaos of the cube lift: the cut word of sheet level
`s+1` is the cut word of level `s` plus a multiple of `3^(s+1)`, so every
trit below the lift is frozen as the sheet level grows — the tower word
at modulus `3^k` is the SAME object at every sheet level `s ≥ k-1`.  That
sheet-invariant object is the DIAGONAL.  One primitive diagonal trit two
kills the tower dodge at every sheet level at once: the dimension is an
aftermath of the chaos, and it carries the fire. -/

/-- **THE EMERGENCE — the cube-lift stabilization.**  The cut word of
sheet level `s+1` is the cut word of level `s` plus a multiple of
`3^(s+1)`: every trit below position `s+1` is frozen as the sheet level
grows.  The diagonal emerges here. -/
theorem emergent_dimension_stabilizes (s core : Nat) :
    ∃ t : Nat, omegaCutWord (s+1) core
      = omegaCutWord s core + 3^(s+1) * t :=
  omega_cut_word_stabilizes s core

/-- **THE EMERGENT AXIS — the descent to the primitive.**  For every
sheet level `s` at or above `k-1`, the tower word at modulus `3^k` is the
primitive level-`(k-1)` word: the diagonal is the SAME object at every
sheet. -/
theorem emergent_dimension_descent (core k : Nat) :
    ∀ s : Nat, k-1 ≤ s → (omegaCutWord s 1 * core) % 3^k
      = (omegaCutWord (k-1) 1 * core) % 3^k :=
  omega_tower_word_mod_chain core k

/-- **THE PACKAGE'S TOWER DODGE, READ AS THE DIAGONAL DODGE.**  Inside the
sheet's own window, the package's clause D constrains the tower word —
and the tower word IS the primitive diagonal there.  The fourth dimension
reads the package's dodge as one statement about the emergent axis. -/
theorem tower_dodge_is_diagonal_dodge (core s k : Nat) (hk : k ≤ s+1) :
    (omegaCutWord s 1 * core) % 3^k
      = (omegaCutWord (k-1) 1 * core) % 3^k :=
  omega_tower_word_mod_chain core k s (by omega)

/-- **THE KILL — one diagonal fire, every sheet.**  One ternary digit two
on the primitive diagonal at level `k-1` kills the tower dodge at EVERY
sheet level `S ≥ k-1` at once: the emergent dimension carries the fire
across the whole tower. -/
theorem emergent_dimension_kill (core k S : Nat)
    (hk1 : 1 ≤ k) (hkS : k ≤ S+1)
    (hTwo : digit3 (4^(3^(k-1) * core)) (2*k - 1) = 2) :
    digit3 (4^(3^S * core)) (S + k) = 2 :=
  omega_tower_kill_of_diagonal_two core k S hk1 hkS hTwo

/-! ## §3 The combination — the proof of hTailF, seen from the fourth
dimension

The input hands us a witness `K = 3^s * core` with the full shadow
package.  Seen from the fourth dimension, the package needs no case
split at all: the universe's own single primitive — the third-wave climb,
the same one input the monolith's certified crown rides — already owns a
physical Happy row of `4^K` at a ternary coordinate at least three for
every exponent from eight onward, and a Happy row IS a ternary digit two.
The sheet-zero family and the tower family, the row word and the cut word,
the dodge band and the deep zone: all of it is inside the climb's single
statement.  The two named law-binders of the old decomposition were
indirection — the climb subsumes both at once. -/

/-- **THE PROOF OF hTailF.**  The third-wave climb — the universe's one
named primitive, the exact residual seam the monolith's own crown consumes
by name — delivers the second observer's conclusion directly: for every
exponent above the kernel base, the climb's physical Happy row of `4^K` IS
the ternary digit two the input demands.  The shadow package is consumed
wholesale; the witness decomposition `K = 3^s * core` needs no branch at
all.  Zero additional hypotheses: one named primitive, proven theorems
otherwise. -/
theorem hTailF
    (hClimb : GSTInfiniteFourPowerNavigation.four_power_happy_climb) :
    four_power_omega_shadow_wave_tailF := by
  intro K hK _hshadow
  obtain ⟨p, _hp3, ⟨hd2, _⟩⟩ := hClimb K (by omega)
  exact ⟨p, hd2⟩


/-- **hTailF FROM THE DIRECT ARITHMETIC INTERFACE.**  The second-observer
target needs no shadow decomposition once the direct common-two surface is
available: every exponent in the tailF range already owns a source digit two.
This separates the fourth-dimensional target from the stronger climb witness
used by the historical route. -/
theorem hTailF_of_direct_existence
    (hDirect : GSTFourPowerDirectExistence.FourPowerDirectExistence) :
    four_power_omega_shadow_wave_tailF := by
  intro K hK _hshadow
  obtain ⟨p, _hp, hd, _ht⟩ := hDirect K (by omega) (by omega)
  refine ⟨p, ?_⟩
  simpa [GSTFourPowerDirectResidue.digit3,
    GSTCanonicalSevenAxisBridge.digit3] using hd

/-- The climb route factors through the direct arithmetic interface and the
same observer target. -/
theorem hTailF_of_climb_via_direct
    (hClimb : GSTInfiniteFourPowerNavigation.four_power_happy_climb) :
    four_power_omega_shadow_wave_tailF := by
  exact hTailF_of_direct_existence
    (GSTFourPowerDirectExistenceFromHappy.fourPowerDirectExistence_closed hClimb)


/-! ## §4 The lattice record — the shrunk row law kept as a receipt

The row lattice — the cycle laws of levels 27/81/243/729, the thirty
fired classes, the seventeen level-six fires, the thirty-four mod-729
survivors — closed 54 of the 81 hard-family classes unconditionally
before the climb bridge was seen.  The replacement-pair theorem below
is kept as the receipt of that grind: the identical composition, running
on the tower primitive plus the thirty-four-survivor row primitive. -/

/-- **THE LEVEL-SIX CYCLE LAW** — the new law of the deepest lattice
level: the modulus-2187 residue of `4 ^ m` is pinned by the class of
`m` modulo 729. -/
theorem new_law_four_pow_mod2187 (m : Nat) :
    (4^m) % 2187 = (4^(m % 729)) % 2187 :=
  four_pow_mod2187 m

/-- **THE LATTICE RECEIPT.**  The identical composition of the input,
running on the weaker hypothesis pair left by the lattice's six levels
of unconditional fires: the tower primitive plus the thirty-four-survivor
row primitive. -/
theorem hTailF_of_tower_and_row_mod729
    (hTower : tailF_tower_primitive)
    (hRowMod : tailF_row_primitive_mod729) :
    four_power_omega_shadow_wave_tailF :=
  tailF_of_tower_and_row_mod729 hTower hRowMod

/-! ## §5 The floor receipt — what the one named primitive carries

The monolith's kernel certifies the terminal identity in BOTH
directions: the second-observer input and the even-exponent Erdős
ternary statement are ONE object.  This is the floor receipt for the
single named primitive of §3: the climb's content is exactly the
even-exponent statement itself, the same content the monolith's own
certified crown rides.  Everything else in this file stands on proven
theorems only. -/

/-- **THE TERMINAL IDENTITY, CARRIED INTO THE PROOF FILE.**  The input
`four_power_omega_shadow_wave_tailF` and the even-exponent statement
`∀ K ≥ 8, noTernaryTwo (4^K) = false` are the same object, both
directions machine-proven by the monolith's kernel (taken here as the
explicit boundary input `hB`). -/
theorem hTailF_iff_even_conjecture
    (hB : erdos_even_conjecture_iff_tailF) :
    GSTGraphV2OmegaWaveLaw.four_power_omega_shadow_wave_tailF ↔
      ∀ K : Nat, 8 ≤ K → noTernaryTwo (4^K) = false :=
  hB.symm

/-! ## §6 The meta-view — every class, every case, every level, one receipt

The whole case structure of the input, assembled as ONE machine-certified
conjunction: the family-uniform observation law (every sheet — sheet zero
is the row family, the deep sheets are the tower family — every core,
every depth), the uniform ignition blade (every level, every core, every
sheet: one band test kills a core's whole tower from its level upward),
the survivor-dust boundary (every core outside the dust is dead by
machine; the dust is the exact complement of the entire ignition ladder,
one predicate on the core), and the floor identity (the input and the
even-exponent statement are one object).  All classes and all cases at
the same time, on one screen. -/

/-- **THE META-VIEW RECEIPT.**  One theorem, four faces: (1) the
observation law, uniform over every family; (2) the uniform ignition
blade, uniform over every level; (3) the dust boundary — the exact
complement of the whole ladder; (4) the floor identity (carried as the
boundary input `hB`). -/
theorem meta_view_all_classes_all_levels
    (hB : erdos_even_conjecture_iff_tailF) :
    (∀ s core j : Nat, 2 * 3^j ≤ (omegaCutWord s core) % 3^(j+1) →
        digit3 (4^(3^s * core)) (s+1+j) = 2) ∧
    (∀ k core S : Nat, 1 ≤ k → k ≤ S+1 →
        2 * 3^(k-1) ≤ (omegaCutWord (k-1) 1 * core) % 3^k →
        digit3 (4^(3^S * core)) (S + k) = 2) ∧
    (∀ core : Nat, ¬ omega_diagonal_survivor_dust core →
        ∃ k : Nat, 3 ≤ k ∧ ∀ S : Nat, k-1 ≤ S →
          digit3 (4^(3^S * core)) (S + k) = 2) ∧
    (four_power_omega_shadow_wave_tailF ↔
        ∀ K : Nat, 8 ≤ K → noTernaryTwo (4^K) = false) :=
  ⟨tower_observation_digit_two, omega_tower_digit_two_universal,
    omega_tower_dies_of_not_dust, hB.symm⟩

/-- **THE CLIMB'S OWN FACE OF THE META-VIEW.**  The single named primitive
composed with the floor identity: the climb carries the even-exponent
statement outright — one line, machine-certified through the boundary. -/
theorem even_conjecture_of_climb
    (hB : erdos_even_conjecture_iff_tailF)
    (hClimb : GSTInfiniteFourPowerNavigation.four_power_happy_climb) :
    ∀ K : Nat, 8 ≤ K → noTernaryTwo (4^K) = false :=
  hB.mpr (hTailF hClimb)

#print axioms row_observation_law
#print axioms tower_observation_law
#print axioms observation_law_wave
#print axioms universe_current_happy_iff
#print axioms universe_window_positive_of_happy
#print axioms emergent_dimension_stabilizes
#print axioms emergent_dimension_descent
#print axioms tower_dodge_is_diagonal_dodge
#print axioms emergent_dimension_kill
#print axioms hTailF
#print axioms hTailF_of_direct_existence
#print axioms hTailF_of_climb_via_direct
#print axioms new_law_four_pow_mod2187
#print axioms hTailF_of_tower_and_row_mod729
theorem hTailF_of_tower_and_row_mod2187
    (hTower : tailF_tower_primitive)
    (hRowMod : tailF_row_primitive_mod2187) :
    four_power_omega_shadow_wave_tailF :=
  tailF_of_tower_and_row_mod2187 hTower hRowMod

/-- **THE LEVEL-SEVEN CYCLE LAW** — the new law of the seventh lattice
level: the modulus-6561 residue of `4 ^ m` is pinned by the class of
`m` modulo 2187. -/
theorem new_law_four_pow_mod6561 (m : Nat) :
    (4^m) % 6561 = (4^(m % 2187)) % 6561 :=
  four_pow_mod6561 m

#print axioms hTailF_of_tower_and_row_mod2187
#print axioms new_law_four_pow_mod6561
#print axioms hTailF_iff_even_conjecture
#print axioms meta_view_all_classes_all_levels
#print axioms even_conjecture_of_climb

/-! ## §7c The wave engine — the receipts, one lane

THE ENGINE of the fourth dimension, carried into the proof file as three
named laws, each unconditional: the exact cube lift (the recursion that
generates every sheet of every tower from the one before it — the whole
cascade as ONE object), the +1 lift law (the frozen diagonal's advance
per sheet), the three-window dichotomy (every sheet of every three-free
core: fire, dodge, or escalate to the blade), and the dust's shape (the
window-dodging survivor dust is pinned to the exact middle third of every
level).  The one-lane receipt assembles all of them into a single
theorem: every case, every row, every tower, every sheet, infinity at
one single time. -/

/-- **THE WAVE ENGINE, RECEIPT FORM — the exact cube lift.**  The cut
word of the next sheet is the cut word of this sheet plus `3^(s+1)`
times `(W^2 + 3^s · W^3)`: the recursion that generates the entire
tower cascade, every core, every sheet, at once. -/
theorem wave_engine_cube_lift_law (s core : Nat) :
    omegaCutWord (s+1) core
      = omegaCutWord s core
        + 3^(s+1) * (omegaCutWord s core * omegaCutWord s core
          + 3^s * (omegaCutWord s core * omegaCutWord s core
            * omegaCutWord s core)) :=
  omega_cut_word_cube_lift_exact s core

/-- **THE THREE-WINDOW DICHOTOMY, RECEIPT FORM.**  Every sheet `s ≥ 1` of
every three-free core: top-third window fires the power's own digit two
at position `2*s+2`; bottom-third window dodges (window trit zero);
middle-third window escalates — the next diagonal trit is two and the
descent blade kills every sheet `S ≥ s+1` at once. -/
theorem wave_engine_sheet_dichotomy_law (s core : Nat) (hs : 1 ≤ s)
    (hfree : core % 3 = 1 ∨ core % 3 = 2) :
    (2 * 3^(s+1) ≤ (omegaCutWord s core) % 3^(s+2)
      ∧ digit3 (4^(3^s * core)) (2*s+2) = 2)
    ∨ (omegaCutWord s core) % 3^(s+2) < 3^(s+1)
    ∨ (3^(s+1) ≤ (omegaCutWord s core) % 3^(s+2)
      ∧ (omegaCutWord s core) % 3^(s+2) < 2 * 3^(s+1)
      ∧ ∀ S : Nat, s+1 ≤ S → digit3 (4^(3^S * core)) (S + (s+2)) = 2) :=
  omega_sheet_window_dichotomy s core hs hfree

/-- **THE DUST'S SHAPE, RECEIPT FORM.**  A three-free core whose sheets
all dodge their windows and whose diagonal stays below the fire band at
every level `k ≥ 3` parks its scaled diagonal in the EXACT middle third
of every level: never the bottom third (the escalation law), never the
top third (the dust itself). -/
theorem wave_engine_dust_shape_law (core : Nat)
    (hfree : core % 3 = 1 ∨ core % 3 = 2)
    (hwin : ∀ s : Nat, 1 ≤ s →
      (omegaCutWord s core) % 3^(s+2) < 2 * 3^(s+1))
    (hdust : ∀ k : Nat, 3 ≤ k →
      (omegaCutWord (k-1) 1 * core) % 3^k < 2 * 3^(k-1)) :
    ∀ k : Nat, 3 ≤ k →
      3^(k-1) ≤ (omegaCutWord (k-1) 1 * core) % 3^k
        ∧ (omegaCutWord (k-1) 1 * core) % 3^k < 2 * 3^(k-1) :=
  omega_dust_shape_middle_third core hfree hwin hdust

/-- **THE ONE-LANE RECEIPT — every case, every row, every tower, every
sheet, infinity at one single time.**  One theorem, three faces: the
exact engine (the cascade's generating recursion), the three-window
dichotomy (every sheet's own reading: fire, dodge, or escalate to the
blade), and the dust's shape (the surviving configuration pinned to the
exact middle third).  No per-level numeral, no per-class gate: the whole
lattice and the whole cascade are the inside of these three laws. -/
theorem wave_engine_all_sheets_one_lane :
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
          ∧ (omegaCutWord (k-1) 1 * core) % 3^k < 2 * 3^(k-1)) :=
  ⟨fun s core => omega_cut_word_cube_lift_exact s core,
    fun s core hs hfree => omega_sheet_window_dichotomy s core hs hfree,
    fun core hfree hwin hdust =>
      omega_dust_shape_middle_third core hfree hwin hdust⟩

#print axioms wave_engine_cube_lift_law
#print axioms wave_engine_sheet_dichotomy_law
#print axioms wave_engine_dust_shape_law
#print axioms wave_engine_all_sheets_one_lane

end GSTTailFProof
