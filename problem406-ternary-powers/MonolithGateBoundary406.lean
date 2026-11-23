import MonolithGate.ErdosTernary2
import MonolithGate.GSTTailFProof

/-!
# THE HYPOTHESIS DISCHARGED — BOSS'S OWN MONOLITH, VENDORED (S085 r9)

The campaign hypothesis `erdos_even_conjecture_iff_tailF` — the terminal
identity of Erdős Problem #406, named in THE_CORE §17 as the remaining
input of the conditional crown — is NOT an open object of BOSS's
mathematics: it is a THEOREM of BOSS's own monolith
(`kyo-oo/erdosternary2`, branch `sol/kyo-gate-universe-wire`, head
`cb29501`, §7.15, `ErdosTernary2.lean:18425`), kernel-certified in BOTH
directions with axiom profile `[propext, choice, Quot.sound]` (the
monolith's own `#print axioms` receipt at its line 18525, vendored along
with it).

This kernel vendors that proof: `MonolithGate/` = the 88-file world of
the monolith (the 84-file `ErdosTernary2` import closure + the 4-file
tailF proof chamber: `GSTTailFProof`, `GSTTailFFourthDimension`,
`GSTGraphV2Ontological`, `GSTGraphV2PowerThreeWaveObservation`), verbatim,
190 import rewrites, at the exact campaign toolchain pin (the monolith's
own pin: Lean v4.33.0-rc2 + Mathlib v4.33.0-rc2 — identical to the
campaign's).

THE CO-IMPORT LAW: the `MonolithGate` world and the `Monolith`/HC-PROOF
world share declaration names in the same namespaces (the two branches
diverged; e.g. both declare root `erdos_even_conjecture_iff_tailF` and
`GSTGraphV2OmegaWaveLaw.four_power_omega_shadow_wave_tailF`). NEVER
import a `MonolithGate.*` module and a `Monolith.*` module into the same
file. This kernel imports `MonolithGate` modules ONLY.

## What this kernel delivers

1. **THE HYPOTHESIS, DISCHARGED** — `erdos_even_conjecture_iff_tailF`
   as a theorem of the campaign build, BOSS's own proof, both
   directions.
2. **THE CROWN CHAIN** — every downstream theorem of the monolith that
   consumed the identity or the tailF input, cited by name: the
   universal theorem, the conjecture reading, the composition theorems.
3. **THE HONEST SEAM, NAMED BY THE MONOLITH ITSELF** — the monolith's
   own declared remaining input: the third-wave climb
   (`GSTInfiniteFourPowerNavigation.four_power_happy_climb`), and the
   row + tower decomposition
   (`GSTTailFFourthDimension.tailF_row_primitive` +
   `GSTTailFFourthDimension.tailF_tower_primitive` composed by
   `GSTTailFFourthDimension.tailF_of_row_and_tower`). The campaign's own
   406 chamber (PiCollapse406 / PiCollapse406Pins / GhostExtinction406 /
   TailFDecomposition406, COMPLETE_PROOF.md §§10–15) is the independent
   self-contained assault on exactly that seam.
-/

namespace MonolithGateBoundary406

/-! ## §1 THE HYPOTHESIS, DISCHARGED -/

/-- **THE TERMINAL IDENTITY — THE CAMPAIGN HYPOTHESIS DISCHARGED.**
The second-observer input and the even-exponent Erdős ternary statement
are one object, BOTH directions, by BOSS's own monolith theorem
(`ErdosTernary2.lean:18425`, vendored verbatim as
`MonolithGate.ErdosTernary2`). Zero hypotheses: this is the identity
itself, unconditional. -/
theorem erdos_even_conjecture_iff_tailF :
    (∀ K : Nat, 8 ≤ K → noTernaryTwo (4^K) = false)
      ↔ GSTGraphV2OmegaWaveLaw.four_power_omega_shadow_wave_tailF :=
  _root_.erdos_even_conjecture_iff_tailF

/-! ## §2 THE CROWN CHAIN — the monolith's certified consumers, by name -/

/-- **THE CROWN.** Every `2^n` from nine onward owns its ternary digit
two, from the second-observer input — BOSS's monolith theorem
(`ErdosTernary2.lean:18344`), cited by name. -/
theorem erdos_ternary_2_universal_of_tailF
    (hTailF : GSTGraphV2OmegaWaveLaw.four_power_omega_shadow_wave_tailF)
    (n : Nat) (hn : 9 ≤ n) :
    noTernaryTwo (2^n) = false :=
  _root_.erdos_ternary_2_universal_of_tailF hTailF n hn

/-- **THE CONJECTURE READING.** The identity's forward face as a
theorem: the tailF input hands the even-exponent statement outright
(`ErdosTernary2.lean:18452`). -/
theorem erdos_even_conjecture_of_tailF
    (hTailF : GSTGraphV2OmegaWaveLaw.four_power_omega_shadow_wave_tailF) :
    ∀ K : Nat, 8 ≤ K → noTernaryTwo (4^K) = false :=
  _root_.erdos_even_conjecture_of_tailF hTailF

/-! ## §3 THE SEAM, NAMED — the monolith's own composition theorems -/

/-- **THE ROW + TOWER COMPOSITION.** The two named 3-adic trit
primitives — the sheet-zero row fire and the deep-tail tower fire —
deliver the second-observer input outright
(`GSTTailFFourthDimension.lean`, the decomposition theorem). This is
the composition the campaign mission board pinned as the remaining
mathematical content. -/
theorem tailF_of_row_and_tower
    (hRow : GSTTailFFourthDimension.tailF_row_primitive)
    (hTower : GSTTailFFourthDimension.tailF_tower_primitive) :
    GSTGraphV2OmegaWaveLaw.four_power_omega_shadow_wave_tailF :=
  GSTTailFFourthDimension.tailF_of_row_and_tower hRow hTower

/-- **THE CLIMB COMPOSITION.** The monolith's single named primitive —
the third-wave climb, every exponent from eight onward owning a physical
Happy row at a ternary coordinate at least three — delivers the input
outright (`GSTTailFProof.lean` §3, "the proof visible in one screen"):
the row and tower law-binders were indirection; the climb subsumes both. -/
theorem hTailF_of_climb
    (hClimb : GSTInfiniteFourPowerNavigation.four_power_happy_climb) :
    GSTGraphV2OmegaWaveLaw.four_power_omega_shadow_wave_tailF :=
  GSTTailFProof.hTailF hClimb

/-! ## §4 THE FULL CHAINS — every face of the crown, composed -/

/-- **THE FULL CHAIN, CLIMB FACE.** Climb → tailF → the universal
theorem: one theorem, every vendored link, Erdős #406's target as the
conclusion, the monolith's named seam as the single input. -/
theorem erdos_ternary_2_universal_of_climb
    (hClimb : GSTInfiniteFourPowerNavigation.four_power_happy_climb)
    (n : Nat) (hn : 9 ≤ n) :
    noTernaryTwo (2^n) = false :=
  erdos_ternary_2_universal_of_tailF (hTailF_of_climb hClimb) n hn

/-- **THE FULL CHAIN, ROW + TOWER FACE.** The two named primitives →
the input → the universal theorem. -/
theorem erdos_ternary_2_universal_of_row_and_tower
    (hRow : GSTTailFFourthDimension.tailF_row_primitive)
    (hTower : GSTTailFFourthDimension.tailF_tower_primitive)
    (n : Nat) (hn : 9 ≤ n) :
    noTernaryTwo (2^n) = false :=
  erdos_ternary_2_universal_of_tailF (tailF_of_row_and_tower hRow hTower) n hn

/-! ## §5 Receipts — the discharge and every composition face -/

#print axioms erdos_even_conjecture_iff_tailF
#print axioms erdos_ternary_2_universal_of_tailF
#print axioms erdos_even_conjecture_of_tailF
#print axioms tailF_of_row_and_tower
#print axioms hTailF_of_climb
#print axioms erdos_ternary_2_universal_of_climb
#print axioms erdos_ternary_2_universal_of_row_and_tower
#print axioms GSTTailFProof.hTailF
#print axioms GSTTailFFourthDimension.tailF_of_row_and_tower
#print axioms GSTInfiniteFourPowerNavigation.four_power_happy_climb

#eval "ERDOS406_MONOLITHGATE_HYPOTHESIS_DISCHARGED"

end MonolithGateBoundary406
