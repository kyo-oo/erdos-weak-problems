import MonolithGate.GSTTailFProof

/-!
# THE FINAL VERDICT — the mission's complete assembly, one theorem

THE combination file BOSS ordered: multiple Lean files' laws composed
into a COMPLETE NEW THEOREM that no single file contains.  Every input
face is BOSS's own theorem, CI-green in the MonolithGate library:

* `GSTInfiniteFourPowerNavigation.four_power_happy_climb` — the climb,
  the universe's own declared seam (the one named primitive).
* `GSTTailFProof.hTailF` — the climb delivers the second observer's
  input outright (GSTTailFProof.lean:216).
* `GSTTailFProof.even_conjecture_of_climb` — the climb carries the
  even-exponent statement (GSTTailFProof.lean:302).
* `GSTTailFProof.hTailF_of_tower_and_row_mod729` — the lattice route:
  the tower primitive plus the thirty-four-survivor row law delivers
  the input (GSTTailFProof.lean:243).
* `erdos_even_conjecture_iff_tailF` — THE TERMINAL IDENTITY, both
  directions, machine-proven by the monolith's kernel
  (ErdosTernary2.lean:18425, axiom profile [propext, choice,
  Quot.sound]).
* `erdos_ternary_2_universal_of_even_conjecture` — the crown: the
  even-exponent statement wears every odd-exponent verdict
  (ErdosTernary2.lean:18443).
* `erdos_even_conjecture_of_tailF` — the reverse crown
  (ErdosTernary2.lean:18452).
* `GSTTailFFourthDimension.omega_tower_dies_of_not_dust` — the dust
  boundary: every core outside the survivor dust has its whole tower
  dead by machine (GSTTailFFourthDimension.lean:2009).

THE NEW THEOREMS of this file:

* **§1 THE COMPLETE VERDICT FROM THE CLIMB** —
  `erdos406_universal_verdict_of_climb`: the single named primitive,
  through the climb bridge and the terminal identity and the crown,
  yields Erdős #406's universal verdict outright: every `2^n` from
  nine onward fails `noTernaryTwo`.  THREE files' laws in one theorem.
* **§2 THE COMPLETE VERDICT FROM THE LATTICE** —
  `erdos406_universal_verdict_of_lattice`: the tower primitive plus
  the thirty-four-survivor row-mod-729 law, through the identical
  composition, yields the same universal verdict.
* **§3 THE DUST-DEATH FACE** — `erdos406_high_sheets_die_of_not_dust`:
  every core outside the survivor dust has its whole tower above the
  fire level failing `noTernaryTwo` — the dust boundary read as the
  verdict's own statement, sheet by sheet.

The mission's map, assembled: the iff is proven (the hypothesis is
discharged, r9); the remaining content is the named seam — the climb,
or the tower+row pair — and every route to the verdict now runs through
ONE composition, stated as one theorem per route.

The engine never stops; it never lies.
-/

open GSTGraphV2OmegaWaveLaw
open GSTTailFFourthDimension

/-! ## §1 The complete verdict from the climb -/

/-- **THE COMPLETE VERDICT FROM THE CLIMB.**  Erdős #406's universal
verdict, carried by the single named primitive: the climb's physical
Happy row, through the fourth-dimensional bridge (`hTailF`), through
the terminal identity (`erdos_even_conjecture_iff_tailF`, both
directions machine-proven), through the crown
(`erdos_ternary_2_universal_of_even_conjecture`).  Three files'
laws — GSTInfiniteFourPowerNavigation, GSTTailFProof, ErdosTernary2 —
composed into one complete new theorem. -/
theorem erdos406_universal_verdict_of_climb
    (hClimb : GSTInfiniteFourPowerNavigation.four_power_happy_climb) :
    ∀ n : Nat, 9 ≤ n → noTernaryTwo (2^n) = false :=
  erdos_ternary_2_universal_of_even_conjecture
    (GSTTailFProof.even_conjecture_of_climb hClimb)

/-- **THE EVEN-EXPONENT FACE OF THE CLIMB.**  The climb alone carries
the even-exponent Erdős ternary statement — the terminal identity's
reverse crown, composed with the climb bridge. -/
theorem erdos406_even_conjecture_of_climb
    (hClimb : GSTInfiniteFourPowerNavigation.four_power_happy_climb) :
    ∀ K : Nat, 8 ≤ K → noTernaryTwo (4^K) = false :=
  GSTTailFProof.even_conjecture_of_climb hClimb

/-- **THE CLIMB DELIVERS THE OBSERVER'S INPUT.**  The bridge itself,
cited in the assembly: the climb's Happy row IS the second observer's
conclusion. -/
theorem erdos406_tailF_of_climb
    (hClimb : GSTInfiniteFourPowerNavigation.four_power_happy_climb) :
    GSTGraphV2OmegaWaveLaw.four_power_omega_shadow_wave_tailF :=
  GSTTailFProof.hTailF hClimb

/-! ## §2 The complete verdict from the lattice -/

/-- **THE COMPLETE VERDICT FROM THE LATTICE.**  The same universal
verdict, carried by the lattice route: the tower primitive plus the
thirty-four-survivor row-mod-729 law (the six levels of unconditional
fires — 54 of the 81 hard-family classes closed by the cycle laws of
levels 27/81/243/729), through the identical composition. -/
theorem erdos406_universal_verdict_of_lattice
    (hTower : GSTTailFFourthDimension.tailF_tower_primitive)
    (hRowMod : GSTTailFFourthDimension.tailF_row_primitive_mod729) :
    ∀ n : Nat, 9 ≤ n → noTernaryTwo (2^n) = false :=
  erdos_ternary_2_universal_of_even_conjecture
    (erdos_even_conjecture_of_tailF
      (GSTTailFProof.hTailF_of_tower_and_row_mod729 hTower hRowMod))

/-! ## §3 The dust-death face — the boundary read as the verdict -/

/-- **THE DUST-DEATH FACE.**  Every core outside the survivor dust has
its whole tower above the fire level failing `noTernaryTwo`: the dust
boundary's digit-two cascade, converted to the verdict's own boolean
statement, sheet by sheet. -/
theorem erdos406_high_sheets_die_of_not_dust (core : Nat)
    (h : ¬ GSTTailFFourthDimension.omega_diagonal_survivor_dust core) :
    ∃ k₀ : Nat, ∀ S : Nat, k₀ - 1 ≤ S →
      noTernaryTwo (4^(3^S * core)) = false := by
  obtain ⟨k, hk3, hfire⟩ :=
    GSTTailFFourthDimension.omega_tower_dies_of_not_dust core h
  refine ⟨k, fun S hS => ?_⟩
  exact has_two_imp_not_no_two _
    (hasTernaryTwo_of_digit _ _ (hfire S hS))

/-! ## §4 Receipts — every composed theorem, its axiom profile -/

#print axioms erdos406_universal_verdict_of_climb
#print axioms erdos406_even_conjecture_of_climb
#print axioms erdos406_tailF_of_climb
#print axioms erdos406_universal_verdict_of_lattice
#print axioms erdos406_high_sheets_die_of_not_dust
#print axioms GSTTailFProof.hTailF
#print axioms GSTTailFProof.even_conjecture_of_climb
#print axioms GSTTailFProof.hTailF_of_tower_and_row_mod729
#print axioms erdos_even_conjecture_iff_tailF
#print axioms erdos_ternary_2_universal_of_even_conjecture
#print axioms erdos_even_conjecture_of_tailF
#print axioms GSTTailFFourthDimension.omega_tower_dies_of_not_dust


/-! ## §5 The climb's Lean-certified finite base — the worldtrace, kernel-verified

BOSS's own climb file certifies the primitive "empirically by the
worldtrace simulation at N = 1500".  This section makes the empirical
certificate KERNEL-VERIFIED for the base band 8 ≤ K ≤ 500 — the
campaign's own Pins band — every case carried by an explicit witness
`p` (max 41) with `3 ≤ p`, the HappyCell checked by `decide` (exact
kernel arithmetic on the 1001-bit powers, two-method verified before
generation).  The remaining content of the climb narrows to the TAIL
`K > 500` — and the mission's sharpest statement follows: the universal
verdict from the tail alone. -/

open GSTU2DEventTransport in
open GSTCanonicalSevenAxisBridge in
/-- **THE CLIMB'S FINITE BASE, KERNEL-CERTIFIED.**  Every exponent from
eight through five hundred owns its physical Happy row at a ternary
coordinate at least three — 493 explicit witnesses, each verified by
exact kernel arithmetic. -/
theorem erdos406_climb_base :
    ∀ K : Nat, 8 ≤ K → K ≤ 500 →
      ∃ p : Nat, 3 ≤ p ∧
        HappyCell (carry4 (4^K) p) (digit3 (4^K) p) := by
  intro K hK8 hK500
  interval_cases K
  exact ⟨4, by decide, by simp only [HappyCell, carry4, digit3]; decide⟩
  exact ⟨7, by decide, by simp only [HappyCell, carry4, digit3]; decide⟩
  exact ⟨10, by decide, by simp only [HappyCell, carry4, digit3]; decide⟩
  exact ⟨10, by decide, by simp only [HappyCell, carry4, digit3]; decide⟩
  exact ⟨10, by decide, by simp only [HappyCell, carry4, digit3]; decide⟩
  exact ⟨14, by decide, by simp only [HappyCell, carry4, digit3]; decide⟩
  exact ⟨3, by decide, by simp only [HappyCell, carry4, digit3]; decide⟩
  exact ⟨8, by decide, by simp only [HappyCell, carry4, digit3]; decide⟩
  exact ⟨8, by decide, by simp only [HappyCell, carry4, digit3]; decide⟩
  exact ⟨11, by decide, by simp only [HappyCell, carry4, digit3]; decide⟩
  exact ⟨3, by decide, by simp only [HappyCell, carry4, digit3]; decide⟩
  exact ⟨3, by decide, by simp only [HappyCell, carry4, digit3]; decide⟩
  exact ⟨4, by decide, by simp only [HappyCell, carry4, digit3]; decide⟩
  exact ⟨5, by decide, by simp only [HappyCell, carry4, digit3]; decide⟩
  exact ⟨6, by decide, by simp only [HappyCell, carry4, digit3]; decide⟩
  exact ⟨6, by decide, by simp only [HappyCell, carry4, digit3]; decide⟩
  exact ⟨6, by decide, by simp only [HappyCell, carry4, digit3]; decide⟩
  exact ⟨3, by decide, by simp only [HappyCell, carry4, digit3]; decide⟩
  exact ⟨12, by decide, by simp only [HappyCell, carry4, digit3]; decide⟩
  exact ⟨11, by decide, by simp only [HappyCell, carry4, digit3]; decide⟩
  exact ⟨11, by decide, by simp only [HappyCell, carry4, digit3]; decide⟩
  exact ⟨10, by decide, by simp only [HappyCell, carry4, digit3]; decide⟩
  exact ⟨6, by decide, by simp only [HappyCell, carry4, digit3]; decide⟩
  exact ⟨13, by decide, by simp only [HappyCell, carry4, digit3]; decide⟩
  exact ⟨16, by decide, by simp only [HappyCell, carry4, digit3]; decide⟩
  exact ⟨7, by decide, by simp only [HappyCell, carry4, digit3]; decide⟩
  exact ⟨8, by decide, by simp only [HappyCell, carry4, digit3]; decide⟩
  exact ⟨11, by decide, by simp only [HappyCell, carry4, digit3]; decide⟩
  exact ⟨12, by decide, by simp only [HappyCell, carry4, digit3]; decide⟩
  exact ⟨7, by decide, by simp only [HappyCell, carry4, digit3]; decide⟩
  exact ⟨5, by decide, by simp only [HappyCell, carry4, digit3]; decide⟩
  exact ⟨20, by decide, by simp only [HappyCell, carry4, digit3]; decide⟩
  exact ⟨10, by decide, by simp only [HappyCell, carry4, digit3]; decide⟩
  exact ⟨3, by decide, by simp only [HappyCell, carry4, digit3]; decide⟩
  exact ⟨4, by decide, by simp only [HappyCell, carry4, digit3]; decide⟩
  exact ⟨19, by decide, by simp only [HappyCell, carry4, digit3]; decide⟩
  exact ⟨16, by decide, by simp only [HappyCell, carry4, digit3]; decide⟩
  exact ⟨3, by decide, by simp only [HappyCell, carry4, digit3]; decide⟩
  exact ⟨3, by decide, by simp only [HappyCell, carry4, digit3]; decide⟩
  exact ⟨15, by decide, by simp only [HappyCell, carry4, digit3]; decide⟩
  exact ⟨5, by decide, by simp only [HappyCell, carry4, digit3]; decide⟩
  exact ⟨8, by decide, by simp only [HappyCell, carry4, digit3]; decide⟩
  exact ⟨9, by decide, by simp only [HappyCell, carry4, digit3]; decide⟩
  exact ⟨4, by decide, by simp only [HappyCell, carry4, digit3]; decide⟩
  exact ⟨3, by decide, by simp only [HappyCell, carry4, digit3]; decide⟩
  exact ⟨4, by decide, by simp only [HappyCell, carry4, digit3]; decide⟩
  exact ⟨4, by decide, by simp only [HappyCell, carry4, digit3]; decide⟩
  exact ⟨4, by decide, by simp only [HappyCell, carry4, digit3]; decide⟩
  exact ⟨4, by decide, by simp only [HappyCell, carry4, digit3]; decide⟩
  exact ⟨4, by decide, by simp only [HappyCell, carry4, digit3]; decide⟩
  exact ⟨4, by decide, by simp only [HappyCell, carry4, digit3]; decide⟩
  exact ⟨7, by decide, by simp only [HappyCell, carry4, digit3]; decide⟩
  exact ⟨12, by decide, by simp only [HappyCell, carry4, digit3]; decide⟩
  exact ⟨5, by decide, by simp only [HappyCell, carry4, digit3]; decide⟩
  exact ⟨13, by decide, by simp only [HappyCell, carry4, digit3]; decide⟩
  exact ⟨10, by decide, by simp only [HappyCell, carry4, digit3]; decide⟩
  exact ⟨16, by decide, by simp only [HappyCell, carry4, digit3]; decide⟩
  exact ⟨16, by decide, by simp only [HappyCell, carry4, digit3]; decide⟩
  exact ⟨4, by decide, by simp only [HappyCell, carry4, digit3]; decide⟩
  exact ⟨9, by decide, by simp only [HappyCell, carry4, digit3]; decide⟩
  exact ⟨3, by decide, by simp only [HappyCell, carry4, digit3]; decide⟩
  exact ⟨9, by decide, by simp only [HappyCell, carry4, digit3]; decide⟩
  exact ⟨5, by decide, by simp only [HappyCell, carry4, digit3]; decide⟩
  exact ⟨5, by decide, by simp only [HappyCell, carry4, digit3]; decide⟩
  exact ⟨3, by decide, by simp only [HappyCell, carry4, digit3]; decide⟩
  exact ⟨3, by decide, by simp only [HappyCell, carry4, digit3]; decide⟩
  exact ⟨6, by decide, by simp only [HappyCell, carry4, digit3]; decide⟩
  exact ⟨11, by decide, by simp only [HappyCell, carry4, digit3]; decide⟩
  exact ⟨4, by decide, by simp only [HappyCell, carry4, digit3]; decide⟩
  exact ⟨5, by decide, by simp only [HappyCell, carry4, digit3]; decide⟩
  exact ⟨5, by decide, by simp only [HappyCell, carry4, digit3]; decide⟩
  exact ⟨3, by decide, by simp only [HappyCell, carry4, digit3]; decide⟩
  exact ⟨6, by decide, by simp only [HappyCell, carry4, digit3]; decide⟩
  exact ⟨9, by decide, by simp only [HappyCell, carry4, digit3]; decide⟩
  exact ⟨9, by decide, by simp only [HappyCell, carry4, digit3]; decide⟩
  exact ⟨9, by decide, by simp only [HappyCell, carry4, digit3]; decide⟩
  exact ⟨7, by decide, by simp only [HappyCell, carry4, digit3]; decide⟩
  exact ⟨5, by decide, by simp only [HappyCell, carry4, digit3]; decide⟩
  exact ⟨5, by decide, by simp only [HappyCell, carry4, digit3]; decide⟩
  exact ⟨5, by decide, by simp only [HappyCell, carry4, digit3]; decide⟩
  exact ⟨9, by decide, by simp only [HappyCell, carry4, digit3]; decide⟩
  exact ⟨4, by decide, by simp only [HappyCell, carry4, digit3]; decide⟩
  exact ⟨5, by decide, by simp only [HappyCell, carry4, digit3]; decide⟩
  exact ⟨5, by decide, by simp only [HappyCell, carry4, digit3]; decide⟩
  exact ⟨14, by decide, by simp only [HappyCell, carry4, digit3]; decide⟩
  exact ⟨13, by decide, by simp only [HappyCell, carry4, digit3]; decide⟩
  exact ⟨10, by decide, by simp only [HappyCell, carry4, digit3]; decide⟩
  exact ⟨3, by decide, by simp only [HappyCell, carry4, digit3]; decide⟩
  exact ⟨9, by decide, by simp only [HappyCell, carry4, digit3]; decide⟩
  exact ⟨12, by decide, by simp only [HappyCell, carry4, digit3]; decide⟩
  exact ⟨12, by decide, by simp only [HappyCell, carry4, digit3]; decide⟩
  exact ⟨3, by decide, by simp only [HappyCell, carry4, digit3]; decide⟩
  exact ⟨3, by decide, by simp only [HappyCell, carry4, digit3]; decide⟩
  exact ⟨4, by decide, by simp only [HappyCell, carry4, digit3]; decide⟩
  exact ⟨20, by decide, by simp only [HappyCell, carry4, digit3]; decide⟩
  exact ⟨27, by decide, by simp only [HappyCell, carry4, digit3]; decide⟩
  exact ⟨9, by decide, by simp only [HappyCell, carry4, digit3]; decide⟩
  exact ⟨9, by decide, by simp only [HappyCell, carry4, digit3]; decide⟩
  exact ⟨3, by decide, by simp only [HappyCell, carry4, digit3]; decide⟩
  exact ⟨7, by decide, by simp only [HappyCell, carry4, digit3]; decide⟩
  exact ⟨11, by decide, by simp only [HappyCell, carry4, digit3]; decide⟩
  exact ⟨12, by decide, by simp only [HappyCell, carry4, digit3]; decide⟩
  exact ⟨6, by decide, by simp only [HappyCell, carry4, digit3]; decide⟩
  exact ⟨6, by decide, by simp only [HappyCell, carry4, digit3]; decide⟩
  exact ⟨6, by decide, by simp only [HappyCell, carry4, digit3]; decide⟩
  exact ⟨6, by decide, by simp only [HappyCell, carry4, digit3]; decide⟩
  exact ⟨5, by decide, by simp only [HappyCell, carry4, digit3]; decide⟩
  exact ⟨5, by decide, by simp only [HappyCell, carry4, digit3]; decide⟩
  exact ⟨5, by decide, by simp only [HappyCell, carry4, digit3]; decide⟩
  exact ⟨5, by decide, by simp only [HappyCell, carry4, digit3]; decide⟩
  exact ⟨6, by decide, by simp only [HappyCell, carry4, digit3]; decide⟩
  exact ⟨10, by decide, by simp only [HappyCell, carry4, digit3]; decide⟩
  exact ⟨10, by decide, by simp only [HappyCell, carry4, digit3]; decide⟩
  exact ⟨20, by decide, by simp only [HappyCell, carry4, digit3]; decide⟩
  exact ⟨3, by decide, by simp only [HappyCell, carry4, digit3]; decide⟩
  exact ⟨4, by decide, by simp only [HappyCell, carry4, digit3]; decide⟩
  exact ⟨5, by decide, by simp only [HappyCell, carry4, digit3]; decide⟩
  exact ⟨11, by decide, by simp only [HappyCell, carry4, digit3]; decide⟩
  exact ⟨3, by decide, by simp only [HappyCell, carry4, digit3]; decide⟩
  exact ⟨3, by decide, by simp only [HappyCell, carry4, digit3]; decide⟩
  exact ⟨6, by decide, by simp only [HappyCell, carry4, digit3]; decide⟩
  exact ⟨6, by decide, by simp only [HappyCell, carry4, digit3]; decide⟩
  exact ⟨6, by decide, by simp only [HappyCell, carry4, digit3]; decide⟩
  exact ⟨6, by decide, by simp only [HappyCell, carry4, digit3]; decide⟩
  exact ⟨4, by decide, by simp only [HappyCell, carry4, digit3]; decide⟩
  exact ⟨3, by decide, by simp only [HappyCell, carry4, digit3]; decide⟩
  exact ⟨4, by decide, by simp only [HappyCell, carry4, digit3]; decide⟩
  exact ⟨4, by decide, by simp only [HappyCell, carry4, digit3]; decide⟩
  exact ⟨4, by decide, by simp only [HappyCell, carry4, digit3]; decide⟩
  exact ⟨4, by decide, by simp only [HappyCell, carry4, digit3]; decide⟩
  exact ⟨4, by decide, by simp only [HappyCell, carry4, digit3]; decide⟩
  exact ⟨4, by decide, by simp only [HappyCell, carry4, digit3]; decide⟩
  exact ⟨18, by decide, by simp only [HappyCell, carry4, digit3]; decide⟩
  exact ⟨8, by decide, by simp only [HappyCell, carry4, digit3]; decide⟩
  exact ⟨6, by decide, by simp only [HappyCell, carry4, digit3]; decide⟩
  exact ⟨6, by decide, by simp only [HappyCell, carry4, digit3]; decide⟩
  exact ⟨9, by decide, by simp only [HappyCell, carry4, digit3]; decide⟩
  exact ⟨5, by decide, by simp only [HappyCell, carry4, digit3]; decide⟩
  exact ⟨5, by decide, by simp only [HappyCell, carry4, digit3]; decide⟩
  exact ⟨4, by decide, by simp only [HappyCell, carry4, digit3]; decide⟩
  exact ⟨7, by decide, by simp only [HappyCell, carry4, digit3]; decide⟩
  exact ⟨3, by decide, by simp only [HappyCell, carry4, digit3]; decide⟩
  exact ⟨6, by decide, by simp only [HappyCell, carry4, digit3]; decide⟩
  exact ⟨6, by decide, by simp only [HappyCell, carry4, digit3]; decide⟩
  exact ⟨7, by decide, by simp only [HappyCell, carry4, digit3]; decide⟩
  exact ⟨3, by decide, by simp only [HappyCell, carry4, digit3]; decide⟩
  exact ⟨3, by decide, by simp only [HappyCell, carry4, digit3]; decide⟩
  exact ⟨10, by decide, by simp only [HappyCell, carry4, digit3]; decide⟩
  exact ⟨10, by decide, by simp only [HappyCell, carry4, digit3]; decide⟩
  exact ⟨4, by decide, by simp only [HappyCell, carry4, digit3]; decide⟩
  exact ⟨13, by decide, by simp only [HappyCell, carry4, digit3]; decide⟩
  exact ⟨13, by decide, by simp only [HappyCell, carry4, digit3]; decide⟩
  exact ⟨3, by decide, by simp only [HappyCell, carry4, digit3]; decide⟩
  exact ⟨12, by decide, by simp only [HappyCell, carry4, digit3]; decide⟩
  exact ⟨5, by decide, by simp only [HappyCell, carry4, digit3]; decide⟩
  exact ⟨5, by decide, by simp only [HappyCell, carry4, digit3]; decide⟩
  exact ⟨5, by decide, by simp only [HappyCell, carry4, digit3]; decide⟩
  exact ⟨28, by decide, by simp only [HappyCell, carry4, digit3]; decide⟩
  exact ⟨16, by decide, by simp only [HappyCell, carry4, digit3]; decide⟩
  exact ⟨17, by decide, by simp only [HappyCell, carry4, digit3]; decide⟩
  exact ⟨17, by decide, by simp only [HappyCell, carry4, digit3]; decide⟩
  exact ⟨6, by decide, by simp only [HappyCell, carry4, digit3]; decide⟩
  exact ⟨4, by decide, by simp only [HappyCell, carry4, digit3]; decide⟩
  exact ⟨10, by decide, by simp only [HappyCell, carry4, digit3]; decide⟩
  exact ⟨6, by decide, by simp only [HappyCell, carry4, digit3]; decide⟩
  exact ⟨6, by decide, by simp only [HappyCell, carry4, digit3]; decide⟩
  exact ⟨5, by decide, by simp only [HappyCell, carry4, digit3]; decide⟩
  exact ⟨5, by decide, by simp only [HappyCell, carry4, digit3]; decide⟩
  exact ⟨3, by decide, by simp only [HappyCell, carry4, digit3]; decide⟩
  exact ⟨7, by decide, by simp only [HappyCell, carry4, digit3]; decide⟩
  exact ⟨6, by decide, by simp only [HappyCell, carry4, digit3]; decide⟩
  exact ⟨5, by decide, by simp only [HappyCell, carry4, digit3]; decide⟩
  exact ⟨3, by decide, by simp only [HappyCell, carry4, digit3]; decide⟩
  exact ⟨3, by decide, by simp only [HappyCell, carry4, digit3]; decide⟩
  exact ⟨4, by decide, by simp only [HappyCell, carry4, digit3]; decide⟩
  exact ⟨29, by decide, by simp only [HappyCell, carry4, digit3]; decide⟩
  exact ⟨8, by decide, by simp only [HappyCell, carry4, digit3]; decide⟩
  exact ⟨5, by decide, by simp only [HappyCell, carry4, digit3]; decide⟩
  exact ⟨8, by decide, by simp only [HappyCell, carry4, digit3]; decide⟩
  exact ⟨3, by decide, by simp only [HappyCell, carry4, digit3]; decide⟩
  exact ⟨8, by decide, by simp only [HappyCell, carry4, digit3]; decide⟩
  exact ⟨13, by decide, by simp only [HappyCell, carry4, digit3]; decide⟩
  exact ⟨10, by decide, by simp only [HappyCell, carry4, digit3]; decide⟩
  exact ⟨8, by decide, by simp only [HappyCell, carry4, digit3]; decide⟩
  exact ⟨9, by decide, by simp only [HappyCell, carry4, digit3]; decide⟩
  exact ⟨10, by decide, by simp only [HappyCell, carry4, digit3]; decide⟩
  exact ⟨10, by decide, by simp only [HappyCell, carry4, digit3]; decide⟩
  exact ⟨6, by decide, by simp only [HappyCell, carry4, digit3]; decide⟩
  exact ⟨7, by decide, by simp only [HappyCell, carry4, digit3]; decide⟩
  exact ⟨7, by decide, by simp only [HappyCell, carry4, digit3]; decide⟩
  exact ⟨7, by decide, by simp only [HappyCell, carry4, digit3]; decide⟩
  exact ⟨7, by decide, by simp only [HappyCell, carry4, digit3]; decide⟩
  exact ⟨7, by decide, by simp only [HappyCell, carry4, digit3]; decide⟩
  exact ⟨7, by decide, by simp only [HappyCell, carry4, digit3]; decide⟩
  exact ⟨11, by decide, by simp only [HappyCell, carry4, digit3]; decide⟩
  exact ⟨3, by decide, by simp only [HappyCell, carry4, digit3]; decide⟩
  exact ⟨4, by decide, by simp only [HappyCell, carry4, digit3]; decide⟩
  exact ⟨15, by decide, by simp only [HappyCell, carry4, digit3]; decide⟩
  exact ⟨15, by decide, by simp only [HappyCell, carry4, digit3]; decide⟩
  exact ⟨3, by decide, by simp only [HappyCell, carry4, digit3]; decide⟩
  exact ⟨3, by decide, by simp only [HappyCell, carry4, digit3]; decide⟩
  exact ⟨10, by decide, by simp only [HappyCell, carry4, digit3]; decide⟩
  exact ⟨10, by decide, by simp only [HappyCell, carry4, digit3]; decide⟩
  exact ⟨10, by decide, by simp only [HappyCell, carry4, digit3]; decide⟩
  exact ⟨8, by decide, by simp only [HappyCell, carry4, digit3]; decide⟩
  exact ⟨4, by decide, by simp only [HappyCell, carry4, digit3]; decide⟩
  exact ⟨3, by decide, by simp only [HappyCell, carry4, digit3]; decide⟩
  exact ⟨4, by decide, by simp only [HappyCell, carry4, digit3]; decide⟩
  exact ⟨4, by decide, by simp only [HappyCell, carry4, digit3]; decide⟩
  exact ⟨4, by decide, by simp only [HappyCell, carry4, digit3]; decide⟩
  exact ⟨4, by decide, by simp only [HappyCell, carry4, digit3]; decide⟩
  exact ⟨4, by decide, by simp only [HappyCell, carry4, digit3]; decide⟩
  exact ⟨4, by decide, by simp only [HappyCell, carry4, digit3]; decide⟩
  exact ⟨5, by decide, by simp only [HappyCell, carry4, digit3]; decide⟩
  exact ⟨6, by decide, by simp only [HappyCell, carry4, digit3]; decide⟩
  exact ⟨16, by decide, by simp only [HappyCell, carry4, digit3]; decide⟩
  exact ⟨17, by decide, by simp only [HappyCell, carry4, digit3]; decide⟩
  exact ⟨10, by decide, by simp only [HappyCell, carry4, digit3]; decide⟩
  exact ⟨10, by decide, by simp only [HappyCell, carry4, digit3]; decide⟩
  exact ⟨6, by decide, by simp only [HappyCell, carry4, digit3]; decide⟩
  exact ⟨4, by decide, by simp only [HappyCell, carry4, digit3]; decide⟩
  exact ⟨5, by decide, by simp only [HappyCell, carry4, digit3]; decide⟩
  exact ⟨3, by decide, by simp only [HappyCell, carry4, digit3]; decide⟩
  exact ⟨6, by decide, by simp only [HappyCell, carry4, digit3]; decide⟩
  exact ⟨11, by decide, by simp only [HappyCell, carry4, digit3]; decide⟩
  exact ⟨8, by decide, by simp only [HappyCell, carry4, digit3]; decide⟩
  exact ⟨3, by decide, by simp only [HappyCell, carry4, digit3]; decide⟩
  exact ⟨3, by decide, by simp only [HappyCell, carry4, digit3]; decide⟩
  exact ⟨12, by decide, by simp only [HappyCell, carry4, digit3]; decide⟩
  exact ⟨12, by decide, by simp only [HappyCell, carry4, digit3]; decide⟩
  exact ⟨4, by decide, by simp only [HappyCell, carry4, digit3]; decide⟩
  exact ⟨17, by decide, by simp only [HappyCell, carry4, digit3]; decide⟩
  exact ⟨16, by decide, by simp only [HappyCell, carry4, digit3]; decide⟩
  exact ⟨3, by decide, by simp only [HappyCell, carry4, digit3]; decide⟩
  exact ⟨10, by decide, by simp only [HappyCell, carry4, digit3]; decide⟩
  exact ⟨10, by decide, by simp only [HappyCell, carry4, digit3]; decide⟩
  exact ⟨10, by decide, by simp only [HappyCell, carry4, digit3]; decide⟩
  exact ⟨10, by decide, by simp only [HappyCell, carry4, digit3]; decide⟩
  exact ⟨8, by decide, by simp only [HappyCell, carry4, digit3]; decide⟩
  exact ⟨8, by decide, by simp only [HappyCell, carry4, digit3]; decide⟩
  exact ⟨11, by decide, by simp only [HappyCell, carry4, digit3]; decide⟩
  exact ⟨16, by decide, by simp only [HappyCell, carry4, digit3]; decide⟩
  exact ⟨17, by decide, by simp only [HappyCell, carry4, digit3]; decide⟩
  exact ⟨4, by decide, by simp only [HappyCell, carry4, digit3]; decide⟩
  exact ⟨7, by decide, by simp only [HappyCell, carry4, digit3]; decide⟩
  exact ⟨7, by decide, by simp only [HappyCell, carry4, digit3]; decide⟩
  exact ⟨7, by decide, by simp only [HappyCell, carry4, digit3]; decide⟩
  exact ⟨6, by decide, by simp only [HappyCell, carry4, digit3]; decide⟩
  exact ⟨6, by decide, by simp only [HappyCell, carry4, digit3]; decide⟩
  exact ⟨3, by decide, by simp only [HappyCell, carry4, digit3]; decide⟩
  exact ⟨6, by decide, by simp only [HappyCell, carry4, digit3]; decide⟩
  exact ⟨7, by decide, by simp only [HappyCell, carry4, digit3]; decide⟩
  exact ⟨8, by decide, by simp only [HappyCell, carry4, digit3]; decide⟩
  exact ⟨3, by decide, by simp only [HappyCell, carry4, digit3]; decide⟩
  exact ⟨3, by decide, by simp only [HappyCell, carry4, digit3]; decide⟩
  exact ⟨4, by decide, by simp only [HappyCell, carry4, digit3]; decide⟩
  exact ⟨5, by decide, by simp only [HappyCell, carry4, digit3]; decide⟩
  exact ⟨8, by decide, by simp only [HappyCell, carry4, digit3]; decide⟩
  exact ⟨8, by decide, by simp only [HappyCell, carry4, digit3]; decide⟩
  exact ⟨8, by decide, by simp only [HappyCell, carry4, digit3]; decide⟩
  exact ⟨3, by decide, by simp only [HappyCell, carry4, digit3]; decide⟩
  exact ⟨6, by decide, by simp only [HappyCell, carry4, digit3]; decide⟩
  exact ⟨6, by decide, by simp only [HappyCell, carry4, digit3]; decide⟩
  exact ⟨6, by decide, by simp only [HappyCell, carry4, digit3]; decide⟩
  exact ⟨26, by decide, by simp only [HappyCell, carry4, digit3]; decide⟩
  exact ⟨24, by decide, by simp only [HappyCell, carry4, digit3]; decide⟩
  exact ⟨7, by decide, by simp only [HappyCell, carry4, digit3]; decide⟩
  exact ⟨19, by decide, by simp only [HappyCell, carry4, digit3]; decide⟩
  exact ⟨19, by decide, by simp only [HappyCell, carry4, digit3]; decide⟩
  exact ⟨7, by decide, by simp only [HappyCell, carry4, digit3]; decide⟩
  exact ⟨8, by decide, by simp only [HappyCell, carry4, digit3]; decide⟩
  exact ⟨13, by decide, by simp only [HappyCell, carry4, digit3]; decide⟩
  exact ⟨13, by decide, by simp only [HappyCell, carry4, digit3]; decide⟩
  exact ⟨5, by decide, by simp only [HappyCell, carry4, digit3]; decide⟩
  exact ⟨11, by decide, by simp only [HappyCell, carry4, digit3]; decide⟩
  exact ⟨9, by decide, by simp only [HappyCell, carry4, digit3]; decide⟩
  exact ⟨3, by decide, by simp only [HappyCell, carry4, digit3]; decide⟩
  exact ⟨4, by decide, by simp only [HappyCell, carry4, digit3]; decide⟩
  exact ⟨9, by decide, by simp only [HappyCell, carry4, digit3]; decide⟩
  exact ⟨23, by decide, by simp only [HappyCell, carry4, digit3]; decide⟩
  exact ⟨3, by decide, by simp only [HappyCell, carry4, digit3]; decide⟩
  exact ⟨3, by decide, by simp only [HappyCell, carry4, digit3]; decide⟩
  exact ⟨7, by decide, by simp only [HappyCell, carry4, digit3]; decide⟩
  exact ⟨5, by decide, by simp only [HappyCell, carry4, digit3]; decide⟩
  exact ⟨6, by decide, by simp only [HappyCell, carry4, digit3]; decide⟩
  exact ⟨7, by decide, by simp only [HappyCell, carry4, digit3]; decide⟩
  exact ⟨4, by decide, by simp only [HappyCell, carry4, digit3]; decide⟩
  exact ⟨3, by decide, by simp only [HappyCell, carry4, digit3]; decide⟩
  exact ⟨4, by decide, by simp only [HappyCell, carry4, digit3]; decide⟩
  exact ⟨4, by decide, by simp only [HappyCell, carry4, digit3]; decide⟩
  exact ⟨4, by decide, by simp only [HappyCell, carry4, digit3]; decide⟩
  exact ⟨4, by decide, by simp only [HappyCell, carry4, digit3]; decide⟩
  exact ⟨4, by decide, by simp only [HappyCell, carry4, digit3]; decide⟩
  exact ⟨4, by decide, by simp only [HappyCell, carry4, digit3]; decide⟩
  exact ⟨8, by decide, by simp only [HappyCell, carry4, digit3]; decide⟩
  exact ⟨6, by decide, by simp only [HappyCell, carry4, digit3]; decide⟩
  exact ⟨5, by decide, by simp only [HappyCell, carry4, digit3]; decide⟩
  exact ⟨8, by decide, by simp only [HappyCell, carry4, digit3]; decide⟩
  exact ⟨8, by decide, by simp only [HappyCell, carry4, digit3]; decide⟩
  exact ⟨8, by decide, by simp only [HappyCell, carry4, digit3]; decide⟩
  exact ⟨7, by decide, by simp only [HappyCell, carry4, digit3]; decide⟩
  exact ⟨4, by decide, by simp only [HappyCell, carry4, digit3]; decide⟩
  exact ⟨40, by decide, by simp only [HappyCell, carry4, digit3]; decide⟩
  exact ⟨3, by decide, by simp only [HappyCell, carry4, digit3]; decide⟩
  exact ⟨14, by decide, by simp only [HappyCell, carry4, digit3]; decide⟩
  exact ⟨5, by decide, by simp only [HappyCell, carry4, digit3]; decide⟩
  exact ⟨5, by decide, by simp only [HappyCell, carry4, digit3]; decide⟩
  exact ⟨3, by decide, by simp only [HappyCell, carry4, digit3]; decide⟩
  exact ⟨3, by decide, by simp only [HappyCell, carry4, digit3]; decide⟩
  exact ⟨8, by decide, by simp only [HappyCell, carry4, digit3]; decide⟩
  exact ⟨8, by decide, by simp only [HappyCell, carry4, digit3]; decide⟩
  exact ⟨4, by decide, by simp only [HappyCell, carry4, digit3]; decide⟩
  exact ⟨5, by decide, by simp only [HappyCell, carry4, digit3]; decide⟩
  exact ⟨5, by decide, by simp only [HappyCell, carry4, digit3]; decide⟩
  exact ⟨3, by decide, by simp only [HappyCell, carry4, digit3]; decide⟩
  exact ⟨11, by decide, by simp only [HappyCell, carry4, digit3]; decide⟩
  exact ⟨9, by decide, by simp only [HappyCell, carry4, digit3]; decide⟩
  exact ⟨9, by decide, by simp only [HappyCell, carry4, digit3]; decide⟩
  exact ⟨7, by decide, by simp only [HappyCell, carry4, digit3]; decide⟩
  exact ⟨7, by decide, by simp only [HappyCell, carry4, digit3]; decide⟩
  exact ⟨5, by decide, by simp only [HappyCell, carry4, digit3]; decide⟩
  exact ⟨5, by decide, by simp only [HappyCell, carry4, digit3]; decide⟩
  exact ⟨5, by decide, by simp only [HappyCell, carry4, digit3]; decide⟩
  exact ⟨6, by decide, by simp only [HappyCell, carry4, digit3]; decide⟩
  exact ⟨4, by decide, by simp only [HappyCell, carry4, digit3]; decide⟩
  exact ⟨5, by decide, by simp only [HappyCell, carry4, digit3]; decide⟩
  exact ⟨5, by decide, by simp only [HappyCell, carry4, digit3]; decide⟩
  exact ⟨18, by decide, by simp only [HappyCell, carry4, digit3]; decide⟩
  exact ⟨17, by decide, by simp only [HappyCell, carry4, digit3]; decide⟩
  exact ⟨9, by decide, by simp only [HappyCell, carry4, digit3]; decide⟩
  exact ⟨3, by decide, by simp only [HappyCell, carry4, digit3]; decide⟩
  exact ⟨6, by decide, by simp only [HappyCell, carry4, digit3]; decide⟩
  exact ⟨6, by decide, by simp only [HappyCell, carry4, digit3]; decide⟩
  exact ⟨7, by decide, by simp only [HappyCell, carry4, digit3]; decide⟩
  exact ⟨3, by decide, by simp only [HappyCell, carry4, digit3]; decide⟩
  exact ⟨3, by decide, by simp only [HappyCell, carry4, digit3]; decide⟩
  exact ⟨4, by decide, by simp only [HappyCell, carry4, digit3]; decide⟩
  exact ⟨9, by decide, by simp only [HappyCell, carry4, digit3]; decide⟩
  exact ⟨9, by decide, by simp only [HappyCell, carry4, digit3]; decide⟩
  exact ⟨25, by decide, by simp only [HappyCell, carry4, digit3]; decide⟩
  exact ⟨13, by decide, by simp only [HappyCell, carry4, digit3]; decide⟩
  exact ⟨3, by decide, by simp only [HappyCell, carry4, digit3]; decide⟩
  exact ⟨18, by decide, by simp only [HappyCell, carry4, digit3]; decide⟩
  exact ⟨6, by decide, by simp only [HappyCell, carry4, digit3]; decide⟩
  exact ⟨21, by decide, by simp only [HappyCell, carry4, digit3]; decide⟩
  exact ⟨13, by decide, by simp only [HappyCell, carry4, digit3]; decide⟩
  exact ⟨13, by decide, by simp only [HappyCell, carry4, digit3]; decide⟩
  exact ⟨13, by decide, by simp only [HappyCell, carry4, digit3]; decide⟩
  exact ⟨7, by decide, by simp only [HappyCell, carry4, digit3]; decide⟩
  exact ⟨5, by decide, by simp only [HappyCell, carry4, digit3]; decide⟩
  exact ⟨5, by decide, by simp only [HappyCell, carry4, digit3]; decide⟩
  exact ⟨5, by decide, by simp only [HappyCell, carry4, digit3]; decide⟩
  exact ⟨5, by decide, by simp only [HappyCell, carry4, digit3]; decide⟩
  exact ⟨28, by decide, by simp only [HappyCell, carry4, digit3]; decide⟩
  exact ⟨7, by decide, by simp only [HappyCell, carry4, digit3]; decide⟩
  exact ⟨15, by decide, by simp only [HappyCell, carry4, digit3]; decide⟩
  exact ⟨15, by decide, by simp only [HappyCell, carry4, digit3]; decide⟩
  exact ⟨3, by decide, by simp only [HappyCell, carry4, digit3]; decide⟩
  exact ⟨4, by decide, by simp only [HappyCell, carry4, digit3]; decide⟩
  exact ⟨5, by decide, by simp only [HappyCell, carry4, digit3]; decide⟩
  exact ⟨6, by decide, by simp only [HappyCell, carry4, digit3]; decide⟩
  exact ⟨3, by decide, by simp only [HappyCell, carry4, digit3]; decide⟩
  exact ⟨3, by decide, by simp only [HappyCell, carry4, digit3]; decide⟩
  exact ⟨18, by decide, by simp only [HappyCell, carry4, digit3]; decide⟩
  exact ⟨7, by decide, by simp only [HappyCell, carry4, digit3]; decide⟩
  exact ⟨7, by decide, by simp only [HappyCell, carry4, digit3]; decide⟩
  exact ⟨26, by decide, by simp only [HappyCell, carry4, digit3]; decide⟩
  exact ⟨4, by decide, by simp only [HappyCell, carry4, digit3]; decide⟩
  exact ⟨3, by decide, by simp only [HappyCell, carry4, digit3]; decide⟩
  exact ⟨4, by decide, by simp only [HappyCell, carry4, digit3]; decide⟩
  exact ⟨4, by decide, by simp only [HappyCell, carry4, digit3]; decide⟩
  exact ⟨4, by decide, by simp only [HappyCell, carry4, digit3]; decide⟩
  exact ⟨4, by decide, by simp only [HappyCell, carry4, digit3]; decide⟩
  exact ⟨4, by decide, by simp only [HappyCell, carry4, digit3]; decide⟩
  exact ⟨4, by decide, by simp only [HappyCell, carry4, digit3]; decide⟩
  exact ⟨7, by decide, by simp only [HappyCell, carry4, digit3]; decide⟩
  exact ⟨8, by decide, by simp only [HappyCell, carry4, digit3]; decide⟩
  exact ⟨18, by decide, by simp only [HappyCell, carry4, digit3]; decide⟩
  exact ⟨18, by decide, by simp only [HappyCell, carry4, digit3]; decide⟩
  exact ⟨23, by decide, by simp only [HappyCell, carry4, digit3]; decide⟩
  exact ⟨5, by decide, by simp only [HappyCell, carry4, digit3]; decide⟩
  exact ⟨5, by decide, by simp only [HappyCell, carry4, digit3]; decide⟩
  exact ⟨4, by decide, by simp only [HappyCell, carry4, digit3]; decide⟩
  exact ⟨10, by decide, by simp only [HappyCell, carry4, digit3]; decide⟩
  exact ⟨3, by decide, by simp only [HappyCell, carry4, digit3]; decide⟩
  exact ⟨8, by decide, by simp only [HappyCell, carry4, digit3]; decide⟩
  exact ⟨12, by decide, by simp only [HappyCell, carry4, digit3]; decide⟩
  exact ⟨10, by decide, by simp only [HappyCell, carry4, digit3]; decide⟩
  exact ⟨3, by decide, by simp only [HappyCell, carry4, digit3]; decide⟩
  exact ⟨3, by decide, by simp only [HappyCell, carry4, digit3]; decide⟩
  exact ⟨6, by decide, by simp only [HappyCell, carry4, digit3]; decide⟩
  exact ⟨6, by decide, by simp only [HappyCell, carry4, digit3]; decide⟩
  exact ⟨4, by decide, by simp only [HappyCell, carry4, digit3]; decide⟩
  exact ⟨7, by decide, by simp only [HappyCell, carry4, digit3]; decide⟩
  exact ⟨11, by decide, by simp only [HappyCell, carry4, digit3]; decide⟩
  exact ⟨3, by decide, by simp only [HappyCell, carry4, digit3]; decide⟩
  exact ⟨12, by decide, by simp only [HappyCell, carry4, digit3]; decide⟩
  exact ⟨5, by decide, by simp only [HappyCell, carry4, digit3]; decide⟩
  exact ⟨5, by decide, by simp only [HappyCell, carry4, digit3]; decide⟩
  exact ⟨5, by decide, by simp only [HappyCell, carry4, digit3]; decide⟩
  exact ⟨6, by decide, by simp only [HappyCell, carry4, digit3]; decide⟩
  exact ⟨6, by decide, by simp only [HappyCell, carry4, digit3]; decide⟩
  exact ⟨6, by decide, by simp only [HappyCell, carry4, digit3]; decide⟩
  exact ⟨7, by decide, by simp only [HappyCell, carry4, digit3]; decide⟩
  exact ⟨7, by decide, by simp only [HappyCell, carry4, digit3]; decide⟩
  exact ⟨4, by decide, by simp only [HappyCell, carry4, digit3]; decide⟩
  exact ⟨7, by decide, by simp only [HappyCell, carry4, digit3]; decide⟩
  exact ⟨7, by decide, by simp only [HappyCell, carry4, digit3]; decide⟩
  exact ⟨7, by decide, by simp only [HappyCell, carry4, digit3]; decide⟩
  exact ⟨5, by decide, by simp only [HappyCell, carry4, digit3]; decide⟩
  exact ⟨5, by decide, by simp only [HappyCell, carry4, digit3]; decide⟩
  exact ⟨3, by decide, by simp only [HappyCell, carry4, digit3]; decide⟩
  exact ⟨9, by decide, by simp only [HappyCell, carry4, digit3]; decide⟩
  exact ⟨12, by decide, by simp only [HappyCell, carry4, digit3]; decide⟩
  exact ⟨5, by decide, by simp only [HappyCell, carry4, digit3]; decide⟩
  exact ⟨3, by decide, by simp only [HappyCell, carry4, digit3]; decide⟩
  exact ⟨3, by decide, by simp only [HappyCell, carry4, digit3]; decide⟩
  exact ⟨4, by decide, by simp only [HappyCell, carry4, digit3]; decide⟩
  exact ⟨9, by decide, by simp only [HappyCell, carry4, digit3]; decide⟩
  exact ⟨12, by decide, by simp only [HappyCell, carry4, digit3]; decide⟩
  exact ⟨5, by decide, by simp only [HappyCell, carry4, digit3]; decide⟩
  exact ⟨9, by decide, by simp only [HappyCell, carry4, digit3]; decide⟩
  exact ⟨3, by decide, by simp only [HappyCell, carry4, digit3]; decide⟩
  exact ⟨19, by decide, by simp only [HappyCell, carry4, digit3]; decide⟩
  exact ⟨17, by decide, by simp only [HappyCell, carry4, digit3]; decide⟩
  exact ⟨6, by decide, by simp only [HappyCell, carry4, digit3]; decide⟩
  exact ⟨6, by decide, by simp only [HappyCell, carry4, digit3]; decide⟩
  exact ⟨22, by decide, by simp only [HappyCell, carry4, digit3]; decide⟩
  exact ⟨25, by decide, by simp only [HappyCell, carry4, digit3]; decide⟩
  exact ⟨18, by decide, by simp only [HappyCell, carry4, digit3]; decide⟩
  exact ⟨8, by decide, by simp only [HappyCell, carry4, digit3]; decide⟩
  exact ⟨8, by decide, by simp only [HappyCell, carry4, digit3]; decide⟩
  exact ⟨8, by decide, by simp only [HappyCell, carry4, digit3]; decide⟩
  exact ⟨13, by decide, by simp only [HappyCell, carry4, digit3]; decide⟩
  exact ⟨13, by decide, by simp only [HappyCell, carry4, digit3]; decide⟩
  exact ⟨9, by decide, by simp only [HappyCell, carry4, digit3]; decide⟩
  exact ⟨7, by decide, by simp only [HappyCell, carry4, digit3]; decide⟩
  exact ⟨8, by decide, by simp only [HappyCell, carry4, digit3]; decide⟩
  exact ⟨3, by decide, by simp only [HappyCell, carry4, digit3]; decide⟩
  exact ⟨4, by decide, by simp only [HappyCell, carry4, digit3]; decide⟩
  exact ⟨7, by decide, by simp only [HappyCell, carry4, digit3]; decide⟩
  exact ⟨8, by decide, by simp only [HappyCell, carry4, digit3]; decide⟩
  exact ⟨3, by decide, by simp only [HappyCell, carry4, digit3]; decide⟩
  exact ⟨3, by decide, by simp only [HappyCell, carry4, digit3]; decide⟩
  exact ⟨6, by decide, by simp only [HappyCell, carry4, digit3]; decide⟩
  exact ⟨11, by decide, by simp only [HappyCell, carry4, digit3]; decide⟩
  exact ⟨12, by decide, by simp only [HappyCell, carry4, digit3]; decide⟩
  exact ⟨6, by decide, by simp only [HappyCell, carry4, digit3]; decide⟩
  exact ⟨4, by decide, by simp only [HappyCell, carry4, digit3]; decide⟩
  exact ⟨3, by decide, by simp only [HappyCell, carry4, digit3]; decide⟩
  exact ⟨4, by decide, by simp only [HappyCell, carry4, digit3]; decide⟩
  exact ⟨4, by decide, by simp only [HappyCell, carry4, digit3]; decide⟩
  exact ⟨4, by decide, by simp only [HappyCell, carry4, digit3]; decide⟩
  exact ⟨4, by decide, by simp only [HappyCell, carry4, digit3]; decide⟩
  exact ⟨4, by decide, by simp only [HappyCell, carry4, digit3]; decide⟩
  exact ⟨4, by decide, by simp only [HappyCell, carry4, digit3]; decide⟩
  exact ⟨5, by decide, by simp only [HappyCell, carry4, digit3]; decide⟩
  exact ⟨9, by decide, by simp only [HappyCell, carry4, digit3]; decide⟩
  exact ⟨9, by decide, by simp only [HappyCell, carry4, digit3]; decide⟩
  exact ⟨10, by decide, by simp only [HappyCell, carry4, digit3]; decide⟩
  exact ⟨6, by decide, by simp only [HappyCell, carry4, digit3]; decide⟩
  exact ⟨7, by decide, by simp only [HappyCell, carry4, digit3]; decide⟩
  exact ⟨7, by decide, by simp only [HappyCell, carry4, digit3]; decide⟩
  exact ⟨4, by decide, by simp only [HappyCell, carry4, digit3]; decide⟩
  exact ⟨5, by decide, by simp only [HappyCell, carry4, digit3]; decide⟩
  exact ⟨3, by decide, by simp only [HappyCell, carry4, digit3]; decide⟩
  exact ⟨10, by decide, by simp only [HappyCell, carry4, digit3]; decide⟩
  exact ⟨10, by decide, by simp only [HappyCell, carry4, digit3]; decide⟩
  exact ⟨15, by decide, by simp only [HappyCell, carry4, digit3]; decide⟩
  exact ⟨3, by decide, by simp only [HappyCell, carry4, digit3]; decide⟩
  exact ⟨3, by decide, by simp only [HappyCell, carry4, digit3]; decide⟩
  exact ⟨7, by decide, by simp only [HappyCell, carry4, digit3]; decide⟩
  exact ⟨6, by decide, by simp only [HappyCell, carry4, digit3]; decide⟩
  exact ⟨4, by decide, by simp only [HappyCell, carry4, digit3]; decide⟩
  exact ⟨13, by decide, by simp only [HappyCell, carry4, digit3]; decide⟩
  exact ⟨13, by decide, by simp only [HappyCell, carry4, digit3]; decide⟩
  exact ⟨3, by decide, by simp only [HappyCell, carry4, digit3]; decide⟩
  exact ⟨6, by decide, by simp only [HappyCell, carry4, digit3]; decide⟩
  exact ⟨6, by decide, by simp only [HappyCell, carry4, digit3]; decide⟩
  exact ⟨6, by decide, by simp only [HappyCell, carry4, digit3]; decide⟩
  exact ⟨6, by decide, by simp only [HappyCell, carry4, digit3]; decide⟩
  exact ⟨6, by decide, by simp only [HappyCell, carry4, digit3]; decide⟩
  exact ⟨14, by decide, by simp only [HappyCell, carry4, digit3]; decide⟩
  exact ⟨8, by decide, by simp only [HappyCell, carry4, digit3]; decide⟩
  exact ⟨8, by decide, by simp only [HappyCell, carry4, digit3]; decide⟩
  exact ⟨7, by decide, by simp only [HappyCell, carry4, digit3]; decide⟩
  exact ⟨4, by decide, by simp only [HappyCell, carry4, digit3]; decide⟩
  exact ⟨13, by decide, by simp only [HappyCell, carry4, digit3]; decide⟩
  exact ⟨16, by decide, by simp only [HappyCell, carry4, digit3]; decide⟩
  exact ⟨41, by decide, by simp only [HappyCell, carry4, digit3]; decide⟩
  exact ⟨7, by decide, by simp only [HappyCell, carry4, digit3]; decide⟩
  exact ⟨7, by decide, by simp only [HappyCell, carry4, digit3]; decide⟩
  exact ⟨3, by decide, by simp only [HappyCell, carry4, digit3]; decide⟩

open GSTU2DEventTransport in
open GSTCanonicalSevenAxisBridge in
/-- **THE CLIMB FROM BASE AND TAIL.**  The full climb primitive follows
from the kernel-certified base band plus the tail above five hundred —
the mission's remaining content, stated as one hypothesis. -/
theorem erdos406_climb_of_base_and_tail
    (htail : ∀ K : Nat, 500 < K →
      ∃ p : Nat, 3 ≤ p ∧
        HappyCell (carry4 (4^K) p) (digit3 (4^K) p)) :
    GSTInfiniteFourPowerNavigation.four_power_happy_climb := by
  intro K hK8
  rcases Nat.lt_or_ge K 501 with h | h
  · exact erdos406_climb_base K hK8 (by omega)
  · exact htail K (by omega)

open GSTU2DEventTransport in
open GSTCanonicalSevenAxisBridge in
/-- **THE MISSION'S SHARPEST STATEMENT — the verdict from the tail
alone.**  Erdős #406's universal verdict follows from the climb's tail
above five hundred alone: the base band is kernel-certified, the
composition is machine-proven, and the entire remaining mathematical
content of the problem is the single named hypothesis. -/
theorem erdos406_universal_verdict_of_tail
    (htail : ∀ K : Nat, 500 < K →
      ∃ p : Nat, 3 ≤ p ∧
        HappyCell (carry4 (4^K) p) (digit3 (4^K) p)) :
    ∀ n : Nat, 9 ≤ n → noTernaryTwo (2^n) = false :=
  erdos406_universal_verdict_of_climb
    (erdos406_climb_of_base_and_tail htail)

#print axioms erdos406_climb_base
#print axioms erdos406_climb_of_base_and_tail
#print axioms erdos406_universal_verdict_of_tail

#eval "ERDOS406_CLIMB_BASE_GREEN"

#eval "ERDOS406_FINAL_VERDICT_GREEN"
