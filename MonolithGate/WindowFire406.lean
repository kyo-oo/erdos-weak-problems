import MonolithGate.RowTowerBreakthrough406
import MonolithGate.GSTDiagonalRead

set_option maxRecDepth 1000000
set_option maxHeartbeats 20000000

/-!
# THE WINDOW FIRE - the tower frontier carved by the diagonal read
## (S090 v6, BOSS order: COMPLETE THE TASK / USE MY OWN MATHS)

WHAT THIS MODULE DELIVERS, all unconditional, all composed from BOSS's
own mathematics (the vendored diagonal read's window fires and the v5
reduction law), zero hidden hypotheses:

  1. **THE WINDOW-COVERED LAW** (`digit_two_of_window_covered`): every
     exponent of the diagonal read's own fire families owns its ternary
     digit two - the level-two band (`K = 3^a·core`, `a ≥ 2`, `core ≡ 13,
     25 (mod 27)`: `GSTDiagonalRead.window_fire_level2`) and the
     level-three band (`a ≥ 3`, `core ≡ 4, 34, 49, 70 (mod 81)`:
     `GSTDiagonalRead.window_fire_level3`).  Both bands are uniform in
     the valuation scale: every level, every core of the band, one row.

  2. **THE SHARP REDUCTION LAW** (`erdos_406_full_verdict_iff_sharp_
     frontier_fires`): the FULL verdict of Erdős #406 is EQUIVALENT to the
     SHARP frontier firing - the v5 fourteen-class frontier minus the
     window-covered bands.  The sharp frontier, named exactly:
     * the five 3-free row-family classes `{1, 10, 28, 37, 64} (mod 81)`
       (unchanged: the window at valuation zero reads one trit, and the
       fire families begin at valuation one);
     * the five valuation-one tower classes `K = 3·core` with `core ≡ 4,
       7, 13, 16, 25 (mod 27)` (the classes `12, 21, 39, 48, 75 (mod 81)`
       - unchanged by the window bands, which begin at valuation two);
     * the valuation-two remainders `K = 9·core`: class `36 (mod 81)`
       with `core ≡ 4, 22 (mod 27)` (the `13` band fires) and class `63
       (mod 81)` with `core ≡ 7, 16 (mod 27)` (the `25` band fires);
     * the valuation-three-plus remainders `K = 3^a·core`, `a ≥ 3`
       (classes `27` and `0 mod 81`): after both bands fire, the cores
       `{7, 16, 22, 31, 43, 58, 61, 76} (mod 81)` remain.

THE HONEST LEDGER: the tower side of the frontier is now carved to ten
named (valuation, core-class) cells; the five row-family classes and the
five valuation-one tower classes remain the exact frontier of the digit
route.  The green dust collapse (`DustCandidates406.
dust_candidate_two_classes`) pins the TAILF-route dust cores to the two
classes `4, 16 (mod 27)` - through the mission board's own tower
primitive composition, the three valuation-one classes with `core ≡ 7,
13, 25 (mod 27)` (classes `21, 39, 75`) are the next kill candidates.
-/

namespace WindowFire406

open GSTCanonicalSevenAxisBridge (digit3)
open RowTowerBreakthrough406

/-! ## §0 THE WINDOW-COVERED LAW - the diagonal read's fire bands,
unconditional at every valuation scale. -/

/-- **The window-covered exponents.**  The diagonal read's own fire
bands: level two (valuation at least two, core in the `13, 25` band mod
27) and level three (valuation at least three, core in the `4, 34, 49,
70` band mod 81).  Every core of both bands is three-free (`≡ 1 mod 3`),
so the valuation witness is exactly the maximal 3-adic valuation. -/
def erdos_406_window_covered (K : Nat) : Prop :=
  ∃ a core : Nat, K = 3 ^ a * core ∧
    ((2 ≤ a ∧ (core % 27 = 13 ∨ core % 27 = 25)) ∨
      (3 ≤ a ∧ (core % 81 = 4 ∨ core % 81 = 34 ∨ core % 81 = 49 ∨
        core % 81 = 70)))

/-- **Every window-covered exponent owns its ternary digit two.**  The
level-two band fires at row `a + 3`, the level-three band at row `a + 4`
- both uniform in the valuation scale, both unconditional theorems of
the vendored diagonal read. -/
theorem digit_two_of_window_covered (K : Nat)
    (hw : erdos_406_window_covered K) :
    ∃ p : Nat, 1 ≤ p ∧ digit3 (4 ^ K) p = 2 := by
  rcases hw with ⟨a, core, hK, h2 | h3⟩
  · obtain ⟨ha, hc⟩ := h2
    refine ⟨a + 3, by omega, ?_⟩
    rw [hK]
    exact GSTDiagonalRead.window_fire_level2 a ha core hc
  · obtain ⟨ha, hc⟩ := h3
    refine ⟨a + 4, by omega, ?_⟩
    rw [hK]
    exact GSTDiagonalRead.window_fire_level3 a ha core hc

/-! ## §1 THE SHARP FRONTIER - the fourteen-class frontier carved by
the window bands. -/

/-- **The sharp frontier of Erdős #406.**  The v5 frontier (beyond the
certified base, outside the thirty-seven covered classes and both Ω-wave
families) minus the window-covered bands: the exact set of exponents
whose digit two is not yet unconditional after the diagonal read's own
fire families are credited. -/
def erdos_406_sharp_frontier_class (K : Nat) : Prop :=
  500 < K ∧ ¬ erdos_406_covered_class K ∧ ¬ erdos_406_omega_covered K ∧
    ¬ erdos_406_window_covered K

/-- **THE EVEN-EXPONENT STATEMENT FROM THE SHARP FRONTIER ALONE.**  If
every sharp-frontier exponent fires its digit two, then every `4^K`
from `K = 8` onward scans false: the v5 frontier splits into the
sharp frontier and the window bands, and both fire. -/
theorem erdos_406_even_conjecture_of_sharp_frontier_fires
    (hsharp : ∀ K : Nat, 8 ≤ K → erdos_406_sharp_frontier_class K →
      ∃ p : Nat, 1 ≤ p ∧ digit3 (4 ^ K) p = 2) :
    ∀ K : Nat, 8 ≤ K → noTernaryTwo (4 ^ K) = false := by
  refine erdos_406_even_conjecture_of_frontier_fires ?_
  intro K hK hfront
  by_cases hw : erdos_406_window_covered K
  · exact digit_two_of_window_covered K hw
  · exact hsharp K hK ⟨hfront.1, hfront.2.1, hfront.2.2, hw⟩

/-- **THE SHARP REDUCTION LAW OF ERDŐS #406.**  The full universal
verdict - every `2^n` from `n = 9` onward owning its ternary digit two
- is EQUIVALENT to the sharp frontier firing.  Both directions compose
the green v5 reduction law with the window-covered law: forward, the
sharp frontier is contained in the v5 frontier; backward, the v5
frontier splits into the window bands (which fire unconditionally) and
the sharp frontier.  The residual of Erdős #406 shrinks from fourteen
classes to ten named (valuation, core-class) cells. -/
theorem erdos_406_full_verdict_iff_sharp_frontier_fires :
    (∀ n : Nat, 9 ≤ n → noTernaryTwo (2 ^ n) = false) ↔
      (∀ K : Nat, 8 ≤ K → erdos_406_sharp_frontier_class K →
        ∃ p : Nat, 1 ≤ p ∧ digit3 (4 ^ K) p = 2) := by
  constructor
  · intro hverdict K hK hsharpK
    refine erdos_406_full_verdict_iff_frontier_fires.mp hverdict K hK
      ⟨hsharpK.1, hsharpK.2.1, hsharpK.2.2.1⟩
  · intro hsharp
    refine erdos_406_full_verdict_iff_frontier_fires.mpr ?_
    intro K hK hfront
    by_cases hw : erdos_406_window_covered K
    · exact digit_two_of_window_covered K hw
    · exact hsharp K hK ⟨hfront.1, hfront.2.1, hfront.2.2, hw⟩

/-! ## §2 THE RECEIPTS - every claim above, axiom-audited. -/

#print axioms digit_two_of_window_covered
#print axioms erdos_406_even_conjecture_of_sharp_frontier_fires
#print axioms erdos_406_full_verdict_iff_sharp_frontier_fires

end WindowFire406

#eval "ERDOS_406_WINDOW_FIRE_GREEN"
