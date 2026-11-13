# W57-5 / P288 — STATUS (two-interval harmonic kernel r1)

1. **Erdos288.lean** — the round-1 kernel (namespace E288, CI-verdict, zero sorry):
   `window`/`wprod`/`hnum`/`equalWindow` (the interval sum Σ 1/i as an exact
   unreduced Nat fraction + the cross-multiplied equality), structural laws
   (recurrences rfl, empty-window, positivity), single-window spellings, the
   strict growth law `window_mono_step`, `empty_never_nonempty` (unconditional),
   `equalWindow_refl`/`equalWindow_symm`, python-verified anchors
   ([2,4]↦26/24, [3,5]↦47/60, [6,9]↦1650/3024, [4,7]↦638/840), two bounded
   decide-censuses, the arsenal bridge (5 Arsenal lemmas at #288 anchors), and
   the 12-conjunct master board `e288_board`.
2. **hunt288.py** — THE HUNT (2.1s): ZERO disjoint equal-sum window pairs with
   all endpoints ≤ 120 (7,260 windows, exact Fraction grouping); ZERO
   single-vs-later-window matches (n ≤ 40, d ≤ 80). **No witness pairs exist in
   range — the conjectured #288 classification is EMPTY.**
3. **verify288.py** — the Lean-mirror verification (anchors + bounded census
   ranges 12/24 both zero) — every decide theorem pre-verified in python.
4. ROUND-2 LANES: (a) the Kürschák parity transfer (unique max-2-adic element
   of the span ⇒ hnum odd) — proves the full empty-classification conjecture,
   the #317 isolated-extremal engine transfer; (b) the separation/length law
   (equal disjoint windows ⇒ the later one is longer); (c) census escalation
   past 12/24 (or replace by the parity proof).
5. NEXT: CI verdict on Erdos288.lean; then the parity kernel (a).
