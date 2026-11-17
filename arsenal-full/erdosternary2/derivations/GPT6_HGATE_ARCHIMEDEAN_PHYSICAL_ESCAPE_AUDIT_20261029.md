# Problem 406 — original hGate: global physical magnitude obstruction (2026-10-29)

## Authority and unmodified goal

Branch: `gpt6/problem406-seventh-trit-worldtrace-20261029`, based on the original conditional proof. The exact remaining theorem is

```lean
def gst_four_power_third_wave_gate : Prop :=
  ∀ K : Nat, 5 ≤ K → K ≠ 7 → GSTFourPowerThirdWave.thirdWave K
```

Here `thirdWave K ↔ CommonTwo K`, meaning a **same-position** ternary digit 2 in both literal physical powers `4^K` and `4^(K+1)`. Production's conditional downstream construction and the challenge's original type are kept untouched: **this goal is not yet proved**.

## New mathematical result: global archimedean physical escape

New verified module: `GSTProblem406ArchimedeanPhysicalEscape.lean`.

Existing proof `GSTFourPowerDirectNo22.no_common_pow4_forbids_all_22` says that for *exact power source* `4^K` the total absence of `CommonTwo K` forbids every consecutive base-three digit pair `22`.

Existing proof `GSTFourPowerNo22Magnitude.no22_nine_power_bound` gives the sharp global magnitude estimate, for any number `N<9^m` with no adjacent `22`,

```
8*N ≤ 7*(9^m-1).
```

Composing those two **kernel-checked** global results yields:

```lean
theorem no_gate_forces_sharp_magnitude
    (K m : Nat) (hBelow : 4^K < 9^m) (hBad : ¬ CommonTwo K) :
    8*4^K ≤ 7*(9^m-1)
```

Contraposition yields a true original hGate-body result with **no earlier witness or universal hypothesis**:

```lean
theorem CommonTwo_of_archimedean_escape
    (K m : Nat)
    (hBelow : 4^K < 9^m)
    (hEscape : 7*(9^m-1) < 8*4^K) :
    CommonTwo K
```

The code also transports the result through `thirdWave_iff_commonTwo` into `GSTFourPowerThirdWave.thirdWave K` and through `GSTFourPowerDirectCreationMaster.commonTwo_to_creation_certificate` into the **original creation-certificate type**. All these declarations have axiom dependencies limited to standard `propext`, `Classical.choice`, `Quot.sound`; **no sorryAx**.

CI kernel PASS: https://github.com/kyo-oo/erdosternary2/actions/runs/40930634621
Commit of Lean fix: `6b713aaaa35399d2a025ae251afacdcb1c88e9c6`.

This is an all-`K` sufficient condition, **not** an assertion that every `K` satisfies the escape inequality. Indeed `K=7` is not permitted as an unconditional gate, and various actual good `K` fail the archimedean inequality. A theorem proving every eligible `K` hits some valid physical gate is still needed.

## Independent exact arithmetic reconnaissance (not a universal proof)

A Python 3 finite test, using exact big-integer modular exponentiation `pow(4,k,3**(p+1))`, examined **every** integer exponent `5≤K≤1,000,000`. For each `K` it tested the simultaneous source-neighbor digits at each increasing row `1≤p≤81`. Every `K≠7` received a witness by row 81. The last nonexceptional survivor at row 80 was `K=181406`, which fired at row 81.

This establishes only the specified **finite assertion** for the independent executable calculation, **not** a kernel proof of the finite million, and not any statement for K>1,000,000. Mathematical proof still needs a source-specific all-exponent cross-depth argument.

## Other global routes checked

- The finite-state source-neighbor automaton count `survivingCount(2m, c)≤7^m` bounds bad **density**, not bad cardinality by zero.
- Exact 3-adic exponent isometry means any bounded digit-observation window can be mimicked by true exponent powers; `GSTProblem406DelayedExactHGate` proves arbitrarily delayed first physical overlaps.
- The generic cubic/three-step propagation is false for arbitrary integer source inputs and cannot be upgraded merely by high dyadic divisibility, as `GSTProblem406DyadicShortcutNoGo` checks without sorryAx.
- A magnitude criterion only covers certain archimedean phases; it cannot simply be substituted as the universal hGate.

## Remaining *single* proof obligation

```
⊢ ∀ K : Nat, 5 ≤ K → K ≠ 7 →
   ∃ p : Nat, 1 ≤ p ∧ digit3 (4^K) p=2 ∧ digit3 (4^(K+1)) p=2
```

Do not change production `Solution.lean` until the above proposition is proved without a new hypothesis, axiom or `sorryAx` and the strict comparator accepts exactly its binder-free challenge type.
