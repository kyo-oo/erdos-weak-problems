import GSTOmegaAbsorbingZero
import GSTInfiniteGateTransport

set_option maxRecDepth 1000000
set_option maxHeartbeats 20000000

/-!
# GST finite-source / genuinely infinite-controller separation

This is the noncircular normal form of the exact all-depth Omega operator.
It uses the existing kernel-proved finite_seed_eventually_zero to eliminate
the infinite zero/zero suffix, NOT a sampled finite search.

The all-Nat controller itself proves no Happy-Gate existence: with
the exact coupled source invariant it is equivalent to assuming the
parent's entire seeded BAD trace. Any proof of Erdős from these premises
needs an extra canonical perfect-power collision, not a second conservation
identity or a stronger all-depth quantifier.
-/

namespace GSTOmegaTerminalNormalForm

open GSTV2
open GSTOmegaAbsorbingZero

/-- The exact cut at which every finite word and seed enters the
absorbing zero/zero Omega state. -/
def cutoff (D X : Nat) : Nat := D + 4 * X + 1

/-- The infinite seeded BAD-language condition is equivalent to the
BAD-language condition only below the terminal cutoff. This is a theorem
for EVERY natural seed and word, without any probabilistic argument. -/
theorem seeded_bad_iff_preterminal (D X : Nat) :
    SeededBadTrace D X ↔
      ∀ j, j < cutoff D X →
        ¬ Happy (affineCarry D X j) (digit X j) := by
  constructor
  · intro hbad j hj
    exact hbad j
  · intro hpre j
    by_cases hj : j < cutoff D X
    · exact hpre j hj
    · have htail : cutoff D X ≤ j := by omega
      have hzero :
          gstDigit X j = 0 ∧
            gstAffineMulCarry 4 D X j = 0 :=
        finite_seed_eventually_zero D X j (by
          dsimp [cutoff] at htail
          exact htail)
      have hDigit : digit X j = 0 := by
        simpa [digit, gstDigit] using hzero.1
      intro hHappy
      exact (by
        have hTwo : digit X j = 2 := hHappy.1
        omega : False)

/-- The terminal tail is a genuinely infinite BAD suffix, for all j
past the exact finite-source cutoff. -/
theorem all_depth_tail_absorbing
    (D X : Nat) :
    ∀ j, cutoff D X ≤ j →
      digit X j = 0 ∧ affineCarry D X j = 0 := by
  intro j hj
  have h := finite_seed_eventually_zero D X j (by
    simpa [cutoff] using hj)
  simpa [digit, gstDigit, affineCarry, gstAffineMulCarry] using h

/-- The exact infinite coupled bad controller is logically equivalent
to its BAD parent input whenever its non-bad physical invariants hold.
This formally identifies which premise cannot be inferred from infinity. -/
theorem infinite_controller_iff_seeded_bad
    (A : Nat) (st : CoupledState)
    (hA : 0 < A) (hInv : CoupledInvariant A st)
    (hzero : st.childCarry = 0) :
    InfiniteBadCoupledControl A st ↔
      SeededBadTrace st.parentSeed (st.parentWord A) := by
  constructor
  · intro h
    exact h.parentBad
  · intro h
    exact infinite_bad_coupled_control A st hA hInv hzero h

/-- The controller condition has an exact, quantifier-reduced
natural-source preterminal characterization. -/
theorem infinite_controller_iff_preterminal
    (A : Nat) (st : CoupledState)
    (hA : 0 < A) (hInv : CoupledInvariant A st)
    (hzero : st.childCarry = 0) :
    InfiniteBadCoupledControl A st ↔
      ∀ j, j < cutoff st.parentSeed (st.parentWord A) →
        ¬ Happy
          (affineCarry st.parentSeed (st.parentWord A) j)
          (digit (st.parentWord A) j) := by
  rw [infinite_controller_iff_seeded_bad A st hA hInv hzero]
  exact seeded_bad_iff_preterminal _ _

#print axioms seeded_bad_iff_preterminal
#print axioms all_depth_tail_absorbing
#print axioms infinite_controller_iff_seeded_bad
#print axioms infinite_controller_iff_preterminal

end GSTOmegaTerminalNormalForm
