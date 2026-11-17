import GSTOmegaAbsorbingZero

set_option maxRecDepth 1000000
set_option maxHeartbeats 20000000

/-!
# Direct residual Omega infinite-bad ↔ exact preterminal source bound

This theorem strengthens the user's original GSTOmegaInfiniteBadTrace
surface itself, rather than introducing an auxiliary V2 controller.
It uses exactly the established perfect-power residual seed/word
decomposition in gst_omega_infiniteBadTrace_iff_seededAffine.
The all-infinite quantifier is eliminated noncircularly.

The remaining residual-termination problem is *not* solved by the
equivalence; it requires proving an actual gate before this cutoff.
-/

namespace GSTOmegaResidualFiniteSupport

def seed (s k : Nat) : Nat :=
  (4*(c s%3^k))/3^k

def word (s k m : Nat) : Nat :=
  c s/3^k+4^(3^s)*gstNavigationConstant (s+k) m

def terminalCut (s k m : Nat) : Nat :=
  seed s k+4*word s k m+1

theorem omega_bad_iff_preterminal
    (s k m : Nat) :
    GSTOmegaInfiniteBadTrace s k m ↔
      ∀ j, j < terminalCut s k m →
        GSTBadPair
          (gstAffineMulCarry 4 (seed s k) (word s k m) j)
          (gstDigit (word s k m) j) := by
  rw [gst_omega_infiniteBadTrace_iff_seededAffine]
  change (∀ j, GSTBadPair
    (gstAffineMulCarry 4 (seed s k) (word s k m) j)
    (gstDigit (word s k m) j)) ↔ _
  constructor
  · intro h j hj
    exact h j
  · intro h j
    by_cases hj : j < terminalCut s k m
    · exact h j hj
    · have htail : seed s k + 4*word s k m+1 ≤ j := by
        simpa [terminalCut] using Nat.le_of_not_gt hj
      obtain ⟨hd,hc⟩ :=
        GSTOmegaAbsorbingZero.finite_seed_eventually_zero
          (seed s k) (word s k m) j htail
      unfold GSTBadPair
      rw [hd, hc]
      decide

/-- For every fixed residual source, a genuine bad orbit must be bad
at every integer point STRICTLY below the explicit cutoff,
and no special infinity axiom is required beyond that. -/
theorem residual_omega_termination_iff_early_collision
    (s k m : Nat) :
    ¬ GSTOmegaInfiniteBadTrace s k m ↔
      ∃ j, j < terminalCut s k m ∧
        ¬ GSTBadPair
          (gstAffineMulCarry 4 (seed s k) (word s k m) j)
          (gstDigit (word s k m) j) := by
  rw [omega_bad_iff_preterminal]
  push_neg
  rfl

#print axioms omega_bad_iff_preterminal
#print axioms residual_omega_termination_iff_early_collision

end GSTOmegaResidualFiniteSupport
