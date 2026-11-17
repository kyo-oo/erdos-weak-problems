import GSTInfiniteCollision

set_option maxRecDepth 1000000
set_option maxHeartbeats 10000000

namespace GSTV2

/-!
# All-depth bad-language transport

This layer connects the coupled information controller to the exact seeded
parent bad language.  A bad trace is not re-proved at each finite depth: one
initial all-Nat bad trace is reindexed through the coupled orbit, preserving
its true regenerated seed and exact remaining information word.
-/

/-- The production Happy cell. -/
def Happy (carry d : Nat) : Prop :=
  d = 2 ∧ (carry = 0 ∨ carry = 3)

/-- Complete seeded parent badness at every natural coordinate. -/
def SeededBadTrace (D X : Nat) : Prop :=
  ∀ k, ¬ Happy (affineCarry D X k) (digit X k)

/-- Exact seeded carry semigroup used to reindex a bad suffix. -/
theorem affineCarry_semigroup
    (D X q j : Nat) :
    affineCarry D X (q+j) =
      affineCarry (affineCarry D X q) (X / 3^q) j := by
  simp only [affineCarry]
  rw [Nat.pow_add, Nat.mod_mul]
  have hq : 0 < 3^q := Nat.pow_pos (by decide)
  have hshape :
      D + 4 * (X % 3^q + 3^q * (X / 3^q % 3^j)) =
        (D + 4 * (X % 3^q)) +
          3^q * (4 * (X / 3^q % 3^j)) := by
    rw [Nat.mul_add]
    ac_rfl
  rw [hshape, ← Nat.div_div_eq_div_mul,
    Nat.add_mul_div_left _ _ hq]

/-- Complete badness survives exact suffix reindexing. -/
theorem seededBadTrace_suffix
    (D X q : Nat) (hbad : SeededBadTrace D X) :
    SeededBadTrace (affineCarry D X q) (X / 3^q) := by
  intro j hHappy
  have h := hbad (q+j)
  rw [affineCarry_semigroup, digit_shift] at h
  exact h hHappy

/-- The digit emitted by a coupled parent step is exactly the current low
ternary digit of the represented parent word. -/
theorem coupled_parent_emitted_exact
    (A : Nat) (st : CoupledState) :
    (st.parentOffset + A * (st.childTail % 3)) % 3 =
      st.parentWord A % 3 := by
  unfold CoupledState.parentWord
  simp [Nat.add_mod, Nat.mul_mod]

/-- The all-Nat coupled parent seed is the true seeded x4 carry of the original
parent information word at that same observation depth. -/
theorem coupledOrbit_parentSeed_exact
    (A : Nat) (initial : CoupledState) :
    ∀ K,
      (coupledOrbit A initial K).parentSeed =
        affineCarry initial.parentSeed (initial.parentWord A) K := by
  intro K
  induction K with
  | zero =>
      simp [coupledOrbit, affineCarry, Nat.mod_one]
  | succ K ih =>
      rw [coupledOrbit]
      change
        cellNextCarry (coupledOrbit A initial K).parentSeed
            (((coupledOrbit A initial K).parentOffset +
              A * ((coupledOrbit A initial K).childTail % 3)) % 3) =
          affineCarry initial.parentSeed (initial.parentWord A) (K+1)
      rw [ih, affineCarry_forward]
      congr 1
      rw [coupled_parent_emitted_exact,
        coupledOrbit_parentWord_exact]
      rfl

/-- The parent digit consumed at every coupled depth is the actual digit of the
original represented parent word. -/
theorem coupledOrbit_parentDigit_exact
    (A : Nat) (initial : CoupledState) :
    ∀ K,
      ((coupledOrbit A initial K).parentOffset +
          A * ((coupledOrbit A initial K).childTail % 3)) % 3 =
        digit (initial.parentWord A) K := by
  intro K
  rw [coupled_parent_emitted_exact,
    coupledOrbit_parentWord_exact]
  rfl

/-- A complete initial bad language is visible as a bad current cell at every
natural depth of the coupled controller. -/
theorem coupledOrbit_parent_bad_current
    (A : Nat) (initial : CoupledState)
    (hbad : SeededBadTrace initial.parentSeed (initial.parentWord A)) :
    ∀ K,
      ¬ Happy
        (coupledOrbit A initial K).parentSeed
        (((coupledOrbit A initial K).parentOffset +
          A * ((coupledOrbit A initial K).childTail % 3)) % 3) := by
  intro K
  have h := hbad K
  rw [← coupledOrbit_parentSeed_exact A initial K,
    ← coupledOrbit_parentDigit_exact A initial K] at h
  exact h

/-- Stronger suffix form: after *any* natural observation depth the remaining
coupled parent word carries the complete bad language with exactly the
regenerated seed.  No finite wave cutoff or terminal-state axiom occurs. -/
theorem coupledOrbit_parent_bad_suffix
    (A : Nat) (initial : CoupledState)
    (hbad : SeededBadTrace initial.parentSeed (initial.parentWord A)) :
    ∀ K,
      SeededBadTrace
        (coupledOrbit A initial K).parentSeed
        ((coupledOrbit A initial K).parentWord A) := by
  intro K
  have hsuffix := seededBadTrace_suffix
    initial.parentSeed (initial.parentWord A) K hbad
  rw [← coupledOrbit_parentSeed_exact A initial K,
    ← coupledOrbit_parentWord_exact A initial K] at hsuffix
  exact hsuffix

/-- The coupled controller simultaneously carries exact child realization,
exact parent realization, and complete regenerated badness at every depth. -/
structure InfiniteBadCoupledControl
    (A : Nat) (initial : CoupledState) : Prop where
  coupled : InfiniteCoupledControl A initial
  childCarryZero : initial.childCarry = 0
  parentBad : SeededBadTrace initial.parentSeed (initial.parentWord A)
  parentBadSuffix : ∀ K,
    SeededBadTrace
      (coupledOrbit A initial K).parentSeed
      ((coupledOrbit A initial K).parentWord A)
  childCarryExact : ∀ K,
    (coupledOrbit A initial K).childCarry =
      naturalCarry initial.childTail K

/-- Construction of the full all-depth bad coupled controller. -/
theorem infinite_bad_coupled_control
    (A : Nat) (initial : CoupledState)
    (hA : 0 < A) (hInv : CoupledInvariant A initial)
    (hC0 : initial.childCarry = 0)
    (hbad : SeededBadTrace initial.parentSeed (initial.parentWord A)) :
    InfiniteBadCoupledControl A initial := by
  exact {
    coupled := infinite_coupled_control A initial hA hInv
    childCarryZero := hC0
    parentBad := hbad
    parentBadSuffix := coupledOrbit_parent_bad_suffix A initial hbad
    childCarryExact := coupledOrbit_childCarry_exact A initial hC0
  }

end GSTV2
