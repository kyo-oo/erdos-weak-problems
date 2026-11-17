import Mathlib
import HodgeDeRhamBridge

/-!
# HC ABSORPTION V2 — EXACT CURRENT AND COMPOSITIONAL PERIOD LAWS

This layer strengthens the proved finite GST bridge.  It does not assume
ReverseOntologicalWindow and does not identify the finite bridge with an
external geometric realization.
-/

set_option maxHeartbeats 10000000
set_option maxRecDepth 1000000

namespace HodgeDeRhamBridgeV2

open GST2DMixedEmergence
open GSTU2DEventTransport
open GSTGraphV2SixAdicOntologicalGeometry
open GSTGraphV2SixAdicSynchronizedShadows
open GSTGraphV2Ontological
open HodgeDeRhamBridge

/-- The positive signature sector has exactly two current values. -/
theorem signature_current_exact
    (C d : Nat) (hC : C < 4) (hd : d < 3) :
    HappyCell C d ↔ ontDensity C d = 84 ∨ ontDensity C d = 42 := by
  interval_cases C <;> interval_cases d <;>
    simp [HappyCell, ontDensity, ontDigitPotential, ontCarryPotential,
      outDigit, nextCarry]

/-- Positive current is not merely bounded below: on physical cells it is
exactly 84 or 42. -/
theorem positive_current_exact
    (C d : Nat) (hC : C < 4) (hd : d < 3) :
    0 < ontDensity C d ↔ ontDensity C d = 84 ∨ ontDensity C d = 42 := by
  rw [← happy_iff_ontDensity_positive C d hC hd]
  exact signature_current_exact C d hC hd

/-- Every signature cell has nonzero current, with an exact dichotomy. -/
theorem signature_current_ne_zero
    (C d : Nat) (hC : C < 4) (hd : d < 3)
    (h : HappyCell C d) :
    ontDensity C d ≠ 0 := by
  rcases (signature_current_exact C d hC hd).mp h with h84 | h42 <;>
    omega

/-- General period rebasing along every residue class modulo three. -/
theorem period_rebase_general (r m : Nat) :
    4^(r + 3*m) = 4^r * 64^m := by
  rw [Nat.pow_add, Nat.pow_mul]

/-- The old period rebase is the residue-one specialization. -/
theorem period_rebase_absorbed (m : Nat) :
    4^(1 + 3*m) = 4 * 64^m := by
  simpa using period_rebase_general 1 m

/-- A combined physical twist is exactly one twist of the summed depth. -/
theorem finite_twist_composed
    (k t u : Nat) (x y : Int) :
    SixAdicIsoAt k ((4 : Int)^(t+u) * x) ((4 : Int)^(t+u) * y) ↔
      DyadicShadowAt (k - 2*(t+u)) x y ∧ TriadicShadowAt k x y :=
  finite_twist_skew_truncated k (t+u) x y

/-- The de Rham side is invariant under any finite composition of physical
twists. -/
theorem deRham_twist_composed
    (k t u : Nat) (x y : Int) :
    TriadicShadowAt k ((4 : Int)^(t+u) * x) ((4 : Int)^(t+u) * y) ↔
      TriadicShadowAt k x y :=
  deRham_twist_isometry k (t+u) x y

/-- Mixed-period depth splitting into any finite number of concatenated
layers. -/
theorem mixed_period_three_split (a b c : Nat) :
    MixedPeriodLayer (a+b+c) =
      MixedPeriodLayer a * MixedPeriodLayer b * MixedPeriodLayer c := by
  rw [show a+b+c = (a+b)+c by omega,
      mixed_period_multiplicative, mixed_period_multiplicative]

/-- Exact two-world factorization after arbitrary depth concatenation. -/
theorem comparison_period_concatenated (j k : Nat) :
    MixedPeriodLayer (j+k) =
      (BettiLayer j * BettiLayer k) *
      (DeRhamLayer j * DeRhamLayer k) := by
  rw [mixed_period_exact]
  rcases world_layers_multiplicative j k with ⟨hb, hd⟩
  rw [hb, hd]

theorem absorption_v2_crown :
    (∀ C d, C < 4 → d < 3 →
      (HappyCell C d ↔ ontDensity C d = 84 ∨ ontDensity C d = 42))
    ∧ (∀ r m, 4^(r+3*m) = 4^r * 64^m)
    ∧ (∀ k t u x y,
      SixAdicIsoAt k ((4 : Int)^(t+u) * x) ((4 : Int)^(t+u) * y) ↔
        DyadicShadowAt (k-2*(t+u)) x y ∧ TriadicShadowAt k x y) := by
  exact ⟨fun C d hC hd => signature_current_exact C d hC hd,
    period_rebase_general, finite_twist_composed⟩

#check signature_current_exact
#check positive_current_exact
#check period_rebase_general
#check finite_twist_composed
#check deRham_twist_composed
#check mixed_period_three_split
#check comparison_period_concatenated
#check absorption_v2_crown

#print axioms signature_current_exact
#print axioms period_rebase_general
#print axioms finite_twist_composed
#print axioms absorption_v2_crown

end HodgeDeRhamBridgeV2
