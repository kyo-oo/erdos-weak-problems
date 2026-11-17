import Mathlib
import GSTAnalyticAbsorption
import HodgeDeRhamBridgeV2

/-!
# ANALYTIC CROWN V2 — FUNCTORIAL TRANSPORT AND TWIST TOWERS

This layer strengthens the existing analytic objects by proving their
composition laws.  It does not add a new geometric interpretation.
-/

set_option maxHeartbeats 10000000
set_option maxRecDepth 1000000

namespace GSTAnalyticAbsorptionV2

open AddCircle
open MeasureTheory
open GSTAnalyticAbsorption
open scoped ComplexConjugate

/-- The period map is equivariant under every natural multiplier, not just
physical powers of four. -/
theorem hc_period_transport_nat (n R : Nat) :
    hcPeriod (n * R) = (n : ℤ) • hcPeriod R := by
  simp only [hcPeriod]
  rw [← AddCircle.coe_zsmul, zsmul_eq_mul]
  congr 1
  push_cast
  ring

/-- Period transport composes exactly with multiplication of re-encodings. -/
theorem hc_period_transport_compose (m n R : Nat) :
    hcPeriod (m * (n * R)) =
      (m : ℤ) • ((n : ℤ) • hcPeriod R) := by
  rw [hc_period_transport_nat, hc_period_transport_nat]

/-- The old physical transport is a specialization of arbitrary multiplier
equivariance. -/
theorem hc_period_transport_absorbed (t R : Nat) :
    hcPeriod (4^t * R) = (4^t : ℤ) • hcPeriod R :=
  hc_period_transport_nat (4^t) R

/-- **DESCENT SEMIGROUP.**  Descending a levels and then b levels is
identically one descent of depth a+b. -/
theorem hc_descent_flow_add (a b : Nat) :
    (fun x : ℝ => (x / (3:ℝ)^a) / (3:ℝ)^b) =
      (fun x : ℝ => x / (3:ℝ)^(a+b)) := by
  funext x
  rw [pow_add]
  field_simp

/-- Every composed descent remains smooth. -/
theorem hc_descent_flow_composed_smooth (a b : Nat) :
    ContDiff ℝ ⊤ (fun x : ℝ => (x / (3:ℝ)^a) / (3:ℝ)^b) := by
  rw [hc_descent_flow_add]
  exact hc_descent_flow_iterate_smooth (a+b)

/-- The physical twist groups form an exact nested tower by depth. -/
theorem hc_physical_tate_tower (t u : Nat) :
    rootsOfUnity (4^t) ℂ ≤ rootsOfUnity (4^(t+u)) ℂ := by
  apply hc_tate_filtration
  refine ⟨4^u, ?_⟩
  rw [pow_add]

/-- Every earlier finite twist embeds into every later twist level. -/
theorem hc_physical_tate_tower_monotone
    {t s : Nat} (h : t ≤ s) :
    rootsOfUnity (4^t) ℂ ≤ rootsOfUnity (4^s) ℂ := by
  obtain ⟨u,rfl⟩ := Nat.exists_eq_add_of_le h
  exact hc_physical_tate_tower t u

/-- Cyclotomic twist rank quadruples at each additional physical twist. -/
theorem hc_cyclotomic_degree_succ (t : Nat) (ht : 1 ≤ t) :
    (Polynomial.cyclotomic (4^(t+1)) ℚ).natDegree =
      4 * (Polynomial.cyclotomic (4^t) ℚ).natDegree := by
  rw [hc_cyclotomic_tate_degree (t+1) (by omega),
      hc_cyclotomic_tate_degree t ht]
  have h1 : 2 * (t+1) - 1 = (2*t - 1) + 2 := by omega
  rw [h1, pow_add]
  norm_num
  ring

/-- Generalized analytic rebase on every residue class modulo three. -/
theorem hc_period_rebase_real_general (r m : Nat) :
    (4 : ℝ)^(r + 3*m) = (4:ℝ)^r * (64:ℝ)^m := by
  rw [pow_add, pow_mul]
  norm_num

/-- Every generalized rebased tower point has transcendental matter in every
positive-radius neighborhood. -/
theorem hc_rebased_window_transcendental
    (r m k : Nat) (ε : ℝ) (hε : 0 < ε) :
    ∃ y : ℝ, Transcendental ℤ y ∧
      |y - ((4:ℝ)^r * (64:ℝ)^m / (3:ℝ)^k)| < ε := by
  exact hc_transcendental_nearby _ ε hε

theorem analytic_v2_crown :
    (∀ n R, hcPeriod (n*R) = (n:ℤ) • hcPeriod R)
    ∧ (∀ a b,
      (fun x : ℝ => (x/(3:ℝ)^a)/(3:ℝ)^b) =
        (fun x : ℝ => x/(3:ℝ)^(a+b)))
    ∧ (∀ t u,
      rootsOfUnity (4^t) ℂ ≤ rootsOfUnity (4^(t+u)) ℂ) := by
  exact ⟨hc_period_transport_nat, hc_descent_flow_add,
    hc_physical_tate_tower⟩

#check hc_period_transport_nat
#check hc_period_transport_compose
#check hc_descent_flow_add
#check hc_descent_flow_composed_smooth
#check hc_physical_tate_tower
#check hc_physical_tate_tower_monotone
#check hc_cyclotomic_degree_succ
#check hc_period_rebase_real_general
#check hc_rebased_window_transcendental
#check analytic_v2_crown

#print axioms hc_period_transport_nat
#print axioms hc_descent_flow_add
#print axioms hc_physical_tate_tower
#print axioms hc_cyclotomic_degree_succ
#print axioms analytic_v2_crown

end GSTAnalyticAbsorptionV2
