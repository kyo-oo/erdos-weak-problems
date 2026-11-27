import Mathlib

/-!
# GST CLASSICAL HODGE — REPAIR TOOLKIT

Distilled from the SB repair waves (SB-98 … SB-109): the lemma shapes that
recurred in every broken round of the classical Hodge lane.

* the nonzero-scalar endomorphism normalization (the two-slot Lefschetz
  firing pattern `c⁻¹ • (c • F) = F`), which raw `simp` leaves as the
  `c⁻¹ * c` residual on the pointwise form;
* the pointwise smul/comp transport shapes that `rw` misses on
  `Module.End` but `exact` closes by default-transparency defeq.

These lemmas are universe-polymorphic in the carrier and require only the
ℚ-module structure, so every classical-Hodge file can import this toolkit
without pulling any scheme-level data.
-/

set_option maxHeartbeats 10000000
set_option maxRecDepth 500000

namespace GSTClassicalHodgeRepairToolkit

variable {M : Type*} [AddCommGroup M] [Module ℚ M]

/-- **THE TWO-SLOT NORMALIZATION LAW.**
A nonzero scalar prefactor cancels on endomorphism words:
`c⁻¹ • (c • F) = F`.  This is the exact shape of the bare-Lefschetz
matrix-unit equation, and closes the residual that `simp` leaves behind
(`(c⁻¹ * c) • x` on the elementwise form). -/
theorem inv_smul_smul_End {c : ℚ} (hc : c ≠ 0) (F : M →ₗ[ℚ] M) :
    c⁻¹ • (c • F) = F := by
  rw [smul_smul, inv_mul_cancel₀ hc, one_smul]

/-- Mirror direction of the normalization law:
`c • (c⁻¹ • F) = F` for nonzero `c`. -/
theorem smul_inv_smul_End {c : ℚ} (hc : c ≠ 0) (F : M →ₗ[ℚ] M) :
    c • (c⁻¹ • F) = F := by
  rw [smul_smul, mul_inv_cancel₀ hc, one_smul]

/-- **POINTWISE SMUL TRANSPORT.**  `(c • F) x = c • (F x)` by reflexivity —
the application-level bridge that raw `rw [LinearMap.smul_apply]` misses
when the coercion head is hidden behind a `Module.End` abbreviation. -/
theorem smul_End_apply (c : ℚ) (F : M →ₗ[ℚ] M) (x : M) :
    (c • F) x = c • (F x) :=
  rfl

/-- **COMP-SMUL WORD TRANSPORT.**  Scaling the middle of a composed word
equals scaling the composite — the shape the arsenal-word reductions need
when the smul sits between two applications. -/
theorem smul_comp_middle (c : ℚ) (F G : M →ₗ[ℚ] M) :
    (c • F).comp G = c • (F.comp G) := by
  ext x
  simp [smul_End_apply]

/-- **DOUBLE-SMUL COMPOSE.**  `(c • F).comp (c • G)` on a module where the
scalar already lives — the geometry-first word re-association shape. -/
theorem smul_comp_smul (c : ℚ) (F G : M →ₗ[ℚ] M) :
    ((c • F).comp (c • G)) = (c * c) • (F.comp G) := by
  ext x
  simp [smul_End_apply, smul_smul]

section V2

/-! ## V2 — the SB-121/122 weapon distillation

The second distillation wave: the map-zero contrapositive that the
separator-defect detector bridges need, and the Finsupp single-sum scalar
transport battery that every `φ.sum (fun ix s => s • T ix)`-shaped linear
lift needs for its `map_smul'`/`map_add'` fields. -/

/-- **MAP-ZERO CONTRAPOSITIVE.**  A linear map that does not vanish on `x`
certifies `x ≠ 0` — the detector-bridge closing the `atom_defect_ne_zero`
family: nonvanishing of `f x` is cheaper to establish than nonvanishing of
`x` itself. -/
theorem ne_zero_of_map_ne_zero {N : Type*} [AddCommGroup N] [Module ℚ N]
    (f : M →ₗ[ℚ] N) (x : M) (h : f x ≠ 0) : x ≠ 0 :=
  fun hzero => h (by rw [hzero, map_zero])

/-- **FINSUPP SINGLE-SUM SCALAR TRANSPORT.**  The sum of a scalar-weighted
point family over a single-index finsupp is the weight times the point —
the `map_smul'` single-case in one application.  The side condition of
`Finsupp.sum_single_index` is discharged by `zero_smul`. -/
theorem sum_single_smul_transport {α : Type*} {β : Type*} [AddCommGroup β]
    [Module ℚ β] (i : α) (t : ℚ) (T : α → β) :
    (Finsupp.single i t).sum (fun ix s => s • T ix) = t • T i :=
  Finsupp.sum_single_index (a := i) (b := t)
    (h := fun ix s => s • T ix) (by simp)

/-- **FINSUPP SINGLE SMUL.**  Scaling a single-index finsupp is the single
with the scaled weight — the pointwise-ℚ instance form. -/
theorem smul_single_eq {α : Type*} (q c : ℚ) (i : α) :
    q • Finsupp.single i c = Finsupp.single i (q * c) := by
  ext j
  by_cases hj : j = i
  · subst hj
    simp
  · simp [hj]

/-- **SCALAR LINEARITY OF A FINSUPP-SUM LIFT.**  The `map_smul'` field of
any `φ.sum (fun ix s => s • T ix)`-shaped linear lift closes in one
rewrite. -/
theorem sum_lift_map_smul {α β : Type*} [AddCommGroup β] [Module ℚ β]
    (T : α → β) (q : ℚ) (φ : α →₀ ℚ) :
    (q • φ).sum (fun ix s => s • T ix) = q • φ.sum (fun ix s => s • T ix) := by
  classical
  induction φ using Finsupp.induction_linear with
  | zero =>
      rw [smul_zero]
      simp only [Finsupp.sum, Finsupp.support_zero, Finset.sum_empty,
        smul_zero]
  | add a b ha hb =>
      simp [ha, hb, add_smul, Finsupp.sum_add_index']
  | single i c =>
      rw [smul_single_eq, sum_single_smul_transport,
        sum_single_smul_transport, smul_smul]

end V2

end GSTClassicalHodgeRepairToolkit

#check GSTClassicalHodgeRepairToolkit.inv_smul_smul_End
#check GSTClassicalHodgeRepairToolkit.smul_inv_smul_End
#check GSTClassicalHodgeRepairToolkit.smul_End_apply
#check GSTClassicalHodgeRepairToolkit.smul_comp_middle
#check GSTClassicalHodgeRepairToolkit.smul_comp_smul
#check GSTClassicalHodgeRepairToolkit.ne_zero_of_map_ne_zero
#check GSTClassicalHodgeRepairToolkit.sum_single_smul_transport
#check GSTClassicalHodgeRepairToolkit.smul_single_eq
#check GSTClassicalHodgeRepairToolkit.sum_lift_map_smul

#print axioms GSTClassicalHodgeRepairToolkit.ne_zero_of_map_ne_zero
#print axioms GSTClassicalHodgeRepairToolkit.sum_single_smul_transport
#print axioms GSTClassicalHodgeRepairToolkit.smul_single_eq
#print axioms GSTClassicalHodgeRepairToolkit.sum_lift_map_smul
