import Mathlib

/-!
# GST Round 52 — the all-degree loss polynomial and curvature specialization memory

The paired rational fold `B_α = A ⊗ Λ(u,v)`, `|u| = |v| = s = 2p−1`,
`du = α`, `dv = 0`, of the all-degree curvature duality record
(`research/records/2026-11-03-gst-all-degree-curvature-duality-specialization.md`)
is bookkept here by two new structures:

* `FoldRankData` — the rank profile (base Poincaré polynomial, cup-by-α rank
  polynomial, fold shift) with the exact all-degree conservation law
  `flat = fold + loss`, the no-loss-below-shift law, the unchanged-below-shift
  law, the first-loss-degree law, and the degree-one blindness of every
  codimension `p ≥ 2` fold;
* `JetFamily` — the parameter-dependent cochain family `d_ε = d + ε·φ` of the
  specialization-memory route, acting on first jets, whose square retains the
  full prescribed curvature exactly in the first jet and is exactly flat in
  the zeroth jet, with the flat ε = 0 face exhibited.

All statements are exact algebraic identities (ℚ[t] ring identities and
first-jet linear-map identities). The geometric identification of the paired
fold with actual cohomology stays in the companion hand derivation; no
original-X algebraic-source existence is claimed, assumed, or concluded
here. Flatness of the base and the memory law are supplied fields of the
family, exactly as in the derivation's equations (5)–(7).
-/

namespace GSTAllDegreeCurvatureMemory

open Polynomial

/-! ## Coefficient helpers for shifted polynomial products -/

theorem coeff_X_pow_mul_lt (q : Polynomial ℚ) (s n : ℕ) (h : n < s) :
    (X ^ s * q).coeff n = 0 := by
  rw [Polynomial.coeff_X_pow_mul' q s n]
  have hs : ¬(s ≤ n) := by omega
  rw [if_neg hs]

theorem coeff_X_pow_mul_self (q : Polynomial ℚ) (s : ℕ) :
    (X ^ s * q).coeff s = q.coeff 0 := by
  have h := Polynomial.coeff_X_pow_mul q s 0
  rwa [Nat.zero_add] at h

theorem coeff_one_add_X_zero : (1 + (X : Polynomial ℚ)).coeff 0 = 1 := by
  rw [Polynomial.coeff_add, Polynomial.coeff_one, Polynomial.coeff_X_zero]
  norm_num

theorem coeff_one_add_X_pow_zero (s : ℕ) (hs : 0 < s) :
    (1 + (X : Polynomial ℚ) ^ s).coeff 0 = 1 := by
  rw [Polynomial.coeff_add, Polynomial.coeff_one, Polynomial.coeff_X_pow]
  have h0 : ¬(0 = s) := by omega
  rw [if_neg h0]
  norm_num

/-! ## The rank profile and the exact all-degree loss polynomial -/

/-- The all-degree fold bookkeeping. Fields:

* `basePoly` — the Poincaré polynomial `P_A(t)` of the original rational cup
  algebra in the chosen grading;
* `cupPoly` — the rank polynomial `R_α(t)` of cup by the prescribed class in
  each original-base degree;
* `shift` — the fold shift `s = 2p − 1`;
* `shift_pos` — positivity of the shift (`p ≥ 1`);
* `cup_zero` — the degree-zero cup rank normalization, i.e. `α ≠ 0`. -/
structure FoldRankData where
  /-- Poincaré polynomial of the original base algebra. -/
  basePoly : Polynomial ℚ
  /-- Rank polynomial of cup by the prescribed class. -/
  cupPoly : Polynomial ℚ
  /-- The fold shift `s = 2p − 1`. -/
  shift : ℕ
  /-- Positivity of the fold shift. -/
  shift_pos : 0 < shift
  /-- The degree-zero cup rank normalization (`α ≠ 0`). -/
  cup_zero : cupPoly.coeff 0 = 1
deriving Repr

namespace FoldRankData

/-- The flat (`α = 0`) fold polynomial `(1 + t^s)^2 P_A(t)`. -/
noncomputable def flatPoly (D : FoldRankData) : Polynomial ℚ :=
  (1 + X ^ D.shift) ^ 2 * D.basePoly

/-- The paired-fold polynomial
`(1 + t^s)((1 + t^s)P_A(t) − (t^(s+1) + t^s)R_α(t))` of the record. -/
noncomputable def foldPoly (D : FoldRankData) : Polynomial ℚ :=
  (1 + X ^ D.shift) * ((1 + X ^ D.shift) * D.basePoly -
    (X ^ (D.shift + 1) + X ^ D.shift) * D.cupPoly)

/-- The exact all-degree loss polynomial `t^s(1 + t)(1 + t^s)R_α(t)`. -/
noncomputable def lossPoly (D : FoldRankData) : Polynomial ℚ :=
  X ^ D.shift * ((1 + X) * ((1 + X ^ D.shift) * D.cupPoly))

/-- **The exact all-degree conservation law.** The flat fold is the paired
fold plus the loss, coefficient for coefficient. -/
theorem flat_conservation (D : FoldRankData) :
    D.flatPoly = D.foldPoly + D.lossPoly := by
  simp only [flatPoly, foldPoly, lossPoly, pow_succ]
  ring

/-- **No loss below the fold shift.** Every degree `i < s` is exactly
unchanged: the loss polynomial has no support below the shift. -/
theorem loss_below_shift (D : FoldRankData) (i : ℕ) (h : i < D.shift) :
    D.lossPoly.coeff i = 0 := by
  simp only [lossPoly]
  exact coeff_X_pow_mul_lt _ D.shift i h

/-- **The fold is unchanged below the shift.** In every degree `i < s` the
paired-fold polynomial equals the flat fold polynomial exactly. -/
theorem fold_unchanged_below_shift (D : FoldRankData) (i : ℕ)
    (h : i < D.shift) :
    D.foldPoly.coeff i = D.flatPoly.coeff i := by
  rw [flat_conservation D, Polynomial.coeff_add,
    loss_below_shift D i h, add_zero]

/-- **The first lost degree is the shift, with loss exactly one.** Under the
`α ≠ 0` normalization the first lost class sits in degree `s` and exactly one
class is lost there. -/
theorem loss_at_shift (D : FoldRankData) :
    D.lossPoly.coeff D.shift = 1 := by
  simp only [lossPoly]
  rw [coeff_X_pow_mul_self, Polynomial.mul_coeff_zero,
    Polynomial.mul_coeff_zero, coeff_one_add_X_zero,
    coeff_one_add_X_pow_zero D.shift D.shift_pos, D.cup_zero]
  norm_num

/-- **The degree-one blindness law.** At codimension `p ≥ 2` the fold shift
is `2p − 1`, so the loss polynomial has no degree-one term: the degree-one
curvature test alone cannot see any `p ≥ 2` target fold, and the first
detecting degree is exactly `2p − 1`. -/
theorem degree_one_blind (D : FoldRankData) (p : ℕ)
    (hp : 2 ≤ p) (hshift : D.shift = 2 * p - 1) :
    D.lossPoly.coeff 1 = 0 := by
  have h1 : 1 < D.shift := by rw [hshift]; omega
  exact loss_below_shift D 1 h1

end FoldRankData

/-! ## The first-jet family and curvature specialization memory -/

variable {V : Type*} [AddCommGroup V] [Module ℚ V]

/-- The parameter-dependent cochain family `d_ε = d + ε·φ` of the
specialization-memory route. Fields:

* `base` — the flat base differential `d`;
* `base_square` — the flatness `d² = 0` of the base;
* `jet` — the memory jet `φ`, the ε-coefficient of the family;
* `curvature` — the prescribed curvature carrier `K`;
* `memory` — the memory law `{d, φ} = dφ + φd = K`.

The family acts on first jets `(x, y)` (standing for `x + εy`) by
`jetDifferential (x, y) = (dx, dy + φx)`. -/
structure JetFamily (V : Type*) [AddCommGroup V] [Module ℚ V] where
  /-- The flat base differential `d`. -/
  base : V →ₗ[ℚ] V
  /-- Flatness of the base: `d² = 0`. -/
  base_square : base.comp base = 0
  /-- The memory jet `φ`: the ε-coefficient of the family. -/
  jet : V →ₗ[ℚ] V
  /-- The prescribed curvature carrier `K`. -/
  curvature : V →ₗ[ℚ] V
  /-- The memory law: `dφ + φd = K`. -/
  memory : base.comp jet + jet.comp base = curvature

namespace JetFamily

/-- The family differential on first jets: `(x, y) ↦ (dx, dy + φx)`,
i.e. `(d + ε·φ)(x + εy) = dx + ε(dy + φx)`. -/
def jetDifferential (F : JetFamily V) : (V × V) →ₗ[ℚ] (V × V) :=
  LinearMap.prod (F.base ∘ₗ LinearMap.fst ℚ V V)
    (F.base ∘ₗ LinearMap.snd ℚ V V +
      F.jet ∘ₗ LinearMap.fst ℚ V V)

theorem jetDifferential_apply (F : JetFamily V) (x y : V) :
    F.jetDifferential (x, y) = (F.base x, F.base y + F.jet x) := by
  simp [jetDifferential, LinearMap.prod_apply, LinearMap.comp_apply,
    LinearMap.add_apply, LinearMap.fst_apply, LinearMap.snd_apply]

theorem base_square_apply (F : JetFamily V) (x : V) :
    F.base (F.base x) = 0 := by
  rw [← LinearMap.comp_apply, F.base_square, LinearMap.zero_apply]

theorem memory_apply (F : JetFamily V) (x : V) :
    F.base (F.jet x) + F.jet (F.base x) = F.curvature x := by
  rw [← LinearMap.comp_apply, ← LinearMap.comp_apply,
    ← LinearMap.add_apply, F.memory]

/-- **The zeroth jet of the square is zero:** the family is exactly flat at
`ε = 0`; switching the curvature off does not disturb the square's zeroth
component. -/
theorem jet_square_zeroth (F : JetFamily V) (x y : V) :
    (F.jetDifferential (F.jetDifferential (x, y))).1 = 0 := by
  simp only [jetDifferential_apply, base_square_apply]

/-- **The first jet of the square is exactly the curvature:** the
parameter-dependent family retains the full prescribed curvature in its
first jet, with the memory field supplying the anticommutator. -/
theorem jet_square_first (F : JetFamily V) (x y : V) :
    (F.jetDifferential (F.jetDifferential (x, y))).2 = F.curvature x := by
  simp only [jetDifferential_apply, map_add, base_square_apply,
    memory_apply, zero_add]

/-- **The full jet square, as one identity:** the family differential squares
to the curvature acting on the zeroth component only. -/
theorem jet_square (F : JetFamily V) (x y : V) :
    F.jetDifferential (F.jetDifferential (x, y)) = (0, F.curvature x) :=
  Prod.ext (jet_square_zeroth F x y) (jet_square_first F x y)

/-- **The flat ε = 0 face.** On the pure-ε fiber the family differential is
the flat base differential: the curvature is switched off while the memory
field `jet` still carries the full curvature data. -/
theorem jet_flat_face (F : JetFamily V) (y : V) :
    F.jetDifferential (0, y) = (0, F.base y) := by
  rw [jetDifferential_apply, F.base.map_zero, F.jet.map_zero, add_zero]

end JetFamily

end GSTAllDegreeCurvatureMemory

#print axioms GSTAllDegreeCurvatureMemory.FoldRankData.flat_conservation
#print axioms GSTAllDegreeCurvatureMemory.FoldRankData.loss_below_shift
#print axioms GSTAllDegreeCurvatureMemory.FoldRankData.fold_unchanged_below_shift
#print axioms GSTAllDegreeCurvatureMemory.FoldRankData.loss_at_shift
#print axioms GSTAllDegreeCurvatureMemory.FoldRankData.degree_one_blind
#print axioms GSTAllDegreeCurvatureMemory.JetFamily.jet_square_zeroth
#print axioms GSTAllDegreeCurvatureMemory.JetFamily.jet_square_first
#print axioms GSTAllDegreeCurvatureMemory.JetFamily.jet_square
#print axioms GSTAllDegreeCurvatureMemory.JetFamily.jet_flat_face
