import Mathlib
import GSTAllDegreeCurvatureMemory

/-!
# GST Round 53 — the second-order memory tower and the composed-fold transport law

Round 52 (`GSTAllDegreeCurvatureMemory`) bookkept the paired rational fold by
the rank profile (`FoldRankData`, the exact all-degree conservation law
`flat = fold + loss`) and the first-jet specialization memory (`JetFamily`,
the family `d_ε = d + ε·φ` whose first jet retains the full prescribed
curvature). This round extends both faces one level up:

* `JetTower` — the second-order memory tower. The parameter family
  `d + ε·φ + ε²·χ` acts on second jets `(x, y, z)` (standing for
  `x + ε·y + ε²·z`) by `(dx, dy + φx, dz + χx + φy)`. New fields: the
  second memory jet `χ`, the second-order curvature carrier, and the
  second-order memory law `dχ + χd + φ² = K₂`. The tower square is
  `(0, K₁x, K₂x + K₁y)`: the curvature is retained one level up and the
  first curvature propagates to the top level; the flat criterion and both
  extraction directions are proved.
* `FoldComposition` — the composed-fold transport. Two successive paired
  folds (shifts `s`, `s'`) satisfy the exact double conservation law
  `double-flat = double-fold + total-loss`, where the total loss carries
  the second fold's own loss plus the first fold's loss transported by the
  second flat factor; below both shifts nothing is lost, the composed first
  lost degree is the first shift with loss exactly one, and the composed
  degree-one blindness holds at codimensions `p, q ≥ 2`.

All statements are exact algebraic identities (ℚ[t] ring identities and
second-jet linear-map identities). The geometric identification of the
tower or of the composed fold with actual cohomology stays in the
companion record; no original-X algebraic-source existence is claimed,
assumed, or concluded here. Flatness of the base and both memory laws are
supplied fields of the structures, exactly as in Round 52's equations.
-/

namespace GSTFoldMemoryTower

open Polynomial

open GSTAllDegreeCurvatureMemory (coeff_X_pow_mul_lt coeff_X_pow_mul_self
  coeff_one_add_X_zero coeff_one_add_X_pow_zero)

/-! ## The second-order memory tower -/

variable {V : Type*} [AddCommGroup V] [Module ℚ V]

/-- The second-order memory tower of the specialization-memory route.
Fields:

* `base` — the flat base differential `d`;
* `base_square` — the flatness `d² = 0` of the base;
* `jet` — the first memory jet `φ`, the ε-coefficient of the family;
* `curvature` — the first prescribed curvature carrier `K₁`;
* `memory` — the first memory law `{d, φ} = dφ + φd = K₁`;
* `second` — the second memory jet `χ`, the ε²-coefficient of the family;
* `second_curvature` — the second-order curvature carrier `K₂`;
* `second_memory` — the second-order memory law
  `dχ + χd + φ² = K₂`.

The family `d + ε·φ + ε²·χ` acts on second jets `(x, y, z)` (standing for
`x + ε·y + ε²·z`) by `towerDifferential (x, y, z) = (dx, dy + φx,
dz + χx + φy)`. -/
structure JetTower (V : Type*) [AddCommGroup V] [Module ℚ V] where
  /-- The flat base differential `d`. -/
  base : V →ₗ[ℚ] V
  /-- Flatness of the base: `d² = 0`. -/
  base_square : base.comp base = 0
  /-- The first memory jet `φ`: the ε-coefficient of the family. -/
  jet : V →ₗ[ℚ] V
  /-- The first prescribed curvature carrier `K₁`. -/
  curvature : V →ₗ[ℚ] V
  /-- The first memory law: `dφ + φd = K₁`. -/
  memory : base.comp jet + jet.comp base = curvature
  /-- The second memory jet `χ`: the ε²-coefficient of the family. -/
  second : V →ₗ[ℚ] V
  /-- The second-order curvature carrier `K₂`. -/
  second_curvature : V →ₗ[ℚ] V
  /-- The second-order memory law: `dχ + χd + φ² = K₂`. -/
  second_memory : base.comp second + second.comp base + jet.comp jet
    = second_curvature

namespace JetTower

/-- The tower differential on second jets: `(x, y, z) ↦ (dx, dy + φx,
dz + χx + φy)`, i.e. `(d + ε·φ + ε²·χ)(x + ε·y + ε²·z) =
dx + ε(dy + φx) + ε²(dz + χx + φy)` up to the ε³ truncation. -/
def towerDifferential (T : JetTower V) : (V × V × V) →ₗ[ℚ] (V × V × V) :=
  LinearMap.prod
    (T.base ∘ₗ LinearMap.fst ℚ V (V × V))
    (LinearMap.prod
      (T.base ∘ₗ ((LinearMap.fst ℚ V V) ∘ₗ (LinearMap.snd ℚ V (V × V)))
        + T.jet ∘ₗ LinearMap.fst ℚ V (V × V))
      (T.base ∘ₗ ((LinearMap.snd ℚ V V) ∘ₗ (LinearMap.snd ℚ V (V × V)))
        + T.jet ∘ₗ ((LinearMap.fst ℚ V V) ∘ₗ (LinearMap.snd ℚ V (V × V)))
        + T.second ∘ₗ LinearMap.fst ℚ V (V × V)))

theorem towerDifferential_apply (T : JetTower V) (x y z : V) :
    T.towerDifferential (x, y, z) =
      (T.base x, T.base y + T.jet x, T.base z + T.second x + T.jet y) := by
  simp [towerDifferential, LinearMap.prod_apply, LinearMap.comp_apply,
    LinearMap.add_apply, LinearMap.fst_apply, LinearMap.snd_apply]
  abel

theorem base_square_apply (T : JetTower V) (x : V) :
    T.base (T.base x) = 0 := by
  rw [← LinearMap.comp_apply, T.base_square, LinearMap.zero_apply]

theorem memory_apply (T : JetTower V) (x : V) :
    T.base (T.jet x) + T.jet (T.base x) = T.curvature x := by
  rw [← LinearMap.comp_apply, ← LinearMap.comp_apply,
    ← LinearMap.add_apply, T.memory]

theorem second_memory_apply (T : JetTower V) (x : V) :
    T.base (T.second x) + T.second (T.base x) + T.jet (T.jet x)
      = T.second_curvature x := by
  rw [← LinearMap.comp_apply, ← LinearMap.comp_apply, ← LinearMap.comp_apply,
    ← LinearMap.add_apply, ← LinearMap.add_apply, T.second_memory]

/-- **The zeroth jet of the tower square is zero:** the family is exactly
flat at `ε = 0`; switching both curvature levels off does not disturb the
square's zeroth component. -/
theorem tower_square_zeroth (T : JetTower V) (x y z : V) :
    (T.towerDifferential (T.towerDifferential (x, y, z))).1 = 0 := by
  simp only [towerDifferential_apply, base_square_apply]

/-- **The curvature is retained one level up.** The first jet component of
the tower square is exactly the first prescribed curvature: the
specialization memory of Round 52 survives the tower extension unchanged. -/
theorem tower_square_first (T : JetTower V) (x y z : V) :
    (T.towerDifferential (T.towerDifferential (x, y, z))).2.1
      = T.curvature x := by
  simp only [towerDifferential_apply, map_add, base_square_apply,
    memory_apply, zero_add]

/-- **The first curvature propagates to the top level.** The second jet
component of the tower square is the second-order curvature plus the first
curvature transported to the next input level: every level of the tower
sees the curvature of the level below. -/
theorem tower_square_second (T : JetTower V) (x y z : V) :
    (T.towerDifferential (T.towerDifferential (x, y, z))).2.2
      = T.second_curvature x + T.curvature y := by
  simp only [towerDifferential_apply, map_add, base_square_apply]
  have h1 : T.base (T.jet y) + T.jet (T.base y) = T.curvature y :=
    memory_apply T y
  have h2 : T.base (T.second x) + T.second (T.base x) + T.jet (T.jet x)
      = T.second_curvature x := second_memory_apply T x
  rw [← h1, ← h2]
  abel

/-- **The full tower square, as one identity:** the tower differential
squares to `(0, K₁x, K₂x + K₁y)` — the curvature pair acting level by
level, with the memory tail `φ²` absorbed into `K₂` by the second-order
memory law. -/
theorem tower_square (T : JetTower V) (x y z : V) :
    T.towerDifferential (T.towerDifferential (x, y, z))
      = (0, T.curvature x, T.second_curvature x + T.curvature y) :=
  Prod.ext (tower_square_zeroth T x y z)
    (Prod.ext (tower_square_first T x y z) (tower_square_second T x y z))

/-- **The flat ε = 0 face of the tower.** On the pure-ε² fiber the tower
differential is the flat base differential: both curvature levels are
switched off while both memory fields still carry the full curvature
data. -/
theorem tower_flat_face (T : JetTower V) (z : V) :
    T.towerDifferential (0, 0, z) = (0, 0, T.base z) := by
  rw [towerDifferential_apply, T.base.map_zero, T.jet.map_zero,
    T.second.map_zero]
  simp

/-- **The flat-tower criterion, sufficiency.** If both curvature levels
vanish identically, the tower differential squares to zero on every
second jet. -/
theorem tower_flat_of_curvatures_zero (T : JetTower V)
    (h1 : ∀ w, T.curvature w = 0) (h2 : ∀ w, T.second_curvature w = 0)
    (x y z : V) :
    T.towerDifferential (T.towerDifferential (x, y, z)) = (0, 0, 0) := by
  rw [tower_square T x y z, h1 x, h2 x, h1 y]
  simp

/-- **The flat-tower criterion, first extraction.** If the tower squares
to zero on every second jet, the first curvature carrier vanishes
identically. -/
theorem curvature_of_flat_tower (T : JetTower V)
    (h : ∀ x y z, T.towerDifferential (T.towerDifferential (x, y, z))
      = (0, 0, 0)) (x : V) :
    T.curvature x = 0 := by
  have h2 : (T.towerDifferential (T.towerDifferential (x, 0, 0))).2.1
      = T.curvature x := tower_square_first T x 0 0
  rw [h x 0 0] at h2
  exact h2.symm

/-- **The flat-tower criterion, second extraction.** If the tower squares
to zero on every second jet, the second-order curvature carrier vanishes
identically (using the first extraction to clear the transported term). -/
theorem second_curvature_of_flat_tower (T : JetTower V)
    (h : ∀ x y z, T.towerDifferential (T.towerDifferential (x, y, z))
      = (0, 0, 0)) (x : V) :
    T.second_curvature x = 0 := by
  have hc : T.curvature x = 0 := curvature_of_flat_tower T h x
  have h2 : (T.towerDifferential (T.towerDifferential (x, x, x))).2.2
      = T.second_curvature x + T.curvature x := tower_square_second T x x x
  rw [h x x x] at h2
  rw [hc, add_zero] at h2
  exact h2.symm

end JetTower

/-! ## The composed-fold transport law -/

/-- The paired-fold polynomial of a base `P`, cup rank polynomial `R` and
shift `s`: `(1 + t^s)((1 + t^s)P − (t^(s+1) + t^s)R)`. -/
noncomputable def foldOf (P R : Polynomial ℚ) (s : ℕ) : Polynomial ℚ :=
  (1 + X ^ s) * ((1 + X ^ s) * P - (X ^ (s + 1) + X ^ s) * R)

/-- The loss polynomial of a cup rank polynomial `R` and shift `s`:
`t^s(1 + t)(1 + t^s)R`. -/
noncomputable def lossOf (R : Polynomial ℚ) (s : ℕ) : Polynomial ℚ :=
  X ^ s * ((1 + X) * ((1 + X ^ s) * R))

/-- **The universal single-fold conservation law.** For every base, cup
rank polynomial and shift, the flat fold decomposes exactly as the paired
fold plus the loss — the Round 52 conservation law, freed of its record
fields so it can be iterated. -/
theorem conservationOf (P R : Polynomial ℚ) (s : ℕ) :
    (1 + X ^ s) ^ 2 * P = foldOf P R s + lossOf R s := by
  simp only [foldOf, lossOf, pow_succ]
  ring

/-- **The universal double-fold conservation law.** For two successive
paired folds with shifts `s`, `s'`, the double flat
`(1 + t^s')²(1 + t^s)²P` decomposes exactly as the double fold plus the
total loss, where the total loss is the second fold's own loss plus the
first fold's loss transported by the second flat factor. -/
theorem double_conservationOf (P R R' : Polynomial ℚ) (s s' : ℕ) :
    (1 + X ^ s') ^ 2 * ((1 + X ^ s) ^ 2 * P)
      = foldOf (foldOf P R s) R' s'
        + (lossOf R' s'
          + X ^ s * ((1 + X ^ s') ^ 2 * ((1 + X) * ((1 + X ^ s) * R)))) := by
  have h1 := conservationOf P R s
  have h2 := conservationOf (foldOf P R s) R' s'
  calc (1 + X ^ s') ^ 2 * ((1 + X ^ s) ^ 2 * P)
      = (1 + X ^ s') ^ 2 * (foldOf P R s + lossOf R s) := by rw [h1]
    _ = (1 + X ^ s') ^ 2 * (foldOf P R s)
        + (1 + X ^ s') ^ 2 * lossOf R s := by rw [mul_add]
    _ = (foldOf (foldOf P R s) R' s' + lossOf R' s')
        + (1 + X ^ s') ^ 2 * lossOf R s := by rw [h2]
    _ = foldOf (foldOf P R s) R' s'
        + (lossOf R' s'
          + X ^ s * ((1 + X ^ s') ^ 2 * ((1 + X) * ((1 + X ^ s) * R)))) := by
        have h3 : (1 + X ^ s') ^ 2 * lossOf R s
            = X ^ s * ((1 + X ^ s') ^ 2 * ((1 + X) * ((1 + X ^ s) * R))) := by
          simp only [lossOf]
          ring
        rw [h3]
        ring

/-- The composed-fold bookkeeping. Fields:

* `base` — the Poincaré polynomial `P_A(t)` of the original rational cup
  algebra;
* `cup` — the rank polynomial `R_α(t)` of cup by the first prescribed
  class;
* `cup2` — the rank polynomial `R'_β(t)` of cup by the second prescribed
  class;
* `shift` — the first fold shift `s = 2p − 1`;
* `shift2` — the second fold shift `s' = 2q − 1`;
* `shift_pos` — positivity of the first shift (`p ≥ 1`);
* `shift2_pos` — positivity of the second shift (`q ≥ 1`);
* `cup_zero` — the first fold's degree-zero cup rank normalization;
* `cup2_zero` — the second fold's degree-zero cup rank normalization. -/
structure FoldComposition where
  /-- Poincaré polynomial of the original base algebra. -/
  base : Polynomial ℚ
  /-- Rank polynomial of cup by the first prescribed class. -/
  cup : Polynomial ℚ
  /-- Rank polynomial of cup by the second prescribed class. -/
  cup2 : Polynomial ℚ
  /-- The first fold shift `s = 2p − 1`. -/
  shift : ℕ
  /-- The second fold shift `s' = 2q − 1`. -/
  shift2 : ℕ
  /-- Positivity of the first fold shift. -/
  shift_pos : 0 < shift
  /-- Positivity of the second fold shift. -/
  shift2_pos : 0 < shift2
  /-- The first fold's degree-zero cup rank normalization. -/
  cup_zero : cup.coeff 0 = 1
  /-- The second fold's degree-zero cup rank normalization. -/
  cup2_zero : cup2.coeff 0 = 1
deriving Repr

namespace FoldComposition

/-- The double flat fold `(1 + t^s')²(1 + t^s)²P_A(t)`. -/
noncomputable def doubleFlat (C : FoldComposition) : Polynomial ℚ :=
  (1 + X ^ C.shift2) ^ 2 * ((1 + X ^ C.shift) ^ 2 * C.base)

/-- The twice-folded polynomial: the second paired fold applied to the
first. -/
noncomputable def doubleFold (C : FoldComposition) : Polynomial ℚ :=
  foldOf (foldOf C.base C.cup C.shift) C.cup2 C.shift2

/-- The second fold's own loss `t^s'(1+t)(1+t^s')R'_β(t)`. -/
noncomputable def secondLoss (C : FoldComposition) : Polynomial ℚ :=
  lossOf C.cup2 C.shift2

/-- The first fold's loss, transported by the second flat factor
(peeled monomial-first for coefficient work):
`t^s(1+t^s')²(1+t)(1+t^s)R_α(t)`. -/
noncomputable def transportedLoss (C : FoldComposition) : Polynomial ℚ :=
  X ^ C.shift * ((1 + X ^ C.shift2) ^ 2 * ((1 + X) * ((1 + X ^ C.shift) * C.cup)))

/-- The total loss of the composition. -/
noncomputable def totalLoss (C : FoldComposition) : Polynomial ℚ :=
  secondLoss C + transportedLoss C

/-- **The exact double conservation law.** The double flat fold is the
double fold plus the total loss, coefficient for coefficient — the
composed-fold transport law. -/
theorem double_conservation (C : FoldComposition) :
    C.doubleFlat = C.doubleFold + C.totalLoss :=
  double_conservationOf C.base C.cup C.cup2 C.shift C.shift2

/-- **No loss below either shift.** Every degree below both fold shifts is
exactly unchanged by the composition: the total loss polynomial has no
support below `min(s, s')`. -/
theorem total_loss_below_min (C : FoldComposition) (i : ℕ)
    (h1 : i < C.shift) (h2 : i < C.shift2) :
    C.totalLoss.coeff i = 0 := by
  simp only [totalLoss, secondLoss, transportedLoss, lossOf,
    Polynomial.coeff_add]
  rw [coeff_X_pow_mul_lt _ C.shift2 i h2, coeff_X_pow_mul_lt _ C.shift i h1]
  norm_num

/-- **The double fold is unchanged below either shift.** In every degree
below both shifts the double-fold polynomial equals the double flat
polynomial exactly. -/
theorem double_fold_unchanged_below_min (C : FoldComposition) (i : ℕ)
    (h1 : i < C.shift) (h2 : i < C.shift2) :
    C.doubleFold.coeff i = C.doubleFlat.coeff i := by
  rw [double_conservation C, Polynomial.coeff_add,
    total_loss_below_min C i h1 h2, add_zero]

/-- **The composed first lost degree is the first shift, with loss
exactly one.** When the first shift is strictly below the second, the
total loss's leading term is the transported first loss: exactly one
class lost in degree `s`, undisturbed by the second fold. -/
theorem double_first_loss (C : FoldComposition) (h : C.shift < C.shift2) :
    C.totalLoss.coeff C.shift = 1 := by
  simp only [totalLoss, secondLoss, transportedLoss, lossOf,
    Polynomial.coeff_add]
  rw [coeff_X_pow_mul_lt _ C.shift2 C.shift h, zero_add, coeff_X_pow_mul_self,
    pow_two, Polynomial.mul_coeff_zero, Polynomial.mul_coeff_zero,
    Polynomial.mul_coeff_zero, Polynomial.mul_coeff_zero,
    coeff_one_add_X_pow_zero C.shift2 C.shift2_pos, coeff_one_add_X_zero,
    coeff_one_add_X_pow_zero C.shift C.shift_pos, C.cup_zero]
  norm_num

/-- **The composed degree-one blindness law.** At codimensions `p, q ≥ 2`
the fold shifts are `2p − 1` and `2q − 1`, so the total loss has no
degree-one term: the degree-one curvature test alone cannot see any
composed `p, q ≥ 2` fold, and the first detecting degree is exactly
`min(2p − 1, 2q − 1)`. -/
theorem double_degree_one_blind (C : FoldComposition) (p q : ℕ)
    (hp : 2 ≤ p) (hq : 2 ≤ q) (hs : C.shift = 2 * p - 1)
    (hs2 : C.shift2 = 2 * q - 1) :
    C.totalLoss.coeff 1 = 0 := by
  have h1 : 1 < C.shift := by rw [hs]; omega
  have h2 : 1 < C.shift2 := by rw [hs2]; omega
  exact total_loss_below_min C 1 h1 h2

end FoldComposition

end GSTFoldMemoryTower

#print axioms GSTFoldMemoryTower.JetTower.towerDifferential_apply
#print axioms GSTFoldMemoryTower.JetTower.tower_square_zeroth
#print axioms GSTFoldMemoryTower.JetTower.tower_square_first
#print axioms GSTFoldMemoryTower.JetTower.tower_square_second
#print axioms GSTFoldMemoryTower.JetTower.tower_square
#print axioms GSTFoldMemoryTower.JetTower.tower_flat_face
#print axioms GSTFoldMemoryTower.JetTower.tower_flat_of_curvatures_zero
#print axioms GSTFoldMemoryTower.JetTower.curvature_of_flat_tower
#print axioms GSTFoldMemoryTower.JetTower.second_curvature_of_flat_tower
#print axioms GSTFoldMemoryTower.conservationOf
#print axioms GSTFoldMemoryTower.double_conservationOf
#print axioms GSTFoldMemoryTower.FoldComposition.double_conservation
#print axioms GSTFoldMemoryTower.FoldComposition.total_loss_below_min
#print axioms GSTFoldMemoryTower.FoldComposition.double_fold_unchanged_below_min
#print axioms GSTFoldMemoryTower.FoldComposition.double_first_loss
#print axioms GSTFoldMemoryTower.FoldComposition.double_degree_one_blind
