import Mathlib
import GSTFoldChainThirdOrderMemory

/-!
# GST Round 55 — the fourth-order memory tower and the arbitrary-order tower law

Round 53 (`GSTFoldMemoryTower`) built the second-order memory tower
(`d + ε·φ + ε²·χ`, the law `dχ + χd + φ² = K₂`); Round 54
(`GSTFoldChainThirdOrderMemory`) built the third-order tower
(`d + ε·φ + ε²·χ + ε³·ψ`, the law `dψ + ψd + φχ + χφ = K₃`). This
round closes the tower series in both directions at once — one explicit
level up, and the general law that subsumes every level:

* `JetTower4` — the fourth-order memory tower. The parameter family
  `d + ε·φ + ε²·χ + ε³·ψ + ε⁴·ω` acts on fourth jets `(v, w, x, y, z)`
  (standing for `v + ε·w + ε²·x + ε³·y + ε⁴·z`) by
  `(dv, dw + φv, dx + χv + φw, dy + ψv + χw + φx,
  dz + ωv + ψw + χx + φy)`. New fields: the fourth memory jet `ω`,
  the fourth-order curvature carrier `K₄`, and the fourth-order memory
  law `dω + ωd + φψ + ψφ + χ² = K₄` — the symmetrized cross of the
  first and third jets joins the anticommutator and the square of the
  second (the order-two tail `φ²` and the order-three cross `φχ + χφ`
  are the lower cases of this pattern). The tower square is the full
  four-level curvature ladder
  `(0, K₁v, K₂v + K₁w, K₃v + K₂w + K₁x, K₄v + K₃w + K₂x + K₁y)`:
  every level of the tower sees the curvature of every level below it,
  with every memory tail absorbed by its memory law; the flat criterion
  and all four extraction directions are proved.

* `JetTowerL` — the arbitrary-order memory tower. The memory jets and
  curvature carriers are ℕ-indexed families with a finite order `n`,
  and the single memory field is the law at EVERY order `k < n`:
  `dφ_k + φ_k d + ∑ i + j = k − 1 φ_i φ_j = K_k` — the anticommutator
  plus the full symmetrized convolution of the lower jets. The Rounds
  52–54 laws are the `k ≤ 2` cases verbatim. The flat-tower recursion
  is proved: in a flat tower the anticommutator of every jet is minus
  its convolution (each order's memory is forced by the lower orders'
  products), and a flat tower with all anticommutators zero has all
  convolutions zero (the flatness propagates through the composition).

* THE UNIFICATION — `familyToTowerL`, `tower2ToTowerL`,
  `tower3ToTowerL`, `tower4ToTowerL`: every explicit tower of the
  series (Round 52's `JetFamily` at order 1, Round 53's `JetTower` at
  order 2, Round 54's `JetTower3` at order 3, and the new `JetTower4`
  at order 4) IS an arbitrary-order tower, by explicit bridges: the
  memory fields of the explicit towers are exactly the `k = 0, 1, 2, 3`
  instances of the single arbitrary-order law. The one-step
  `extension` construction raises any flat tower by one order under
  the new jet's own law — flat towers extend forever, order by order.

All statements are exact algebraic identities (fourth-jet linear-map
identities and finite ℚ-linear-map sum identities). The geometric
identification of the tower with actual cohomology stays in the
companion record; no original-X algebraic-source existence is claimed,
assumed, or concluded here. Flatness of the base and every memory law
are supplied fields of the structures, exactly as in Rounds 52–54.
-/

namespace GSTFoldFourthOrderMemoryTower

/-! ## The fourth-order memory tower -/

variable {V : Type*} [AddCommGroup V] [Module ℚ V]

/-- The fourth-order memory tower of the specialization-memory route.
Fields:

* `base` — the flat base differential `d`;
* `base_square` — the flatness `d² = 0` of the base;
* `jet` — the first memory jet `φ`, the ε-coefficient of the family;
* `curvature` — the first prescribed curvature carrier `K₁`;
* `memory` — the first memory law `{d, φ} = dφ + φd = K₁`;
* `second` — the second memory jet `χ`, the ε²-coefficient;
* `second_curvature` — the second-order curvature carrier `K₂`;
* `second_memory` — the second-order memory law
  `dχ + χd + φ² = K₂`;
* `third` — the third memory jet `ψ`, the ε³-coefficient;
* `third_curvature` — the third-order curvature carrier `K₃`;
* `third_memory` — the third-order memory law
  `dψ + ψd + φχ + χφ = K₃`;
* `fourth` — the fourth memory jet `ω`, the ε⁴-coefficient;
* `fourth_curvature` — the fourth-order curvature carrier `K₄`;
* `fourth_memory` — the fourth-order memory law
  `dω + ωd + φψ + ψφ + χ² = K₄`.

The family `d + ε·φ + ε²·χ + ε³·ψ + ε⁴·ω` acts on fourth jets
`(v, w, x, y, z)` (standing for `v + ε·w + ε²·x + ε³·y + ε⁴·z`) by
`tower4Differential (v, w, x, y, z) = (dv, dw + φv, dx + χv + φw,
dy + ψv + χw + φx, dz + ωv + ψw + χx + φy)`. -/
structure JetTower4 (V : Type*) [AddCommGroup V] [Module ℚ V] where
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
  /-- The third memory jet `ψ`: the ε³-coefficient of the family. -/
  third : V →ₗ[ℚ] V
  /-- The third-order curvature carrier `K₃`. -/
  third_curvature : V →ₗ[ℚ] V
  /-- The third-order memory law: `dψ + ψd + φχ + χφ = K₃`. -/
  third_memory : base.comp third + third.comp base + jet.comp second
    + second.comp jet = third_curvature
  /-- The fourth memory jet `ω`: the ε⁴-coefficient of the family. -/
  fourth : V →ₗ[ℚ] V
  /-- The fourth-order curvature carrier `K₄`. -/
  fourth_curvature : V →ₗ[ℚ] V
  /-- The fourth-order memory law: `dω + ωd + φψ + ψφ + χ² = K₄`. -/
  fourth_memory : base.comp fourth + fourth.comp base + jet.comp third
    + third.comp jet + second.comp second = fourth_curvature

namespace JetTower4

/-- The first projection `p₀` of the fourth-jet space
`(v, w, x, y, z) ↦ v`. -/
def jet4p0 : (V × (V × (V × (V × V)))) →ₗ[ℚ] V :=
  LinearMap.fst ℚ V (V × (V × (V × V)))

/-- The second projection `p₁` of the fourth-jet space:
`(v, w, x, y, z) ↦ w`. -/
def jet4p1 : (V × (V × (V × (V × V)))) →ₗ[ℚ] V :=
  (LinearMap.fst ℚ V (V × (V × V))) ∘ₗ
    (LinearMap.snd ℚ V (V × (V × (V × V))))

/-- The third projection `p₂` of the fourth-jet space:
`(v, w, x, y, z) ↦ x`. -/
def jet4p2 : (V × (V × (V × (V × V)))) →ₗ[ℚ] V :=
  (LinearMap.fst ℚ V (V × V)) ∘ₗ
    ((LinearMap.snd ℚ V (V × (V × V))) ∘ₗ
      (LinearMap.snd ℚ V (V × (V × (V × V)))))

/-- The fourth projection `p₃` of the fourth-jet space:
`(v, w, x, y, z) ↦ y`. -/
def jet4p3 : (V × (V × (V × (V × V)))) →ₗ[ℚ] V :=
  (LinearMap.fst ℚ V V) ∘ₗ
    ((LinearMap.snd ℚ V (V × V)) ∘ₗ
      ((LinearMap.snd ℚ V (V × (V × V))) ∘ₗ
        (LinearMap.snd ℚ V (V × (V × (V × V))))))

/-- The fifth projection `p₄` of the fourth-jet space:
`(v, w, x, y, z) ↦ z`. -/
def jet4p4 : (V × (V × (V × (V × V)))) →ₗ[ℚ] V :=
  (LinearMap.snd ℚ V V) ∘ₗ
    ((LinearMap.snd ℚ V (V × V)) ∘ₗ
      ((LinearMap.snd ℚ V (V × (V × V))) ∘ₗ
        (LinearMap.snd ℚ V (V × (V × (V × V))))))

/-- The tower differential on fourth jets: `(v, w, x, y, z) ↦ (dv,
dw + φv, dx + χv + φw, dy + ψv + χw + φx, dz + ωv + ψw + χx + φy)`,
i.e. `(d + ε·φ + ε²·χ + ε³·ψ + ε⁴·ω)(v + ε·w + ε²·x + ε³·y + ε⁴·z) =
dv + ε(dw + φv) + ε²(dx + χv + φw) + ε³(dy + ψv + χw + φx) +
ε⁴(dz + ωv + ψw + χx + φy)` up to the ε⁵ truncation. -/
def tower4Differential (T : JetTower4 V) :
    (V × (V × (V × (V × V)))) →ₗ[ℚ] (V × (V × (V × (V × V)))) :=
  LinearMap.prod (T.base ∘ₗ jet4p0)
    (LinearMap.prod (T.base ∘ₗ jet4p1 + T.jet ∘ₗ jet4p0)
      (LinearMap.prod (T.base ∘ₗ jet4p2 + T.second ∘ₗ jet4p0
          + T.jet ∘ₗ jet4p1)
        (LinearMap.prod (T.base ∘ₗ jet4p3 + T.third ∘ₗ jet4p0
            + T.second ∘ₗ jet4p1 + T.jet ∘ₗ jet4p2)
          (T.base ∘ₗ jet4p4 + T.fourth ∘ₗ jet4p0 + T.third ∘ₗ jet4p1
            + T.second ∘ₗ jet4p2 + T.jet ∘ₗ jet4p3))))

theorem tower4Differential_apply (T : JetTower4 V) (v w x y z : V) :
    T.tower4Differential (v, w, x, y, z)
      = (T.base v, T.base w + T.jet v, T.base x + T.second v + T.jet w,
         T.base y + T.third v + T.second w + T.jet x,
         T.base z + T.fourth v + T.third w + T.second x + T.jet y) := by
  simp [tower4Differential, jet4p0, jet4p1, jet4p2, jet4p3, jet4p4,
    LinearMap.prod_apply, LinearMap.comp_apply,
    LinearMap.add_apply, LinearMap.fst_apply, LinearMap.snd_apply]

theorem base_square_apply (T : JetTower4 V) (x : V) :
    T.base (T.base x) = 0 := by
  rw [← LinearMap.comp_apply, T.base_square, LinearMap.zero_apply]

theorem memory_apply (T : JetTower4 V) (x : V) :
    T.base (T.jet x) + T.jet (T.base x) = T.curvature x := by
  rw [← LinearMap.comp_apply, ← LinearMap.comp_apply,
    ← LinearMap.add_apply, T.memory]

theorem second_memory_apply (T : JetTower4 V) (x : V) :
    T.base (T.second x) + T.second (T.base x) + T.jet (T.jet x)
      = T.second_curvature x := by
  rw [← LinearMap.comp_apply, ← LinearMap.comp_apply,
    ← LinearMap.comp_apply, ← LinearMap.add_apply,
    ← LinearMap.add_apply, T.second_memory]

theorem third_memory_apply (T : JetTower4 V) (x : V) :
    T.base (T.third x) + T.third (T.base x) + T.jet (T.second x)
      + T.second (T.jet x) = T.third_curvature x := by
  rw [← LinearMap.comp_apply, ← LinearMap.comp_apply,
    ← LinearMap.comp_apply, ← LinearMap.comp_apply,
    ← LinearMap.add_apply, ← LinearMap.add_apply,
    ← LinearMap.add_apply, T.third_memory]

theorem fourth_memory_apply (T : JetTower4 V) (x : V) :
    T.base (T.fourth x) + T.fourth (T.base x) + T.jet (T.third x)
      + T.third (T.jet x) + T.second (T.second x)
      = T.fourth_curvature x := by
  rw [← LinearMap.comp_apply, ← LinearMap.comp_apply,
    ← LinearMap.comp_apply, ← LinearMap.comp_apply,
    ← LinearMap.comp_apply, ← LinearMap.add_apply,
    ← LinearMap.add_apply, ← LinearMap.add_apply,
    ← LinearMap.add_apply, T.fourth_memory]

/-- **The zeroth jet of the tower square is zero:** the family is
exactly flat at `ε = 0`; switching all four curvature levels off does
not disturb the square's zeroth component. -/
theorem tower4_square_zeroth (T : JetTower4 V) (v w x y z : V) :
    (T.tower4Differential (T.tower4Differential (v, w, x, y, z))).1
      = 0 := by
  simp only [tower4Differential_apply, base_square_apply]

/-- **The curvature is retained one level up.** The first jet component
of the tower square is exactly the first prescribed curvature: the
specialization memory of Round 52 survives the fourth-order extension
unchanged. -/
theorem tower4_square_first (T : JetTower4 V) (v w x y z : V) :
    (T.tower4Differential (T.tower4Differential (v, w, x, y, z))).2.1
      = T.curvature v := by
  simp only [tower4Differential_apply, map_add, base_square_apply,
    memory_apply, zero_add]

/-- **The first curvature propagates to the second level.** The second
jet component of the tower square is the second-order curvature plus
the first curvature transported to the next input level. -/
theorem tower4_square_second (T : JetTower4 V) (v w x y z : V) :
    (T.tower4Differential (T.tower4Differential (v, w, x, y, z))).2.2.1
      = T.second_curvature v + T.curvature w := by
  simp only [tower4Differential_apply, map_add, base_square_apply]
  have h1 : T.base (T.jet w) + T.jet (T.base w) = T.curvature w :=
    memory_apply T w
  have h2 : T.base (T.second v) + T.second (T.base v)
      + T.jet (T.jet v) = T.second_curvature v :=
    second_memory_apply T v
  rw [← h1, ← h2]
  abel

/-- **The curvature ladder at the third level.** The third jet component
of the tower square is the third-order curvature plus the second-order
curvature transported one level up plus the first curvature
transported two levels up. -/
theorem tower4_square_third (T : JetTower4 V) (v w x y z : V) :
    (T.tower4Differential (T.tower4Differential (v, w, x, y, z))).2.2.2.1
      = T.third_curvature v + T.second_curvature w + T.curvature x := by
  simp only [tower4Differential_apply, map_add, base_square_apply]
  have h1 : T.base (T.jet x) + T.jet (T.base x) = T.curvature x :=
    memory_apply T x
  have h2 : T.base (T.second w) + T.second (T.base w)
      + T.jet (T.jet w) = T.second_curvature w :=
    second_memory_apply T w
  have h3 : T.base (T.third v) + T.third (T.base v)
      + T.jet (T.second v) + T.second (T.jet v)
      = T.third_curvature v := third_memory_apply T v
  rw [← h1, ← h2, ← h3]
  abel

/-- **The full curvature ladder.** The fourth jet component of the
tower square is the fourth-order curvature plus the third-order
curvature transported one level up plus the second-order curvature
transported two levels up plus the first curvature transported three
levels up: every level of the tower sees the curvature of every level
below it, the cross tails `φψ + ψφ` and the square `χ²` cancelling
exactly into the fourth memory law. -/
theorem tower4_square_fourth (T : JetTower4 V) (v w x y z : V) :
    (T.tower4Differential (T.tower4Differential (v, w, x, y, z))).2.2.2.2
      = T.fourth_curvature v + T.third_curvature w
        + T.second_curvature x + T.curvature y := by
  simp only [tower4Differential_apply, map_add, base_square_apply]
  have h1 : T.base (T.jet y) + T.jet (T.base y) = T.curvature y :=
    memory_apply T y
  have h2 : T.base (T.second x) + T.second (T.base x)
      + T.jet (T.jet x) = T.second_curvature x :=
    second_memory_apply T x
  have h3 : T.base (T.third w) + T.third (T.base w)
      + T.jet (T.second w) + T.second (T.jet w)
      = T.third_curvature w := third_memory_apply T w
  have h4 : T.base (T.fourth v) + T.fourth (T.base v)
      + T.jet (T.third v) + T.third (T.jet v)
      + T.second (T.second v) = T.fourth_curvature v :=
    fourth_memory_apply T v
  rw [← h1, ← h2, ← h3, ← h4]
  abel

/-- **The full tower square, as one identity:** the tower differential
squares to `(0, K₁v, K₂v + K₁w, K₃v + K₂w + K₁x,
K₄v + K₃w + K₂x + K₁y)` — the four-level curvature ladder acting
level by level, with every memory tail absorbed by its memory law. -/
theorem tower4_square (T : JetTower4 V) (v w x y z : V) :
    T.tower4Differential (T.tower4Differential (v, w, x, y, z))
      = (0, T.curvature v, T.second_curvature v + T.curvature w,
         T.third_curvature v + T.second_curvature w + T.curvature x,
         T.fourth_curvature v + T.third_curvature w
           + T.second_curvature x + T.curvature y) :=
  Prod.ext (tower4_square_zeroth T v w x y z)
    (Prod.ext (tower4_square_first T v w x y z)
      (Prod.ext (tower4_square_second T v w x y z)
        (Prod.ext (tower4_square_third T v w x y z)
          (tower4_square_fourth T v w x y z))))

/-- **The flat ε = 0 face of the tower.** On the pure-ε⁴ fiber the tower
differential is the flat base differential: all four curvature levels
are switched off while all four memory fields still carry the full
curvature data. -/
theorem tower4_flat_face (T : JetTower4 V) (z : V) :
    T.tower4Differential (0, 0, 0, 0, z) = (0, 0, 0, 0, T.base z) := by
  rw [tower4Differential_apply, T.base.map_zero, T.jet.map_zero,
    T.second.map_zero, T.third.map_zero, T.fourth.map_zero]
  simp

/-- **The flat-tower criterion, sufficiency.** If all four curvature
levels vanish identically, the tower differential squares to zero on
every fourth jet. -/
theorem tower4_flat_of_curvatures_zero (T : JetTower4 V)
    (h1 : ∀ v, T.curvature v = 0) (h2 : ∀ v, T.second_curvature v = 0)
    (h3 : ∀ v, T.third_curvature v = 0) (h4 : ∀ v, T.fourth_curvature v = 0)
    (v w x y z : V) :
    T.tower4Differential (T.tower4Differential (v, w, x, y, z))
      = (0, 0, 0, 0, 0) := by
  rw [tower4_square T v w x y z, h1 v, h2 v, h3 v, h4 v, h1 w, h2 w,
    h3 w, h1 x, h2 x, h1 y]
  simp

/-- **The flat-tower criterion, first extraction.** If the tower
squares to zero on every fourth jet, the first curvature carrier
vanishes identically. -/
theorem curvature_of_flat_tower4 (T : JetTower4 V)
    (h : ∀ v w x y z, T.tower4Differential (T.tower4Differential
      (v, w, x, y, z)) = (0, 0, 0, 0, 0)) (v : V) :
    T.curvature v = 0 := by
  have h2 : (T.tower4Differential (T.tower4Differential (v, 0, 0, 0,
    0))).2.1 = T.curvature v := tower4_square_first T v 0 0 0 0
  rw [h v 0 0 0 0] at h2
  exact h2.symm

/-- **The flat-tower criterion, second extraction.** If the tower
squares to zero on every fourth jet, the second-order curvature
carrier vanishes identically (using the first extraction to clear the
transported term). -/
theorem second_curvature_of_flat_tower4 (T : JetTower4 V)
    (h : ∀ v w x y z, T.tower4Differential (T.tower4Differential
      (v, w, x, y, z)) = (0, 0, 0, 0, 0)) (v : V) :
    T.second_curvature v = 0 := by
  have hc : T.curvature v = 0 := curvature_of_flat_tower4 T h v
  have h2 : (T.tower4Differential (T.tower4Differential (v, v, 0, 0,
    0))).2.2.1 = T.second_curvature v + T.curvature v :=
    tower4_square_second T v v 0 0 0
  rw [h v v 0 0 0] at h2
  rw [hc, add_zero] at h2
  exact h2.symm

/-- **The flat-tower criterion, third extraction.** If the tower
squares to zero on every fourth jet, the third-order curvature
carrier vanishes identically (using the two lower extractions to clear
the transported terms). -/
theorem third_curvature_of_flat_tower4 (T : JetTower4 V)
    (h : ∀ v w x y z, T.tower4Differential (T.tower4Differential
      (v, w, x, y, z)) = (0, 0, 0, 0, 0)) (v : V) :
    T.third_curvature v = 0 := by
  have hc : T.curvature v = 0 := curvature_of_flat_tower4 T h v
  have hsc : T.second_curvature v = 0 :=
    second_curvature_of_flat_tower4 T h v
  have h2 : (T.tower4Differential (T.tower4Differential (v, v, v, 0,
    0))).2.2.2.1 = T.third_curvature v + T.second_curvature v
      + T.curvature v := tower4_square_third T v v v 0 0
  rw [h v v v 0 0] at h2
  rw [hsc, hc, add_zero, add_zero] at h2
  exact h2.symm

/-- **The flat-tower criterion, fourth extraction.** If the tower
squares to zero on every fourth jet, the fourth-order curvature
carrier vanishes identically (using the three lower extractions to
clear the transported terms). -/
theorem fourth_curvature_of_flat_tower4 (T : JetTower4 V)
    (h : ∀ v w x y z, T.tower4Differential (T.tower4Differential
      (v, w, x, y, z)) = (0, 0, 0, 0, 0)) (v : V) :
    T.fourth_curvature v = 0 := by
  have hc : T.curvature v = 0 := curvature_of_flat_tower4 T h v
  have hsc : T.second_curvature v = 0 :=
    second_curvature_of_flat_tower4 T h v
  have htc : T.third_curvature v = 0 :=
    third_curvature_of_flat_tower4 T h v
  have h2 : (T.tower4Differential (T.tower4Differential (v, v, v, v,
    v))).2.2.2.2 = T.fourth_curvature v + T.third_curvature v
      + T.second_curvature v + T.curvature v :=
    tower4_square_fourth T v v v v v
  rw [h v v v v v] at h2
  rw [htc, hsc, hc, add_zero, add_zero, add_zero] at h2
  exact h2.symm

end JetTower4

/-! ## The arbitrary-order memory tower -/

/-- The arbitrary-order memory tower of the specialization-memory
route: the memory jets and curvature carriers as ℕ-indexed families
of finite order `n`, the single memory field carrying the law at EVERY
order `k < n`:

`dφ_k + φ_k d + ∑ i + j = k − 1 φ_i φ_j = K_k`

— the anticommutator of the `k`-th jet plus the full symmetrized
convolution of the lower jets (the Rounds 52–54 laws are the
`k ≤ 2` cases verbatim: `k = 1` is `{d, φ} = K₁`, `k = 2` is
`dχ + χd + φ² = K₂`, `k = 3` is `dψ + ψd + φχ + χφ = K₃`). -/
structure JetTowerL (V : Type*) [AddCommGroup V] [Module ℚ V] where
  /-- The flat base differential `d`. -/
  base : V →ₗ[ℚ] V
  /-- Flatness of the base: `d² = 0`. -/
  base_square : base.comp base = 0
  /-- The finite order `n` of the tower: the number of memory jets. -/
  order : ℕ
  /-- The memory jets `φ_k`, the ε^(k+1)-coefficients of the family. -/
  jet : ℕ → (V →ₗ[ℚ] V)
  /-- The curvature carriers `K_k`. -/
  curv : ℕ → (V →ₗ[ℚ] V)
  /-- The memory law at every order `k < n`:
  `dφ_k + φ_k d + ∑ i + j = k − 1 φ_i φ_j = K_k`. -/
  memory : ∀ k < order,
    base.comp (jet k) + (jet k).comp base
      + ∑ i ∈ Finset.range k, (jet i).comp (jet (k - 1 - i))
      = curv k

namespace JetTowerL

/-- **The head memory law** (the `k = 0` instance, stated without the
empty sum): the first memory jet's anticommutator is exactly the first
curvature carrier — Round 52's memory law, now the head of the
arbitrary-order law. -/
theorem first_memory (T : JetTowerL V) (h0 : 0 < T.order) :
    T.base.comp (T.jet 0) + (T.jet 0).comp T.base = T.curv 0 := by
  have h := T.memory 0 h0
  rwa [Finset.sum_range_zero, add_zero] at h

/-- **The head memory law, pointwise.** -/
theorem first_memory_apply (T : JetTowerL V) (h0 : 0 < T.order) (x : V) :
    T.base (T.jet 0 x) + T.jet 0 (T.base x) = T.curv 0 x := by
  rw [← LinearMap.comp_apply, ← LinearMap.comp_apply,
    ← LinearMap.add_apply, first_memory T h0]

/-- **The flat tower predicate:** every curvature carrier of the tower
vanishes identically. -/
def IsFlat (T : JetTowerL V) : Prop := ∀ k < T.order, T.curv k = 0

/-- **The flat head law.** In a flat tower of positive order the first
memory jet's anticommutator vanishes: the head of the tower is
memory-flat. -/
theorem flat_first (T : JetTowerL V) (hflat : T.IsFlat) (h0 : 0 < T.order) :
    T.base.comp (T.jet 0) + (T.jet 0).comp T.base = 0 := by
  rw [first_memory T h0, hflat 0 h0]

/-- **THE FLAT-TOWER RECURSION.** In a flat tower the anticommutator of
every jet is minus its convolution: each order's memory is forced by
the products of the lower orders' jets — the higher memory jets are
the curvature tail of the lower ones. -/
theorem flat_memory_recursion (T : JetTowerL V) (hflat : T.IsFlat)
    (k : ℕ) (hk : k < T.order) :
    T.base.comp (T.jet k) + (T.jet k).comp T.base
      = -∑ i ∈ Finset.range k, (T.jet i).comp (T.jet (k - 1 - i)) := by
  have h := T.memory k hk
  rw [hflat k hk] at h
  rw [eq_neg_iff_add_eq_zero]
  exact h

/-- **The flatness propagates through the composition.** In a flat
tower whose every anticommutator vanishes (a totally-flat tower),
every convolution vanishes: the memory jets compose to zero at every
order — the flatness of the individual jets closes under the
composition. -/
theorem flat_convolution_free (T : JetTowerL V) (hflat : T.IsFlat)
    (hanti : ∀ k < T.order,
      T.base.comp (T.jet k) + (T.jet k).comp T.base = 0)
    (k : ℕ) (hk : k < T.order) :
    ∑ i ∈ Finset.range k, (T.jet i).comp (T.jet (k - 1 - i)) = 0 := by
  have h := T.memory k hk
  rw [hanti k hk, zero_add, hflat k hk] at h
  exact h

/-- **The memory laws of the one-order extension: below the old order
they are the old laws; at the new top order the law is the new jet's
own hypothesis.** This is the standalone form of the extension's
memory field. -/
theorem extension_memory (T : JetTowerL V) (ψ c : V →ₗ[ℚ] V)
    (hnew : T.base.comp ψ + ψ.comp T.base
      + ∑ i ∈ Finset.range T.order,
        (T.jet i).comp (T.jet (T.order - 1 - i)) = c)
    (k : ℕ) (hk : k < T.order + 1) :
    T.base.comp (if k < T.order then T.jet k else ψ)
      + (if k < T.order then T.jet k else ψ).comp T.base
      + ∑ i ∈ Finset.range k,
          (if i < T.order then T.jet i else ψ).comp
            (if k - 1 - i < T.order then T.jet (k - 1 - i) else ψ)
      = if k < T.order then T.curv k else c := by
  rcases Nat.lt_or_ge k T.order with hk' | hk'
  · rw [if_pos hk', if_pos hk']
    have hsum : ∑ i ∈ Finset.range k,
        (if i < T.order then T.jet i else ψ).comp
          (if k - 1 - i < T.order then T.jet (k - 1 - i) else ψ)
        = ∑ i ∈ Finset.range k,
          (T.jet i).comp (T.jet (k - 1 - i)) := by
      apply Finset.sum_congr rfl
      intro i hi
      have hik : i < k := Finset.mem_range.mp hi
      rw [if_pos (by omega : i < T.order),
        if_pos (by omega : k - 1 - i < T.order)]
    rw [hsum]
    exact T.memory k hk'
  · have hke : k = T.order := by omega
    have hk'' : ¬(k < T.order) := by omega
    rw [if_neg hk'', if_neg hk'']
    have hsum : ∑ i ∈ Finset.range k,
        (if i < T.order then T.jet i else ψ).comp
          (if k - 1 - i < T.order then T.jet (k - 1 - i) else ψ)
        = ∑ i ∈ Finset.range k,
          (T.jet i).comp (T.jet (k - 1 - i)) := by
      apply Finset.sum_congr rfl
      intro i hi
      have hik : i < k := Finset.mem_range.mp hi
      rw [if_pos (by omega : i < T.order),
        if_pos (by omega : k - 1 - i < T.order)]
    rw [hsum, hke]
    exact hnew

/-- **The one-order extension of a memory tower.** The jets agree with
the old tower below the old order and carry the new jet `ψ` at the new
top order; the curvatures agree below and carry `c` at the top. The
memory laws hold by `extension_memory`: below the old order they are
the old laws, and at the top the law is the new jet's own hypothesis
— flat towers extend forever, order by order. -/
def extension (T : JetTowerL V) (ψ c : V →ₗ[ℚ] V)
    (hnew : T.base.comp ψ + ψ.comp T.base
      + ∑ i ∈ Finset.range T.order,
        (T.jet i).comp (T.jet (T.order - 1 - i)) = c) :
    JetTowerL V where
  base := T.base
  base_square := T.base_square
  order := T.order + 1
  jet := fun k => if k < T.order then T.jet k else ψ
  curv := fun k => if k < T.order then T.curv k else c
  memory := by
    intro k hk
    exact extension_memory T ψ c hnew k hk

/-- **The flat extension law.** Extending a flat tower by one order
under a new jet satisfying its own memory law with zero curvature
yields a flat tower again: the flat towers extend forever, order by
order, and the flat predicate is preserved by the extension. -/
theorem extension_flat (T : JetTowerL V) (hflat : T.IsFlat)
    (ψ : V →ₗ[ℚ] V)
    (hnew : T.base.comp ψ + ψ.comp T.base
      + ∑ i ∈ Finset.range T.order,
        (T.jet i).comp (T.jet (T.order - 1 - i)) = 0) :
    (T.extension ψ 0 hnew).IsFlat := by
  intro k hk
  show (if k < T.order then T.curv k else 0) = 0
  by_cases hk' : k < T.order
  · rw [if_pos hk']
    exact hflat k hk'
  · rw [if_neg hk']

end JetTowerL

/-! ## The unification — every explicit tower of the series is an
arbitrary-order tower -/

/-- The jet family of Round 53's second-order tower, ℕ-indexed:
`tower2JetOf 0 = φ`, `tower2JetOf 1 = χ`, zero beyond. -/
def tower2JetOf (T : GSTFoldMemoryTower.JetTower V) : ℕ → (V →ₗ[ℚ] V)
  | 0 => T.jet
  | 1 => T.second
  | _ => 0

/-- The curvature family of Round 53's second-order tower, ℕ-indexed. -/
def tower2CurvOf (T : GSTFoldMemoryTower.JetTower V) : ℕ → (V →ₗ[ℚ] V)
  | 0 => T.curvature
  | 1 => T.second_curvature
  | _ => 0

theorem tower2JetOf_zero (T : GSTFoldMemoryTower.JetTower V) :
    tower2JetOf T 0 = T.jet := rfl

theorem tower2JetOf_one (T : GSTFoldMemoryTower.JetTower V) :
    tower2JetOf T 1 = T.second := rfl

theorem tower2CurvOf_zero (T : GSTFoldMemoryTower.JetTower V) :
    tower2CurvOf T 0 = T.curvature := rfl

theorem tower2CurvOf_one (T : GSTFoldMemoryTower.JetTower V) :
    tower2CurvOf T 1 = T.second_curvature := rfl

/-- **Round 53's `JetTower` is the order-2 tower.** Both memory laws of
the second-order tower are the `k = 0, 1` instances of the
arbitrary-order law. -/
def tower2ToTowerL (T : GSTFoldMemoryTower.JetTower V) : JetTowerL V where
  base := T.base
  base_square := T.base_square
  order := 2
  jet := tower2JetOf T
  curv := tower2CurvOf T
  memory := by
    intro k hk
    interval_cases k
    · simp only [tower2JetOf_zero, tower2CurvOf_zero,
        Finset.sum_range_zero, add_zero]
      exact T.memory
    · simp only [tower2JetOf_zero, tower2JetOf_one, tower2CurvOf_one,
        Finset.sum_range_one, show (1 : ℕ) - 1 - 0 = 0 from rfl]
      exact T.second_memory

/-- The jet family of Round 54's third-order tower, ℕ-indexed:
`0 ↦ φ`, `1 ↦ χ`, `2 ↦ ψ`, zero beyond. -/
def tower3JetOf (T : GSTFoldChainThirdOrderMemory.JetTower3 V) :
    ℕ → (V →ₗ[ℚ] V)
  | 0 => T.jet
  | 1 => T.second
  | 2 => T.third
  | _ => 0

/-- The curvature family of Round 54's third-order tower, ℕ-indexed. -/
def tower3CurvOf (T : GSTFoldChainThirdOrderMemory.JetTower3 V) :
    ℕ → (V →ₗ[ℚ] V)
  | 0 => T.curvature
  | 1 => T.second_curvature
  | 2 => T.third_curvature
  | _ => 0

theorem tower3JetOf_zero (T : GSTFoldChainThirdOrderMemory.JetTower3 V) :
    tower3JetOf T 0 = T.jet := rfl

theorem tower3JetOf_one (T : GSTFoldChainThirdOrderMemory.JetTower3 V) :
    tower3JetOf T 1 = T.second := rfl

theorem tower3JetOf_two (T : GSTFoldChainThirdOrderMemory.JetTower3 V) :
    tower3JetOf T 2 = T.third := rfl

theorem tower3CurvOf_zero (T : GSTFoldChainThirdOrderMemory.JetTower3 V) :
    tower3CurvOf T 0 = T.curvature := rfl

theorem tower3CurvOf_one (T : GSTFoldChainThirdOrderMemory.JetTower3 V) :
    tower3CurvOf T 1 = T.second_curvature := rfl

theorem tower3CurvOf_two (T : GSTFoldChainThirdOrderMemory.JetTower3 V) :
    tower3CurvOf T 2 = T.third_curvature := rfl

/-- **Round 54's `JetTower3` is the order-3 tower.** All three memory
laws of the third-order tower are the `k = 0, 1, 2` instances of the
arbitrary-order law. -/
def tower3ToTowerL (T : GSTFoldChainThirdOrderMemory.JetTower3 V) :
    JetTowerL V where
  base := T.base
  base_square := T.base_square
  order := 3
  jet := tower3JetOf T
  curv := tower3CurvOf T
  memory := by
    intro k hk
    interval_cases k
    · simp only [tower3JetOf_zero, tower3CurvOf_zero,
        Finset.sum_range_zero, add_zero]
      exact T.memory
    · simp only [tower3JetOf_zero, tower3JetOf_one, tower3CurvOf_one,
        Finset.sum_range_one, show (1 : ℕ) - 1 - 0 = 0 from rfl]
      exact T.second_memory
    · simp only [Finset.sum_range_succ, Finset.sum_range_zero,
        add_zero, zero_add, tower3JetOf_zero, tower3JetOf_one,
        tower3JetOf_two, tower3CurvOf_two,
        show (2 : ℕ) - 1 - 0 = 1 from rfl,
        show (2 : ℕ) - 1 - 1 = 0 from rfl]
      rw [← T.third_memory]
      abel

/-- The jet family of the new fourth-order tower, ℕ-indexed:
`0 ↦ φ`, `1 ↦ χ`, `2 ↦ ψ`, `3 ↦ ω`, zero beyond. -/
def tower4JetOf (T : JetTower4 V) : ℕ → (V →ₗ[ℚ] V)
  | 0 => T.jet
  | 1 => T.second
  | 2 => T.third
  | 3 => T.fourth
  | _ => 0

/-- The curvature family of the new fourth-order tower, ℕ-indexed. -/
def tower4CurvOf (T : JetTower4 V) : ℕ → (V →ₗ[ℚ] V)
  | 0 => T.curvature
  | 1 => T.second_curvature
  | 2 => T.third_curvature
  | 3 => T.fourth_curvature
  | _ => 0

theorem tower4JetOf_zero (T : JetTower4 V) :
    tower4JetOf T 0 = T.jet := rfl

theorem tower4JetOf_one (T : JetTower4 V) :
    tower4JetOf T 1 = T.second := rfl

theorem tower4JetOf_two (T : JetTower4 V) :
    tower4JetOf T 2 = T.third := rfl

theorem tower4JetOf_three (T : JetTower4 V) :
    tower4JetOf T 3 = T.fourth := rfl

theorem tower4CurvOf_zero (T : JetTower4 V) :
    tower4CurvOf T 0 = T.curvature := rfl

theorem tower4CurvOf_one (T : JetTower4 V) :
    tower4CurvOf T 1 = T.second_curvature := rfl

theorem tower4CurvOf_two (T : JetTower4 V) :
    tower4CurvOf T 2 = T.third_curvature := rfl

theorem tower4CurvOf_three (T : JetTower4 V) :
    tower4CurvOf T 3 = T.fourth_curvature := rfl

/-- **The new `JetTower4` is the order-4 tower.** All four memory laws
of the fourth-order tower — including the new fourth law
`dω + ωd + φψ + ψφ + χ² = K₄` — are the `k = 0, 1, 2, 3` instances of
the single arbitrary-order law: the Rounds 52–55 explicit towers are
the order-1, 2, 3, 4 instances of one law. -/
def tower4ToTowerL (T : JetTower4 V) : JetTowerL V where
  base := T.base
  base_square := T.base_square
  order := 4
  jet := tower4JetOf T
  curv := tower4CurvOf T
  memory := by
    intro k hk
    interval_cases k
    · simp only [tower4JetOf_zero, tower4CurvOf_zero,
        Finset.sum_range_zero, add_zero]
      exact T.memory
    · simp only [tower4JetOf_zero, tower4JetOf_one, tower4CurvOf_one,
        Finset.sum_range_one, show (1 : ℕ) - 1 - 0 = 0 from rfl]
      exact T.second_memory
    · simp only [Finset.sum_range_succ, Finset.sum_range_zero,
        add_zero, zero_add, tower4JetOf_zero, tower4JetOf_one,
        tower4JetOf_two, tower4CurvOf_two,
        show (2 : ℕ) - 1 - 0 = 1 from rfl,
        show (2 : ℕ) - 1 - 1 = 0 from rfl]
      rw [← T.third_memory]
      abel
    · simp only [Finset.sum_range_succ, Finset.sum_range_zero,
        add_zero, zero_add, tower4JetOf_zero, tower4JetOf_one,
        tower4JetOf_two, tower4JetOf_three, tower4CurvOf_three,
        show (3 : ℕ) - 1 - 0 = 2 from rfl,
        show (3 : ℕ) - 1 - 1 = 1 from rfl,
        show (3 : ℕ) - 1 - 2 = 0 from rfl]
      rw [← T.fourth_memory]
      abel

/-- **Round 52's `JetFamily` is the order-1 tower.** The first-jet
family's memory law is the `k = 0` instance of the arbitrary-order
law. -/
def familyToTowerL (F : GSTAllDegreeCurvatureMemory.JetFamily V) :
    JetTowerL V where
  base := F.base
  base_square := F.base_square
  order := 1
  jet := fun _ => F.jet
  curv := fun _ => F.curvature
  memory := by
    intro k hk
    interval_cases k
    · simp only [Finset.sum_range_zero, add_zero]
      exact F.memory

namespace JetTower4

/-- **The flat head law of the fourth-order tower, via the
arbitrary-order law.** Every flat fourth-order tower (all four
curvature carriers zero) has its first memory jet memory-flat — the
arbitrary-order `flat_first` instantiated at order 4 through the
unification bridge. -/
theorem flat_head_of_flat_tower4 (T : JetTower4 V)
    (h1 : T.curvature = 0) (h2 : T.second_curvature = 0)
    (h3 : T.third_curvature = 0) (h4 : T.fourth_curvature = 0) :
    T.base.comp T.jet + T.jet.comp T.base = 0 := by
  have hflat : (tower4ToTowerL T).IsFlat := by
    intro k hk
    have hk' : k < 4 := hk
    interval_cases k
    · exact h1
    · exact h2
    · exact h3
    · exact h4
  exact JetTowerL.flat_first (tower4ToTowerL T) hflat (Nat.succ_pos 3)

end JetTower4

end GSTFoldFourthOrderMemoryTower

#print axioms GSTFoldFourthOrderMemoryTower.JetTower4.tower4Differential_apply
#print axioms GSTFoldFourthOrderMemoryTower.JetTower4.base_square_apply
#print axioms GSTFoldFourthOrderMemoryTower.JetTower4.memory_apply
#print axioms GSTFoldFourthOrderMemoryTower.JetTower4.second_memory_apply
#print axioms GSTFoldFourthOrderMemoryTower.JetTower4.third_memory_apply
#print axioms GSTFoldFourthOrderMemoryTower.JetTower4.fourth_memory_apply
#print axioms GSTFoldFourthOrderMemoryTower.JetTower4.tower4_square_zeroth
#print axioms GSTFoldFourthOrderMemoryTower.JetTower4.tower4_square_first
#print axioms GSTFoldFourthOrderMemoryTower.JetTower4.tower4_square_second
#print axioms GSTFoldFourthOrderMemoryTower.JetTower4.tower4_square_third
#print axioms GSTFoldFourthOrderMemoryTower.JetTower4.tower4_square_fourth
#print axioms GSTFoldFourthOrderMemoryTower.JetTower4.tower4_square
#print axioms GSTFoldFourthOrderMemoryTower.JetTower4.tower4_flat_face
#print axioms GSTFoldFourthOrderMemoryTower.JetTower4.tower4_flat_of_curvatures_zero
#print axioms GSTFoldFourthOrderMemoryTower.JetTower4.curvature_of_flat_tower4
#print axioms GSTFoldFourthOrderMemoryTower.JetTower4.second_curvature_of_flat_tower4
#print axioms GSTFoldFourthOrderMemoryTower.JetTower4.third_curvature_of_flat_tower4
#print axioms GSTFoldFourthOrderMemoryTower.JetTower4.fourth_curvature_of_flat_tower4
#print axioms GSTFoldFourthOrderMemoryTower.JetTowerL.first_memory
#print axioms GSTFoldFourthOrderMemoryTower.JetTowerL.first_memory_apply
#print axioms GSTFoldFourthOrderMemoryTower.JetTowerL.flat_first
#print axioms GSTFoldFourthOrderMemoryTower.JetTowerL.flat_memory_recursion
#print axioms GSTFoldFourthOrderMemoryTower.JetTowerL.flat_convolution_free
#print axioms GSTFoldFourthOrderMemoryTower.JetTowerL.extension_memory
#print axioms GSTFoldFourthOrderMemoryTower.JetTowerL.extension_flat
#print axioms GSTFoldFourthOrderMemoryTower.familyToTowerL
#print axioms GSTFoldFourthOrderMemoryTower.tower2ToTowerL
#print axioms GSTFoldFourthOrderMemoryTower.tower3ToTowerL
#print axioms GSTFoldFourthOrderMemoryTower.tower4ToTowerL
#print axioms GSTFoldFourthOrderMemoryTower.JetTower4.flat_head_of_flat_tower4
