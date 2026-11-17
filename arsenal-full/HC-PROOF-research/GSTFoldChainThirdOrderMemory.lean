import Mathlib
import GSTAllDegreeCurvatureMemory
import GSTFoldMemoryTower

/-!
# GST Round 54 — the third-order memory tower and the arbitrary-length fold chain

Round 53 (`GSTFoldMemoryTower`) built the second-order memory tower
(`d + ε·φ + ε²·χ` on second jets, the second-order memory law
`dχ + χd + φ² = K₂`) and the two-fold composition transport. This round
extends both faces one structural step further — the tower one level up,
the composition to arbitrary stack length:

* `JetTower3` — the third-order memory tower. The parameter family
  `d + ε·φ + ε²·χ + ε³·ψ` acts on third jets `(w, x, y, z)` (standing for
  `w + ε·x + ε²·y + ε³·z`) by `(dw, dx + φw, dy + χw + φx,
  dz + ψw + χx + φy)`. New fields: the third memory jet `ψ`, the
  third-order curvature carrier `K₃`, and the third-order memory law
  `dψ + ψd + φχ + χφ = K₃` — the symmetrized cross of the two lower
  memory jets joins the anticommutator (the order-two tail `φ²` is the
  single-term case of this pattern). The tower square is the full
  curvature ladder `(0, K₁w, K₂w + K₁x, K₃w + K₂x + K₁y)`: every level
  of the tower sees the curvature of every level below it, with all
  memory tails absorbed by the three memory laws; the flat criterion and
  all three extraction directions are proved.

* `FoldChain` — the arbitrary-length fold stack. A finite stack of
  successive paired folds (outermost, i.e. last-applied, first) satisfies
  the exact chain conservation law `chain-flat = chain-fold +
  chain-loss`, proved by one induction on the stack: the iterated flat
  factor is the composed fold plus the total loss, where each fold's own
  loss is transported by the flat factors of all folds applied after it.
  Below the minimum shift nothing is lost; the stack's degree-one
  blindness holds whenever every codimension is ≥ 2; and under a
  strictly-smallest innermost shift the first lost degree is that shift
  with loss exactly one (the Round 53 two-fold law is the stack of
  length two).

All statements are exact algebraic identities (ℚ[t] ring identities and
third-jet linear-map identities). The geometric identification of the
tower or of the fold stack with actual cohomology stays in the companion
record; no original-X algebraic-source existence is claimed, assumed, or
concluded here. Flatness of the base and all three memory laws are
supplied fields of the structures, exactly as in Rounds 52–53.
-/

namespace GSTFoldChainThirdOrderMemory

open Polynomial

open GSTAllDegreeCurvatureMemory (coeff_X_pow_mul_lt coeff_X_pow_mul_self
  coeff_one_add_X_zero coeff_one_add_X_pow_zero)

open GSTFoldMemoryTower (foldOf lossOf conservationOf)

/-! ## The third-order memory tower -/

variable {V : Type*} [AddCommGroup V] [Module ℚ V]

/-- The third-order memory tower of the specialization-memory route.
Fields:

* `base` — the flat base differential `d`;
* `base_square` — the flatness `d² = 0` of the base;
* `jet` — the first memory jet `φ`, the ε-coefficient of the family;
* `curvature` — the first prescribed curvature carrier `K₁`;
* `memory` — the first memory law `{d, φ} = dφ + φd = K₁`;
* `second` — the second memory jet `χ`, the ε²-coefficient of the family;
* `second_curvature` — the second-order curvature carrier `K₂`;
* `second_memory` — the second-order memory law `dχ + χd + φ² = K₂`;
* `third` — the third memory jet `ψ`, the ε³-coefficient of the family;
* `third_curvature` — the third-order curvature carrier `K₃`;
* `third_memory` — the third-order memory law
  `dψ + ψd + φχ + χφ = K₃`.

The family `d + ε·φ + ε²·χ + ε³·ψ` acts on third jets `(w, x, y, z)`
(standing for `w + ε·x + ε²·y + ε³·z`) by `tower3Differential (w, x, y,
z) = (dw, dx + φw, dy + χw + φx, dz + ψw + χx + φy)`. -/
structure JetTower3 (V : Type*) [AddCommGroup V] [Module ℚ V] where
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

namespace JetTower3

/-- The tower differential on third jets: `(w, x, y, z) ↦ (dw, dx + φw,
dy + χw + φx, dz + ψw + χx + φy)`, i.e. `(d + ε·φ + ε²·χ + ε³·ψ)(w +
ε·x + ε²·y + ε³·z) = dw + ε(dx + φw) + ε²(dy + χw + φx) + ε³(dz + ψw +
χx + φy)` up to the ε⁴ truncation. -/
def tower3Differential (T : JetTower3 V) :
    (V × (V × (V × V))) →ₗ[ℚ] (V × (V × (V × V))) :=
  LinearMap.prod
    (T.base ∘ₗ LinearMap.fst ℚ V (V × (V × V)))
    (LinearMap.prod
      (T.base ∘ₗ ((LinearMap.fst ℚ V (V × V)) ∘ₗ
          (LinearMap.snd ℚ V (V × (V × V))))
        + T.jet ∘ₗ LinearMap.fst ℚ V (V × (V × V)))
      (LinearMap.prod
        (T.base ∘ₗ ((LinearMap.fst ℚ V V) ∘ₗ
            ((LinearMap.snd ℚ V (V × V)) ∘ₗ
              (LinearMap.snd ℚ V (V × (V × V)))))
          + T.second ∘ₗ LinearMap.fst ℚ V (V × (V × V))
          + T.jet ∘ₗ ((LinearMap.fst ℚ V (V × V)) ∘ₗ
              (LinearMap.snd ℚ V (V × (V × V)))))
        (T.base ∘ₗ ((LinearMap.snd ℚ V V) ∘ₗ
            ((LinearMap.snd ℚ V (V × V)) ∘ₗ
              (LinearMap.snd ℚ V (V × (V × V)))))
          + T.third ∘ₗ LinearMap.fst ℚ V (V × (V × V))
          + T.second ∘ₗ ((LinearMap.fst ℚ V (V × V)) ∘ₗ
              (LinearMap.snd ℚ V (V × (V × V))))
          + T.jet ∘ₗ ((LinearMap.fst ℚ V V) ∘ₗ
              ((LinearMap.snd ℚ V (V × V)) ∘ₗ
                (LinearMap.snd ℚ V (V × (V × V))))))))

theorem tower3Differential_apply (T : JetTower3 V) (w x y z : V) :
    T.tower3Differential (w, x, y, z) =
      (T.base w, T.base x + T.jet w, T.base y + T.second w + T.jet x,
       T.base z + T.third w + T.second x + T.jet y) := by
  simp [tower3Differential, LinearMap.prod_apply, LinearMap.comp_apply,
    LinearMap.add_apply, LinearMap.fst_apply, LinearMap.snd_apply]

theorem base_square_apply (T : JetTower3 V) (x : V) :
    T.base (T.base x) = 0 := by
  rw [← LinearMap.comp_apply, T.base_square, LinearMap.zero_apply]

theorem memory_apply (T : JetTower3 V) (x : V) :
    T.base (T.jet x) + T.jet (T.base x) = T.curvature x := by
  rw [← LinearMap.comp_apply, ← LinearMap.comp_apply,
    ← LinearMap.add_apply, T.memory]

theorem second_memory_apply (T : JetTower3 V) (x : V) :
    T.base (T.second x) + T.second (T.base x) + T.jet (T.jet x)
      = T.second_curvature x := by
  rw [← LinearMap.comp_apply, ← LinearMap.comp_apply,
    ← LinearMap.comp_apply, ← LinearMap.add_apply,
    ← LinearMap.add_apply, T.second_memory]

theorem third_memory_apply (T : JetTower3 V) (x : V) :
    T.base (T.third x) + T.third (T.base x) + T.jet (T.second x)
      + T.second (T.jet x) = T.third_curvature x := by
  rw [← LinearMap.comp_apply, ← LinearMap.comp_apply,
    ← LinearMap.comp_apply, ← LinearMap.comp_apply,
    ← LinearMap.add_apply, ← LinearMap.add_apply,
    ← LinearMap.add_apply, T.third_memory]

/-- **The zeroth jet of the tower square is zero:** the family is exactly
flat at `ε = 0`; switching all three curvature levels off does not
disturb the square's zeroth component. -/
theorem tower3_square_zeroth (T : JetTower3 V) (w x y z : V) :
    (T.tower3Differential (T.tower3Differential (w, x, y, z))).1 = 0 := by
  simp only [tower3Differential_apply, base_square_apply]

/-- **The curvature is retained one level up.** The first jet component
of the tower square is exactly the first prescribed curvature: the
specialization memory of Round 52 survives the third-order extension
unchanged. -/
theorem tower3_square_first (T : JetTower3 V) (w x y z : V) :
    (T.tower3Differential (T.tower3Differential (w, x, y, z))).2.1
      = T.curvature w := by
  simp only [tower3Differential_apply, map_add, base_square_apply,
    memory_apply, zero_add]

/-- **The first curvature propagates to the second level.** The second
jet component of the tower square is the second-order curvature plus the
first curvature transported to the next input level: the Round 53 tower
square pattern survives the third-order extension unchanged. -/
theorem tower3_square_second (T : JetTower3 V) (w x y z : V) :
    (T.tower3Differential (T.tower3Differential (w, x, y, z))).2.2.1
      = T.second_curvature w + T.curvature x := by
  simp only [tower3Differential_apply, map_add, base_square_apply]
  have h1 : T.base (T.jet x) + T.jet (T.base x) = T.curvature x :=
    memory_apply T x
  have h2 : T.base (T.second w) + T.second (T.base w) + T.jet (T.jet w)
      = T.second_curvature w := second_memory_apply T w
  rw [← h1, ← h2]
  abel

/-- **The curvature ladder.** The third jet component of the tower
square is the third-order curvature plus the second-order curvature
transported one level up plus the first curvature transported two levels
up: every level of the tower sees the curvature of every level below it,
the two cross tails `φχ + χφ` cancelling exactly into the third memory
law. -/
theorem tower3_square_third (T : JetTower3 V) (w x y z : V) :
    (T.tower3Differential (T.tower3Differential (w, x, y, z))).2.2.2
      = T.third_curvature w + T.second_curvature x + T.curvature y := by
  simp only [tower3Differential_apply, map_add, base_square_apply]
  have h1 : T.base (T.jet y) + T.jet (T.base y) = T.curvature y :=
    memory_apply T y
  have h2 : T.base (T.second x) + T.second (T.base x) + T.jet (T.jet x)
      = T.second_curvature x := second_memory_apply T x
  have h3 : T.base (T.third w) + T.third (T.base w) + T.jet (T.second w)
      + T.second (T.jet w) = T.third_curvature w := third_memory_apply T w
  rw [← h1, ← h2, ← h3]
  abel

/-- **The full tower square, as one identity:** the tower differential
squares to `(0, K₁w, K₂w + K₁x, K₃w + K₂x + K₁y)` — the curvature
ladder acting level by level, with every memory tail absorbed by its
memory law. -/
theorem tower3_square (T : JetTower3 V) (w x y z : V) :
    T.tower3Differential (T.tower3Differential (w, x, y, z))
      = (0, T.curvature w, T.second_curvature w + T.curvature x,
         T.third_curvature w + T.second_curvature x + T.curvature y) :=
  Prod.ext (tower3_square_zeroth T w x y z)
    (Prod.ext (tower3_square_first T w x y z)
      (Prod.ext (tower3_square_second T w x y z)
        (tower3_square_third T w x y z)))

/-- **The flat ε = 0 face of the tower.** On the pure-ε³ fiber the tower
differential is the flat base differential: all three curvature levels
are switched off while all three memory fields still carry the full
curvature data. -/
theorem tower3_flat_face (T : JetTower3 V) (z : V) :
    T.tower3Differential (0, 0, 0, z) = (0, 0, 0, T.base z) := by
  rw [tower3Differential_apply, T.base.map_zero, T.jet.map_zero,
    T.second.map_zero, T.third.map_zero]
  simp

/-- **The flat-tower criterion, sufficiency.** If all three curvature
levels vanish identically, the tower differential squares to zero on
every third jet. -/
theorem tower3_flat_of_curvatures_zero (T : JetTower3 V)
    (h1 : ∀ v, T.curvature v = 0) (h2 : ∀ v, T.second_curvature v = 0)
    (h3 : ∀ v, T.third_curvature v = 0) (w x y z : V) :
    T.tower3Differential (T.tower3Differential (w, x, y, z))
      = (0, 0, 0, 0) := by
  rw [tower3_square T w x y z, h1 w, h2 w, h3 w, h1 x, h2 x, h1 y]
  simp

/-- **The flat-tower criterion, first extraction.** If the tower squares
to zero on every third jet, the first curvature carrier vanishes
identically. -/
theorem curvature_of_flat_tower3 (T : JetTower3 V)
    (h : ∀ w x y z, T.tower3Differential (T.tower3Differential (w, x, y, z))
      = (0, 0, 0, 0)) (w : V) :
    T.curvature w = 0 := by
  have h2 : (T.tower3Differential (T.tower3Differential (w, 0, 0, 0))).2.1
      = T.curvature w := tower3_square_first T w 0 0 0
  rw [h w 0 0 0] at h2
  exact h2.symm

/-- **The flat-tower criterion, second extraction.** If the tower squares
to zero on every third jet, the second-order curvature carrier vanishes
identically (using the first extraction to clear the transported
term). -/
theorem second_curvature_of_flat_tower3 (T : JetTower3 V)
    (h : ∀ w x y z, T.tower3Differential (T.tower3Differential (w, x, y, z))
      = (0, 0, 0, 0)) (w : V) :
    T.second_curvature w = 0 := by
  have hc : T.curvature w = 0 := curvature_of_flat_tower3 T h w
  have h2 : (T.tower3Differential (T.tower3Differential (w, w, 0, 0))).2.2.1
      = T.second_curvature w + T.curvature w :=
    tower3_square_second T w w 0 0
  rw [h w w 0 0] at h2
  rw [hc, add_zero] at h2
  exact h2.symm

/-- **The flat-tower criterion, third extraction.** If the tower squares
to zero on every third jet, the third-order curvature carrier vanishes
identically (using the two lower extractions to clear the transported
terms). -/
theorem third_curvature_of_flat_tower3 (T : JetTower3 V)
    (h : ∀ w x y z, T.tower3Differential (T.tower3Differential (w, x, y, z))
      = (0, 0, 0, 0)) (w : V) :
    T.third_curvature w = 0 := by
  have hc : T.curvature w = 0 := curvature_of_flat_tower3 T h w
  have hsc : T.second_curvature w = 0 := second_curvature_of_flat_tower3 T h w
  have h2 : (T.tower3Differential (T.tower3Differential (w, w, w, w))).2.2.2
      = T.third_curvature w + T.second_curvature w + T.curvature w :=
    tower3_square_third T w w w w
  rw [h w w w w, hsc, hc, add_zero, add_zero] at h2
  exact h2.symm

end JetTower3

/-! ## The arbitrary-length fold chain -/

/-- The iterated flat factor of a fold stack (outermost first): the
product of all `(1 + t^s)²` factors, multiplied onto the base. -/
noncomputable def chainFlat : List (Polynomial ℚ × ℕ) → Polynomial ℚ →
    Polynomial ℚ
  | [], P => P
  | (R, s) :: rest, P => (1 + X ^ s) ^ 2 * chainFlat rest P

/-- The composed fold of a fold stack (outermost first): each fold's
paired-fold polynomial applied to the result of all folds below it. -/
noncomputable def chainFold : List (Polynomial ℚ × ℕ) → Polynomial ℚ →
    Polynomial ℚ
  | [], P => P
  | (R, s) :: rest, P => foldOf (chainFold rest P) R s

/-- The total loss of a fold stack (outermost first): the outermost
fold's own loss plus the losses of all folds below it, each transported
by the flat factors of all folds applied after it. -/
noncomputable def chainLoss : List (Polynomial ℚ × ℕ) → Polynomial ℚ →
    Polynomial ℚ
  | [], _ => 0
  | (R, s) :: rest, P =>
      lossOf R s + (1 + X ^ s) ^ 2 * chainLoss rest P

/-- **The flat factor is invisible below its own shift.** In every
degree `i < s`, multiplication by `(1 + t^s)²` does not change the
coefficient: the transport of a loss past a later flat factor leaves
every below-shift degree untouched. -/
theorem coeff_flat_factor_lt (Q : Polynomial ℚ) (s i : ℕ) (h : i < s) :
    ((1 + X ^ s) ^ 2 * Q).coeff i = Q.coeff i := by
  have e : (1 + X ^ s) ^ 2 * Q = Q + X ^ s * Q + X ^ s * Q + X ^ s * (X ^ s * Q) := by
    rw [pow_two]
    ring
  rw [e]
  simp only [Polynomial.coeff_add]
  rw [coeff_X_pow_mul_lt _ s i h, coeff_X_pow_mul_lt _ s i h]
  norm_num

/-- **The single-fold loss lands on its own shift.** Under the degree-zero
cup rank normalization, the paired-fold loss polynomial has coefficient
exactly one in degree `s`. -/
theorem lossOf_coeff_self (R : Polynomial ℚ) (s : ℕ) (hs : 0 < s)
    (h : R.coeff 0 = 1) :
    (lossOf R s).coeff s = 1 := by
  simp only [lossOf]
  rw [coeff_X_pow_mul_self, Polynomial.mul_coeff_zero,
    Polynomial.mul_coeff_zero, coeff_one_add_X_zero,
    coeff_one_add_X_pow_zero s hs, h]
  norm_num

/-- **The universal chain conservation law.** For every finite stack of
successive paired folds, the chain flat — the iterated flat factor over
the base — decomposes exactly as the composed fold plus the total loss,
where the total loss carries each fold's own loss transported by the
flat factors of all folds applied after it. The Round 53 double
conservation law is the length-two case. -/
theorem chain_conservationOf (P : Polynomial ℚ)
    (L : List (Polynomial ℚ × ℕ)) :
    chainFlat L P = chainFold L P + chainLoss L P := by
  induction L with
  | nil => simp [chainFlat, chainFold, chainLoss]
  | cons f rest ih =>
      obtain ⟨R, s⟩ := f
      have h1 := conservationOf (chainFold rest P) R s
      have h2 := ih
      calc chainFlat ((R, s) :: rest) P
          = (1 + X ^ s) ^ 2 * chainFlat rest P := by simp only [chainFlat]
        _ = (1 + X ^ s) ^ 2 * (chainFold rest P + chainLoss rest P) := by
              rw [h2]
        _ = (1 + X ^ s) ^ 2 * chainFold rest P
            + (1 + X ^ s) ^ 2 * chainLoss rest P := mul_add _ _ _
        _ = (chainFold ((R, s) :: rest) P + lossOf R s)
            + (1 + X ^ s) ^ 2 * chainLoss rest P := by
              simp only [chainFold]
              rw [← h1]
        _ = chainFold ((R, s) :: rest) P
            + (lossOf R s + (1 + X ^ s) ^ 2 * chainLoss rest P) := by
              ring
        _ = chainFold ((R, s) :: rest) P + chainLoss ((R, s) :: rest) P := by
              simp only [chainLoss]

/-- **No loss below the stack minimum.** In every degree below every
shift of the stack, the total loss vanishes: the transport of each
fold's loss past all later flat factors never reaches below the stack's
minimum shift. -/
theorem chainLoss_below_min (P : Polynomial ℚ) (i : ℕ) :
    ∀ L : List (Polynomial ℚ × ℕ),
      (∀ f ∈ L, i < f.2) → (chainLoss L P).coeff i = 0 := by
  intro L
  induction L with
  | nil => intro _; simp [chainLoss]
  | cons f rest ih =>
      obtain ⟨R, s⟩ := f
      intro h
      have hf : i < s := h (R, s) (by simp)
      have hrest : ∀ g ∈ rest, i < g.2 :=
        fun g hg => h g (List.mem_cons_of_mem _ hg)
      simp only [chainLoss, Polynomial.coeff_add]
      rw [coeff_flat_factor_lt _ s i hf, ih hrest]
      have h0 : (lossOf R s).coeff i = 0 := by
        simp only [lossOf]
        exact coeff_X_pow_mul_lt _ s i hf
      rw [h0, add_zero]

/-- **The stack's first lost degree under a strictly-smallest innermost
shift.** If the innermost (first-applied) fold's shift is strictly below
every other shift of the stack, the total loss has coefficient exactly
one in that degree: the first fold's own loss lands undisturbed, every
other fold's loss and every transport vanishing below it. The Round 53
composed first-loss law is the length-two case. -/
theorem chainLoss_inner_first (P R : Polynomial ℚ) (s : ℕ) (hs : 0 < s)
    (hR : R.coeff 0 = 1) :
    ∀ L : List (Polynomial ℚ × ℕ),
      (∀ g ∈ L, s < g.2) → (chainLoss (L ++ [(R, s)]) P).coeff s = 1 := by
  intro L
  induction L with
  | nil =>
      intro _
      simp only [List.nil_append, chainLoss, mul_zero, add_zero]
      exact lossOf_coeff_self R s hs hR
  | cons f rest ih =>
      obtain ⟨R', s'⟩ := f
      intro h
      have hs' : s < s' := h (R', s') (by simp)
      have hrest : ∀ g ∈ rest, s < g.2 :=
        fun g hg => h g (List.mem_cons_of_mem _ hg)
      simp only [List.cons_append, chainLoss, Polynomial.coeff_add]
      rw [coeff_flat_factor_lt _ s' s hs', ih hrest]
      have h0 : (lossOf R' s').coeff s = 0 := by
        simp only [lossOf]
        exact coeff_X_pow_mul_lt _ s' s hs'
      rw [h0, zero_add]

/-- The fold-stack bookkeeping. Fields:

* `base` — the Poincaré polynomial `P_A(t)` of the original rational cup
  algebra;
* `folds` — the fold stack, outermost (last-applied) fold first, each
  entry the cup rank polynomial and shift of one paired fold;
* `cup_zero` — the degree-zero cup rank normalization of every fold in
  the stack (`α ≠ 0` for every fold);
* `shift_pos` — positivity of every fold shift in the stack. -/
structure FoldChain where
  /-- Poincaré polynomial of the original base algebra. -/
  base : Polynomial ℚ
  /-- The fold stack, outermost (last-applied) fold first. -/
  folds : List (Polynomial ℚ × ℕ)
  /-- Degree-zero cup rank normalization of every fold in the stack. -/
  cup_zero : ∀ f ∈ folds, f.1.coeff 0 = 1
  /-- Positivity of every fold shift in the stack. -/
  shift_pos : ∀ f ∈ folds, 0 < f.2
deriving Repr

namespace FoldChain

/-- The chain flat fold: the iterated flat factor over the base. -/
noncomputable def chainFlatF (C : FoldChain) : Polynomial ℚ :=
  chainFlat C.folds C.base

/-- The composed fold of the whole stack. -/
noncomputable def chainFoldF (C : FoldChain) : Polynomial ℚ :=
  chainFold C.folds C.base

/-- The total loss of the whole stack. -/
noncomputable def chainLossF (C : FoldChain) : Polynomial ℚ :=
  chainLoss C.folds C.base

/-- **The exact chain conservation law.** The chain flat fold is the
composed fold plus the total loss, coefficient for coefficient — the
arbitrary-length composed-fold transport law. -/
theorem chain_conservation (C : FoldChain) :
    C.chainFlatF = C.chainFoldF + C.chainLossF :=
  chain_conservationOf C.base C.folds

/-- **No loss below the stack minimum.** Every degree below every shift
of the stack is exactly unchanged by the composition: the total loss
polynomial has no support below the stack's minimum shift. -/
theorem chain_loss_below_min (C : FoldChain) (i : ℕ)
    (h : ∀ f ∈ C.folds, i < f.2) :
    C.chainLossF.coeff i = 0 :=
  chainLoss_below_min C.base i C.folds h

/-- **The composed fold is unchanged below the stack minimum.** In every
degree below every shift the composed-fold polynomial equals the chain
flat polynomial exactly. -/
theorem chain_fold_unchanged_below_min (C : FoldChain) (i : ℕ)
    (h : ∀ f ∈ C.folds, i < f.2) :
    C.chainFoldF.coeff i = C.chainFlatF.coeff i := by
  rw [chain_conservation C, Polynomial.coeff_add,
    chain_loss_below_min C i h, add_zero]

/-- **The stack's degree-one blindness law.** If every fold of the stack
sits at codimension `p ≥ 2` (shift `2p − 1`), the total loss has no
degree-one term: the degree-one curvature test alone cannot see any
stack of `p ≥ 2` folds, of any length. -/
theorem chain_degree_one_blind (C : FoldChain)
    (hp : ∀ f ∈ C.folds, ∃ p, 2 ≤ p ∧ f.2 = 2 * p - 1) :
    C.chainLossF.coeff 1 = 0 := by
  apply chain_loss_below_min
  intro f hf
  obtain ⟨p, hp2, hs⟩ := hp f hf
  have h1 : 1 < f.2 := by rw [hs]; omega
  exact h1

/-- **The stack's first lost degree under a strictly-smallest innermost
shift.** When the innermost fold's shift is strictly below every other
shift of the stack, the total loss's leading term is that fold's own
loss: exactly one class lost in the innermost degree, undisturbed by
every later fold and every transport. -/
theorem chain_inner_first_loss (C : FoldChain) (R : Polynomial ℚ) (s : ℕ)
    (hs : 0 < s) (L : List (Polynomial ℚ × ℕ))
    (hdecomp : C.folds = L ++ [(R, s)])
    (hR : R.coeff 0 = 1) (hmin : ∀ g ∈ L, s < g.2) :
    C.chainLossF.coeff s = 1 := by
  show (chainLoss C.folds C.base).coeff s = 1
  rw [hdecomp]
  exact chainLoss_inner_first C.base R s hs hR L hmin

end FoldChain

end GSTFoldChainThirdOrderMemory

#print axioms GSTFoldChainThirdOrderMemory.JetTower3.tower3Differential_apply
#print axioms GSTFoldChainThirdOrderMemory.JetTower3.base_square_apply
#print axioms GSTFoldChainThirdOrderMemory.JetTower3.memory_apply
#print axioms GSTFoldChainThirdOrderMemory.JetTower3.second_memory_apply
#print axioms GSTFoldChainThirdOrderMemory.JetTower3.third_memory_apply
#print axioms GSTFoldChainThirdOrderMemory.JetTower3.tower3_square_zeroth
#print axioms GSTFoldChainThirdOrderMemory.JetTower3.tower3_square_first
#print axioms GSTFoldChainThirdOrderMemory.JetTower3.tower3_square_second
#print axioms GSTFoldChainThirdOrderMemory.JetTower3.tower3_square_third
#print axioms GSTFoldChainThirdOrderMemory.JetTower3.tower3_square
#print axioms GSTFoldChainThirdOrderMemory.JetTower3.tower3_flat_face
#print axioms GSTFoldChainThirdOrderMemory.JetTower3.tower3_flat_of_curvatures_zero
#print axioms GSTFoldChainThirdOrderMemory.JetTower3.curvature_of_flat_tower3
#print axioms GSTFoldChainThirdOrderMemory.JetTower3.second_curvature_of_flat_tower3
#print axioms GSTFoldChainThirdOrderMemory.JetTower3.third_curvature_of_flat_tower3
#print axioms GSTFoldChainThirdOrderMemory.coeff_flat_factor_lt
#print axioms GSTFoldChainThirdOrderMemory.lossOf_coeff_self
#print axioms GSTFoldChainThirdOrderMemory.chain_conservationOf
#print axioms GSTFoldChainThirdOrderMemory.chainLoss_below_min
#print axioms GSTFoldChainThirdOrderMemory.chainLoss_inner_first
#print axioms GSTFoldChainThirdOrderMemory.FoldChain.chain_conservation
#print axioms GSTFoldChainThirdOrderMemory.FoldChain.chain_loss_below_min
#print axioms GSTFoldChainThirdOrderMemory.FoldChain.chain_fold_unchanged_below_min
#print axioms GSTFoldChainThirdOrderMemory.FoldChain.chain_degree_one_blind
#print axioms GSTFoldChainThirdOrderMemory.FoldChain.chain_inner_first_loss
