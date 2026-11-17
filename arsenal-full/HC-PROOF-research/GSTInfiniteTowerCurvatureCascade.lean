import Mathlib
import GSTFoldTowerSquare

/-!
# GST Round 57 — the infinite tower differential and the curvature cascade

Round 56 (`GSTFoldTowerSquare`) squared the arbitrary-order tower: the
full curvature ladder `D² u j = ∑ i < j, K_i (u (j − 1 − i))` at every
level `j ≤ n`, the flat criterion at arbitrary order, and the infinite
memory tower `JetTowerInf` (the unbounded law at every order, with no
`n`). This round pushes the same line to its two natural limits:

* **The infinite tower differential and THE UNBOUNDED SQUARE.** The
  parameter family `d + ∑_{k ≥ 0} ε^(k+1) φ_k` becomes an actual
  operator on the infinite jet space `ℕ → V`: `D u j = d (u j) +
  ∑ i < j, φ_i (u (j − 1 − i))` at EVERY level `j : ℕ`, with no order
  bound anywhere. THE INFINITE TOWER SQUARE: `D² u j =
  ∑ i < j, K_i (u (j − 1 − i))` at every level of the infinite tower —
  every memory tail absorbed by its own unbounded memory law, the two
  cross tails cancelling exactly into the arbitrary-order law by the
  Round 56 triangle reindexing. THE FULL FLAT CRITERION, INFINITE: the
  square vanishes at every level if and only if every curvature
  carrier vanishes (the concentrated-jet extraction reading every
  carrier off the unbounded ladder's diagonal — no bound, no order).
  The truncation compatibility: the finite tower's differential of
  `toTowerL T n` is the infinite differential, level by level.

* **THE CARRIER TOWER AND THE CURVATURE CASCADE.** The carriers `K_k`
  of a tower are themselves a jet family — so they form a tower: THE
  CARRIER TOWER `carrierTower T` (base zero, jets the carriers of `T`,
  carriers the SELF-CONVOLUTION `K ⊛ K`). The carrier-operator law:
  the carrier tower's differential is exactly the square of `T`'s
  differential. THE FOURTH-ORDER LADDER: `D⁴ u j =
  ∑ i < j, (K ⊛ K)_i (u (j − 1 − i))` — the curvature of the curvature
  is the self-convolution of the carriers, the Jacobi face of the
  ladder. THE CONVOLUTION POWER CASCADE: the `2^m`-fold composition of
  the differential (the `squarePower` family, each step squaring) is
  the differential of the `m`-fold carrier tower (the `carrierPower`
  family) — `D^(2^m) = D_{carrierTower^m(T)}` for every `m`, by one
  induction; flatness is preserved through the whole cascade, and the
  cascade's own ladder reads off the iterated convolutions.

All statements are exact algebraic identities over supplied data
(linear-map identities and finite ℚ-linear-map sum identities),
kernel-verified by the module's own CI lane on the pinned toolchain
`leanprover/lean4:v4.33.0-rc2` with Mathlib. Zero `sorry`, zero axiom
declarations, zero `native_decide`. The geometric identification of
the tower with actual cohomology stays hand-level; no original-X
algebraic-source existence is claimed, assumed, or concluded.
-/

namespace GSTFoldTowerSquare.JetTowerInf

variable {V : Type*} [AddCommGroup V] [Module ℚ V]

/-! ## Face 1 — the infinite tower differential and the unbounded square -/

/-- **The infinite tower differential.** The parameter family
`d + ∑_{k ≥ 0} ε^(k+1) φ_k` acting on the infinite jet space `ℕ → V`:
`D u j = d (u j) + ∑ i < j, φ_i (u (j − 1 − i))` — one differential
for the whole unbounded family, no order anywhere. -/
def jetInfDifferential (T : JetTowerInf V) : (ℕ → V) →ₗ[ℚ] (ℕ → V) where
  toFun u := fun j => T.base (u j) + ∑ i ∈ Finset.range j, (T.jet i) (u (j - 1 - i))
  map_add' := by
    intro u w
    funext j
    show T.base ((u + w) j) + ∑ i ∈ Finset.range j, T.jet i ((u + w) (j - 1 - i))
      = (T.base (u j) + ∑ i ∈ Finset.range j, T.jet i (u (j - 1 - i)))
        + (T.base (w j) + ∑ i ∈ Finset.range j, T.jet i (w (j - 1 - i)))
    have h1 : T.base ((u + w) j) = T.base (u j) + T.base (w j) := by
      rw [Pi.add_apply, map_add]
    have h2 : ∑ i ∈ Finset.range j, T.jet i ((u + w) (j - 1 - i))
        = (∑ i ∈ Finset.range j, T.jet i (u (j - 1 - i)))
          + ∑ i ∈ Finset.range j, T.jet i (w (j - 1 - i)) := by
      rw [← Finset.sum_add_distrib]
      exact Finset.sum_congr rfl fun i _ => by rw [Pi.add_apply, map_add]
    rw [h1, h2]
    abel
  map_smul' := by
    intro r u
    funext j
    show T.base ((r • u) j) + ∑ i ∈ Finset.range j, T.jet i ((r • u) (j - 1 - i))
      = (r : ℚ) • (T.base (u j) + ∑ i ∈ Finset.range j, T.jet i (u (j - 1 - i)))
    have h1 : T.base ((r • u) j) = (r : ℚ) • T.base (u j) := by
      rw [Pi.smul_apply, map_smul]
    have h2 : ∑ i ∈ Finset.range j, T.jet i ((r • u) (j - 1 - i))
        = (r : ℚ) • ∑ i ∈ Finset.range j, T.jet i (u (j - 1 - i)) := by
      have hper : ∀ i ∈ Finset.range j,
          T.jet i ((r • u) (j - 1 - i))
            = (r : ℚ) • T.jet i (u (j - 1 - i)) := by
        intro i _
        rw [Pi.smul_apply, map_smul]
      rw [Finset.sum_congr rfl hper]
      first
        | exact Finset.sum_smul
        | exact (Finset.sum_smul).symm
        | exact Finset.smul_sum
        | exact (Finset.smul_sum).symm
    rw [h1, h2, smul_add]

/-- **The computation rule for the infinite tower differential.** -/
theorem jetInfDifferential_apply (T : JetTowerInf V) (u : ℕ → V) (j : ℕ) :
    T.jetInfDifferential u j
      = T.base (u j) + ∑ i ∈ Finset.range j, T.jet i (u (j - 1 - i)) := rfl

/-- **The unbounded memory law, pointwise.** The infinite tower's
memory law applied at a point — the form the unbounded square proof
consumes, at every order with no bound. -/
theorem memoryInf_apply (T : JetTowerInf V) (m : ℕ) (x : V) :
    T.base (T.jet m x) + T.jet m (T.base x)
      + ∑ r ∈ Finset.range m, T.jet r (T.jet (m - 1 - r) x)
      = T.curv m x := by
  have h := T.memory m
  have hx := congrArg (fun f : V →ₗ[ℚ] V => f x) h
  simpa only [LinearMap.add_apply, LinearMap.comp_apply, LinearMap.sum_apply]
    using hx

/-- **THE INFINITE TOWER SQUARE.** For every level `j` of the infinite
tower — no order, no bound — the square of the infinite differential
is the CURVATURE LADDER: `D² u j = ∑ i < j, K_i (u (j − 1 − i))` —
every level sees the curvature of every level below it, every memory
tail absorbed by its own unbounded memory law, the two cross tails
cancelling exactly into the arbitrary-order law by the triangle
reindexing. The Round 56 square (the `j ≤ n` version) is the
truncation of this identity to the levels below any order. -/
theorem jetInfDifferential_square_apply (T : JetTowerInf V) (u : ℕ → V) (j : ℕ) :
    T.jetInfDifferential (T.jetInfDifferential u) j
      = ∑ m ∈ Finset.range j, T.curv m (u (j - 1 - m)) := by
  have hstep : T.jetInfDifferential (T.jetInfDifferential u) j
      = T.base (T.base (u j))
        + ∑ i ∈ Finset.range j, T.base (T.jet i (u (j - 1 - i)))
        + ∑ i ∈ Finset.range j, T.jet i (T.base (u (j - 1 - i)))
        + ∑ i ∈ Finset.range j, ∑ i' ∈ Finset.range (j - 1 - i),
            T.jet i (T.jet i' (u (j - 1 - i - 1 - i'))) := by
    have h1 := jetInfDifferential_apply T (T.jetInfDifferential u) j
    have h2 := jetInfDifferential_apply T u j
    have h3 : ∀ i ∈ Finset.range j, (T.jetInfDifferential u) (j - 1 - i)
        = T.base (u (j - 1 - i))
          + ∑ i' ∈ Finset.range (j - 1 - i), T.jet i' (u (j - 1 - i - 1 - i')) :=
      fun i _ => jetInfDifferential_apply T u (j - 1 - i)
    have hsum : ∑ i ∈ Finset.range j, T.jet i ((T.jetInfDifferential u) (j - 1 - i))
        = ∑ i ∈ Finset.range j, T.jet i (T.base (u (j - 1 - i)))
          + ∑ i ∈ Finset.range j, ∑ i' ∈ Finset.range (j - 1 - i),
              T.jet i (T.jet i' (u (j - 1 - i - 1 - i'))) := by
      have hexp : ∀ i ∈ Finset.range j, T.jet i ((T.jetInfDifferential u) (j - 1 - i))
          = T.jet i (T.base (u (j - 1 - i)))
            + ∑ i' ∈ Finset.range (j - 1 - i),
                T.jet i (T.jet i' (u (j - 1 - i - 1 - i'))) := by
        intro i hi
        rw [h3 i hi, map_add, map_sum]
      rw [Finset.sum_congr rfl hexp, Finset.sum_add_distrib]
    rw [h1, h2, map_add, map_sum, hsum]
    abel
  have hbb : T.base (T.base (u j)) = 0 := by
    rw [← LinearMap.comp_apply, T.base_square, LinearMap.zero_apply]
  have hmerge : (∑ i ∈ Finset.range j, T.base (T.jet i (u (j - 1 - i))))
      + (∑ i ∈ Finset.range j, T.jet i (T.base (u (j - 1 - i))))
      = ∑ i ∈ Finset.range j, (T.curv i (u (j - 1 - i))
          - ∑ r ∈ Finset.range i, T.jet r (T.jet (i - 1 - r) (u (j - 1 - i)))) := by
    rw [← Finset.sum_add_distrib]
    refine Finset.sum_congr rfl fun i hi => ?_
    have hi' : i < j := Finset.mem_range.mp hi
    have hlaw := memoryInf_apply T i (u (j - 1 - i))
    calc T.base (T.jet i (u (j - 1 - i))) + T.jet i (T.base (u (j - 1 - i)))
        = (T.base (T.jet i (u (j - 1 - i))) + T.jet i (T.base (u (j - 1 - i)))
            + ∑ r ∈ Finset.range i, T.jet r (T.jet (i - 1 - r) (u (j - 1 - i))))
          - ∑ r ∈ Finset.range i, T.jet r (T.jet (i - 1 - r) (u (j - 1 - i))) := by
          abel
      _ = T.curv i (u (j - 1 - i))
          - ∑ r ∈ Finset.range i, T.jet r (T.jet (i - 1 - r) (u (j - 1 - i))) := by
          rw [hlaw]
  have htri : (∑ i ∈ Finset.range j, ∑ r ∈ Finset.range i,
        T.jet r (T.jet (i - 1 - r) (u (j - 1 - i))))
      = ∑ i ∈ Finset.range j, ∑ i' ∈ Finset.range (j - 1 - i),
          T.jet i (T.jet i' (u (j - 1 - i - 1 - i'))) := by
    have hcanon := sum_triangle_succ (fun r i => T.jet r (T.jet (i - 1 - r) (u (j - 1 - i)))) j
    rw [hcanon]
    refine Finset.sum_congr rfl fun p _ => Finset.sum_congr rfl fun q _ => ?_
    rw [show p + q + 1 - 1 - p = q from by omega,
      show j - 1 - (p + q + 1) = j - 1 - p - 1 - q from by omega]
  calc T.jetInfDifferential (T.jetInfDifferential u) j
      = T.base (T.base (u j))
        + ∑ i ∈ Finset.range j, T.base (T.jet i (u (j - 1 - i)))
        + ∑ i ∈ Finset.range j, T.jet i (T.base (u (j - 1 - i)))
        + ∑ i ∈ Finset.range j, ∑ i' ∈ Finset.range (j - 1 - i),
            T.jet i (T.jet i' (u (j - 1 - i - 1 - i'))) := hstep
    _ = ∑ m ∈ Finset.range j, T.curv m (u (j - 1 - m)) := by
        rw [hbb, zero_add, hmerge, Finset.sum_sub_distrib, htri]
        abel

/-- **Level zero of the unbounded ladder.** The square of the infinite
differential at the head is the square of the flat base — zero. -/
theorem jetInfDifferential_square_zero (T : JetTowerInf V) (u : ℕ → V) :
    T.jetInfDifferential (T.jetInfDifferential u) 0 = 0 := by
  have h := jetInfDifferential_square_apply T u 0
  simpa using h

/-- **THE UNBOUNDED FLAT LADDER COLLAPSE.** In a flat infinite tower
the square vanishes at every level, with no bound: the whole unbounded
ladder collapses. -/
theorem flat_inf_tower_square (T : JetTowerInf V) (hflat : T.IsFlat)
    (u : ℕ → V) (j : ℕ) :
    T.jetInfDifferential (T.jetInfDifferential u) j = 0 := by
  rw [jetInfDifferential_square_apply T u j]
  refine Finset.sum_eq_zero fun m hm => ?_
  rw [hflat m, LinearMap.zero_apply]

/-- **THE CONCENTRATED-JET EXTRACTION, UNBOUNDED.** If the square of
the infinite differential vanishes at every level, every curvature
carrier vanishes — each carrier read off the unbounded ladder's
diagonal by the jet concentrated at level zero, at every order with no
bound. -/
theorem curvature_inf_of_square_zero (T : JetTowerInf V)
    (h : ∀ u : ℕ → V, ∀ j : ℕ,
      T.jetInfDifferential (T.jetInfDifferential u) j = 0)
    (m : ℕ) (x : V) :
    T.curv m x = 0 := by
  have hlevel : T.jetInfDifferential
      (T.jetInfDifferential (fun t => if t = 0 then x else 0)) (m + 1) = 0 :=
    h (fun t => if t = 0 then x else 0) (m + 1)
  rw [jetInfDifferential_square_apply (T := T)
    (u := fun t => if t = 0 then x else 0) (j := m + 1)] at hlevel
  have hsum : ∑ i ∈ Finset.range (m + 1),
      T.curv i ((fun t => if t = 0 then x else 0) (m + 1 - 1 - i))
      = T.curv m x := by
    rw [Finset.sum_range_succ]
    have hzero : ∀ i ∈ Finset.range m,
        T.curv i ((fun t => if t = 0 then x else 0) (m + 1 - 1 - i)) = 0 := by
      intro i hi
      have hi' : i < m := Finset.mem_range.mp hi
      show T.curv i (if m + 1 - 1 - i = 0 then x else 0) = 0
      rw [if_neg (show ¬ (m + 1 - 1 - i = 0) by omega), map_zero]
    rw [Finset.sum_eq_zero hzero, zero_add]
    show T.curv m (if m + 1 - 1 - m = 0 then x else 0) = T.curv m x
    rw [show m + 1 - 1 - m = 0 from by omega, if_pos rfl]
  rw [hsum] at hlevel
  exact hlevel

/-- **THE FULL FLAT CRITERION, INFINITE.** The square of the infinite
tower differential vanishes at every level if and only if the
infinite tower is flat — the complete two-sided flat criterion with no
order anywhere: the ε-family `d + ∑ ε^(k+1) φ_k` squares to zero
exactly when every curvature carrier vanishes. -/
theorem square_inf_zero_iff_flat (T : JetTowerInf V) :
    (∀ u : ℕ → V, ∀ j : ℕ,
      T.jetInfDifferential (T.jetInfDifferential u) j = 0)
      ↔ T.IsFlat := by
  constructor
  · intro h m
    ext x
    simpa using curvature_inf_of_square_zero T h m x
  · intro hflat u j
    exact flat_inf_tower_square T hflat u j

/-- **The truncation compatibility.** The finite tower's differential
of the truncation is the infinite differential, level by level: the
Round 56 square law and this round's unbounded square law are the same
identity on the same levels. -/
theorem toTowerL_jetLDifferential (T : JetTowerInf V) (n : ℕ) (u : ℕ → V) (j : ℕ) :
    (T.toTowerL n).jetLDifferential u j = T.jetInfDifferential u j := by
  rw [GSTFoldFourthOrderMemoryTower.JetTowerL.jetLDifferential_apply
      (T.toTowerL n) u j, jetInfDifferential_apply T u j]
  rfl

/-! ## Face 2 — the carrier tower and the curvature cascade -/

/-- **The carrier convolution.** The convolution of two carrier
families: the k-th carrier of the composite is the sum of all composites
`K_i ∘ L_{k-1-i}` with `i < k` — the convolution product of the
curvature algebra, the algebra of the ε-family's defects. -/
def carrierConvolution (K L : ℕ → (V →ₗ[ℚ] V)) : ℕ → (V →ₗ[ℚ] V) :=
  fun k => ∑ i ∈ Finset.range k, (K i).comp (L (k - 1 - i))

/-- **THE CARRIER TOWER.** The tower whose jets are the curvature
carriers of `T` and whose carriers are the self-convolution `K ⊛ K`:
the curvature of the curvature — the Jacobi face of the memory tower.
Its base is zero (the carrier ladder has no flat part) and its memory
law holds by construction: the convolution IS the anticommutator-free
part of the carrier family's own law. -/
def carrierTower (T : JetTowerInf V) : JetTowerInf V where
  base := 0
  base_square := by ext x; simp [LinearMap.comp_apply]
  jet := T.curv
  curv := carrierConvolution T.curv T.curv
  memory := by
    intro k
    ext x
    simp [carrierConvolution, LinearMap.comp_apply, LinearMap.add_apply,
      LinearMap.sum_apply, LinearMap.zero_apply, map_zero]

/-- **The carrier tower's carriers are the self-convolution.** -/
theorem carrierTower_curv (T : JetTowerInf V) (k : ℕ) :
    (carrierTower T).curv k = carrierConvolution T.curv T.curv k := rfl

/-- **Flat towers have flat carrier towers.** The cascade preserves
flatness: if every curvature carrier of `T` vanishes, every
self-convolution carrier vanishes — the curvature of the curvature of
a flat family is zero. -/
theorem flat_carrierTower (T : JetTowerInf V) (hflat : T.IsFlat) :
    (carrierTower T).IsFlat := by
  intro k
  show ∑ i ∈ Finset.range k, (T.curv i).comp (T.curv (k - 1 - i)) = 0
  refine Finset.sum_eq_zero fun i _ => ?_
  rw [hflat i, hflat (k - 1 - i)]
  ext x
  simp [LinearMap.comp_apply, LinearMap.zero_apply, map_zero]

/-- **The pointwise carrier-operator law.** The carrier tower's
differential at a level is the square of the original tower's
differential at that level: `D_{K(T)} u j = D² u j`. -/
theorem jetInfDifferential_carrier_apply (T : JetTowerInf V) (u : ℕ → V) (j : ℕ) :
    (carrierTower T).jetInfDifferential u j
      = T.jetInfDifferential (T.jetInfDifferential u) j := by
  have hL : (carrierTower T).jetInfDifferential u j
      = ∑ i ∈ Finset.range j, T.curv i (u (j - 1 - i)) := by
    show (0 : V →ₗ[ℚ] V) (u j)
        + ∑ i ∈ Finset.range j, T.curv i (u (j - 1 - i))
      = ∑ i ∈ Finset.range j, T.curv i (u (j - 1 - i))
    rw [LinearMap.zero_apply, zero_add]
  rw [hL, jetInfDifferential_square_apply T u j]

/-- **THE CARRIER-OPERATOR LAW.** The carrier tower's differential IS
the square of the tower's differential, as operators:
`D_{K(T)} = D_T ∘ D_T`. The curvature of a family is a family; the
square of the ε-family's differential is the ε-family of the
carriers. -/
theorem carrierTower_differential (T : JetTowerInf V) :
    (carrierTower T).jetInfDifferential
      = T.jetInfDifferential.comp T.jetInfDifferential := by
  ext u j
  exact jetInfDifferential_carrier_apply T u j

/-- **THE FOURTH-ORDER LADDER.** The fourth iterate of the infinite
differential at every level is the SELF-CONVOLUTION ladder:
`D⁴ u j = ∑ i < j, (K ⊛ K)_i (u (j − 1 − i))` — the curvature of the
curvature is the convolution of the carriers with themselves. On a
flat tower every convolution carrier vanishes and the whole fourth
ladder collapses; on a non-flat tower the fourth ladder measures the
quadratic defect. -/
theorem jetInfDifferential_fourth_order (T : JetTowerInf V) (u : ℕ → V) (j : ℕ) :
    T.jetInfDifferential
        (T.jetInfDifferential (T.jetInfDifferential (T.jetInfDifferential u))) j
      = ∑ m ∈ Finset.range j, carrierConvolution T.curv T.curv m (u (j - 1 - m)) := by
  have h4 := jetInfDifferential_square_apply T
    (T.jetInfDifferential (T.jetInfDifferential u)) j
  have hinner : ∀ m ∈ Finset.range j,
      T.curv m (T.jetInfDifferential (T.jetInfDifferential u) (j - 1 - m))
        = ∑ i ∈ Finset.range (j - 1 - m),
            T.curv m (T.curv i (u (j - 1 - m - 1 - i))) := by
    intro m _
    rw [jetInfDifferential_square_apply T u (j - 1 - m), map_sum]
  have hunf : ∀ m ∈ Finset.range j,
      carrierConvolution T.curv T.curv m (u (j - 1 - m))
        = ∑ i ∈ Finset.range m, T.curv i (T.curv (m - 1 - i) (u (j - 1 - m))) := by
    intro m _
    show (∑ i ∈ Finset.range m, (T.curv i).comp (T.curv (m - 1 - i))) (u (j - 1 - m))
      = ∑ i ∈ Finset.range m, T.curv i (T.curv (m - 1 - i) (u (j - 1 - m)))
    rw [LinearMap.sum_apply]
    rfl
  rw [h4, Finset.sum_congr rfl hinner, Finset.sum_congr rfl hunf]
  have htri2 := sum_triangle_succ
    (fun r i => T.curv r (T.curv (i - 1 - r) (u (j - 1 - i)))) j
  rw [htri2]
  refine Finset.sum_congr rfl fun p _ => Finset.sum_congr rfl fun q _ => ?_
  rw [show p + q + 1 - 1 - p = q from by omega,
    show j - 1 - (p + q + 1) = j - 1 - p - 1 - q from by omega]

/-- **The square-power family.** The `2^m`-fold composition of a
differential: `D^(2^0) = D`, each step squaring — the operator side of
the cascade. -/
def squarePower (D : (ℕ → V) →ₗ[ℚ] (ℕ → V)) : ℕ → ((ℕ → V) →ₗ[ℚ] (ℕ → V))
  | 0 => D
  | m + 1 => (squarePower D m).comp (squarePower D m)

/-- **The carrier-power family.** The `m`-fold carrier tower: each step
takes the carrier tower of the previous — the tower side of the
cascade. -/
def carrierPower (T : JetTowerInf V) : ℕ → JetTowerInf V
  | 0 => T
  | m + 1 => carrierTower (carrierPower T m)

/-- **THE CONVOLUTION POWER CASCADE.** For every `m`, the `2^m`-fold
composition of the infinite differential is the differential of the
`m`-fold carrier tower: `D^(2^m) = D_{carrierTower^m(T)}` — one
induction on the carrier-operator law. The iterated curvatures of the
cascade are the iterated convolutions of the carriers. -/
theorem carrierPower_differential (T : JetTowerInf V) (m : ℕ) :
    (carrierPower T m).jetInfDifferential
      = squarePower T.jetInfDifferential m := by
  induction m with
  | zero => rfl
  | succ m ih =>
    show (carrierTower (carrierPower T m)).jetInfDifferential
      = (squarePower T.jetInfDifferential m).comp (squarePower T.jetInfDifferential m)
    rw [carrierTower_differential, ← ih]

/-- **The flat cascade.** Flatness is preserved through the whole
carrier-power cascade: every `m`-fold carrier tower of a flat tower is
flat — the iterated curvature of a flat family vanishes at every
order of the cascade. -/
theorem carrierPower_flat (T : JetTowerInf V) (hflat : T.IsFlat) (m : ℕ) :
    (carrierPower T m).IsFlat := by
  induction m with
  | zero => exact hflat
  | succ m ih => exact flat_carrierTower (carrierPower T m) ih

/-- **THE CASCADE LADDER.** The differential of the `m+1`-fold carrier
tower at every level is its own jet ladder — the carriers of the
`m`-fold tower, at every level: the cascade's pointwise readout of the
iterated convolutions, with zero flat part. -/
theorem carrierPower_succ_apply (T : JetTowerInf V) (m : ℕ) (u : ℕ → V) (j : ℕ) :
    (carrierPower T (m + 1)).jetInfDifferential u j
      = ∑ i ∈ Finset.range j, (carrierPower T (m + 1)).jet i (u (j - 1 - i)) := by
  show (carrierTower (carrierPower T m)).jetInfDifferential u j
      = ∑ i ∈ Finset.range j, (carrierPower T m).curv i (u (j - 1 - i))
  have hD : (carrierTower (carrierPower T m)).jetInfDifferential u j
      = ∑ i ∈ Finset.range j, (carrierPower T m).curv i (u (j - 1 - i)) := by
    show (0 : V →ₗ[ℚ] V) (u j)
        + ∑ i ∈ Finset.range j, (carrierPower T m).curv i (u (j - 1 - i))
      = ∑ i ∈ Finset.range j, (carrierPower T m).curv i (u (j - 1 - i))
    rw [LinearMap.zero_apply, zero_add]
  rw [hD]

end GSTFoldTowerSquare.JetTowerInf

#print axioms GSTFoldTowerSquare.JetTowerInf.jetInfDifferential_apply
#print axioms GSTFoldTowerSquare.JetTowerInf.memoryInf_apply
#print axioms GSTFoldTowerSquare.JetTowerInf.jetInfDifferential_square_apply
#print axioms GSTFoldTowerSquare.JetTowerInf.jetInfDifferential_square_zero
#print axioms GSTFoldTowerSquare.JetTowerInf.flat_inf_tower_square
#print axioms GSTFoldTowerSquare.JetTowerInf.curvature_inf_of_square_zero
#print axioms GSTFoldTowerSquare.JetTowerInf.square_inf_zero_iff_flat
#print axioms GSTFoldTowerSquare.JetTowerInf.toTowerL_jetLDifferential
#print axioms GSTFoldTowerSquare.JetTowerInf.carrierTower_curv
#print axioms GSTFoldTowerSquare.JetTowerInf.flat_carrierTower
#print axioms GSTFoldTowerSquare.JetTowerInf.jetInfDifferential_carrier_apply
#print axioms GSTFoldTowerSquare.JetTowerInf.carrierTower_differential
#print axioms GSTFoldTowerSquare.JetTowerInf.jetInfDifferential_fourth_order
#print axioms GSTFoldTowerSquare.JetTowerInf.carrierPower_differential
#print axioms GSTFoldTowerSquare.JetTowerInf.carrierPower_flat
#print axioms GSTFoldTowerSquare.JetTowerInf.carrierPower_succ_apply
