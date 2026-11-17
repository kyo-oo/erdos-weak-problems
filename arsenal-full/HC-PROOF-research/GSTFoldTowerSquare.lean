import Mathlib
import GSTFoldFourthOrderMemoryTower

/-!
# GST Round 56 — the arbitrary-order tower square and the infinite memory tower

Round 55 (`GSTFoldFourthOrderMemoryTower`) built the arbitrary-order
memory tower `JetTowerL`: the memory jets as ℕ-indexed families of
finite order `n`, the single memory law
`dφ_k + φ_k d + ∑ i + j = k − 1 φ_i φ_j = K_k` at every `k < n`, and the
unification of Rounds 52–54's explicit towers as its order-1, 2, 3, 4
instances. This round closes the ladder in both remaining directions:

* **The arbitrary-order tower square** — the full curvature ladder at
  EVERY order at once. The tower differential `D` acts on the infinite
  jet space `ℕ → V` by `D u j = d (u j) + ∑ i < j, φ_i (u (j − 1 − i))`
  (the parameter family `d + ∑ ε^(k+1) φ_k` on jets of every level).
  THE TOWER SQUARE LAW: for every level `j ≤ n`,
  `D² u j = ∑ i < j, K_i (u (j − 1 − i))` — every level of the tower
  sees the curvature of every level below it, every memory tail
  absorbed by its own memory law, and the two cross tails cancelling
  exactly into the arbitrary-order law. The explicit curvature
  ladders of Rounds 53–55 (the `j ≤ 2, 3, 4` instances) are the
  low-order cases of this one identity. The flat criterion is the full
  iff: the square vanishes at every level iff every curvature carrier
  below the order vanishes (the concentrated-jet extraction reading
  every carrier off the ladder's diagonal).

* **The infinite memory tower** `JetTowerInf` — the complete formal
  family `d + ∑_{k ≥ 0} ε^(k+1) φ_k`: the memory law at EVERY order,
  with no bound. Every finite tower series of Rounds 52–55 is a
  truncation of one infinite tower whenever the unbounded law holds.
  The flat predicates, the flat-head law, the infinite flat-tower
  recursion, and THE ORIGIN TOWER: every flat base `d` (with `d² = 0`)
  generates the trivial infinite memory tower.

The heart of the square law is the TRIANGLE REINDEXING LAW
(`sum_triangle_succ`): the two triangular indexings of the strict
lower triangle `{(p, q) : p + q ≤ j − 2}` coincide — the cross-cancellation
at every level is one instance of this single combinatorial identity.

All statements are exact algebraic identities over supplied data
(linear-map identities and finite ℚ-linear-map sum identities),
kernel-verified by the module's own CI lane on the pinned toolchain
`leanprover/lean4:v4.33.0-rc2` with Mathlib. Zero `sorry`, zero axiom
declarations, zero `native_decide`. The geometric identification of
the tower with actual cohomology stays hand-level; no original-X
algebraic-source existence is claimed, assumed, or concluded.
-/

namespace GSTFoldTowerSquare

variable {V : Type*} [AddCommGroup V] [Module ℚ V]

open GSTFoldFourthOrderMemoryTower

/-! ## The triangle reindexing law -/

/-- **The triangle reindexing law.** The two triangular indexings of the
strict lower triangle `{(p, q) : p + q ≤ j − 2}` — by the outer level
(first summand) and by the first coordinate (second summand) — compute
the same sum. This is the combinatorial heart of the tower square's
cross-cancellation. -/
theorem sum_triangle_succ {M : Type*} [AddCommMonoid M] (G : ℕ → ℕ → M) (j : ℕ) :
    ∑ i ∈ Finset.range j, ∑ r ∈ Finset.range i, G r i
      = ∑ p ∈ Finset.range j, ∑ q ∈ Finset.range (j - 1 - p), G p (p + q + 1) := by
  have key : ∀ n : ℕ, n + 1 - 1 = n := fun n => by omega
  induction j with
  | zero => simp
  | succ j ih =>
    have hL : ∑ i ∈ Finset.range (j + 1), ∑ r ∈ Finset.range i, G r i
        = (∑ i ∈ Finset.range j, ∑ r ∈ Finset.range i, G r i)
          + ∑ r ∈ Finset.range j, G r j :=
      Finset.sum_range_succ (fun i => ∑ r ∈ Finset.range i, G r i) j
    have hinner : ∀ p ∈ Finset.range j,
        ∑ q ∈ Finset.range (j - p), G p (p + q + 1)
          = (∑ q ∈ Finset.range (j - 1 - p), G p (p + q + 1))
            + G p (p + (j - 1 - p) + 1) := by
      intro p hp
      have hp' : p < j := Finset.mem_range.mp hp
      have hn : j - p = (j - 1 - p) + 1 := by omega
      rw [hn, Finset.sum_range_succ]
    have hR : ∑ p ∈ Finset.range (j + 1), ∑ q ∈ Finset.range (j + 1 - 1 - p),
          G p (p + q + 1)
        = (∑ p ∈ Finset.range j, ∑ q ∈ Finset.range (j - 1 - p), G p (p + q + 1))
          + ∑ p ∈ Finset.range j, G p j := by
      simp only [key, Finset.sum_range_succ, Nat.sub_self,
        Finset.sum_range_zero, add_zero]
      rw [Finset.sum_congr rfl hinner, Finset.sum_add_distrib]
      have hlast : ∑ p ∈ Finset.range j, G p (p + (j - 1 - p) + 1)
          = ∑ p ∈ Finset.range j, G p j := by
        refine Finset.sum_congr rfl fun p hp => ?_
        have hp' : p < j := Finset.mem_range.mp hp
        exact congrArg (G p) (show p + (j - 1 - p) + 1 = j by omega)
      rw [hlast]
    rw [hL, hR, ih]

/-- **The single-level peel under a truncated bound.** For `p < n`, the
sum over `range (n − p)` peels one term off `range (n − 1 − p)`. -/
theorem sum_range_sub_succ {M : Type*} [AddCommMonoid M] {n p : ℕ} (hp : p < n)
    (h : ℕ → M) :
    ∑ q ∈ Finset.range (n - p), h q
      = (∑ q ∈ Finset.range (n - 1 - p), h q) + h (n - 1 - p) := by
  have hn : n - p = (n - 1 - p) + 1 := by omega
  rw [hn, Finset.sum_range_succ]

end GSTFoldTowerSquare

open GSTFoldTowerSquare

namespace GSTFoldFourthOrderMemoryTower.JetTowerL

variable {V : Type*} [AddCommGroup V] [Module ℚ V]

/-! ## The pointwise arbitrary-order memory law -/

/-- **The memory law, pointwise.** The arbitrary-order law of Round 55
applied at a point — the form the tower square proof consumes. -/
theorem memory_apply (T : JetTowerL V) {m : ℕ} (hm : m < T.order) (x : V) :
    T.base (T.jet m x) + T.jet m (T.base x)
      + ∑ r ∈ Finset.range m, T.jet r (T.jet (m - 1 - r) x)
      = T.curv m x := by
  have h := T.memory m hm
  have hx := congrArg (fun f : V →ₗ[ℚ] V => f x) h
  simpa only [LinearMap.add_apply, LinearMap.comp_apply, LinearMap.sum_apply]
    using hx

/-! ## The tower differential on the infinite jet space -/

/-- **The tower differential.** The parameter family
`d + ∑ ε^(k+1) φ_k` acts on the infinite jet space `ℕ → V` by
`D u j = d (u j) + ∑ i < j, φ_i (u (j − 1 − i))` — one differential for
every order at once. -/
def jetLDifferential (T : JetTowerL V) : (ℕ → V) →ₗ[ℚ] (ℕ → V) where
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

/-- **The computation rule for the tower differential.** -/
theorem jetLDifferential_apply (T : JetTowerL V) (u : ℕ → V) (j : ℕ) :
    T.jetLDifferential u j
      = T.base (u j) + ∑ i ∈ Finset.range j, T.jet i (u (j - 1 - i)) := rfl

/-! ## THE ARBITRARY-ORDER TOWER SQUARE — the full curvature ladder -/

/-- **THE TOWER SQUARE LAW AT EVERY ORDER.** For every level `j` below or
at the order, the square of the tower differential is the CURVATURE
LADDER: `D² u j = ∑ i < j, K_i (u (j − 1 − i))` — every level of the
tower sees the curvature of every level below it, every memory tail
absorbed by its own memory law, the two cross tails cancelling exactly
into the arbitrary-order law (the triangle reindexing). The explicit
curvature ladders of Rounds 53–55 are the `j ≤ 2, 3, 4` instances. -/
theorem jetLDifferential_square_apply (T : JetTowerL V) (u : ℕ → V)
    {j : ℕ} (hj : j ≤ T.order) :
    T.jetLDifferential (T.jetLDifferential u) j
      = ∑ m ∈ Finset.range j, T.curv m (u (j - 1 - m)) := by
  have hstep : T.jetLDifferential (T.jetLDifferential u) j
      = T.base (T.base (u j))
        + ∑ i ∈ Finset.range j, T.base (T.jet i (u (j - 1 - i)))
        + ∑ i ∈ Finset.range j, T.jet i (T.base (u (j - 1 - i)))
        + ∑ i ∈ Finset.range j, ∑ i' ∈ Finset.range (j - 1 - i),
            T.jet i (T.jet i' (u (j - 1 - i - 1 - i'))) := by
    have h1 := jetLDifferential_apply T (T.jetLDifferential u) j
    have h2 := jetLDifferential_apply T u j
    have h3 : ∀ i ∈ Finset.range j, (T.jetLDifferential u) (j - 1 - i)
        = T.base (u (j - 1 - i))
          + ∑ i' ∈ Finset.range (j - 1 - i), T.jet i' (u (j - 1 - i - 1 - i')) :=
      fun i _ => jetLDifferential_apply T u (j - 1 - i)
    have hsum : ∑ i ∈ Finset.range j, T.jet i ((T.jetLDifferential u) (j - 1 - i))
        = ∑ i ∈ Finset.range j, T.jet i (T.base (u (j - 1 - i)))
          + ∑ i ∈ Finset.range j, ∑ i' ∈ Finset.range (j - 1 - i),
              T.jet i (T.jet i' (u (j - 1 - i - 1 - i'))) := by
      have hexp : ∀ i ∈ Finset.range j, T.jet i ((T.jetLDifferential u) (j - 1 - i))
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
    have hlaw := memory_apply T (show i < T.order by omega) (u (j - 1 - i))
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
    have hcanon : (∑ i ∈ Finset.range j, ∑ r ∈ Finset.range i,
          T.jet r (T.jet (i - 1 - r) (u (j - 1 - i))))
        = ∑ p ∈ Finset.range j, ∑ q ∈ Finset.range (j - 1 - p),
            T.jet p (T.jet (p + q + 1 - 1 - p) (u (j - 1 - (p + q + 1)))) :=
      sum_triangle_succ (fun r i => T.jet r (T.jet (i - 1 - r) (u (j - 1 - i)))) j
    rw [hcanon]
    refine Finset.sum_congr rfl fun p _ => Finset.sum_congr rfl fun q _ => ?_
    rw [show p + q + 1 - 1 - p = q from by omega,
      show j - 1 - (p + q + 1) = j - 1 - p - 1 - q from by omega]
  calc T.jetLDifferential (T.jetLDifferential u) j
      = T.base (T.base (u j))
        + ∑ i ∈ Finset.range j, T.base (T.jet i (u (j - 1 - i)))
        + ∑ i ∈ Finset.range j, T.jet i (T.base (u (j - 1 - i)))
        + ∑ i ∈ Finset.range j, ∑ i' ∈ Finset.range (j - 1 - i),
            T.jet i (T.jet i' (u (j - 1 - i - 1 - i'))) := hstep
    _ = ∑ m ∈ Finset.range j, T.curv m (u (j - 1 - m)) := by
        rw [hbb, zero_add, hmerge, Finset.sum_sub_distrib, htri]
        abel

/-- **Level zero of the ladder.** The square of the tower at the head is
the square of the flat base — zero. -/
theorem jetLDifferential_square_zero (T : JetTowerL V) (u : ℕ → V) :
    T.jetLDifferential (T.jetLDifferential u) 0 = 0 := by
  have h := jetLDifferential_square_apply T u (Nat.zero_le T.order)
  simpa using h

/-- **THE FLAT LADDER COLLAPSE.** In a flat tower the square vanishes at
every level below or at the order: the whole ladder collapses. -/
theorem flat_tower_square (T : JetTowerL V) (hflat : T.IsFlat) (u : ℕ → V)
    {j : ℕ} (hj : j ≤ T.order) :
    T.jetLDifferential (T.jetLDifferential u) j = 0 := by
  rw [jetLDifferential_square_apply T u hj]
  refine Finset.sum_eq_zero fun m hm => ?_
  have hm'' : m < j := Finset.mem_range.mp hm
  have hm' : m < T.order := by omega
  rw [hflat m hm', LinearMap.zero_apply]

/-- **THE CONCENTRATED-JET EXTRACTION.** If the square vanishes at every
level, every curvature carrier below the order vanishes: each carrier
is read off the ladder's diagonal by the jet concentrated at level
zero. -/
theorem curvature_of_square_zero (T : JetTowerL V)
    (h : ∀ u : ℕ → V, ∀ j ≤ T.order,
      T.jetLDifferential (T.jetLDifferential u) j = 0)
    {m : ℕ} (hm : m < T.order) (x : V) :
    T.curv m x = 0 := by
  have hlevel : T.jetLDifferential
      (T.jetLDifferential (fun t => if t = 0 then x else 0)) (m + 1) = 0 :=
    h (fun t => if t = 0 then x else 0) (m + 1) (by omega)
  rw [jetLDifferential_square_apply (T := T)
    (u := fun t => if t = 0 then x else 0) (j := m + 1)
    (by omega : m + 1 ≤ T.order)] at hlevel
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

/-- **THE FULL FLAT CRITERION AT ARBITRARY ORDER.** The square of the
tower vanishes at every level below or at the order if and only if the
tower is flat — the complete extension of the Rounds 53–55 two-sided
flat criteria to every order at once. -/
theorem square_zero_iff_flat (T : JetTowerL V) :
    (∀ u : ℕ → V, ∀ j ≤ T.order,
      T.jetLDifferential (T.jetLDifferential u) j = 0)
      ↔ T.IsFlat := by
  constructor
  · intro h
    intro m hm
    ext x
    simpa using curvature_of_square_zero T h hm x
  · intro hflat u j hj
    exact flat_tower_square T hflat u hj

end GSTFoldFourthOrderMemoryTower.JetTowerL

namespace GSTFoldTowerSquare

variable {V : Type*} [AddCommGroup V] [Module ℚ V]

/-! ## The infinite memory tower -/

/-- **The infinite memory tower.** The complete formal family
`d + ∑_{k ≥ 0} ε^(k+1) φ_k`: the memory law holds at EVERY order, with
no bound. The finite towers of Rounds 52–55 are the finite-order faces. -/
structure JetTowerInf (V : Type*) [AddCommGroup V] [Module ℚ V] where
  /-- The flat base differential `d`. -/
  base : V →ₗ[ℚ] V
  /-- Flatness of the base: `d² = 0`. -/
  base_square : base.comp base = 0
  /-- The memory jets `φ_k` — the ε^(k+1)-coefficients, at every order. -/
  jet : ℕ → (V →ₗ[ℚ] V)
  /-- The curvature carriers `K_k`. -/
  curv : ℕ → (V →ₗ[ℚ] V)
  /-- The memory law at EVERY order `k`, unbounded:
  `dφ_k + φ_k d + ∑ i + j = k − 1 φᵢφⱼ = K_k`. -/
  memory : ∀ k : ℕ,
    base.comp (jet k) + (jet k).comp base
      + ∑ i ∈ Finset.range k, (jet i).comp (jet (k - 1 - i))
      = curv k

namespace JetTowerInf

/-- **The flat predicate:** every curvature carrier, at every order,
vanishes identically. -/
def IsFlat (T : JetTowerInf V) : Prop := ∀ k : ℕ, T.curv k = 0

/-- **The truncation.** Every infinite tower is an arbitrary-order tower
at every finite order: the memory laws below the order are instances
of the unbounded law. -/
def toTowerL (T : JetTowerInf V) (n : ℕ) :
    GSTFoldFourthOrderMemoryTower.JetTowerL V where
  base := T.base
  base_square := T.base_square
  order := n
  jet := T.jet
  curv := T.curv
  memory := by
    intro k hk
    exact T.memory k

/-- **Flatness truncates.** A flat infinite tower is flat at every
finite order. -/
theorem flat_of_flat_inf (T : JetTowerInf V) (h : T.IsFlat) (n : ℕ) :
    (T.toTowerL n).IsFlat := by
  intro k _
  exact h k

/-- **The infinite flat-head law.** In a flat infinite tower the first
memory jet's anticommutator vanishes. -/
theorem flat_head_inf (T : JetTowerInf V) (h : T.IsFlat) :
    T.base.comp (T.jet 0) + (T.jet 0).comp T.base = 0 := by
  have h0 := T.memory 0
  simp only [Finset.sum_range_zero, add_zero] at h0
  rw [h 0] at h0
  exact h0

/-- **THE INFINITE FLAT-TOWER RECURSION.** In a flat infinite tower the
anticommutator of every jet is minus its convolution — each order's
memory forced by the lower orders' products, at every order without
bound. -/
theorem flat_memory_recursion_inf (T : JetTowerInf V) (h : T.IsFlat)
    (k : ℕ) :
    T.base.comp (T.jet k) + (T.jet k).comp T.base
      + ∑ i ∈ Finset.range k, (T.jet i).comp (T.jet (k - 1 - i)) = 0 := by
  have hlaw := T.memory k
  rw [h k] at hlaw
  exact hlaw

/-- **THE ORIGIN TOWER.** Every flat base `d` (with `d² = 0`) generates
the trivial infinite memory tower: all memory jets zero, all curvature
carriers zero — the ε-family is `d + 0` at every order, and the
unbounded law holds trivially at every order. -/
def originTower (d : V →ₗ[ℚ] V) (hd : d.comp d = 0) : JetTowerInf V where
  base := d
  base_square := hd
  jet := fun _ => 0
  curv := fun _ => 0
  memory := by
    intro k
    ext x
    simp [LinearMap.add_apply, LinearMap.comp_apply, LinearMap.sum_apply,
      LinearMap.zero_apply, map_zero, Finset.sum_const_zero]

/-- **The origin tower is flat.** -/
theorem originTower_isFlat (d : V →ₗ[ℚ] V) (hd : d.comp d = 0) :
    (originTower d hd).IsFlat := fun _ => rfl

end JetTowerInf

end GSTFoldTowerSquare

#print axioms GSTFoldTowerSquare.sum_triangle_succ
#print axioms GSTFoldTowerSquare.sum_range_sub_succ
#print axioms GSTFoldFourthOrderMemoryTower.JetTowerL.memory_apply
#print axioms GSTFoldFourthOrderMemoryTower.JetTowerL.jetLDifferential_apply
#print axioms GSTFoldFourthOrderMemoryTower.JetTowerL.jetLDifferential_square_apply
#print axioms GSTFoldFourthOrderMemoryTower.JetTowerL.jetLDifferential_square_zero
#print axioms GSTFoldFourthOrderMemoryTower.JetTowerL.flat_tower_square
#print axioms GSTFoldFourthOrderMemoryTower.JetTowerL.curvature_of_square_zero
#print axioms GSTFoldFourthOrderMemoryTower.JetTowerL.square_zero_iff_flat
#print axioms GSTFoldTowerSquare.JetTowerInf.toTowerL
#print axioms GSTFoldTowerSquare.JetTowerInf.flat_of_flat_inf
#print axioms GSTFoldTowerSquare.JetTowerInf.flat_head_inf
#print axioms GSTFoldTowerSquare.JetTowerInf.flat_memory_recursion_inf
#print axioms GSTFoldTowerSquare.JetTowerInf.originTower
#print axioms GSTFoldTowerSquare.JetTowerInf.originTower_isFlat
