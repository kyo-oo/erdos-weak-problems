import GSTGraphV2SixAdicOntologicalGeometry

/-!
# Laws of GST Graph V2 Six-Adic Ontological Geometry

Theorems in this file split into two layers.

* Arithmetic six-adic laws: exact congruence, non-Archimedean threshold law,
  nested balls, six-way refinement centers, and dyadic/triadic shadows.
* GST compatibility laws: the six-adic resolution is an overlay on the
  existing seven-axis ontology and is respected by the physical x4 chart.

No analytic completion is assumed: all statements are finite, exact, and
kernel-checkable over `Int`/`Nat`.
-/

namespace GSTGraphV2SixAdicOntologicalGeometryLaws

open GSTGraphV2NonEuclidean
open GSTGraphV2SixAdicOntologicalGeometry

/-! ## Six-adic equivalence and non-Archimedean threshold laws -/

theorem six_iso_refl (k : Nat) (x : Int) : SixAdicIsoAt k x x := by
  refine ⟨0, ?_⟩
  simp [SixAdicIsoAt]

theorem six_iso_symm {k : Nat} {x y : Int}
    (h : SixAdicIsoAt k x y) : SixAdicIsoAt k y x := by
  rcases h with ⟨q, hq⟩
  refine ⟨-q, ?_⟩
  calc
    y - x = -(x - y) := by ring
    _ = -((6 : Int) ^ k * q) := by rw [hq]
    _ = (6 : Int) ^ k * (-q) := by ring

theorem six_iso_trans {k : Nat} {x y z : Int}
    (hxy : SixAdicIsoAt k x y) (hyz : SixAdicIsoAt k y z) :
    SixAdicIsoAt k x z := by
  rcases hxy with ⟨q, hq⟩
  rcases hyz with ⟨r, hr⟩
  refine ⟨q + r, ?_⟩
  calc
    x - z = (x - y) + (y - z) := by ring
    _ = (6 : Int) ^ k * q + (6 : Int) ^ k * r := by rw [hq, hr]
    _ = (6 : Int) ^ k * (q + r) := by ring

/-- Threshold form of the strong triangle law: if `x` and `y`, and `y` and
    `z`, are indistinguishable at resolution `k`, then so are `x` and `z`. -/
theorem six_iso_nonarchimedean {k : Nat} {x y z : Int}
    (hxy : SixAdicIsoAt k x y) (hyz : SixAdicIsoAt k y z) :
    SixAdicIsoAt k x z :=
  six_iso_trans hxy hyz

theorem six_iso_translate (k : Nat) (a x y : Int)
    (h : SixAdicIsoAt k x y) :
    SixAdicIsoAt k (a + x) (a + y) := by
  rcases h with ⟨q, hq⟩
  refine ⟨q, ?_⟩
  calc
    (a + x) - (a + y) = x - y := by ring
    _ = (6 : Int) ^ k * q := hq

theorem six_iso_neg (k : Nat) (x y : Int)
    (h : SixAdicIsoAt k x y) :
    SixAdicIsoAt k (-x) (-y) := by
  rcases h with ⟨q, hq⟩
  refine ⟨-q, ?_⟩
  calc
    (-x) - (-y) = -(x - y) := by ring
    _ = -((6 : Int) ^ k * q) := by rw [hq]
    _ = (6 : Int) ^ k * (-q) := by ring

theorem six_iso_mul (k : Nat) (a x y : Int)
    (h : SixAdicIsoAt k x y) :
    SixAdicIsoAt k (a * x) (a * y) := by
  rcases h with ⟨q, hq⟩
  refine ⟨a * q, ?_⟩
  calc
    a * x - a * y = a * (x - y) := by ring
    _ = a * ((6 : Int) ^ k * q) := by rw [hq]
    _ = (6 : Int) ^ k * (a * q) := by ring

/-- Multiplication by six raises the guaranteed resolution by one level. -/
theorem six_iso_scale_six {k : Nat} {x y : Int}
    (h : SixAdicIsoAt k x y) :
    SixAdicIsoAt (k + 1) (6 * x) (6 * y) := by
  rcases h with ⟨q, hq⟩
  refine ⟨q, ?_⟩
  calc
    6 * x - 6 * y = 6 * (x - y) := by ring
    _ = 6 * ((6 : Int) ^ k * q) := by rw [hq]
    _ = (6 : Int) ^ (k + 1) * q := by rw [pow_succ]; ring

/-- Finer six-adic indistinguishability implies every immediately coarser
    level. -/
theorem six_iso_weaken {k : Nat} {x y : Int}
    (h : SixAdicIsoAt (k + 1) x y) : SixAdicIsoAt k x y := by
  rcases h with ⟨q, hq⟩
  refine ⟨6 * q, ?_⟩
  calc
    x - y = (6 : Int) ^ (k + 1) * q := hq
    _ = (6 : Int) ^ k * (6 * q) := by rw [pow_succ]; ring

/-! ## Dyadic and triadic shadows -/

theorem six_iso_to_dyadic {k : Nat} {x y : Int}
    (h : SixAdicIsoAt k x y) : DyadicShadowAt k x y := by
  rcases h with ⟨q, hq⟩
  refine ⟨(3 : Int) ^ k * q, ?_⟩
  calc
    x - y = (6 : Int) ^ k * q := hq
    _ = ((2 : Int) * 3) ^ k * q := by norm_num
    _ = (2 : Int) ^ k * ((3 : Int) ^ k * q) := by
      rw [mul_pow]
      ring

theorem six_iso_to_triadic {k : Nat} {x y : Int}
    (h : SixAdicIsoAt k x y) : TriadicShadowAt k x y := by
  rcases h with ⟨q, hq⟩
  refine ⟨(2 : Int) ^ k * q, ?_⟩
  calc
    x - y = (6 : Int) ^ k * q := hq
    _ = ((2 : Int) * 3) ^ k * q := by norm_num
    _ = (3 : Int) ^ k * ((2 : Int) ^ k * q) := by
      rw [mul_pow]
      ring

/-! ## Non-Euclidean ball laws -/

theorem six_ball_center (k : Nat) (c : Int) : c ∈ SixAdicBall k c := by
  exact six_iso_refl k c

theorem six_ball_recenter {k : Nat} {c x : Int}
    (hxc : x ∈ SixAdicBall k c) :
    SixAdicBall k x = SixAdicBall k c := by
  apply Set.ext
  intro y
  change SixAdicIsoAt k y x ↔ SixAdicIsoAt k y c
  change SixAdicIsoAt k x c at hxc
  constructor
  · intro hyx
    exact six_iso_trans hyx hxc
  · intro hyc
    exact six_iso_trans hyc (six_iso_symm hxc)

/-- Equal-radius six-adic balls are either disjoint or identical. -/
theorem intersecting_equal_radius_balls_eq {k : Nat} {c d : Int}
    (h : (SixAdicBall k c ∩ SixAdicBall k d).Nonempty) :
    SixAdicBall k c = SixAdicBall k d := by
  rcases h with ⟨x, hxc, hxd⟩
  have hcx : SixAdicBall k c = SixAdicBall k x := by
    exact (six_ball_recenter hxc).symm
  have hdx : SixAdicBall k d = SixAdicBall k x := by
    exact (six_ball_recenter hxd).symm
  exact hcx.trans hdx.symm

/-- Every ball at level `k+1` is contained in its level-`k` ball. -/
theorem six_ball_nested (k : Nat) (c : Int) :
    SixAdicBall (k + 1) c ⊆ SixAdicBall k c := by
  intro x hx
  exact six_iso_weaken hx

/-! ## Six-way rooted refinement -/

theorem six_child_center_in_parent (k : Nat) (c : Int) (j : Fin 6) :
    sixChildCenter k c j ∈ SixAdicBall k c := by
  change SixAdicIsoAt k (sixChildCenter k c j) c
  refine ⟨(j.val : Int), ?_⟩
  simp [sixChildCenter]
  ring

/-- The six canonical child centers at each node are genuinely distinct. -/
theorem six_child_centers_injective (k : Nat) (c : Int) :
    Function.Injective (sixChildCenter k c) := by
  intro i j hij
  have hp : 0 < (6 : Int) ^ k := by positivity
  have hv : (i.val : Int) = (j.val : Int) := by
    dsimp [sixChildCenter] at hij
    nlinarith
  apply Fin.ext
  exact_mod_cast hv

/-! ## GST Graph V2 compatibility -/

theorem graph_iso_refl (k : Nat) (G : GSTGraphV2NonEuclidean.Graph) :
    GraphIsoAt k G G := by
  exact six_iso_refl k (G.energy : Int)

theorem graph_iso_symm {k : Nat} {G H : GSTGraphV2NonEuclidean.Graph}
    (h : GraphIsoAt k G H) : GraphIsoAt k H G := by
  exact six_iso_symm h

theorem graph_iso_trans {k : Nat} {G H J : GSTGraphV2NonEuclidean.Graph}
    (hGH : GraphIsoAt k G H) (hHJ : GraphIsoAt k H J) :
    GraphIsoAt k G J := by
  exact six_iso_trans hGH hHJ

/-- Every physical x4 phase chart is six-adically non-expansive: multiplication
    by `4^t` preserves every six-adic congruence already present. -/
theorem x4_chart_preserves_six_iso
    (k t E F : Nat)
    (h : SixAdicIsoAt k (E : Int) (F : Int)) :
    SixAdicIsoAt k ((4 : Int) ^ t * (E : Int))
      ((4 : Int) ^ t * (F : Int)) := by
  exact six_iso_mul k ((4 : Int) ^ t) (E : Int) (F : Int) h

/-- Exact reduction of physical-projection isometry to the underlying x4
    energy charts. -/
theorem physical_projection_iso_exact
    (k E F N M t s p q : Nat) :
    PhysicalProjectionIsoAt k
        (GSTGraphV2NonEuclidean.projectPhysicalCell E N t p)
        (GSTGraphV2NonEuclidean.projectPhysicalCell F M s q) ↔
      SixAdicIsoAt k
        ((4 : Int) ^ t * (E : Int))
        ((4 : Int) ^ s * (F : Int)) := by
  rfl

/-- Six-adic resolution is ontological metadata only: it leaves every one of
    the seven primitive GST axes of a resolved vertex exactly untouched. -/
theorem resolved_vertex_axes_exact (G : ResolvedGraph) (p : Nat) :
    (resolvedVertex G p).axes =
      GSTGraphV2NonEuclidean.axes G.ambient.energy G.ambient.horizon p := by
  rfl

/-- The resolution overlay also leaves the full underlying GST vertex exact. -/
theorem resolved_vertex_exact (G : ResolvedGraph) (p : Nat) :
    resolvedVertex G p = GSTGraphV2NonEuclidean.vertex G.ambient p := by
  rfl

end GSTGraphV2SixAdicOntologicalGeometryLaws
