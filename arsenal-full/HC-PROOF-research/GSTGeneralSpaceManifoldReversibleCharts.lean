import GSTGeneralSpaceManifoldCharts
import GSTGeneralSpaceReversiblePartialCharts
import Mathlib.Geometry.Manifold.ChartedSpace

/-!
# GENERAL SPACE THEORY — REVERSIBLE MANIFOLD CHARTS

Every native manifold chart is a genuine open partial homeomorphism.  Hence it
is not merely a local observation: on its source it is a reversible
coordinatization onto its target.  This file imports that exact local
reversibility into GST without making coordinates ontological.
-/

universe u h

namespace GSTGeneralSpace

open scoped Manifold

/-- The actual Mathlib chart at x as a reversible local GST coordinatization. -/
def manifoldReversibleChart
    (H : Type h) [TopologicalSpace H]
    (M : Type u) [TopologicalSpace M] [ChartedSpace H M]
    (x : M) : ReversiblePartialChart (manifoldGeneralSpace M) where
  Coord := H
  domain := (chartAt H x).source
  target := (chartAt H x).target
  coordEquiv := {
    toFun := fun y =>
      ⟨chartAt H x y.1, (chartAt H x).map_source y.2⟩
    invFun := fun z =>
      ⟨(chartAt H x).symm z.1, (chartAt H x).map_target z.2⟩
    left_inv := by
      intro y
      apply Subtype.ext
      exact (chartAt H x).left_inv y.2
    right_inv := by
      intro z
      apply Subtype.ext
      exact (chartAt H x).right_inv z.2
  }

/-- Forgetting reversibility recovers the previously defined local manifold
observation. -/
theorem manifoldReversibleChart_toPartialChart
    (H : Type h) [TopologicalSpace H]
    (M : Type u) [TopologicalSpace M] [ChartedSpace H M]
    (x : M) :
    (manifoldReversibleChart H M x).toPartialChart =
      manifoldPartialChart H M x := by
  rfl

/-- Native chart inversion is literally GST coordinate recovery. -/
theorem manifold_chart_recover
    (H : Type h) [TopologicalSpace H]
    (M : Type u) [TopologicalSpace M] [ChartedSpace H M]
    (x y : M)
    (hy : y ∈ (chartAt H x).source) :
    (manifoldReversibleChart H M x).recoverAt
      (chartAt H x y) ((chartAt H x).map_source hy) = y := by
  exact (chartAt H x).left_inv hy

/-- Every charted manifold therefore comes equipped with a point-indexed atlas
of reversible local GST coordinatizations. -/
def manifoldReversibleAtlas
    (H : Type h) [TopologicalSpace H]
    (M : Type u) [TopologicalSpace M] [ChartedSpace H M] :
    M → ReversiblePartialChart (manifoldGeneralSpace M) :=
  manifoldReversibleChart H M

#check manifoldReversibleChart
#check manifoldReversibleChart_toPartialChart
#check manifold_chart_recover
#check manifoldReversibleAtlas

end GSTGeneralSpace
