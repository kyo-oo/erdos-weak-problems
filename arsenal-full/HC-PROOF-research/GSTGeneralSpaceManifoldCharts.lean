import GSTGeneralSpaceManifold
import GSTGeneralSpacePartialCharts
import Mathlib.Geometry.Manifold.ChartedSpace

/-!
# GENERAL SPACE THEORY — NATIVE MANIFOLD CHART OBSERVATIONS

A manifold chart is now literally a GST partial observation.  The manifold is
not identified with its model space; each `chartAt` only observes the genuine
source region on which that coordinate system is valid.
-/

universe u h

namespace GSTGeneralSpace

open scoped Manifold

/-- The native Mathlib chart at x, viewed as a partial General-Space chart. -/
def manifoldPartialChart
    (H : Type h) [TopologicalSpace H]
    (M : Type u) [TopologicalSpace M] [ChartedSpace H M]
    (x : M) : PartialChart (manifoldGeneralSpace M) where
  Coord := H
  domain := (chartAt H x).source
  observe := fun y => chartAt H x y.1

/-- Every point lies in the domain of its own canonical manifold chart. -/
theorem self_mem_manifoldPartialChart
    (H : Type h) [TopologicalSpace H]
    (M : Type u) [TopologicalSpace M] [ChartedSpace H M]
    (x : M) :
    x ∈ (manifoldPartialChart H M x).domain := by
  exact mem_chart_source H x

/-- On its domain the GST observation is definitionally the native manifold
chart map. -/
@[simp]
theorem manifoldPartialChart_observe
    (H : Type h) [TopologicalSpace H]
    (M : Type u) [TopologicalSpace M] [ChartedSpace H M]
    (x y : M)
    (hy : y ∈ (chartAt H x).source) :
    (manifoldPartialChart H M x).observeAt y hy = chartAt H x y := rfl

/-- Every charted space has a complete point-indexed family of genuine local
GST observations. -/
def manifoldChartAtlas
    (H : Type h) [TopologicalSpace H]
    (M : Type u) [TopologicalSpace M] [ChartedSpace H M] :
    M → PartialChart (manifoldGeneralSpace M) :=
  manifoldPartialChart H M

#check manifoldPartialChart
#check self_mem_manifoldPartialChart
#check manifoldPartialChart_observe
#check manifoldChartAtlas

end GSTGeneralSpace
