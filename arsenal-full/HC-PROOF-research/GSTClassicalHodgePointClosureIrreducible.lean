import GSTClassicalHodgePointClosurePrincipalCut
import Mathlib.Topology.Irreducible

/-!
# GST CLASSICAL HODGE — IRREDUCIBILITY OF GENERIC-POINT CLOSURE SCHEMES

The reduced subscheme built from `closure {x}` must retain the defining
irreducibility of a generic-point closure.  Mathlib's ideal-sheaf API identifies
the range of the subscheme inclusion with the ideal-sheaf support, while the
vanishing ideal has support exactly the closed set from which it was built.
Hence the point-closure subscheme is homeomorphic to `closure {x}`.

Since the closure of a singleton is irreducible, every point-closure scheme is
an irreducible Noetherian carrier.  This supplies the recursive domain on which
the proper-principal-cut codimension-one theorem can be reapplied at every
stage.
-/

set_option maxHeartbeats 30000000
set_option maxRecDepth 1000000

noncomputable section

open TopologicalSpace
open AlgebraicGeometry
open GSTProjectiveOverC
open GSTClassicalHodgePointClosurePrincipalCut

namespace GSTClassicalHodgePointClosureIrreducible

/-- The vanishing ideal defining the point closure has exactly the expected
support. -/
@[simp]
theorem pointClosureIdeal_support
    (V : SmoothProjectiveComplexScheme) (x : V.X) :
    (pointClosureIdeal V x).support = pointClosureClosed V x := by
  rfl

/-- The range of the point-closure inclusion is literally `closure {x}`. -/
theorem range_pointClosureι
    (V : SmoothProjectiveComplexScheme) (x : V.X) :
    Set.range (pointClosureι V x) = closure ({x} : Set V.X) := by
  have h1 : Set.range (pointClosureι V x)
      = (pointClosureIdeal V x).support :=
    Scheme.IdealSheafData.range_subschemeι (pointClosureIdeal V x)
  rw [h1, pointClosureIdeal_support]
  rfl

/-- Homeomorphism from the reduced point-closure scheme to the topological
closure of its generic point. -/
noncomputable def pointClosureHomeomorph
    (V : SmoothProjectiveComplexScheme) (x : V.X) :
    pointClosureScheme V x ≃ₜ closure ({x} : Set V.X) := by
  let e := (pointClosureι V x).isEmbedding.toHomeomorph
  let erange : Set.range (pointClosureι V x) ≃ₜ closure ({x} : Set V.X) :=
    Homeomorph.setCongr (range_pointClosureι V x)
  exact e.trans erange

/-- A singleton closure is irreducible. -/
theorem closure_singleton_irreducible
    (V : SmoothProjectiveComplexScheme) (x : V.X) :
    IsIrreducible (closure ({x} : Set V.X)) := by
  exact isIrreducible_singleton.closure

/-- The subtype of the singleton closure is an irreducible space. -/
noncomputable def closureSingletonIrreducibleSpace
    (V : SmoothProjectiveComplexScheme) (x : V.X) :
    IrreducibleSpace (closure ({x} : Set V.X)) :=
  Subtype.irreducibleSpace (closure_singleton_irreducible V x)

/-- **GENERIC-CLOSURE IRREDUCIBILITY.**  The actual reduced closure subscheme
of every point is irreducible. -/
noncomputable def pointClosureIrreducibleSpace
    (V : SmoothProjectiveComplexScheme) (x : V.X) :
    IrreducibleSpace (pointClosureScheme V x) := by
  letI : IrreducibleSpace (closure ({x} : Set V.X)) :=
    closureSingletonIrreducibleSpace V x
  exact (pointClosureHomeomorph V x).irreducibleSpace_iff.mpr inferInstance

/-- Canonical point of the closure scheme mapping to the original generic
point. -/
noncomputable def closureGenericPoint
    (V : SmoothProjectiveComplexScheme) (x : V.X) :
    pointClosureScheme V x :=
  (pointClosureHomeomorph V x).symm
    ⟨x, subset_closure (Set.mem_singleton x)⟩

@[simp]
theorem closureGenericPoint_maps_to_source
    (V : SmoothProjectiveComplexScheme) (x : V.X) :
    pointClosureι V x (closureGenericPoint V x) = x := by
  change ((pointClosureHomeomorph V x) (closureGenericPoint V x)).1 = x
  simp [closureGenericPoint, pointClosureHomeomorph]

/-- Irreducible/Noetherian closure crown. -/
theorem point_closure_irreducible_noetherian_crown
    (V : SmoothProjectiveComplexScheme) (x : V.X) :
    Nonempty (pointClosureScheme V x) := by
  exact ⟨closureGenericPoint V x⟩

#check pointClosureIdeal_support
#check range_pointClosureι
#check pointClosureHomeomorph
#check pointClosureIrreducibleSpace
#check closureGenericPoint
#check closureGenericPoint_maps_to_source

#print axioms range_pointClosureι
#print axioms pointClosureHomeomorph
#print axioms pointClosureIrreducibleSpace
#print axioms closureGenericPoint_maps_to_source

end GSTClassicalHodgePointClosureIrreducible
