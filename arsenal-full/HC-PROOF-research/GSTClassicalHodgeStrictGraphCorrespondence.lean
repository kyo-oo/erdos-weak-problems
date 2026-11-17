import GSTClassicalHodgeSchemeFiniteCorrespondenceFirewall

/-!
# GST CLASSICAL HODGE — STRICT PROJECTIVE GRAPH CORRESPONDENCES

A finite algebraic self-map of the smooth projective carrier already gives a
genuine strict bi-finite correspondence: its graph has identity left
projection and the supplied finite map as right projection.  Transposing this
graph therefore produces a strict correspondence whose right projection is
literally the identity.

This file removes the first supplied geometric object from the strict-Betti
ray route.  No Hodge class, cycle-class surjectivity, transfer, or desired
cohomological action is assumed.
-/

set_option maxHeartbeats 100000000
set_option maxRecDepth 1000000

noncomputable section

open CategoryTheory
open AlgebraicGeometry

namespace GSTClassicalHodgeStrictGraphCorrespondence

open GSTProjectiveOverC
open GSTClassicalHodgeAnalytificationFunctoriality
open GSTClassicalHodgeProjectiveSelfCorrespondences
open GSTClassicalHodgeSchemeFiniteCorrespondenceFirewall

variable {V : SmoothProjectiveComplexScheme}

/-- The graph of a finite C-scheme endomorphism, promoted to the strict
scheme-bi-finite correspondence API. -/
noncomputable def strictGraph
    (f : ComplexSchemeEndomorphism V)
    (hf : IsFinite f.hom) :
    SchemeBiFiniteClosedCorrespondence V where
  carrier := V.X
  intoProduct := graph V f
  closedImmersion := inferInstance
  left_isFinite := by
    rw [graph_fst]
    infer_instance
  right_isFinite := by
    rw [graph_snd]
    exact hf

@[simp]
theorem strictGraph_left
    (f : ComplexSchemeEndomorphism V)
    (hf : IsFinite f.hom) :
    (strictGraph f hf).toSchemeFiniteClosedCorrespondence.left = 𝟙 V.X := by
  exact graph_fst V f

@[simp]
theorem strictGraph_right
    (f : ComplexSchemeEndomorphism V)
    (hf : IsFinite f.hom) :
    (strictGraph f hf).right = f.hom := by
  exact graph_snd V f

/-- After genuine factor-swap transpose, the finite map is the left leg. -/
@[simp]
theorem strictGraph_transpose_left
    (f : ComplexSchemeEndomorphism V)
    (hf : IsFinite f.hom) :
    (strictGraph f hf).transpose.toSchemeFiniteClosedCorrespondence.left =
      f.hom := by
  rw [SchemeBiFiniteClosedCorrespondence.transpose_left, strictGraph_right]

/-- After genuine factor-swap transpose, the right leg is literally identity.
This is the scheme-level source of the degree-one Betti trace constructed in
the next layer. -/
@[simp]
theorem strictGraph_transpose_right
    (f : ComplexSchemeEndomorphism V)
    (hf : IsFinite f.hom) :
    (strictGraph f hf).transpose.right = 𝟙 V.X := by
  rw [SchemeBiFiniteClosedCorrespondence.transpose_right, strictGraph_left]

#check strictGraph
#check strictGraph_left
#check strictGraph_right
#check strictGraph_transpose_left
#check strictGraph_transpose_right

#print axioms strictGraph_left
#print axioms strictGraph_right
#print axioms strictGraph_transpose_left
#print axioms strictGraph_transpose_right

end GSTClassicalHodgeStrictGraphCorrespondence
