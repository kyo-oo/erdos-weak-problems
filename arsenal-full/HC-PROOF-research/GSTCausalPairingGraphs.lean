import GSTFoldPeriodDescent

/-!
# GST causal pairing graphs: determinant amplitudes and exact source return

This is the commutative tensor-coordinate algebra of pairing graphs.
Actual exterior cup products require the Koszul sign dictionary in the
companion derivation. A bracket identity is not asserted as an unsigned
Chow identity. The all-arity invariant-theory/basis theorem is hand-level.
-/

namespace GSTCausalPairingGraphs
variable {R : Type*} [CommRing R]

def bracket (v w : R × R) : R := v.1*w.2-v.2*w.1
def transform (a b c d : R) (v : R × R) : R × R :=
  (a*v.1+b*v.2,c*v.1+d*v.2)

theorem bracket_skew (v w : R × R) : bracket v w= -bracket w v := by
  simp [bracket]
  ring

theorem bracket_self (v : R × R) : bracket v v=0 := by
  simp only [bracket]
  ring

theorem bracket_transform (a b c d : R) (v w : R × R) :
    bracket (transform a b c d v) (transform a b c d w)=
      (a*d-b*c)*bracket v w := by
  simp [bracket,transform]
  ring

theorem bracket_shear (t : R) (v w : R × R) :
    bracket (transform 1 t 0 1 v) (transform 1 t 0 1 w)=bracket v w := by
  rw [bracket_transform]
  ring

theorem plucker_four (u v w x : R × R) :
    bracket u v*bracket w x-bracket u w*bracket v x+
      bracket u x*bracket v w=0 := by
  simp [bracket]
  ring

/-- An ordered edge list. For the geometric multilinear sector it is a
perfect matching; this amplitude is also meaningful for general graphs. -/
def graphAmplitude {I : Type*} (state : I → R × R) : List (I × I) → R
  | [] => 1
  | (i,j) :: es => bracket (state i) (state j)*graphAmplitude state es

theorem graph_transform {I : Type*} (state : I → R × R)
    (edges : List (I × I)) (a b c d : R) :
    graphAmplitude (fun i => transform a b c d (state i)) edges=
      (a*d-b*c)^edges.length*graphAmplitude state edges := by
  induction edges with
  | nil => simp [graphAmplitude]
  | cons e es ih =>
      rcases e with ⟨i,j⟩
      simp only [graphAmplitude,bracket_transform,ih,List.length_cons,pow_succ]
      ring

theorem graph_special_linear_invariant {I : Type*} (state : I → R × R)
    (edges : List (I × I)) (a b c d : R) (h : a*d-b*c=1) :
    graphAmplitude (fun i => transform a b c d (state i)) edges=
      graphAmplitude state edges := by
  rw [graph_transform,h]
  simp

theorem graph_append {I : Type*} (state : I → R × R)
    (es fs : List (I × I)) :
    graphAmplitude state (es++fs)=graphAmplitude state es*graphAmplitude state fs := by
  induction es with
  | nil => simp [graphAmplitude]
  | cons e es ih =>
      rcases e with ⟨i,j⟩
      simp [graphAmplitude,ih,mul_assoc]

theorem vacuum_graph {I : Type*} (state : I → R × R) :
    graphAmplitude state []=1 := rfl

/-! For an actual pair divisor the return scalar is its intersection -2nm.
These normalization equations do not assert that a Betti external product
already has an algebraic representative. -/
section Return
variable {V : Type*} [AddCommGroup V] [Module ℚ V]

theorem normalize_handle_return (alpha : V) (n m : ℚ)
    (hn : n ≠ 0) (hm : m ≠ 0) :
    (-2*n*m)⁻¹ • ((-2*n*m) • alpha)=alpha := by
  rw [smul_smul,inv_mul_cancel₀ (by exact mul_ne_zero (mul_ne_zero (by norm_num) hn) hm),one_smul]

theorem paired_return_product_nonzero (terms : List ℚ)
    (h : ∀ x ∈ terms,x ≠ 0) : terms.prod ≠ 0 := by
  induction terms with
  | nil => simp
  | cons x xs ih =>
      simp only [List.prod_cons]
      exact mul_ne_zero (h x List.mem_cons_self)
        (ih (by intro y hy; exact h y (List.mem_cons_of_mem x hy)))

end Return

#print axioms bracket_transform
#print axioms plucker_four
#print axioms graph_special_linear_invariant
#print axioms normalize_handle_return
end GSTCausalPairingGraphs
