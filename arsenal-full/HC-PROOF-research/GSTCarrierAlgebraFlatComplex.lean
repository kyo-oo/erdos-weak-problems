import Mathlib
import GSTInfiniteTowerCurvatureCascade

/-!
# GST Round 58 — the carrier algebra and the flat complex

Round 57 (`GSTInfiniteTowerCurvatureCascade`) made the ε-family an
operator (the infinite tower differential `D`), squared it with no
bound (the unbounded curvature ladder), and built the curvature
cascade: the carrier tower `K(T)` whose differential is `D²`, the
self-convolution `K ⊛ K` as its carriers, and the law
`D^(2^m) = D_{carrierTower^m(T)}`. This round gives that machinery its
two algebraic closures:

* **THE CARRIER ALGEBRA.** The convolution `⊛` of carrier families is
  an ASSOCIATIVE product: `(K ⊛ L) ⊛ M = K ⊛ (L ⊛ M)` — the curvature
  algebra of the ε-family, associative by the SAME triangle
  reindexing law that cancels the tower square's cross tails (the
  combinatorial heart, now a standalone algebra law: the two
  triangular indexings of the strict lower triangle compute the same
  triple sum). The zero laws: `0 ⊛ K = K ⊛ 0 = 0`. The cascade's
  carriers ARE the iterated self-convolutions
  (`(carrierTower^m(T)).curv` chains by `⊛`).

* **THE FLAT COMPLEX.** On a flat tower the infinite differential
  squares to zero AS AN OPERATOR (`D² = 0`), so the jet space becomes
  a differential module: the BOUNDARIES (`range D`) lie inside the
  CYCLES (`ker D`) — the complex condition, with the cycles and
  boundaries as new submodule-valued fields (`cycles`, `boundaries`)
  and the cycles' pointwise characterization (a jet is D-closed iff
  its differential vanishes at every level). THE ORIGIN COMPLEX: the
  origin tower's differential is the base differential applied
  levelwise. THE CASCADE ANNIHILATION: every square-power iterate
  `D^(2^(m+1))` vanishes on a flat tower — the whole cascade
  collapses.

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

/-! ## Face 1 — the carrier algebra -/

/-- **The left zero law.** The zero carrier family annihilates the
convolution on the left: `0 ⊛ K = 0`. -/
theorem carrierConvolution_zero_left (K : ℕ → (V →ₗ[ℚ] V)) (k : ℕ) :
    carrierConvolution 0 K k = 0 := by
  ext x
  simp [carrierConvolution, LinearMap.comp_apply, LinearMap.sum_apply,
    LinearMap.zero_apply, map_zero, Finset.sum_const_zero, Pi.zero_apply]

/-- **The right zero law.** The zero carrier family annihilates the
convolution on the right: `K ⊛ 0 = 0`. -/
theorem carrierConvolution_zero_right (K : ℕ → (V →ₗ[ℚ] V)) (k : ℕ) :
    carrierConvolution K 0 k = 0 := by
  ext x
  simp [carrierConvolution, LinearMap.comp_apply, LinearMap.sum_apply,
    LinearMap.zero_apply, map_zero, Finset.sum_const_zero, Pi.zero_apply]

/-- **THE ASSOCIATIVITY OF THE CARRIER CONVOLUTION.**
`(K ⊛ L) ⊛ M = K ⊛ (L ⊛ M)` at every index — the curvature algebra
of the ε-family is an associative (non-unital, generally
non-commutative) graded product. The proof is the triangle
reindexing law AGAIN: the two triangular indexings of the strict
lower triangle — by the middle coordinate and by the first — compute
the same triple sum, exactly as they cancelled the tower square's
cross tails in Rounds 56 and 57. The associativity is what makes the
cascade's square-tree convolutions honest iterated products. -/
theorem carrierConvolution_assoc (K L M : ℕ → (V →ₗ[ℚ] V)) (k : ℕ) (x : V) :
    carrierConvolution (carrierConvolution K L) M k x
      = carrierConvolution K (carrierConvolution L M) k x := by
  have hL : carrierConvolution (carrierConvolution K L) M k x
      = ∑ j ∈ Finset.range k, ∑ i ∈ Finset.range j,
          K i (L (j - 1 - i) (M (k - 1 - j) x)) := by
    simp [carrierConvolution, LinearMap.sum_apply, LinearMap.comp_apply]
  have hR : carrierConvolution K (carrierConvolution L M) k x
      = ∑ i ∈ Finset.range k, ∑ r ∈ Finset.range (k - 1 - i),
          K i (L r (M (k - 1 - i - 1 - r) x)) := by
    simp [carrierConvolution, LinearMap.sum_apply, LinearMap.comp_apply]
  rw [hL, hR]
  have htri := sum_triangle_succ
    (fun r i => K r (L (i - 1 - r) (M (k - 1 - i) x))) k
  rw [htri]
  refine Finset.sum_congr rfl fun p _ => Finset.sum_congr rfl fun q _ => ?_
  rw [show p + q + 1 - 1 - p = q from by omega,
    show k - 1 - (p + q + 1) = k - 1 - p - 1 - q from by omega]

/-- **The cascade's carriers are the iterated self-convolutions.**
The `m+1`-fold carrier tower's carrier family is the
self-convolution of the `m`-fold's: the cascade iterates the
convolution product, and the associativity makes every grouping of
the iterates agree. -/
theorem carrierPower_curv_succ (T : JetTowerInf V) (m : ℕ) :
    (carrierPower T (m + 1)).curv
      = carrierConvolution (carrierPower T m).curv (carrierPower T m).curv := rfl

/-! ## Face 2 — the flat complex -/

/-- **THE OPERATOR FLAT SQUARE.** On a flat tower the infinite
differential squares to zero as an operator: `D ∘ D = 0` — the
jet space becomes a differential module. -/
theorem flat_square_operator (T : JetTowerInf V) (hflat : T.IsFlat) :
    T.jetInfDifferential.comp T.jetInfDifferential = 0 := by
  ext u j
  exact flat_inf_tower_square T hflat u j

/-- **The complex condition, kernel-level.** On a flat tower the
boundaries lie inside the cycles: every exact jet is closed. -/
theorem flat_range_le_ker (T : JetTowerInf V) (hflat : T.IsFlat) :
    LinearMap.range T.jetInfDifferential ≤ LinearMap.ker T.jetInfDifferential := by
  intro x hx
  obtain ⟨u, rfl⟩ := LinearMap.mem_range.mp hx
  rw [LinearMap.mem_ker]
  funext j
  exact flat_inf_tower_square T hflat u j

/-- **THE TOWER CYCLES.** The D-closed jets: the kernel of the
infinite tower differential — a submodule of the jet space. -/
def cycles (T : JetTowerInf V) : Submodule ℚ (ℕ → V) :=
  LinearMap.ker T.jetInfDifferential

/-- **THE TOWER BOUNDARIES.** The D-exact jets: the image of the
infinite tower differential — a submodule of the jet space. -/
def boundaries (T : JetTowerInf V) : Submodule ℚ (ℕ → V) :=
  LinearMap.range T.jetInfDifferential

/-- **THE FLAT COMPLEX.** On a flat tower the boundaries lie inside
the cycles: every exact jet is closed — the complex condition,
stated on the cycle and boundary fields. -/
theorem boundaries_le_cycles (T : JetTowerInf V) (hflat : T.IsFlat) :
    boundaries T ≤ cycles T :=
  flat_range_le_ker T hflat

/-- **The cycles' pointwise characterization.** A jet is D-closed if
and only if its differential vanishes at every level. -/
theorem mem_cycles (T : JetTowerInf V) (u : ℕ → V) :
    u ∈ cycles T ↔ ∀ j, T.jetInfDifferential u j = 0 := by
  constructor
  · intro h j
    have hj := congrFun (LinearMap.mem_ker.mp h) j
    simpa [Pi.zero_apply] using hj
  · intro h
    show u ∈ LinearMap.ker T.jetInfDifferential
    rw [LinearMap.mem_ker]
    funext j
    simpa [Pi.zero_apply] using h j

/-- **THE ORIGIN COMPLEX, LEVELWISE.** The origin tower's differential
is the base differential applied levelwise: the origin's jet-space
complex is the levelwise complex of the flat base. -/
theorem originTower_jetInfDifferential (d : V →ₗ[ℚ] V) (hd : d.comp d = 0)
    (u : ℕ → V) (j : ℕ) :
    (originTower d hd).jetInfDifferential u j = d (u j) := by
  show d (u j) + ∑ i ∈ Finset.range j, (0 : V →ₗ[ℚ] V) (u (j - 1 - i)) = d (u j)
  simp [LinearMap.zero_apply, Finset.sum_const_zero]

/-- **THE CASCADE ANNIHILATION.** On a flat tower every square-power
iterate from the first on vanishes: `D^(2^(m+1)) = 0` for every `m`
— the whole curvature cascade collapses, order by order, because
the flat square is zero. -/
theorem flat_squarePower (T : JetTowerInf V) (hflat : T.IsFlat) (m : ℕ) :
    squarePower T.jetInfDifferential (m + 1) = 0 := by
  induction m with
  | zero =>
    show T.jetInfDifferential.comp T.jetInfDifferential = 0
    exact flat_square_operator T hflat
  | succ m ih =>
    show (squarePower T.jetInfDifferential (m + 1)).comp
      (squarePower T.jetInfDifferential (m + 1)) = 0
    rw [ih]
    ext x
    simp [LinearMap.comp_apply, LinearMap.zero_apply]

end GSTFoldTowerSquare.JetTowerInf

#print axioms GSTFoldTowerSquare.JetTowerInf.carrierConvolution_zero_left
#print axioms GSTFoldTowerSquare.JetTowerInf.carrierConvolution_zero_right
#print axioms GSTFoldTowerSquare.JetTowerInf.carrierConvolution_assoc
#print axioms GSTFoldTowerSquare.JetTowerInf.carrierPower_curv_succ
#print axioms GSTFoldTowerSquare.JetTowerInf.flat_square_operator
#print axioms GSTFoldTowerSquare.JetTowerInf.flat_range_le_ker
#print axioms GSTFoldTowerSquare.JetTowerInf.boundaries_le_cycles
#print axioms GSTFoldTowerSquare.JetTowerInf.mem_cycles
#print axioms GSTFoldTowerSquare.JetTowerInf.originTower_jetInfDifferential
#print axioms GSTFoldTowerSquare.JetTowerInf.flat_squarePower
