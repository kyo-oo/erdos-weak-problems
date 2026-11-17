import GSTGeneralSpaceCohomology

/-!
# GST causal word defect, with exact cancellation

The ring equations apply to actual operators after a realization is supplied.
In weight one use complex-structure operators. In higher degree use the full
Hodge-charge or filtration data, not a weight-one operator substituted for it.
No assertion of original-X algebraic source existence is an input or conclusion.
-/

namespace GSTCausalFoldDefect

variable {R : Type*} [Ring R]

def defect (J K T : R) : R := K*T-T*J

theorem defect_comp (J K L S T : R) :
    defect J L (S*T) = defect K L S*T + S*defect J K T := by
  simp only [defect]
  noncomm_ring

theorem defect_identity (J : R) : defect J J 1 = 0 := by simp [defect]

theorem safe_comp (J K L S T : R)
    (hS : defect K L S = 0) (hT : defect J K T = 0) :
    defect J L (S*T) = 0 := by rw [defect_comp, hS, hT]; simp

/-- Chronological list: the newest operator multiplies on the left. -/
def transportWord : List R → R
  | [] => 1
  | T :: ts => transportWord ts * T

/-- The exact sum of propagated edge defects, not merely a bound. -/
def accumulatedDefect (J : R) : List R → R
  | [] => 0
  | T :: ts => accumulatedDefect J ts * T + transportWord ts * defect J J T

theorem word_defect_exact (J : R) (ts : List R) :
    defect J J (transportWord ts) = accumulatedDefect J ts := by
  induction ts with
  | nil => simp [transportWord, accumulatedDefect, defect]
  | cons T ts ih =>
      show defect J J (transportWord ts * T) =
        accumulatedDefect J ts * T + transportWord ts * defect J J T
      rw [defect_comp J J J (transportWord ts) T, ih]

theorem every_edge_safe_word_safe (J : R) (ts : List R)
    (h : ∀ T ∈ ts, defect J J T = 0) :
    defect J J (transportWord ts) = 0 := by
  induction ts with
  | nil => exact defect_identity J
  | cons T ts ih =>
      apply safe_comp J J J (transportWord ts) T
      · exact ih (by intro U hU; exact h U (List.mem_cons_of_mem T hU))
      · exact h T (List.mem_cons_self)

/-- A nonzero endpoint defect certifies an offending causal edge. -/
theorem endpoint_break_has_bad_edge (J : R) (ts : List R)
    (h : defect J J (transportWord ts) ≠ 0) :
    ∃ T ∈ ts, defect J J T ≠ 0 := by
  classical
  by_contra hh
  apply h
  apply every_edge_safe_word_safe
  intro T hT
  by_contra hBad
  exact hh ⟨T,hT,hBad⟩

section GeneralSpace
open GSTGeneralSpace
variable {G : GeneralSpace}

/-- A genuinely realized causal operator functor. No Hodge-safety field is assumed. -/
structure OperatorRealization (G : GeneralSpace) (R : Type*) [Ring R] where
  operator : ∀ {x y : G.Point}, G.Path x y → R
  identity : ∀ x, operator (G.idPath x) = 1
  composition : ∀ {x y z} (a : G.Path x y) (b : G.Path y z),
    operator (G.compPath a b) = operator b * operator a

theorem causal_path_defect (P : OperatorRealization G R)
    {x y z : G.Point} (a : G.Path x y) (b : G.Path y z) (J K L : R) :
    defect J L (P.operator (G.compPath a b)) =
      defect K L (P.operator b) * P.operator a +
        P.operator b * defect J K (P.operator a) := by
  rw [P.composition, defect_comp]

end GeneralSpace

section NativeTower
open GSTGeneralSpace
open GSTGeneralSpace.NativeCycleRecoordination
variable {G : GeneralSpace} {N H : Type*}
  [AddCommGroup N] [Module ℚ N] [AddCommGroup H] [Module ℚ H]

/-- The cycle itself, recursively built from genuine native transports. -/
def nativeCycleTower (P : CyclePathRealization G N H)
    (world : ℕ → G.Point)
    (step : ∀ n, G.Path (world n) (world (n+1))) : ℕ → N → N
  | 0, seed => seed
  | n+1, seed => P.nativeTransport (step n) (nativeCycleTower P world step n seed)

/-- Compatibility at every finite depth is derived from naturality, rather
than supplied as an unrelated proposition-valued hypothesis. -/
theorem nativeCycleTower_class (P : CyclePathRealization G N H)
    (world : ℕ → G.Point) (step : ∀ n, G.Path (world n) (world (n+1)))
    (n : ℕ) (seed : N) :
    P.cycleClass (nativeCycleTower P world step n seed) =
      causalTowerHodgeState P world step n (P.cycleClass seed) := by
  induction n with
  | zero => rfl
  | succ n ih =>
      change P.cycleClass (P.nativeTransport (step n)
        (nativeCycleTower P world step n seed)) =
        P.hodgeTransport (step n) (causalTowerHodgeState P world step n (P.cycleClass seed))
      rw [P.naturality, ih]

end NativeTower

/-! ## Rational branching with the cycle itself retained

Terms may have different seeds and depths. They share the same realized
cycle carrier; a geometric instance must respect the intended grading and
world summands. A sum equality to alpha is checked data, never assumed from
the common causal address.
-/
section NativeBranching
open GSTGeneralSpace GSTGeneralSpace.NativeCycleRecoordination
variable {G : GeneralSpace} {N H : Type*}
  [AddCommGroup N] [Module ℚ N] [AddCommGroup H] [Module ℚ H]

def nativeCycleCombination (P : CyclePathRealization G N H)
    (world : ℕ → G.Point) (step : ∀ n, G.Path (world n) (world (n+1))) :
    List (ℚ × (ℕ × N)) → N
  | [] => 0
  | (a,n,z) :: ts => a • nativeCycleTower P world step n z +
      nativeCycleCombination P world step ts

def hodgeCombination (P : CyclePathRealization G N H)
    (world : ℕ → G.Point) (step : ∀ n, G.Path (world n) (world (n+1))) :
    List (ℚ × (ℕ × N)) → H
  | [] => 0
  | (a,n,z) :: ts => a • causalTowerHodgeState P world step n (P.cycleClass z) +
      hodgeCombination P world step ts

theorem nativeCycleCombination_class (P : CyclePathRealization G N H)
    (world : ℕ → G.Point) (step : ∀ n, G.Path (world n) (world (n+1)))
    (ts : List (ℚ × (ℕ × N))) :
    P.cycleClass (nativeCycleCombination P world step ts) =
      hodgeCombination P world step ts := by
  induction ts with
  | nil => simp [nativeCycleCombination, hodgeCombination]
  | cons t ts ih =>
      rcases t with ⟨a,n,z⟩
      simp only [nativeCycleCombination, hodgeCombination, map_add,
        map_smul, nativeCycleTower_class, ih]

theorem prescribed_class_from_branching (P : CyclePathRealization G N H)
    (world : ℕ → G.Point) (step : ∀ n, G.Path (world n) (world (n+1)))
    (ts : List (ℚ × (ℕ × N))) (alpha : H)
    (hexact : hodgeCombination P world step ts = alpha) :
    P.cycleClass (nativeCycleCombination P world step ts) = alpha :=
  (nativeCycleCombination_class P world step ts).trans hexact

/-- A nonzero scale is explicitly inverted in the native cycle carrier. -/
theorem normalized_cycle_class (cl : N →ₗ[ℚ] H)
    (z : N) (alpha : H) (m : ℚ) (hm : m ≠ 0)
    (hz : cl z=m • alpha) : cl (m⁻¹ • z)=alpha := by
  rw [map_smul, hz, smul_smul, inv_mul_cancel₀ hm, one_smul]

theorem rational_range_saturated (cl : N →ₗ[ℚ] H)
    (alpha : H) (m : ℚ) (hm : m ≠ 0) :
    m • alpha ∈ LinearMap.range cl ↔ alpha ∈ LinearMap.range cl := by
  constructor
  · rintro ⟨z,hz⟩
    exact ⟨m⁻¹ • z, normalized_cycle_class cl z alpha m hm hz⟩
  · rintro ⟨z,hz⟩
    exact ⟨m • z, by rw [map_smul, hz]⟩

#print axioms nativeCycleCombination_class
#print axioms prescribed_class_from_branching
#print axioms rational_range_saturated
end NativeBranching

#print axioms word_defect_exact
#print axioms endpoint_break_has_bad_edge
#print axioms causal_path_defect
#print axioms nativeCycleTower_class
/-! ## Whole-space opposedness: explicit missing-mode decomposition

L is instantiated by the actual curvature transpose, not a cycle-class map.
The manifold proof identifies ker L as the closed vertical holomorphic modes.
-/
section WholeSpaceOpposedness
variable {V W : Type*} [AddCommGroup V] [Module ℂ V]
  [AddCommGroup W] [Module ℂ W]

noncomputable def centralPlus (u v : V) : V := (1/2 : ℂ) • (u-Complex.I • v)
noncomputable def centralMinus (u v : V) : V := (1/2 : ℂ) • (u+Complex.I • v)

theorem central_parts_sum (u v : V) : centralPlus u v+centralMinus u v=u := by
  unfold centralPlus centralMinus
  module

theorem central_parts_difference (u v : V) :
    Complex.I • (centralPlus u v-centralMinus u v)=v := by
  calc
    Complex.I • (centralPlus u v-centralMinus u v)=
        (-Complex.I*Complex.I) • v := by
          unfold centralPlus centralMinus
          module
    _ = v := by simp [neg_mul,Complex.I_mul_I]

theorem closed_parts_of_zero_missing_mode (L : V →ₗ[ℂ] W) (u v : V)
    (hu : L u=0) (hv : L v=0) :
    L (centralPlus u v)=0 ∧ L (centralMinus u v)=0 := by
  simp [centralPlus,centralMinus,map_smul,map_sub,map_add,hu,hv]

theorem pure_split_iff_missing_mode_zero (L : V →ₗ[ℂ] W) (u v : V)
    (hu : L u=0) :
    (∃ a b : V,L a=0 ∧ L b=0 ∧ u=a+b ∧ v=Complex.I • (a-b)) ↔ L v=0 := by
  constructor
  · rintro ⟨a,b,ha,hb,_,rfl⟩
    simp [map_smul,map_sub,ha,hb]
  · intro hv
    have h := closed_parts_of_zero_missing_mode L u v hu hv
    exact ⟨centralPlus u v,centralMinus u v,h.1,h.2,
      (central_parts_sum u v).symm,(central_parts_difference u v).symm⟩

theorem nonzero_missing_mode_refuses_pure_split (L : V →ₗ[ℂ] W) (u v : V)
    (hu : L u=0) (hv : L v ≠ 0) :
    ¬ ∃ a b : V,L a=0 ∧ L b=0 ∧ u=a+b ∧ v=Complex.I • (a-b) := by
  rw [pure_split_iff_missing_mode_zero L u v hu]
  exact hv

#print axioms pure_split_iff_missing_mode_zero
end WholeSpaceOpposedness

/-! The full missing-mode short exact sequence. Its geometric identification
is in the central-fold hand proof; no original-X cycle source is asserted. -/
section MissingModeExactSequence
variable {V W : Type*} [AddCommGroup V] [Module ℂ V]
  [AddCommGroup W] [Module ℂ W]

def closedVerticalSpace (L : V →ₗ[ℂ] W) : Submodule ℂ (V × V) :=
  (L.comp (LinearMap.fst ℂ V V)).ker

def missingModeMap (L : V →ₗ[ℂ] W) :
    closedVerticalSpace L →ₗ[ℂ] LinearMap.range L where
  toFun z := ⟨L z.1.2, ⟨z.1.2, rfl⟩⟩
  map_add' z w := by apply Subtype.ext; exact L.map_add _ _
  map_smul' c z := by apply Subtype.ext; exact L.map_smul c _

theorem missingModeMap_surjective (L : V →ₗ[ℂ] W) :
    Function.Surjective (missingModeMap L) := by
  rintro ⟨w, v, rfl⟩
  refine ⟨⟨(0, v), ?_⟩, rfl⟩
  change L 0 = 0
  exact L.map_zero

theorem missingModeMap_zero_iff (L : V →ₗ[ℂ] W)
    (z : closedVerticalSpace L) : missingModeMap L z = 0 ↔ L z.1.2 = 0 := by
  constructor
  · intro h
    exact congrArg Subtype.val h
  · intro h
    apply Subtype.ext
    exact h

theorem closed_vertical_pure_iff_zero_missing (L : V →ₗ[ℂ] W)
    (z : closedVerticalSpace L) :
    (∃ a b : V, L a = 0 ∧ L b = 0 ∧
      z.1.1 = a+b ∧ z.1.2 = Complex.I • (a-b)) ↔ missingModeMap L z = 0 := by
  have hu : L z.1.1 = 0 := z.property
  rw [pure_split_iff_missing_mode_zero L z.1.1 z.1.2 hu,
    missingModeMap_zero_iff]

theorem missingMode_kernel_pure_split (L : V →ₗ[ℂ] W)
    (z : closedVerticalSpace L) :
    z ∈ (missingModeMap L).ker ↔
      ∃ a b : V, L a = 0 ∧ L b = 0 ∧
        z.1.1 = a+b ∧ z.1.2 = Complex.I • (a-b) := by
  exact (closed_vertical_pure_iff_zero_missing L z).symm

theorem missingMode_nonzero_witness (L : V →ₗ[ℂ] W)
    (w : LinearMap.range L) (hw : w ≠ 0) :
    ∃ z : closedVerticalSpace L, missingModeMap L z = w ∧
      ¬ ∃ a b : V, L a = 0 ∧ L b = 0 ∧
        z.1.1 = a+b ∧ z.1.2 = Complex.I • (a-b) := by
  obtain ⟨z, hz⟩ := missingModeMap_surjective L w
  refine ⟨z, hz, ?_⟩
  intro hpure
  apply hw
  rw [← hz]
  exact (closed_vertical_pure_iff_zero_missing L z).mp hpure

#print axioms missingModeMap_surjective
#print axioms missingMode_kernel_pure_split
end MissingModeExactSequence

/-! ## Universal relation factorization for base-coupled quotient folds

For geometry, C sends a vertical handle to its actual Chern class. A
quotient's pullback on vertical coefficients is I. Every restoring I has
one and only one factorization through ker C. No cycle selector is involved.
-/
section RestoringRelations
variable {𝕜 U V W : Type*} [Field 𝕜]
  [AddCommGroup U] [Module 𝕜 U] [AddCommGroup V] [Module 𝕜 V]
  [AddCommGroup W] [Module 𝕜 W]

def restoringLift (C : V →ₗ[𝕜] W) (I : U →ₗ[𝕜] V)
    (h : C.comp I=0) : U →ₗ[𝕜] C.ker where
  toFun u := ⟨I u, by
    have hu := congrArg (fun T : U →ₗ[𝕜] W => T u) h
    simpa using hu⟩
  map_add' u v := by apply Subtype.ext; exact I.map_add u v
  map_smul' a u := by apply Subtype.ext; exact I.map_smul a u

theorem restoringLift_underlying (C : V →ₗ[𝕜] W) (I : U →ₗ[𝕜] V)
    (h : C.comp I=0) : C.ker.subtype.comp (restoringLift C I h)=I := by
  ext u
  rfl

theorem restoring_iff_factors_through_relations
    (C : V →ₗ[𝕜] W) (I : U →ₗ[𝕜] V) :
    C.comp I=0 ↔ ∃ J : U →ₗ[𝕜] C.ker, C.ker.subtype.comp J=I := by
  constructor
  · intro h
    exact ⟨restoringLift C I h,restoringLift_underlying C I h⟩
  · rintro ⟨J,rfl⟩
    ext u
    exact (J u).property

theorem restoring_factorization_unique (C : V →ₗ[𝕜] W)
    (I : U →ₗ[𝕜] V) (h : C.comp I=0) :
    ∃! J : U →ₗ[𝕜] C.ker, C.ker.subtype.comp J=I := by
  refine ⟨restoringLift C I h,restoringLift_underlying C I h,?_⟩
  intro J hJ
  apply LinearMap.ext
  intro u
  apply Subtype.ext
  exact congrArg (fun T : U →ₗ[𝕜] V => T u) hJ

theorem restoringLift_injective (C : V →ₗ[𝕜] W)
    (I : U →ₗ[𝕜] V) (h : C.comp I=0) (hinj : Function.Injective I) :
    Function.Injective (restoringLift C I h) := by
  intro u v huv
  apply hinj
  exact congrArg Subtype.val huv

theorem relation_inclusion_restores (C : V →ₗ[𝕜] W) :
    C.comp C.ker.subtype=0 := by
  ext u
  exact u.property

#print axioms restoring_factorization_unique
end RestoringRelations

/-! ## Projective restoring relations

The hand theorem algebraizes a principal projective-torus torsor exactly when
its analytic gluing class is torsion. These are the supporting group/lattice
lemmas, not Lean instances of manifolds, Picard spaces or projective GAGA.
In particular curvature-zero and torsor-torsion are kept separate.
-/
section ProjectiveRestoringRelations
variable {Λ T W U : Type*} [AddCommGroup Λ] [AddCommGroup T]
  [AddCommGroup W] [AddCommGroup U]

/-- Saturated relations: a positive multiple of the actual gluing class vanishes. -/
def torsionRelation (theta : Λ →+ T) : AddSubgroup Λ where
  carrier := {m | ∃ n : ℕ, n ≠ 0 ∧ n • theta m = 0}
  zero_mem' := ⟨1, by decide, by simp⟩
  add_mem' := by
    rintro x y ⟨n, hn, hx⟩ ⟨m, hm, hy⟩
    refine ⟨n*m, Nat.mul_ne_zero hn hm, ?_⟩
    rw [map_add, nsmul_add]
    have hleft : (n*m) • theta x = 0 := by
      calc
        (n*m) • theta x = m • (n • theta x) := by
          rw [smul_smul, Nat.mul_comm]
        _ = 0 := by rw [hx, smul_zero]
    have hright : (n*m) • theta y = 0 := by
      rw [← smul_smul, hy, smul_zero]
    rw [hleft, hright, add_zero]
  neg_mem' := by
    rintro x ⟨n, hn, hx⟩
    exact ⟨n, hn, by simpa only [map_neg, smul_neg, hx, neg_zero]⟩

theorem mem_torsionRelation (theta : Λ →+ T) (x : Λ) :
    x ∈ torsionRelation theta ↔ ∃ n : ℕ, n ≠ 0 ∧ n • theta x = 0 := Iff.rfl

theorem kernel_le_torsionRelation (theta : Λ →+ T) :
    theta.ker ≤ torsionRelation theta := by
  intro x hx
  change theta x = 0 at hx
  exact ⟨1, by decide, by simpa using hx⟩

/-- The exact saturation equality, with a genuine finite annihilator witness. -/
theorem torsionRelation_eq_kernel_saturation (theta : Λ →+ T) (x : Λ) :
    x ∈ torsionRelation theta ↔
      ∃ n : ℕ, n ≠ 0 ∧ n • x ∈ theta.ker := by
  change (∃ n : ℕ, n ≠ 0 ∧ n • theta x = 0) ↔
    ∃ n : ℕ, n ≠ 0 ∧ theta (n • x) = 0
  simp only [map_nsmul]

theorem torsionRelation_saturated (theta : Λ →+ T) (k : ℕ) (hk : k ≠ 0)
    (x : Λ) : k • x ∈ torsionRelation theta ↔ x ∈ torsionRelation theta := by
  constructor
  · rintro ⟨n, hn, hx⟩
    refine ⟨n*k, Nat.mul_ne_zero hn hk, ?_⟩
    simpa only [map_nsmul, smul_smul] using hx
  · rintro ⟨n, hn, hx⟩
    refine ⟨n, hn, ?_⟩
    rw [map_nsmul]
    calc
      n • (k • theta x) = k • (n • theta x) := by
        rw [smul_smul, smul_smul, Nat.mul_comm]
      _ = 0 := by rw [hx, smul_zero]

theorem torsion_annihilator_maps (f : T →+ W) (x : T) (n : ℕ)
    (hx : n • x = 0) : n • f x = 0 := by
  rw [← map_nsmul, hx, map_zero]

/-- The curvature comparison has a torsion-free target; it detects necessity only. -/
theorem torsionRelation_le_curvatureKernel (theta : Λ →+ T)
    (C : Λ →+ W) (curv : T →+ W) (hcomp : curv.comp theta = C)
    (noTorsion : ∀ (n : ℕ), n ≠ 0 → ∀ w : W, n • w = 0 → w = 0) :
    torsionRelation theta ≤ C.ker := by
  rintro x ⟨n, hn, hx⟩
  change C x = 0
  have he := congrArg (fun f : Λ →+ W => f x) hcomp
  change curv (theta x) = C x at he
  apply noTorsion n hn (C x)
  rw [← he]
  exact torsion_annihilator_maps curv (theta x) n hx

/-- Polarization necessity: an isogeny killing the torsor supplies a finite order. -/
theorem isogeny_kernel_torsion (f : T →+ W) (g : W →+ T)
    (n : ℕ) (hn : n ≠ 0) (hcomp : ∀ x, g (f x) = n • x)
    (x : T) (hx : f x = 0) : ∃ k : ℕ, k ≠ 0 ∧ k • x = 0 := by
  refine ⟨n, hn, ?_⟩
  rw [← hcomp, hx, map_zero]

/-- Every finite collection of torsion coordinates has a single finite cover order. -/
theorem finite_torsion_common_annihilator (xs : List T)
    (h : ∀ x ∈ xs, ∃ n : ℕ, n ≠ 0 ∧ n • x = 0) :
    ∃ n : ℕ, n ≠ 0 ∧ ∀ x ∈ xs, n • x = 0 := by
  revert h
  induction xs with
  | nil => intro h; exact ⟨1, by decide, by simp⟩
  | cons x xs ih =>
    intro h
    obtain ⟨n, hn, hx⟩ := h x (List.mem_cons_self)
    obtain ⟨m, hm, hxs⟩ := ih (by
      intro y hy
      exact h y (List.mem_cons_of_mem x hy))
    refine ⟨n*m, Nat.mul_ne_zero hn hm, ?_⟩
    intro y hy
    rcases List.mem_cons.mp hy with hxy | hy
    · subst y
      calc
        (n*m) • x = m • (n • x) := by rw [smul_smul, Nat.mul_comm]
        _ = 0 := by rw [hx, smul_zero]
    · rw [← smul_smul, hxs y hy, smul_zero]

/-- A projective quotient's relation map factors through the saturated relations. -/
def torsionRestoringLift (theta : Λ →+ T) (I : U →+ Λ)
    (h : ∀ u, I u ∈ torsionRelation theta) : U →+ torsionRelation theta where
  toFun u := ⟨I u, h u⟩
  map_zero' := by apply Subtype.ext; exact I.map_zero
  map_add' u v := by apply Subtype.ext; exact I.map_add u v

theorem torsionRestoringLift_underlying (theta : Λ →+ T) (I : U →+ Λ)
    (h : ∀ u, I u ∈ torsionRelation theta) :
    (torsionRelation theta).subtype.comp (torsionRestoringLift theta I h) = I := by
  ext u
  rfl

theorem projective_relation_factorization_unique (theta : Λ →+ T) (I : U →+ Λ)
    (h : ∀ u, I u ∈ torsionRelation theta) :
    ∃! J : U →+ torsionRelation theta, (torsionRelation theta).subtype.comp J = I := by
  refine ⟨torsionRestoringLift theta I h, torsionRestoringLift_underlying theta I h, ?_⟩
  intro J hJ
  apply AddMonoidHom.ext
  intro u
  apply Subtype.ext
  exact congrArg (fun F : U →+ Λ => F u) hJ

#print axioms torsionRelation_saturated
#print axioms projective_relation_factorization_unique
end ProjectiveRestoringRelations

/-! ## Transfer through arbitrary projective folds and actual boundary sources

The companion hand derivation constructs the raw transfer geometrically as
f_*(h^r * -), of positive generic degree d. These algebraic drafts take that
actual transfer and its comparison equations as inputs. They do not assert
the existence of a cycle for an arbitrary Hodge class or of an algebraic
compactification of its topological nullhomotopy. Compilation is owner-run.
-/
section ProjectiveFoldTransfer
variable {V W Z NX NY : Type*}
  [AddCommGroup V] [Module ℚ V] [AddCommGroup W] [Module ℚ W]
  [AddCommGroup Z] [Module ℚ Z]
  [AddCommGroup NX] [Module ℚ NX] [AddCommGroup NY] [Module ℚ NY]

def normalizedFoldReturn (tr : W →ₗ[ℚ] V) (d : ℚ) : W →ₗ[ℚ] V := d⁻¹ • tr

theorem normalizedFoldReturn_pullback (pull : V →ₗ[ℚ] W)
    (tr : W →ₗ[ℚ] V) (d : ℚ) (hd : d ≠ 0)
    (htr : ∀ a, tr (pull a) = d • a) (a : V) :
    normalizedFoldReturn tr d (pull a) = a := by
  simp only [normalizedFoldReturn, LinearMap.smul_apply, htr, smul_smul]
  rw [inv_mul_cancel₀ hd, one_smul]

theorem fold_pullback_injective (pull : V →ₗ[ℚ] W)
    (tr : W →ₗ[ℚ] V) (d : ℚ) (hd : d ≠ 0)
    (htr : ∀ a, tr (pull a) = d • a) : Function.Injective pull := by
  intro a b hab
  calc
    a = normalizedFoldReturn tr d (pull a) :=
      (normalizedFoldReturn_pullback pull tr d hd htr a).symm
    _ = normalizedFoldReturn tr d (pull b) := congrArg _ hab
    _ = b := normalizedFoldReturn_pullback pull tr d hd htr b

theorem projective_fold_nullifier_zero (pull : V →ₗ[ℚ] W)
    (tr : W →ₗ[ℚ] V) (d : ℚ) (hd : d ≠ 0)
    (htr : ∀ a, tr (pull a) = d • a) (a : V) (ha : pull a = 0) :
    a = 0 := by
  apply fold_pullback_injective pull tr d hd htr
  simpa using ha

theorem projective_fold_retains_nonzero (pull : V →ₗ[ℚ] W)
    (tr : W →ₗ[ℚ] V) (d : ℚ) (hd : d ≠ 0)
    (htr : ∀ a, tr (pull a) = d • a) (a : V) :
    pull a ≠ 0 ↔ a ≠ 0 := by
  constructor
  · intro h ha; exact h (by rw [ha, map_zero])
  · intro h ha; exact h (projective_fold_nullifier_zero pull tr d hd htr a ha)

/-- Raw degrees multiply under composition; both maps retain the marked base. -/
theorem foldTransfer_composite (f : V →ₗ[ℚ] W) (g : W →ₗ[ℚ] Z)
    (rf : W →ₗ[ℚ] V) (rg : Z →ₗ[ℚ] W) (d e : ℚ)
    (hf : ∀ a, rf (f a) = d • a) (hg : ∀ b, rg (g b) = e • b)
    (a : V) :
    (rf.comp rg) ((g.comp f) a) = (e*d) • a := by
  simp only [LinearMap.comp_apply, hg, map_smul, hf, smul_smul]

theorem normalizedFoldReturn_composite (rf : W →ₗ[ℚ] V)
    (rg : Z →ₗ[ℚ] W) (d e : ℚ) :
    normalizedFoldReturn (rf.comp rg) (e*d) =
      (normalizedFoldReturn rf d).comp (normalizedFoldReturn rg e) := by
  ext a
  simp only [normalizedFoldReturn, LinearMap.smul_apply, LinearMap.comp_apply,
    map_smul, smul_smul, mul_inv_rev, mul_comm]

theorem foldReturn_projector_idempotent (pull : V →ₗ[ℚ] W)
    (tr : W →ₗ[ℚ] V) (d : ℚ) (hd : d ≠ 0)
    (htr : ∀ a, tr (pull a) = d • a) (b : W) :
    pull (normalizedFoldReturn tr d (pull (normalizedFoldReturn tr d b))) =
      pull (normalizedFoldReturn tr d b) := by
  rw [normalizedFoldReturn_pullback pull tr d hd htr]

theorem foldReturn_remainder_killed (pull : V →ₗ[ℚ] W)
    (tr : W →ₗ[ℚ] V) (d : ℚ) (hd : d ≠ 0)
    (htr : ∀ a, tr (pull a) = d • a) (b : W) :
    normalizedFoldReturn tr d (b - pull (normalizedFoldReturn tr d b)) = 0 := by
  rw [map_sub, normalizedFoldReturn_pullback pull tr d hd htr, sub_self]

/-- Applies an actual cycle transfer; the canonical comparison is explicit. -/
theorem transferred_cycle_class (clX : NX →ₗ[ℚ] V) (clY : NY →ₗ[ℚ] W)
    (pull : V →ₗ[ℚ] W) (tr : W →ₗ[ℚ] V) (cycleTr : NY →ₗ[ℚ] NX)
    (d : ℚ) (hd : d ≠ 0) (htr : ∀ a, tr (pull a) = d • a)
    (hcompare : ∀ z, clX (cycleTr z) = tr (clY z))
    (a : V) (z : NY) (hz : clY z = pull a) :
    clX (d⁻¹ • cycleTr z) = a := by
  rw [map_smul, hcompare, hz]
  exact normalizedFoldReturn_pullback pull tr d hd htr a

/-- A genuine source-image statement, not a surjectivity assumption. -/
theorem fold_cycle_image_iff (clX : NX →ₗ[ℚ] V) (clY : NY →ₗ[ℚ] W)
    (pull : V →ₗ[ℚ] W) (tr : W →ₗ[ℚ] V)
    (cyclePull : NX →ₗ[ℚ] NY) (cycleTr : NY →ₗ[ℚ] NX)
    (d : ℚ) (hd : d ≠ 0) (htr : ∀ a, tr (pull a) = d • a)
    (hpush : ∀ z, clX (cycleTr z) = tr (clY z))
    (hpull : ∀ z, clY (cyclePull z) = pull (clX z)) (a : V) :
    pull a ∈ LinearMap.range clY ↔ a ∈ LinearMap.range clX := by
  constructor
  · rintro ⟨z, hz⟩
    exact ⟨d⁻¹ • cycleTr z,
      transferred_cycle_class clX clY pull tr cycleTr d hd htr hpush a z hz⟩
  · rintro ⟨z, hz⟩
    exact ⟨cyclePull z, by rw [hpull, hz]⟩

/-- The finite boundary combination itself is retained, before its return. -/
theorem boundary_combination_return {ι : Type*} [Fintype ι]
    (clX : NX →ₗ[ℚ] V) (clY : NY →ₗ[ℚ] W)
    (pull : V →ₗ[ℚ] W) (tr : W →ₗ[ℚ] V) (cycleTr : NY →ₗ[ℚ] NX)
    (d : ℚ) (hd : d ≠ 0) (htr : ∀ a, tr (pull a) = d • a)
    (hcompare : ∀ z, clX (cycleTr z) = tr (clY z))
    (a : V) (coeff : ι → ℚ) (boundary : ι → NY)
    (hboundary : (∑ i, coeff i • clY (boundary i)) = pull a) :
    clX (d⁻¹ • cycleTr (∑ i, coeff i • boundary i)) = a := by
  apply transferred_cycle_class clX clY pull tr cycleTr d hd htr hcompare
  simpa only [map_sum, map_smul] using hboundary

/-- Different boundary solutions need agree only after the Betti map. -/
theorem boundary_solution_difference_nullhomologous
    (clX : NX →ₗ[ℚ] V) (clY : NY →ₗ[ℚ] W)
    (tr : W →ₗ[ℚ] V) (cycleTr : NY →ₗ[ℚ] NX) (d : ℚ)
    (hcompare : ∀ z, clX (cycleTr z) = tr (clY z))
    (z w : NY) (hzw : clY z = clY w) :
    clX (d⁻¹ • cycleTr z - d⁻¹ • cycleTr w) = 0 := by
  rw [map_sub, map_smul, map_smul, hcompare, hcompare, hzw, sub_self]

#print axioms projective_fold_nullifier_zero
#print axioms fold_cycle_image_iff
#print axioms boundary_combination_return
end ProjectiveFoldTransfer

/-! ## Divisorial source extraction and the ample-boundary test

The hand proof constructs rational Hodge lifts using a polarized kernel
complement, and in codimension two constructs genuine boundary line bundles.
These algebraic drafts retain every supplied comparison and denominator.
No arbitrary Hodge-to-Chow surjection is postulated.
-/
section DivisorialBoundaryReturn
variable {B V W NX NY : Type*}
  [AddCommGroup B] [Module ℚ B] [AddCommGroup V] [Module ℚ V]
  [AddCommGroup W] [Module ℚ W]
  [AddCommGroup NX] [Module ℚ NX] [AddCommGroup NY] [Module ℚ NY]

/-- A commuting rational type correction retains the exact target class.
The hand polarization construction, rather than an arbitrary complex type
projection, supplies such correction data when it is used geometrically. -/
theorem corrected_boundary_lift (G : B →ₗ[ℚ] V)
    (sourceCorrection : B →ₗ[ℚ] B) (targetCorrection : V →ₗ[ℚ] V)
    (hcommute : G.comp sourceCorrection = targetCorrection.comp G)
    (b : B) (a : V) (hb : G b = a) (ha : targetCorrection a = a) :
    G (sourceCorrection b) = a := by
  have h := congrArg (fun F : B →ₗ[ℚ] V => F b) hcommute
  simpa only [LinearMap.comp_apply, hb, ha] using h

theorem boundary_lifts_differ_by_kernel (G : B →ₗ[ℚ] V) (b c : B) :
    G b = G c ↔ b-c ∈ G.ker := by
  change G b = G c ↔ G (b-c) = 0
  rw [map_sub, sub_eq_zero]

theorem restriction_unchanged_by_boundary (G : B →ₗ[ℚ] V)
    (restrict : V →ₗ[ℚ] W) (hzero : restrict.comp G = 0)
    (a : V) (b : B) : restrict (a-G b) = restrict a := by
  have h := congrArg (fun F : B →ₗ[ℚ] W => F b) hzero
  have hb : restrict (G b) = 0 := by simpa using h
  rw [map_sub, hb, sub_zero]

/-- Integral boundary line bundles may represent N times the lifted input;
the genuine generic multisection degree contributes its separate factor d. -/
theorem denominator_cleared_boundary_return
    (clX : NX →ₗ[ℚ] V) (clY : NY →ₗ[ℚ] W)
    (pull : V →ₗ[ℚ] W) (tr : W →ₗ[ℚ] V) (cycleTr : NY →ₗ[ℚ] NX)
    (d N : ℚ) (hd : d ≠ 0) (hN : N ≠ 0)
    (htr : ∀ a, tr (pull a) = d • a)
    (hcompare : ∀ z, clX (cycleTr z) = tr (clY z))
    (a : V) (boundaryCycle : NY) (hboundary : clY boundaryCycle = N • pull a) :
    clX ((N*d)⁻¹ • cycleTr boundaryCycle) = a := by
  calc
    clX ((N*d)⁻¹ • cycleTr boundaryCycle) =
        (N*d)⁻¹ • (N • (d • a)) := by
      rw [map_smul, hcompare, hboundary, map_smul, htr]
    _ = ((N*d)⁻¹ * (N*d)) • a := by rw [smul_smul N d a, smul_smul]
    _ = a := by rw [inv_mul_cancel₀ (mul_ne_zero hN hd), one_smul]

/-- The geometric hand theorem proves ker(restrict)=range(L) for a smooth
ample boundary. A nonzero primitive readout then survives that actual open. -/
theorem ample_primitive_survives_restriction (L : B →ₗ[ℚ] V)
    (restrict : V →ₗ[ℚ] W) (primitive : V →ₗ[ℚ] V)
    (hkernel : restrict.ker = LinearMap.range L)
    (hprimitive : primitive.comp L = 0)
    (a : V) (ha : primitive a ≠ 0) : restrict a ≠ 0 := by
  intro hzero
  have hm : a ∈ LinearMap.range L := by
    rw [← hkernel]
    exact hzero
  obtain ⟨b, hb⟩ := hm
  apply ha
  rw [← hb]
  have h := congrArg (fun F : B →ₗ[ℚ] V => F b) hprimitive
  simpa using h

#print axioms denominator_cleared_boundary_return
#print axioms ample_primitive_survives_restriction
end DivisorialBoundaryReturn

end GSTCausalFoldDefect
