import Mathlib

/-!
# Finite-group cocycles: explicit integral kill and rational primitive

Uncompiled proof draft. Finiteness and the actual cocycle equation are
essential. An infinite translation groupoid is not silently replaced by G.
The nonabelian product theorem corrects an actual abelian extension layer;
it does not claim arbitrary SL-valued defects have such a layer.
-/

open scoped BigOperators
noncomputable section
namespace GSTFiniteGroupCocycleAveraging

section Integral
variable {G M : Type*} [Group G] [Fintype G] [AddCommGroup M]

def cocycleSum (c : G → G → M) (g : G) : M := ∑ k, c g k

/-- The identity only needs the displayed additive actions and equations.
A geometric group action must independently satisfy its representation law. -/
def IsTwoCocycle (rho : G → (M →+ M)) (c : G → G → M) : Prop :=
  ∀ g h k, c g h + c (g*h) k = rho g (c h k) + c g (h*k)

theorem sum_left_permutation (f : G → M) (h : G) :
    (∑ k, f (h*k)) = ∑ k, f k := by
  exact Fintype.sum_equiv (Equiv.mulLeft h)
    (fun k => f (h*k)) f (fun k => rfl)

/-- Universal |G|-kill with an actual primitive and no cohomology stub. -/
theorem integral_averaging (rho : G → (M →+ M)) (c : G → G → M)
    (hc : IsTwoCocycle rho c) (g h : G) :
    cocycleSum c g + rho g (cocycleSum c h) - cocycleSum c (g*h) =
      Fintype.card G • c g h := by
  have hsum : Fintype.card G • c g h + cocycleSum c (g*h) =
      rho g (cocycleSum c h) + cocycleSum c g := by
    calc
      Fintype.card G • c g h + cocycleSum c (g*h) =
          ∑ k, (c g h + c (g*h) k) := by
            simp [cocycleSum, Finset.sum_add_distrib]
      _ = ∑ k, (rho g (c h k) + c g (h*k)) := by
            apply Finset.sum_congr rfl
            intro k hk
            exact hc g h k
      _ = rho g (cocycleSum c h) + cocycleSum c g := by
            rw [Finset.sum_add_distrib, ← map_sum, sum_left_permutation]
            rfl
  have hswap : cocycleSum c g + rho g (cocycleSum c h) =
      Fintype.card G • c g h + cocycleSum c (g*h) := by rw [hsum]; abel
  rw [hswap]
  abel
end Integral

section Rational
variable {G V : Type*} [Group G] [Fintype G] [AddCommGroup V] [Module ℚ V]

def averagedPrimitive (c : G → G → V) (g : G) : V :=
  (Fintype.card G : ℚ)⁻¹ • cocycleSum c g

theorem rational_averaging (rho : G → Module.End ℚ V) (c : G → G → V)
    (hc : IsTwoCocycle (fun g => (rho g).toAddMonoidHom) c) (g h : G) :
    averagedPrimitive c g + rho g (averagedPrimitive c h) -
      averagedPrimitive c (g*h) = c g h := by
  have hm : (Fintype.card G : ℚ) ≠ 0 := by
    exact_mod_cast Fintype.card_ne_zero
  calc
    averagedPrimitive c g + rho g (averagedPrimitive c h) - averagedPrimitive c (g*h) =
        (Fintype.card G : ℚ)⁻¹ •
          (cocycleSum c g + rho g (cocycleSum c h) - cocycleSum c (g*h)) := by
            simp [averagedPrimitive, smul_add, smul_sub, map_smul]
    _ = (Fintype.card G : ℚ)⁻¹ • (Fintype.card G • c g h) := by
          rw [← LinearMap.toAddMonoidHom_coe,
            integral_averaging (fun g => (rho g).toAddMonoidHom) c hc]
    _ = c g h := by
          rw [← Nat.cast_smul_eq_nsmul ℚ, smul_smul]
          simp [hm]

theorem normalized_primitive (c : G → G → V) (hc : ∀ k, c 1 k=0) :
    averagedPrimitive c 1=0 := by simp [averagedPrimitive, cocycleSum, hc]

/-- The corrected lifts satisfy an actual multiplicative equation. -/
theorem correct_extension_product {E : Type*} [Group E]
    (rho : G → Module.End ℚ V) (embed : V → E)
    (embed_add : ∀ u v, embed (u+v)=embed u*embed v)
    (sectionLift : G → E) (c : G → G → V) (b : G → V)
    (slide : ∀ g v, sectionLift g*embed v=embed (rho g v)*sectionLift g)
    (product_rule : ∀ g h, sectionLift g*sectionLift h=embed (c g h)*sectionLift (g*h))
    (primitive : ∀ g h, b g+rho g (b h)-b (g*h)=c g h) (g h : G) :
    (embed (-b g)*sectionLift g)*(embed (-b h)*sectionLift h) =
      embed (-b (g*h))*sectionLift (g*h) := by
  have hcoef : -b g + rho g (-b h) + c g h = -b (g*h) := by
    rw [map_neg, ← primitive g h]
    abel
  calc
    (embed (-b g)*sectionLift g)*(embed (-b h)*sectionLift h) =
        (embed (-b g)*embed (rho g (-b h)))*(sectionLift g*sectionLift h) := by
          rw [mul_assoc, ← mul_assoc (sectionLift g), slide]
          simp only [mul_assoc]
    _ = embed (-b g + rho g (-b h))*(embed (c g h)*sectionLift (g*h)) := by
          rw [← embed_add, product_rule]
    _ = embed (-b g + rho g (-b h) + c g h)*sectionLift (g*h) := by
          rw [← mul_assoc, ← embed_add]
    _ = embed (-b (g*h))*sectionLift (g*h) := by rw [hcoef]
end Rational

#print axioms integral_averaging
#print axioms rational_averaging
#print axioms correct_extension_product
end GSTFiniteGroupCocycleAveraging
