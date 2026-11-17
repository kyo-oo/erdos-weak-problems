import Mathlib

/-!
# GST universal projective-product primitive codimension-two constructor

For every smooth projective complex d-fold X, d>=2, with an ample
hyperplane class h, and the projective plane P² with hyperplane t,
consider Y=X×P². Write u=pr_X^*h, v=pr_P²^*t.
Then u^(d+1)=0 and v³=0 on actual Betti cohomology; the
ample class L=u+v has exponent d-1 in the primitive condition
for codimension 2 of the (d+2)-dimensional product.

The genuine algebraic cycle

 P_d = u² - (d-1)*u*v + (d*(d-1)/2)*v²

is PRIMITIVE: L^(d-1) P_d=0. It is NONZERO: multiplication
by v² picks out u²*v², and h² is nonzero by positive ample
top degree on every smooth projective d-fold for d>=2.

This Lean module checks the entire dimension-uniform *rational
coefficient and primitive-kernel calculation* in a precise
3-coordinate cohomology model. It does NOT claim to formalize
the scheme-theoretic cohomology ring or the external classical
ample intersection theorem for all smooth projective X.

This is a genuine geometric primitive CYCLE construction for
the UNBOUNDED family X×P² for ARBITRARY X and d>=2, but does
not construct each primitive Hodge class on arbitrary X itself.
-/

set_option maxHeartbeats 1000000

namespace GSTUniversalProjectiveProductPrimitive

/-- Coefficients of u²,uv,v² in degree four. -/
abbrev HodgeCodimTwo := ℚ × (ℚ × ℚ)

/-- Coefficients of u^d*v,u^(d-1)*v², after multiplying
a codimension-two class by L^(d-1), modulo u^(d+1)=v³=0. -/
abbrev HodgeNearTop := ℚ × ℚ

/-- The actual projective-product Hard Lefschetz multiplier
in rational coordinate form. -/
def hyperplaneCupToNearTop (d : ℕ)
    (w : HodgeCodimTwo) : HodgeNearTop :=
  let k : ℚ := (d:ℚ)-1
  (k*w.1+w.2.1,
    (k*(k-1)/2)*w.1+k*w.2.1+w.2.2)

/-- Coefficients of a genuine algebraic cycle:
h² - (d-1) h*t + binomial(d,2) t². -/
def actualPrimitiveProductCycle (d : ℕ) : HodgeCodimTwo :=
  (1, (-((d:ℚ)-1), (d:ℚ)*((d:ℚ)-1)/2))

/-- At every dimension d, the explicit algebraic cycle is killed
by the correct power of L. No assumed primitive-cycle witness. -/
theorem actualPrimitiveProductCycle_primitive (d : ℕ) :
    hyperplaneCupToNearTop d (actualPrimitiveProductCycle d) =
      (0,0) := by
  apply Prod.ext
  · dsimp [hyperplaneCupToNearTop,actualPrimitiveProductCycle]
    ring
  · dsimp [hyperplaneCupToNearTop,actualPrimitiveProductCycle]
    ring

/-- It has a nonzero u² coefficient, and therefore is a
nonzero cohomology class whenever u² is genuinely nonzero
and Kunneth degree components are independent. -/
theorem actualPrimitiveProductCycle_nonzero (d : ℕ) :
    actualPrimitiveProductCycle d ≠ (0,(0,0)) := by
  intro hz
  have h := congrArg Prod.fst hz
  norm_num [actualPrimitiveProductCycle] at h

/-- Every primitive class INSIDE the explicit three-generator
hyperplane subalgebra of X×P² is a rational multiple of P_d.
This says nothing about independent primitive cohomology
inherited from X outside the hyperplane subalgebra. -/
theorem primitive_hyperplane_subspace_unique
    (d : ℕ) (w : HodgeCodimTwo)
    (hw : hyperplaneCupToNearTop d w = (0,0)) :
    w =
      (w.1,
        (-((d:ℚ)-1)*w.1,
          ((d:ℚ)*((d:ℚ)-1)/2)*w.1)) := by
  rcases w with ⟨a,⟨b,c⟩⟩
  have h1 := congrArg Prod.fst hw
  dsimp [hyperplaneCupToNearTop] at h1
  have h2 := congrArg Prod.snd hw
  dsimp [hyperplaneCupToNearTop] at h2
  have hb : b = -((d:ℚ)-1)*a := by
    linarith
  have hc : c = ((d:ℚ)*((d:ℚ)-1)/2)*a := by
    rw [hb] at h2
    nlinarith [h2]
  simp [hb,hc]

/-- A uniform actual-coefficient constructor for the primitive
subspace; the output is a rational linear combination of
geometrically defined algebraic intersections. -/
def constructPrimitiveHyperplaneCycle
    (d : ℕ) (w : HodgeCodimTwo) : HodgeCodimTwo :=
  (w.1,
    (-((d:ℚ)-1)*w.1,
      ((d:ℚ)*((d:ℚ)-1)/2)*w.1))

theorem constructPrimitiveHyperplaneCycle_correct
    (d : ℕ) (w : HodgeCodimTwo)
    (hw : hyperplaneCupToNearTop d w = (0,0)) :
    constructPrimitiveHyperplaneCycle d w = w := by
  exact (primitive_hyperplane_subspace_unique d w hw).symm

theorem constructPrimitiveHyperplaneCycle_primitive
    (d : ℕ) (w : HodgeCodimTwo) :
    hyperplaneCupToNearTop d
      (constructPrimitiveHyperplaneCycle d w) = (0,0) := by
  apply Prod.ext
  · dsimp [hyperplaneCupToNearTop,constructPrimitiveHyperplaneCycle]
    ring
  · dsimp [hyperplaneCupToNearTop,constructPrimitiveHyperplaneCycle]
    ring

#check actualPrimitiveProductCycle_primitive
#check actualPrimitiveProductCycle_nonzero
#check primitive_hyperplane_subspace_unique
#check constructPrimitiveHyperplaneCycle_correct

#print axioms actualPrimitiveProductCycle_primitive
#print axioms actualPrimitiveProductCycle_nonzero
#print axioms constructPrimitiveHyperplaneCycle_correct

end GSTUniversalProjectiveProductPrimitive
