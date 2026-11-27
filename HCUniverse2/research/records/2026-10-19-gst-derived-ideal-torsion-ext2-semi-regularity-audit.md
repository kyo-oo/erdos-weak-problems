# Mathbox GST — finite-étale split of the derived CM pair and a 576-dimensional raw Ext² pressure test

- **Date:** 2026-10-19
- **Kind:** adversarial geometric source/deformation audit; correction to overly optimistic single-object semiregularity expectation
- **Corrects/extends:** [derived graph-ideal incidence and Euler source](2026-10-19-gst-derived-ideal-incident-cohomology-self-euler-source.md).
- **Original target:** actual rational Chow source for arbitrary original X and primitive Hodge target. This bounded audit concerns a concrete CM abelian sixfold test object.
- **Base:** `66bb014c1306c142b6205aa5ed470c1dddcad5ae`
- **Lean code:** `GSTUniversalCMArithmeticObstruction.lean`, new commit `74d5e52f9703768a2a4295d5913f0cedf40aec62`. This checks the general torsion-orbit factorization and the exact finite dimension inequality, NOT derived Ext formalization.
- **Numerics independently reproduced:** 64 torsion elements, 64 free anti-diagonal pair orbits of size 64, 9 tangent tensor directions per orbit, giving 576; raw semireg target 495.

## 1. A concrete finite-étale cover turns the derived object into an exterior tensor

The two distinct codimension-three CM graph abelian subvarieties Z₀,Z₁⊂A=E⁶ are complementary as Lie subgroups. Their intersection is P=E[2]³≅(ℤ/2)^6 (64 points). The addition map
`φ: Z₀×Z₁→A, (a,b)↦a+b`
is an isogeny with deck kernel `G={(t,-t):t∈P}`, of order 64. It is finite étale in characteristic zero.

The scheme-theoretic inverse images under φ are `Z₀×P` and `P×Z₁`. Therefore
`φ*I_{Z₀}=pr₂*I_{P/Z₁}`, `φ*I_{Z₁}=pr₁*I_{P/Z₀}` (pullback notation, not proper pushforward).

For F=RHom(I_{Z₀},O_A)⊗^L I_{Z₁}, finite flat base change gives the **actual external tensor model**
`φ*F ≅ pr₁*I_{P/Z₀} ⊗^L pr₂*(RHom(I_{P/Z₁},O_{Z₁})).`

This makes the one-object complex much more explicit, but also reveals that the tensor construction has **not itself created an indecomposable derived coupling** under étale base change.

## 2. Exact point-motion representation in Ext¹ of an ideal of reduced points

For B a smooth abelian threefold and P⊂B a finite reduced translation-invariant 64-point subgroup, the fixed-determinant first-order deformation tangent of the ideal I_P contains, in fact equals, the Hilbert tangent
`Hom_B(I_P,O_P) ≅ ⊕_{p∈P} T_p B ≅ ℂ³⊗ℂ[P]`.

Its dimension is 3·64=192; translation by G permutes P freely and acts trivially on the derivative coordinates. It is a quotient of Ext¹_B(I_P,I_P); equivalently it splits off equivariantly because G is finite and the ground field has characteristic zero. The derived dual ideal has isomorphic self Ext¹ G-representations by the duality anti-equivalence.

Thus the Künneth summand
`Ext¹(I_P,I_P)⊗Ext¹(I_P^∨,I_P^∨)⊂Ext²(φ*F,φ*F)`
contains an equivariant tensor of **two** 192-dimensional point-motion representations.

## 3. Deck invariants and the raw-semiregularity dimension inequality

Under deck translation t∈P, point labels move by `(p,q)→(p+t,q−t)`. An invariant function f on P×P factors uniquely as
`f(p,q)=h(p+q)`.
The Lean theorem `cmWeilSixfoldTorsionPairOrbit_invariant_iff_factors` proves this for **every abelian group**, not merely the chosen 64-element model. There are |P|=64 orbits, each with 3×3=9 independent tangent-tensor coordinates. Exact invariant dimension:

`dim[(ℂ³⊗ℂ[P]) ⊗ (ℂ³⊗ℂ[P])]ᴳ = 64·3·3 = 576.`

By finite étale Galois descent in characteristic zero, `Ext²_A(F,F)≅Ext²_{Z₀×Z₁}(φ*F,φ*F)^G`. Hence the original Ext² has dimension **at least 576**, subject to the stated standard scheme/derived identifications being carried out for this actual object.

On an abelian sixfold, the complete raw Buchweitz–Flenner semiregularity target has dimension
`Σ_{k=0}⁴ dim H^{k+2}(A, Ω_A^k)
 = Σ_{k=0}⁴ binom(6,k) binom(6,k+2)
 =15+120+225+120+15=495.`

Thus **576>495** rules out injectivity of the *full raw semiregularity map* for F if the geometric Ext² descent is instantiated exactly. The Lean theorem `cmWeilSixfoldTorsionPairExtTwo_rawSemiregSizeTest` proves the arithmetic 576>495, not the external Ext equivalence.

This is not a nonalgebraic Weil counterexample and not a proof that `At(F)⌟κ` is nonzero. A potentially much smaller actual obstruction image may still vanish despite noninjective raw semiregularity.

## 4. The mathematically changed route

The prior index identity `χ(F,F)=0` does not control Ext² dimensions; the étale cover reveals why. Avoid trying to prove raw semiregularity injectivity of THIS uncoupled tensor-derived F without first addressing its 576 point-motion sector. Choose one of two discriminators:

1. Compute the actual Atiyah/Kodaira–Spencer obstruction `At(F)⌟κ` on a named non-split Weil-period tangent and establish its vanishing directly, **without** assuming raw semireg injectivity.
2. Construct a genuinely non-split coherent/perfect object with a derived differential that kills or identifies these point-motion Ext² packets while retaining the explicit exceptional Weil Chern character and canonical periods. The previously recorded finite incidence Yoneda kernels provide candidate geometry, but their effect on full Ext² must be calculated, not asserted.

- **Outcome:** rigorous orbit arithmetic; geometric Ext² lower bound conditional on standard equivariant derived-category identifications; noninjectivity test for the specific F, not the general Hodge target.
- **Evidence:** Lean numerical/action lemmas pending revision-matched CI, Python exact bit-group orbit enumeration. Self-review, not an independently peer-verified derived-category proof.
- **Disposition:** original all-X program open; naive raw semiregularity-injection route for F obstructed if geometric descent holds, Atiyah-obstruction and genuinely coupled source routes remain open.
