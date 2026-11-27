# GST exceptional birth on a rational blowup: exact original-X return and residual readout

**Date:** 20 October 2026 (IST). **Branch:** `research/gpt6-native-point-primitive-span-20261017`.
**Lean source:** `GSTGraphV2SelfExpandingCosmology.lean`, namespace `NativeGeometryBirth.BlowupRationalHodgeTest`.
**Construction commits:** `213136a3fd4de5c7b8fd6104c067517be1089f1e`, `5b1c227e3fb045d9dbb6cd5cbac1de19586abac6`.
**First revision-matched CI:** Graph V2 CM NM Geometry Upgrade [#39405037695](https://github.com/kyo-oo/HC-PROOF/actions/runs/39405037695), success for `213136a3`. Recheck the later readout commit's own workflow before promoting its verification.

## Construction from an arbitrary original X

Let X be any smooth projective complex n-fold and choose an algebraic embedding i:X→P^N with c=N−n≥2 (enlarge the projective embedding if needed). Define the genuine smooth rational blowup world Y=Bl_X(P^N), exceptional Cartier divisor j:E=P(N_{X/P^N})→Y, bundle q:E→X, and ξ=c₁(O_E(1)) in CH¹(E). All constructions are algebraic on named actual schemes.

For an arbitrary prescribed rational codimension-p Hodge class alpha on X, there is a canonical cohomological exceptional marked birth

  gamma_alpha = j_*(q^* alpha) in Hdg^(p+1)(Y)_Q.

This definition does **not** assert gamma_alpha algebraic. Suppose a GST geometric event actually produces an independent **algebraic** W in CH^(p+1)(Y)_Q whose canonical Betti class equals gamma_alpha. Define the native rational Chow return

  R(W) = -q_*( ξ^(c-2) · j^!(W) ) in CH^p(X)_Q.

Here j^! is the refined divisor Gysin pullback (equal to the usual restriction in Chow cohomology for the smooth varieties at hand). Its output lives on **the original X**, not an altered model. Two standard exceptional geometry identities, interpreted as semantic bridges for GST's actual birth geometry, are

  j^* j_*(q^*alpha) = -ξ q^*alpha,   q_*(ξ^(c-1) q^*alpha) = alpha.

Therefore, with naturality of genuine canonical cycle classes,

  cl_X(R(W))
   = -q_*(ξ^(c-2) j^*(cl_Y W))
   = -q_*(ξ^(c-2) j^*j_*q^*alpha)
   = q_*(ξ^(c-1) q^*alpha)
   = alpha.

No Hodge-to-Chow inverse and no already-known cycle on original X enters this forward construction. **The nontrivial input is independently producing W on Y with the required canonical cohomology class.** The present Lean compiler verifies the rational-linear return under the corresponding explicit scheme/Betti functoriality identities; it does not yet instantiate the entire geometric scheme-to-Betti square in Lean or build W universally.

## Source-detection form (less than exact representative)

Let ell_X be the original-X target residual functional. From any independently native W in CH^(p+1)(Y)_Q we get the exact conservation relation

  ell_X(cl_X R(W)) =
    -ell_X( q_*(ξ^(c-2) j^*(cl_Y W)) ).

The RHS is a computable target-sensitive exceptional readout ell_Y on the born cohomology. Thus **nonzero ell_Y(cl_Y W)** produces a real original-X detecting algebraic Chow cycle, even if W's full class is not gamma_alpha. Moreover ell_Y(gamma_alpha)=ell_X(alpha), an exact self-intersection/fiber-integration identity. This narrows the GST birth challenge to a verified nonzero genuine exceptional readout, rather than selecting an arbitrary target preimage.

Implemented theorem names:
- `exceptional_lift_return_identity`, `exceptionalOriginalXCycle`;
- `exceptional_lift_cycle_recovery`, `exceptional_lift_range_iff`;
- `exceptional_native_residual_readout`, `exceptional_native_residual_detected_of_birth`, `exceptional_prescribed_target_readout`.

## Arbitrary-arity exceptional channels have an invertible triangular return matrix

Fix a total codimension q on Y. The i-th exceptional input module is B_i=Hdg^(q−i)(X)_Q (and analogously CH^(q−i)(X)_Q). For every 1≤i≤c−1 the graded exceptional Hodge channel E_i:B_i→Hdg^q(Y)_Q is E_i(a)=j_*(ξ^(i−1)q^*a), and the return R_i:Hdg^q(Y)_Q→B_i is R_i(b)=−q_*(ξ^(c−1−i)j^*b). All off-diagonal entries are degree-raising operators B_j→B_i, **not scalar maps on one incorrectly shared Hodge degree**. Then

  R_i E_j(a) = 0 if j<i;
  R_i E_i(a) = a;
  R_i E_j(a) = s_(j−i)(N)·a if j>i,

where s_k(N) is **defined in this convention** by q_*(ξ^(c−1+k)q^*(-)). So the exceptional return matrix T is upper triangular with all diagonal entries 1. Write T=I+U; U is strictly upper triangular and U^(c−1)=0. Its exact inverse over the rational Chow/Hodge module is

  T^(-1) = I − U + U² − … + (−1)^(c−2) U^(c−2).

This is a uniform algebraic proof for every c≥2, not an inference from finite cases. It provides a finite GST multibirth correction law for all shifted exceptional channels. Wolfram exact symbolic audits independently checked determinants=1 and both inverse products=identity for c=2,…,9 using algebraically independent s_k. The all-c geometric comparison remains an explicit semantic obligation in Lean.

## Falsifiable source filter: tautological exceptional words

For a,b≥0 let H be the hyperplane pullback from P^N; h=H|_X. The particular return R=R_1 satisfies

  R(H^a E^b) = 0 when b=0;
  R(H^a E^b) = (−1)^(b+1) h^a s_(b−1)(N) when b≥1.

In particular the complete sequence b=0,…,5 is (0, 1, −s₁, s₂, −s₃, s₄), independent of c≥2; Wolfram checked c=2,…,6. Consequently any source generated **only** by the tautological hyperplane and exceptional divisor returns inside the existing algebraic ring generated by h and normal characteristic classes. Repeatedly amplifying such words cannot guarantee coupling to an arbitrary residual orthogonal to that ring. GST must use additional source geometry (non-split perfect complexes, Koszul/Clifford, genuine incidence sheaves, or geometric moduli) on this rational blowup.

## K3×K3 discriminator: explicit non-tautological source needed

This is a regression test for the arbitrary-X **constructor class**, not a pivot away from the universal quantifiers. Choose a polarized K3 surface S with h²=d≠0 and take X=S×S. Write A=[pt]×S, B=S×[pt], U=h×h, Δ the diagonal, H=h₁+h₂. Then

  H²=d(A+B)+2U, c₂(T_X)=24(A+B),
  P_Δ=Δ−A−B−U/d.

The actual GST K3 intersection Gram from `GSTK3PrimitiveGram.lean` gives the **exact identities**

  ∫_X P_Δ² = 21,    ∫_X P_Δ·H²=0,    ∫_X P_Δ·c₂(T_X)=0.

The independently constructed native reduced tangent-K₀ primitive
  T=16(A+B)−(16/d)U
has `∫ T²=768`, `∫ P_Δ T=0`, so the two-source Gram determinant is **16128**. Wolfram's independent exact calculation reproduced `{21,0,0,0,768,16128}` with d a nonzero rational symbol. Thus a prescribed primitive readout ell(Z)=∫P_Δ·Z vanishes on all degree-two polynomials in H and c(N_{X/P^N}), because the exact tangent-normal identity `c(N)c(T_X)=(1+H)^(N+1)` reduces that graded characteristic sector to the span of H² and c₂(T_X). Consequently every blowup source built ONLY from the ambient hyperplane and exceptional divisor fails to detect this very real algebraic class.

In contrast, `[O_Δ]` is an independently given algebraic perfect-complex source, and the established GST GRR/Gram correction constructs P_Δ with ell(P_Δ)=21. Its exceptional Gysin birth on Bl_X(P^N) is genuine algebraic geometry, and the exact return recovers P_Δ on X. This verifies that **non-tautological sheaf birth**, not a larger power of E, is the relevant geometric difference.

A focused new Lean check is added in `GSTK3PrimitiveGram.lean` as `primitive_diagonal_outside_characteristic_plane`, commit `73f3e7a4dd0aa2fab694cb69113015e9ab181f1e`. Its exact workflow result must be checked at this SHA before calling the addition kernel-verified.

## Uniform noncommutative finite GST exceptional feedback inverse

New existing-module Lean theorem `nilpotent_birth_inverse_two_sided` (commit `36d2e7f9382e296ddac0184d195657e828c5d2a8`) is verified by the revision-matched [Graph V2 Lean CI #39407994946](https://github.com/kyo-oo/HC-PROOF/actions/runs/39407994946). For any unital **not necessarily commutative** ring R, element u and integer c≥0 with u^c=0, the **explicit constructive two-sided correction law** is

  (1+u)(Σ_{k=0}^{c−1}(-u)^k) = (Σ_{k=0}^{c−1}(-u)^k)(1+u) = 1.

The proof uses two finite telescoping identities, checked by Lean induction without assumed inverse, commutativity of source operators, Hodge surjectivity, or a chosen cycle. For the c−1 exceptional return slots the strict upper-triangular shift U is nilpotent, so the theorem constructs the rational-native finite GST inverse to the entire feedback matrix at arbitrary rank, after instantiating the graded endomorphism algebra and its nilpotence. The current Lean theorem verifies the ring-level inverse; geometric nilpotence and exact graded Chow comparison remain separately specified scheme-level inputs. This is a uniform mathematical upgrade over any bounded Gram inversion.

## Exact acceptance condition

Build **one** actual algebraic perfect complex or Chow source W on the blowup Y=Bl_X P^N from original-X equations and GST birth rules such that

  ell_Y(cl_Y(W)) ≠ 0

whenever the specified original-X primitive residual is nonzero. The existing verified Gram-dual native correction and one-center K₀ compiler then apply to R(W) on original X. A genuine counterexample would instead require an exhibited rational Hodge alpha not in canonical cl_X(CH^p(X)_Q), with a proof of that non-membership; absence from any finite GST source family is not such a counterexample.

**Interpretation:** The exact blowup descent and nonzero-preserving readout are mathematical and formal construction progress. They do not by themselves prove universal algebraicity or furnish a Hodge counterexample.
