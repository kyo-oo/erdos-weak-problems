# Mathbox: direct alpha-indexed GST algebraic curvature source equations, exact original-X Chow return, and circular-support correction

**Date:** 2026-10-23 IST. **Original branch HEAD:** `ea09c78364bc94c1e46df609b51922a21299f914`. **Owner's immutable output contract:** for ANY smooth projective complex original X, codimension p and prescribed rational Hodge alpha, CONSTRUCT an actual `Z_alpha∈CH^p(X)_Q` with canonical rational Betti `cl_X^can(Z_alpha)=alpha`. **Research workflows loaded:** Mathbox research-program, research-attempt, proof-audit, computation-audit; evidence-model, program-protocol and proof-audit checklists. This is a self-review (no external referee), not a purported Lean or journal certificate. No public internet and no local Lean compilation.

## 1. Exact discovered dependency error in the previous source algebra

[Complete universally quantified Gysin support theorem and explicit proof](../derivations/GST_gysin_support_is_exact_chow_image_mathbox_audit_2026_10_23.tex), created commit `4c8e9d41be39a826ac1f1f8936966615bca11b0f` and typing correction `6ca5e2a7dce173fbac702deeb0e84aee33327de9`. For **every original smooth projective X,p≥1**, the image of ALL proper Gysin maps `f_*:H^2(Y,Q)∩H^(1,1)(Y)→H^(2p)(X,Q)` from smooth projective Y of complex dimension d-p+1 equals EXACTLY the genuine canonical original-X Chow cycle-class image in codimension p. The nontrivial converse is explicit: for ANY original-X codim-p irreducible cycle Z, resolve `ν:Ztilde→Z`, set `Y=Ztilde×P1` and `f:Y→X` factoring projection to Ztilde and its inclusion into X, then `β=pr_P1^* c1(O_P1(1))` is an actual integral (1,1) class with `f_*β=cl_X^can[Z]`, via projective-line fiber integration and proper resolution pushforward. The forward direction uses Lefschetz (1,1) and canonical Chow/Betti Gysin comparison.

Therefore the previously claimed 'independently verifiable geometric support hypothesis' in the existing [Todd--Fitting mathematical source](../derivations/GST_alpha_directed_todd_fitting_source_2026_10_23.tex) is **equivalent** to algebraicity of the prescribed alpha when unrestricted f are allowed. Its GRR formulas are valid SOURCE CONVERSIONS, not a new independent birth theorem. The original LaTeX was corrected IN PLACE in commit `eb5d75d458b73e50aeea98267b6e88a77b2f9984`, preserving genuine prior mathematics but eliminating the circular 'support is weaker input' implication. This is not evidence against Hodge/GST.

## 2. Constructive DIFFERENT source mechanism: direct alpha-dependent polynomial curvature system

[New complete algebraic source and proof](../derivations/GST_direct_alpha_finite_polynomial_curvature_source_equations_2026_10_23.tex), first commit `d0ad0876f75952ec0e69b81f2499b2349472abfa`, rational denominator repair `7580bce09fb3dd998ec0bdfe6548102a10499b32`, idempotent differential-source rigidity and exact extremal case construction later in the SAME LaTeX source.

On the ACTUAL affine Jouanolou GST fold q:J→X, ANY rational Betti alpha (Hodge or otherwise) has an algebraic de Rham class represented by a globally closed algebraic 2p-form eta_alpha, using Grothendieck algebraic de Rham comparison and J AFFINE. Fix the canonical Tate normalization so ch_p^dR of a genuine algebraic bundle corresponds to its rational Betti Chern character.

Form ACTUAL finite regular matrix idempotents P+,P- with P±²=P±, an actual algebraic (2p−1)-form B, and an integer **mu>0** satisfying the EXACT alpha-indexed equation:

`Omega_p(P+)-Omega_p(P-)-mu eta_alpha = dB,quad Omega_p(P)=Tr(P(dP)^(2p))/p!`.

Any such solution constructs an ACTUAL original-X rational Chow cycle

`Z_alpha=(1/mu)(q*)^-1(ch_p^CH(im P+)-ch_p^CH(im P-))`,

with TRUE canonical rational Betti class exactly alpha. This is not a fictional given Chow witness or untyped operator: both projectors define true algebraic finite projective modules, the Chern character is actual algebraic Chow, and exact algebraic de Rham comparison checks the canonical rational class.

**Finite POLYNOMIAL scheme realization:** compactify J as the complement D(s) of its actual ample incidence divisor in the smooth projective barJ. Every regular projector entry, the input eta_alpha and the unknown regular transgression B have some finite pole order along D. At any finite matrix size/pole/form bound and fixed positive mu, write P=A/s^k and B with finitely many coefficients of algebraic twisted differential forms. After multiplying through by a sufficient power of s, P²=P and the target curvature-exactness equation give actual FINITELY MANY POLYNOMIAL coefficient equations. Their solutions define real finite-type complex algebraic parameter schemes. Running through all bounds gives the countable filtered source system. Its solution NONEMPTY iff alpha is in the original-X rational Chow Betti image: reverse direction follows by rational algebraic K0↔Chow, actual finite idempotents on affine J, and AFFINE algebraic de Rham exactness. This converse audits completeness, not an input to the forward algorithm. A theorem that every Hodge alpha yields a finite solution would finish the target; no such theorem was derived by the existing GST laws merely because eta_alpha is closed or has Hodge type.

**UNCONDITIONAL full sectors:** when p=1, alpha type (1,1) yields actual algebraic L by Lefschetz (1,1)/GAGA, with a finite incidence idempotent and algebraic B supplying a genuine solution. When p=d, connected smooth projective X has one-dimensional rational top Betti cohomology, explicitly generated by the class of ANY actual closed complex point; its coefficient is computed from alpha and source encoded by finite algebraic K0/projector algebra and an algebraic B. These sectors produce true Chow cycles directly from alpha, not from an assumed higher-codimension algebraicity assertion.

## 3. Derived nonabelian first-order algebraic obstruction

For any rational algebra R and idempotent P, a first-order dual-number idempotent P+eps Q satisfies `PQ+QP=Q` EXACTLY, and hence `PQP=0`, `(I−P)Q(I−P)=0`, and `Q=[[Q,P],P]`. Thus all first-order algebraic projector deformations are conjugations by an invertible dual-number matrix, and cannot change the algebraic K0/Chern Betti source; a truly NEW source direction must come from a different algebraic projective-module class, not from tangent perturbation near one already-known idempotent. This theorem is universal in affine GST spatial dimension; it does NOT claim no new class exists.

## 4. Exact actual Wolfram tests, source and outcome

[Executable source committed to branch](../computations/gst_direct_alpha_deRham_curvature_certificate_2026_10_23.wl) at `ddda6783bc90a1e0360a4c5874ea6dc4b306d981`, fetched blob `c011001a811e684e860def30e07b0df5eb29028b` and executed verbatim:

- True projective incidence rank-one algebraic idempotent `P=[[1,v],[u,uv]]/(1+uv)` obeys P²=P, trace 1, and its exact Chern--Weil curvature coefficient is `Tr[P(P_u P_v−P_v P_u)] = −1/(1+uv)²` for du∧dv. All exact checks TRUE.
- On actual Gr(2,5), `ch_2(S)=h²/2−s₂`, `ch_2(O(1))=h²/2`, so `5 ch_2(S)−ch_2(O(1))=5((2/5)h²−s₂)`; exact zero transgression test with **mu=5** and genuine Pluecker incidence algebraic projectors. Exact symbolic TRUE.
- **54/54** deterministic rational matrix-rank pairs m=1..9,r=0..m satisfy idempotent linearization and double-commutator conjugacy; no failures. General theorem is the algebraic calculation, not inference from these 54 cases.

## 5. Audit and next mathematical dependency, without repeating prior misdirection

**Evidence 'proved as written' under standard established algebraic de Rham/K0/Chow comparison:** full real scheme equation/source-return theorem, finite stage polynomial equations, equivalence of unrestricted support to Chow image, extremal case actual solutions, first-order conjugacy theorem. **Finite computation only:** specific 54 matrix checks and exact rank-one/Schubert characteristic examples. **NOT derived:** for arbitrary primitive rational (p,p) class alpha on arbitrary original X with 1<p<d, a universal existence theorem for an ACTUAL solution of the direct alpha-indexed finite polynomial algebraic projector system. This is the exact source-birth algebra itself, not an external 'geometric support' assumption. The new equations provide an explicit algebraic construction-and-verification interface but their automatic solvability is equivalent to the target conjecture, not an additional trivial lemma.

**No Lean source was modified in this attempt**, because the actual differential forms, algebraic de Rham comparison, affine scheme finite-pole modules and canonical rational Chow comparison are not kernel-formalized by the repo's present Mathlib signatures. No GitHub Actions result is attributed to this new theorem. No external research web searched.
