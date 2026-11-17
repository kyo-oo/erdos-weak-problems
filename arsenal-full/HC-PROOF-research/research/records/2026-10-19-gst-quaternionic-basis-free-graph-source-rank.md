# Mathbox — quaternionic graph full Weil frame and all-rank GST source audit

- **Date:** 2026-10-19 (IST)
- **Kind:** existing-route strengthening, direct proof and adversarial residual-coupling test
- **Program:** all-original-X rational Hodge construction, Gate 3
- **Base checkpoint:** \`bc284f0251376372936812e53e1628e49f933bfe\` on \`research/gpt6-native-point-primitive-span-20261017\`
- **Live mathematical files strengthened:** \`GSTPrimitiveProductTowerStabilization.lean\` and \`GSTUniversalCMArithmeticObstruction.lean\`
- **Exact original acceptance:** given any smooth projective complex original X, any codimension p and any rational Hodge target alpha, construct actual Z in CH^p(X)_Q with canonical Betti class alpha; no target-presupposing rank or canonical-map replacement
- **Evidence:** Lean kernel-verified algebraic laws at revision-matched GitHub Actions: all-rank native source at `42176b063399` (runs `39182871195`, `39182871216`, both success) and full quaternionic four-vector graph rank at `58893ae1d061` (pinned integration run `39183863842`, success). Source geometry independently requires genuine divisor/bundle data, quaternionic scheme endomorphism and graph-to-Betti compatibility. The original universal target is not inferred from these results.

## 1. Previously verified all-rank primitive birth — repaired in a ring with zero divisors

For any commutative rational Chow ring, algebraic classes u,v with u^(m+1)=v^(m+1)=0, put

\[
P_m=\sum_{k=0}^{m}(-1)^k u^{m-k}v^k.
\]

The existing Lean source proof establishes (u+v)P_m=0. The new exact all-rank native intersection identity is

\[
u^m P_m=(-v)^m u^m.
\]

Since (-1)^m is a **unit even in a ring with zero divisors**, u^m v^m nonzero forces P_m nonzero. The first compiler attempts incorrectly used \`mul_ne_zero\` on two nonzero factors, which requires a domain and fails for Chow rings; the corrected proof uses invertible parity multiplication and **does not require no-zero-divisors**.

**Confirmed GH Actions:** \`GST Primitive External Product Birth\` run 39182871195 and \`GST Universal Surface Graph Primitive Augmentation\` run 39182871216, both SUCCESS for \`42176b063399a6b85d8dbf4fdc9204f8a7838737\`.

This proves a valuable source on actual smooth finite covers of products where the two factor divisor powers are geometrically realized and the mixed top volume nonzero. It does not imply arbitrary-X source existence.

## 2. Quaternionic graph — full four-dimensional σ⊕σ̄ independence

On a genuine quaternionic abelian surface B with Q-linear endomorphism operators I,J obeying I²=-1, J²=3, IJ=-JI, let v,w in the +i eigenspace be complex-linearly independent.

The previously verified GST theorem \`quaternionicAntiKGraphSwitchesEigensector\` derives

\[
I(Jv)=-i(Jv),\quad I(Jw)=-i(Jw).
\]

The new theorem \`quaternionicAntiKGraphPreservesTwoIndependentEigendirections\` uses J²=3 to show Jv,Jw remain independent with no extra matrix-determinant hypothesis. The further theorem \`quaternionicAntiKGraphFourVectorWeilFrameIndependent\` proves

\[
\{v,w,Jv,Jw\}\quad\text{is complex-linearly independent}.
\]

**Proof:** set x=av+bw and y=cJv+dJw. If x+y=0, then Ix=ix and Iy=-iy. Applying I yields ix-iy=0, while multiplying x+y=0 by i yields ix+iy=0. Subtract: (-2i)y=0. Since -2i≠0, y=0 and then x=0. Independence of v,w and Jv,Jw forces all a,b,c,d to vanish.

It follows abstractly that the exterior fourfold wedge \(v\wedge w\wedge Jv\wedge Jw\) is nonzero. On original A=B×B, the *actual algebraic codimension-two graph* Γ_J of a genuine quaternionic isogeny would pair with the Weil top form through pullback of H¹. The canonical geometric comparison between this graph's class and the stated H¹ pullback is a separate required theorem: the Lean statement proves the linear-algebra rank for specified I,J, not itself that such I,J occur as the exact Betti action for every original X.

The preexisting repository script \`research/computations/quaternionic_graph_weil_source.py\` computes the exact rational quaternion 4x4 determinant \(-12\) and squared norm \(144\). The basis-free proof now explains **why this determinant cannot vanish** in a genuine quaternionic graph H¹ realization, independent of chosen quaternion basis. It is restricted to the QM geometric family, not universal X.

- **First independent source condition:** actual B with quaternionic multiplication and an algebraic J endomorphism (or integral multiple), plus canonical graph H¹/Betti comparison
- **No free Gram/nonzero condition:** four-vector independence is deduced algebraically from J²=3 and the independence of source σ basis
- **Remaining geometric gate for this route:** instantiate the true Q-isogeny graph with the canonical original-A Weil H⁴ Betti fundamental class, with correct pullback/pushforward variance and scalar normalization

## 3. Falsifiable residual detection test; no implication from nonzero sources to target coupling

On the concrete original fourfold X=(P¹)^4, let a,b,c,d be genuine square-zero divisor classes with \(\int abcd=1\), and set u=a+b, v=c+d, H=u+v.

The newly constructed unseeded class \(P_2=u^2-uv+v^2\) satisfies HP_2=0 and \(P_2^2=12abcd\). A second **actual algebraic primitive source** \(Q=(a-b)(c-d)\) satisfies HQ=0 and \(Q^2=4abcd\), yet

\[
\boxed{P_2Q=0}.
\]

Wolfram exact polynomial reduction modulo the genuine fiber divisor relations \(a^2=b^2=c^2=d^2=0\) returns the triplet (P_2²,P_2Q,Q²)=(12,0,4)abcd. This is not a counterexample to Hodge; Q itself is algebraic. It is a precise counterexample to treating merely nonzero norm of one constructed source as **universal detection of every primitive residual**. Thus the next GST birth must construct a source whose period against the PARTICULAR residual is nonzero.

## 4. Route disposition and next exact implication

- **Proved:** arbitrary-m algebraic ring identities and source nonvanishing (at cited Lean runs); basis-free quaternionic two-vector rank and four-vector rank as abstract complex-linear propositions (GitHub Actions compilation evidence is revision-matched separately).
- **Not supplied by this route:** for every original X and nonzero primitive Hodge residual r, an independent algebraic E in K0(X)_Q with \(Q(r,\operatorname{cl}_X[\operatorname{ch}(\mathcal P_f^K(E))\operatorname{Td}(T_f)]_p)\ne0\).
- **Route stays open:** instantiate actual QM graph H¹/Betti exterior comparison on its correct A to secure a genuinely algebraic Weil source. Then return to generic-original-X incidence/Hilbert or coniveau source construction; do not silently assume the transcendental residual has an algebraic representative.
- **Review:** self-audit of precise hypotheses and external geometric leaves; Lean kernel verification scope separately reported. No assertion of an all-varieties Hodge proof.

