# GST exceptional Chow idempotent and original-X native readout

- **Date:** 2026-10-20 (IST).
- **Research target:** All original smooth projective complex varieties X, all codimensions p, all rational (p,p)-Hodge classes; construct canonical original-X Chow representatives, or an actual rational Hodge counterexample.
- **Branch/base:** `research/gpt6-native-point-primitive-span-20261017`; the parent code had already developed the exceptional return, multibirth and Chern–Segre correction.
- **Code commit:** `0cfa18427061fbbe11b420c591ed3a8963f841e3`.
- **Edited source:** `GSTGraphV2SelfExpandingCosmology.lean`, namespace `NativeGeometryBirth.BlowupRationalHodgeTest`.
- **Exact-revision verification:** Graph V2 CM NM Geometry Upgrade [39407555109](https://github.com/kyo-oo/HC-PROOF/actions/runs/39407555109), **success**; GST Pinned Universal Hodge Geometric Integration [39407555039](https://github.com/kyo-oo/HC-PROOF/actions/runs/39407555039), **success**; both at code commit `0cfa184`.
- **Review:** Mathbox-guided self-audit of the raw theorem hypotheses and Wolfram exact coefficient check; no independent referee.

## Newly constructed native exceptional projector

For any original smooth projective X embedded in P^N with codimension c>=2 and honest blowup Y=Bl_X(P^N), set j:E->Y and q:E->X. The existing GST return from rational Chow sources on Y to actual Chow sources on X is

  R(W) = -q_*(xi^(c-2) j^! W).

Define the genuinely algebraic exceptional birth E_Chow(Z)=j_*(q^*Z) on rational Chow groups and its ambient projector

  P_GST(W) = E_Chow(R(W)).

From the explicit **Chow-level** self-intersection identity and fiber integration

  j^! E_Chow(Z) = -xi*q^*Z,
  q_*(xi^(c-1)q^*Z)=Z,

the formal theorem `exceptional_native_return_left_inverse` proves R E_Chow = id. Consequently

  P_GST(E_Chow Z) = E_Chow Z,     P_GST^2 = P_GST.

The existing abstract typed Lean infrastructure has been strengthened in-place by:

- `exceptionalNativeReturn` — explicit rational linear Chow return;
- `exceptional_native_return_left_inverse` — genuine Chow geometric identity assumptions, no Hodge-to-Chow inverse;
- `exceptionalNativeAmbientProjector` — native algebraic endomorphism of the blowup-world Chow carrier;
- `exceptional_native_ambient_projector_fixed`;
- `exceptional_native_ambient_projector_idempotent`;
- `exceptional_native_ambient_projector_betti` — verifies the stated canonical Betti action `clY(P_GST W) = excGysin(-qReturn(jBetti(clY W)))` when the genuine class-map/Gysin comparisons are supplied.

The proof is uniform in the rational linear carrier and does not require a preselected Chow representative of an arbitrary Hodge target. **Semantic boundary:** the present Lean arguments accept the actual Chow Gysin and Betti comparison laws as explicit typed inputs; they do not create the scheme-level Lean functors or universal source W. This is a verified native Chow-projector theorem under genuine geometric comparison hypotheses, not a new unconditional proof of the full rational Hodge conjecture.

## New independent symbolic geometric discriminator

For the normal bundle N=N_(X/P^N), the Euler and tangent-normal sequences give

  c(N;t)c(T_X;t) = (1+h t)^(N+1),

and hence for the Segre push operations

  s(N;t)=c(T_X;t)/(1+h t)^(N+1).

The exact coefficient identity valid at every k is

  s_k(N) = Sum_(i=0)^k (-1)^(k-i) binomial(N+k-i,k-i) c_i(T_X) h^(k-i).

The stateless Wolfram evaluator independently expanded this series to degree four with symbolic N,h,c1,c2,c3,c4; all **five** coefficient differences were exactly zero. With vanishing positive tangent Chern classes (e.g. an abelian variety), this reduces to the pure hyperplane formula

  s_k(N)=(-1)^k binomial(N+k,k) h^k.

This arithmetic check is not a proof of universal source existence. It gives a falsifiable filter: every source composed solely from ambient hyperplane, exceptional divisor and normal characteristic words returns inside the original-X characteristic-class subring. To couple to a primitive residual annihilating that subring, a truly non-tautological algebraic sheaf/incidence/perfect complex is essential.

The existing K3×K3 GST diagonal perfect-complex construction gives a decisive positive test of that distinction: its primitive diagonal class has squared norm 21 and is orthogonal to H^2 and c2(T_X). Its independently constructed [O_Delta] is a genuine non-tautological native source on that X and its exceptional birth returns to X. This is **not** yet a generator for arbitrary X; see `2026-10-20-gst-exceptional-ambient-original-x-return.md`.

## Follow-on constructor contract

For each original X and prescribed nonzero primitive rational Hodge residual r, construct a **new actual algebraic** W in CH^(p+1)(Bl_X P^N)_Q from independent X-specific geometric data, with

  Q(r, cl_X R(W)) != 0.

Then the verified GST Gram correction and pure K0 one-center compiler can proceed on X; the new P_GST isolates the canonically returned native exceptional summand. The matching original-X algebraicity obligation cannot be replaced by an abstract Hodge-to-Chow inverse, a prescribed target preimage, or an uninstantiated cycle map. For a counterexample, prove a specific rational Hodge class absent from the complete Chow-image, not merely an enumerated source family.

- **Attempt outcome:** proved as a typed geometric-interface projector with exact-revision Lean success; exact finite Wolfram normal-Segre coefficients validated; no arbitrary-X detector or counterexample is claimed.
- **Route disposition:** open; progress is the Chow-idempotent and normal-source filter; first unresolved implication is independent non-tautological W with nonzero prescribed residual coupling.
