# GST arbitrary-X Hilbert-incidence algebraic source and separable Euler reconstruction

- **Date:** 2026-10-21 IST.
- **Kind:** executed mathematics-first derivation and self-audit.
- **Program/route:** full rational Hodge conjecture, arbitrary original-X geometric source; new Hilbert-scheme incidence route, distinct from the prior doubled diagonal projection.
- **Base revision:** `055b4687027eba14912d8092cf52eb787140e3e5`, active branch `research/gpt6-native-point-primitive-span-20261017`.
- **Primary derivation:** [full LaTeX proof, 800+ lines](../derivations/GST_arbitrary_X_Hilbert_incidence_primitive_Euler_source_2026-10-21.tex).
- **Input and trust:** Standard blowup, conormal filtration, rational algebraic Chern character, Todd/Adams GRR and topological K Chern character. The arbitrary-X blowup-world canonical Chern--Segre return and its normalizer are taken from previously recorded GST derivations, not re-proved scheme-theoretically in this standalone note. No Lean code was edited; this is the user-requested LaTeX-first round.

## New exact mathematical construction

For every smooth projective complex d-fold X, the actual length-two Hilbert pointed incidence is the blowup B=Bl_Delta(X×X). Its proper algebraic K0 source is F_m=u_!O_B(-mE). Rees algebra and the diagonal normal-conormal filtration give the complete actual K0 identity

`F_m = chi(O_X) O_X - sum_{k=0}^{m-1} Sym^k(Omega_X^1)`

for all m≥0. This is not a target-preimage input. Rational Chern-character generating function and uniform closed expressions through degree two are proved in the LaTeX derivation.

On every arbitrary original smooth projective complex fourfold, W1=F2-F1=-Omega_X and W2=F3-F2=-Sym^2(Omega_X) have true Todd-corrected algebraic codimension-two classes

`Z1=(-1/3)c1(T_X)^2+(2/3)c2(T_X)`,
`Z2=(-11/6)c1(T_X)^2+(31/6)c2(T_X)`.

For any rational (2,2) Hodge r, let a=int r c1², b=int r c2 and delta_i=int r Z_i. The exact geometric period matrix M=[[-1/3,2/3],[-11/6,31/6]] has determinant -1/2 and inverse [[-31/3,4/3],[-11/3,2/3]]. The `ACTUAL` original-X Chow source Z_r=delta_1 Z1+delta_2 Z2 has period int r Z_r=delta_1²+delta_2², strictly positive for (a,b)≠(0,0).

### Entire even-dimensional middle sector

For every even-dimensional X of dimension 2p, define Z_m=[ch(F_m)td(T_X)]_p in actual CH^p(X)_Q, 0≤m≤3p; set d_m=(-1)^p int r cl(Z_m). The actual original-X cycle Z_r=sum d_m Z_m has signed Hodge coupling Q(r,Z_r)=sum d_m². Actual finite-Adams purified algebraic K0 classes C_m give a `factorable` algebraic two-ended kernel K=sum C_m^vee box C_m and one-sided algebraic source C_r=sum d_m C_m, with BOTH rational Euler indices equal to sum d_m². All p parity signs are proved algebraically. The full exceptional Hilbert-twist Euler sequence is a polynomial in m of degree ≤3p, so checking 3p+1 twists is complete for that family.

### Return to an arbitrary-dimensional original X

For Y=Bl_X(P^(2M)), M≥dim(X)+1, choose the established pure-middle GST topological packet A_alpha^Y. Apply the same independently constructed Hilbert sources on the actual Y, choose d_m^Y=chi_Y(A_alpha^Y,C_m^Y), and build E_alpha^Y=sum d_m^Y C_m^Y. GST's actual algebraic Chern--Segre return gives a rational Chow cycle Z_alpha,Hilb in CH^(dim X-p)(X)_Q, satisfying

`int_X alpha cl(Z_alpha,Hilb)=(-1)^(M+1) sum_{m=0}^{3M}(d_m^Y)^2`.

It is a **complementary-degree detector**, not automatically the codimension-p representative required by the conjecture. The formula is a genuine original-X cycle construction whenever the computed source period is nonzero.

## Computation and audit

- Stateless Wolfram exact symbolic summations obtained all surface m-polynomials through ch2 and the fourfold 2×2 matrix; det=-1/2, inverse exact, gram matrix leading principal minor 125/36 and determinant 1/4 (positive definite).
- Separate exact weak-composition enumeration checked rank/ch1/ch2 against the splitting-principle formula for d=1..5 and k=0..4: **25 pairs / 75 identities true**.
- Parity signs of the separable two-ended Euler construction checked symbolically for p=1..8 (all pass), backed by a uniform sign proof.
- Rational test a=3,b=5 gave d1=7/3, d2=61/3, squared energy 3770/9; not alleged to be a realized target on a named variety.
- The uniform proofs are geometric/characteristic-class derivations in LaTeX. Not kernel-verified Lean and not independently refereed.
- **Adversarial check:** a residual annihilating the entire algebraic Chow image necessarily has zero pairing with every Hilbert source constructed here. Nonzero positivity of the prior GST non-separable diagonal kernel is NOT substituted for these separately measured periods. The exact all-X spanning claim is not established.

## Outcome and decision

**Evidence label:** proved mathematical identities within the standard geometrical input framework, exact Wolfram algebra cross-check, self-reviewed only. **Original universal goal:** not achieved. **Route state:** open; the explicit source and one-sided detector are valid in the characteristic/Hilbert-incidence reachable sector, including a finite test over all exceptional twist powers. New independent non-characteristic algebraic geometry is required to address Hodge residuals orthogonal to this sector, not another formal renaming of the same kernel.

No global internet search, no subagents, no local Lean or altered Lean files. This source-first work was saved directly as committed LaTeX, as explicitly requested.
