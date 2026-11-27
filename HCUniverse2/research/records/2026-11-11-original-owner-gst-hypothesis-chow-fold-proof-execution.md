# GST original-branch geometric hypothesis execution — 11 November 2026

## Immutable universal original-X target

For every smooth projective complex X, every p, and every prescribed rational Hodge alpha, produce a **new actual algebraic cycle on X** with its **canonical** rational Betti class equal to alpha, not a synthetic wave signal, arbitrary abstract cycleClass map, or a user-supplied Chow inverse. This is the unsolved original universal GST hypothesis. The exact conditional implication remains in GSTHodgeSingleHypothesisConditional.lean.

## Git integration actually performed

Original owner branch: `research/gpt6-native-point-primitive-span-20261017`.
Starting original HEAD: `8d85045980acc09fe6190f7b938bf6234e27f41b`.
All previously committed advanced-source math was proved to be a STRICT fast-forward descendant of this HEAD, 205 commits ahead and zero behind, and then moved to the original branch via a nonforced, expected-SHA checked fast-forward to `a6c4915844789401fc8bef903cc99c2989278ff8`.
This preserved ALL original history and ALL advanced commits and was verified by rereading the OG HEAD. Research has continued directly on that ORIGINAL branch since the transfer.

## New unconditional genuine original-X Chow construction

Mathematical source: `research/derivations/GST_original_X_divisor_curve_hodge_cyclic_chow_correspondence_2026_11_11.tex`.

1. For arbitrary original smooth connected projective X dim d≥2, choose actual rational divisors D_i forming a basis of NS(X)_Q, ample h, and invert the NONDEGENERATE Hodge-index intersection matrix G_ij=deg(D_i D_j h^{d−2}).
2. In every codimension 1≤p≤d−1, ACTUAL Chow cycles Z_i=D_i h^{p−1} and Y_i=sum_j (G⁻¹)_ij D_j h^{d−p−1} satisfy deg(Y_i Z_j)=δ_ij in CH intersection theory.
3. ACTUAL codim-d Chow correspondences E_ij=pr1*Y_i · pr2*Z_j in CH^d(X×X)_Q satisfy E_ij∘E_kℓ=δ_iℓ E_kj. This is a GENUINE Chow product/pushforward equation, not merely a cohomology operator: it uses the middle-factor degree of an actual 0-cycle. Consequently Π_p=sum_i E_ii and R_p=Δ_X−Π_p are Chow-idempotents, and Γ_p=sum_i E_i,i+1modρ is a genuine rational cyclic-fold self-correspondence on the algebraic divisor-Lefschetz sector.
4. For **EVERY prescribed** rational Hodge alpha in W_p(X), the explicit newly constructed original-X cycle Z_(alpha,Lef)=sum_i (int_X alpha∪cl(Y_i))Z_i has canonical class cl(Z_(alpha,Lef))=Π_p^B alpha. Its residual alpha−cl(Z_(alpha,Lef)) is orthogonal to every explicitly constructed algebraic Y_i. No unknown class preimage is assumed.
5. For p=1 and p=d−1, Lefschetz (1,1) + hard Lefschetz give W_p=span_Q{cl(Z_i)}. Thus Γ_p and Z_0 provide the actual full single-fold algebraic orbit geometry in these weights. In particular all weights on any smooth connected projective X dim≤3 are covered by ordinary Chow geometry. This is CLASSICAL-INPUT restricted progress; no claim of the full arbitrary-dimensional Hodge conjecture.
6. The geometric detector ℓ(v)=int_X v∪cl(Y_(ρ−1)) has exact Hankel matrix δ_(i+j,ρ−1) on the cyclic divisor-Lefschetz sector and determinant (−1)^(ρ(ρ−1)/2).
7. The owner-original two-birth seed Z0+N Z0 has an EXACT parity obstruction in even ρ: its orbit loses one dimension. The repaired TRUE algebraic seed Z0+2N Z0 is cyclic for every positive ρ. Formula det K(new)= [1−(−2)^ρ]det K(base); the finite inverse is (I+2T)Σ_(k<ρ)(−2T)^k=[1−(−2)^ρ]I.
8. The full REAL Chow matrix-unit algebra map Φ:Mat_ρ(Q)→CH^d(X×X)_Q, A↦Σ_i,j A_(j,i) E_ij, is INJECTIVE and multiplicative with image identity Π_p. For ρ(X)≥12, Φ realizes the owner's true original 12-cell U,J,M,[J,M], all their rational curvature words, and true original seed on an ACTUAL independent 12-dim algebraic Lefschetz sector for every p. At a=b=1 the 12-cycle Krylov determinant equals −445265540949 on that genuine original-X sector, exactly as in prior native computation. The full Hodge space need NOT equal that 12-dim sector.

## Lean implementation and CI status

- `GSTOriginalXDivisorCurveCyclicChowFold.lean` contains exact rational source intersection readouts, canonical class naturality, cycle source action and orbit span equality. GitHub Actions `43057256805` SUCCESS at SHA `19becef52299d041f62b0c05ec750e3a0152a029`, no sorryAx.
- `GSTOriginalXAllWeightsLefschetzResidual.lean`: source projector, Betti projector, both idempotents, actual prescribed-alpha selected-cycle class, residual detection-zero theorem. Originally CI found two definitional-normalization errors; repaired on OG at `37130f1a84ea2b113b2fee278ba9e8418f03f62b`. Verify **current** CI success before promoting this file's kernel status.
- `GSTOriginalXWaveChowMatrixCompiler.lean`: arbitrary rational source matrix compiled from actual dual-intersection source operators, matching Betti map, source-column action, source-image stability. It is an abstract module theorem using the corresponding **independently proved Chow construction in the TeX**; it does NOT create real Chow objects directly inside Mathlib. Exact CI on OG should validate this new file.
- `research/computations/GST_original_X_cyclic_seed_parity_resonance_20261111.wl` executed from committed content with Wolfram and returned `allPassed -> True` for ranks1–12; universal proof is an exact rational geometric-series identity independent of finite tests.
- The prior advanced source CI error was exactly missing `NoZeroDivisors (ZMod 11/19)` synthesis in multiplication of nonzero polynomial residues; repaired on OG by local explicit `Fact (Nat.Prime 11)` and `Fact (Nat.Prime 19)` instances. Check exact current integrated CI result; do not claim green from older incomplete logs.

## Genuine geometric boundary (one quantified statement)

**Not established:** for an arbitrary original X of dimension≥4 and an arbitrary prescribed higher-middle primitive rational Hodge class alpha_res, an algebraic original-X cycle Z_res with cl(Z_res)=alpha_res. The new exact Chow projector separates and constructs all divisor-Lefschetz components but cannot force this residual to vanish. The finite-fiber `RealizedFiniteClosedCorrespondence` Lean datatype also excludes ordinary product correspondences with positive-dimensional left fibers; the named `NativeGSTSingleFoldOrbitLaw` in that restricted formal system cannot yet be instantiated by these genuine full Chow cycles without a distinct full refined-Chow correspondence API.

No Hodge surjectivity hypothesis is hidden in any new source proof. Do not say the universal GST hypothesis or Hodge conjecture has been proved.
