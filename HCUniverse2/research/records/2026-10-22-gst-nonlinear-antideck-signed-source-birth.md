# GST nonlinear anti-deck causal source birth — signed component Chow extraction

- **Date:** 2026-10-22 IST
- **Kind:** Mathbox sustained-research route + one substantive research-attempt + adversarial proof-audit self-review + computation audit
- **Original target:** For every smooth projective complex original X, every p and every rational (p,p) Hodge alpha, construct actual Z_alpha in CH^p(X)_Q with canonical rational Betti class alpha, without an Hodge-to-Chow witness input.
- **Base checkpoint:** `442359b0eaa3021fac40eb17fcce510838e09788` on `research/gpt6-native-point-primitive-span-20261017`.
- **Nearest prior attempted operation:** The projective and punctured Hopf/Gysin causal folds produced true Chow returns but no independently detecting first-missing source. The old double-cover route gave anti-deck algebraic classes with linear pushforward zero. This attempt multiplies TWO anti-invariant divisor sources before the genuine original-X pushforward.
- **Main evidence status:** Uniform algebraic geometry derivation self-reviewed; exact Wolfram arithmetic checked; an additional signed-period identity inserted in the *existing* `GSTPolarizedHodgeResidualEnergy.lean` at source commit `597d4aae439472e993aedab4258f88f9d73387ac`. Its initial Lean CI `39823487928` failed on an accidental nested comment token (`+/-2`) and a solved-goal tactic; both were repaired by `ec9b81b8ce240ae6de65622baa4caa04c9fa2608`, with follow-up CI `39824209398`, which exposed a conditional-scalar simplification mismatch. That was repaired at `70f70242e25c896f76a78d39e5786c338dc83c9a`; revision-specific CI `39824757535` exposed the remaining rational scalar-action normalization in the first map-sum step. Repaired at `925308aa94299eaacb71d29cad65670e7a05d041`; targeted [CI run 39825251419](https://github.com/kyo-oo/HC-PROOF/actions/runs/39825251419) completed **SUCCESS** at the exact Lean source SHA `925308aa94299eaacb71d29cad65670e7a05d041`. The workflow compiled the existing GSTPolarizedHodgeResidualEnergy module and its source graph, ran #print axioms and its no-sorryAx log gate, and reported LEAN PASSED.
- **Proof artifact:** [Full LaTeX mathematical derivation](../derivations/GST_nonlinear_antideck_chow_source_birth_2026-10-22.tex), source created at commit `33fe2283fdbe22a9df042a4bbbc44ed32f7ae68a`, enhanced target-directed at `5f658b5d6df894b2a4266f44f74eef7c65e9d4e9`.
- **Computation artifact:** [Fetched/actually re-executed Wolfram script](../computations/gst_antideck_signed_chow_birth_2026_10_22.wl), source blob `4f2687f8add4ec8470313fc31c756296010e97f1`.

## Nonlinear all-original-X geometric source

Given any smooth projective original X and two integral effective Cartier divisors W1,W2 with a proper **reduced** intersection C=union_j C_j in codimension two, choose any signs epsilon_j=±1. The conductor ideal of the normalization of C, Serre global generation and large-twist restriction surjectivity construct global algebraic sections A1,A2 of some ample L and a branch F of L^2 such that F|Wi=Ai^2 and A2=epsilon_j A1 at the generic point of C_j. Take the true degree-two algebraic cover t^2=F; normalize, then resolve equivariantly to smooth projective Y with proper f:Y→X. The two generically split divisors above each Wi define actual anti-invariant Chow divisors Δi.

The **true original-X Chow intersection law** is

`f_*(Δ1·Δ2)=2 Σ_j epsilon_j [C_j] ∈ CH²(X)_Q`,

not just a numerical period identity. Individual f_*Δi=0, yet their product is invariant. Exceptional intersection components on the resolution cannot change the codimension-two coefficient because all components of its original-X support lie in C and the finite cover is étale over the generic points of every C_j.

For one selected component C_j, choose sign + on it and - on all others:

`[C_j]= (1/4) f_*(Δ1·Δ2) + (1/2) [W1]·[W2]` in **actual CH²(X)_Q**.

This furnishes a real non-linear self-expanding-world source operator. Using standard high-degree CI component cofinality, signed covers produce all *already algebraic* codimension-two Chow generators on arbitrary original X, and a smooth resolved codim-(p-2) slicing world similarly returns arbitrary actual codimension-p algebraic Chow generators for p>2.

## Exact positive original-X primitive example

On the actual smooth quadric Q^4: Q=x0*y0+x1*y1+x2*y2=0; W1=(y1=0), W2=(y2=0); intersection C=P_A∪P_B (two actual P² components). The explicit degree-two branch is

`F=(x0+y0)^2+4*x1*y1=(x0-y0)^2-4*x2*y2` modulo the quadric relation.

On P_A (x0=0) the relative sign is -1; on P_B (y0=0) it is +1. Thus

`f_*(Δ1·Δ2)=2([P_B]-[P_A])`.

The original-X primitive `r=[P_A]-[P_B]` has true h²-pairing 0, square 2; the constructed signed-push output has square 8 and is not hyperplane-only. This is genuine new nonlinear anti-channel **original-X algebraic source geometry**, not an abstract native placeholder. Singularities of the auxiliary branch are handled by genuine equivariant projective resolution.

## Target-sensitive exact sign optimization

For d>=4 and any rational primitive Hodge residual r on the original X, let `a_j=∫_X r · cl(C_j) · h^(d-4)`. A single sign-controlled cover with eps_j=+1 for a_j>=0 and -1 otherwise yields a true source of coupling

`Q(r,f_*(Δ1·Δ2)) = 2 Σ_j |a_j|`.

It is the EXACT maximum among the 2^m signs. The sign law does not use an algebraic preimage of r; only the actual rational intersection readouts with independently constructed geometric components. The existing `GSTPolarizedHodgeResidualEnergy.lean` was surgically strengthened with `signedAntideckPeriodSource` and `signedAntideckPeriodSource_pairing`, checking the scalar form of this optimizer. This is the typed GST residual-to-source interface, not a Lean formalization of the equivariant scheme geometry.

**Execution evidence:** fetched Wolfram script re-executed cleanly and returned `branchCompatibility=True`, `componentSignsCorrect=True`, signed sheet coefficients {-2,+2}, 510/510 finite sign patterns, 36/36 component extractors, 780/780 exhaustive rational target optimizers, four Z2-squared cubic-character cases and seven odd single-deck parity cases, true quadric primitive square 2, signed source square 8 and maximal quadric coupling 4. The later Wolfram addition verifies the **complete original-Q4 rational Hodge target-to-Chow compiler**: in genuine basis h²,S with intersection Gram diag(2,8), the constructed original Chow cycle with coefficients (alpha·h²)/2 and (alpha·S)/8 has the canonical target class for every rational middle Hodge alpha; `hodgeCompilerExact=True`. The original 510-case loop was found by computation audit to compare an expression to an identical expression (a tautology), so it was replaced by a genuine independent two-sheet intersection enumerator at commit `2f4cd2b6aeb0b0fa58943707689b846d33fb6ba3`. The fetched corrected source was re-executed and all cases passed. These finite assertions now independently cross-check signs and rational normalization; the all-X statement is supported by the separately written scheme argument.

## Complete checked codimension-two Hodge source assembly on one original variety

A genuinely complete end-to-end rational Hodge representative on original smooth quadric Q4 was added to the LaTeX derivation at commit `af527bb1912473589879d78cb8072f3b3ff9abc9`: for each α∈Hdg²(Q4)_Q, set `S=f_*(Δ1·Δ2)`, then `Zα=((α·h²)/2) h² + ((α·S)/8) S ∈ CH²(Q4)_Q`. Since middle H4(Q4)_Q is rank two with basis h²,S and true Gram diag(2,8), cl_can(Zα)=α without any selected Chow preimage of α. Wolfram symbolic algebra verified exactness. This is an unconditional original-X source theorem for that fourfold test, not a claim for arbitrary X.

## Higher-arity non-linear causal extension

A separate all-finite-two-group character theorem has now been proved in the same derivation. For an elementary 2-group G acting on a smooth projective world Y, and genuine algebraic Chow sources Z_i with true characters chi_i, f_*(product_i Z_i)=0 whenever product_i chi_i is nontrivial. Trivial product character is necessary for a nonvanishing original-X return, but not sufficient. A single involution forbids odd products of anti-divisors; for G=(Z/2)^2, the three nontrivial characters satisfy chi_a chi_b chi_(a+b)=1, opening a genuine cubic invariant geometric channel once three independently algebraic eigen-sources are realized. This is a distinct higher-arity mechanism, not a claim that an arbitrary-X rank-three source already exists. Exact Wolfram verified all 4 G character cases and seven odd-parity powers.

## Adversarial Mathbox proof audit and limitations

- **Passed (mathematics-first):** actual algebraic double cover from conductor/Serre interpolation; true anti-invariant divisors after equivariant resolution; local étale multiplicity one; actual CH² equality by proper pushforward; canonical Betti naturality; explicit Q4 branch; rational sign maximization.
- **Not claimed as Lean-kernel proof:** scheme-theoretic conductor selection, normalization, equivariant resolution, and actual canonical Chow comparison; the signed-period Lean declaration verifies its finite rational algebraic shadow only.
- **First unresolved implication:** show that for **each** nonzero primitive rational Hodge residual on **each arbitrary original X**, at least one real reduced incidence component C_j has a nonzero canonical period. The theorem creates all existing algebraic source directions, but does not independently establish that those directions span the rational Hodge fiber.
- **Anti-circularity:** Full source cofinality is stated for actual existing Chow generators. It is not promoted to `EveryHodgeClassIsRationalAlgebraic`. Finite sign optimization returns zero when all genuine component periods vanish. A positive self-pairing of an unrelated born source does not imply coupling with every possible Hodge residual.
- **Route disposition:** nonlinear anticharacter-source construction succeeded as a true all-X scheme-level Chow source birth; target-sensitive universal residual detection remains an active research continuation, not closed by this scoped route.

**Exact research continuation:** test whether a genuinely non-incidence *scheme-specific* GST geometric operator (coherent-sheaf moduli / deformation algebraization / non-separable branched source) forces nonzero original-X target pairing beyond the algebraic span already enumerated. Such a forcing argument must not restate native surjectivity or merely add more finite signed words.
