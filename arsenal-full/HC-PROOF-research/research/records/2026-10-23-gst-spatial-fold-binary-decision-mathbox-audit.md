# Mathbox research attempt — exact spatial fold binary proof/counterexample rule

**Current task:** Respect the owner's exact proposed experimental rule without replacing it by a projective-fold Chow-defect criterion. Start from dimensionless General Space, vary actual topology, emergent dimension N and complex-geometry realizations, and attempt to derive either a counterexample or proof of the universal rational Hodge conjecture from presence/absence of a Hodge break.

**Research revision:** Base `4f5e6a84f1769e0aae3baa3963db202ba8c2252e` on `research/gpt6-native-point-primitive-span-20261017`. Source inspected: AGENTS.md, ACTIVE_HODGE_PROOF_PLAN.md, the 2026-10-23 GST Hodge causal graph/spatial whole-world derivations and existing GSTGradedWorldAlgebra.lean plus GSTGraphV2UnboundedHigherCausality.lean.

**Protocol used:** Mathbox sustained research-program, geometry-first research-attempt, focused adversarial proof audit, computation audit; Wolfram exact symbolic execution. There was no separately exposed Mathbox API action in the connected tool inventory; do not claim a standalone Mathbox engine computation was run. No internet/public literature accessed.

## Actual experiment and three independent geometric routes

**Route A — Smooth projective geometric Hodge-type break.** For each N>=2, let k=N-2. Realize one marked General Space world in two actual smooth projective shapes Y0=E_i × E_i × CP^k and Y1=E_i × E_(2i) × CP^k. These have the SAME underlying marked real torus topology and SAME whole Hodge polynomial `(1+u)^2(1+v)^2 Sum[(uv)^j,j=0..k]`, hence pure Hodge structures in all degrees. The single marked integral topological class beta=(dx1-dx2) wedge (dy1-dy2) cup h^k satisfies `beta wedge dz1 wedge dz2 wedge h^k=(sigma-tau) volume cup h^k`. Its rational (k+1,k+1) Hodge type HOLDS on Y0 and FAILS on Y1. At Y0 beta is the true diagonal algebraic cycle times a CP^k point. At Y1 beta ceases to be a Hodge class. Nevertheless the rational Hodge conjecture holds in ALL codimensions on BOTH Y0 and Y1 at every N, because a smooth projective surface satisfies Hodge in codim 0,1,2 (Lefschetz (1,1) for divisors) and the CP^k projective-bundle Chow/Hodge formulas transport that property.

**Exact arbitrary-original-X strengthening:** For every nonempty original smooth projective complex X, product with X preserves this type-breaking phenomenon via the H^0(X) Kunneth summand, and the aligned beta has an actual X × diagonal × point algebraic representative. This is a universal geometric fold experiment on original X; it does NOT claim a universal Hodge conjecture proof on arbitrary original X.

**Route B — Actual topology purity break.** Identify two different points on an elliptic curve to form an honest nodal projective curve C. For each emergent dimension N>=1, Z=C×CP^(N-1) is projective, singular, and satisfies Gr^W_0 H^1(Z,Q)=Q(0), Gr^W_1 H^1(Z,Q)=H^1(E,Q). The full purity predicate breaks, but output is singular, not an admissible smooth projective Hodge conjecture counterexample. This is real geometric topology, not an abstract model.

**Route C — Unbroken full Hodge purity.** Full cohomological purity is automatic for EVERY smooth projective complex variety by Hodge decomposition, in every complex dimension. Thus observing this unbroken property on every admissible smooth-projective fold is not a new theorem of canonical Chow representability. To deduce the universal rational Hodge conjecture from purity alone would require proving precisely the missing implication as a new theorem; pure-Hodge survival is not already a substitute for this.

## Decisive mathematical outcome

The owner's two-branch decision rule has a **false-positive negative verdict in ACTUAL smooth projective geometry in every dimension N>=2**, not just an abstract algebraic-source toy model. Marked Hodge-type breaking can happen while the rational Hodge conjecture is KNOWN TRUE on all participating geometries. A genuine whole-purity break can be produced by topology folding only after leaving the smooth-projective scope in this experiment. The universally unbroken full-purity branch does not decide algebraicity without an additional independent geometric law, because purity itself is already a theorem. This refutes the **decision rule as formulated**, NOT the Hodge conjecture and NOT the GST dimensionless ontology.

**Exact proof artifact:** [GST all-N spatial fold mathematical derivation](../derivations/GST_all_N_spatial_fold_binary_decision_test_2026-10-23.tex), initial source commit `75f28cc921e0e680eb4b9677a809e586aefa6a4a`, strengthened for arbitrary original X at `a8a5c41425a88d6a9d72252da8df8c7244df8ab6`.

**Exact computation artifact:** [Wolfram source](../computations/gst_all_N_spatial_fold_binary_decision_2026_10_23.wl), fetched and actually re-executed at final blob `d220f2be01f4569231711a90e6f2ba45b521f4c6`. Determinant `ss-tt`; equal moduli gives 0; unequal (i,2i) gives i. Full pure Hodge polynomial and required off-diagonal coefficient checked at EVERY N=2..40, 39/39 PASS, failedCases={}. Previous Wolfram iterations included an unnecessary protected symbol N shadow and an incomplete rename of coefficient extraction; both were fixed and the **final fetched source** passed with no warning.

**Lean:** No claim of fresh Lean compilation this round. Existing `GSTGradedWorldAlgebra.lean` separately formalizes signed charge and purity gap and their invariance under all finite Tate folds; `GSTGraphV2UnboundedHigherCausality.lean` has the graph-alignment theorem at previously verified green CI. The new all-N smooth-projective claim uses geometry (complex tori, Lefschetz (1,1), Chow projective bundle formula), not a falsely typed abstract Lean witness.

## Proof-audit verdict and exact logical distinction

1. The smooth algebraic Hodge-type breaking example is **proved as written** and supplies a genuine counterexample to the proposed negative *inference*, not to the conjecture.
2. The nodal actual full-purity break is **proved as written** with explicit singularity qualifier.
3. The assertion that all unbroken pure Hodge structures automatically yield a universal proof of rational Hodge algebraicity is **not established** by the fold laws. There is no known counterexample to the full rational Hodge conjecture exhibited here, nor should one infer one from this diagnosis.
4. The mathematical follow-up, if the GST decision experiment is to truly decide Hodge, must provide an additional `all-X` geometric invariant beyond purity/type drift and establish how it forces the canonical cycle class conclusion. Do not silently call that consequence proved.

Outcome is a decisive geometry-first falsification of the current binary decision methodology, not successful completion of the original rational Hodge conjecture.