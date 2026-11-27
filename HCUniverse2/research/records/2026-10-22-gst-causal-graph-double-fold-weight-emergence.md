# GST causal-graph double-fold weight-emergence law

- **Date:** 2026-10-22
- **Kind:** bounded mathematical research attempt and exact finite verification
- **Base checkpoint:** branch research/gpt6-native-point-primitive-span-20261017 at a561857fc24edf835c66c559ad6128c27bba0736
- **Target:** Realize the user's dimension-free GST causal fold as an actual topological identification, derive a dimension-emergence equation, and distinguish pure Hodge structure from misleading charge-zero nonpure classes
- **Types:** Connected finite multigraph Γ with r≥1 rational P¹ normalization components and e ordinary nodal identifications; β=e-r+1; projective nodal curve C_Γ with mixed Hodge cohomology H^k(C_Γ,Q)
- **Conventions:** Cohomological degree k, weight w=p+q, Hodge charge χ=p-q, purity gap δ=w-k, Tate Q(-j) of type (j,j) and weight 2j
- **Nearest prior work:** 2026-10-21-gst-emergent-dimensional-causal-hodge-fold-program.md had one nodal curve plus separate charge leakage. This attempt generalizes causal incidence graphs and produces an **even-degree rational diagonal yet nonpure** class through two independent graph-cycle identifications
- **Outcome:** Proved under standard mixed-Hodge and normalization-sequence facts; self-reviewed, not Lean-kernel-verified. Exact Wolfram computations pass in stated finite ranges
- **Route disposition:** Causal-topology/Hodge purity diagnostic derived; no original-X Chow-source theorem claimed
- **Evidence:** Self-reviewed mathematical argument plus computationally verified finite identities; no new Lean build or axioms assumed
- **Cheapest discriminators:** Tree versus triangle; bouquet with 2 and 3 loops at N=2 gives rank-six weight-two diagonal degree-four cohomology
- **Next unresolved implication:** Obtain an independently constructed actual canonical Chow class on untouched original smooth projective X from an appropriate causal geometric operation, without assuming algebraicity of the input class

## The causal graph rank law

Normalize a connected projective nodal curve whose rational components correspond to Γ vertices. The constant-sheaf normalization sequence gives

\[
0\longrightarrow\mathbb Q\longrightarrow\mathbb Q^r
\xrightarrow{B_\Gamma}\mathbb Q^e
\longrightarrow H^1(C_\Gamma,\mathbb Q)\longrightarrow0.
\]

Connectedness implies rank B_Γ=r-1, so the new weight-zero, Hodge-(0,0) cohomology is

\[
H^1(C_\Gamma,\mathbb Q)\cong H^1(\Gamma,\mathbb Q)
\cong\mathbb Q(0)^{e-r+1}.
\]

No emergent weight-zero hole appears from a tree. One independent causal graph loop produces one, and g independent loops produce g.

With a=t²s²uv, the exact mixed-Hodge graded polynomial on C_Γ×P^N is

\[
(1+\beta t+r a)\sum_{j=0}^{N}a^j.
\]

Every j from 0 through N has β classes at cohomological degree 2j+1 of weight 2j, Hodge type (j,j), giving (χ,δ)=(0,-1).

## Double-causal-fold law: all N, even degree, diagonal charge

For connected graphs Γ₁ and Γ₂ with independent causal loop ranks β₁ and β₂, let

\[
Z_N=C_{\Gamma_1}\times C_{\Gamma_2}\times\mathbb P^N.
\]

The precise all-N formula is

\[
\operatorname{Gr}^{W}_{2j}H^{2j+2}(Z_N,\mathbb Q)
\cong
H^1(\Gamma_1,\mathbb Q)\otimes
H^1(\Gamma_2,\mathbb Q)(-j)
\cong\mathbb Q(-j)^{\beta_1\beta_2},
\quad 0\le j\le N.
\]

Hence there are β₁β₂ rational diagonal Hodge-charge-zero classes in even cohomological degree 2j+2 whose true weight is 2j. They have purity gap δ=-2. This is genuine topological/cohomological birth, not a change of Hodge-coordinate labels.

For every nonempty connected smooth projective X, H⁰(X,Q)=Q supplies the same direct summand in X×Z_N. This validates the arbitrary-input-X and all-emergent-N diagnostic on a **new singular projective realized world**, not on the original smooth X.

An algebraic Tate dimension fold (k,p,q,w)→(k+2j,p+j,q+j,w+2j) conserves both χ and δ; increasing dimension cannot remove the causal purity deficit.

## Executed Wolfram checks

- Connected tree: (vertices,edges,rank B,β)=(3,2,2,0)
- Triangle: (3,3,2,1)
- Three self-loops: (1,3,0,3)
- Four vertices and five edges: (4,5,3,2)
- Single-fold coefficient identities: 84 exact parameter pairs; all TRUE for β=1..4, N=0..5, all j≤N
- Double-fold identities: 324 exact cases; all TRUE for β₁,β₂=1..3, N=0..7, all j≤N
- Degree-four, weight-two example for two and three loops: 6uv, i.e. six rational (1,1) pieces of **weight two below its cohomological degree**

The uniform proofs follow from incidence-rank/normalization plus mixed-Hodge Künneth. The finite checks are not substituted for those proofs.

## Critical category boundary

This does **not** falsify the classical rational Hodge conjecture. C_Γ has nodes, so Z_N is singular. Genuine mixed Hodge structures exist on its cohomology, but the weight-2j classes in degree 2j+2 are not valid pure degree-2j+2 rational Hodge classes of a smooth projective complex variety. A spectral charge-zero projector without the purity index would confuse these objects. No theorem constructing a Chow representative of an arbitrary original-X rational Hodge class is claimed.

## Artifacts and source provenance

- [Full mathematical derivation](../derivations/GST_causal_graph_double_fold_weight_emergence_2026-10-22.tex)
- [Exact stateless Wolfram source](../computations/gst_causal_graph_double_fold_weight_emergence_2026_10_22.wl)
- GST modules read: GSTGeneralSpace, GSTGraphV2OmniversalCore, GSTGraphV2SelfExpandingCosmology, GSTGraphV2RecursiveStateCausality, GSTGraphV2UnboundedHigherCausality, GSTGradedWorldAlgebra, waves/GSTNCohomologyV2, waves/GSTNCohomologyV3, plus current October 21 causal-fold records.
- Exact Wolfram outputs: SingleCount=84, SingleAllTrue=True, DoubleCount=324, DoubleAllTrue=True; matrix rank outputs (2,2,0,3); double even weight-two coefficient 6uv.
- No local Lean installation, no new Lean CI run and no public internet search.


## Reverse causal operation: smoothing births actual pure algebraic Hodge directions

For the irreducible nodal rational curve with g≥1 independent self-node causal identifications, a flat projective smoothing (when specified as an actual geometric family) has smooth genus-g fibers C_t because arithmetic genus is constant and equals the dual graph cycle rank g. This is a real topology change, not a relabeling.

In degree/Hodge/weight variables (t,u,v,s), let a=t²s²uv. The singular nodal polynomial is (1+g t+a)Σ_{j=0}^N a^j. The smooth pure genus-g polynomial is (1+g t s(u+v)+a)Σ_{j=0}^N a^j. Thus smoothing replaces the weight-2j, (j,j), rank-g cohomology of degree 2j+1 with genuine pure weight-(2j+1) Hodge types (j+1,j) and (j,j+1), multiplicity g each. This is the distinct *Hodge-preserving birth* outcome of the user's proposed topological experiment.

On the smooth self-product C_t×C_t, the actual algebraic cycle
Z_t = [diagonal] − [C_t×{o}] − [{o}×C_t], for any closed complex point o,
has nonzero rational Betti class in H¹(C_t)⊗H¹(C_t), pure (1,1), because it acts as identity on H¹. External cup product with h^j on P^N gives a nonzero, actual algebraic rational (j+1,j+1) class in degree 2j+2 for all j≤N. This demonstrates real algebraic Hodge birth as a side effect of a specified geometric smoothing, independently of any assumption that the universal Hodge conjecture is true.

**Additional Wolfram evidence:** 144 parameter tuples (g=1..4, N=0..7, every j≤N), each with two exact polynomial identity checks, returned both TRUE. These checks validate the formulas, not the geometric smoothing existence theorem or the diagonal correspondence proof; those use their explicit standard geometric arguments. The total newly executed source checks are 84+324+144=552 parameter tuples.

**Original-X limit remains unchanged:** X×C_t×C_t×P^N acquires true new diagonal Chow cycles, but a prescribed unknown rational Hodge class on the untouched original X has not been represented. No general-Hodge solution or counterexample is asserted.


## 2026-10-22 in-place Lean upgrades: causal and Hodge genesis integration

The owner's correction makes the research object one **causal fold which births both topology and Hodge data**, not a preexisting Hodge structure receiving a separate coordinate transformation.

- **Higher causality:** Updated [GSTGraphV2UnboundedHigherCausality.lean](../../GSTGraphV2UnboundedHigherCausality.lean) in place. Certified distinct, nonidentity higher-causal 1-cell loop families obey zero signed incidence gradient and exact independent finite cochain reconstruction. These are 1-skeleton channels; higher 2-cell relations could remove some surviving H¹ and must not be ignored in a geometric realization.
- **N-cohomology:** Updated [waves/GSTNCohomologyV3.lean](../../waves/GSTNCohomologyV3.lean) in place. The independent double-fold rational coordinates are indexed by pairs of N-hole channels with exact multiplicity (g,h) → gh and reconstruction/uniqueness.
- **Graded Hodge:** Updated [GSTGradedWorldAlgebra.lean](../../GSTGradedWorldAlgebra.lean) in place. CausalHodgeCell derives weight and signed charge from its unlimited cosmic address while independently retaining actual born cohomological degree. The geometric nodal, doubled and smooth birth grading signatures and their arbitrary-depth Tate laws are kernel-checked.

**Generative mathematical equation (G1/G2).** For a connected nodal graph with r rational normalization components and g=e-r+1 independent graph loops, set A=t²s²uv. Then the actual singular-projective and specified smooth-projective realizations have graded polynomials

    G_fold = (1 + g t + r A) Sum_{j=0}^N A^j
    G_smooth = (1 + g t s(u+v) + A) Sum_{j=0}^N A^j
    G_smooth - G_fold =
       [g t (s(u+v)-1) + (1-r) A] Sum_{j=0}^N A^j.

The graph loop rank g is computed by the causal incidence. Smooth Hodge ranks follow from the genus of the *actual* smooth geometric realization. The updated [LaTeX derivation](../derivations/GST_causal_graph_double_fold_weight_emergence_2026-10-22.tex) includes the proof and precise scope.

**GitHub Actions Lean verification:** [graded world run 39733509021](https://github.com/kyo-oo/HC-PROOF/actions/runs/39733509021) SUCCESS (commit 579e40b3d0e7ec250ba72b562da563899874ba41). [Higher causal repair run 39733964568](https://github.com/kyo-oo/HC-PROOF/actions/runs/39733964568) SUCCESS (commit eb9dcc463c82004db6af5d731fdc1747c9e557ad); the first compile caught omitted explicit cosmos arguments, which were repaired. [N-cohomology run 39733826306](https://github.com/kyo-oo/HC-PROOF/actions/runs/39733826306) SUCCESS (commit 4e1563f4b49135cf5ea713c1641eedd2c9fe08f6).

**Wolfram:** Re-executed the updated [exact source](../computations/gst_causal_graph_double_fold_weight_emergence_2026_10_22.wl) from GitHub. All 1308 tested parameter tuples passed: 84 single-fold, 324 double-fold, 144 smoothing, 216 general equation identities, 540 general coefficient pairs, together with four graph incidence-rank fixtures. These are exact bounded checks. No new Mathlib theorem identifies this abstract causal loop type with an arbitrary smooth-projective original-X Chow class; that remains the independent universal theorem goal and must not be claimed from graded algebra alone.
