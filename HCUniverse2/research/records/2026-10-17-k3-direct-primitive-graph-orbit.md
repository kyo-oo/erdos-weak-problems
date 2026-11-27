# Mathbox — directly primitive K3 graph orbit cycles

- **Date:** 2026-10-17
- **Kind:** constructive research upgrade
- **Target:** Produce independent non-Lefschetz algebraic cycles directly on a smooth projective fourfold using genuine native subvarieties and canonical geometric cohomology.
- **Corrects/strengthens:** [K3 graph primitive sources](2026-10-17-k3-graph-primitive-source.md): the original geometric construction used algebraic Lefschetz corrections; the present orbit differences are primitive **without applying any corrective cycle operator**.
- **Hypotheses and types:** Smooth projective quartic K3 surface S={z₀⁴+z₁⁴+z₂⁴+z₃⁴=0}⊂ℙ³, its genuine order-four projective automorphism g:[z₀:z₁:z₂:z₃]↦[i z₀:z₁:z₂:z₃], and X=S×S, complex dimension four. Rational codimension-two algebraic graph cycles and canonical Betti cup product, ample class L=pr₁*h+pr₂*h.
- **Active conventions:** Γ_{g^k} is the algebraic graph of g^k embedded as a codimension-two surface in X; k∈{0,1,2,3}. Define A=Γ_id−Γ_{g²}, B=Γ_g−Γ_{g³} in CH²(X)_ℚ.
- **Geometric source construction:** For any polarized automorphism u of the **quartic K3 surface S**, the restriction of L to Γ_u is h+u^*h=2h. Thus L⋅Γ_u=i_{u*}(2h). Since H¹(S,ℚ)=0, Künneth gives H²(S×S,ℚ)=H²(S)⊗H⁰(S)⊕H⁰(S)⊗H²(S), so the relevant pairings reduce to ∫_S 2h∧a and ∫_S 2h∧u^*b=∫_S 2h∧b. Therefore **L cl(Γ_u) is independent of u on this K3**, and the two graph differences satisfy
  L⋅cl(A)=L⋅cl(B)=0.
  Thus A and B are directly **primitive algebraic cycles**, without choosing any unknown Hodge representative or constructing a Hard-Lefschetz inverse.
- **Independence mechanism:** The Künneth H²(S)⊗H²(S) component of cl(Γ_u) acts on H²(S) as u^* or its adjoint. Its restriction to the cyclotomic transcendental subspace of H²(S,ℚ) has g²=−I. A acts as (I−g²)=2I, B acts as (g−g³)=2g. On the nonzero holomorphic 2-form, these actions have eigenvalues 2 and 2i. No nontrivial rational linear combination of 2 and 2i vanishes, so A,B are independent rational primitive Hodge classes.
- **Exact Wolfram audit:** The rational rotation g=[[0,-1],[1,0]], g⁴=I, g²=−I. Wolfram computed A_op=2I and B_op=2g, rank_Q{vec A_op,vec B_op}=2, exact Frobenius trace Gram [[8,0],[0,8]], determinant **64**. The quartic polynomial is invariant under diag(i,1,1,1), and its holomorphic residue transforms by determinant i, whose rational minimal polynomial is t²+1.
- **Lean implementation:** `GSTK3DirectGraphOrbitDifference.lean` defines direct differences from four genuine native codimension-two cycles, proves their primitive-test vanishing when the four hyperplane images agree, and proves their linear independence under the actual geometric transcendental measurement interface. The geometric proof above supplies the common hyperplane image for the explicit K3 graph orbit. The current Lean source distinguishes scheme-level graph realization from abstract Q-linear action; the canonical Künneth graph comparison remains the next integration obligation.
- **Success criterion:** Direct native primitive graph differences, independent rational Hodge classes, and Lean-kernel verification without sorryAx.
- **Failure/no-go criterion:** An unsupported analytic graph-action comparison would weaken the geometric conclusion; derive it from actual Künneth and Gysin maps before treating the formal interface as a completely instantiated K3 scheme object.
- **Current dependency/evidence status:** Dedicated Actions workflow `.github/workflows/gst-k3-direct-graph-orbit.yml` created. It was running at record creation. Earlier exact Wolfram computation completed with rank2, determinant64. Original K3 primitive graph module was under CI after namespace repair.
- **Nearest prior attempt and first failure:** Earlier graph module CI initially missed the `GSTUniversalLefschetzCurveCycles` namespace for divisor geometry, repaired in commit ce79f7f07381823812eda891c6dd95b5d98c5256. Direct graph differences eliminate reliance on a divisor correction in the geometric K3 case.
- **Route:** Actual order-four algebraic automorphism orbit, canonical graph-Gysin comparison, rational cyclotomic independence.
- **Changed input:** Use the explicit algebraic orbit differences Γ0−Γ2 and Γ1−Γ3 instead of primitiveizing arbitrary graph cycles.
- **Attempt outcome:** A concrete direct primitive algebraic source construction on an actual K3 self-product, with an exact independent rank-two holomorphic-character witness.
- **Route disposition and scope:** Constructive example and a mechanism for any polarized smooth projective surface admitting an automorphism with nontrivial rational action on its transcendental H² sector.
- **Evidence label:** Ordinary geometric proof plus exact Wolfram arithmetic; Lean proof interface awaiting GH CI.
- **Review and freshness status:** Mathbox self-reviewed 2026-10-17 at research branch, commit dbe5bfe5c75b33bb65664912efa92ddfecea4fbe.
- **First unresolved implication:** Instantiate the projective K3 graphs' canonical Betti cycle classes as Lean terms and extend independent graph correspondences to arbitrary smooth projective X beyond self-product sources.
- **Strongest surviving statement:** On the original quartic K3 self-product, two explicit rational differences of genuine algebraic automorphism graphs are intrinsically primitive, rational and independent.
- **Artifacts and commands:** `GSTK3DirectGraphOrbitDifference.lean`, `.github/workflows/gst-k3-direct-graph-orbit.yml`, Wolfram exact order-four operator Gram.
- **Next unresolved question:** Construct GST native graph/correspondence generators on an arbitrary original X with enough primitive directions for its rational Hodge fiber; the new orbit-difference operator suggests an arithmetic-geometric route to source independence.


## Extension to irregular surfaces

For smooth surfaces with nonzero \(H^1(S,\mathbb Q)\), the additional Künneth summand \(H^1(S)\otimes H^1(S)\) contributes \(2\int_S h\wedge a\wedge u^*b\) to the graph's Lefschetz image. The exact polarized graph construction uses two independent moments: \(\sum_g a_g=0\) and \(\sum_g a_g g^*|_{H^1}=0\). The new `GSTSurfaceGraphH1Obstruction.lean` implements the corresponding finite-group primitive construction and its precise Künneth separation criterion.
