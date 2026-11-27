# Mathbox: complete polarized surface-graph H1 moment criterion

- **Date:** 2026-10-17
- **Kind:** constructive geometric theorem, computation, and proof-scope refinement.
- **Target:** Construct independent non-Lefschetz algebraic codimension-two cycles on the original smooth fourfold S×S for every smooth polarized projective surface S.
- **Corrects and strengthens:** [K3 direct graph orbit](2026-10-17-k3-direct-primitive-graph-orbit.md) and the green surface augmentation Lean theorem: a polarized automorphism need not preserve the graph Lefschetz class when H¹(S) is nonzero.
- **Objects:** S smooth projective complex surface, h ample, automorphisms g preserving h, X=S×S with L=pr1*h+pr2*h. Every graph Γ_g is an authentic rational algebraic codimension-two cycle on X. For a finite rational coefficient vector a let Z(a)=Σ_g a_g Γ_g.
- **Exact geometric proof:** The graph inclusion i_g:S→S×S obeys i_g*L=2h. Pair L cup cl(Γ_g) against H²(X), split by Künneth:
  1. For pr1*u with u∈H²(S), the pairing is 2∫_S h u, independent of g.
  2. For pr2*v with v∈H²(S), the pairing is 2∫_S h g*v=2∫_S h v.
  3. For pr1*s cup pr2*t with s,t∈H¹(S), the pairing is 2∫_S h s g*t.
  
  Since h²>0, the first two types vanish on Z(a) iff Σ a_g=0. The polarized H¹ bilinear form Q_h(s,t)=∫ h s t is nondegenerate by Hard Lefschetz and Poincaré duality. Thus the third type vanishes for all s,t iff Σ a_g g*|H¹=0. Künneth exhausts H²(X), and Poincaré duality detects H⁶ classes.
- **Full theorem:**
  
  \[
  \operatorname{cl}(Z(a))\text{ primitive}
  \iff \sum_g a_g=0
  \quad\text{and}\quad
  \sum_g a_g\,g^*|_{H^1(S,\mathbb Q)}=0.
  \]
  
  Thus graph-primitiveness is the kernel of a computable rational moment matrix, not an abstract surjectivity condition.
- **Specialization:** For K3 and other regular surfaces H¹(S,ℚ)=0, all coefficient vectors with total sum zero produce genuine algebraic primitive classes. The graph classes may be cohomologically dependent; an independent second rank certificate comes from their action on primitive H²(S).
- **Concrete irregular test:** For S=E×ℙ¹ with E elliptic, take g=[−1]_E×id. It preserves a product polarization but acts as −I on H¹(S). For normalized H¹(E) classes s,t, the Lefschetz pairing of Γ_id−Γ_g with pr1*s cup pr2*t is 4∫_S h s t=4. Its class is therefore nonprimitive. The two-graph moment matrix has rational rows (1,1) and (1,−1), determinant −2, and kernel zero.
- **Wolfram exact tests:** For C4 acting by rotation J=[[0,−1],[1,0]] on a two-dimensional rational H¹ sector, the augmented moment matrix of (I,J,−I,−J) has rank 3, giving one-dimensional primitive graph coefficient kernel spanned by (−1,1,−1,1). For a regular surface the pure augmentation condition on four graphs has kernel dimension three. The matrix computation is exact over ℚ.
- **Lean:** GSTSurfaceGraphH1Obstruction.lean implements both directions of the two-moment equivalence using a separated Künneth comparison, the augmented native group-ring cycle, and a theorem that primitiveization retains any transcendental measurement annihilating the native Lefschetz correction. Dedicated CI workflow gst-universal-surface-graph-augmentation.yml compiles this plus GSTUniversalSurfaceGraphAugmentation.lean; [run #39030587546](https://github.com/kyo-oo/HC-PROOF/actions/runs/39030587546) passed at commit 008dc6b05b2359528394eb1f775fea7173c33fcf, with the sorryAx audit passing.
- **Further rank source:** The projection of a graph class to the primitive H²(S)⊗H²(S) Künneth sector detects its action on primitive H²(S). Lefschetz-correction classes project to zero there. Therefore representation rank on the primitive H² sector provides nonzero, independent algebraic primitive classes even on irregular S after GST primitiveization.
- **Failure/no-go criterion:** Degree-one polarization preservation alone gives a shared graph Lefschetz image only when the odd-cohomology terms cancel. The exact moment condition supplies the missing hypothesis.
- **Success:** Full necessary-and-sufficient criterion in ordinary geometry; exact rational examples; Lean theorem and independent primitive readout committed.
- **Route disposition:** Active for original-carrier surface self-products. Extending to every arbitrary original smooth projective X demands a new source-producing correspondence with full primitive rational Hodge rank.
- **Evidence label:** Geometry proof, exact Wolfram calculations, Lean source with explicit comparison hypotheses; final kernel CI to be reconciled.
- **First unresolved implication:** Construct universal native cycle sources on arbitrary X, not just self-products and finite group orbits, with canonical cycle-class spanning all rational primitive Hodge directions.
