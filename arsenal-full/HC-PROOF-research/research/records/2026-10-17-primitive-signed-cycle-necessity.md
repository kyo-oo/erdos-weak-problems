# Mathbox: primitive algebraic representatives require signed cycles

- **Date:** 2026-10-17
- **Kind:** direct original-X geometric constraint, exact calculation, and program decision.
- **Target:** Refine the construction of primitive rational algebraic classes on arbitrary smooth projective complex X, rather than rely on positivity of a single effective analytic subvariety.
- **Hypotheses and types:** X an n-dimensional smooth projective complex variety, h=c1(O_X(1)) ample, 1≤p≤n/2. Rational cohomology class α∈H^(2p)(X,Q) primitive in the usual Lefschetz sense: L^(n−2p+1)α=0 with L∪β=h∪β.
- **Mechanism (uniform geometry):** Multiply the primitive equation by h^(p−1). Since n−2p+1+p−1=n−p,
  
  \[
     h^{n-p}\cup\alpha=0,\qquad
     \deg_h(\alpha)=\int_X\alpha\cup h^{n-p}=0.
  \]
  
  If α=cl_X(Z) for a nonempty effective algebraic codimension-p cycle Z=Σ_i a_i[V_i] with a_i>0 and nonempty projective subvarieties V_i, then
  \[
     \deg_h(\alpha)=\sum_i a_i\deg_h(V_i)>0
  \]
  by positivity of ample intersection degree. Therefore a nonzero primitive rational algebraic class is represented by a **signed** rational algebraic cycle with both positive and negative coefficients, or by another rational expression equivalent to such a difference.
- **Concrete test on a cubic fourfold containing a plane:** H=h², P=plane, pairing Gram [[3,1],[1,3]] on basis (H,P). The primitive algebraic cycle Z=3P−H satisfies H·Z=0 and Z²=24. Wolfram evaluated H·H=3, H·P=1, and
  \[
     3(H\cdot P)-H^2=3-3=0,\qquad
     (3P-H)^2=24.
  \]
  It also solved exactly a≥0,b≥0,a+3b=0, obtaining only a=b=0. Hence positive rational source combinations cannot generate this primitive direction, whereas the actual signed cycle does.
- **Success criterion:** Design a direct **signed native difference** constructor from X's own geometric subvarieties that produces a prescribed primitive rational Hodge direction and certifies its canonical class. In codimension 2, arbitrary smooth fourfolds are the decisive first unresolved regime.
- **Failure criterion:** A route insisting on one nonzero effective calibrated complex analytic representative for a nonzero primitive class contradicts the degree-zero and positive-ample-degree identities. It must instead produce signed differences, a genuinely new geometric decomposition, or a corrected calibrated-current argument proving rational algebraicity after decomposition.
- **Outcome and evidence label:** Proved general positive-degree obstruction and exact cubic example in standard projective intersection theory; Wolfram independently verified the integer intersection arithmetic. This is a statement about admissible construction routes, not a counterexample to rational Hodge algebraicity.
- **Route disposition:** Purely effective primitive-cycle construction retired. Signed native algebraic incidence/regularization becomes the active direct-X source route. Prior cubic plane component and native point-cycle construction give genuine positive/negative source examples, but the universal source-generation theorem for arbitrary X remains the first mathematical obligation.
- **Nearest prior attempt:** GST direct trace-zero cycles and integral calibration efforts; GSTActualXHodgeResidualProjection.picardTraceZero_has_zero_primitive_projection shows the existing divisor-born trace-zero source has zero primitive contribution.
- **Changed input:** Work with \(\mathbb Q\)-linear differences of independently constructed actual codimension-p subvarieties, not a single positive analytic cycle; constrain exact degree zero first, then independently certify nonzero primitive pairing.
- **Cheapest next decisive computation:** Given a candidate all-X source family of actual codimension-two subvarieties, build its degree vector and primitive intersection Gram on the ORIGINAL X. Test whether the degree-zero kernel maps to a nonzero canonical primitive class; if yes, attempt a target-dependent spanning construction without assumed rank.
- **Artifacts and commands:** Wolfram exact cubic Gram test this session; mathematical source modules GSTCubicFourfoldPlanePrimitive.lean and GSTActualXHodgeResidualProjection.lean; current program plan research/ACTIVE_HODGE_PROOF_PLAN.md.
- **Strongest surviving statement:** Every nonzero primitive algebraic Hodge class in a positive codimension has zero ample degree and requires a signed cycle representation. The existing native algebraic cycle infrastructure supports signed rational coefficients.
