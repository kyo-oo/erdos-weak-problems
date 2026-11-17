# Mathbox corrected-GST program: exact calibrated-current obstruction and direct all-p support Gysin Chow construction

**Date:** 2026-10-23, Asia/Kolkata.  
**Starting checked branch:** `research/gpt6-native-point-primitive-span-20261017`, SHA `351418df4f9d7fa0b27b417cf508096b4f3944ab`.  
**Research target:** arbitrary original smooth projective complex X, all p, every rational (p,p) alpha, an independently constructed actual rational Chow cycle Z_alpha on SAME X with canonical Betti class alpha.  
**Owner's direction:** full dimensionless GST whole-spatial folding and source creation; no special-family replacements, no source-image/conditional theorem relabeled the final proof.  
**Mathbox methods:** research-program, research-attempt, proof-audit (self-review), computation-audit principles. No external internet and no local Lean installation. New result uses standard external theorems (Federer--Fleming, calibrated integral current structure/King, Chow, Serre ideal-sheaf generation, rational semisimplicity, Lefschetz (1,1)) whose exact primary source has not been independently fetched this turn.

## A. What EXACTLY remained wrong after the previous research-plan correction

The prescribed-alpha original-X topological K-theory `E_plus,E_minus` and smooth-real determinantal pseudocycles `D_plus,D_minus` truly existed; their signed rational Betti class was alpha and the primitive Hodge--Riemann coupling was nonzero. But these constructions exist for **every rational even cohomology class, including non-Hodge inputs**. They DO NOT exploit the full rational Hodge condition to produce actual algebraic cycles. The old suggested completion introduced BOTH bounded mass and vanishing Kähler Wirtinger calibration defect; bounded mass is mathematically automatically implied by vanishing defect in a FIXED homology class, since mass = defect + closed calibration pairing. Thus the actual missing fact was entirely the zero-defect existence law. The corrected plan had repaired the research INPUT but not derived this last independent GEOMETRIC conclusion.

## B. Executed new exact spatial variational theorem, all original X and p

[Mathematical proof file](../derivations/GST_target_sensitive_calibration_variational_gap_and_coniveau_source_2026-10-23.tex), introduced at `da5545ccee4285da9e108fbf46a4fa28a9f39790`, refined through `48d6452364d0a7cc5a7830ba3159aaf8324dc894`, `4096d1a0478a3a75ba2fd52c7dc4101a816b78e6` and `1fc80ff481bfb926395a6aae8babff0d60645717`.

For k=d-p, phi_k=omega^k/k!, and an ACTUAL integral homology class gamma of closed integral 2k-currents on ORIGINAL X, define `d_omega(gamma)=inf_([T]=gamma)(Mass(T)-T(phi_k))`. It is ALWAYS attained: constant closed pairing plus bounded defects => bounded mass; Federer-Fleming gives an integral flat limit in the same integral homology class; lower semicontinuity attains the infimum.

**Exact original-X effective theorem**: `d_omega(gamma)=0` IFF gamma is represented by an EFFECTIVE actual algebraic codim-p integral cycle. Proof: minimizing integral current with defect zero is positive complex-calibrated; positive integral closed currents are analytic holomorphic chains, then projective Chow algebraizes. Converse effective complex cycle is Wirtinger-calibrated.

**Stronger one-gap original-X algebraicity equivalence**: for ANY rational alpha in H^(2p)(X,Q), it is rational algebraic on original X iff there exist integers m>0,n>=0 and an ACTUAL integral homology lift gamma with PD_Q gamma=m alpha+n h^p and d_omega(gamma)=0. On the positive side, an independently constructed effective C of class gamma and a genuine ample complete intersection B of class h^p give `Z_alpha=(C-nB)/m` on original X. Conversely, if alpha is genuinely algebraic, multiply its Chow cycle to write mZ=A-B with effective cycles A,B; the existing actual Serre/Bertini hypersurface-incidence excess-component theorem embeds each negative component W in a pure complete intersection of degree r_W^p h^p with multiplicity one; a finite sum builds n h^p=B+R effective, so mZ+n h^p=A+R EFFECTIVE. This is a mathematically exact all-X equivalence, not an independent theorem that zero gap always holds for Hodge input.

**Critical correction:** The previous proposed two-bundle calibrated-limit path needs only ONE calibrated effective source *if* one uses an ample background term; the second one is already a genuine algebraic complete intersection. Even with this simplification, universal zero-gap existence is the unproved geometric law, so the proof cannot be honestly certified by relabeling the equivalence.

## C. Executed falsification of naive smooth-flow completion

An actual nonzero algebraic Hodge (1,1) class on X=P1×P1 has a stationary smooth real representative with STRICTLY POSITIVE defect: T=(P1×{q}) disjoint union (equator×equator), q off the equator. Both components totally geodesic, H_T=0; equator product is nullhomologous and Lagrangian, hence class [T]=[P1×{q}] is Hodge, while defect(T)=Area(equator torus)>0. Thus a universal rule 'mean-curvature stationary + Hodge => calibrated' is FALSE for genuine projective geometry, and the prior mass Lyapunov law does not prove defect extinction. This is a counterexample to that FLOW INFERENCE, not a counterexample to Hodge conjecture.

## D. Separate genuinely ALgebraic source birth from ALREADY-SUPPORTED prescribed Hodge alpha

The same math source proves for EVERY original X, every p (1<=p<=dim X), and every rational Hodge alpha of type(p,p) with independently supplied algebraic support-Gysin relation:

`alpha ∈ Σ_i f_i* H²(Y_i,Q)` where each Y_i is a smooth projective (dim X−p+1)-fold mapped properly into X, with image in algebraic codim-(p−1) support.

This input is a genuine geometric support/cohomology relation and **does not supply an original-X Chow representative**. The actual rational Hodge map `Σf_i*: ⊕H²(Y_i,Q)(−(p−1))→H^(2p)(X,Q)` has a rational Hodge substructure image; semisimplicity yields a rational (1,1) lift beta_i of the PRESCRIBED alpha. By Lefschetz (1,1), beta_i is the canonical class of a REAL algebraic divisor D_i on Y_i. The explicit ORIGINAL-X Chow cycle is `Z_alpha=Σ_i f_i* D_i`, with exact canonical Betti equality alpha by proper Gysin/cycle naturality. This is a real source constructor covering the maximal-support/coniveau-(p−1) part of each Hodge group, **not** all arbitrary primitive alpha.

## E. Acceptance audit & classification

1. Original-X alpha present as input? **YES**, for geometric signed cycle and support-dependent Gysin source.
2. Genuine original-X algebraic Chow source for maximal-support rational Hodge alpha? **YES**, given the independent geometric Gysin image condition (not Chow source).
3. Genuine original-X algebraic Chow source for EVERY alpha unconditionally? **NO**. No universal existence of zero-gap shifted effective class, and no proof all Hodge alpha admit maximal Gysin support.
4. Canonical Betti comparison for the supported route? **YES**, via actual proper algebraic pushforward; no abstract Stage2G cycleClass substituted.
5. Mean-curvature stationary => positive calibrated analytic cycle? **REFUTED**, by the above nonzero algebraic class example.
6. Validity of universal variational theorem? **PROVED from named analytic/geometric theorem dependencies**, self-reviewed, not kernel formalized.
7. New Lean CI? **NONE**. Not claiming a Lean proof of positive-current holomorphic-chain structure without genuine Mathlib geometry APIs.

**Most important mathematical lesson**: The correction to a target-dependent smooth source is not sufficient; real Poincare duals exist for every rational input. To finish the original-X proof, a new GST law must actually force the existence of *positive complex-algebraic source geometry* from type(p,p), not merely the real source, monotone flow, or another equivalent zero-gap restatement. The coniveau-Gysin route is a concrete successful construction where extra geometric support information is independently available; arbitrary remaining primitive Hodge classes are the active unsupplied sources.
