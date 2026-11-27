# GST all-full-fiber native birth: hyperplane-derived mass-one null cycle eliminates artificial marginal obstruction

**Date:** 2026-10-22 IST. **Authoritative repo:** `kyo-oo/HC-PROOF`, branch `research/gpt6-native-point-primitive-span-20261017`; starting HEAD `1baa2b42f4b36a3d713f16d1e67e67d0af97bfb7`. **Exact Hodge target still retained:** For EVERY smooth projective complex original X, every p, and every rational Hodge (p,p) alpha, ACTUALLY construct Z_alpha native rational codimension-p and prove canonical Betti equality. **Mathematics-first new construction:** [GST_fibered_native_mass_calibrated_cycle_birthday_2026-10-22.tex](../derivations/GST_fibered_native_mass_calibrated_cycle_birthday_2026-10-22.tex). **Edited real existing Lean GST module:** [GSTClassicalHodgeFiberedCycleClassDefect.lean](../../GSTClassicalHodgeFiberedCycleClassDefect.lean). **Reproducible exact Wolfram:** [gst_fibered_mass_calibration_2026_10_22.wl](../computations/gst_fibered_mass_calibration_2026_10_22.wl). **GitHub Actions kernel run:** [39677511282](https://github.com/kyo-oo/HC-PROOF/actions/runs/39677511282) for source SHA `b32b470e7868e92c435de6d66adce518fe7ac0a9`; check actual current status before any claim green.

## Crucial existing GST laws used and new mathematics

The existing `GSTClassicalHodgeFiberedNativePullback.lean` has ALREADY proved:
- two independently meaningful FULL marginals on a common finite-support state: `forgetPoint` retains EVERY Hodge basis index while `forgetMultiplicity` retains every actual codimension-p point-cycle coefficient.
- `marginal_mass_balance` and `exists_joint_marginals_iff`: a simultaneous native/Hodge state exists exactly if the *sum of Hodge coefficients* equals the *sum of native coefficients*.
- explicit `glueMarginals` and `glueMarginals_forgetPoint/forgetMultiplicity` preserve both marginals when their masses match.
- `toNativeCycle` realizes the full native rational finite presentation into an ACTUAL codimension-p algebraic cycle, not a fake abstract source.

`GSTClassicalHodgeFiberedCycleClassDefect.lean` defines `fiberedCycleClassDefect = (H.cycleClass p)∘toNativeCycle - subtype∘fiberedHodgeClass`. It previously required genuinely existing zero-defect states for every Hodge basis vector; assembling those zero-defect basis states reconstructs arbitrary rational Hodge classes, but those states were NOT produced.

**NEW mass-gauge theorem:** For a Hodge multiplicity presentation a and candidate genuinely algebraic native presentation b, if there is an independently constructed TRUE native finite presentation nu with coefficient mass 1 and canonical Betti class 0, define
`bSharp=b+(multiplicityMass(a)−presentationMass(b))*nu`.
Then **presentationMass(bSharp)=multiplicityMass(a)**, while **cl_can(realize bSharp)=cl_can(realize b)**. This permits an EXACT common-refinement fibered state `Phi=glueMarginals(a,bSharp)`; its true defect is `cl_can(realize b)−(basis.repr.symm a).1`. So the FULL multiplicity family can now use ANY independent native algebraic candidate without an artificial coefficient-mass constraint; it does NOT manufacture such a native candidate from an unknown Hodge alpha.

## Important positive universal geometry: find nu on every integral X in codim 1<=p<dim X

Let X be any smooth projective geometrically INTEGRAL complex d-fold, and 1<=p<d. Choose an ACTUAL very ample H; by Bertini choose p sufficiently general hyperplanes in |H| with integral, smooth positive-dimensional intersection W1; choose p sufficiently general divisors in |2H| with integral, smooth positive-dimensional W2. As formal cycle PRESENTATIONS, W1 and W2 are each ONE irreducible codim-p generator, so their native augmentation/mass is 1 each. In actual CH^p(X)_Q, their cycle products satisfy `[W2]=2^p[W1]` as rational-equivalence classes because c1(2H)=2c1(H). Thus their canonical rational Betti classes have the same degree relation. The ACTUAL finite codim-p rational source

`nu = (2^p [W1] − [W2])/(2^p−1)`

has `presentationMass(nu)=1` and `cl_can(nu)=0`. The denominator is nonzero for p>=1. This is a GENUINE, independently constructed native geometric source for all these p, not a target-Hodge representative.

**Exceptional case:** for p=d, generic complete intersections are FINITE ZERO-CYCLES, not single irreducible generators, so their augmentation is their number of points/total multiplicities, and the proposed combination's total augmentation vanishes instead of 1. p=0 also has denominator 0. The geometric theorem is restricted, not claimed in those two cases.

**Chow-vs-cycle distinction:** W2−2^p W1=0 in CH^p(X)_Q and canonical Betti cohomology, but is generally NONZERO in the free rational native cycle presentation of the distinct integral subvarieties. This distinction is precisely why its source augmentation can be nonzero even though its Chow and Betti class are zero. Do not claim equality of actual *cycle presentations* merely from rational equivalence.

## New Lean source additions

Existing `GSTClassicalHodgeFiberedCycleClassDefect.lean` has new actual theorems/definitions:
- `massBalancedPresentation` defined from actual finite point cycle presentation and full genuine Hodge basis index;
- `massBalancedPresentation_mass` proving exact augmentation equality;
- `massBalancedPresentation_cycleClass` proving full ACTUAL Stage2G cycle-class invariance;
- `gluedMassBalancedState_defect_zero_iff` explicitly assembling the actual common-refinement fibered state and identifying its zero defect with the candidate b having the required original rational Hodge Betti class. The theorem's only extra source premise is the mass-one nullhomologous nu, discharged geometrically in LaTeX for 1<=p<d.

No `sorry`, `admit`, custom axioms, or fake cycle surjectivity. **Formalization scope:** the new Lean code is conditional on the independently true geometric mass-one nullhomologous witness, not yet a Lean encoding of the Bertini/Chow proof which supplies this witness.

## Exact Wolfram computation and result

Reproduced the actual committed Wolfram script in a STATELESS kernel, SHA `ce213c32c3dab98912f5673f92cf623136524bb0`, rational arithmetic p=1..12:
- source Betti relation C(W2)=2^p C(W1);
- nu=(2^p W1−W2)/(2^p−1), has null class and mass one;
- candidate b=(W2/2^p), mass=1/2^p but correct Betti class;
- mass-corrected bSharp=(W1), mass1 and SAME Betti class;
- every p=1..12 returned exact True for all four properties.

A single symbolic identity covers arbitrary p>=1 for the algebraic equations; finite tests are an independent finite calculation. The geometry supplies a true all-X representative for p<d via Bertini and Chow.

## Project-wide meaning / next immediate use

This closes a REAL EXTRA obstruction in the common-refinement GST state: coordinate augmentation balance is always achievable from the raw algebraic geometry of any geometrically integral X in non-top positive codimensions, without needing to discover unknown Hodge-source cycles first. It transforms the earlier `exists_joint_marginals_iff` from a potential nontrivial source restriction into an explicit geometric construction. To finish the universal original-X Hodge target, the existing/native cycle source still must match an arbitrary Hodge alpha in canonical Betti cohomology; this theorem does NOT assert such an independent target-sensitive cycle. End each route with the actual new mathematics and tested status, not repeated rank-one projectors.


## Additional all-X theorem: native coefficient mass cannot factor through Betti realization

The mathematics-first LaTeX now also proves a novel nonfactorization statement for EVERY geometrically integral smooth projective X and 1<=p<dim X: there exists **no** rational-linear map `tr:H^(2p)(X,Q)->Q` such that `tr(cl_X^can(b))=presentationMass(b)` for ALL finite actual native codim-p presentations b. The explicitly constructed actual source nu has mass1 but Betti class0; any such tr would give 1=tr(0)=0. This is an unconditional geometric theorem on the stated original-X scope, not a finite computation. It establishes the strict distinction between GST raw multiplicity/counting mass and canonical projective degree / cohomology traces. It is also why mass calibration can succeed without affecting the original Betti target. The theorem is in the LaTeX and not yet a newly compiled standalone Lean theorem.
