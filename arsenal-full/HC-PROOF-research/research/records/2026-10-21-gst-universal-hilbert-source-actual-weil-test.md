# GST universal-source repair: actual Weil-fourfold test of twisted Hilbert incidence

**Date:** 2026-10-21 IST. **Original proof target:** for every original smooth projective complex X and every rational (p,p) Hodge alpha, construct an actual CH^p(X)_Q source with canonical Betti class alpha; do not replace with K0 recovery from an existing algebraic input.

**Mathematics-first correction:** [GST Hilbert-incidence derivation, new section 14](../derivations/GST_arbitrary_X_Hilbert_incidence_primitive_Euler_source_2026-10-21.tex), committed in `bfd8f97c6d37cb373a1e4fb0894ac3f10c0b422e`. No Lean file edited, no current-commit CI claim.

## Geometric discriminator (actual original variety; no Hodge counterexample)

Take an actual smooth complex abelian fourfold A of Weil type with rational NS rank one, NS(A)_Q=Q theta for an ample algebraic polarization theta, and any nonzero rational primitive Weil Hodge (2,2) class r with theta cup r=0. **A is smooth projective and the rational Hodge class exists independently of any Chow representative.** The cotangent bundle of an abelian variety is algebraically trivial rank four. Therefore, for every actual algebraic line bundle L, and every m>=0, the true twisted length-two Hilbert incidence source of the previously established scheme-theoretic construction obeys the integral K0 equality:

`F_m(L) = chi(A,L)[O_A] - binomial(m+3,4)[L].`

Under canonical Betti realization, c1(L)=ell theta for ell∈Q, so the actual rational degree-four class is

`cl(ch2 F_m(L)) = - binomial(m+3,4) ell^2 theta^2 /2.`

Its original-A canonical Hodge coupling with r is exactly zero:

`int_A r cl(ch2 F_m(L)) = 0`.

The same holds for every finite rational K0 word under ring combinations, duals and Adams operations built from the line-bundle-twisted incidence outputs, because canonical Betti Chern characters remain in Q[theta]. This disproves the **sufficiency of the named source recipe** to detect arbitrary primitive Hodge directions; it neither constructs a nonalgebraic Hodge class nor refutes the rational Hodge conjecture.

**Exact Wolfram audit:** Evaluate `chi-Binomial[m+3,4] Exp[t ell]` with rational formal series to degree four. The degree-two coefficient was `-ell^2*m(m+1)(m+2)(m+3)/48`, the correct `-Binomial[m+3,4]*ell^2/2`. The exact binomial summation `Sum[Binomial[k+3,3],{k,0,m-1}] == Binomial[m+3,4]` checked for m=0..10 (all true); the general identity follows symbolically by the hockey-stick theorem. No numerical tolerance, conjectural full-rank or target Chow witness used.

## Exact root of repeated false completion

The identity `F_0(E)-F_1(E)=E` is correct for **every independently EXISTING algebraic** perfect-complex E, but does not construct E from a prescribed rational Hodge r. Adding arbitrarily many tautological line-bundle incidence twists only produces old Betti algebra `Q[theta]` on this real Weil-type test. Consequently, declaring general K0 recovery or an algebraic factorization of a source already input as a *universal source-birth theorem* is mathematically invalid. Earlier source-stage restrictions and exact Euler identities remain valid within their typed scopes.

**Outcome:** successful audit and repaired overclaim in actual LaTeX; universal original-X source constructor was **not** derived. This is a no-go for a specific input category, not for higher-rank/non-tautological actual sheaves or the Hodge conjecture. This experiment is not a new special-family Hodge completeness theorem. No alternative unsupported source-existence result is claimed.
