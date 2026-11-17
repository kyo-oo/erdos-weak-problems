# Problem 406: source-specific GST Worldtrace fourth and fifth gate discoveries

**Research checkpoint:** 2026-10-29 UTC.  
**Base revision:** `e2ccbc451a811b6230392990d7dc36ef90219c4b` (`gpt6/problem406-hgate-discharge-20261029`).  
**Working branch:** `gpt6/problem406-fourth-trit-discovery-20261029`.

## Exact target and distinction

The benchmark demands `forall n >= 9, noTernaryDigitTwo (2^n) = false`
with **no auxiliary input**. The currently imported benchmark Solution
accepts `hGate : gst_four_power_third_wave_gate` and is conditional.

The source `GSTFourPowerThirdWave.thirdWave_iff_commonTwo` proves the
exact gate body is equivalent to one row `p >= 1` on which both
`4^K` and `4^(K+1)` have ternary digit two. The full gate
requires that body for **every** `K >= 5, K != 7`.

The original branch independently proves the body for eleven of
eighteen three-free `u mod 27` classes in the family
`K=4+u*3^L`, `L>=6`. The present work upgrades this source-specific
same-row theorem, rather than redefining or assuming the universal gate.

## Derived identities

Let `c_L = GSTCanonicalTailLTE.lteCoeff L`; the kernel-proved
Worldtrace identity is

`4^(3^L) = 1+3^(L+1)*c_L`

and its exact recurrence

`c_(L+1) = c_L + 3^(L+1)*c_L^2 + 3^(2L+1)*c_L^3`.

For any `1<=w<=L+1`, the already proved whole-block transport is

`floor(4^(M+u*3^L)/3^(L+1)) mod 3^w
 = (floor(4^M/3^(L+1)) + u*c_L*4^M) mod 3^w`.

For `M=4,5`, `L>=6`, the initial quotient vanishes
since `4^5 < 3^7`, so the full source and neighbor powers
are maintained, without an abstract BAD-controller replacement.

### Fourth new trit, all unbounded L and u

Coefficient stabilization gives `c_L mod 81 = 16`,
hence the low FOUR postcut quotient trits are
`(46u mod81)` for `4^(4+u3^L)` and
`(22u mod81)` for `4^(5+u3^L)`.

For `u mod81 in {10,40,58}`, the fourth trit in **both**
is 2. Thus `CommonTwo (4+u*3^L)` holds with witness
`p=L+4` for all `L>=6` and all such natural `u`.

The Lean proof is `GSTProblem406HGateCoreClass.commonTwo_new_fourth_trit_classes`.
Dedicated Lean CI run [40848436050](https://github.com/kyo-oo/erdosternary2/actions/runs/40848436050)
was successful on commit `e7ba34ecf5f40515e48574d6b2f8f9eda900949a`.
Wolfram independently checked **45 actual power-residue pairs** at
`L=6..10`, `u=r+81*t` for each r and `t=0,1,2`:
all had digit pair `(2,2)` at `p=L+4`.

### Fifth new trit, all unbounded L and u

The exact recurrence gives `c_L mod243=178`
for all `L>=6`; therefore the low FIVE quotient trits are
`127u mod243` (source) and `22u mod243` (neighbor).

The ten previously uncovered fifth-trit classes are

`{19,76,97,118,130,151,187,208,229,241} (mod243)`.

For every one, the fifth trit of both words is 2.
Hence the original `CommonTwo` proposition holds for
**all** `L>=6` and **all** multipliers u in each
corresponding unbounded congruence class, at row `p=L+5`.

Lean kernel-proved theorem:
`GSTProblem406HGateCoreClass.commonTwo_new_fifth_trit_classes`.
The first CI attempt failed because `by decide` lacked a `Decidable` instance
for the ten-class proposition, not because of a false residue identity.
Commit `539ea642818c5f14718c0ef9fed7164ba5e93cf0` replaced this
with ten explicit `norm_num` cases. The dedicated Lean source check
[40849695938](https://github.com/kyo-oo/erdosternary2/actions/runs/40849695938)
**PASSED**, with no errors and no `sorryAx` in printed proof dependencies.
Wolfram tested **90 actual physical power-residue pairs** at
`L in {6,8,11}` and `u=r+243*t`, `t=0,1,2`, and found
zero violations. Kernel verdict must be taken from the dedicated
`gpt6_problem406_fourth_trit.yml` run at the fifth-trit commit
`97faba71ad46916f62addcb5884a49362363e4cd`.

The integration module `GSTProblem406HGateCoreIntegration.lean` exports
these class-specific results into both the exact `thirdWave`
body and the existing `CreationCertificate` type.
Its dedicated `gpt6_problem406_new_trits_integration.yml` job
[40849695946](https://github.com/kyo-oo/erdosternary2/actions/runs/40849695946)
**PASSED**, compiling the explicit fourth/fifth same-row lemmas into the
original `thirdWave` and `CreationCertificate` types, with no extra hGate
assumption for those residue families.

## Exact finite classifier, unbounded mathematical meaning

For congruence-class certificates, reducing each arbitrary unbounded
natural u modulo 81 or 243 is a mathematically exact periodicity
argument, not a bound or sample on u. The finite computation is
confined to the residue class truth table. The proof quantifies over
all L and u and transports the class result via the exact quotient.

Among three-free residues at successive cut widths:

| Width w | Modulus 3^w | Source-neighbor classes with shared digit up through width w | Total three-free classes |
|---|---:|---:|---:|
| 3 | 27 | 11 | 18 |
| 4 | 81 | 36 | 54 |
| 5 | 243 | 118 | 162 |
| 6 | 729 | 376 | 486 |
| 7 | 2187 | 1186 | 1458 |
| 8 | 6561 | 3698 | 4374 |

These counts use the stabilized coefficients
`c_(w-1) mod3^w`, exact quotient integers, and simultaneous
digit-two windows. They are finite classification evidence only
except for classes explicitly formalized above.

## Unresolved universal obligation and failed prior routes

This document **does not assert** that
`gst_four_power_third_wave_gate` is universally proved.
The original benchmark still has `erdos_ternary_2 (hGate : ...)`.
The new infinite congruence families do not include all positive
exponents, and there remain branch descendants escaping each finite
window census.

Original `GSTInfiniteFourPowerNavigation.power_three_step_collision`
had a failing isolated Lean audit (run 40785543486, line 176),
while exact GST Ω normal forms prove a finite-seed BAD trace can end
in a perfectly BAD absorbing (0,0) tail. Thus a generic all-depth
conservation identity does not force an escape. A canonical
perfect-power fingerprint and a genuine noncircular cross-column
invariant are still necessary for that specific route.

A one-column vacuum-neutral GST U-potential satisfying all BAD
nonnegativity and Happy negativity conditions is ruled out by
`GSTProblem406UGateSeparatorNoGo.no_global_GST_happy_separator`,
so repeating that mechanism cannot bridge the missing case.

The next research route should retain full source identity while
controlling multiple adjacent carry columns or a source-dependent
phase invariant, and use actual Lean proof of all nonexceptional
K rather than merely further finite-window enumeration.
