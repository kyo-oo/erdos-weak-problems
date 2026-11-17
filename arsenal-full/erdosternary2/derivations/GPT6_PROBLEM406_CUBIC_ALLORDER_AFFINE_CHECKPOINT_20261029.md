# GST Erdős 406: 2026-10-29 cubic/all-order/affine research checkpoint

## Authoritative base and exact target

- Branch: `gpt6/problem406-cubic-universal-research-20261029`.
- Forked from `gpt6/problem406-fourth-trit-discovery-20261029` commit
  `211b3ef4b8b0edab6c6e16702d7aa579203dce77`.
- Research-history anchor: `de11dc2c5ee340fee1929ba2adc6834a72ab9879`.
- Goal is still to prove, with **no custom axiom, no hGate binder**, the
  production `gst_four_power_third_wave_gate` for all
  `K>=5`, `K!=7`, or a direct unconditional proof of the original
  exact comparator challenge. The root third-wave condition is
  equivalent to an ORIGINAL same-row ternary two of both
  `4^K` and `4^(K+1)`.

The historical September 6 comparator PASS is genuine, but its final
unconditional-looking theorem depended on custom axiom
`gst_four_power_direct_existence_inline`, as the historical Lean
kernel axiom audit recorded. See
`derivations/GPT6_HISTORICAL_406_COMPARATOR_AXIOM_FORENSICS_20261029.md`.
This branch does NOT restore that axiom.

## New exact theorem results (strict Lean kernel passed)

| Module | Scope | GitHub Actions receipt |
|---|---|---|
| `GSTWorldtraceCubicBlockLift.lean` | exact third-order physical quotient modulo up to `3^(3(L+1))`, uniformly all M,u,L | [40855392755](https://github.com/kyo-oo/erdosternary2/actions/runs/40855392755) |
| `GSTWorldtraceCubicGlobalFingerprint.lean` | cubic source-neighbor physical digit readback for **every natural K**; noncircular certificate and exact survivor obstruction | [40856098649](https://github.com/kyo-oo/erdosternary2/actions/runs/40856098649) |
| `GSTWorldtraceCubicPhysicalEscape13.lean` | new third-band pair `K=355`, row 13; ALL natural `u%59049=13` at `K=4+27u`; exact original thirdWave + CreationCertificate | [40856107657](https://github.com/kyo-oo/erdosternary2/actions/runs/40856107657) |
| `GSTWorldtraceCubicPhysicalEscape49.lean` | high-scale pair `K=35725`, row27; ALL `u%(3^21)=49` at `K=4+729u`; exact original thirdWave + CreationCertificate | [40857097112](https://github.com/kyo-oo/erdosternary2/actions/runs/40857097112) |
| `GSTWorldtraceAllOrderAffineUnification.lean` | exact untruncated source quotient for every digit depth, and equality `cumulativeWorldtrace 3 1 K = affineOrbit K` for every K; equivalence to ORIGINAL CommonTwo | [40857161200](https://github.com/kyo-oo/erdosternary2/actions/runs/40857161200) |

In the high-scale source example, modulo `3^21=10460353203`:
- source quotient residue `7080391750`,
- neighbor quotient residue `7400860594`,
- both have digit two at actual physical row 27.

This pair is different from a linear/quadratic approximation. It
requires the cubic term `tetra u*(3^(L+1))^2*c_L^3*4^M`.

## Independent exact finite audit

`scripts/gst_worldtrace_cubic_independent_audit.py` runs pure Python
integer calculations: `pow(base, exponent, modulus)`, exact Euclidean
quotients, `math.comb`, and digit extraction.

[GitHub Actions 40857356603](https://github.com/kyo-oo/erdosternary2/actions/runs/40857356603)
**PASSED**. It checks the cubic quotient for L=0..7, physical offsets
M in {0,4,5}, u in {0,1,2,3,13,31,49}, and widths
`w in {1,L+1,2(L+1),3(L+1)}`. Also checks nonlinear first physical
hits K=355 and 35725 and delayed u=2 examples L in {6,8,11,15}.
This is a finite cross-check only, not universal proof.

## Structural insight and route selection

The all-order ledger is an EXACT match to the older affine orbit:
`A_0=0`, `A_(K+1)=4*A_K+1`,
`4^K=1+3*A_K`. For arbitrary scale L, the untruncated quotient is

```
(4^(M+u*3^L) / 3^(L+1))
  = 4^M/3^(L+1)
  + c_L*4^M*cumulativeWorldtrace (3^(L+1)) c_L u.
```

This is not a new assumption: the formula follows by exact iteration
of the proved Worldtrace quotient increment. It connects GST cubic
source analysis to the historical affine-survivor controller, but
the existence of a successful original source-neighbor digit remains
a separate and presently unresolved logical statement.

The mathematical missing implication can now be stated without
surrogate objects: for each K>=5, K!=7, the literal physical
all-order source and neighbor words must share some digit 2.
Merely requiring a witness of this type under a new name would
repeat the former custom axiom and would not close the proof.

## Active proof attempts requiring their own CI receipts

- `GSTProblem406DelayedExactHGate.lean`: show arbitrary delay of the
  first simultaneous physical two, with a true hit at row L+1 whenever
  L>=6 and u%3=2. This proves any constant prefix cutoff is
  inadequate. After explicit modular residue proof repair, the targeted Lean
  workflow [40857225569](https://github.com/kyo-oo/erdosternary2/actions/runs/40857225569)
  **PASSED**. This now proves for all L>=6 and u%3=2, the FIRST
  simultaneous physical digit two is at row L+1, and for every
  finite B a genuine pair has first common two strictly after B.
- `GSTFourPowerAffineOntologicalCompleteness.lean`: use exact
  affine-prefix isometry and finite injective/surjective equivalence
  to show that every arbitrary finite ternary affine prefix is
  realized by some genuine perfect-power exponent. This would
  establish that finite-prefix source filters cannot alone
  discriminate a physical origin. Targeted workflow:
  [40857788676](https://github.com/kyo-oo/erdosternary2/actions/runs/40857788676).

The older generic all-depth controller is demonstrably insufficient:
the repository contains `GSTCanonicalSeedCountermodel.lean` and
`GSTCoupledControllerCountermodel.lean`, where a child Happy packet
coexists with a BAD parent on a NON-physical arbitrary source. A proof
that excludes every nonexceptional physical exponent must use a
global source constraint not implied by those generic controllers.

## Honest proof status and next mathematical target

**Unconditional Erdős 406 verdict: not yet certified.** The new
all-K exact digit reconstructions and infinite congruence families
are proved, not a proof that every admissible K has a hit.

The promising route is to use the exact all-order affine dictionary
together with exponent termination/absolute-size information to
exclude a *whole infinite bad path* for any actual exponent K>=5,
not to enumerate another fixed finite residue window. Exact
source-to-target comparison, no extra hypotheses and a final
`#print axioms` on the original comparator theorem are mandatory
acceptance conditions. The strict comparator must pass on that
same exact commit.
