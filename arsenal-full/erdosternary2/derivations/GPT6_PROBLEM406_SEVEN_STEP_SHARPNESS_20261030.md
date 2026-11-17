# GST Erdős 406: exact optimality of seven-step multiplicative pair forcing

**Research branch:** `gpt6/problem406-seven-step-sharpness-20261030`  
**Inherited original tip:** `b951fce952dbbed91e59febc13aaaa9695523076`  
**Source theorem:** `GSTProblem406SevenStepUniversalPair.any_positive_source_pair_within_seven`.

## New exact theorem / smallest sufficient distinguishing source

The inherited branch proves for every *positive integer* A that one of the
eight consecutive multiplicative orbit sources A,4A,...,4^7 A shares
some positive-position ternary digit two with its immediate quadruple.

The bound 7 cannot be reduced to 6 for general positive source A.
Choose A=3829, which is **not** a power of four.

For j=0,...,6, put R_j=3829*4^j. Direct exact arithmetic certifies

```text
j    R_j           common-two positions in (R_j, 4 R_j)
0        3829       none
1       15316       none
2       61264       none
3      245056       none
4      980224       none
5     3920896       none
6    15683584       none
7    62734336       2, 3, 4, 7
```

All row positions for j<=6 have been checked, not merely a fixed
prefix: for all j<=6, 4R_j <= 4*3829*4^6 = 62,734,336 <
3^17 = 129,140,163. Thus both source and neighbor digits vanish
at every row p>=17. The Fin 7 x Fin 17 exact finite certificate
handles all remaining rows 0<=p<17.

The witness at shift j=7 is already at positive ternary row p=2:
`digit3(3829*4^7,2)=digit3(4*3829*4^7,2)=2`.

This was also independently checked in Wolfram by integer division
and modular arithmetic, without approximations:
for j=0..7 the lists of all common-two positions through p=18 were
`{}, {}, {}, {}, {}, {}, {}, {2,3,4,7}`.

The corresponding new Lean file is
`GSTProblem406SevenStepSharpness.lean`; a strict kernel workflow is
`.github/workflows/gpt6_problem406_seven_step_sharpness.yml`.
Do not mark the Lean result verified until this workflow succeeds
and the #print axioms output has no `sorryAx` or new custom axiom.

## Direct mathematical consequence for Problem 406

The sharpness witness is a **countermodel to a proposed generic
six-step shortening**, not a counterexample to Erdős 406.

For A=4^K the inherited seven-step existence result is
`exists j<=7, CommonTwo(K+j)`, and the original unproved proposition
remains `CommonTwo K` for each K>=5 with K!=7. Even a very strong
bounded-gap theorem cannot transfer its witness backwards to the
specified exponent without an independently derived *perfect-power
origin* condition. The source A=3829 shows why dropping that origin
condition cannot work.

A viable future mathematical bridge would be an exact GST theorem
that confines an all-row BAD source to the 3-adic roots that are
incompatible with the finite natural exponential origin. That
exclusion must use more than finite residue counting, entropy, or
generic multiplication dynamics. No such bridge is claimed here.

## Complete current-branch commit chronology and verification warning

The GitHub REST commit history was exhaustively paginated at
`b951fce952dbbed91e59febc13aaaa9695523076`: **1,461** reachable
commits, 15 nonempty pages, from 2026-08-16T19:16:56Z to
2026-10-29T21:37:59Z. The historical `de11dc2c5ee340fee1929ba2adc6834a72ab9879`
is reachable. The exact tree has 1,776 blobs including archival snapshots;
this commit metadata audit is not a claim that every archival file's text
was semantically inspected.

The legacy `scripts/comparator.sh` only runs `lake build`, a
textual grep for `sorry`, and a success banner. It does **not**
type-check the final binder-free exact benchmark statement.
The latest baseline whole-project build passed 17,530 jobs but the
legacy comparator stopped on a false positive from the word `sorry`
in a documentation comment in
`GSTProblem406ArchimedeanPhysicalEscape.lean`.
Removing that comment false positive is not proof of the original theorem.

The actual `questions/deepmind_problem_406/Solution.lean` theorem
still has parameter `hGate : gst_four_power_third_wave_gate`.
A genuine unconditional resolution must remove that binder *by proof*,
not by renaming it or importing a custom axiom, and check the exact
final theorem's Lean kernel dependencies.
