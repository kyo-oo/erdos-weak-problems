# Mathbox: recover and discriminate Sol's 2026-10-02 cubic universal-induction attempt

**Starting source**: `sol/gpt56-de11-direct-existence-closure` (20 commits
not in the current newest mainline; additional historical source
`GSTFourPowerUniversalInduction.lean`).  
**Current research branch**:
`gpt6/problem406-rowtwo-first-hit-exact-20261030`.  
**Target** (unchanged): for every K≥5, K≠7, a physical shared ternary
digit two in 4^K and 4^(K+1).

## Recovered conditional source theorem

The historical module defines `BranchBadDescent` with three rules:
for every q, letting
`X_q=(4^q-1)/3` and `Y_q=(4^(3q)-1)/9`,

1. `BadChannel 0 Y_q -> BadChannel 1 X_q`;
2. `BadChannel 1 (4Y_q) -> BadChannel 1 X_q`;
3. `BadChannel 3 (16Y_q+1) -> BadChannel 1 X_q`.

These three hypotheses imply the original
`FourPowerDirectExistence` by a mathematical strong-induction
argument with explicit finite base cases.

The crucial original-source identity is
`Y_q = P(X_q)` where `P(X)=X+3X²+3X³`.
The repository's earlier exact classification is:

```text
¬CommonTwo(3q)   ↔ BadChannel 0 Y_q
¬CommonTwo(3q+1) ↔ BadChannel 1 (4Y_q)
¬CommonTwo(3q+2) ↔ BadChannel 3 (16Y_q+1)
¬CommonTwo(q)    ↔ BadChannel 1 X_q
```

Therefore the historical branch package is precisely a tritwise
BAD-descend implication, equivalent to the contraposed good-event
propagation `CommonTwo(q) -> CommonTwo(3q+r)` for r=0,1,2.

**Important logical calibration**: this source-restricted
`BranchBadDescent` package is NOT inherently weaker than the
original conjecture. Conversely, assume the exact original all-K
CommonTwo target. If q≥5 and q≠7, then its three children
3q,3q+1,3q+2 are ≥15 and ≠7, hence all good, making the
hypotheses of every BAD descent false. If q∈{0,1,2,3,4,7},
then q itself is BAD by exact finite arithmetic, so every
descent implication has a true conclusion. Consequently
the universal theorem implies all three historical descent
rules. The equivalence is a direct mathematical consequence of
the existing source classifiers and finite exceptional set.
It does not discharge the original theorem.

## Newly found exact generic countermodels (Python + Wolfram independent)

Removing the essential restriction `X=X_q=(4^q-1)/3`
from ANY of the three old hypotheses yields false implications.

```text
P(X)=X+3X²+3X³.
  X   P(X)   pair with CommonTwo(X,4X+1)   BAD cubic child
  52  429988       yes, row 2              BadChannel 0 P(X)
  53  455111       yes, rows 1,2           BadChannel 1 (4P(X))
  44  261404       yes, row 1              BadChannel 3 (16P(X)+1)
```

For every listed cubic child there is NO shared-two at ANY
ternary position, not only within a finite tested prefix.
The largest cubic child source is 16*261404+1 = 4182465,
strictly below 3^16=43046721. A complete Fin16 exact
digit decision handles 0≤p<16; for p≥16, the source digit is zero.
The new formal proof module is
`GSTProblem406CubicBranchCountermodels.lean`, with dedicated strict
kernel workflow `gst_406_cubic_branch_countermodels.yml`.
Do not promote it to Lean-verified until that workflow reports
success and the final #print axioms output has no custom axioms.

The examples are NOT pure-power sources: 44,52,53 are not
in the natural affineOrbit(q) sequence 0,1,5,21,85,341,...
This does NOT refute the original theorem or the three
source-restricted historical BranchBadDescent implications.

## Constructive continuation dictated by the actual obstruction

The prior attempt cannot be repaired by proving
`BadChannel c (P(X)) -> BadChannel1 X` for arbitrary integers X.
A correct derivation must exploit the exact source
`X=affineOrbit(q)` and its independent geometric/binary-origin
constraints. The exact cubic polynomial alone admits all three
counterexamples. The original final gate remains the named
all-q, source-specific BAD-destruction problem.

## Two other exact all-depth research checkpoints

1. `GSTProblem406RationalPerronBound.lean` is strict Lean VERIFIED:
   `675*1000^n*survivingCount n 1 <= 1000*2482^n`.
   Green run: https://github.com/kyo-oo/erdosternary2/actions/runs/41104097664 .
2. `GSTProblem406CarryCubicRecurrence.lean` is strict Lean VERIFIED:
   `C_(n+3)(1)+2C_n(1)=2C_(n+2)(1)+2C_(n+1)(1)`.
   Green run: https://github.com/kyo-oo/erdosternary2/actions/runs/41105185701 .
3. `GSTProblem406RowTwoFirstHit.lean` and
   `GSTProblem406PurePowerNonlocalTransport.lean` strict Lean VERIFIED:
   https://github.com/kyo-oo/erdosternary2/actions/runs/41104219555 .

These are unconditional mathematical facts about the GST
transducer, not an unconditional proof of Problem 406.
