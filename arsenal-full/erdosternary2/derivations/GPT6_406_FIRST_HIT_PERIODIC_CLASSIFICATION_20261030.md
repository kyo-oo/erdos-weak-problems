# Mathbox GST Problem 406 — exact row-two first-hit and universal-gate dependency audit

**Branch:** `gpt6/problem406-rowtwo-first-hit-exact-20261030`  
**Base SHA:** `72da465559e2b46816bbfdf39b7be0c3f510bc94`  
**Target:** `∀ K : Nat, 5 ≤ K → K ≠ 7 → CommonTwo K` exactly; no extra input, no hidden axiom.

## Reachable history and tree

The GitHub REST API returned all 16 commit pages for the base SHA,
100 commits on pages 1–15 and 39 on page 16: **1,539 reachable commits**,
from 2026-08-16T19:16:56Z to 2026-10-30T16:36:37Z.
The referenced historical commit
`de11dc2c5ee340fee1929ba2adc6834a72ab9879`
is reachable at zero-indexed position 295 from that tip.
Its patch disables an auxiliary omega workflow's automatic push trigger;
it does not establish an unconditional theorem.

The new branch's complete nontruncated recursive tree contains 1,821
tree entries / 1,684 blobs: 1,138 archived `ker07-snapshot/`
blobs; 254 non-archive `.lean` source files; 21 `derivations/`
docs (prior to this document). This is a metadata inventory;
not all 1,138 archival file contents were individually reread.

## Historical comparator versus current theorem

September 6 V5 comparator PASS is authentic but the archived kernel
axiom print included `gst_four_power_direct_existence_inline`.
The current `questions/deepmind_problem_406/Solution.lean`
still declares `erdos_ternary_2 (hGate : gst_four_power_third_wave_gate)`.
That gate is definitionally linked via
`GSTFourPowerThirdWave.fourPowerDirectExistence_iff_thirdWave`
and `thirdWave_iff_commonTwo` to the exact fixed-K universal
simultaneous-two statement. Neither a clean build nor a renamed hGate
constitutes its proof.

Verified source-specific reduction at the branch base:
for K≥13, `CommonTwo K` is equivalent to a shared digit at some
`1 ≤ p < ceil(24*K/19)`, with no relaxed source domain.
The main point requiring discovery is a uniform all-K impossibility
of a BAD path for the literal source `4^K`.

## New exact GST first-hit law (source file)

Source: `GSTProblem406RowTwoFirstHit.lean`.
Use the established kernel identity `pow4_digit_period`
at p=2, so the simultaneous-two predicate at p=2 has
exponent period 9. Its first nonnegative future hit depends
exactly on `K mod 9`:

| K mod 9 | least shift j for a row-2 same-digit pair |
|---:|---:|
| 0 | 5 |
| 1 | 4 |
| 2 | 3 |
| 3 | 2 |
| 4 | 1 |
| 5 | 0 |
| 6 | 0 |
| 7 | 7 |
| 8 | 6 |

Consequently
`(∃ j ≤ 6, RowTwoGate (K+j)) ↔ K mod 9 ≠ 7`.
At K mod 9 =7, the first row-two event is at exactly j=7.
This is sharp ONLY for row 2. It does not exclude
earlier common-two events at higher ternary rows.

The finite certificate explicitly proves both existence and the
absence of earlier row-two hits for all nine residue classes.
The physical extension is by exact exponent periodicity, not
sampling. WolframLanguageEvaluator independently recomputed the
nine least shifts. Do not mark as kernel-proved until the
dedicated strict CI workflow completes with clean axioms.

## Three mathematically distinct research mechanisms and outcomes

1. **Source-specific digit-period / first-hit classification.**
   The new theorem settles the entire fixed row-two first-hit
   mechanism. Any remaining K mod 9 = 7 requires information at
   higher ternary positions, not another row-two residue check.

2. **Physical cofactor-one nonlocal collision.**
   `GSTInfiniteFourPowerNavigation.power_three_step_collision`
   fails at the concluding sign step. Exact source K=8 phase
   data and source-independent countermodels disprove the
   local propagation mechanism, while leaving the source-specific
   global all-K gate unresolved. Existing exact terminal-U
   identities do not supply the required global sign inequality.

3. **3/2 dyadic BAD exclusion / finite candidate reduction.**
   Prior exhaustive candidate sweeps through ternary length 260
   found only the known K=7 exception. This is finite evidence,
   not universal exclusion. The weaker all-R 4L/3 valuation
   barrier is disproved by the certified 47-trit BAD example
   `143*2^67`. Any induction must use carry-state transitions
   and literal power-of-four origin rather than extrapolating
   finite injectivity.

## Release gate

A valid final result must remove the `hGate` binder from
`questions/deepmind_problem_406/Solution.lean` by a proof term;
it must type-check the EXACT original challenge statement and
have a `#print axioms` output free from `sorryAx` and all custom
mathematical existence axioms. The same exact commit must then
pass the comparator. No such promotion is made here.


## Independent exact finite test, 2026-10-30

The included reproducible script
`scripts/gst_406_exact_first_hit_scan.py` computes the actual
numbers `4^K` and `4^(K+1)` for each K, searching each positive
ternary digit row until the source has no remaining nonzero digits.
It does not impose a fixed digit window or use a hypothetical gate.

Executed `python3 scripts/gst_406_exact_first_hit_scan.py --max-k 50000`.
Of 49,996 exponents K=5,...,50,000, precisely K=7 lacked a
common-two position. Maximum encountered earliest row: p=64 at
K=26,849. New earliest-row record observations are
`[(5,2),(8,4),(9,7),(10,10),(13,14),(39,20),(103,27),
(165,28),(183,29),(310,40),(497,41),(3847,46),
(13022,47),(21904,49),(25713,61),(26849,64)]`.
These are finite computational receipts, never an all-K proof.
