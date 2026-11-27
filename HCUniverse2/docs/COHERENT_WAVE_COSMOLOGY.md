# Coherent wave cosmology and exact reconstruction

Research extension of HC-PROOF, based on commit
`fac6f12f280b4c507cd2dfcab0682ed2f8b9a94f`.

The source is `GSTCoherentCosmology.lean`. The development uses the existing
GST cell operators, mixed density, ontological current, frozen-window tower,
and rectangle/no-erasure laws. It introduces no new axioms or boundary
hypotheses. Verification receipts are recorded below after the build.

## 1. The mechanism recovered from the source

The mathematical starting point is the exact twelve-cell transducer

    o(C,d) = (C+4d) mod 3,       c(C,d) = floor((C+4d)/3),
    0 ≤ C < 4,                 0 ≤ d < 3.

The seven-axis vertices record position, next position, carry, carry-space,
digit, remaining horizon, and quotient descent. The NULL/ALT-/GST+ labels
are classifications of this carry coordinate. They do not introduce extra
unconstrained states.

The following are the load-bearing parts of the framework.

| Mechanism | Exact role | Source |
|---|---|---|
| Cardinal Worlds | Binary/ternary factors, dual tower identities, bridge transport, signature cases | `CardinalWorlds.lean` |
| Physical lattice | `×4` output glues horizontally; next carry glues vertically | `GSTCanonicalSevenAxisBridge.lean`, `GSTGraphV2ProductionLaws.lean` |
| Mixed emergence | Mixed density = horizontal boundary difference + weighted vertical difference + microscopic SURVIVE source | `GST2DMixedEmergence.lean` |
| Ontological current | A second density whose positive sector is exactly Happy; reverse-base-seven accumulation prevents erasure | `GSTGraphV2Ontological.lean` |
| Synchronized shadows | Six-adic resolution equals simultaneous dyadic and triadic resolution; multiplication by `4^t` has exact asymmetric depth action | `GSTGraphV2SixAdicSynchronizedShadows.lean` |
| Coupled controller | Child/parent information transports with its exact invariant | `GSTGraphV2InfiniteControllerBridge.lean` |
| Past/Future ledger | Consumed information remains in the emitted prefix; a zero quotient is not lost history | `GSTInfiniteCoupledLedger.lean` |
| Anchored cocycle | Adjacent intervals compose with an explicit scale factor and retained phase | `GSTGraphV2HandwrittenAnchoredCocycle.lean` |
| Omega tower | Exact cut factorization and stabilization modulo increasing powers of three | `GSTGraphV2OmegaWaveLaw.lean`, `GSTTailFFourthDimension.lean` |
| Worldtrace | Finite polynomial windows read powers at controlled precision | `GSTWorldtraceArithmetic.lean` |
| Relative precision | Separates automatic divisibility from additional information; terminal conclusions retain their stated inputs | `GSTWorldtraceMahlerRelativePrecision.lean` |
| Wave layers | Mixed/source readouts, channel windows, interference decomposition, finite rotation and ignition certificates | `waves/` |

The baseline contains 136 Lean files and 33,473 lines. A module inventory was
made across the complete source tree; close proof reading focused on the
foundations and dependencies used here. This is not a claim that every line
of every imported proof has received a separate human-style audit.

## 2. The first obstruction: a stationary controller

The original `ControlledTower` requires both

    level j = bridge j (level j)
    level (j+1) = bridge j (level j).

Consequently `level (j+1) = level j`, hence every level equals level zero.
`old_controlled_tower_stationary` proves this for every carrier type.
The old dimension theorem counts satisfied ledger clauses; it does not
establish independent degrees of freedom in changing tower values.

The extension retains the original structure and defines a stronger
working space for the intended changing-resolution interpretation:

    0 ≤ X_k < 3^k,
    X_s mod 3^k = X_k whenever k ≤ s.

This is `WindowTower`. New levels may contain new information. Every old
window is preserved exactly. The existing Omega tower inhabits it:

    X_k(core) = omegaCutWord(k−1,1) · core mod 3^k.

The proof uses `omega_tower_word_mod_chain`. For core 1, the first nonzero
levels are 1, 7, 16. Thus nonstationarity has an actual GST witness.

## 3. The two-current reconstruction law

Define the paired current

    J(C,d) = (mixedDensity(C,d), ontDensity(C,d)).

The full table is:

| C | d | Mixed density | Ontological current |
|---:|---:|---:|---:|
| 0 | 0 | 70 | −54 |
| 0 | 1 | 112 | −21 |
| 0 | 2 | −56 | 84 |
| 1 | 0 | 0 | −21 |
| 1 | 1 | 210 | 0 |
| 1 | 2 | −112 | −33 |
| 2 | 0 | 112 | 0 |
| 2 | 1 | 42 | −54 |
| 2 | 2 | −56 | 0 |
| 3 | 0 | 168 | −33 |
| 3 | 1 | 0 | 0 |
| 3 | 2 | 70 | 42 |

Every pair is different. `dual_current_separation` proves injectivity;
`decode_current` proves a concrete decoder recovers every legal cell.

Mixed amplitude alone is insufficient: `(0,0)` and `(3,2)` both read 70.
Combining the two existing currents removes every collision. This is an
exact reconstruction result, stronger than the implication “digit two
has nonzero mixed amplitude.”

The new pair is Wave I's mixed amplitude plus the ontological current. It
is not the existing `twoWaveFrame`, whose second coordinate is a digit
difference. These are explicitly different observations.

## 4. Infinite worlds with finite observations

At tower time t and height p, read the finite representative

    E = 4^t X_(p+1),
    C_X(t,p) = carry4(E,p),
    d_X(t,p) = digit3(E,p).

For every K ≥ p+1, `finite_realization` proves the same cell is obtained
from `4^t X_K`. The precision K depends on observation height, not on t.
The entire horizontal orbit below a fixed height has a finite
representative, however long the orbit is followed.

This gives both exact lattice edge laws on every coherent tower:

    o(C_X(t,p),d_X(t,p)) = d_X(t+1,p),
    c(C_X(t,p),d_X(t,p)) = C_X(t,p+1).

The two-current observation is `J_X(t,p)=J(C_X(t,p),d_X(t,p))`.

**Central theorem — `finite_observation_equivalence`:**

    X_K = Y_K
      iff
    for every t and every p<K, J_X(t,p) = J_Y(t,p).

The reverse implication needs only t=0. Decode the trit at each height,
then reconstruct successively with

    X_(p+1) = X_p + 3^p d_X(0,p).

Thus the paired wave observations are a complete description of the
finite worlds. Equality at a finite resolution is neither guessed from
a picture nor defined as equality of observations; the equivalence is
proved from the source arithmetic.

## 5. Independent innovations and complete presentation

For any sequence `a : Nat → Fin 3`, set

    P_0 = 0,
    P_(n+1) = P_n + 3^n a_n.

`stream_prefix_bound` and `stream_prefix_coherent` construct a
`WindowTower`. `stream_tower_injective` proves different streams cannot
produce the same tower. `wave_stream_injective` proves different streams
cannot produce the same complete two-current trace either.

`unique_innovation_presentation` gives the converse: every coherent tower
has exactly one innovation stream, obtained by reading its trits at t=0.
This is a classification, with existence and uniqueness in both directions.

At each depth, `three_way_extension` supplies all three distinct next
windows. `unique_finite_signature` proves every depth-K observation has
exactly one representative in `Fin (3^K)`. Every such representative is
realized by a natural tower. Consequently there are exactly `3^K`
attainable depth-K signatures. Here “K independent trit choices” has an
explicit reconstruction meaning; it is not a claim about vector-space
or cohomological dimension.

`no_countable_catalogue` proves a stronger size statement: every proposed
natural-indexed list of coherent worlds misses a coherent world. The proof
constructs its trit at position n to differ from world n at that position.
All these worlds obey the same exact edge and finite conservation laws.
Their distinct level families are observable by the reconstruction theorem.

There are also towers with no single natural number representing all
their windows. The all-two tower satisfies

    X_K + 1 = 3^K.

`all_two_not_natural` proves it differs from `naturalTower R` for every
natural R. This rules out the possibility that the new space merely
renames finite natural energies.

## 6. The physical laws extend with the worlds

`tower_rectangle_gauss` lifts the existing GST rectangle identity to every
`WindowTower`. The proof supplies the two exact edge gluings to
`mixed_rectangle_emergence`. The top boundary is kept explicitly.

`tower_no_erasure` lifts the ontological domination law:

    a Happy cell at the top of the left edge
      implies
    positive weighted current across every nonzero-width block below it.

Both laws apply to non-natural infinite inhabitants as well as finite
energies and Omega towers. They introduce no global summation of an
infinite current and require no unproved convergence exchange: each
statement quantifies over every finite rectangle.

## 7. Proof boundaries

The new module requires only the explicit tower compatibility and the
stated local Happy premise for the no-erasure theorem. None of its
theorems assumes `hTailF`, `MahlerSharp`, `WorldtraceScaledCompression`,
or a monolith boundary proposition.

The repository's broader terminal theorems must still be read with their
actual binders. A definition of a proposition and a theorem assuming that
proposition are not proofs of the proposition. This extension does not
change their logical status.

The result here is a precise extension of the GST arithmetic framework:
coherent infinite inhabitants, exact wave reconstruction, independent
innovations, and inherited finite physical laws. No claim of resolving
the Hodge conjecture, a fluid PDE, or an Erdős conjecture follows merely
from these constructions. No claim of priority over existing mathematics
has been established by a literature review.

## 8. Verification

- Baseline commit `fac6f12f280b4c507cd2dfcab0682ed2f8b9a94f`:
  GitHub Actions run `35524151180` succeeded.
- New source: `GSTCoherentCosmology.lean`, with explicit kernel axiom reports.
- Branch workflow: `.github/workflows/coherent-wave-cosmology.yml`.
- The workflow compiles the new module, checks its axiom reports, then runs
  the repository's complete comparator.
- Independent finite arithmetic checked all 12 paired-current states,
  all 1,092 signatures at depths 1 through 6, and 25,515 instances of
  finite realization and the two edge laws. These computations support
  diagnosis; the universally quantified results are the Lean theorems.
