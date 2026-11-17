<!-- ======================================================================
<!-- CHRONOLOGICAL LABEL -- #0800 / 1132
<!--    Path         : branches/sol_physical-phase-crossing-surgery-plan/docs/GST_V2_DISCOVERY_INDEX_CONTINUATION_2026-08-17.md
<!--    Ref          : origin/sol/physical-phase-crossing-surgery-plan
<!--    First-commit : 2026-08-17 04:41:52 +0530  (0acb653)
<!--    Last-commit  : 2026-08-17 04:41:52 +0530  (0acb653)
<!--    Total commits: 1
<!-- ======================================================================
<!-- GIT HISTORY (chronological, oldest first)
<!-- ======================================================================
<!-- [01/1] 2026-08-17 04:41:52 +0530  0acb653  (ker07-dev)
<!--        Index 11-equation, base-6, and true residual discoveries
<!-- ====================================================================== -->

# GST Graph V2 — Discovery Index Continuation — 2026-08-17

Branch: `sol/physical-phase-crossing-surgery`

This continuation supersedes the **proposed next derivation** in the earlier discovery index wherever that proposal treated the 36-state aligned re-coordinate as automatic horizontal phase transport. The orbit algebra remains exact; that physical-transport interpretation was experimentally falsified and is now explicitly prohibited.

## New stored ledgers

### 8. `GST_V2_11_EQUATION_INTERCONNECTION_MASTER.md`

Commit: `9126a3a76952652ebc4a6bd87044618c9c04b5b3`

New exact web:

- EQ2 is the complete GST event-word encoder `J=d+3e`;
- EQ3 is its directed NULL-crossing projection;
- EQ4 is first-active-BIG2 orientation;
- EQ5/EQ8/EQ11 form binary-resonance / scale / 2-vs-3 coordinates;
- EQ6 is the canonical nested origin/phase address;
- EQ10 is the binary-shadow projection of the ternary digit polynomial;
- master generating identity
  `4D_R(x)-E_R(x)=(3/x-1)C_R(x)`;
- general world projection `x=3/K`, modulus `K-1`;
- source EQ1 indexing defect recorded;
- source EQ7's 95.95%-only classifier explicitly barred from proof use;
- EQ9 retained only as a density axis.

Also records the critical correction: the aligned 36-state re-coordinate is a subspace reading, not automatic neighboring-power transport.

### 9. `GST_V2_CANONICAL_MOD35_PHASE_QUOTIENT.md`

Commit: `150a699a9a180c823f0d07c8dbd3200347d1cb36`

Contains:

- `A_s=4^(3^s) ≡ -6 (mod35)` for all `s≥1`;
- `c_s mod35` cycles `7 -> 14 -> 28 -> 21 -> 7`;
- these are exactly the four proper nonzero 7-multiple ALT− masses;
- complete binary phase quotient:
  `Q_s(b)≡0` for even `b`, `Q_s(b)≡c_s` for odd `b` modulo 35;
- hard prefix-one odd-child branch has universal parent residue `H≡23 mod35`.

### 10. `GST_V2_UNIVERSAL_ORIGIN_MODULUS_AND_PHYSICAL_36_DIGIT.md`

Commit: `5377aca897a157bb4dc6856bb10a40c8419a7bfe`

Contains two major exact bridges:

1. universal origin modulus theorem
   `Q_t(b) mod Q_t(m) = Q_t(b mod m)` for every `m>0`;
2. physical 36-information digit
   `m=floor(36*x)=C+4w=e+9C'`.

It also records that repeated base-36 shift is a **power/depth diagonal** motion, not the complete vertical word of one fixed consecutive-power pair.

### 11. `GST_V2_BASE6_BRIDGE_UNIVERSE_AND_TRUE_K1_RESIDUAL.md`

Commit: `d67ab4154c8429f7dd3e8f545814e2aee55dbfed`

Contains:

- the fundamental x2/base-3 six-state cell `a+2d=e+3a'`;
- x4 GST as two binary bridge layers;
- `NULL=00`, `ALT−=01/10`, `GST+=11`;
- microscopic pure-power coordinate
  `m_(n,p)=floor(2^(n+1)/3^p) mod6`;
- exact x4 gate pairs `(4,2)` or `(5,5)`;
- EQ5 half-phase all-BIG2 sheet;
- most important architectural reduction: the real residual `k=1` branch has `m mod3 !=0`, so only origin trits `1` and `2` occur;
- the `0 -> DESTROY` branch is not part of the true final k=1 seam.

### 12. `GST_V2_MICRO_BRIDGE_TABLE_AND_NESTED_BINARY_QUOTIENTS.md`

Commit: `b6c2a9568f41d5543767157482f029db76d4ce0e`

Contains:

- complete 12-cell x4 -> two-x2-event decomposition;
- phase one = `CREATE -> DESTROY`;
- phase two NULL gate = `DESTROY -> CREATE`;
- GST+ gate = `SURVIVE -> SURVIVE`;
- global EQ2 event word satisfies `sum J_p 3^p = 13R`;
- nested binary quotient tower `M_t=Q_t(2)` with `M_t | M_(t+1)`;
- every higher canonical multiplier has order dividing two in each lower quotient;
- parity classification of `Q_s(b)` in every `M_t`;
- odd prefix-one child gives `3H≡-1 (mod M_t)` for every `t≤s`.

## Additional exact discoveries not to lose

### EQ2 global factor 13

With `J_p=d_p+3e_p`,

`sum_p J_p 3^p = 13R`.

Thus factor 13 is the global weight of the GST event encoding. Together:

- factor 5 comes from the EQ10 / `x=1/2` world projection;
- factor 7 comes from the `8` bridge / ALT alignment;
- factor 13 comes from EQ2's complete event word.

The first nested binary quotient is

`M_1=Q_1(2)=455=5*7*13`.

### Fundamental x2 event masses

For `m=a+2d`:

- `2 = CREATE`;
- `4 = DESTROY`;
- `5 = SURVIVE`.

The hard canonical `b≡1 mod3` origin cell is the hidden-BIG2 pair

`(2,4)=CREATE -> DESTROY`.

The forced `b≡2 mod3` cell is

`(4,2)=DESTROY -> CREATE`,

which is a full x4 NULL Happy Gate.

### True residual modulo-27 cylinder already closed

In the actual `k=1` residual, `n mod3∈{1,2}`. If

`n≡4 (mod9)`,

then

`b=1+3n≡13 (mod27)`.

`NavigationResidueCutScratch.lean` already proves for `s≥2` that this class has

`Q_s(b)≡19 (mod27)`,

and residue 19 supplies a NULL Happy Gate at position two.

Thus one complete infinite cylinder of the true final residual is already discharged by existing green residue-cut mathematics.

## Structural theorem explaining why finite shortcuts fail

For every finite ternary depth `L`, the canonical map

`n mod3^L -> H_s(n) mod3^L`

is a 3-adic permutation/isometry (composition of the canonical `Q` tree isometry with an affine unit map).

Therefore arbitrary finite bad parent prefixes can be shadowed by canonical origin prefixes. No fixed local modulus, bounded witness depth, bounded synchronizer length, or finite-prefix classifier can by itself prove the universal crossing.

The genuine discriminator has to use global compatibility of all finite coordinates — equivalently the inverse-limit origin — together with the fact that the original origin is an ordinary natural integer and the exact finite offset/multiplier accumulated by the origin transducer.

Important correction: origin exhaustion `n->0` does **not** make the physical state bare `z_t`; the origin transducer retains finite offset and multiplier coordinates. The terminal state is `(offset,multiplier,0)`, not a terminal NULL state.

## Current exact final seam

The real final k=1 residual has only two first-origin cases:

1. `m mod3=1`:
   - first parent-tail event is NEITHER;
   - parent seed regenerates `1 -> 0` (NULL);
   - exact suffix is a nested prefix-one affine state with retained finite offset.

2. `m mod3=2`:
   - first event is CREATE;
   - parent seed stays `1`;
   - exact suffix is the phase-two affine state with retained finite offset.

The final theorem must show that neither branch can support a complete seed-retaining bad trace under the **canonical pure-power/origin constraints**.

## Current best representation of the missing theorem

At microscopic scale, a full x4 Happy Gate is exactly

`exists p, (m_(2K,p),m_(2K+1,p)) in {(4,2),(5,5)}`,

where

`m_(n,p)=floor(2^(n+1)/3^p) mod6`.

At canonical-origin scale, the same orbit is indexed exactly by

`Q_t(b) mod Q_t(6^k) = Q_t(b mod6^k)`.

Thus the missing exclusion is now an intersection theorem between:

- the **physical 2/3 bridge table** (base-6 microscopic masses), and
- the **canonical finite-origin coordinates** (the exact `6^k` Q-embedding),

with CREATE/DESTROY/SURVIVE already completely classified locally.

No remaining work should revert to a global mirror, residual Omega termination, terminal NULL, or unrestricted affine lift.
