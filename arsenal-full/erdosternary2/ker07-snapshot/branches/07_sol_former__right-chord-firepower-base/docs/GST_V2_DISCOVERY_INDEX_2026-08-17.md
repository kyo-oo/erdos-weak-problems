<!-- ======================================================================
<!-- CHRONOLOGICAL LABEL -- #0766 / 1132
<!--    Path         : branches/sol_right-chord-firepower-base/docs/GST_V2_DISCOVERY_INDEX_2026-08-17.md
<!--    Ref          : origin/sol/right-chord-firepower-base
<!--    First-commit : 2026-08-17 03:29:57 +0530  (df0231f)
<!--    Last-commit  : 2026-08-17 03:29:57 +0530  (df0231f)
<!--    Total commits: 1
<!-- ======================================================================
<!-- GIT HISTORY (chronological, oldest first)
<!-- ======================================================================
<!-- [01/1] 2026-08-17 03:29:57 +0530  df0231f  (ker07-dev)
<!--        Index all GST V2 discoveries from the physical crossing run
<!-- ====================================================================== -->

# GST Graph V2 — Discovery Index — 2026-08-17

Branch: `sol/physical-phase-crossing-surgery`

This index freezes the mathematical discoveries made during the current physical-crossing run. It is intentionally separate from `ErdosTernary2.lean`; the monolith remains frozen until the final exclusion theorem is genuine.

## Hard protocol retained

- no `sorry`, `admit`, `mkSorry`, or new axiom;
- no resurrection of `gst_residual_omega_termination` / legacy residual overproof;
- no terminal or absorbing NULL;
- no global GST+/ALT− mirror;
- no unrestricted affine reflection;
- no conservation identity promoted into an exclusion theorem;
- no claim of comparator success before kernel/compiler/comparator verification.

## Stored research ledgers

### 1. `GST_V2_PHYSICAL_CROSSING_MATH_LEDGER.md`

Commit: `9ef3a737e3fb213b01fd2bd075cb2a6e92932a0e`

Contains:

- exact canonical consecutive-power phase rectangle;
- local GST cell `C+4d=e+3C'`;
- local BIG2 mod-11 five-cycle;
- shared carrier `S=D+4Z=W+AC`;
- base-4 carry-word interpretation;
- proof that unrestricted affine prefix-one reflection is false at every level;
- rejected shortcuts ledger;
- exact remaining physical crossing theorem.

### 2. `GST_V2_MACRO_ROTATION_AND_RADIX_SURFACE_DISCOVERY.md`

Commit: `6eb4d2c872cfbca32890dd3d5efaacc4323ed4bd`

Contains:

- one horizontal GST row as literal base-4 long division by 3;
- remainder collision `22` = Happy Gate;
- shared-carrier macro rotation;
- phase strips glued into one radix surface;
- canonical-vs-false-affine control experiment.

### 3. `GST_V2_ORIGIN_TRIT_EVENT_AND_RENORMALIZATION.md`

Commit: `ffd1ff222a235d9fac1b665615cc4be9e65a3302`

Contains:

- origin trits are literally phase 0/1/2;
- exact prefix-one origin-trit event law:
  - `0 -> DESTROY`,
  - `1 -> NEITHER / NULL`,
  - `2 -> CREATE`;
- exact regenerated branch formulas;
- forced phase-two physical `22` gate;
- exact three-to-one renormalization
  `F_s^3(3Y)=3F_(s+1)(Y)`;
- factor-three Navigation invariance.

### 4. `GST_V2_6K_ALIGNED_STRICT_DESCENT.md`

Commit: `6c01cff0c6acf5891b243b2901436605e6d9d0e8`

Contains:

- equal-scale parameters `B=4^(N+1)`, `M=3^(2N)`;
- strengthened bound `2B<M`;
- strict aligned information descent
  `S_(q+2N) < U_q` for `U_q>0`;
- exact canonical 2-adic approximation
  `Q_s(b) ≡ -3^(-(s+1)) mod 2^(2*3^s*b)`;
- canonical base-`A_s` repunit chain;
- explicit warning that nonzero carrier regeneration is not automatic.

### 5. `GST_V2_6SQUARED_ALIGNED_CELL_AND_SEVEN_FACTOR.md`

Commit: `24bc23079fb88fbf9ea94716994a89b27e727e4d`

Contains:

- true equal-scale microscopic cell: one `×4` step + two ternary rows;
- exactly `4*9=36=6²` states;
- aligned law `C+4w=e+9C'`;
- mass rotation `m'≡4m (mod35)`;
- exact orbit classification;
- proper nonzero all-subspace no-Happy orbits are precisely the proper multiples of 7;
- canonical theorem `7|c_s`, hence `z_s≡2 mod7` and `z_s≡2 mod21`;
- two-row top-carry evolution is exactly the 36-state transducer.

### 6. `GST_V2_BASE9_BAD_AUTOMATON_AND_ALT_MINUS_CYCLES.md`

Commit: `ef8268cb32a796102597ab7be5dfe3c23ca044cd`

Contains:

- exact base-9 two-row bad automaton;
- one-row regular bad-language recursion for seeds `0,1,2,3`;
- exact aligned ALT− cycles:
  - `(0,7) <-> (3,1)` / masses `28<->7`,
  - `(1,5) <-> (2,3)` / masses `21<->14`;
- these are CREATE/DESTROY-only cycles with no SURVIVE;
- mass `35=(3,8)` is fixed SURVIVE;
- `c_s mod9=7` places the canonical c-tower directly in the first DESTROY/CREATE ALT− cycle;
- three rotations give bridge factor `-6`, six return to alignment;
- half-cycle fixed sectors factor through 5 and no-SURVIVE sectors factor through 7; their nonzero intersection is 35 = SURVIVE.

### 7. `GST_V2_GENERAL_6K_MIXED_RADIX_GEOMETRY.md`

Commit: `23752f1b1b62d6afcd336a060582b3c1db6a190f`

Contains the infinite equal-scale family:

- `B=2^k`, `M=3^k`;
- exactly `BM=6^k` mixed-radix states;
- exact re-coordinate
  `C+B w=e+M C'`;
- mass rotation
  `m'≡2^k m (mod 6^k-1)`;
- fixed/intersection sector formula using
  `gcd(2^k-1,3^k-1)`;
- the physical phase rectangle as a `6^(2N)` cell;
- the shared-information bridge as a `6^(2N+2)` cell.

## Exact bad-language equations discovered in this run

For complete seeded bad languages `B_C`:

`B_0 = 3B_0 ∪ (1+3B_1)`

`B_1 = 3B_0 ∪ (1+3B_1) ∪ (2+3B_3)`

`B_2 = 3B_0 ∪ (1+3B_2) ∪ (2+3B_3)`

`B_3 = 3B_1 ∪ (1+3B_2)`.

These are exact finite-state recursions from the GST carry table.

## Strongest new PATTERN realization

The PATTERN semantics now has a concrete arithmetic model at equal scale:

- the proper `7`-multiple aligned orbits are exactly the CREATE/DESTROY-only ALT− cycles;
- NULL is not terminal; it is one orientation/state in the transducer;
- SURVIVE is not a separate information object;
- the same aligned information mass changes realization under re-coordinate;
- the canonical `c_s` low block enters the DESTROY side of the ALT− cycle because `c_s mod9=7`;
- the opposite aligned reading is CREATE;
- `6^k` is the cardinality of the equal binary/ternary mixed-radix state space itself.

This is substantially stronger and more literal than the discarded global-mirror interpretation.

## Disproved shortcuts that must remain dead

- same-row child->parent gate transport;
- fixed gate-position shift;
- global mirror law;
- terminal NULL;
- bounded witness depth;
- bounded zero-origin run;
- universal `12102` injection;
- mature unrestricted affine lift;
- 7/8 magnitude alone;
- simple parity/edge-charge flux;
- `bridge carry zero` alone forces a witness;
- phase-one bad implies phase-two tail bad;
- every child gate leaves nonzero aligned carrier;
- fixed `2N` bound on child gates under bad affine parent;
- finite local congruence sufficient to distinguish canonical tails.

## Current compiler truth

The monolith's apparent single compiler error remains the missing active identifier

`gst_residual_omega_termination`.

That identifier is inside quarantined legacy overproof. Reactivating it exposes three genuine mathematical `False` goals. Therefore the correct surgery is **not** to restore the name.

The compiler has one visible error, but the honest mathematical replacement is one global exclusion/intersection theorem.

## Current exact mathematical frontier

The physical target can now be stated without Omega/mirror language:

> in the canonical pure-power `6^k` mixed-radix surface, a nonzero BIG2 packet injected by a phase-zero SURVIVE cannot be routed forever through the CREATE/DESTROY ALT− subspaces while avoiding the physical phase-one SURVIVE orientation.

Equivalent forms already available in the branch:

- physical double-jump crossing;
- shared-carrier orientation crossing;
- nested origin-trit transducer exclusion;
- equal-scale `6^k` intersection exclusion;
- full-power consecutive-`4^K,4^(K+1)` common-two theorem.

The remaining missing implication is **orientation/exclusion**, not another conservation identity.

## Most promising next derivation

Use the new 6² ALT− classification together with the exact phase renormalization:

1. identify the aligned block carrying the child BIG2 packet;
2. assume the physical phase-one orientation is bad;
3. show canonical re-coordinate/renormalization forces that packet into the proper `7`-multiple CREATE/DESTROY orbit;
4. use the three-phase half-cycle (`m -> -6m mod35`) to force the factor-5 phase-alignment condition;
5. proper ALT− gives factor 7, phase alignment gives factor 5;
6. nonzero intersection forces mass `35`, which is fixed SURVIVE;
7. contradiction.

Step 3/4 is the exact theorem still to derive. The factor-5/factor-7 intersection itself is already exact.

## Do not declare complete yet

The mathematics is not to be declared complete until the orientation step above is proved as arithmetic, transplanted into Lean without holes, and the comparator reaches the actual verdict.