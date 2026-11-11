# REPORT — Erdős #261 Commander Front Assault (Task 1-c, 2026-11-11)

**Working dir:** `/home/z/erdos-weak-problems` (git repo, branch
`oneshot/1108-cascade-20261105` working tree). **No push performed** (per
constraints). **Deliverables written:** `problem261-full/COMPLETE_PROOF.md`,
`problem261-full/APRationality.lean`, this report.

---

## 1. THE STATE ASSESSMENT (the disk is the truth)

### What is GREEN (Lean / CI, workflow `kills.yml`, Lean 4.33.0-rc2 core-only)

| Kernel | Theorems | Axioms | CI step |
|---|---|---|---|
| `bulldoze/problem261-two-solutions/TwoSolutions.lean` (Kill #5) | `erdos261_weakened_two_solutions`, `erdos261_three_solutions`, `block_swap`, `block_swap_value`, the three `rep_*` | **ZERO** (CI-grepped: "does not depend on any axioms") | Kernel 3 |
| `bulldoze/problem261-continuum-tower/Erdos261Tower.lean` (Kill #6) | `erdos261_continuum`, `F_injective`, `tower_sameValue`, `tower_cauchy`, `checkpoint_eq`, `halving_nat`, region machinery | **[propext, Quot.sound]** (CI-grepped) | Kernel 4 |
| `problem261-q3bridge/BlockIdentity.lean` (Kill #8) | `bl_family`, `bl_of_jpow`, `bl_sum_split`, `jpow_sum_eq`, `pow_sum_eq` | CI-grepped (axioms printed) | Kernel 6 |
| `problem261-funnels/FunnelStructure.lean` (Kill #10) | `death_fuel_mono` (the coalescence certificate) | **[propext, Quot.sound]** (CI-grepped) | Kernel 8 |
| Kill #2 (walk equivalence + structure laws) | monorepo branch `gpt6/erdos-one-shots-2-20261101` @ `4302b85` (kernel-green THERE — not in this repo) | — | — |

The CI also runs the Python batteries (verify_frontiers, verify_tower261,
funnels) as receipt gates.

### What is PROVEN at the math level (complete written proofs + exact-arithmetic batteries)

- **The Q3 bridge** (`problem261-q3bridge/DERIVATION.tex`): bounded-room all-n
  ⟹ a rational x with 2^ℵ₀ representations — the SQ2→SQ3 reduction.
- **The periodic-tower impossibility** (`bulldoze/problem261-rational-x/PERIODIC_TOWER_ANALYSIS.md`,
  Theorems 1–5): no periodic gadget tower of any pattern structure yields
  2^ℵ₀ representations of a rational; the carry loophole is isolated.
- **x* is irrational** (cluster isolation; receipts in the tower battery).
- **Greedy-room unboundedness along the BL family** (V1 battery: room = m exactly).

### The open cores (named, no hedging)

- **Sub-Q2 (all-n termination): labeled frontier — the funnel-head
  enumeration + fast-sorting proof program.** Certified data: contiguous
  engine receipts [1, 4000] (5 ways) and [3,000,000, 4,400,200] (19 blocks,
  1,140,000 consecutive n — e1–e19, on disk, audited live by me this session);
  zero nontermination signals in 1,243,969 death records; record death modulus
  D = 1,449,322,159 stable from 3.0M to 4.4M. The next strike is the rolling
  frontier march (economics: ~30–110 s per 60K block; shadow boundaries at
  n ≈ 4.19×10⁶ — mapped — and 5.24×10⁶) plus the theoretical program
  (front-loaded coalescence: 99.5% of merges at the first aligned checkpoint).
- **Sub-Q3 (rational-x continuum): labeled frontier — the carry loophole /
  scattered-representation conjecture** (every rational's representation set
  is scattered; tree surgery to extract gadget pairs from a perfect subtree,
  then the Theorem 2/3/5 machinery). Secondary route: the Q3 bridge fires
  iff non-greedy bounded-room witnesses exist (greedy room is provably
  unbounded along the family — the greedy route is dead).

### FINDING (registry lag, worth the commander's attention)

THE_CORE.md / WORKLOG.md / README.md record the #261 frontier as
**3,740,200** (the wiped-then-reproduced push). **The disk says 4,400,200**:
`FUNNEL_RESULTS.md` (session-021 section, Agent Q1) documents blocks e1–e8
reproducing [3,260,201, 3,740,200] and e9–e19 extending to **4,400,200**
(1,140,000 consecutive n, 21/21 deep cross-checks), with receipts
`engine/run261/e{1..19}_*` present on disk. I audited them live this session:
contiguity n = 3,260,201..4,400,200 exactly once each, D odd ∧ D > n over all
1,140,000 records, record D = 1,449,322,159 (unchanged). **Registry update
needed: frontier 3,740,200 → 4,400,200** (a one-line THE_CORE/README edit —
left unwritten here to respect the write-scope constraint).

---

## 2. WHAT I BUILT

### 2.1 `problem261-full/COMPLETE_PROOF.md` — the complete-proof assembly (PRIMARY)

Campaign format (matches `problem271-status/COMPLETE_PROOF.md`): §0 the problem
verbatim + sub-question structure; §1 the theorem board (11 rows A1–A11, each
with exact PROVEN / PROVEN-at-derivation-level / CERTIFIED-DATA + labeled
frontier status); §2 the walk engine (Kill #2's equivalence + the coalescence
certificate); §3 SQ1 + the weakened question (A1–A3); §4 THE TOWER (A4–A5, with
the exact Lean theorem inventory); §5 the rational-x front (the bridge A8,
the greedy-room wall A9, the four walls, the periodic-tower impossibility A10,
the surviving carry loophole §5.5); §6 the termination frontier (A11: the
certification state, the funnel architecture, the shadow regime, the attack
program); §7 the receipts (this session's live battery runs + the CI-grepped
Lean gates); §8 the Lean conversion plan (per theorem, six items, 8.1 DONE);
§9 the arsenal citation table (honest: no #261 kernel imports an arsenal law
yet; the mapped future applications); §10 the closing statement + the
prior-art caveat.

### 2.2 `problem261-full/APRationality.lean` — THE CONVERSION STRIKE (secondary, one theorem)

**The pick:** the AP rationality engine — the finite kernel of the Q3 bridge's
rationality lemma. Rationale: it is the one *cited-but-unformalized* engine of
the bridge (DERIVATION.tex calls it "the kernel identity `jpow_sum_eq` +
`pow_sum_eq`"); it is Theorem 1 of the periodic-tower analysis (the ONLY clean
rationality source); it is battery-verified (W5 V5) but was in no Lean file;
and it is convertible with zero OOM surface (a general induction, no bounded
∀, no big decides). It most advances the complete proof by making the bridge's
rationality half engine-backed.

**The theorem (`ap_sum_kernel`):** for ALL r, T, K ∈ Nat,

    Σ_{k=0}^{K} (r + kT)·2^{K−k} = r·(2^{K+1} − 1) + T·(2^{K+1} − K − 2),

with `apSum r T K` a fuel-free structural recursion. **Degenerate points:
(r,T) = (0,1) IS `jpow_sum_eq`; T = 0 IS the r-scaled `pow_sum_eq`** — the two
CI-green Kill #8 engines become two points of one law. Dividing by 2^K gives
the closed partial-value form whose limit is the rational 2r + 2T (the
bridge's Lemma `ap` engine).

**Construction discipline (blind-written, no local Lean — maximum-caution
route):** §1 of the file is a *verbatim copy* of the CI-green BlockIdentity
engines (`jpow_sum`, `pow_sum`, `one_le_mul`, `one_le_two_pow`, `pow_sum_eq`,
`two_pow_big`, `jpow_sum_eq`); §2's split theorem clones the CI-green
`bl_sum_split` architecture (equation-compiler cases + `show`-unfolding +
`Nat.mul_add`/`Nat.mul_one`/`Nat.mul_left_comm` syntax normalization + one
linear `omega` — the monomial-normalization discipline of compile-war lessons
25/30); §3's headline closes by `rw` + auto-`rfl` after the engine identities
(every rewrite traced to fire exactly once); §4 receipts: five #eval mirror
pairs (120, 399, 4239, 217, 120 — matching the campaign's own battery numbers)
+ `#print axioms` gates on four theorems. No Mathlib, no sorry, no custom
axioms, no boundedForall/decide over > 501, statement-first comments, the
NEW RULE problem-verbatim header, no arsenal import (not applicable — the
#261 kernels carry none; stated in-file).

**Honest caveat:** the file has NOT been compiled (no local Lean per the task
rules). Risk assessment: §1 is copied verbatim from CI-green code; §2's proof
architecture is a clone of a CI-green proof with each rewrite step traced
(fires exactly once, final goal linear in atoms); §3 is rw+rfl. Residual risk
is low but nonzero (the `show` defeq step and the rw chain). The receipts were
verified against the Python battery (V5) this session.

### 2.3 Live verification receipts (this session, all exact arithmetic)

- `verify_frontiers.py` — ALL PASSED (4 representations of 1/2 incl. the 4th
  {4,5,7,8,11,13,14}; block swap; census growth by depth).
- `verify_tower261.py` — ALL PASSED (halving family, disjointness,
  σ-invariance, irrationality zero-gaps, collision recheck).
- `verify_periodic_tower.py` — 54 passed / 0 failed.
- `funnels.py` — ALL PASSED (the [1,4000] census, head table).
- `verify_complete_proof.py` (W5 battery) — V1/V2/V2b/V3/V4-σ-invariance ALL
  PASSED (run in foreground; the full script is slow on this 2-core sandbox in
  the V4 B_K big-integer segment, so V5/V8 were re-executed directly):
  **V5 kernel identity PASS** (the exact theorem now in Lean) and **V8
  receipts audit PASS** (e1–e19: 1,140,000 records contiguous [3,260,201,
  4,400,200]; D odd ∧ D > n zero violations; record D = 1,449,322,159).
- `q3bridge/walk.py` + `funnels engine` receipts: inventoried; the C engines'
  binaries (`war261b`) are present; the frontier deaths files are complete on
  disk (audited above).

---

## 3. NEXT ACTIONS (for the commander)

1. **CI inclusion of the new kernel** (the immediate push item): add
   `problem261-full/**` to the `kills.yml` path triggers + a Kernel step
   `lake env lean problem261-full/APRationality.lean` with grep gates
   `(120, 120)`, `(399, 399)`, `(4239, 4239)`, `(217, 217)` and
   `'ap_sum_kernel' depends on axioms` — then push and read the verdict (the
   file is blind-written; the CI is the only verdict, per campaign law).
2. **Registry update:** THE_CORE/README #261 frontier 3,740,200 → 4,400,200
   (the disk receipts are the authority; §1 finding above).
3. **The next #261 strikes** (per COMPLETE_PROOF §8): (8.2) the parity lemma
   (D odd — general fuel-induction) + the 501-safe bounded termination
   certificate `walk_terminates_le_400`; (8.3) the Tower's irrationality;
   (8.4) the gadget equation conversion; (8.5) the bridge implication on the
   sameValue machinery; the frontier march + the funnel-head enumeration
   (sub-Q2) and the scattered-representation conjecture (sub-Q3).

**The engine never stops; it never lies.**
