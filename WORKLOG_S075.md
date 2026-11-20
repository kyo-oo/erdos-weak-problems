# WORKLOG S075 — THE DUST-LAW ROUND (sorry-kill + the exact doubling + the protection system)

**Session type:** hypothesis assault continuation (BOSS order: "TARGET #406 ONLY...
crack the HFTAIL hypothesis completely... read the commit history... build a
system that protects the sandbox even if we completely reset it"). English only.

## The intake

The zip bag recovered from the Drive link (token restored, repo re-synced from
`fa4a160` to the live `campaign` HEAD `934fa6f`, 139 commits — the latest
branch entirely, as ordered). The #406 history read in full: COMPLETE_PROOF.md
§1–§10 (the census, the parity law, the mod-8 budget, the semantic law, the
cap-law reduction), WORKLOG_S074 (the war council record), the kernel-b CI
failure log (run 44645520793: six elaboration errors auto-inserting sorryAx
into ten lemmas), the caplaw artifacts (v2star_table, dust_census, battery).

## Deliverable 1 — THE SORRY-KILL (Kernel 68, CapLaw406.lean)

Root-caused all six CI errors by reading the Actions log directly:

| line | error | fix |
|---|---|---|
| 120 | `rw [Nat.pow_succ]` leaves `2^j * 2 = 2 * 2^j` | append `Nat.mul_comm` |
| 134 | `decide` after a closed rw chain ("No goals") | drop the decide |
| 170 | `Nat.mul_le_mul (le_refl _)` type mismatch (heq rewrote both sides) | calc with `Nat.mul_le_mul_left` |
| 194 | double `rw [Nat.pow_succ]` pattern loss | calc with `Nat.pow_succ a (f+1)` explicit |
| 201 | `rw [Nat.pow_mul, Nat.mul_comm]` direction (goal RHS already flat) | `rw [← Nat.pow_mul, Nat.mul_comm]` |
| 349 | `hRider : ¬(... = false)` fed to a `= true` slot | Bool case split (`cases h :` + `absurd`) |

The reduction kernel now compiles with ZERO sorry: the rider squeeze, the
rider bound, the Postulate-II instantiation, the C=185 retargeting, and the
census composition — all machine-checked, axiom-receipted.

## Deliverable 2 — THE DUST LAW (DustLaw406.lean, new kernel)

THE EXACT DOUBLING THEOREM: **`|alive[j]| = 2^j` at every level, forever** —
the census's verified-to-level-12 doubling is now a theorem with no ceiling.
The engine chain, all unconditional:

1. **`four_pow_3j_struct`**: `4^(3^j) = 1 + 3^(j+1)·c`, `c ≡ 1 mod 3` (cube
   induction on the Arsenal's `cubic_expansion`).
2. **`binom_cong`**: `(1 + 3^(j+1)·z)^t = 1 + t·(3^(j+1)·z) + 3^(j+2)·K`.
3. **`dust_shift`** (THE SHIFT LAW): `digit_{j+1}(4^(r + t·3^j)) =
   (digit_{j+1}(4^r) + t) % 3` — the three children of every node present
   the digit values d, d+1, d+2 at the new position: exactly one dead child.
4. **`digit_period`**: `digit_q(4^(k + 3^q·m)) = digit_q(4^k)` — the level-q
   digit is a function of the class mod 3^q.
5. **`dust_spec`** (THE FULL SPEC): `r ∈ dust j ↔ r < 3^j ∧ ∀ q ≤ j,
   digit3 (4^r) q ≠ 2` — the tree IS the survivor set.
6. **`dust_rider_classes`**: the riders are the integer points of the tree.
7. **`dust_doubling` / `dust_card`**: the exact doubling, forever.

Battery H-lane: the doubling verified to level 18 in Python, the tree-is-
survivor-set spec verified levels 1–5, and the level receipts
(`dust 1 = [0,1]`, `dust 2 = [0,3,1,4]`, `dust 3 = [0,9,12,21,1,10,4,13]`)
match the kernel receipts exactly. ALL GREEN: `BATTERY_CAPLAW_GREEN=1`.

## Deliverable 3 — THE CAP ASSAULT (the honest verdict)

The war council fired both modes. The attacker-math (this session's own
analysis, sub-agent channel unavailable):

- **The magnitude fantasy REFUTATED (recorded so no future session re-falls):**
  a "relaxed-slope cap" (v2 ≤ σM + C with σ = 84/53 < log₂3) appears to kill
  riders K ≤ 3260C by pure magnitude — FALSE: the fixpoint between the
  cap-side validity range M ≤ (C−0.585)/(log₂3−σ) and the rider bound
  K ≤ C/(2−σμ) requires the M-certificate slack s₂ = 0 (impossible for
  rationals). The magnitude constraints are CONSISTENT; the content is in
  the digits. (My own first arithmetic — σ·log₃4 = 1.9996932 — was wrong by
  10⁻³; the true product is 1.9999685; the Third-Eye caught it before ship.)
- **The counting-kill requirement:** with |alive[j]| = 2^j (now a theorem),
  the kill needs ANTI-CLUSTERING: a lower bound min(alive[j] \ {0,1,4}) ≥
  a^j (a > 1), or any upper bound on |alive[j] ∩ [0,N)| for N ≪ 3^j. This
  is THE named remaining front.
- **The repunit reformulation (recorded):** riders = K where the base-4
  repunit u_K = (4^K−1)/3 = Σ_{i<K} C(K,i+1)3^i (hockey-stick) is 0/1-ternary;
  the dust tree is the solution set of these binomial congruences.
- CAP(185) itself remains OPEN — equivalent in strength to the #406 kill
  (the anti-concentration wall). What stands: the reduction (CI-green,
  zero sorry) + the Dust Law (the entropy row closed: branching exactly 2
  forever) + the census to 200000 + v₂* ≤ M+4 through M=34.

## Deliverable 4 — THE SANDBOX PROTECTION SYSTEM (BOSS's order)

- `/home/z/BACKUP.md` — the master restore runbook (token vault = the Drive
  bag; progress vault = GitHub `campaign` + `sandbox-vault` branches).
- `/home/z/backup/backup.sh` — the engine: seals uncommitted work, pushes
  campaign, refreshes the vault branch. `ghtoken.txt` chmod 600, NEVER in
  git (the repo is PUBLIC).
- `.bashrc` anchor — every future session opens to the BACKUP.md pointer.
- Cron guardian (job 539857, 3× daily): automated backup turns.
- Branch `sandbox-vault` pushed to GitHub with the runbook + engine.

## Next strikes

(a) ANTI-CLUSTERING: the survivor residues' distribution — min-survivor
    exponential lower bound, or |alive[j] ∩ [0,N)| sub-linearity — the
    counting kill's named input.
(b) The binomial stratification: forced digit-2 deaths by K mod 3^m class
    analysis of the hockey-stick digits.
(c) The census extension under the (now exact) 2^j tree — C-engine lane.

The engine never stops; it never lies. In English, always.
