# AUDIT W89-A61 — ADVERSARIAL AUDIT OF DM61_Proof_E.lean (kernel 61DM-E, mission #61)

TASK: W89-A61 | TARGET: `problem61-erdos-hajnal/DM61_Proof_E.lean` (1268 lines, branch campaign, tip d290274)
CLAIM UNDER AUDIT: CI-green (job `kernel-dm-w85`, run 45497202986) theorems
`Erdos61E.eh_P4`, `Erdos61E.eh_Pbar4`, `Erdos61E.erdos_61_p4` with axiom profile
`[propext, Classical.choice, Quot.sound]`.
METHOD: full-file read (all 1268 lines), statement diffing against the official
sources, independent mathematical re-derivation of the lemma chain, CI-log
forensics (run 45497202986 logs, W89 zero-sorryAx sweep). No Lean toolchain run
(campaign law: CI is the only Lean verdict); no proof code written; no push.

---

## 1. VERDICT

**PASS — the green is REAL.** Zero sorry, zero admit, zero native_decide, zero
axiom declarations; the official predicate is byte-identical to the DeepMind
upstream; the three headline statements are clean instances of the official
pattern with no added hypotheses; the proof spine is mathematically sound and
every load-bearing composition closes; the CI gate is a genuine rejection gate
(error/sorryAx/marker/axiom-profile greps under `set -euo pipefail`), and the
archived CI log shows exactly the claimed axiom profile. **No defects found.**
Three INFO-level observations below (dead code / import weight / representation
note) — none affects soundness or statement fidelity.

---

## 2. STATEMENT FIDELITY (side-by-side)

### 2.1 The official predicate `IsErdosHajnalLowerBound`

| side | location | text |
|---|---|---|
| OFFICIAL (upstream, byte-verified @ 2207c54d) | `deepmind-comparator/DM_61.lean:39-42` | `def IsErdosHajnalLowerBound {α : Type*} [Fintype α] [DecidableEq α]` / `  (H : SimpleGraph α) (f : ℕ → ℝ) : Prop :=` / `  ∀ᶠ n in atTop, ∀ G : SimpleGraph (Fin n),` / `    (¬∃ g : α ↪ Fin n, H = G.comap g) → G.indepNum ≥ f n ∨ G.cliqueNum ≥ f n` |
| OFFICIAL (campaign spec file) | `DM61_Official.lean:42-45` | identical (diff vs upstream: empty, W82 provenance) |
| KERNEL 61E | `DM61_Proof_E.lean:54-57` (namespace `Erdos61E`) | identical — **`diff` run this session: EMPTY (`DEF_IDENTICAL`)** |

The kernel re-declares the predicate in its own namespace (campaign pattern,
identically in 61A:72-75, 61B/DM61_Closure:66-69, 61D:83-86 — all verified
identical this session). Same environment (Mathlib v4.33.0-rc2, same imports),
byte-identical body ⇒ the same predicate up to namespace. No drift.

### 2.2 The theorem statements

| item | OFFICIAL pattern / instance | KERNEL 61E | verdict |
|---|---|---|---|
| family pattern | `erdos_61` (`DM_61.lean:49-51`): `∀ H, ∃ c > (0:ℝ), IsErdosHajnalLowerBound H (fun n : ℕ => (n:ℝ)^c)` | `erdos_61_p4` (:1249-1251): `∃ c > (0:ℝ), IsErdosHajnalLowerBound P4 (fun n => (n:ℝ)^c) ∧ IsErdosHajnalLowerBound (P4ᶜ) (fun n => (n:ℝ)^c)`, witnessed `c := 1/4` with `positivity` (:1252) | MATCH — the H := P4 instance of the official pattern, plus the P̄4 conjunct (a strengthening, not a weakening) |
| headline | — (no P4-specific official target exists upstream; p5/c5 use `pathGraph 5`/`cycleGraph 5`) | `eh_P4` (:1220): `IsErdosHajnalLowerBound P4 (fun n => (n:ℝ)^((1:ℝ)/4))` — **no hypotheses** | MATCH — hypothesis-free instance at the Seinsche exponent c = 1/4 |
| complement | — | `eh_Pbar4` (:1244-1245): `IsErdosHajnalLowerBound (P4ᶜ) (fun n => (n:ℝ)^((1:ℝ)/4))` := `isEH_compl eh_P4` | MATCH |
| H itself | P4 = the 4-vertex path | hand-rolled `P4` (:64-69): `Adj i j := ((i:ℕ)+1 = (j:ℕ) ∨ (j:ℕ)+1 = (i:ℕ))` on `Fin 4` ⇒ edges exactly {01, 12, 23} | MATCH (genuine path; see §7 INFO-3) |
| hypothesis shape | official: `¬∃ g : α ↪ Fin n, H = G.comap g` at α = Fin 4 | kernel `P4free` (:239-240): `¬∃ g : Fin 4 ↪ α, P4 = G.comap g`; at α := Fin n consumed **definitionally** at :1225 (`hG` passed directly — the "zero-bridge") | MATCH — no weakening, no extra hypothesis, no restated antecedent |

Eventual threshold: `eh_P4` unwraps `eventually_atTop` at N = 4 (:1222) and the
finisher chain needs `4 ≤ n` — the "sufficiently large n" of the official
statement is honored, not truncated.

---

## 3. ZERO-SORRY SCAN (word-boundary precise)

```
$ rg -n '\b(sorry|admit|native_decide|axiom)\b' DM61_Proof_E.lean
41:Zero sorry, zero native_decide; `#print axioms` on every headline. -/
   (a docstring comment — no code hit)
```
- `sorry` : 0 hits in code. `admit` : 0. `native_decide` : 0. `axiom` declarations: 0
  (only `#print axioms` commands, :1258-1266, and the docstring).
- Corroborated by CI forensics: run 45497202986 job log
  (`problem406-ternary-powers/CI_LOGS_W89/kernel-dm-w85.log`) — compile clean
  (warnings only: unused simp args, `push_neg` deprecations); all nine
  `#print axioms` lines print `depends on axioms: [propext, Classical.choice,
  Quot.sound]` incl. `eh_P4`/`eh_Pbar4`/`erdos_61_p4` (log :451-453); marker
  `DM61E_P4_GREEN` printed; `KERNEL_61DM_E_GREEN=1` (:464). The W89 global
  sorryAx sweep (run 45497202986): `kernel-dm-w85 hits=6 guard=6 REAL=0`.
- No `==`/BEq/bne traps (grep: 0 hits outside `⟨⟩`-free arrows). No
  `opaque/private/unsafe/macro/syntax/partial`. `set_option` only
  `maxHeartbeats 16000000` / `maxRecDepth 262144` (:43-44) — capacity, not logic.
- `decide` sites (L86 audit): :111-126 (16 cells of `p4_comap_of_path` — the P4
  side only, concrete `Fin 4` literals after `fin_cases`; the G side is fed by
  hypotheses `e1/e2/e3/n1/n2/n3`, never decided); :434, :441 (closed Fin 4
  computations in `p4_compl_comap`/`psi_comp`); :1109 (`(2:ℕ)^2 = 4`). **All
  closed terms — L86 compliant.**

---

## 4. CRITICAL-PATH COMPOSITION MAP (theorem → lemmas, with line numbers)

```
Erdos61E.erdos_61_p4 (:1249)
├── Erdos61E.eh_P4 (:1220)                                  [witness c = 1/4, N = 4]
│   ├── p4_witness_product (:1084) via p4_witness_product_aux (:669, strong ind.)
│   │   ├── seinsche_split (:656) via seinsche_split_aux (:500, strong ind.)
│   │   │   ├── caseA (:327) — the Seinsche heart
│   │   │   │   ├── last_exit (:278) / last_exit_aux (:256)   [STEP 1]
│   │   │   │   ├── flip (:289)                               [STEP 2]
│   │   │   │   ├── p4_comap_of_path (:102) + emb4 (:77) + P4_adj (:71)
│   │   │   │   │     [the induced P4 (q,p,u,z′), 16-cell grid verified]
│   │   │   │   └── reach_isolated (:310)                     [STEP 3]
│   │   │   ├── walk_crosses (:171) → unreachable-pair extraction (:613, :650)
│   │   │   ├── conn_of_no_sep (:206) ← sep_class_of_unreachable (:187)
│   │   │   ├── p4free_comap (:244) ← comap_comap' (:231)     [heredity, inj]
│   │   │   ├── p4free_compl (:445) ← compl_comap (:219, INJ repaired)
│   │   │   │   ← p4_compl_comap (:431) + psi (:429) + psiInv (:437)
│   │   │   │     + psi_comp (:439) + comap_comap' (:231)     [ψ-bridge]
│   │   │   └── card_peel (:478)
│   │   └── (union case :721-896 / join case :897-1082; image transports,
│   │       le_total max-dichotomy :870/:1056)
│   ├── sqrt_le_of_sq (:1094)                                [n ≤ M² → √n ≤ M]
│   ├── Mathlib: IsClique.card_le_cliqueNum / IsIndepSet.card_le_indepNum
│   │   (applied :1234, :1238)
│   └── official_bound_of_sqrt (:1164) ← rpow_quarter_le_sqrt (:1143)
│       ← le_sqrt_pow_four (:1115)                           [n^(1/4) ≤ √n, n ≥ 4]
├── Erdos61E.eh_Pbar4 (:1244) = isEH_compl (:1176) applied to eh_P4
└── witness ⟨1/4, positivity⟩ (:1252)
```
GReach plumbing: `prepend` (:141) used by `symm` (:152); `symm`/`trans` (:161)
used at :352, :363, :376. Dead: `arsenal_threshold` (:1106) — see §7.

**Exact logical composition of `eh_P4`:** ∀ n ≥ 4, ∀ G : SimpleGraph (Fin n),
official no-copy hypothesis (defeq `P4free G`) → `p4_witness_product` gives
I, K with |I|·|K| ≥ n → M := max(|I|,|K|) satisfies n ≤ |I||K| ≤ M² →
`sqrt_le_of_sq` gives √n ≤ M → `le_total` dichotomy: M = |K| (then
card_le_cliqueNum) or M = |I| (then card_le_indepNum) → indepNum ≥ √n ∨
cliqueNum ≥ √n → `official_bound_of_sqrt` (rpow chain n^(1/4) ≤ √n) → the
official conclusion. Every link verified present and correctly applied.

---

## 5. MATH SPOT-CHECKS (statements verified true independent of Lean)

| # | lemma (line) | statement | independent verdict |
|---|---|---|---|
| 1 | `walk_crosses` (:171-173) | a walk a→b crosses every separation s (∃ p∈s, q∉s, p—q edge) | **TRUE** — standard first-crossing-edge induction |
| 2 | `sep_class_of_unreachable` (:187-190) | if x ↛ y, the reachability class of x is a nonempty proper Finset with no cross edges | **TRUE** — classes are adjacency-closed |
| 3 | `compl_comap` (:219-221) | (G.comap f)ᶜ = Gᶜ.comap f **at injective f** | **TRUE** — adjacency sides are (a≠b ∧ ¬G(f a)(f b)) vs (f a≠f b ∧ ¬G(f a)(f b)); equal iff f injective. (The uninjective draft version was indeed false — the repair is correct, not a weakening: heredity/complement uses only injective carriers) |
| 4 | `flip` (:289-296) | on a G−u walk a→*b with u∼a, u≁b, some walk edge p—q has u∼p, u≁q, both reachable from a | **TRUE** — u-adjacency must flip along the walk |
| 5 | `caseA` (:327-333) | G, Gᶜ both walk-connected, P4free G, some pair unreachable in G−u ⟹ False | **TRUE** — Seinsche's core: mixed class ⟹ induced P4 (q,p,u,z′) with all six pairs accounted (edges q—p, p—u, u—z′; non-edges q—u, q—z′, p—z′ — z′ outside a's class by construction, p,q inside); uniform case ⟹ u G-universal ⟹ u isolated in Gᶜ ⟹ contradicts Gᶜ-connectivity. Machine-verified exhaustively n ≤ 6 + sampled n = 7, 8 (W85 audit: 23,724 constructive completions, 0 bad) |
| 6 | `seinsche_split` (:656-662) | P4free G, ≥ 2 vertices ⟹ G or Gᶜ has a separation | **TRUE** — Seinsche 1974. Base n=2 (edge dichotomy, :514-579) needs no P4-freeness (correct: any 2-vertex graph satisfies it); recursion peels u, applies caseA on G or Gᶜ (via ψ-bridge + compl_comap) |
| 7 | ψ-bridge (:429-441, :445-472) | P4ᶜ = P4.comap ψ, ψ = ![1,3,0,2], ψ∘ψ⁻¹ = id ⟹ P4free G → P4free Gᶜ | **TRUE** — P4 is self-complementary; hand-checked all 16 cells of the ψ grid (P4ᶜ edges {02, 03, 13} = P4 edges under ψ) and ψ∘ψ⁻¹ = id on all 4 points |
| 8 | `p4_witness_product` (:1084-1088) | P4free G ⟹ ∃ independent I, clique K with \|I\|·\|K\| ≥ n | **TRUE** — the cograph product law. Union case: I = I₁∪I₂ (cross pairs non-adjacent by the separation), K = the larger clique (cliques cannot merge across a separation); join case dual (K = K₁∪K₂, cross pairs adjacent by compl_adj; I = the larger). Arithmetic verified: (\|I₁\|+\|I₂\|)·max ≥ \|I₁\|\|K₁\| + \|I₂\|\|K₂\| ≥ \|s\| + \|sᶜ\| = n; both parts nonempty and strictly smaller (induction fuel) |
| 9 | finisher chain (:1094-1170) | n ≤ m² → √n ≤ m; n ≥ 4 → n ≤ (√n)^4; n^(1/4) ≤ √n; dichotomy transfer | **TRUE** — √n ≥ 2 and (√n+1)² ≤ (√n·√n)² for n ≥ 4; rpow monotone at exponent 1/4 > 0; 4·(1/4) = 1 |
| 10 | `isEH_compl` (:1176-1214) | H at f ⟹ Hᶜ at f | **TRUE** — complementing the embedding equation at injective g (Hᶜ = (Gᶜ.comap g)ᶜ = G.comap g), indepNum/cliqueNum swap under complement, disjunct swap. Final `eh_Pbar4` follows |

Chain closure: §4's composition uses exactly these; no circularity (the two
strong inductions are on `Fintype.card α ≤ n` with explicit decreasing parts:
card peel :478/:585-590, separation parts :744-747/:920-923).

---

## 6. SUPPORTING KERNELS + CI GATES (jobs verified in `.github/workflows/kills.yml`)

| job | file | gated theorems (axiom-profile grep) | status |
|---|---|---|---|
| `kernel-dm-w85` (:222) | `DM61_Proof_E.lean` | `Erdos61E.eh_P4 / eh_Pbar4 / erdos_61_p4 / seinsche_split / p4_witness_product / last_exit / walk_crosses` + sorryAx-rejection + `DM61E_P4_GREEN` marker | **GREEN (run 45497202986, log archived: 9 axiom lines, all [propext, Classical.choice, Quot.sound])** |
| `kernel-dm-w84` (:176) | `DM61_Proof_D.lean` (K5/E5 at c = 1/5) | `Erdos61D.eh_K5 / eh_E5 / erdos_61_k5_e5 / ramsey_ladder / choose_le_of_ge_1024 / rpow_fifth_le_root5_succ / four_and_twenty_choose_four_le` | consistent sibling (statements :637/:713/:725; same predicate verbatim :83-86) |
| `kernel-dm-w82` (:103) | `DM61_Proof_A.lean` (+ `DM61_Closure.lean`, `DM61_Official.lean` step at :89) | `Erdos61A.erdos_61_family` (F7 family at c = 1/4); P4 honestly NOT claimed there | consistent sibling (same predicate verbatim :72-75) |
| `kernel-61k` (:2545) | `Erdos61.lean` | `E61.family_board` + greedy/degree/cluster/complement/tightness/arsenal lemmas (F7 at floor √n, c = 1/2) | consistent sibling |
| `kernel-61e-probe` (:276) | `DM61_API_Probe.lean` | **none — by design**: "NEVER FAILS: the log is the receipt" (API survey only, `|| true`, no gate) | honest probe, not a gate — correctly labeled |

Gate quality note: the `kernel-dm-w85` step runs `set -euo pipefail` and
REQUIRES (i) no `error[:(:]`/`sorryAx`/`unknown identifier`/`unsolved goals`
strings, (ii) the green marker, (iii) the seven axiom-profile lines, (iv) no
sorryAx in any Erdos61E axiom line. `if: always()` only makes the step run
after earlier failures; it cannot mask a failure inside the step. This is a
real rejection gate, not a rubber stamp.

## 7. COMPARATOR

`comparator-official/challenges/61/RECEIPTS_official.txt`: **CHECKS: 20/20
passed (official=5, solution=7, controls=8), VERDICT: YOUR SOLUTION IS OKAY**
(2026-11-24T20:18:23). Confirmed independently in the CI copy
`problem406-ternary-powers/CI_LOGS_W89/gate-61-official.log` of run 45497202986
(:154 "CHECKS: 20/20 passed", :156/:158 "VERDICT: YOUR SOLUTION IS OKAY"). The
official gate includes the statement-file control `S-W82-SPEC` (verbatim
DeepMind predicate) and negative control `N-W82-NEG` (corrupted predicate
string is rejected).

---

## 8. FINDINGS (defects: NONE; observations)

No defects. Adversarial holes hunted and not found: no circular lemma pair; no
statement that strengthens a hypothesis (checked `p4free_comap` and
`compl_comap` injectivity side-conditions are used only where true); no dead
branch ON the critical path; no decide on open terms; no BEq/`==` traps; no
namespace/def smuggling (predicate diff empty).

- **INFO-1 (dead code, cosmetic).** `arsenal_threshold` (:1106-1111) is proven
  and axiom-printed (:1266) but never applied: the N = 4 threshold enters via
  `refine ⟨4, ?_⟩` (:1222) and `official_bound_of_sqrt hn` (:1237/:1241);
  `le_sqrt_pow_four` does not use it either. It is a verbatim 61A port kept for
  attribution; the CI job description even lists it as part of the "61A
  finisher chain". Harmless (it is itself axiom-clean), but the worklog/job
  text could be read as claiming it is load-bearing. It is not.
- **INFO-2 (import weight, cosmetic).** `import Arsenal.ErdosTernary2.Basic`
  (:2) is referenced nowhere in the file; `Arsenal.CardinalWorlds` (:3) feeds
  only the dead `arsenal_threshold` (via `two_pow_pos`/`two_pow_ge2`,
  :1107-1108). No soundness impact (both Arsenal modules are independently
  CI-built and axiom-clean).
- **INFO-3 (representation note).** `P4` is hand-rolled (:64-69) while 61A
  used Mathlib's `SimpleGraph.pathGraph 3` for P3 (DM61_Proof_A.lean:538). The
  hand-rolled graph IS the 4-vertex path (edges exactly {01,12,23}; confirmed
  by inspection and by the W85 census machines), and no official P4-named
  target exists upstream to drift from — the official family pattern is
  `∃ c > 0, IsErdosHajnalLowerBound H (fun n => (n:ℝ)^c)`, which
  `erdos_61_p4` instantiates faithfully. If a future kernel needs
  `pathGraph 4` syntactically, a defeq/iso bridge lemma should be added;
  none is needed for this kernel's claims.

---

## 9. NEXT ACTIONS (recommended, non-blocking)

1. Keep `AUDIT_W85_61E.md` + this file as the two-lock audit record for 61E.
2. Optional hygiene commit (no math content): drop or `@[deprecated]`-mark
   `arsenal_threshold` in 61E or annotate it "vestigial, 61A attribution",
   and prune the unused `Arsenal.ErdosTernary2.Basic` import — or leave as-is
   (CI cost only).
3. The open core (`erdos_61` ∀ H) remains honestly unclaimed — no action.

*Audit executed under campaign law: no lake/lean runs, no proof code written,
no push. English only. The engine never stops; it never lies.*
