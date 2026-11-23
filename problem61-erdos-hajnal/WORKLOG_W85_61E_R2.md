# WORKLOG_W85_61E — R2: THE P4/SEINCHE KERNEL COMPLETED (commander-written)

Task ID: W85-61E (R2). The draft's four sorry bodies + §7 completed
in-thread (the subagent channel died on context deadlines; the audit
contract AUDIT_W85_61E.md — 52 PASS / 0 FAIL machine-verified — was the
specification). DM61_Proof_E.lean: 1258 lines, zero sorry.

## The as-built ledger (audit defect → fix applied)

| audit | fix |
|---|---|
| D1/D2 (grid cells (2,3)/(3,2) transposed) | e3 / G.adj_symm e3 as prescribed |
| D3 (Std field scripts) | `adj_comm := ⟨fun h => Or.symm h⟩`, `loopless := ⟨fun a => show ¬(...); omega⟩` |
| D4 (compl_comap FALSE uninjective) | the injective-function version with the hf hypothesis; both directions by hand |
| D5 (p4free_comap rw-loop) | the comap_comap' defeq term `hg.trans (comap_comap' G f g)` with the composite-embedding witness |
| D6/D7 (refl-branch outer fvars) | branch binders `a` only |
| D8 (trans circular) | induction on the SECOND walk; branches as implications (`intro h`) |
| D9 (last_exit ill-typed) | the subtype statement + last_exit_aux carrying `i = u` in the motive + the ∀-hj conclusion form |
| D10 (sqrt tail) | `have h4 : (m+1)*(m+1) = m*m + 2*m + 1 := by ring; omega` |
| D11 (cons_val_three unprobed) | the inj' proof via the four @[simp] rfl-lemmas (emb4_zero..three), 16 explicit cells |
| D12 (walk_crosses missing) | added (the clean induction); the isolated-vertex lemma added |

## The §4 engine (the audit §1.1–1.3 case tree, implemented exactly)

last_exit_aux/last_exit → flip (with the class-reachability receipts) →
caseA (STEP 1 neighbor-in-every-class via last_exit at hconn; STEP 2 the
mixed class: flip + the two-class trick + the P4 completion (q, p, u, z′)
via p4_comap_of_path with all six distinctness receipts; STEP 3 the
universality finish: uniform + STEP 1 → G-universal → isolated in Gᶜ via
compl_adj → reach_isolated contra) → the ψ-bridge (p4_compl_comap by the
16-cell decide grid; psi_comp by funext+fin_cases+decide; p4free_compl via
compl_comap + comap_comap' + comap_id) → seinsche_split_aux (strong
induction; the n = 2 base: the equivFin pair + the 3-in-2 pigeonhole world
fact via Fintype.card_le_of_injective + the edge dichotomy; the recursion:
peel u → IH on G−u (card_peel via Fintype.card_add_card_compl +
Fintype.card_unique) → caseA on G or on Gᶜ through the comap-complement
bridge).

## §5 the witness product law (the audit §1.5, implemented)

Strong induction; the ≤ 1 world by Fintype.card_eq_zero/one (IsEmpty /
Unique + Subsingleton.elim); the union case (I := I₁′ ∪ I₂′ with the
four-cell membership chase: within-part via the comap-adj simp route,
cross-part via the separation; K := the larger by le_total; the count by
Finset.card_disjoint_union (probed) + Nat.mul_le_mul +
Nat.add_mul/Nat.mul_add + omega); the join case dual (K := K₁′ ∪ K₂′ with
the compl_adj cross-clique bridge ¬(Gᶜ).Adj ∧ a ≠ b → G.Adj; I := the
larger).

## §6/§7

sqrt_le_of_sq (the ring+omega tail); arsenal_threshold, le_sqrt_pow_four,
rpow_quarter_le_sqrt, official_bound_of_sqrt, isEH_compl — ported VERBATIM
from the CI-green DM61_Proof_A.lean; eh_P4 (threshold 4, the official
hypothesis consumed directly as P4free — the audit §3 zero-bridge
finding); eh_Pbar4 via isEH_compl; the board erdos_61_p4.

## RISK LIST (CI adjudicates; fallbacks ready)

1. `Fintype.card_add_card_compl` + `Fintype.card_unique` (card_peel) —
   fallback: Fintype.subtypeCard + filter arithmetic, or a hand equiv to
   Fin 1 + Fintype.card_congr.
2. `Fintype.card_le_of_injective` (the 3-in-2 pigeonhole) — standard;
   fallback: the Finset image route.
3. `Fintype.equivFin` + the Fin-2 literal decide cells — the `simp at h2e`
   on `(0 : Fin 2) = 1` should close; fallback `Fin.ext_iff` + omega.
4. `SimpleGraph.comap_id` (the ψ⁻¹ pullback) — standard; fallback: ext +
   simp [comap_adj] (2 lines).
5. `Finset.card_disjoint_union` — PROBED at v4.33.0-rc2 (probe61e).
6. The GReach induction branch shapes (the auto-revert implication forms)
   — D8/D9 analysis; if a branch arrives non-generalized, add `intro`.
7. `Nat.le_div_iff_mul_le`-style order risks — none here (no division).
8. The `subsingleton`-free ≤ 1 world via `Fintype.card_eq_one.1` →
   `Nonempty (Unique α)` → `haveI` + `Subsingleton.elim` — the instance
   chase; fallback: the equivFin singleton route.

The engine never stops; it never lies. In English, always.
