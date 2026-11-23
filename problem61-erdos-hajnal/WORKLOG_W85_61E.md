# W85-61E — THE P4/SEINCHE OFFICIAL-FORM KERNEL (IN PROGRESS, round 1)

Mission: `eh_P4` — the official IsErdosHajnalLowerBound for H = P4 at c = 1/4,
the eighth family member (completes erdos_61_family8: F7 + P4).

## The architecture (fully derived this round; DM61_Proof_E.lean carries
§0-§3 + §6 core complete; the four marked bodies land next round)

- §1 P4 hand-rolled (Adj = +1 arithmetic; zero pathGraph API) + the 16-cell
  p4_comap_of_path grid (the green pathGraph3_comap pattern extended to
  Fin 4) + emb4 (the green Matrix.cons embedding).
- §2 GReach — the campaign's OWN reachability closure (inductive,
  append-shaped): prepend via the append-x-x-y refl trick, symm, trans —
  all derivation inductions, zero Mathlib Walk API. sep_class_of_unreachable:
  the unreachable pair gives the Finset separation (classical filter).
- §3 heredity: P4free passes to comap (comap_comap' + Embedding.trans) with
  DIY compl_comap.
- §4 SEINCHE (the clean route, D=V' stall eliminated): caseA packaged
  complement-symmetrically: G conn + Gᶜ conn + G−u not conn + P4free → False.
  The route: last-exit (u's neighbor in each G−u class) + the flip lemma
  (the u-adjacency flip pair on the class-internal walk) + the two-class
  trick (a's class differs from x's or y's since x,y unreachable) + the
  P4 completion (p, q, u, z') with z' in the other class. n=2 base direct.
  Case B: apply caseA to Gᶜ (self-complementarity via ψ = ![1,3,0,2]).
- §5 the witness product law (∃ I K, |I|·|K| ≥ n — witnesses explicit, no
  attainment API; DIY strong induction (the ∀ n, ∀ m ≤ n strengthening —
  no Nat.strongRecOn dependency); the separation split: union side α ≥
  α₁+α₂ (image-union, disjoint by parts), ω ≥ max; join side dual; the
  algebra (c₁+c₂)·max(d₁,d₂) ≥ c₁d₁+c₂d₂ ≥ n).
- §6 sqrt_le_of_sq (DONE: by_contra + Nat.le_sqrt + ring + omega) + the
  rpow chain n^{1/4} ≤ (m²)^{1/4} = m^{1/2} ≤ m (the green 61A template).
- §7 eh_P4: threshold 4 on eventually_atTop, the max-case split feeding
  indepNum (card_le_indepNum, green) / cliqueNum (via the compl bridge:
  clique in G = indep in Gᶜ + indepNum_compl, green).

## Status
- §0-§3 + sqrt_le_of_sq: written, believed sound (uncompiled — CI next).
- last_exit / seinsche_split / p4_witness_product / rpow tail: derived on
  paper above, bodies to write (next round).
- NOT wired into kills.yml yet (the sorry draft must never touch CI).
- W85-61E-A ADVERSARIAL AUDIT LANDED (AUDIT_W85_61E.md + audit61e_w85.py +
  receipts61e_audit.txt, 52/0 GREEN): the ARCHITECTURE is sound (the caseA
  route machine-verified exhaustively n≤6 + sampled n=7,8; the W82 §2
  uniform-case sentence is DEFECTIVE — do not use; use the universality
  finish). The DRAFT has 12 defects, incl. compl_comap FALSE as stated
  (missing injectivity — critical path of caseB + ψ-bridge), last_exit's
  statement ill-typed, GReach.trans's strategy broken (induct on h2), 2
  transposed grid cells (lines 104/107), and 2 missing lemmas the §4
  inventory must add (walk_crosses, isolated-vertex). All repairs
  specified in the audit §4. Fix before CI.

## The API probe (kernel-61e-probe job, run on 10ee62c) receipts the
connectivity/cograph surface — though the architecture now avoids ALL of it
(GReach is own-rolled); the probe still confirms the finisher set.
