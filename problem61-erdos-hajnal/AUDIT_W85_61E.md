# AUDIT W85-61E — ADVERSARIAL AUDIT OF THE P4/SEINCHE KERNEL ROUTE (COMPLETE)

TASK: W85-61E-A | DISPOSITION: Doubter | TARGET: the `eh_P4` route as
architected in WORKLOG_W85_61E.md + drafted in DM61_Proof_E.lean (§0-§3 +
sqrt_le_of_sq written; last_exit / seinsche_split / p4_witness_product /
rpow tail pending), against the GREEN idioms of DM61_Proof_A.lean (61A) and
DM61_Proof_D.lean (61D).

METHOD: full paper re-derivation of every component (A-D of the brief) +
an exhaustive machine audit (`audit61e_w85.py`, receipts
`receipts61e_audit.txt`, 52 PASS / 0 FAIL): all labeled graphs n ≤ 6
(6,866 P4-free graphs; counts match the known labeled-cograph sequence
1, 2, 8, 52, 472, 5504 — independent confirmation of both P4 detectors),
samples at n = 7, 8, and constructive instrumentation of every sub-lemma of
the Seinsche case tree (23,724 P4 completions, all six pairs checked each
time). No Lean toolchain in the sandbox (CI-only campaign law); Lean-level
findings below are elaboration-semantics analysis, confidence-labeled.

---

## 0. VERDICT SUMMARY

| component | verdict | note |
|---|---|---|
| A. Seinsche split (the mathematics, W85 caseA route) | **SOUND** | fully re-derived; machine-verified n ≤ 6 exhaustive + n = 7, 8 sampled; every sub-lemma constructively checked |
| A′. W82_61A §2 MASTER sketch (the uniform-case sentence) | **DEFECT (superseded)** | the "{u} ∪ (u's non-neighbors) vs (u's neighbors)" Gᶜ-separation claim is FALSE for plain G−u-classes (cross-class pairs are Gᶜ-EDGES); it only holds for CO-classes. W85's universality finish replaces it correctly. The writer must NOT follow the W82 sentence. |
| B. Witness product law (§5) | **SOUND** | heredity, union/join constructions, transport, strict decrease, algebra all verified |
| C. Finisher (§6/§7) | **SOUND** | integer-sqrt chain clean; all-green idiom reuse; the architecture's "compl bridge for cliqueNum" is unnecessary (see §C.4) |
| D. Draft §0 | **SOUND** | byte-identical to DM61_Official.lean and to 61A §0 (verified by string diff this session) |
| D. Draft §1 (P4, emb4, p4_comap_of_path) | **DEFECT ×3** | the math is sound; two transposed terms (lines 104/107), the structure-field scripts (lines 45-53) are malformed for v4.33, `Matrix.cons_val_three` unverified |
| D. Draft §2 (GReach) | **DEFECT ×3** | sep_class_of_unreachable SOUND; prepend/symm refl branches reference outer index fvars; **trans's proof strategy is unprovable as scripted** |
| D. Draft §3 (heredity) | **DEFECT ×2** | **compl_comap is FALSE as stated (missing injectivity — the worst finding)**; p4free_comap's rw-script cannot work (math sound, script broken) |
| D. Draft §4 statement (last_exit) | **DEFECT** | the statement does not elaborate (⟨val w, _⟩ : β against an abstract β) |
| D. Draft §6 (sqrt_le_of_sq) | SOUND, tail incomplete | needs the ring step; h3 is dead code |

**Can the kernel ship as architected? YES** — the architecture is sound
end-to-end; every defect is a local repair (≈10 one-liners + 2 statement
fixes + 1 strategy fix). But §0-§3 as committed DO NOT COMPILE as written;
§3's compl_comap is a false statement. All repairs are specified below.

---

## 1. THE COMPLETE SEINCHE CASE TREE (verified; the writer's contract)

Notation: `sep(X)` := ∃ s : Finset, s.Nonempty ∧ s ≠ univ ∧ ∀ a ∈ s, ∀ b ∉ s,
¬X.Adj a b (the draft's separation shape). `GReach` = walk existence
(the draft's own closure). `G−u` := G.comap Subtype.val on `{x // x ≠ u}`.

**Bridge (verified):** ¬sep(G) → (∀ x y, GReach G x y) is the *contrapositive
of sep_class_of_unreachable* (pure logic; no extra lemma). The CONVERSE
direction — GReach G a b → every nonempty proper s has a cross edge — is a
SEPARATE required lemma (the **walk-crossing lemma**, missing from both the
draft and the worklog's §4 inventory; see defect D12):

> **walk_crosses**: GReach G a b → ∀ s, a ∈ s → b ∉ s → ∃ p q, p ∈ s ∧ q ∉ s ∧ G.Adj p q.
> Proof: induction on the derivation. refl (c): c ∈ s ∧ c ∉ s → absurd. append
> (a b c) hrec hadj ih: if b ∉ s, ih; else the edge b—c crosses (b ∈ s, c ∉ s). ✓
> (No outer-index references — the induction is clean.)

### 1.1 seinsche_split (strong induction on n = Fintype.card α)

Statement: P4free G → 2 ≤ n → sep(G) ∨ sep(Gᶜ).

* **n = 2**: if sep(G), LEFT done. Else ∀ x y, GReach G x y; take the two
  distinct vertices x ≠ y; GReach G x y with x ≠ y gives an edge u—w with
  w ≠ u (this is `last_exit` instantiated at n = 2 — its conclusion's
  GReach(G−u) part is vacuous, only the edge is consumed). Then s := {x} is
  a Gᶜ-separation: nonempty ✓, ≠ univ (2 vertices) ✓, cross pair (x, y):
  ¬Gᶜ.Adj x y since G.Adj x y ∧ x ≠ y ✓. RIGHT done.
* **n ≥ 3**: by contradiction assume ¬sep(G) ∧ ¬sep(Gᶜ). Pick ANY u : α.
  G−u is P4free (heredity), card = n−1 ≥ 2, so the IH gives
  sep(G−u) ∨ sep((G−u)ᶜ).
  * **LEFT (sep(G−u))**: caseA(G, u, sep(G−u)) → False.
  * **RIGHT (sep((G−u)ᶜ))**: (G−u)ᶜ = Gᶜ−u (compl_comap at the INJECTIVE
    Subtype.val — needs the repaired lemma); Gᶜ is P4free (ψ-bridge, §1.3);
    Gᶜ conn (from ¬sep(Gᶜ)); (Gᶜ)ᶜ = G conn; so caseA(Gᶜ, u, sep(Gᶜ−u)) → False.

Every branch terminates in a separation (the disjuncts) or False. COMPLETE.

### 1.2 caseA (the heart) — G conn, Gᶜ conn, sep(G−u), P4free G → False

Input shape (any of): the separation itself, or the D-unreachable pair
(x, y) with ¬GReach (G−u) x y extracted from it by walk_crosses. Write
D := G−u; classes := D-reachability classes (at least two; D has ≥ 2
vertices since a nonempty proper separation exists, so n ≥ 3).

**STEP 1 (last-exit / neighbor-in-every-class).** For every class C:
u has a G-neighbor in C. Proof: pick v ∈ C; GReach G u v (G conn);
`last_exit` gives w ≠ u with G.Adj u w ∧ GReach D w v; w is D-connected to
v, so w ∈ C. ∎ (machine-verified: 0 violations over all graphs n ≤ 6.)

**STEP 2 (uniformity).** u is G-adjacent to all of each class or none of it.
Suppose not: a class C with u-neighbor a and u-non-neighbor b.

* **FLIP lemma** (on the intra-class walk; GReach D a b exists since
  a, b ∈ C, by symm+trans from class membership): ∃ p q ∈ C with
  G.Adj p q ∧ G.Adj u p ∧ ¬G.Adj u q. Proof: induction on GReach D a b;
  refl: G.Adj u a ∧ ¬G.Adj u a → absurd; append: if G.Adj u (mid), the pair
  (mid, end); else recurse into the IH. ✓ (Both-indices-generalized motive
  `fun i j _ => G.Adj u i → ¬G.Adj u j → ∃ p q, …` closes with no
  outer-index references — the cleanest induction in the whole kernel.)
* **TWO-CLASS trick.** The D-unreachable pair (x, y) from sep(D): for EVERY
  class C, x ∉ C or y ∉ C. Proof: if both were in C, then
  GReach D x ←symm/ trans→ GReach D y, contradicting ¬GReach D x y. ∎
* **z′.** Take y′ := whichever of {x, y} is outside C; by STEP 1 applied to
  y′'s class, u has a neighbor z′ in class(y′). Then z′ ∉ C (if z′ ∈ C,
  reachability through z′ would put y′ in C). Hence ¬GReach D p z′ and
  ¬GReach D q z′ (else transit through p/q into C), and since p, q, z′ ≠ u,
  ¬G.Adj p z′ ∧ ¬G.Adj q z′.
* **P4 COMPLETION.** The four vertices **(q, p, u, z′)** — all six pairs:
  q—p edge (flip) | p—u edge (flip) | u—z′ edge (STEP 1) |
  q—u NON-edge (flip) | q—z′ NON-edge (cross-class) | p—z′ NON-edge
  (cross-class). An induced P4 — contradicts P4free. ∎
  (Machine-verified: 23,724 constructive instances at n = 4, 5, 6 — every
  mixed-u configuration yields exactly this P4, all six pairs checked.)

**STEP 3 (universality finish).** If u is uniform on every class, then by
STEP 1 u has a neighbor in every class, hence (uniformity) is adjacent to
every vertex ≠ u: **u is G-universal.** Then u is isolated in Gᶜ
(Gᶜ.Adj u w ↔ ¬G.Adj u w ∧ u ≠ w — both fail). Micro-lemma (isolated): if
∀ w ≠ u, ¬Gᶜ.Adj u w, then GReach Gᶜ u v → v = u (induction on the
derivation: refl ✓; append's edge from u is impossible). But Gᶜ conn gives
GReach Gᶜ u v for a v ≠ u (exists, n ≥ 3) — contradiction. ∎

**Note (the reconciliation the brief asked for):** the case tree NEVER
needs a spanning tree or "G−u connected for some u". u is ARBITRARY in the
step; "G−u not conn" is an *input* from the IH disjunct, and caseA is
applied symmetrically (to G, or to Gᶜ via (G−u)ᶜ = Gᶜ−u). The W82 sketch's
alternative uniform-case finish (a Gᶜ-separation "{u} ∪ u's non-neighbors")
is wrong for plain classes — do not use it; the universality finish above
is the verified replacement.

### 1.3 The ψ self-complementarity bridge (verified, all 16 cells)

P4 (hand-rolled): edges 01, 12, 23. P4ᶜ edges: 02, 03, 13.
ψ = ![1,3,0,2] (ψ(0)=1, ψ(1)=3, ψ(2)=0, ψ(3)=2; bijective; NOT an
involution — ψ⁻¹ = ![2,0,3,1]).

`P4ᶜ = P4.comap ψ` verified pair-by-pair: (0,1)→P4.Adj 1 3 ✗✓; (0,2)→P4.Adj 1 0 ✓✓; (0,3)→P4.Adj 1 2 ✓✓; (1,2)→P4.Adj 3 0 ✗✓; (1,3)→P4.Adj 3 2 ✓✓; (2,3)→P4.Adj 0 2 ✗✓ — all six unordered pairs match (machine-checked, S4).

P4free G → P4free Gᶜ: from P4 = Gᶜ.comap g, complement both sides:
P4ᶜ = (Gᶜ.comap g)ᶜ = G.comap g (**repaired** compl_comap, g injective);
compose with ψ⁻¹: P4 = (P4ᶜ).comap ψ⁻¹ = (G.comap g).comap ψ⁻¹ =
G.comap (g ∘ ψ⁻¹) (comap_comap'), witness (ψ⁻¹).trans g : Fin 4 ↪ α.
Needs BOTH ψ and ψ⁻¹ grids (or one grid + bijectivity + comap id).

### 1.4 The n = 2 base and the |V| ≤ 1 vacuity (verified)

n = 2 handled in §1.1. n ≤ 1 never reaches the split (2 ≤ n gate);
p4_witness_product at n = 0/1: I = K = ∅ / the singleton univ — both
IsIndepSet and IsClique vacuously (no distinct pairs), 0·0 ≥ 0, 1·1 ≥ 1. ✓
Machine-checked (S3-n1/n2, S7).

### 1.5 The witness product law (§5) — verified SOUND

Strong induction on n (DIY ∀-m≤n strengthening). For 2 ≤ n:
seinsche_split gives sep(G) or sep(Gᶜ).

* **G-separation (union case)**: parts s, sᶜ (both nonempty, cards ≥ 1,
  sum n, both < n). IH on both induced subgraphs (heredity). Set
  I := image I₁ ∪ image I₂ — independent: within-part by the IH +
  comap_adj; cross-part by the separation's ¬G.Adj. K := the larger of
  image K₁, image K₂ — clique within one part ✓. Count:
  (i₁+i₂)·max(k₁,k₂) ≥ i₁k₁ + i₂k₂ ≥ card s + card sᶜ = n
  (first: unfold max by le_total + Nat.mul_le_mul; second: the two IHs;
  card bookkeeping: Fintype.card_coe [green, W84 ledger] +
  card_disjoint_union [probed]).
* **Gᶜ-separation (join case)**: cross pairs a ∈ s, b ∉ s have
  ¬Gᶜ.Adj a b; since a ≠ b (part-disjoint), Gᶜ.Adj a b ↔ ¬G.Adj a b ∧ a ≠ b
  gives **G.Adj a b for ALL cross pairs**. So K := image K₁ ∪ image K₂ is a
  clique (within-part ✓ + all-cross-edges ✓); I := the larger of I₁, I₂.
  Count dual: max(i₁,i₂)·(k₁+k₂) ≥ i₁k₁ + i₂k₂ ≥ n. ✓
  (This answers the brief's join-case question: the bridge is
  ¬Gᶜ.Adj a b ∧ a ≠ b → G.Adj a b — the part-disjointness supplies a ≠ b.)

Transport: Finset.image Subtype.val, card preserved by injectivity
(Finset.card_image_of_injOn / card_image_eq). Machine-verified: α·ω ≥ n
over ALL P4-free graphs n ≤ 6 (S3).

---

## 2. THE INTEGER-SQRT CHAIN + THE FINISHER IDIOM REPORT

**The clean route (replaces the architecture's max ≥ √n detour — one lemma
fewer):**

```
M := Nat.max I.card K.card
hM1 : I.card ≤ M          := Nat.le_max_left _ _
hM2 : K.card ≤ M          := Nat.le_max_right _ _ (or Nat.max_cases for the split)
hmul : I.card * K.card ≤ M * M   := Nat.mul_le_mul hM1 hM2
hn  : n ≤ I.card * K.card        (p4_witness_product)
-- n ≤ M * M → Nat.sqrt n ≤ M  — EXACTLY the draft's sqrt_le_of_sq
hsq : Nat.sqrt n ≤ M     := sqrt_le_of_sq (le_trans hn hmul)
```
Integer-sqrt facts verified (S6, n = 4..20000): Nat.sqrt n satisfies
s² ≤ n < (s+1)², so n ≤ M·M forces s ≤ M (else (s+1)² ≤ n ≤ M·M ≤ s·s,
absurd). Equivalently the brief's route: max ≤ s−1 → i·k ≤ (s−1)² < s² ≤ n
(s ≥ 1; s = 0 forces n = 0, excluded) — both valid; the M² route reuses the
draft's own sqrt_le_of_sq and is shorter.

**sqrt_le_of_sq tail (the sorry)**: after `h2 : (m+1)*(m+1) ≤ n` and
`h : n ≤ m*m`, close with
`have h4 : (m+1)*(m+1) = m*m + 2*m + 1 := by ring` then `omega`
(omega alone will NOT close it — (m+1)*(m+1) is a nonlinear atom to omega;
the ring normalization is mandatory). The current h3 (2*(1/4) = 1/2) is
dead code here — it belongs to the §6/§7 rpow chain; delete or move.

**The green finisher idioms (exact statements, from 61A — CI-verified):**
* `SimpleGraph.IsIndepSet.card_le_indepNum (t := s) (tc := hsindep) :
  s.card ≤ G.indepNum` (61A:414/493/506; indepNum is the ℕ∞-valued sup over
  IsIndepSet Finsets — consumed by `Nat.cast_le`/le_trans against ℕ bounds).
* `SimpleGraph.IsClique.card_le_cliqueNum (t := s) (tc := hclique)` —
  DIRECT, green (61A:549, the eh_P3 dichotomy). **No compl bridge needed
  for the clique side** — the architecture's "clique in G = indep in Gᶜ +
  indepNum_compl" detour is unnecessary; `indepNum_compl` is only needed
  for the predicate-level H→Hᶜ transfer (61A's isEH_compl), which 61E does
  NOT need (P4 is handled self-complementarily inside the split).
* rpow chain, verbatim 61A §4 reuse: `rpow_quarter_le_sqrt (hn : 4 ≤ n) :
  (n:ℝ)^((1:ℝ)/4) ≤ (Nat.sqrt n : ℝ)` — built from
  `le_sqrt_pow_four` (n ≤ (Nat.sqrt n)^4 via Nat.lt_succ_sqrt' +
  s ≥ 2 from Nat.le_sqrt.2 with 4 ≤ n) + `Real.rpow_le_rpow` (positivity) +
  `Real.rpow_mul` (**REVERSED orientation at this pin**: x^(y*z) = (x^y)^z;
  use .symm) + `Real.rpow_one`; the `Real.rpow_natCast` cast dance per 61A
  lines 329-346. The consumption: `official_bound_of_sqrt`-shape
  (61A:396-402): `le_trans rpow_quarter_le_sqrt (Nat.cast_le.2 h)`.
* Threshold: `eventually_atTop` with N = 4 (61A's `refine ⟨4, ?_⟩`
  intro n hn G hG pattern); the Arsenal bridge (arsenal_threshold,
  two_pow_pos/two_pow_ge2 at root namespace) is only needed if the
  le_sqrt_pow_four-style 2 ≤ √n gate is re-proved locally — 61A's
  rpow_quarter_le_sqrt takes only 4 ≤ n and is reusable verbatim.

---

## 3. THE EMBEDDING-DIRECTION BRIDGE REPORT

Official predicate: `(¬∃ g : α ↪ Fin n, H = G.comap g)` — the embedding
runs **from H's vertex type INTO the graph's vertex type**, and the
equation puts **H on the LEFT** (`H = G.comap g`, i.e., H is the pullback).

* **61A (P3)**: no bridge — the no-copy ladder lemmas are stated in the
  SAME shape directly (`cliqueFree3_of_no_induced (hG : ¬∃ g : Fin 3 ↪ Fin n,
  (⊤ : SimpleGraph (Fin 3)) = G.comap g)`, 61A:142), and the copy
  constructors produce the same orientation (`top_comap_of_pairwise :
  ⊤ = G.comap f`, `pathGraph3_comap : pathGraph 3 = G.comap (emb3 …)`).
* **61D (K5)**: same — `no_five_clique_of_no_induced` takes the official
  hypothesis verbatim (D:540) and kills 5-cliques via Finset.orderIsoOfFin
  + top_comap_of_pairwise.
* **61E (P4)**: `P4free G := ¬∃ g : Fin 4 ↪ α, P4 = G.comap g` — at
  α := Fin n this is the official hypothesis **verbatim, definitionally**.
  ZERO bridge needed. The only place direction matters is comap
  composition: p4free_comap's witness is `g.trans f : Fin 4 ↪ α`
  (toFun ≡ f ∘ g), matching comap_comap' — the draft's witness shape is
  CORRECT (only its rw-script is broken, D5).

---

## 4. DRAFT §0-§3 DEFECTS (line-referenced, with repairs)

**D1 (line 104) — TYPE ERROR.** Cell (2,3) of the 16-cell grid needs
`G.Adj (emb 2) (emb 3) = G.Adj y z`, i.e. `e3` DIRECTLY; the draft has
`G.adj_symm e3` (type G.Adj z y). Repair: `exact iff_of_true (by decide) e3`.
**D2 (line 107) — TYPE ERROR.** Cell (3,2) needs `G.Adj z y`, i.e.
`G.adj_symm e3`; the draft has `G.adj_symm (G.adj_symm e3)` (type G.Adj y z).
Repair: `exact iff_of_true (by decide) (G.adj_symm e3)`.
(The two cells are transposed; every other cell of the grid checks out —
verified orientation-by-orientation against the green 3×3 pathGraph3_comap
which uses the forward-hypothesis-direct / transpose-symmetrized pattern.)

**D3 (lines 45-53) — structure-field scripts malformed (high confidence).**
Per the campaign's own verified v4.33 playbook (WORKLOG S083:
"SimpleGraph.loopless : Std.Irrefl Adj is a STRUCTURE field", Basic.lean:163),
`loopless := by intro a; …` cannot work (intro on a structure goal fails),
and `adj_comm := by intro a b; constructor; …` fails under every plausible
field shape (∀-arrow: constructor on a Pi fails; Std.Symm: intro fails).
Repair (probe Basic.lean:160-166 from the tag first — the S083 discipline):
`loopless := ⟨fun a => by omega⟩` (omega closes
¬(↑a+1 = ↑a ∨ ↑a+1 = ↑a) on the coerced atom) and
`adj_comm := ⟨fun h => Or.symm h⟩` (Std.Symm shape) or
`adj_comm := fun _ _ h => Or.symm h` (∀-arrow shape).

**D4 (lines 171-175) — FALSE STATEMENT (the worst finding).**
`compl_comap (G) (f : β → α) : (G.comap f)ᶜ = Gᶜ.comap f` is FALSE without
injectivity. Counterexample: β = Bool, α = Unit, f constant: LHS
((G.comap f)ᶜ).Adj true false ⟺ true ≠ false (holds); RHS
(Gᶜ.comap f).Adj true false ⟺ Gᶜ.Adj () () ⟺ False. Not equal. `tauto`
cannot (and must not) close it. Repair: take `f : β ↪ α` (or add
`hf : Function.Injective f`):
```lean
theorem compl_comap {α β : Type} (G : SimpleGraph α) (f : β ↪ α) :
    (G.comap f)ᶜ = (Gᶜ).comap f := by
  ext a b
  simp only [SimpleGraph.compl_adj, SimpleGraph.comap_adj]
  constructor
  · rintro ⟨h1, h2⟩; exact ⟨h1, fun heq => h2 (f.injective heq)⟩
  · rintro ⟨h1, h2⟩; exact ⟨h1, fun heq => h2 (congrArg _ heq)⟩
```
This lemma is on the critical path of BOTH caseB ((G−u)ᶜ = Gᶜ−u) and the
ψ-bridge (P4free G → P4free Gᶜ) — i.e., the entire complement-symmetric
half of Seinsche routes through it. (Campaign precedent: the W83 wave
caught a backwards comap-complement identity in 61A at CI — this is the
same trap, one lane later.)

**D5 (lines 189-194) — p4free_comap script broken (math sound).**
`rw [← comap_comap', ← hg] at *` fails: the pattern `G.comap (f ∘ g)`
cannot match the goal's `G.comap ↑(g.trans f)` (Embedding.trans is not
reducible; rw matches syntactically up to instances). Even on a match, the
trailing `exact hg` would be a no-goals error (rw auto-closes P4 = P4 by
rfl). Repair (defeq closes the coe — ↑(g.trans f) ≡ f ∘ g definitionally):
```lean
theorem p4free_comap {α β : Type} (G : SimpleGraph α) (f : β ↪ α)
    (h : P4free G) : P4free (G.comap f) := by
  intro ⟨g, hg⟩
  exact h ⟨g.trans f, hg.trans (comap_comap' G f g)⟩
```

**D6 (line 126, GReach.prepend refl branch).** The branch references the
outer index fvar `y`; under indexed-induction the refl case's goal is
stated over the constructor's OWN binder (the original y,z are generalized
into the motive), so the exact mismatches (or `y` is not in scope).
Repair: `| refl a => intro x hadj; exact GReach.append x x a (GReach.refl x) hadj`.
(The append branch at lines 127-129 is CORRECT as written ✓.)

**D7 (line 135, GReach.symm refl branch).** Same defect: `exact GReach.refl x`
references the outer x. Repair: `| refl a => exact GReach.refl a`.
(The append branch, lines 136-138, is CORRECT ✓ — it uses only its own
binders; `GReach.prepend ih (G.adj_symm hadj) : GReach G c a` checks.)

**D8 (lines 141-146) — GReach.trans: BROKEN STRATEGY (not just a script
slip).** Inducting on h1 with the FIXED continuation z makes the append
case circular (the IH yields GReach a b — a prefix — while the goal needs
GReach a z; chaining back through the peeled edge re-needs trans), and the
scripted term `GReach.append a c z (ih h2) hadj` is ill-typed under every
plausible generalization semantics (`ih` is not a function / `ih h2`
mismatches). Repair — induct on the SECOND walk (peel its far end):
```lean
theorem GReach.trans {G : SimpleGraph α} {x y z : α}
    (h1 : GReach G x y) (h2 : GReach G y z) : GReach G x z := by
  induction h2 with
  | refl a => exact h1            -- (if h1 is auto-generalized: `intro h; exact h`)
  | append a b c hrec hadj ih => exact GReach.append x b c (ih h1) hadj
```
(h2's first index y occurs in h1 — Lean auto-generalizes h1; if the branch
goals arrive as implications, intro first. Verify at CI.)

**D9 (lines 200-208) — last_exit STATEMENT DOES NOT ELABORATE.**
`⟨val w, _⟩ : β` with `{β : Type}` an abstract variable cannot elaborate
(an anonymous constructor needs a concrete structure; the intended β is
{ x // x ≠ u }). Repair — state it concretely:
```lean
theorem last_exit {α : Type} (G : SimpleGraph α) (u : α) {z : α}
    (hz : z ≠ u) (h : GReach G u z) :
    ∃ w : {x : α // x ≠ u}, G.Adj u w.1 ∧
      GReach (G.comap (Subtype.val : {x : α // x ≠ u} → α)) w ⟨z, hz⟩
```
PROOF WARNING (verified on paper): the naive motive
`fun i j _ => j ≠ u → ∃ w, …` is FALSE at refl (a refl-walk at an arbitrary
a ≠ u proves nothing about u's edges); the induction MUST carry `i = u` in
the motive: `fun i j _ => i = u → j ≠ u → ∃ w, G.Adj u w.1 ∧
GReach (G.comap Subtype.val) w ⟨j, ‹j ≠ u›⟩`. refl: a = u ∧ a ≠ u → absurd.
append (a b c) ih: case b = u → witness ⟨c, _⟩ (the edge u—c, refl-walk);
case b ≠ u → ih (rfl) (b ≠ u) then `GReach.append w ⟨b,_⟩ ⟨c,_⟩ (walk)
(hadj as a (G−u)-edge)`.

**D10 (line 238-243, sqrt_le_of_sq).** Sound statement; the sorry-tail
needs `have : (m+1)*(m+1) = m*m + 2*m + 1 := by ring` before omega (see §2).
h3 is dead code (belongs to the §6/§7 rpow chain).

**D11 (line 66-67, emb4).** `Matrix.cons_val_two` exists (green arsenal
usage, GSTTargetWordRecovery.lean:105); **`Matrix.cons_val_three` is
UNVERIFIED at this pin** — never used by any green kernel, not in the probe.
Probe it; fallback: `Matrix.cons_val_succ` chains (the green arsenal
pattern: cons_val_zero/one/succ/two/head_cons/tail_cons).

**D12 (architecture gap — a missing lemma, not a draft defect).** The
**walk-crossing lemma** (§1 above) is required to extract the D-unreachable
pair (x, y) from the IH's separation sep(G−u) (the "two-class trick"
presupposes it: "since x, y unreachable"). It is absent from the draft AND
from the worklog's §4 lemma inventory. Add it (5-line induction, clean).
Also missing-but-implied: the **isolated-vertex micro-lemma** (§1.2 STEP 3)
— GReach from an isolated vertex stays put — required for the universality
finish. Both are specified in §1 of this audit.

**Minor notes.** (a) P4_adj by Iff.rfl ✓; emb4_zero/one/two/three by rfl ✓;
the 16-cell grid's cell ORDER (i-major after `fin_cases i <;> fin_cases j`)
matches the green convention ✓. (b) sep_class_of_unreachable (lines
150-166): math ✓, script plausible-green (mem_filter, Classical instance
only in the witness) ✓. (c) The two-code P4 detection in the audit engine
agrees on every graph; the P4-free counts match the labeled-cograph
sequence exactly (1, 2, 8, 52, 472, 5504 for n = 1..6) — Seinsche's
theorem itself is thereby exhaustively confirmed for n ≤ 6, on top of the
proof-theoretic verification.

---

## 5. RECEIPTS

* `audit61e_w85.py` — the audit engine (this round, two independent P4
  detectors, constructive instrumentation of every caseA sub-lemma).
* `receipts61e_audit.txt` — 52 PASS / 0 FAIL: S1 Seinsche (exhaustive n ≤ 6
  + sampled n = 7, 8), S2 caseA + UNIFORM-ONLY + S2a/S2b/S2c/S2d/S2e
  (0 violations; 23,724 constructive P4 completions), S3 product law
  (exhaustive n ≤ 6), S4 ψ-iso (16 cells), S6 finisher arithmetic
  (n = 4..20000), S7 base, S8 heredity/complement-freeness (sampled).

## 6. BOTTOM LINE

The ARCHITECTURE ships: the Seinsche route as re-derived here (caseA via
last-exit → flip → two-class → P4 completion → universality finish, applied
symmetrically through the repaired compl_comap and the ψ-bridge) is sound
and complete, with every branch machine-verified to terminate. The DRAFT
does not compile as written: 2 transposed grid cells, 1 false statement
(compl_comap), 1 ill-typed statement (last_exit), 1 broken induction
strategy (trans), 3 malformed structure-field/refl-branch scripts, and 2
missing lemmas (walk-crossing, isolated-vertex) that the worklog's
inventory must name. All repairs are specified above; none re-architects
the route. The single most dangerous finding is compl_comap (D4) — a false
statement sitting on the critical path of the entire complement-symmetric
half of the proof, in a section labeled "believed sound".

The engine never stops; it never lies. In English, always.
