# Four-Power Universal Relocation Lemma Implementation Plan

> **For agentic workers:** REQUIRED SUB-SKILL: Use superpowers:subagent-driven-development (recommended) or superpowers:executing-plans to implement this plan task-by-task. Steps use checkbox (`- [ ]`) syntax for tracking.

**Goal:** Prove, without `sorry`, axioms, quarantined declarations, or circular assumptions, the universal power-specific lemma that transports a physical Happy cell on the `4^K` Graph V2 sheet to some physical Happy cell on the `4^(K+1)` sheet, then use it to construct `FourPowerGraphForcing`, replace the broken monolith theorem, and obtain the literal official-comparator success output.

**Architecture:** Keep the mathematical proof standalone until the universal propagation theorem is kernel-green. Reuse the already-green local split `Happy → Happy ∨ latent`; focus all new mathematics on extracting a later or relocated Happy witness from the latent branch specifically for a four-power sheet. Once propagation and the three finite bases are green, prove `FourPowerGraphForcing` by induction, convert it to `FourPowerCreationMaster` through the existing equivalence, transplant only that completed proof into the monolith, and run the unchanged comparator.

**Tech Stack:** Lean 4.33.0-rc2, Mathlib, GST Graph V2 modules, GitHub Actions as the Lean compilation environment, repository V5 comparator.

**Spec:** This document is the formal handoff specification. Mathematical motivation is in `E:\deep-research-report (4).md`; that report is evidence and a proposed construction, not kernel evidence.

## Global Constraints

- Work on branch `sol/gpt56-canonical-tail-escape-20260827` in repository `kyo-oo/erdosternary2`.
- Do not search the internet.
- Do not install or use a new local Lean installation; compile through GitHub Actions.
- Do not use `sorry`, `admit`, `axiom`, `False.elim` from an unproved contradiction, or declarations whose axiom audit includes `sorryAx`.
- Do not reactivate the quarantined `gst_four_power_creation_certificate_inline` chain.
- Do not use `gst_oscillation_from_navigation`; its historical route explicitly contained unresolved deep cases.
- Do not treat a successful dependency build as proof of the new universal lemma. The exact theorem file must compile and its axiom print must be clean.
- Do not transplant a conditional theorem that accepts `FourPowerCreationMaster`, `FourPowerGraphForcing`, Navigation, or the desired relocation statement as an input.
- Preserve the consumed origin trit as horizontal phase. Never rewrite the regenerated graph back to phase zero without an exact equality.
- A carry value `3` at row `p+1` does not by itself make that cell Happy; its digit must independently be proved equal to `2`.
- Run the production comparator only after the standalone universal theorem and monolith compile are green.
- Completion requires both literal lines: `Your solution is okay!` and `=== COMPARATOR RESULT: PASS ===`.

---

## Exact mathematical target

The final existing proposition is:

```lean
GSTGraphV2FourPowerForcingBridge.FourPowerGraphForcing
```

which unfolds to:

```lean
∀ K : Nat, 5 ≤ K → K ≠ 7 →
  ∃ p : Nat, 1 ≤ p ∧
    GSTCanonicalTailStateIso.HappyCell
      (GSTCanonicalTailStateIso.carry4 (4^K) p)
      (GSTCanonicalTailStateIso.digit3 (4^K) p)
```

The recommended new universal induction edge is represented first as this compilable target proposition:

```lean
def FourPowerHappyPropagation : Prop :=
  ∀ K p : Nat, 8 ≤ K → 1 ≤ p →
    GSTU2DEventTransport.HappyCell
      (GSTGraphV2InfiniteControl.graph 1 K p).seven.carry
      (GSTGraphV2InfiniteControl.graph 1 K p).seven.digit →
    ∃ q : Nat, 1 ≤ q ∧
      GSTU2DEventTransport.HappyCell
        (GSTGraphV2InfiniteControl.graph 1 (K+1) q).seven.carry
        (GSTGraphV2InfiniteControl.graph 1 (K+1) q).seven.digit
```

This formulation deliberately does not demand `q = p` or `q = p+1`. The numerical behavior shows that relocation may be nonlocal. For example, a Happy cell at `K = 8, p = 4` becomes a latent packet in `K = 9`; the next Happy witness occurs later, at `p = 7`.

The historical creation target is:

```lean
GSTFourPowerOntologicalAdapter.FourPowerCreationMaster
```

The already-green theorem

```lean
GSTGraphV2FourPowerForcingBridge.graph_forcing_to_creation_master
```

converts the completed Graph V2 theorem into exactly that proposition. Do not re-prove the conversion.

## What is already kernel-green

### Exact local cascade

File: `GSTGraphV2NonlocalCascade.lean`

Commit: `958e8c6807619c24c4f1061098005de91bffd541`

Successful workflow run: `https://github.com/kyo-oo/erdosternary2/actions/runs/33553382534`

The theorem

```lean
GSTGraphV2NonlocalCascade.four_power_happy_lifts_or_latent
```

proves:

```text
Happy on graph 1 K at p
    ↓ horizontal ×4 wave
Happy on graph 1 (K+1) at p
OR
digit(K+1,p) = 2
carry(K+1,p) ∈ {1,2}
carry(K+1,p+1) = 3
```

The second branch is the exact latent packet. It is conserved information, but it is not yet a Happy witness.

### Exact graph/creation equivalence

File: `GSTGraphV2FourPowerForcingBridge.lean`

Useful declarations:

```lean
FourPowerGraphForcing
graph_forcing_to_creation_master
creation_master_to_graph_forcing
graph_forcing_iff_creation_master
one_trit_phase_regeneration_happy_iff
```

The equivalence prevents weakening the goal. Any purported replacement must actually produce the graph forcing proposition, not rename the missing master.

### Exact graph evolution

Files:

- `GSTGraphV2InfiniteControl.lean`
- `GSTCanonicalSevenAxisBridge.lean`
- `GST2DMixedEmergence.lean`

Useful declarations:

```lean
graph_cell_exact
graph_carry_lt_four
graph_digit_lt_three
canonical_cell_exact
nextCarry
outDigit
```

`graph_cell_exact` supplies both directions of the spacetime cell law:

```lean
outDigit (carry t p) (digit t p) = digit (t+1) p
nextCarry (carry t p) (digit t p) = carry t (p+1)
```

### Infinite controller and non-lossy ledger machinery

Files:

- `GSTInfiniteBadTransport.lean`
- `GSTInfiniteGateTransport.lean`
- `GSTInfiniteCoupledLedger.lean`
- `GSTGraphV2InfiniteControllerBridge.lean`
- `GSTGraphV2CanonicalEscape.lean`
- `GSTGraphV2CanonicalInfiniteCycle.lean`
- `GSTGraphV2CanonicalTerminalExtinctionProbe.lean`

Useful declarations include:

```lean
GSTV2.InfiniteBadCoupledControl
GSTV2.LatentGateTransfer
GSTV2.coupled_happy_transports_information
graph_infinite_bad_control
graph_child_happy_latent_transfer
canonical_latent_gate_packet
canonical_controller_childTail_cut_exact
canonical_origin_packet_nonzero
nat_no_unbounded_ternary_support
infinite_coupled_ledger
```

These theorems certify exact transport and finite natural support. They do not currently construct the relocated Happy position. Use them only through their actual conclusions.

### N-wave and re-coordination machinery

Files:

- `GSTGraphV2CanonicalNWave.lean`
- `GSTGraphV2CanonicalEscape.lean`
- `GSTGraphV2HandwrittenExponentialCascade.lean`

Useful declarations:

```lean
canonical_n_wave_physical
canonical_n_wave_happy_iff
canonical_n_wave_bad_trace_iff
canonicalTail_cut_quotient_exact
canonical_graph_u_cut_recoordinate_exact
```

These preserve the exact phase and residual energy through arbitrary finite cuts. They may be used to move the latent packet to a simpler residual sheet, but the phase term must remain explicit.

## The precise missing derivation

Starting with `hHappy` on `graph 1 K p`, apply:

```lean
four_power_happy_lifts_or_latent K p hHappy
```

The direct branch immediately supplies witness `q := p`.

The only unresolved branch contains:

```lean
hDigit : digit(K+1,p) = 2
hCarry : carry(K+1,p) = 1 ∨ carry(K+1,p) = 2
hNext  : carry(K+1,p+1) = 3
```

The new proof must construct:

```lean
∃ q, 1 ≤ q ∧ digit(K+1,q) = 2 ∧
  (carry(K+1,q) = 0 ∨ carry(K+1,q) = 3)
```

The report incorrectly closes this at `q := p+1` from `hNext`. That conclusion additionally requires:

```lean
digit(K+1,p+1) = 2
```

which is not a conclusion of `gst_pure_lift_or_forced_cascade` or `four_power_happy_lifts_or_latent`.

Therefore the genuine mathematical task is a **power-specific nonlocal relocation theorem**. It must analyze the vertical future of the latent packet together with the special origin `4^(K+1)`, and produce an actual row `q`; a generic arbitrary-digit state-machine theorem is too strong and has counterexamples.

The preferred derivation structure is:

```text
latent packet on the 4^(K+1) sheet
    ↓ exact vertical cell evolution
full future carry/digit orbit
    ↓ exact four-power origin identities + retained horizontal phase
power-specific restriction on any all-bad continuation
    ↓ infinite controller / ledger / finite-support synchronization
construct a finite row q where digit = 2 and carry = 0 or 3
    ↓
physical Happy witness on graph 1 (K+1)
```

The construction may use a least or first row satisfying a proven finite predicate, but it cannot use a fixed computational cutoff as the universal proof.

---

### Task 1: Create the focused relocation probe

**Files:**

- Create: `GSTGraphV2FourPowerRelocation.lean`
- Create: `.github/workflows/sol56-four-power-relocation.yml`

**Interfaces:**

- Consumes: `GSTGraphV2NonlocalCascade.four_power_happy_lifts_or_latent` and the exact Graph V2 cell laws.
- Produces: the compilable target proposition `FourPowerHappyPropagation` and a CI environment for proving it.

- [ ] **Step 1: Write the target proposition with the complete conclusion and no weakening**

```lean
import GSTGraphV2NonlocalCascade
import GSTGraphV2CanonicalEscape
import GSTGraphV2CanonicalInfiniteCycle

set_option maxRecDepth 1000000
set_option maxHeartbeats 20000000

namespace GSTGraphV2FourPowerRelocation

open GSTCanonicalTailStateIso
open GSTU2DEventTransport
open GSTGraphV2InfiniteControl
open GSTGraphV2NonlocalCascade

def FourPowerHappyPropagation : Prop :=
  ∀ K p : Nat, 8 ≤ K → 1 ≤ p →
    HappyCell (graph 1 K p).seven.carry (graph 1 K p).seven.digit →
    ∃ q : Nat, 1 ≤ q ∧
      HappyCell (graph 1 (K+1) q).seven.carry
        (graph 1 (K+1) q).seven.digit

#check FourPowerHappyPropagation

end GSTGraphV2FourPowerRelocation
```

The probe commits only the exact proposition and imports. The first attempted theorem proof belongs in a workflow-generated scratch copy until it has no unsolved goals; do not merge an `admit` or `sorry` version into production.

- [ ] **Step 2: Compile the exact probe in GitHub Actions and capture the first unsolved Lean state**

Workflow command:

```bash
set -euo pipefail
lake build GSTGraphV2CanonicalEscape GSTGraphV2CanonicalInfiniteCycle
lake env lean GSTGraphV2NonlocalCascade.lean
lake env lean GSTGraphV2FourPowerRelocation.lean 2>&1 | tee relocation.log
```

Expected diagnostic: only the latent branch remains. Any import or namespace errors must be fixed before mathematical experimentation.

- [ ] **Step 3: Commit the focused probe infrastructure**

```bash
git add GSTGraphV2FourPowerRelocation.lean .github/workflows/sol56-four-power-relocation.yml
git commit -m "Probe universal four-power latent relocation"
git push origin sol/gpt56-canonical-tail-escape-20260827
```

### Task 2: Derive the power-specific vertical future packet

**Files:**

- Modify: `GSTGraphV2FourPowerRelocation.lean`

**Interfaces:**

- Consumes: the latent triple `hDigit`, `hCarry`, `hNext` and `graph_cell_exact`.
- Produces: a named structure or conjunction retaining every exact state coordinate needed after row `p+1`.

- [ ] **Step 1: Introduce explicit row functions without projecting away information**

```lean
let C : Nat → Nat := fun r => (graph 1 (K+1) (p+1+r)).seven.carry
let d : Nat → Nat := fun r => (graph 1 (K+1) (p+1+r)).seven.digit
have hC0 : C 0 = 3 := by simpa [C] using hNext
have hC_lt : ∀ r, C r < 4 := by
  intro r
  exact graph_carry_lt_four 1 (K+1) (p+1+r)
have hd_lt : ∀ r, d r < 3 := by
  intro r
  exact graph_digit_lt_three 1 (K+1) (p+1+r)
```

- [ ] **Step 2: Prove the exact vertical recurrence for every future row**

```lean
have hVertical : ∀ r,
    GST2DMixedEmergence.nextCarry (C r) (d r) = C (r+1) := by
  intro r
  simpa [C, d, Nat.add_assoc] using
    (graph_cell_exact 1 (K+1) (p+1+r)).2
```

- [ ] **Step 3: Express the negation of the required witness as an exact all-bad future language**

```lean
have hFutureBad : ∀ r, ¬ HappyCell (C r) (d r) := by
  intro r h
  apply hNoRelocated
  exact ⟨p+1+r, by omega, by simpa [C, d] using h⟩
```

Here `hNoRelocated` must arise only inside a proof-by-contradiction or witness-extraction argument for `four_power_happy_propagates`; it must not become an additional theorem parameter.

- [ ] **Step 4: Commit after the exact future packet compiles cleanly**

```bash
git add GSTGraphV2FourPowerRelocation.lean
git commit -m "Expose exact vertical future of latent four-power packet"
git push origin sol/gpt56-canonical-tail-escape-20260827
```

### Task 3: Connect the future packet to four-power origin arithmetic

**Files:**

- Modify: `GSTGraphV2FourPowerRelocation.lean`
- Read only: `GSTGraphV2CanonicalEscape.lean`
- Read only: `GSTGraphV2CanonicalNWave.lean`

**Interfaces:**

- Consumes: `C`, `d`, `hVertical`, and the exact identity `graph 1 (K+1) =` the arithmetic sheet for `4^(K+1)`.
- Produces: a finite-support cutoff and exact residual state at that cutoff, with every phase term explicit.

- [ ] **Step 1: Prove a symbolic finite-support cutoff rather than choosing a constant**

Use a bound derived from `K`, for example a proved exponent `B K` satisfying:

```lean
4^(K+1) < 3^(B K)
```

Then derive:

```lean
digit3 (4^(K+1)) (B K) = 0
```

and the exact corresponding graph state. The bound must be proved for all `K` in the theorem domain.

- [ ] **Step 2: Re-coordinate through the exact N-wave identity if the controller representation is used**

Every application of `canonical_n_wave_physical` or `canonical_graph_u_cut_recoordinate_exact` must retain its returned phase:

```lean
uPhaseShift (...) + x
```

Do not replace it by `0`, and do not simplify `graph 1 P` to `graph 1 0` unless `P = 0` has separately been proved.

- [ ] **Step 3: Prove the power-specific obstruction to an all-bad future**

The theorem must have a conclusion that directly yields a witness, such as:

```lean
∃ r, HappyCell (C r) (d r)
```

or an exact finite disjunction whose branches each produce such an `r`. It must consume a property unique to the `4^(K+1)` origin; a theorem about arbitrary terminating ternary words is not sufficient and is generally false.

- [ ] **Step 4: Compile and print axioms**

Append:

```lean
#check four_power_happy_propagates
#print axioms four_power_happy_propagates
```

Workflow acceptance checks:

```bash
lake env lean GSTGraphV2FourPowerRelocation.lean 2>&1 | tee relocation.log
! grep -E 'declaration uses .sorry.|sorryAx|unknown identifier|unsolved goals' relocation.log
```

- [ ] **Step 5: Commit only after the exact universal propagation theorem is green**

```bash
git add GSTGraphV2FourPowerRelocation.lean
git commit -m "Prove universal four-power Happy relocation"
git push origin sol/gpt56-canonical-tail-escape-20260827
```

### Task 4: Build `FourPowerGraphForcing` by induction

**Files:**

- Modify: `GSTGraphV2FourPowerRelocation.lean`

**Interfaces:**

- Consumes: `four_power_happy_propagates`.
- Produces: `four_power_graph_forcing : FourPowerGraphForcing`.

- [ ] **Step 1: Prove the three explicit bases with concrete witnesses**

Use the repository definitions and let `norm_num` verify the arithmetic:

```lean
have h5 : ∃ p, 1 ≤ p ∧ HappyCell (carry4 (4^5) p) (digit3 (4^5) p) := by
  refine ⟨2, by decide, ?_⟩
  norm_num [HappyCell, carry4, digit3]

have h6 : ∃ p, 1 ≤ p ∧ HappyCell (carry4 (4^6) p) (digit3 (4^6) p) := by
  refine ⟨2, by decide, ?_⟩
  norm_num [HappyCell, carry4, digit3]

have h8 : ∃ p, 1 ≤ p ∧ HappyCell (carry4 (4^8) p) (digit3 (4^8) p) := by
  refine ⟨4, by decide, ?_⟩
  norm_num [HappyCell, carry4, digit3]
```

- [ ] **Step 2: Prove all `K ≥ 8` by induction from `h8`**

At the successor step, translate the arithmetic Happy witness to `graph 1 K p`, call `four_power_happy_propagates`, and translate the returned graph witness back to `carry4`/`digit3`. Use existing graph vertex definitions or a small exact adapter lemma; do not assume definitional equality without checking it.

- [ ] **Step 3: Assemble the full exception-aware theorem**

```lean
theorem four_power_graph_forcing : FourPowerGraphForcing := by
  intro K hK5 hK7
  interval_cases K
  · exact h5
  · exact h6
  · exact False.elim (hK7 rfl)
  · exact hAllFromEight 8
  · exact hAllFromEight K
```

The concrete syntax may instead use arithmetic cases if `interval_cases` does not leave the intended goals. The only use of `False.elim` permitted here is the explicit impossible hypothesis `K = 7` together with `K ≠ 7`.

- [ ] **Step 4: Convert to the production master and audit both declarations**

```lean
theorem four_power_creation_master : FourPowerCreationMaster :=
  graph_forcing_to_creation_master four_power_graph_forcing

#print axioms four_power_graph_forcing
#print axioms four_power_creation_master
```

- [ ] **Step 5: Run the exact theorem CI and commit**

```bash
lake env lean GSTGraphV2FourPowerRelocation.lean 2>&1 | tee four-power-universal.log
! grep -E 'declaration uses .sorry.|sorryAx|unknown identifier|unsolved goals' four-power-universal.log
```

```bash
git add GSTGraphV2FourPowerRelocation.lean .github/workflows/sol56-four-power-relocation.yml
git commit -m "Construct four-power creation master from Graph V2 relocation"
git push origin sol/gpt56-canonical-tail-escape-20260827
```

### Task 5: Perform the monolith surgery

**Files:**

- Modify: `ErdosTernary2.lean` near theorem `gst_four_power_creation_master_inline` (currently around line 16934).
- Modify only if required by import closure: `lakefile.toml` or the existing module-root configuration.

**Interfaces:**

- Consumes: the completed, axiom-clean proof term for `FourPowerCreationMaster`.
- Produces: a compiling `gst_four_power_creation_master_inline` with no reference to `gst_four_power_creation_certificate_inline`.

- [ ] **Step 1: Remove the broken identifier use**

Delete this proof body:

```lean
by
  intro K hK5 hK7
  simpa [GSTFourPowerOntologicalAdapter.CreationCertificate] using
    (gst_four_power_creation_certificate_inline K hK5 hK7)
```

- [ ] **Step 2: Insert the completed master proof**

If the standalone module can be imported without an import cycle, use its theorem directly. If it imports the monolith, transplant the already-compiled proof and its genuinely required standalone helpers into the production location. Do not copy unrelated experiment modules into the monolith.

Add `import GSTGraphV2FourPowerRelocation` to the monolith import block after confirming the standalone module does not import `ErdosTernary2`. The resulting theorem must retain the exact public signature and use the completed standalone declaration directly:

```lean
theorem gst_four_power_creation_master_inline :
    GSTFourPowerOntologicalAdapter.FourPowerCreationMaster := by
  exact GSTGraphV2FourPowerRelocation.four_power_creation_master
```

- [ ] **Step 3: Verify the obsolete route is absent from the active declaration graph**

```bash
rg -n "gst_four_power_creation_certificate_inline|gst_oscillation_from_navigation" ErdosTernary2.lean
```

Expected: occurrences may remain only inside clearly quarantined comments; no active production theorem may reference them.

- [ ] **Step 4: Compile the exact monolith in GitHub Actions**

```bash
set -euo pipefail
lake env lean ErdosTernary2.lean 2>&1 | tee monolith.log
! grep -E 'unknown identifier|unsolved goals|declaration uses .sorry.' monolith.log
```

- [ ] **Step 5: Audit the production theorem chain**

Create a temporary audit file containing:

```lean
import ErdosTernary2

#print axioms gst_four_power_creation_master_inline
#print axioms gst_prefix_one_navigation_lift
#print axioms erdos_ternary_2_universal
```

Run:

```bash
lake env lean FinalFourPowerAudit.lean 2>&1 | tee final-four-power-axioms.log
! grep -F 'sorryAx' final-four-power-axioms.log
```

- [ ] **Step 6: Commit the surgery only after monolith compilation and axiom audit pass**

```bash
git add ErdosTernary2.lean
git commit -m "Replace quarantined four-power creation theorem with Graph V2 proof"
git push origin sol/gpt56-canonical-tail-escape-20260827
```

### Task 6: Run and certify the unchanged comparator

**Files:**

- Do not modify: `scripts/comparator.sh`
- Do not modify: comparator configuration or challenge statement.

**Interfaces:**

- Consumes: the committed, compiling monolith.
- Produces: literal comparator success evidence tied to the final commit SHA.

- [ ] **Step 1: Run the repository V5 comparator in GitHub Actions**

```bash
set -euo pipefail
bash scripts/comparator.sh 2>&1 | tee final-v5-comparator.log
grep -F 'Your solution is okay!' final-v5-comparator.log
grep -F '=== COMPARATOR RESULT: PASS ===' final-v5-comparator.log
```

- [ ] **Step 2: Record the exact evidence**

Report:

```text
final commit SHA
universal-relocation workflow URL
monolith compilation workflow URL
comparator workflow URL
literal comparator success lines
```

- [ ] **Step 3: Stop only at the real terminal condition**

The task is complete only if the committed production monolith compiles, the relevant declarations are free of `sorryAx`, and the unchanged comparator emits both required success lines. A green helper theorem or successful experiment is progress, not completion.

---

## Failure interpretations for Sol

- `Unknown identifier gst_four_power_creation_certificate_inline`: the old quarantined theorem is still wired into production. This is a surgery failure, not a new mathematical result.
- Goal contains only the latent triple and asks for a Happy existential: this is the intended universal-relocation problem. Continue the mathematical derivation there.
- A proof requires `digit(K+1,p+1)=2`: derive it or construct a different row `q`; do not infer it from `carry(K+1,p+1)=3`.
- A proposed lemma accepts `FourPowerGraphForcing`, `FourPowerCreationMaster`, Navigation, or the desired Happy existential: it is circular and cannot close the production DAG.
- A generic theorem about arbitrary finite ternary words fails: narrow it to the exact `4^(K+1)` origin and retain the Graph V2 phase.
- A theorem prints only standard Lean axioms such as `propext`, `Classical.choice`, and `Quot.sound`: acceptable under the existing project policy. Any `sorryAx`: unacceptable.
- Comparator does not run because monolith compilation fails: fix the monolith first; do not report comparator success or completion.

## Final acceptance checklist

- [ ] `GSTGraphV2NonlocalCascade.four_power_happy_lifts_or_latent` remains green.
- [ ] `four_power_happy_propagates` is proved for all `K ≥ 8` and every supplied physical Happy witness.
- [ ] The latent branch constructs an actual row `q`; no digit equality is assumed.
- [ ] Bases `K = 5`, `K = 6`, and `K = 8` compile by exact arithmetic.
- [ ] `four_power_graph_forcing : FourPowerGraphForcing` is kernel-green.
- [ ] `four_power_creation_master : FourPowerCreationMaster` is kernel-green.
- [ ] `gst_four_power_creation_master_inline` no longer references `gst_four_power_creation_certificate_inline`.
- [ ] The monolith compiles.
- [ ] Axiom audit contains no `sorryAx`.
- [ ] The unchanged comparator prints `Your solution is okay!`.
- [ ] The unchanged comparator prints `=== COMPARATOR RESULT: PASS ===`.
