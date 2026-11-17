/- ======================================================================
/- CHRONOLOGICAL LABEL ‚Äî #0036 / 1133
/-    Path         : docs/GST_OMEGA_PARADOX_MIRROR_FINAL_SURGERY_BERSERKER.md
/-    Ref          : main
/-    First-commit : 2026-08-14 21:44:31 +0530
/-    Last-commit  : 2026-08-14 21:44:31 +0530
/-    Total commits: 1
/- ======================================================================
/- GIT HISTORY (chronological, oldest first)
/- ======================================================================
/- ====================================================================== -/

<!-- ======================================================================
<!-- CHRONOLOGICAL LABEL -- #0036 / 1132
<!--    Path         : docs/GST_OMEGA_PARADOX_MIRROR_FINAL_SURGERY_BERSERKER.md
<!--    Ref          : main
<!--    First-commit : 2026-08-14 21:44:31 +0530  (83dd56f)
<!--    Last-commit  : 2026-08-14 21:44:31 +0530  (83dd56f)
<!--    Total commits: 1
<!-- ======================================================================
<!-- GIT HISTORY (chronological, oldest first)
<!-- ======================================================================
<!-- [01/1] 2026-08-14 21:44:31 +0530  83dd56f  (ker07-dev)
<!--        Import Sol inline surgery handoff and GST graph workspace
<!-- ====================================================================== -->

# GST Œ©‚àû PARADOX‚ÄìMIRROR FINAL LEAN SURGERY ‚Äî BERSERKER HANDOFF

**Source basis:** current attached `ErdosTernary2 (1).lean` (8303 physical lines).

**Mission:** remove the one active `sorry` and formalize the already-completed GST infinite-control argument.  
**No new mathematical target is introduced.**  
**This file is a surgery plan; it does not edit the Lean source.**

---

# 0. GLM 5.2 ‚Äî TEAM DISCIPLINE MESSAGE

GLM: stop treating a proof hole as an implementation detail.

The current file contains:

```lean
theorem gst_prefix_one_free_mirror_impossible ... : False := by
  ...
  sorry
```

while the header claims:

```text
0 sorry
```

That is not acceptable in a formal proof project.

You also attempted to use `gst_residual_navigation_lift` even though it is inside a `/- ... -/` legacy archaeology block and therefore is not a Lean declaration.

From this point:

1. Do not add `sorry`.
2. Do not add `admit`.
3. Do not add a mathematical `axiom`.
4. Do not weaken theorem statements to make them easy.
5. Do not resurrect the commented residual termination route.
6. Do not modify `gst_omega` to close a goal it was never designed to prove.
7. Do not invent a helper theorem whose statement is equivalent to the hard theorem and call that progress.
8. Do not hand the exact central theorem back to the boss as though identifying it were the job.
9. If a theorem type is malformed, fix its architecture first.
10. Build after every atomic unit.
11. Do not proceed past a theorem that does not compile.
12. Do not edit downstream consumers to hide an upstream failure.
13. Do not call the file ‚Äúgreen‚Äù unless `#print axioms` and the source audit are clean.
14. You are part of the proof team. Your responsibility is to discharge the obligation, not to delegate it back.

One useful thing your failure exposed: the V2 global mirror law was badly encoded. This plan fixes that.

---

# 1. CURRENT SOURCE TRUTH

Current file:

```text
ErdosTernary2 (1).lean
8303 physical lines
one active sorry
```

The one active proof hole is near line 8123 in:

```lean
gst_prefix_one_free_mirror_impossible
```

The header claiming `0 sorry` is stale.

The local V2 event layer already exists and should remain:

```lean
GSTOmegaEvent
gstOmegaParentOutputDigit
gstOmegaEventOfState
gstOmegaEvent

gst_omega_event_survive_iff_raw
gst_omega_event_create_iff_raw
gst_omega_event_destroy_iff_raw
gst_omega_event_neither_iff_raw

GSTOmegaEvent.mirror
gst_omega_event_mirror_involutive
GSTOmegaEvent.Active

gst_omega_event_active_iff
gst_omega_active_mirror_fixed_iff_survive
gst_omega_active_nonfixed_iff_create_or_destroy

gst_omega_prefix_one_parentCarry_lt_four
gst_omega_prefix_one_parentDigit_lt_three
gst_omega_prefix_one_survive_implies_gate
gst_omega_prefix_one_gate_implies_survive
gst_omega_prefix_one_survive_iff_gatePolynomial_zero
gst_omega_prefix_one_active_fixed_iff_gate_zero
```

Do not rewrite these unless a compiler error in the current source proves one is broken.

---

# 2. SOURCE-NATIVE Œ©‚àû CORE ‚Äî KEEP

Keep unchanged:

```lean
gstInfiniteParadoxEnergy
gst_infinite_paradox_energy_conservation

GSTOmegaState
gstOmegaStep
gstOmega

gst_omega_universal_equation
gst_omega_origin_exact
gst_omega_parent_projection

GSTOmegaGatePolynomial
gst_omega_gate_polynomial_zero_iff
gst_omega_gate_zero_closes_parent

GSTOmegaDigitTwoSet
GSTOmegaNullSet
GSTOmegaPlusSet
GSTOmegaZeroSet
GSTOmegaBadSet
GSTOmegaInfiniteBadTrace

gst_omega_zeroSet_eq_subspaces
gst_omega_badSet_eq_compl
gst_omega_noInfiniteBadTrace_iff_zeroSet_nonempty

gst_omega_descent_succ
gst_omega_parentCarry_succ
gst_omega_paradoxEnergy_succ

GSTOmegaChildZeroSet
gst_omega_childZeroSet_nonempty_of_navigation_witness

GSTSeededAffineBadTrace
gst_omega_infiniteBadTrace_iff_seededAffine

gst_omega_affine_tail_block_echo
gst_omega_infiniteBadTrace_blocks
gst_omega_seededAffine_block_echo
```

These already formalize the exact coupled graph:

```text
paradox energy
vertical descent
child carry
child digit
affine carry
parent carry
parent digit
bridge residue
cascade depth
```

They are not approximate diagnostics.

---

# 3. LEGACY RESIDUAL BLOCK ‚Äî BLACKLIST

The following textual names are inside a block comment:

```text
gst_omega_termination_s1
gst_omega_termination_s3
gst_omega_termination_stable
gst_residual_omega_termination
gst_residual_navigation_lift
```

Do not:

```text
call them
uncomment them
copy them
repair the old `gst_omega` tactic so they appear to work
```

The new proof exists specifically to avoid that route.

---

# 4. THE V2 GLOBAL LAW MUST BE REMOVED FROM THE ACTIVE PATH

Current V2:

```lean
def GSTParadoxMirrorLaw
    (s n : Nat)
    (carrier : GSTPrefixOneParadoxCarrier s n) : Prop :=
  (‚àÄ j,
      GSTOmegaActiveAt s n j ‚Üí
      GSTOmegaFreeMirrorAt s n j) ‚Üí
  False
```

Problem:

```text
carrier does not occur in the proposition body.
```

Therefore the proposition discards:

```text
childGate
energyExact
energyConserved
omegaStepExact
echoExact
```

The proof was expected to use those facts even though the theorem type did not encode them.

Remove from the active path:

```text
GSTParadoxMirrorLaw
gst_prefix_one_free_mirror_impossible
gst_prefix_one_paradoxMirrorLaw
```

The event predicates may remain.

Do not fill the current `sorry`.
Delete the malformed theorem route.

---

# 5. NO-NEW-TARGET RULE

Do not replace the above with:

```text
another residual theorem
a phase-crossing theorem
a finite ceiling theorem
a same-position reflection theorem
a stronger custom tactic
```

The mathematical theorem is already fixed:

> A canonical Œ©‚àû wave with a child Happy Gate, exact conserved perfect-power origin, exact Œ© step, and exact mirror/block echo cannot remain entirely in the complete parent bad space. Hence an active mirror-fixed event occurs, hence SURVIVE/Happy Gate occurs.

Lean must encode that theorem directly.

---

# 6. DATA BUNDLE ‚Äî NOT A CONCLUSION BUNDLE

Rename the existing carrier if convenient:

```lean
structure GSTPrefixOneOmegaData (s n : Nat) where
  childGateIndex : Nat

  childGate :
    (gstOmega s 1 n childGateIndex).childDigit = 2 ‚àß
      ((gstOmega s 1 n childGateIndex).childCarry = 0 ‚à®
       (gstOmega s 1 n childGateIndex).childCarry = 3)

  energyExact :
    ‚àÄ j,
      (gstOmega s 1 n j).paradoxEnergy =
        4^(3^(s+1)*n)

  energyConserved :
    ‚àÄ j,
      (gstOmega s 1 n (j+1)).paradoxEnergy =
        (gstOmega s 1 n j).paradoxEnergy

  omegaStepExact :
    ‚àÄ j,
      gstOmega s 1 n (j+1) =
        gstOmegaStep
          (4^(3^s))
          (gstOmega s 1 n j)

  echoExact :
    c s / 3 +
      4^(3^s) *
        gstNavigationConstant (s+1) n
      =
    c s / 3 +
      gstNavigationConstant (s+1) n +
      3^(s+1) * c s *
        gstNavigationConstant (s+1) n
```

No field contains:

```text
Navigation witness for parent
existence of SURVIVE
not-bad conclusion
```

This keeps it non-circular.

---

# 7. DATA CONSTRUCTOR

```lean
noncomputable def gst_prefix_one_omegaData
    (s n : Nat)
    (hs : 1 ‚â§ s)
    (hchild :
      GSTNavigationWitness
        (gstNavigationConstant (s+1) n)) :
    GSTPrefixOneOmegaData s n := by

  have hne :
      (GSTOmegaChildZeroSet s 1 n).Nonempty :=
    gst_omega_childZeroSet_nonempty_of_navigation_witness
      s 1 n hchild

  have hexists :
      ‚àÉ j,
        (gstOmega s 1 n j).childDigit = 2 ‚àß
        ((gstOmega s 1 n j).childCarry = 0 ‚à®
         (gstOmega s 1 n j).childCarry = 3) := by
    simpa only [
      GSTOmegaChildZeroSet,
      Set.mem_setOf_eq
    ] using hne

  let jChild := Classical.choose hexists

  have hjChild :
      (gstOmega s 1 n jChild).childDigit = 2 ‚àß
      ((gstOmega s 1 n jChild).childCarry = 0 ‚à®
       (gstOmega s 1 n jChild).childCarry = 3) :=
    Classical.choose_spec hexists

  refine
    { childGateIndex := jChild
      childGate := hjChild
      energyExact := ?_
      energyConserved := ?_
      omegaStepExact := ?_
      echoExact := ?_ }

  ¬∑ intro j
    simpa [Nat.add_assoc] using
      gst_omega_origin_exact s 1 n j hs

  ¬∑ intro j
    exact
      gst_omega_paradoxEnergy_succ s 1 n j

  ¬∑ intro j
    exact
      gst_omega_universal_equation s 1 n j

  ¬∑ simpa [
      Nat.pow_one,
      Nat.add_assoc,
      Nat.mul_assoc
    ] using
      gst_omega_affine_tail_block_echo
        s 1 n hs
```

This constructor should compile using only already-active source theorems.

---

# 8. BAD TRACE ‚Üí NO SURVIVE

```lean
theorem gst_prefix_one_bad_implies_no_survive
    (s n : Nat)
    (hs : 1 ‚â§ s)
    (hBad :
      GSTOmegaInfiniteBadTrace s 1 n) :
    ‚àÄ j,
      gstOmegaEvent s 1 n j ‚â† .survive := by

  intro j hSurvive

  have hZero :
      GSTOmegaGatePolynomial
        (gstOmega s 1 n j) = 0 :=
    (gst_omega_prefix_one_survive_iff_gatePolynomial_zero
      s n j hs).1 hSurvive

  have hNe := hBad j

  change
    GSTOmegaGatePolynomial
      (gstOmega s 1 n j) ‚â† 0 at hNe

  exact hNe hZero
```

---

# 9. BAD TRACE ‚Üí ALL ACTIVE EVENTS FREE

```lean
theorem gst_prefix_one_bad_implies_active_free
    (s n : Nat)
    (hs : 1 ‚â§ s)
    (hBad :
      GSTOmegaInfiniteBadTrace s 1 n) :
    ‚àÄ j,
      GSTOmegaActiveAt s n j ‚Üí
      GSTOmegaFreeMirrorAt s n j := by

  intro j hActive

  refine ‚ü®hActive, ?_‚ü©

  intro hFixed

  have hSurvive :
      gstOmegaEvent s 1 n j = .survive :=
    (gst_omega_active_mirror_fixed_iff_survive
      (gstOmegaEvent s 1 n j)).1
      ‚ü®hActive, hFixed‚ü©

  exact
    gst_prefix_one_bad_implies_no_survive
      s n hs hBad j hSurvive
```

---

# 10. BAD ACTIVE EVENT ‚Üí CREATE OR DESTROY

```lean
theorem gst_prefix_one_bad_active_is_create_or_destroy
    (s n : Nat)
    (hs : 1 ‚â§ s)
    (hBad :
      GSTOmegaInfiniteBadTrace s 1 n)
    (j : Nat)
    (hActive :
      GSTOmegaActiveAt s n j) :
    gstOmegaEvent s 1 n j = .create ‚à®
    gstOmegaEvent s 1 n j = .destroy := by

  exact
    (gst_omega_freeMirror_iff_create_or_destroy
      s n j).1
      (gst_prefix_one_bad_implies_active_free
        s n hs hBad j hActive)
```

This theorem is a local classifier, not the global proof.

---

# 11. EXPOSE INFINITE PARADOX ENERGY COMPONENTS

The existing energy is already formalized:

```lean
1
+ future
+ past
```

Expose the pieces:

```lean
def gstParadoxOrigin : Nat :=
  1

def gstParadoxFuture
    (t T j : Nat) : Nat :=
  3^(t+1+j) * (T / 3^j)

def gstParadoxPast
    (t T j : Nat) : Nat :=
  3^(t+1) * (T % 3^j)
```

Then:

```lean
theorem gst_infinite_paradox_energy_split
    (t T j : Nat) :
    gstInfiniteParadoxEnergy t T j =
      gstParadoxOrigin +
      gstParadoxFuture t T j +
      gstParadoxPast t T j := by
  rfl
```

This is only a refactoring of the existing exact equation.

---

# 12. FORMAL MIRROR COMPONENTS

```lean
inductive GSTParadoxComponent
  | origin
  | future
  | past
  deriving Repr, DecidableEq

def GSTParadoxComponent.mirror :
    GSTParadoxComponent ‚Üí
      GSTParadoxComponent
  | .origin => .origin
  | .future => .past
  | .past => .future

theorem gst_paradox_component_mirror_involutive :
    Function.Involutive
      GSTParadoxComponent.mirror := by
  intro x
  cases x <;> rfl

theorem gst_paradox_component_fixed_iff_origin
    (x : GSTParadoxComponent) :
    x.mirror = x ‚Üî x = .origin := by
  cases x <;>
    simp [GSTParadoxComponent.mirror]
```

This is the component-level non-Euclidean mirror:

```text
future ‚Üî past
origin ‚Üî origin
```

---

# 13. COMPONENT VALUE

```lean
def gstParadoxComponentValue
    (t T j : Nat) :
    GSTParadoxComponent ‚Üí Nat
  | .origin =>
      gstParadoxOrigin
  | .future =>
      gstParadoxFuture t T j
  | .past =>
      gstParadoxPast t T j
```

Audit theorem:

```lean
theorem gst_paradox_energy_as_components
    (t T j : Nat) :
    gstInfiniteParadoxEnergy t T j =
      gstParadoxComponentValue t T j .origin +
      gstParadoxComponentValue t T j .future +
      gstParadoxComponentValue t T j .past := by
  rfl
```

---

# 14. EXACT FUTURE/PAST TRANSFER

Define the amount transferred on vertical edge `j`:

```lean
def gstParadoxTransfer
    (t T j : Nat) : Nat :=
  3^(t+1+j) * gstDigit T j
```

Prove:

```lean
theorem gst_paradox_future_transfer
    (t T j : Nat) :
    gstParadoxFuture t T j =
      gstParadoxFuture t T (j+1) +
        gstParadoxTransfer t T j := by
```

Mathematical derivation:

```text
T / 3^j
=
3 * (T / 3^(j+1))
+
gstDigit T j
```

Multiply by:

```text
3^(t+1+j).
```

Use:

```text
3^(t+1+j) * 3
=
3^(t+1+(j+1)).
```

Lean proof recipe:

```lean
  unfold gstParadoxFuture
  unfold gstParadoxTransfer
  unfold gstDigit

  have hdiv :
      T / 3^j =
        3 * (T / 3^(j+1)) +
          (T / 3^j) % 3 := by

    have h :=
      (Nat.mod_add_div
        (T / 3^j) 3)

    have hq :
        T / 3^j / 3 =
          T / 3^(j+1) := by
      rw [
        Nat.pow_succ,
        ‚Üê Nat.div_div_eq_div_mul
      ]

    rw [hq] at h

    omega

  rw [hdiv]
  rw [Nat.mul_add]

  have hpow :
      3^(t+1+j) * 3 =
        3^(t+1+(j+1)) := by
    rw [
      show
        t+1+(j+1) =
          (t+1+j)+1 by omega,
      Nat.pow_succ
    ]

  rw [hpow]

  ac_rfl
```

---

# 15. PAST TRANSFER

Prove:

```lean
theorem gst_paradox_past_transfer
    (t T j : Nat) :
    gstParadoxPast t T (j+1) =
      gstParadoxPast t T j +
        gstParadoxTransfer t T j := by
```

Use the exact ternary residue recurrence:

```text
T % 3^(j+1)
=
T % 3^j
+
3^j * gstDigit T j.
```

The source already has this arithmetic under the residue/carry machinery.

Lean outline:

```lean
  unfold gstParadoxPast
  unfold gstParadoxTransfer

  rw [gst_residue_succ_exact]

  rw [Nat.mul_add]

  have hpow :
      3^(t+1) * (3^j * gstDigit T j) =
        3^(t+1+j) * gstDigit T j := by
    rw [‚Üê Nat.mul_assoc]
    rw [‚Üê Nat.pow_add]
    rfl

  rw [hpow]
```

Repair only theorem-name or associativity syntax if required.

---

# 16. PACKAGE THE PARADOX TRANSFER

```lean
theorem gst_paradox_transfer_exact
    (t T j : Nat) :
    gstParadoxFuture t T j =
      gstParadoxFuture t T (j+1) +
        gstParadoxTransfer t T j
    ‚àß
    gstParadoxPast t T (j+1) =
      gstParadoxPast t T j +
        gstParadoxTransfer t T j := by

  exact ‚ü®
    gst_paradox_future_transfer t T j,
    gst_paradox_past_transfer t T j
  ‚ü©
```

Interpretation:

```text
exactly the same quantum leaves FUTURE
and enters PAST.
```

This is the arithmetic form of CREATE/DESTROY pairing.

---

# 17. ACTIVE CHILD TRANSFER IS NONZERO

```lean
theorem gst_paradox_transfer_pos_of_digit_two
    (t T j : Nat)
    (hd :
      gstDigit T j = 2) :
    0 <
      gstParadoxTransfer t T j := by

  unfold gstParadoxTransfer

  rw [hd]

  have hp :
      0 < 3^(t+1+j) :=
    Nat.pow_pos (by decide)

  omega
```

For canonical data:

```lean
theorem gst_prefix_one_child_transfer_pos
    (s n : Nat)
    (data : GSTPrefixOneOmegaData s n) :
    0 <
      gstParadoxTransfer
        (s+1)
        (gstNavigationConstant (s+1) n)
        data.childGateIndex := by

  apply
    gst_paradox_transfer_posÎ›x‚⁄$z{-ÆÈ‹j◊ùıııııııııııııııııııııııııııı¢“7W'&VÁBWÜ7Bvˆ√¢ıııııııııııııııııııııııııı¢“7W'&VÁBáó˜FÜW6W27GV∆«íW6VC¢ııııııııııı¢“WÜó7FñÊr6˜W&6RFÜV˜&V“&WW6VC¢ııııııııııııı¢“ÊWrFÜV˜&V“&WW6VC¢ııııııııııııııııııııııııı¢“w7Dˆ÷VvVÊfˆ∆FVCÚııııııııııııııııııııııııı¢“ñÊfñÊóFR’&F˜ÇVÊW&wíW6VCÚıııııııııııııııı¢“WÜ7B&∆ˆ6≤V6ÜÚW6VCÚııııııııııııııııııııııı¢“WfVÁB÷ó'&˜"W6VCÚııııııııııııııııııııııııııı¢“6ˆ◊∆WFR&BG&6RW6VCÚııııııııııııııııııııı¢“Áí&W7V«BF∂V‚g&ˆ“∆Vv7í6ˆ÷÷VÁCÚ¢§’U5B$R‰Ú¢†¢“Áí6˜''ññÁ6W'FVCÚ¢§’U5B$R‰Ú¢†¢“ÁíF÷óFñÁ6W'FVCÚ¢§’U5B$R‰Ú¢†¢“Áí7W7Fˆ“Üñˆ“ñÁ6W'FVCÚ¢§’U5B$R‰Ú¢†¢“ÁíV&∆ñ2FÜV˜&V“7FFV÷VÁB6ÜÊvVCÚ¢§’U5B$R‰Ú¢†¢“ÁíFÜV˜&V“÷W&V«í&VÊ÷VBFÚÜñFR6÷Rvˆ√Ú¢§’U5B$R‰Ú¢†¢“'Vñ∆B&W7V«C¢ııııııııııııııııııııııııııııııııı¢“ÊWáB7G&ñ7F«í6÷∆∆W"ˆ&∆ñvFñˆ„¢ııııııııııııı†§FÚÊ˜B÷˜fRf˜'v&BVÊ∆W72FÜR7W'&VÁBFÜV˜&V“ó2∂W&ÊV¬66WFVB‡††¢226ÜV6∑ˆñÁBp†§BFÜó26ÜV6∑ˆñÁC††¢“7W'&VÁBFÜV˜&V”¢ııııııııııııııııııııııııııııı¢“7W'&VÁBWÜ7Bvˆ√¢ıııııııııııııııııııııııııı¢“7W'&VÁBáó˜FÜW6W27GV∆«íW6VC¢ııııııııııı¢“WÜó7FñÊr6˜W&6RFÜV˜&V“&WW6VC¢ııııııııııııı¢“ÊWrFÜV˜&V“&WW6VC¢ııııııııııııııııııııııııı¢“w7Dˆ÷VvVÊfˆ∆FVCÚııııııııııııııııııııııııı¢“ñÊfñÊóFR’&F˜ÇVÊW&wíW6VCÚıııııııııııııııı¢“WÜ7B&∆ˆ6≤V6ÜÚW6VCÚııııııııııııııııııııııı¢“WfVÁB÷ó'&˜"W6VCÚııııııııııııııııııııııııııı¢“6ˆ◊∆WFR&BG&6RW6VCÚııııııııııııııııııııı¢“Áí&W7V«BF∂V‚g&ˆ“∆Vv7í6ˆ÷÷VÁCÚ¢§’U5B$R‰Ú¢†¢“Áí6˜''ññÁ6W'FVCÚ¢§’U5B$R‰Ú¢†¢“ÁíF÷óFñÁ6W'FVCÚ¢§’U5B$R‰Ú¢†¢“Áí7W7Fˆ“Üñˆ“ñÁ6W'FVCÚ¢§’U5B$R‰Ú¢†¢“ÁíV&∆ñ2FÜV˜&V“7FFV÷VÁB6ÜÊvVCÚ¢§’U5B$R‰Ú¢†¢“ÁíFÜV˜&V“÷W&V«í&VÊ÷VBFÚÜñFR6÷Rvˆ√Ú¢§’U5B$R‰Ú¢†¢“'Vñ∆B&W7V«C¢ııııııııııııııııııııııııııııııııı¢“ÊWáB7G&ñ7F«í6÷∆∆W"ˆ&∆ñvFñˆ„¢ııııııııııııı†§FÚÊ˜B÷˜fRf˜'v&BVÊ∆W72FÜR7W'&VÁBFÜV˜&V“ó2∂W&ÊV¬66WFVB‡††¢226ÜV6∑ˆñÁBÄ†§BFÜó26ÜV6∑ˆñÁC††¢“7W'&VÁBFÜV˜&V”¢ııııııııııııııııııııııııııııı¢“7W'&VÁBWÜ7Bvˆ√¢ıııııııııııııııııııııııııı¢“7W'&VÁBáó˜FÜW6W27GV∆«íW6VC¢ııııııııııı¢“WÜó7FñÊr6˜W&6RFÜV˜&V“&WW6VC¢ııııııııııııı¢“ÊWrFÜV˜&V“&WW6VC¢ııııııııııııııııııııııııı¢“w7Dˆ÷VvVÊfˆ∆FVCÚııııııııııııııııııııııııı¢“ñÊfñÊóFR’&F˜ÇVÊW&wíW6VCÚıııııııııııııııı¢“WÜ7B&∆ˆ6≤V6ÜÚW6VCÚııııııııııııııııııııııı¢“WfVÁB÷ó'&˜"W6VCÚııııııııııııııııııııııııııı¢“6ˆ◊∆WFR&BG&6RW6VCÚııııııııııııııııııııı¢“Áí&W7V«BF∂V‚g&ˆ“∆Vv7í6ˆ÷÷VÁCÚ¢§’U5B$R‰Ú¢†¢“Áí6˜''ññÁ6W'FVCÚ¢§’U5B$R‰Ú¢†¢“ÁíF÷óFñÁ6W'FVCÚ¢§’U5B$R‰Ú¢†¢“Áí7W7Fˆ“Üñˆ“ñÁ6W'FVCÚ¢§’U5B$R‰Ú¢†¢“ÁíV&∆ñ2FÜV˜&V“7FFV÷VÁB6ÜÊvVCÚ¢§’U5B$R‰Ú¢†¢“ÁíFÜV˜&V“÷W&V«í&VÊ÷VBFÚÜñFR6÷Rvˆ√Ú¢§’U5B$R‰Ú¢†¢“'Vñ∆B&W7V«C¢ııııııııııııııııııııııııııııııııı¢“ÊWáB7G&ñ7F«í6÷∆∆W"ˆ&∆ñvFñˆ„¢ııııııııııııı†§FÚÊ˜B÷˜fRf˜'v&BVÊ∆W72FÜR7W'&VÁBFÜV˜&V“ó2∂W&ÊV¬66WFVB‡††¢226ÜV6∑ˆñÁBê†§BFÜó26ÜV6∑ˆñÁC††¢“7W'&VÁBFÜV˜&V”¢ııııııııııııııııııııııııııııı¢“7W'&VÁBWÜ7Bvˆ√¢ıııııııııııııııııııııııııı¢“7W'&VÁBáó˜FÜW6W27GV∆«íW6VC¢ııııııııııı¢“WÜó7FñÊr6˜W&6RFÜV˜&V“&WW6VC¢ııııııııııııı¢“ÊWrFÜV˜&V“&WW6VC¢ııııııııııııııııııııııııı¢“w7Dˆ÷VvVÊfˆ∆FVCÚııııııııııııııııııııııııı¢“ñÊfñÊóFR’&F˜ÇVÊW&wíW6VCÚıııııııııııııııı¢“WÜ7B&∆ˆ6≤V6ÜÚW6VCÚııııııııııııııııııııııı¢“WfVÁB÷ó'&˜"W6VCÚııııııııııııııııııııııııııı¢“6ˆ◊∆WFR&BG&6RW6VCÚııııııııııııııııııııı¢“Áí&W7V«BF∂V‚g&ˆ“∆Vv7í6ˆ÷÷VÁCÚ¢§’U5B$R‰Ú¢†¢“Áí6˜''ññÁ6W'FVCÚ¢§’U5B$R‰Ú¢†¢“ÁíF÷óFñÁ6W'FVCÚ¢§’U5B$R‰Ú¢†¢“Áí7W7Fˆ“Üñˆ“ñÁ6W'FVCÚ¢§’U5B$R‰Ú¢†¢“ÁíV&∆ñ2FÜV˜&V“7FFV÷VÁB6ÜÊvVCÚ¢§’U5B$R‰Ú¢†¢“ÁíFÜV˜&V“÷W&V«í&VÊ÷VBFÚÜñFR6÷Rvˆ√Ú¢§’U5B$R‰Ú¢†¢“'Vñ∆B&W7V«C¢ııııııııııııııııııııııııııııııııı¢“ÊWáB7G&ñ7F«í6÷∆∆W"ˆ&∆ñvFñˆ„¢ııııııııııııı†§FÚÊ˜B÷˜fRf˜'v&BVÊ∆W72FÜR7W'&VÁBFÜV˜&V“ó2∂W&ÊV¬66WFVB‡††¢226ÜV6∑ˆñÁB †§BFÜó26ÜV6∑ˆñÁC††¢“7W'&VÁBFÜV˜&V”¢ııııııııııııııııııııııııııııı¢“7W'&VÁBWÜ7Bvˆ√¢ıııııııııııııııııııııııııı¢“7W'&VÁBáó˜FÜW6W27GV∆«íW6VC¢ııııııııııı¢“WÜó7FñÊr6˜W&6RFÜV˜&V“&WW6VC¢ııııııııııııı¢“ÊWrFÜV˜&V“&WW6VC¢ııııııııııııııııııııııııı¢“w7Dˆ÷VvVÊfˆ∆FVCÚııııııııııııııııııııııııı¢“ñÊfñÊóFR’&F˜ÇVÊW&wíW6VCÚıııııııııııııııı¢“WÜ7B&∆ˆ6≤V6ÜÚW6VCÚııııııııııııııııııııııı¢“WfVÁB÷ó'&˜"W6VCÚııııııııııııııııııııııııııı¢“6ˆ◊∆WFR&BG&6RW6VCÚııııııııııııııııııııı¢“Áí&W7V«BF∂V‚g&ˆ“∆Vv7í6ˆ÷÷VÁCÚ¢§’U5B$R‰Ú¢†¢“Áí6˜''ññÁ6W'FVCÚ¢§’U5B$R‰Ú¢†¢“ÁíF÷óFñÁ6W'FVCÚ¢§’U5B$R‰Ú¢†¢“Áí7W7Fˆ“Üñˆ“ñÁ6W'FVCÚ¢§’U5B$R‰Ú¢†¢“ÁíV&∆ñ2FÜV˜&V“7FFV÷VÁB6ÜÊvVCÚ¢§’U5B$R‰Ú¢†¢“ÁíFÜV˜&V“÷W&V«í&VÊ÷VBFÚÜñFR6÷Rvˆ√Ú¢§’U5B$R‰Ú¢†¢“'Vñ∆B&W7V«C¢ııııııııııııııııııııııııııııııııı¢“ÊWáB7G&ñ7F«í6÷∆∆W"ˆ&∆ñvFñˆ„¢ııııııııııııı†§FÚÊ˜B÷˜fRf˜'v&BVÊ∆W72FÜR7W'&VÁBFÜV˜&V“ó2∂W&ÊV¬66WFVB‡††¢226ÜV6∑ˆñÁB†§BFÜó26ÜV6∑ˆñÁC††¢“7W'&VÁBFÜV˜&V”¢ııııııııııııııııııııııııııııı¢“7W'&VÁBWÜ7Bvˆ√¢ıııııııııııııııııııııııııı¢“7W'&VÁBáó˜FÜW6W27GV∆«íW6VC¢ııııııııııı¢“WÜó7FñÊr6˜W&6RFÜV˜&V“&WW6VC¢ııııııııııııı¢“ÊWrFÜV˜&V“&WW6VC¢ııııııııııııııııııııııııı¢“w7Dˆ÷VvVÊfˆ∆FVCÚııııııııııııııııııııııııı¢“ñÊfñÊóFR’&F˜ÇVÊW&wíW6VCÚıııııııııııııııı¢“WÜ7B&∆ˆ6≤V6ÜÚW6VCÚııııııııııııııııııııııı¢“WfVÁB÷ó'&˜"W6VCÚııııııııııııııııııııııııııı¢“6ˆ◊∆WFR&BG&6RW6VCÚııııııııııııııııııııı¢“Áí&W7V«BF∂V‚g&ˆ“∆Vv7í6ˆ÷÷VÁCÚ¢§’U5B$R‰Ú¢†¢“Áí6˜''ññÁ6W'FVCÚ¢§’U5B$R‰Ú¢†¢“ÁíF÷óFñÁ6W'FVCÚ¢§’U5B$R‰Ú¢†¢“Áí7W7Fˆ“Üñˆ“ñÁ6W'FVCÚ¢§’U5B$R‰Ú¢†¢“ÁíV&∆ñ2FÜV˜&V“7FFV÷VÁB6ÜÊvVCÚ¢§’U5B$R‰Ú¢†¢“ÁíFÜV˜&V“÷W&V«í&VÊ÷VBFÚÜñFR6÷Rvˆ√Ú¢§’U5B$R‰Ú¢†¢“'Vñ∆B&W7V«C¢ııııııııııııııııııııııııııııııııı¢“ÊWáB7G&ñ7F«í6÷∆∆W"ˆ&∆ñvFñˆ„¢ııııııııııııı†§FÚÊ˜B÷˜fRf˜'v&BVÊ∆W72FÜR7W'&VÁBFÜV˜&V“ó2∂W&ÊV¬66WFVB‡††¢226ÜV6∑ˆñÁB †§BFÜó26ÜV6∑ˆñÁC††¢“7W'&VÁBFÜV˜&V”¢ııııııııııııııııııııııııııııı¢“7W'&VÁBWÜ7Bvˆ√¢ıııııııııııııııııııııııııı¢“7W'&VÁBáó˜FÜW6W27GV∆«íW6VC¢ııııııııııı¢“WÜó7FñÊr6˜W&6RFÜV˜&V“&WW6VC¢ııııııııııııı¢“ÊWrFÜV˜&V“&WW6VC¢ııııııııııııııııııııııııı¢“w7Dˆ÷VvVÊfˆ∆FVCÚııııııııııııııııııııııııı¢“ñÊfñÊóFR’&F˜ÇVÊW&wíW6VCÚıııııııııııııııı¢“WÜ7B&∆ˆ6≤V6ÜÚW6VCÚııııııııııııııııııııııı¢“WfVÁB÷ó'&˜"W6VCÚııııııııııııııııııııııııııı¢“6ˆ◊∆WFR&BG&6RW6VCÚııııııııııııııııııııı¢“Áí&W7V«BF∂V‚g&ˆ“∆Vv7í6ˆ÷÷VÁCÚ¢§’U5B$R‰Ú¢†¢“Áí6˜''ññÁ6W'FVCÚ¢§’U5B$R‰Ú¢†¢“ÁíF÷óFñÁ6W'FVCÚ¢§’U5B$R‰Ú¢†¢“Áí7W7Fˆ“Üñˆ“ñÁ6W'FVCÚ¢§’U5B$R‰Ú¢†¢“ÁíV&∆ñ2FÜV˜&V“7FFV÷VÁB6ÜÊvVCÚ¢§’U5B$R‰Ú¢†¢“ÁíFÜV˜&V“÷W&V«í&VÊ÷VBFÚÜñFR6÷Rvˆ√Ú¢§’U5B$R‰Ú¢†¢“'Vñ∆B&W7V«C¢ııııııııııııııııııııııııııııııııı¢“ÊWáB7G&ñ7F«í6÷∆∆W"ˆ&∆ñvFñˆ„¢ııııııııııııı†§FÚÊ˜B÷˜fRf˜'v&BVÊ∆W72FÜR7W'&VÁBFÜV˜&V“ó2∂W&ÊV¬66WFVB‡††¢226ÜV6∑ˆñÁB0†§BFÜó26ÜV6∑ˆñÁC††¢“7W'&VÁBFÜV˜&V”¢ııııııııııııııııııııııııııııı¢“7W'&VÁBWÜ7Bvˆ√¢ıııııııııııııııııııııııııı¢“7W'&VÁBáó˜FÜW6W27GV∆«íW6VC¢ııııııııııı¢“WÜó7FñÊr6˜W&6RFÜV˜&V“&WW6VC¢ııııııııııııı¢“ÊWrFÜV˜&V“&WW6VC¢ııııııııııııııııııııııııı¢“w7Dˆ÷VvVÊfˆ∆FVCÚııııııııııııııııııııııııı¢“ñÊfñÊóFR’&F˜ÇVÊW&wíW6VCÚıııııııııııııııı¢“WÜ7B&∆ˆ6≤V6ÜÚW6VCÚııııııııııııııııııııııı¢“WfVÁB÷ó'&˜"W6VCÚııııııııııııııııııııııııııı¢“6ˆ◊∆WFR&BG&6RW6VCÚııııııııııııııııııııı¢“Áí&W7V«BF∂V‚g&ˆ“∆Vv7í6ˆ÷÷VÁCÚ¢§’U5B$R‰Ú¢†¢“Áí6˜''ññÁ6W'FVCÚ¢§’U5B$R‰Ú¢†¢“ÁíF÷óFñÁ6W'FVCÚ¢§’U5B$R‰Ú¢†¢“Áí7W7Fˆ“Üñˆ“ñÁ6W'FVCÚ¢§’U5B$R‰Ú¢†¢“ÁíV&∆ñ2FÜV˜&V“7FFV÷VÁB6ÜÊvVCÚ¢§’U5B$R‰Ú¢†¢“ÁíFÜV˜&V“÷W&V«í&VÊ÷VBFÚÜñFR6÷Rvˆ√Ú¢§’U5B$R‰Ú¢†¢“'Vñ∆B&W7V«C¢ııııııııııııııııııııııııııııııııı¢“ÊWáB7G&ñ7F«í6÷∆∆W"ˆ&∆ñvFñˆ„¢ııııııııııııı†§FÚÊ˜B÷˜fRf˜'v&BVÊ∆W72FÜR7W'&VÁBFÜV˜&V“ó2∂W&ÊV¬66WFVB‡††¢226ÜV6∑ˆñÁB@†§BFÜó26ÜV6∑ˆñÁC††¢“7W'&VÁBFÜV˜&V”¢ııııııııııııııııııııııııııııı¢“7W'&VÁBWÜ7Bvˆ√¢ıııııııııııııııııııııııııı¢“7W'&VÁBáó˜FÜW6W27GV∆«íW6VC¢ııııııııııı¢“WÜó7FñÊr6˜W&6RFÜV˜&V“&WW6VC¢ııııııııııııı¢“ÊWrFÜV˜&V“&WW6VC¢ııııııııııııııııııııııııı¢“w7Dˆ÷VvVÊfˆ∆FVCÚııııııııııııııııııııııııı¢“ñÊfñÊóFR’&F˜ÇVÊW&wíW6VCÚıııııııııııııııı¢“WÜ7B&∆ˆ6≤V6ÜÚW6VCÚııııııııııııııııııııııı¢“WfVÁB÷ó'&˜"W6VCÚııııııııııııııııııııııııııı¢“6ˆ◊∆WFR&BG&6RW6VCÚııııııııııııııııııııı¢“Áí&W7V«BF∂V‚g&ˆ“∆Vv7í6ˆ÷÷VÁCÚ¢§’U5B$R‰Ú¢†¢“Áí6˜''ññÁ6W'FVCÚ¢§’U5B$R‰Ú¢†¢“ÁíF÷óFñÁ6W'FVCÚ¢§’U5B$R‰Ú¢†¢“Áí7W7Fˆ“Üñˆ“ñÁ6W'FVCÚ¢§’U5B$R‰Ú¢†¢“ÁíV&∆ñ2FÜV˜&V“7FFV÷VÁB6ÜÊvVCÚ¢§’U5B$R‰Ú¢†¢“ÁíFÜV˜&V“÷W&V«í&VÊ÷VBFÚÜñFR6÷Rvˆ√Ú¢§’U5B$R‰Ú¢†¢“'Vñ∆B&W7V«C¢ııııııııııııııııııııııııııııııııı¢“ÊWáB7G&ñ7F«í6÷∆∆W"ˆ&∆ñvFñˆ„¢ııııııııııııı†§FÚÊ˜B÷˜fRf˜'v&BVÊ∆W72FÜR7W'&VÁBFÜV˜&V“ó2∂W&ÊV¬66WFVB‡††¢226ÜV6∑ˆñÁBP†§BFÜó26ÜV6∑ˆñÁC††¢“7W'&VÁBFÜV˜&V”¢ııııııııııııııııııııııııııııı¢“7W'&VÁBWÜ7Bvˆ√¢ıııııııııııııııııııııııııı¢“7W'&VÁBáó˜FÜW6W27GV∆«íW6VC¢ııııııııııı¢“WÜó7FñÊr6˜W&6RFÜV˜&V“&WW6VC¢ııııııııııııı¢“ÊWrFÜV˜&V“&WW6VC¢ııııııııııııııııııııııııı¢“w7Dˆ÷VvVÊfˆ∆FVCÚııııııııııııııııııııııııı¢“ñÊfñÊóFR’&F˜ÇVÊW&wíW6VCÚıııııııııııııııı¢“WÜ7B&∆ˆ6≤V6ÜÚW6VCÚııııııııııııııııııııııı¢“WfVÁB÷ó'&˜"W6VCÚııııııııııııııııııııııııııı¢“6ˆ◊∆WFR&BG&6RW6VCÚııııııııııııııııııııı¢“Áí&W7V«BF∂V‚g&ˆ“∆Vv7í6ˆ÷÷VÁCÚ¢§’U5B$R‰Ú¢†¢“Áí6˜''ññÁ6W'FVCÚ¢§’U5B$R‰Ú¢†¢“ÁíF÷óFñÁ6W'FVCÚ¢§’U5B$R‰Ú¢†¢“Áí7W7Fˆ“Üñˆ“ñÁ6W'FVCÚ¢§’U5B$R‰Ú¢†¢“ÁíV&∆ñ2FÜV˜&V“7FFV÷VÁB6ÜÊvVCÚ¢§’U5B$R‰Ú¢†¢“ÁíFÜV˜&V“÷W&V«í&VÊ÷VBFÚÜñFR6÷Rvˆ√Ú¢§’U5B$R‰Ú¢†¢“'Vñ∆B&W7V«C¢ııııııııııııııııııııııııııııııııı¢“ÊWáB7G&ñ7F«í6÷∆∆W"ˆ&∆ñvFñˆ„¢ııııııııııııı†§FÚÊ˜B÷˜fRf˜'v&BVÊ∆W72FÜR7W'&VÁBFÜV˜&V“ó2∂W&ÊV¬66WFVB‡††¢226ÜV6∑ˆñÁB`†§BFÜó26ÜV6∑ˆñÁC††¢“7W'&VÁBFÜV˜&V”¢ııııııııııııııııııııııııııııı¢“7W'&VÁBWÜ7Bvˆ√¢ıııııııııııııııııııııııııı¢“7W'&VÁBáó˜FÜW6W27GV∆«íW6VC¢ııııııııııı¢“WÜó7FñÊr6˜W&6RFÜV˜&V“&WW6VC¢ııııııııııııı¢“ÊWrFÜV˜&V“&WW6VC¢ııııııııııııııııııııııııı¢“w7Dˆ÷VvVÊfˆ∆FVCÚııııııııııııııııııııııııı¢“ñÊfñÊóFR’&F˜ÇVÊW&wíW6VCÚıııııııııııııııı¢“WÜ7B&∆ˆ6≤V6ÜÚW6VCÚııııııııııııııııııııııı¢“WfVÁB÷ó'&˜"W6VCÚııııııııııııııııııııııııııı¢“6ˆ◊∆WFR&BG&6RW6VCÚııııııııııııııııııııı¢“Áí&W7V«BF∂V‚g&ˆ“∆Vv7í6ˆ÷÷VÁCÚ¢§’U5B$R‰Ú¢†¢“Áí6˜''ññÁ6W'FVCÚ¢§’U5B$R‰Ú¢†¢“ÁíF÷óFñÁ6W'FVCÚ¢§’U5B$R‰Ú¢†¢“Áí7W7Fˆ“Üñˆ“ñÁ6W'FVCÚ¢§’U5B$R‰Ú¢†¢“ÁíV&∆ñ2FÜV˜&V“7FFV÷VÁB6ÜÊvVCÚ¢§’U5B$R‰Ú¢†¢“ÁíFÜV˜&V“÷W&V«í&VÊ÷VBFÚÜñFR6÷Rvˆ√Ú¢§’U5B$R‰Ú¢†¢“'Vñ∆B&W7V«C¢ııııııııııııııııııııııııııııııııı¢“ÊWáB7G&ñ7F«í6÷∆∆W"ˆ&∆ñvFñˆ„¢ııııııııııııı†§FÚÊ˜B÷˜fRf˜'v&BVÊ∆W72FÜR7W'&VÁBFÜV˜&V“ó2∂W&ÊV¬66WFVB‡††¢226ÜV6∑ˆñÁBp†§BFÜó26ÜV6∑ˆñÁC††¢“7W'&VÁBFÜV˜&V”¢ııııııııııııııııııııııııııııı¢“7W'&VÁBWÜ7Bvˆ√¢ıııııııııııııııııııııııııı¢“7W'&VÁBáó˜FÜW6W27GV∆«íW6VC¢ııııııııııı¢“WÜó7FñÊr6˜W&6RFÜV˜&V“&WW6VC¢ııııııııııııı¢“ÊWrFÜV˜&V“&WW6VC¢ııııııııııııııııııııııııı¢“w7Dˆ÷VvVÊfˆ∆FVCÚııııııııııııııııııııııııı¢“ñÊfñÊóFR’&F˜ÇVÊW&wíW6VCÚıııııııııııııııı¢“WÜ7B&∆ˆ6≤V6ÜÚW6VCÚııııııııııııııııııııııı¢“WfVÁB÷ó'&˜"W6VCÚııııııııııııııııııııııııııı¢“6ˆ◊∆WFR&BG&6RW6VCÚııııııııııııııııııııı¢“Áí&W7V«BF∂V‚g&ˆ“∆Vv7í6ˆ÷÷VÁCÚ¢§’U5B$R‰Ú¢†¢“Áí6˜''ññÁ6W'FVCÚ¢§’U5B$R‰Ú¢†¢“ÁíF÷óFñÁ6W'FVCÚ¢§’U5B$R‰Ú¢†¢“Áí7W7Fˆ“Üñˆ“ñÁ6W'FVCÚ¢§’U5B$R‰Ú¢†¢“ÁíV&∆ñ2FÜV˜&V“7FFV÷VÁB6ÜÊvVCÚ¢§’U5B$R‰Ú¢†¢“ÁíFÜV˜&V“÷W&V«í&VÊ÷VBFÚÜñFR6÷Rvˆ√Ú¢§’U5B$R‰Ú¢†¢“'Vñ∆B&W7V«C¢ııııııııııııııııııııııııııııııııı¢“ÊWáB7G&ñ7F«í6÷∆∆W"ˆ&∆ñvFñˆ„¢ııııııııııııı†§FÚÊ˜B÷˜fRf˜'v&BVÊ∆W72FÜR7W'&VÁBFÜV˜&V“ó2∂W&ÊV¬66WFVB‡††¢226ÜV6∑ˆñÁBÄ†§BFÜó26ÜV6∑ˆñÁC††¢“7W'&VÁBFÜV˜&V”¢ııııııııııııııııııııııııııııı¢“7W'&VÁBWÜ7Bvˆ√¢ıııııııııııııııııııııııııı¢“7W'&VÁBáó˜FÜW6W27GV∆«íW6VC¢ııııııııııı¢“WÜó7FñÊr6˜W&6RFÜV˜&V“&WW6VC¢ııııııııııııı¢“ÊWrFÜV˜&V“&WW6VC¢ııııııııııııııııııııııııı¢“w7Dˆ÷VvVÊfˆ∆FVCÚııııııııııııııııııııııııı¢“ñÊfñÊóFR’&F˜ÇVÊW&wíW6VCÚıııııııııııııııı¢“WÜ7B&∆ˆ6≤V6ÜÚW6VCÚııııııııııııııııııııııı¢“WfVÁB÷ó'&˜"W6VCÚııııııııııııııııııııııııııı¢“6ˆ◊∆WFR&BG&6RW6VCÚııııııııııııııııııııı¢“Áí&W7V«BF∂V‚g&ˆ“∆Vv7í6ˆ÷÷VÁCÚ¢§’U5B$R‰Ú¢†¢“Áí6˜''ññÁ6W'FVCÚ¢§’U5B$R‰Ú¢†¢“ÁíF÷óFñÁ6W'FVCÚ¢§’U5B$R‰Ú¢†¢“Áí7W7Fˆ“Üñˆ“ñÁ6W'FVCÚ¢§’U5B$R‰Ú¢†¢“ÁíV&∆ñ2FÜV˜&V“7FFV÷VÁB6ÜÊvVCÚ¢§’U5B$R‰Ú¢†¢“ÁíFÜV˜&V“÷W&V«í&VÊ÷VBFÚÜñFR6÷Rvˆ√Ú¢§’U5B$R‰Ú¢†¢“'Vñ∆B&W7V«C¢ııııııııııııııııııııııııııııııııı¢“ÊWáB7G&ñ7F«í6÷∆∆W"ˆ&∆ñvFñˆ„¢ııııııııııııı†§FÚÊ˜B÷˜fRf˜'v&BVÊ∆W72FÜR7W'&VÁBFÜV˜&V“ó2∂W&ÊV¬66WFVB‡††¢226ÜV6∑ˆñÁBê†§BFÜó26ÜV6∑ˆñÁC††¢“7W'&VÁBFÜV˜&V”¢ııııııııııııııııııııııııııııı¢“7W'&VÁBWÜ7Bvˆ√¢ıııııııııııııııııııııııııı¢“7W'&VÁBáó˜FÜW6W27GV∆«íW6VC¢ııııııııııı¢“WÜó7FñÊr6˜W&6RFÜV˜&V“&WW6VC¢ııııııııııııı¢“ÊWrFÜV˜&V“&WW6VC¢ııııııııııııııııııııııııı¢“w7Dˆ÷VvVÊfˆ∆FVCÚııııııııııııııııııııııııı¢“ñÊfñÊóFR’&F˜ÇVÊW&wíW6VCÚıııııııııııııııı¢“WÜ7B&∆ˆ6≤V6ÜÚW6VCÚııııııııııııııııııııııı¢“WfVÁB÷ó'&˜"W6VCÚııııııııııııııııııııııııııı¢“6ˆ◊∆WFR&BG&6RW6VCÚııııııııııııııııııııı¢“Áí&W7V«BF∂V‚g&ˆ“∆Vv7í6ˆ÷÷VÁCÚ¢§’U5B$R‰Ú¢†¢“Áí6˜''ññÁ6W'FVCÚ¢§’U5B$R‰Ú¢†¢“ÁíF÷óFñÁ6W'FVCÚ¢§’U5B$R‰Ú¢†¢“Áí7W7Fˆ“Üñˆ“ñÁ6W'FVCÚ¢§’U5B$R‰Ú¢†¢“ÁíV&∆ñ2FÜV˜&V“7FFV÷VÁB6ÜÊvVCÚ¢§’U5B$R‰Ú¢†¢“ÁíFÜV˜&V“÷W&V«í&VÊ÷VBFÚÜñFR6÷Rvˆ√Ú¢§’U5B$R‰Ú¢†¢“'Vñ∆B&W7V«C¢ııııııııııııııııııııııııııııııııı¢“ÊWáB7G&ñ7F«í6÷∆∆W"ˆ&∆ñvFñˆ„¢ııııııııııııı†§FÚÊ˜B÷˜fRf˜'v&BVÊ∆W72FÜR7W'&VÁBFÜV˜&V“ó2∂W&ÊV¬66WFVB‡††¢226ÜV6∑ˆñÁB# †§BFÜó26ÜV6∑ˆñÁC††¢“7W'&VÁBFÜV˜&V”¢ııııııııııııııııııııııııııııı¢“7W'&VÁBWÜ7Bvˆ√¢ıııııııııııııııııııııııııı¢“7W'&VÁBáó˜FÜW6W27GV∆«íW6VC¢ııııııııııı¢“WÜó7FñÊr6˜W&6RFÜV˜&V“&WW6VC¢ııııııııııııı¢“ÊWrFÜV˜&V“&WW6VC¢ııııııııııııııııııııııııı¢“w7Dˆ÷VvVÊfˆ∆FVCÚııııııııııııııııııııııııı¢“ñÊfñÊóFR’&F˜ÇVÊW&wíW6VCÚıııııııııııııııı¢“WÜ7B&∆ˆ6≤V6ÜÚW6VCÚııııııııııııııııııııııı¢“WfVÁB÷ó'&˜"W6VCÚııııııııııııııııııııııııııı¢“6ˆ◊∆WFR&BG&6RW6VCÚııııııııııııııııııııı¢“Áí&W7V«BF∂V‚g&ˆ“∆Vv7í6ˆ÷÷VÁCÚ¢§’U5B$R‰Ú¢†¢“Áí6˜''ññÁ6W'FVCÚ¢§’U5B$R‰Ú¢†¢“ÁíF÷óFñÁ6W'FVCÚ¢§’U5B$R‰Ú¢†¢“Áí7W7Fˆ“Üñˆ“ñÁ6W'FVCÚ¢§’U5B$R‰Ú¢†¢“ÁíV&∆ñ2FÜV˜&V“7FFV÷VÁB6ÜÊvVCÚ¢§’U5B$R‰Ú¢†¢“ÁíFÜV˜&V“÷W&V«í&VÊ÷VBFÚÜñFR6÷Rvˆ√Ú¢§’U5B$R‰Ú¢†¢“'Vñ∆B&W7V«C¢ııııııııııııııııııııııııııııııııı¢“ÊWáB7G&ñ7F«í6÷∆∆W"ˆ&∆ñvFñˆ„¢ııııııııııııı†§FÚÊ˜B÷˜fRf˜'v&BVÊ∆W72FÜR7W'&VÁBFÜV˜&V“ó2∂W&ÊV¬66WFVB‡