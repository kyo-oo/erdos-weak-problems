<!-- ======================================================================
<!-- CHRONOLOGICAL LABEL -- #0034 / 1132
<!--    Path         : docs/ERDOSTERNARY2_ATOMIC_OMEGA_PARADOX_MIRROR_SURGERY_PLAN.md
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

# ERDOSTERNARY2 â€” ATOMIC Î©âˆž PARADOXâ€“MIRROR SURGERY PLAN
## Source-accurate handoff for `ErdosTernary2.lean` + `GSTTactic.lean`

**Date:** 2026-08-13  
**Input files inspected directly:**  
- `ErdosTernary2.lean`
- `GSTTactic.lean`

**This document does not modify either Lean file.**

---

# 0. Exact source audit

## File sizes

The uploaded files currently contain:

```text
ErdosTernary2.lean : 7891 lines
GSTTactic.lean      :  201 lines
TOTAL               : 8092 lines
```

The header at the top of `ErdosTernary2.lean` is stale:

```lean
-- 10001 lines, 0 sorry, 0 native_decide
```

The actual uploaded file is 7891 lines and contains exactly one active `sorry`.

Do not edit that header until the proof is green.

---

# 1. Exact current proof hole

The only active `sorry` detected is:

```text
ErdosTernary2.lean:7786
```

It occurs inside:

```lean
theorem gst_prefix_one_navigation_lift :
    GSTPrefixOneNavigationLift := by
  ...
  sorry
```

Current source region:

```lean
7756 -- The ONE mathematical theorem.
...
7765 theorem gst_prefix_one_navigation_lift :
7766     GSTPrefixOneNavigationLift := by
...
7784   by_contra hnotBadChild
7785   obtain âŸ¨j, hjâŸ© := (Classical.not_forall.mp hnotBadChild)
7786   sorry
```

This theorem is the only source-level proof hole that must be replaced.

---

# 2. Exact downstream dependency from the hole

The active dependency chain is:

```text
gst_prefix_one_navigation_lift
        â”‚
        â–¼
gst_navigation_witness_four_pow_div_three_of_prefix_one
        â”‚
        â–¼
gst_power_two_wave_large
        â”‚
        â–¼
erdos_ternary_2_even_universal
        â”‚
        â–¼
erdos_ternary_2_universal
```

More precisely:

## `gst_prefix_one_navigation_lift`

Current definition starts at approximately source line 7765.

Its public type is:

```lean
GSTPrefixOneNavigationLift
```

where:

```lean
def GSTPrefixOneNavigationLift : Prop :=
  âˆ€ s n, 1 â‰¤ s â†’ 1 â‰¤ n â†’
    GSTNavigationWitness (gstNavigationConstant (s + 1) n) â†’
    GSTNavigationWitness (gstNavigationConstant s (1 + 3 * n))
```

## Consumer 1

```lean
theorem gst_navigation_witness_four_pow_div_three_of_prefix_one
    (hp1 : GSTPrefixOneNavigationLift)
    ...
```

At the active final call:

```lean
gst_navigation_witness_four_pow_div_three_of_prefix_one
  gst_prefix_one_navigation_lift ...
```

## Consumer 2

```lean
theorem gst_power_two_wave_large
    (a : Nat) (ha : 500 < a) :
    GSTPowerTwoWave a := by
```

It uses `gst_prefix_one_navigation_lift` in exactly two branches:

```lean
a % 3 = 0
```

and

```lean
a % 3 = 1
```

The `a % 3 = 2` branch is already closed by:

```lean
even_case_a_mod3_2
```

## Final chain

```lean
gst_power_two_wave_large
  â†’ erdos_ternary_2_even_universal
  â†’ erdos_ternary_2_universal
```

Therefore:

> **Do not rewrite `gst_power_two_wave_large`.**
>
> Close `gst_prefix_one_navigation_lift` and preserve the existing downstream chain.

This has the smallest possible blast radius.

---

# 3. Important source fact: the old Î© termination proofs are NOT active

At line ~7300 the source opens a block comment:

```lean
/-
  Legacy residual overproof.
```

That quarantined block contains:

```lean
gst_omega_termination_s1
gst_omega_termination_s3
gst_omega_termination_stable
gst_residual_omega_termination
gst_residual_navigation_lift
...
```

The block closes at approximately line 7537.

Therefore those termination theorems are **proof archaeology**, not active code.

This matters because they must not be treated as dependencies available to the new proof.

---

# 4. Important source fact: `gst_omega` tactic is not on the active final path

`GSTTactic.lean` defines:

```lean
elab "gst_omega" : tactic => ...
```

Its intended purpose is well-founded decreasing goals involving subtraction.

In the uploaded `ErdosTernary2.lean`, the literal tactic invocation:

```lean
gst_omega
```

occurs only three times:

```text
7329
7352
7376
```

All three occurrences are inside the quarantined legacy comment.

Therefore:

```text
GSTTactic.lean DOES NOT need to be rewritten
to implement the new Î©âˆž proof.
```

Keep the tactic file unchanged initially.

The existing utility tactics remain useful:

```lean
gst_carry_cases
gst_digit_cases
gst_carry_eq_cases
gst_origin_residue_cases
```

especially for finite local event proofs.

---

# 5. The active Î©âˆž infrastructure already present

This is the strongest reason not to create a second framework.

The canonical file already contains a nine-coordinate Î© state.

## Existing `GSTOmegaState`

At approximately line 6803:

```lean
structure GSTOmegaState where
  paradoxEnergy : Nat
  descent : Nat
  childCarry : Nat
  childDigit : Nat
  affineCarry : Nat
  parentCarry : Nat
  parentDigit : Nat
  bridgeResidue : Nat
  cascadeDepth : Nat
  deriving Repr, DecidableEq
```

Do not replace this structure.

It already contains exactly the coordinates needed by the new proof.

---

# 6. Existing Î©âˆž transition

At approximately line 6816:

```lean
def gstOmegaStep (A : Nat) (w : GSTOmegaState) : GSTOmegaState where
  paradoxEnergy := w.paradoxEnergy
  descent := w.descent / 3
  childCarry := (w.childCarry + 4*w.childDigit) / 3
  childDigit := (w.descent / 3) % 3
  affineCarry := (w.affineCarry + A*w.childDigit) / 3
  parentCarry := (w.parentCarry + 4*w.parentDigit) / 3
  parentDigit :=
    (((w.affineCarry + A*w.childDigit) / 3)
      + A*((w.descent / 3) % 3)) % 3
  bridgeResidue := w.bridgeResidue
  cascadeDepth := w.cascadeDepth
```

This is already the coupled infinite-space transition.

Do not create another `OmegaStep`.

---

# 7. Existing canonical Î© orbit

At approximately line 6829:

```lean
def gstOmega (s k m j : Nat) : GSTOmegaState :=
  let T := gstNavigationConstant (s+k) m
  let A := 4^(3^s)
  let z := c s / 3^k
  let delta := (4 * (c s % 3^k)) / 3^k
  let X := z + A*T
  {
    paradoxEnergy := gstInfiniteParadoxEnergy (s+k) T j
    descent := T / 3^j
    childCarry := gstCarry T j
    childDigit := gstDigit T j
    affineCarry := gstAffineMulCarry A z T j
    parentCarry := gstAffineMulCarry 4 delta X j
    parentDigit := gstDigit X j
    bridgeResidue := c s % 3^k
    cascadeDepth := k
  }
```

This is extremely important.

For the missing prefix-one theorem set:

```text
k = 1
m = n
```

Then:

```text
child = gstNavigationConstant (s+1) n
parent = gstNavigationConstant s (1+3*n)
```

This is exactly the missing theorem's parent/child pair.

Therefore:

> The missing theorem does not need a new seed-one state.
> `gstOmega s 1 n` already is the correct infinite coupled state.

---

# 8. Existing Î© exact evolution theorem

At approximately line 6849:

```lean
theorem gst_omega_universal_equation (s k m j : Nat) :
    gstOmega s k m (j+1) =
      gstOmegaStep (4^(3^s)) (gstOmega s k m j) := by
  ...
```

Reuse this theorem.

It is the exact Î©âˆž recurrence.

The new proof should never unfold the entire `gstOmega` state at every graph position manually.

---

# 9. Existing Infinite-Paradox energy is already formal

At approximately lines 6786â€“6800:

```lean
def gstInfiniteParadoxEnergy (t T j : Nat) : Nat :=
  1 + 3^(t+1+j) * (T / 3^j)
    + 3^(t+1) * (T % 3^j)
```

with:

```lean
theorem gst_infinite_paradox_energy_conservation
    (t T j : Nat) :
    gstInfiniteParadoxEnergy t T j
      =
    1 + 3^(t+1) * T := by
  ...
```

and Î© projection:

```lean
theorem gst_omega_paradoxEnergy_succ (s k m j : Nat) :
    (gstOmega s k m (j+1)).paradoxEnergy
      =
    (gstOmega s k m j).paradoxEnergy := by
  ...
```

This is the source-native place to attach the new paradox/mirror theorem.

---

# 10. Existing parent projection

At approximately line 6884:

```lean
theorem gst_omega_parent_projection
    (s k m j : Nat) (hs : 1 â‰¤ s) :
    gstDigit
      (gstNavigationConstant s (1+3^k*m))
      (k+j)
      =
      (gstOmega s k m j).parentDigit
    âˆ§
    gstCarry
      (gstNavigationConstant s (1+3^k*m))
      (k+j)
      =
      (gstOmega s k m j).parentCarry := by
  ...
```

This theorem is crucial.

It means any Î© Happy Gate can already be transported to the actual parent Navigation Constant.

Do not reproach the parent through `GSTSeedOneAffineWitness`.

---

# 11. Existing Happy-Gate polynomial

At approximately line 6898:

```lean
def GSTOmegaGatePolynomial (w : GSTOmegaState) : Int :=
  ((w.parentDigit : Int) - 2)^2 +
  ((w.parentCarry : Int)
    * ((w.parentCarry : Int) - 3))^2
```

Kernel theorem:

```lean
theorem gst_omega_gate_polynomial_zero_iff
    (w : GSTOmegaState) :
    GSTOmegaGatePolynomial w = 0
      â†”
    w.parentDigit = 2
      âˆ§
    (w.parentCarry = 0
      âˆ¨ w.parentCarry = 3) := by
  ...
```

This is already the exact Happy Gate.

The new mirror/event layer should connect to this theorem, not replace it.

---

# 12. Existing theorem that closes the parent

At approximately line 6932:

```lean
theorem gst_omega_gate_zero_closes_parent
    (s k m : Nat) (hs : 1 â‰¤ s)
    (hzero :
      âˆƒ j,
        GSTOmegaGatePolynomial
          (gstOmega s k m j) = 0) :
    GSTNavigationWitness
      (gstNavigationConstant s (1+3^k*m)) := by
  ...
```

This theorem is the key surgical endpoint.

For the missing prefix-one theorem:

```lean
k := 1
m := n
```

Therefore once the new mathematics proves:

```lean
âˆƒ j,
  GSTOmegaGatePolynomial
    (gstOmega s 1 n j) = 0
```

the target follows immediately:

```lean
gst_omega_gate_zero_closes_parent
  s 1 n hs ...
```

No additional Navigation transport theorem is required.

---

# 13. Existing zero/bad spaces

Already active:

```lean
def GSTOmegaZeroSet (s k m : Nat) : Set Nat :=
  {j |
    GSTOmegaGatePolynomial
      (gstOmega s k m j) = 0}

def GSTOmegaBadSet (s k m : Nat) : Set Nat :=
  {j |
    GSTOmegaGatePolynomial
      (gstOmega s k m j) â‰  0}
```

And:

```lean
def GSTOmegaInfiniteBadTrace
    (s k m : Nat) : Prop :=
  âˆ€ j : Nat,
    j âˆˆ GSTOmegaBadSet s k m
```

Already proven:

```lean
theorem gst_omega_noInfiniteBadTrace_iff_zeroSet_nonempty
    (s k m : Nat) :
    Â¬ GSTOmegaInfiniteBadTrace s k m
      â†”
    (GSTOmegaZeroSet s k m).Nonempty := by
  ...
```

This theorem is exactly the bridge needed after the new paradox/mirror exclusion.

---

# 14. Existing child Navigation projection

Already active:

```lean
def GSTOmegaChildZeroSet (s k m : Nat) : Set Nat :=
  {j |
    (gstOmega s k m j).childDigit = 2
      âˆ§
    ((gstOmega s k m j).childCarry = 0
      âˆ¨
     (gstOmega s k m j).childCarry = 3)}
```

and:

```lean
theorem gst_omega_childZeroSet_nonempty_of_navigation_witness
    (s k m : Nat)
    (hchild :
      GSTNavigationWitness
        (gstNavigationConstant (s+k) m)) :
    (GSTOmegaChildZeroSet s k m).Nonempty := by
  ...
```

For the missing theorem:

```text
s+k = s+1
m = n
```

so the hypothesis of `GSTPrefixOneNavigationLift` already gives:

```lean
(GSTOmegaChildZeroSet s 1 n).Nonempty
```

This should be used as the **active-wave anchor** in the paradox/mirror theorem.

---

# 15. Existing affine/block-echo theorem

Already active:

```lean
theorem gst_omega_affine_tail_block_echo
    (s k m : Nat) (hs : 1 â‰¤ s) :
    c s / 3^k
      + 4^(3^s) * gstNavigationConstant (s+k) m
    =
    c s / 3^k
      + gstNavigationConstant (s+k) m
      + 3^(s+1) * c s
        * gstNavigationConstant (s+k) m := by
  ...
```

This is the exact "creation of the new shifted echo while the child survives"
equation.

Use it in the mathematical proof of mirror recurrence.

Do not use the experimental HTML creation/destruction ratio.

---

# 16. Current prefix-one helper layer is now optional

The source currently defines:

```lean
GSTSeedOneAffineWitness
GSTPrefixOneBadReflection
GSTPrefixOneSeedCore

gst_prefix_one_seed_core_of_bad_reflection
gst_prefix_one_navigation_lift_of_seed_core
gst_prefix_one_navigation_lift_of_bad_reflection
```

These are all active, but the final proof only consumes:

```lean
gst_prefix_one_navigation_lift
```

Therefore after the new Î©âˆž proof is installed:

```text
GSTPrefixOneBadReflection
GSTPrefixOneSeedCore
their adapter theorems
```

can remain in the file but will no longer be on the active dependency path.

Do not delete them before the universal theorem is green.

---

# 17. Surgical strategy: add ONE new Î©âˆž theorem family

The new mathematics should be inserted into the active Î© section.

## Recommended insertion anchor

Insert the new event/mirror/closure block:

```text
AFTER:
gst_omega_seededAffine_block_echo

BEFORE:
the line that opens
/- Legacy residual overproof.
```

In the uploaded file this is currently between approximately:

```text
7299
and
7300
```

After insertion all later line numbers will move, so use theorem names as anchors.

---

# 18. New event datatype

Add:

```lean
inductive GSTOmegaEvent
  | create
  | destroy
  | survive
  | neither
  deriving DecidableEq, Repr
```

Keep it distinct from `GSTSpace`.

`GSTSpace` classifies carry space.

`GSTOmegaEvent` classifies one wave interaction.

---

# 19. Output digit of one Î© parent edge

Define:

```lean
def gstOmegaParentOutputDigit
    (w : GSTOmegaState) : Nat :=
  gstOutputDigit w.parentCarry w.parentDigit
```

This uses the already-active core definition:

```lean
def gstOutputDigit (C d : Nat) : Nat :=
  (C + 4*d) % 3
```

Do not compute the output by constructing a second parent natural number.

---

# 20. Event classifier

```lean
def gstOmegaEventOfState
    (w : GSTOmegaState) : GSTOmegaEvent :=
  let d := w.parentDigit
  let e := gstOmegaParentOutputDigit w

  if d = 2 then
    if e = 2 then .survive
    else .destroy
  else
    if e = 2 then .create
    else .neither
```

Orbit projection:

```lean
def gstOmegaEvent
    (s k m j : Nat) : GSTOmegaEvent :=
  gstOmegaEventOfState (gstOmega s k m j)
```

---

# 21. First finite event lemmas

Prove these before touching the global theorem.

```lean
theorem gst_omega_event_survive_iff_raw
    (w : GSTOmegaState) :
    gstOmegaEventOfState w = .survive
      â†”
    w.parentDigit = 2
      âˆ§
    gstOmegaParentOutputDigit w = 2 := by
  unfold gstOmegaEventOfState
  by_cases hd : w.parentDigit = 2
  Â· simp [hd]
  Â· simp [hd]
```

Similarly optional:

```lean
gst_omega_event_create_iff_raw
gst_omega_event_destroy_iff_raw
gst_omega_event_neither_iff_raw
```

These are definitional and should be closed with `simp`.

---

# 22. Prove canonical Î© parent carry bound

The raw `GSTOmegaState` type does not constrain `parentCarry`.

Therefore do NOT prove:

```lean
survive â†” gate
```

for an arbitrary `GSTOmegaState`.

Prove it only for the canonical state:

```lean
theorem gst_omega_parentCarry_lt_four
    (s k m j : Nat)
    (hs : 1 â‰¤ s)
    (hk : 1 â‰¤ k) :
    (gstOmega s k m j).parentCarry < 4 := by
```

Recommended proof:

1. use:

```lean
gst_omega_parent_projection s k m j hs
```

2. rewrite parent carry back to:

```lean
gstCarry
  (gstNavigationConstant s (1+3^k*m))
  (k+j)
```

3. prove:

```lean
1 â‰¤ k+j
```

from `hk`.

4. apply:

```lean
gstCarry_ltç}µ¶‰žËkºwµçJP)Á…É•¹Ñ¥¥Ð€ô€È)…¹Á…É•¹Ñ…ÉÉäƒŠ" ìÀ°Íô)€()á¥ÍÑ¥¹œMPÍÁ…”µ•…¹¥¹Ìè()Ñ•áÐ)Á…É•¹Ñ…ÉÉä€ô€ÀƒŠH9U10)Á…É•¹Ñ…ÉÉä€ô€ÌƒŠHMP¬)Á…É•¹Ñ…ÉÉä€ô€Ä½È€ÈƒŠH1P´)€()Q¡•É•™½É”è()Ñ•áÐ)MUIY%Y(€ƒŠP)!…ÁÁä…Ñ”(€ƒŠP)MQ=µ•……Ñ•A½±å¹½µ¥…°€ô€À¸)€()Q¡¥Ì¥‘•¹Ñ¥ÑäÍ¡½Õ±‰”­•É¹•°µÁÉ½Ù•‰•™½É”Ñ¡”±½‰…°Á…É…‘½àÑ¡•½É•´¸((´´´((Œ€ÐÌ¸9¼¹Õµ•É¥…°É•…Ñ¥½¸½‘•ÍÑÉÕÑ¥½¸É…Ñ¥¼¥¸1•…¸()¼¹½Ð™½Éµ…±¥é”è()Ñ•áÐ)É•…Ñ¥½¸½‘•ÍÑÉÕÑ¥½¸É…Ñ¥¼€ô€Ä)€()½Èè()Ñ•áÐ)É…Ñ¥¼ƒŠ" lÀ¸ä°€È¸Át¸)€()Q¡½Í”¹Õµ‰•ÉÌ…µ”™É½´É…Á •áÁ•É¥µ•¹ÑÌ…¹…É”Õ¹¹••ÍÍ…Éä¸()Q¡”™½Éµ…°ÁÉ½½˜¹••‘Ì½¹±äè()Ñ•áÐ)•Ù•¹ÐÁ…ÉÑ¥Ñ¥½¸)µ¥ÉÉ½È¥¹Ù½±ÕÑ¥½¸)…Ñ¥Ù”µ¥ÉÉ½È™¥á•Í•Ñ½È)MUIY%YƒŠP…Ñ”é•É¼)Á…É…‘½à½µ¥ÉÉ½È±½‰…°É•ÕÉÉ•¹”)€((´´´((Œ€ÐÐ¸MQQ…Ñ¥Œ¹±•…¸ÍÕÉ•ÉäÉ•½µµ•¹‘…Ñ¥½¸((ŒŒ%¹¥Ñ¥…°Á…ÍÌ()5…­”€¨©é•É¼•‘¥ÑÌ¨¨Ñ¼MQQ…Ñ¥Œ¹±•…¹€¸()Q¡”¹•ÜÁÉ½½˜…¸ÕÍ”•á¥ÍÑ¥¹œè()±•…¸)¹…Ñ}±Ñ}™½ÕÉ}…Í•Ì)¹…Ñ}±Ñ}Ñ¡É••}…Í•Ì)ÍÑ}…ÉÉå}…Í•Ì)ÍÑ}‘¥¥Ñ}…Í•Ì)€()9¼¹•ÜÑ…Ñ¥Œ¥Ì¹••ÍÍ…Éä¸((ŒŒ=¹±ä¥˜É•Á•Ñ¥Ñ¥Ù”±½…°•Ù•¹ÐÍÁ±¥ÑÑ¥¹œ‰•½µ•Ì¹½¥Íä()=ÁÑ¥½¹…±±ä…‘±…Ñ•Èè()±•…¸)Íå¹Ñ…à€‰ÍÑ}•Ù•¹Ñ}…Í•Ì€ˆ¥‘•¹Ð€èÑ…Ñ¥Œ)€()	ÕÐ‘¼¹½Ðµ…­”Ñ¡”ÁÉ½½˜‘•Á•¹½¸„¹•Üµ•Ñ…ÁÉ½É…µµ¥¹œÑ…Ñ¥Œ¥˜½É‘¥¹…Éäè()±•…¸)…Í•Ì”)€()½Èè()±•…¸)ÍÑ}…ÉÉå}…Í•Ì)€()¥ÌÍÕ™™¥¥•¹Ð¸()Q¡”µ…Ñ¡•µ…Ñ¥…°Ñ¡•½É•´Í¡½Õ±É•µ…¥¸É•…‘…‰±”Ý¥Ñ¡½ÕÐÑ…Ñ¥Œµ…¥Œ¸((´´´((Œ€ÐÔ¸½µÁ¥±…Ñ¥½¸½É‘•ÈƒŠP•á…Ð()¼¹½ÐÁ…ÍÑ”Ñ¡”•¹Ñ¥É”¹•Ü‰±½¬…¹‘•‰Õœ•Ù•ÉåÑ¡¥¹œÍ¥µÕ±Ñ…¹•½ÕÍ±ä¸()UÍ”Ñ¡¥Ì½É‘•È¸((ŒŒAMLƒŠP•Ù•¹Ð‘•™¥¹¥Ñ¥½¹Ì()‘è()±•…¸)MQ=µ•…Ù•¹Ð)ÍÑ=µ•…A…É•¹Ñ=ÕÑÁÕÑ¥¥Ð)ÍÑ=µ•…Ù•¹Ñ=™MÑ…Ñ”)ÍÑ=µ•…Ù•¹Ð)€()½µÁ¥±”¸((´´´((ŒŒAMLƒŠP™¥¹¥Ñ”•Ù•¹ÐÑ¡•½É•µÌ()‘è()±•…¸)ÍÑ}½µ•…}•Ù•¹Ñ}ÍÕÉÙ¥Ù•}¥™™}É…Ü)MQ=µ•…Ù•¹Ð¹µ¥ÉÉ½È)ÍÑ}½µ•…}•Ù•¹Ñ}µ¥ÉÉ½É}¥¹Ù½±ÕÑ¥Ù”)MQ=µ•…Ù•¹Ð¹Ñ¥Ù”)ÍÑ}½µ•…}…Ñ¥Ù•}µ¥ÉÉ½É}™¥á•‘}¥™™}ÍÕÉÙ¥Ù”)€()½µÁ¥±”¸()Q¡•Í”Í¡½Õ±¡…Ù”¹¼‘•Á•¹‘•¹ä½¸Ñ¡”±½‰…°Ñ¡•½É•´¸((´´´((ŒŒAMLƒŠP…¹½¹¥…°‰½Õ¹‘Ì()‘è()±•…¸)ÍÑ}½µ•…}Á…É•¹Ñ…ÉÉå}±Ñ}™½ÕÈ)ÍÑ}½µ•…}Á…É•¹Ñ¥¥Ñ}±Ñ}Ñ¡É•”)€()½µÁ¥±”¸((´´´((ŒŒAMLƒŠP…Ñ”•ÅÕ¥Ù…±•¹”()‘è()±•…¸)ÍÑ}½µ•…}•Ù•¹Ñ}ÍÕÉÙ¥Ù•}¥™™}…Ñ•}é•É¼)ÍÑ}½µ•…}…Ñ¥Ù•}™¥á•‘}¥™™}…Ñ•}é•É¼)€()½µÁ¥±”¸()ÐÑ¡¥Ì¡•­Á½¥¹ÐÑ¡”¹•Ü•Ù•¹Ð±…å•È¥Ì™Õ±±äÑ¥•Ñ¼•á¥ÍÑ¥¹œMP…É¥Ñ¡µ•Ñ¥Œ¸((´´´((ŒŒAMLƒŠPÁ…É…‘½à½µ¥ÉÉ½ÈÑ¡•½É•´()‘¥¹Ñ•É¹…°±•µµ…Ìè()±•…¸)ÍÑ}½µ•…}…Ñ¥Ù•}¹½¹™¥á•‘}¥Í}É•…Ñ•}½É}‘•ÍÑÉ½ä(¸¸¸)ÍÑ}½µ•…}ÁÉ•™¥á}½¹•}¹½}™É••}µ¥ÉÉ½É}Á…É…‘½à)ÍÑ}½µ•…}ÁÉ•™¥á}½¹•}Á…É…‘½á}µ¥ÉÉ½É}É•ÕÉÉ•¹”)€()½µÁ¥±”•… ½¹”Í•Á…É…Ñ•±ä¸()Q¡¥Ì¥ÌÑ¡”µ…Ñ¡•µ…Ñ¥…°Á…ÍÌ¸((´´´((ŒŒAMLƒŠP…Ñ”•á¥ÍÑ•¹”()‘è()±•…¸)ÍÑ}½µ•…}ÁÉ•™¥á}½¹•}…Ñ•}•á¥ÍÑÌ)€()½µÁ¥±”¸((´´´((ŒŒAMLƒŠPÉ•Á±…”=91dÍÑ}ÁÉ•™¥á}½¹•}¹…Ù¥…Ñ¥½¹}±¥™Ñ€()I•µ½Ù”Ñ¡”½±‰½‘ä½¹Ñ…¥¹¥¹œÑ¡”±¥¹”´ÜÜàØÍ½ÉÉå€¸()%¹Í•ÉÐÑ¡”™½ÕÈ½™¥Ù”µ±¥¹”ƒ:¤ÁÉ½½˜¸()½µÁ¥±”Ñ¡”™¥±”¸((´´´((ŒŒAML ƒŠPÙ•É¥™ä•á¥ÍÑ¥¹œ‘½Ý¹ÍÑÉ•…´()¼¹½Ð•‘¥Ð¥Ðå•Ð¸()½¹™¥É´è()±•…¸)ÍÑ}¹…Ù¥…Ñ¥½¹}Ý¥Ñ¹•ÍÍ}™½ÕÉ}Á½Ý}‘¥Ù}Ñ¡É••}½™}ÁÉ•™¥á}½¹”)ÍÑ}Á½Ý•É}ÑÝ½}Ý…Ù•}±…É”)•É‘½Í}Ñ•É¹…Éå|É}•Ù•¹}Õ¹¥Ù•ÉÍ…°)•É‘½Í}Ñ•É¹…Éå|É}Õ¹¥Ù•ÉÍ…°)€()…±°•±…‰½É…Ñ”¸((´´´((Œ€ÐØ¸9¼µÍ½ÉÉä‘•Ù•±½Áµ•¹Ð‘¥Í¥Á±¥¹”()%˜„¹•ÜÑ¡•½É•´¥Ì¹½Ðå•ÐÁÉ½Ù•°‘¼¹½Ð¥¹Í•ÉÐè()±•…¸)Í½ÉÉä)€()¥¹Ñ¼Ñ¡”µ…¥¸™¥±”¸()%¹ÍÑ•…°Ñ•ÍÐ‘½Ý¹ÍÑÉ•…´Ñ¡•½É•´…É¡¥Ñ•ÑÕÉ”¥¸„ÍÉ…Ñ Ñ¡•½É•´Ý¥Ñ Ñ¡”)¹••‘•É•ÍÕ±Ð…Ì…¸•áÁ±¥¥ÐÁ…É…µ•Ñ•Èè()±•…¸)Ñ¡•½É•´Ñ•ÍÑ}ÁÉ•™¥á}½¹ÍÕµ•È(€€€€¡¡…Ñ”€è(€€€€€ƒŠ" Ì¸°(€€€€€€€€ÄƒŠ&ÌƒŠH(€€€€€€€€ÄƒŠ&¸ƒŠH(€€€€€€€MQ9…Ù¥…Ñ¥½¹]¥Ñ¹•ÍÌ(€€€€€€€€€€¡ÍÑ9…Ù¥…Ñ¥½¹½¹ÍÑ…¹Ð€¡Ì¬Ä¤¸¤ƒŠH(€€€€€€€ƒŠ"¨°(€€€€€€€€€MQ=µ•……Ñ•A½±å¹½µ¥…°(€€€€€€€€€€€€¡ÍÑ=µ•„Ì€Ä¸¨¤€ô€À¤€è(€€€MQAÉ•™¥á=¹•9…Ù¥…Ñ¥½¹1¥™Ð€èô‰ä((€¥¹ÑÉ¼Ì¸¡Ì¡¸¡¡¥±((€•á…Ð(€€€ÍÑ}½µ•…}…Ñ•}é•É½}±½Í•Í}Á…É•¹Ð(€€€€€Ì€Ä¸¡Ì(€€€€€€¡¡…Ñ”Ì¸¡Ì¡¸¡¡¥±¤)€()Q¡¥ÌÙ•É¥™¥•ÌÁ±Õµ‰¥¹œÝ¥Ñ¡½ÕÐ…‘‘¥¹œ…¸Õ¹ÁÉ½Ù•Ñ¡•½É•´¸()=¹”Ñ¡”É•…°…Ñ”Ñ¡•½É•´¥Ì½µÁ±•Ñ”°‘•±•Ñ”Ñ¡”ÍÉ…Ñ Ñ¡•½É•´¥˜)Õ¹¹••ÍÍ…Éä¸((´´´((Œ€ÐÜ¸á…ÐÁÉ½½˜É•Á±…•µ•¹Ð‘¥™˜½¹•ÁÐ()ÕÉÉ•¹Ðè()±•…¸)Ñ¡•½É•´ÍÑ}ÁÉ•™¥á}½¹•}¹…Ù¥…Ñ¥½¹}±¥™Ð€è(€€€MQAÉ•™¥á=¹•9…Ù¥…Ñ¥½¹1¥™Ð€èô‰ä(€…ÁÁ±äÍÑ}ÁÉ•™¥á}½¹•}¹…Ù¥…Ñ¥½¹}±¥™Ñ}½™}‰…‘}É•™±•Ñ¥½¸(€€¸¸¸(€Í½ÉÉä)€()I•Á±…•µ•¹Ðè()±•…¸)Ñ¡•½É•´ÍÑ}ÁÉ•™¥á}½¹•}¹…Ù¥…Ñ¥½¹}±¥™Ð€è(€€€MQAÉ•™¥á=¹•9…Ù¥…Ñ¥½¹1¥™Ð€èô‰ä((€¥¹ÑÉ¼Ì¸¡Ì¡¸¡¡¥±((€¡…Ù”¡é•É¼€è(€€€€€ƒŠ"¨°(€€€€€€€MQ=µ•……Ñ•A½±å¹½µ¥…°(€€€€€€€€€€¡ÍÑ=µ•„Ì€Ä¸¨¤€ô€À€èô(€€€ÍÑ}½µ•…}ÁÉ•™¥á}½¹•}…Ñ•}•á¥ÍÑÌ(€€€€€Ì¸¡Ì¡¸¡¡¥±((€•á…Ð(€€€ÍÑ}½µ•…}…Ñ•}é•É½}±½Í•Í}Á…É•¹Ð(€€€€€Ì€Ä¸¡Ì¡é•É¼)€()Q¡¥ÌÍ¡½Õ±‰”Ñ¡”½¹±äµ½‘¥™¥…Ñ¥½¸Ñ¼Ñ¡”•á¥ÍÑ¥¹œ…Ñ¥Ù”™¥¹…°¡…¥¸¸()±°½Ñ¡•È¹•Ü½‘”¥Ì…‘‘¥Ñ¥Ù”¥¸Ñ¡”ƒ:¤Í•Ñ¥½¸¸((´´´((Œ€Ðà¸ÉÉ½ÈÑÉ¥…”‘ÕÉ¥¹œ¥µÁ±•µ•¹Ñ…Ñ¥½¸()Q¡”ÕÍ•ÈÝ¥±°¡…¹‘±”Íå¹Ñ…à½•±…‰½É…Ñ¥½¸•ÉÉ½ÉÌ¸…Ñ•½É¥é”Ñ¡•´…Ì™½±±½ÝÌ¸((ŒŒ…Ñ•½Éä€ÄƒŠP¹…µ”µ¥Íµ…Ñ ()á…µÁ±•Ìè()Ñ•áÐ)Õ¹­¹½Ý¸¥‘•¹Ñ¥™¥•È)¥¹Ù…±¥™¥•±)ÝÉ½¹œÑ¡•½É•´¹…µ•ÍÁ…”)€()I•Á…¥È‰äÕÍ¥¹œÑ¡”•á…ÐÍ½ÕÉ”¹…µ”¸()¼¹½Ð¡…¹”µ…Ñ¡•µ…Ñ¥Ì¸((´´´((ŒŒ…Ñ•½Éä€ÈƒŠP…ÉÕµ•¹Ð½É‘•È()á…µÁ±•Ìè()Ñ•áÐ)…ÁÁ±¥…Ñ¥½¸ÑåÁ”µ¥Íµ…Ñ )™Õ¹Ñ¥½¸•áÁ•Ñ•µ½É”…ÉÕµ•¹ÑÌ)€()%¹ÍÁ•ÐÑ¡•½É•´Í¥¹…ÑÕÉ”…¹É•½É‘•È•áÁ±¥¥ÐÁ…É…µ•Ñ•ÉÌ¸((´´´((ŒŒ…Ñ•½Éä€ÌƒŠP¬­©€Á½Í¥Ñ¥Ù¥Ñä()½ÈÕÍ”½˜è()±•…¸)ÍÑ…ÉÉå}±Ñ}™½ÕÈ)€()ÁÉ½Ù”è()±•…¸(ÄƒŠ&¬­¨)€()Ý¥Ñ è()±•…¸)½µ•„)€()™É½´è()±•…¸)¡¬€è€ÄƒŠ&¬¸)€((´´´((ŒŒ…Ñ•½Éä€ÐƒŠP•Ù•¹ÐÍ¥µÁ±¥™¥…Ñ¥½¸()%˜è()±•…¸)Í¥µÀ)€()‘½•Ì¹½ÐÕ¹™½±¹•ÍÑ•¥™Ì°ÕÍ”è()±•…¸)Õ¹™½±ÍÑ=µ•…Ù•¹Ñ=™MÑ…Ñ”)‰å}…Í•Ì¡€è€¸¸¸)‰å}…Í•Ì¡”€è€¸¸¸)Í¥µÀm¡°¡•t)€((´´´((ŒŒ…Ñ•½Éä€ÔƒŠPÁ…É•¹ÐÁÉ½©•Ñ¥½¸É•ÝÉ¥Ñ”½É¥•¹Ñ…Ñ¥½¸()%˜è()±•…¸)ÉÜoŠ@¡ÁÉ½©•Ñ¥½¸¸Ét)€()™…¥±Ì‰•…ÕÍ”1•…¸¡½Í”Ñ¡”ÝÉ½¹œ•ÅÕ…±¥Ñä½É¥•¹Ñ…Ñ¥½¸°ÕÍ”è()±•…¸)Í¥µÁ„m¡ÁÉ½©•Ñ¥½¸¸Ét)€()½ÈÉ•…Ñ”„¹…µ••ÅÕ…±¥ÑäÝ¥Ñ Ñ¡”É•ÅÕ¥É•‘¥É•Ñ¥½¸¸((´´´((ŒŒ…Ñ•½Éä€ØƒŠPÁ½±å¹½µ¥…°Ñ¡•½É•´½•É¥½¹Ì()¼¹½ÐÕ¹™½±è()±•…¸)MQ=µ•……Ñ•A½±å¹½µ¥…°)€()¥¹Í¥‘”Ñ¡”±½‰…°Ñ¡•½É•´¸()UÍ”è()±•…¸)ÍÑ}½µ•…}…Ñ•}Á½±å¹½µ¥…±}é•É½}¥™˜)€()Ñ¼…Ù½¥9…Ñ€½%¹Ñ€…ÍÐ¹½¥Í”¸((´´´((Œ€Ðä¸-••ÀÑ¡”±½‰…°Ñ¡•½É•´™É•”½˜…É¥Ñ¡µ•Ñ¥Œ¹½¥Í”()%‘•…°ÍÑÉÕÑÕÉ”½˜Ñ¡”¡…É±½‰…°Ñ¡•½É•´è()±•…¸)Ñ¡•½É•´ÍÑ}½µ•…}ÁÉ•™¥á}½¹•}¹½}™É••}µ¥ÉÉ½É}Á…É…‘½à€¸¸¸€è(€€€…±Í”€èô‰ä((€½‰Ñ…¥¸ƒŠ~¡«Š
 °¡¡¥±‘…Ñ—Š~¤€èô(€€€ÍÑ}½µ•…}¡¥±‘i•É½M•Ñ}¹½¹•µÁÑå}½™}¹…Ù¥…Ñ¥½¹}Ý¥Ñ¹•ÍÌ(€€€€€Ì€Ä¸¡¡¥±((€¡…Ù”¡ÍÑ•À€èô(€€€ÍÑ}½µ•…}Õ¹¥Ù•ÉÍ…±}•ÅÕ…Ñ¥½¸(€€€€€Ì€Ä¸«Š
 ((€¡…Ù”¡•¹•Éä€èô(€€€ÍÑ}½µ•…}½É¥¥¹}•á…Ð(€€€€€Ì€Ä¸«Š
 ¡Ì((€¡…Ù”¡½¹Í•ÉÙ•€èô(€€€ÍÑ}½µ•…}Á…É…‘½á¹•Éå}ÍÕŒ(€€€€€Ì€Ä¸«Š
 ((€¡…Ù”¡•¡¼€èô(€€€ÍÑ}½µ•…}…™™¥¹•}Ñ…¥±}‰±½­}•¡¼(€€€€€Ì€Ä¸¡Ì((€€´´…ÁÁ±äÑ¡”™½Éµ…±¥é•Á…É…‘½à½µ¥ÉÉ½ÈµÍÁ…”±•µµ„(€€¸¸¸)€()Q¡”±½‰…°Ñ¡•½É•´Í¡½Õ±É•…Í½¸¥¸Ñ•ÉµÌ½˜ÁÉ•Ù¥½ÕÍ±äÁÉ½Ù•ÍÑÉÕÑÕÉ…°)±•µµ…Ì¸()%ÐÍ¡½Õ±¹½ÐÉ•ÁÉ½Ù”è()Ñ•áÐ)…ÉÉä€ð€Ð)‘¥¥Ð€ð€Ì)½ÕÑÁÕÐ‘¥¥Ð•ÅÕ…Ñ¥½¸)…Ñ”Á½±å¹½µ¥…°¡…É…Ñ•É¥é…Ñ¥½¸)•Ù•¹Ð±…ÍÍ¥™¥…Ñ¥½¸)€()¥¹Í¥‘”¥ÑÍ•±˜¸((´´´((Œ€ÔÀ¸Q¡”•¹ÑÉ…°Ñ¡•½É•´¡¥•É…É¡ä()I•½µµ•¹‘••á…Ð¡¥•É…É¡äè()Ñ•áÐ)1=01	I+ŠRŠRŠRŠRŠRŠRŠRŠRŠRŠRŠRŠRŠR )ÍÑ}½µ•…}•Ù•¹Ñ}ÍÕÉÙ¥Ù•}¥™™}É…Ü)ÍÑ}½µ•…}Á…É•¹Ñ…ÉÉå}±Ñ}™½ÕÈ)ÍÑ}½µ•…}•Ù•¹Ñ}ÍÕÉÙ¥Ù•}¥™™}…Ñ•}é•É¼()5%II=HY9P=5QId+ŠRŠRŠRŠRŠRŠRŠRŠRŠRŠRŠRŠRŠRŠRŠRŠRŠRŠRŠRŠRŠR )ÍÑ}½µ•…}•Ù•¹Ñ}µ¥ÉÉ½É}¥¹Ù½±ÕÑ¥Ù”)ÍÑ}½µ•…}…Ñ¥Ù•}µ¥ÉÉ½É}™¥á•‘}¥™™}ÍÕÉÙ¥Ù”)ÍÑ}½µ•…}…Ñ¥Ù•}™¥á•‘}¥™™}…Ñ•}é•É¼()1=	09I0MAQ!=Id+ŠRŠRŠRŠRŠRŠRŠRŠRŠRŠRŠRŠRŠRŠRŠRŠRŠRŠRŠRŠRŠRŠRŠRŠRŠRŠRŠR )ÍÑ}½µ•…}ÁÉ•™¥á}½¹•}¹½}™É••}µ¥ÉÉ½É}Á…É…‘½à)ÍÑ}½µ•…}ÁÉ•™¥á}½¹•}Á…É…‘½á}µ¥ÉÉ½É}É•ÕÉÉ•¹”()9=9%0Q+ŠRŠRŠRŠRŠRŠRŠRŠRŠRŠRŠRŠRŠRŠR )ÍÑ}½µ•…}ÁÉ•™¥á}½¹•}…Ñ•}•á¥ÍÑÌ()=1AU	1%%9QI+ŠRŠRŠRŠRŠRŠRŠRŠRŠRŠRŠRŠRŠRŠRŠRŠRŠRŠRŠRŠR )ÍÑ}ÁÉ•™¥á}½¹•}¹…Ù¥…Ñ¥½¹}±¥™Ð()U9!9=9MU5IL+ŠRŠRŠRŠRŠRŠRŠRŠRŠRŠRŠRŠRŠRŠRŠRŠRŠRŠRŠR )ÍÑ}¹…Ù¥…Ñ¥½¹}Ý¥Ñ¹•ÍÍ}…±±}½™}ÁÉ•™¥á}½¹”)ÍÑ}¹…Ù¥…Ñ¥½¹}Ý¥Ñ¹•ÍÍ}™½ÕÉ}Á½Ý}‘¥Ù}Ñ¡É••}½™}ÁÉ•™¥á}½¹”)ÍÑ}Á½Ý•É}ÑÝ½}Ý…Ù•}±…É”)•É‘½Í}Ñ•É¹…Éå|É}•Ù•¹}Õ¹¥Ù•ÉÍ…°)•É‘½Í}Ñ•É¹…Éå|É}Õ¹¥Ù•ÉÍ…°)€((´´´((Œ€ÔÄ¸]¡äÑ¡”¹•Ü½‘”‰•±½¹Ì‰•™½É”Ñ¡”ÅÕ…É…¹Ñ¥¹•‰±½¬()Q¡”¹•ÜÑ¡•½É•´¥Ì½¹•ÁÑÕ…±±äÁ…ÉÐ½˜è()Ñ•áÐ+
MPƒ:§Š"x)€()¹½Ðè()Ñ•áÐ+
AI%`µ=9Mµ=9MUIId¸)€()A±…”•¹•É¥Œ•Ù•¹Ð‘•™¥¹¥Ñ¥½¹Ì…¹ƒ:¤±•µµ…Ì‰•Í¥‘”è()±•…¸)MQ=µ•…MÑ…Ñ”)MQ=µ•……Ñ•A½±å¹½µ¥…°)MQ=µ•…%¹™¥¹¥Ñ•	…‘QÉ…”)ÍÑ}½µ•…}…™™¥¹•}Ñ…¥±}‰±½­}•¡¼)€()Q¡•¸Ñ¡”™¥¹…°ÁÉ•™¥àµ½¹”Ñ¡•½É•´‰•½µ•Ì„Ñ¡¥¸½¹ÍÕµ•È¸()Q¡¥Ìµ…¥¹Ñ…¥¹ÌÑ¡”…É¡¥Ñ•ÑÕÉ”è()Ñ•áÐ+:¤±¥‰É…Éä(€ƒŠL)ÁÉ•™¥àµ½¹”Ñ¡•½É•´(€ƒŠL)™¥¹…°Á½Ý•ÈÑ¡•½É•´¸)€((´´´((Œ€ÔÈ¸]¡ä¹¼¹•ÜMQ=µ•…MÑ…Ñ•€™¥•±Í¡½Õ±‰”…‘‘•()¼¹½Ð…‘è()Ñ•áÐ)•Ù•¹Ð)µ¥ÉÉ½ÉÙ•¹Ð)¥ÍÑ¥Ù”)€()…ÌÍÑ½É•™¥•±‘Ì¸()Q¡•ä…É”‘•É¥Ù•ÁÉ½©•Ñ¥½¹Ì¸()¡…¹¥¹œÑ¡”ÍÑÉÕÑÕÉ”Ý½Õ±™½É”•Ù•Éä½¹ÍÑÉÕÑ¥½¸…¹•ÅÕ…±¥ÑäÑ¡•½É•´)…‰½ÕÐMQ=µ•…MÑ…Ñ•€Ñ¼‰”É•Á…¥É•¸()%¹ÍÑ•…è()±•…¸)‘•˜ÍÑ=µ•…Ù•¹Ñ=™MÑ…Ñ”€¡Ü€èMQ=µ•…MÑ…Ñ”¤€¸¸¸)€()Q¡¥Ì¥Ù•Ìé•É¼‰±…ÍÐÉ…‘¥ÕÌ¸((´´´((Œ€ÔÌ¸]¡ä¹¼¡…¹”Ñ¼ÍÑ=µ•…MÑ•Á€¥Ì¹••‘•()Q¡”•á¥ÍÑ¥¹œÍÑ•À…±É•…‘ä½¹Ñ…¥¹Ìè()Ñ•áÐ)Á…É•¹Ñ…ÉÉäœ)Á…É•¹Ñ¥¥Ðœ)¡¥±‘…ÉÉäœ)¡¥±‘¥¥Ðœ)…™™¥¹•…ÉÉäœ)‘•Í•¹Ðœ)Á…É…‘½á¹•Éäœ)€()Q¡”•Ù•¹Ð…Ð„ÍÑ…Ñ”¥Ì½µÁÕÑ•™É½´è()Ñ•áÐ)Á…É•¹Ñ…ÉÉä)Á…É•¹Ñ¥¥Ð)€()Í¼Ñ¡”µ¥ÉÉ½È½•Ù•¹Ðµ•¡…¹¥Ì…É”½‰Í•ÉÙ•ÉÌ½˜Ñ¡”•á¥ÍÑ¥¹œÑÉ…¹Í¥Ñ¥½¸¸()¼¹½ÐÁÕÐ•Ù•¹Ð¡…¹‘±¥¹œ¥¹Í¥‘”ÍÑ=µ•…MÑ•Á€¸((´´´((Œ€ÔÐ¸]¡äÑ¡”!…ÁÁäµ…Ñ”Á½±å¹½µ¥…°Í¡½Õ±É•µ…¥¸Ñ¡”…¹½¹¥…°½±±¥Í¥½¸A$()±Ñ¡½Õ Ñ¡”•Ù•¹ÐÑ¡•½É•´Í…åÌè()Ñ•áÐ)MUIY%YƒŠP!…ÁÁä…Ñ”°)€()Ñ¡”Í½ÕÉ”…±É•…‘äÕÍ•Ìè()±•…¸)MQ=µ•……Ñ•A½±å¹½µ¥…°€ô€À)€()…ÌÑ¡”ƒ:¤½±±¥Í¥½¸A$¸()-••ÀÑ¡…ÐA$¸()¥¹…°¡…¥¸è()Ñ•áÐ)Á…É…‘½àµ¥ÉÉ½È+ŠHMUIY%Y+ŠHÁ½±å¹½µ¥…°é•É¼+ŠH•á¥ÍÑ¥¹œ…Ñ•}é•É½}±½Í•Í}Á…É•¹Ð)€()Q¡¥ÌÉ•ÕÍ•ÌÑ¡”µ½ÍÐµ…ÑÕÉ”Í½ÕÉ”½‘”¸((´´´((Œ€ÔÔ¸á…ÐÍ½ÕÉ”µ¹…Ñ¥Ù”™¥¹…°±½¥…°…ÉÕµ•¹Ð()Q¡”µ¥ÍÍ¥¹œÑ¡•½É•´Í¡½Õ±Õ±Ñ¥µ…Ñ•±äÉ•…µ…Ñ¡•µ…Ñ¥…±±ä…Ìè()Ñ•áÐ)ÍÍÕµ”è(€¡¥±D¡Ì¬Ä±¸¤¡…Ì9…Ù¥…Ñ¥½¸¸()Q¡•¸è(€¡¥±ƒ:¤é•É¼µÍ•Ð¥Ì¹½¹•µÁÑä¸()Q¡”•á…Ðƒ:§Š"xÉ•ÕÉÉ•¹”•µ‰•‘ÌÑ¡…Ð…Ñ¥Ù”¡¥±•Ù•¹Ð)¥¹Í¥‘”Ñ¡”½¹Í•ÉÙ•Á•É™•ÐµÁ½Ý•ÈÁ…É…‘½àÍÁ…”¸()Q¡”…™™¥¹”‰±½¬•¡¼É•…Ñ•ÌÑ¡”µ¥ÉÉ½Èµ…±Ñ•É¹…Ñ¥Ù”½µÁ½¹•¹Ð¸()	äÑ¡”½µÁ±•Ñ••¹•É…°MÁ…”Q¡•½ÉäÁ…É…‘½à½µ¥ÉÉ½È±…Ü°)„…¹½¹¥…°ƒ:§Š"x…Ñ¥Ù”Ý…Ù”…¹¹½ÐÉ•µ…¥¸•¹Ñ¥É•±ä)¥¹Í¥‘”Ñ¡”¹½¸µ™¥á•IQŠQMQI=dÍ•Ñ½È¸()Q¡•É•™½É”è(€Í½µ”…¹½¹¥…°ƒ:¤•Ù•¹Ð¥Ì…Ñ¥Ù”…¹µ¥ÉÉ½Èµ™¥á•¸()¥¹¥Ñ”•Ù•¹Ð±…ÍÍ¥™¥…Ñ¥½¸è(€…Ñ¥Ù”€¬µ¥ÉÉ½Èµ™¥á•€ôMUIY%Y¸()MUIY%Y•ÅÕ¥Ù…±•¹”è(€MUIY%Y€ôMQ=µ•……Ñ•A½±å¹½µ¥…°é•É¼¸()á¥ÍÑ¥¹œÁ…É•¹ÐÁÉ½©•Ñ¥½¸è(€Á½±å¹½µ¥…°é•É¼¥Ù•ÌÁ…É•¹Ð9…Ù¥…Ñ¥½¸¸()Q¡•É•™½É”è(€D¡Ì°Ä¬Í¸¤¡…Ì9…Ù¥…Ñ¥½¸¸)€()Q¡¥Ì¥ÌÑ¡”•á…ÐÉ•Á±…•µ•¹Ð™½ÈÑ¡”½±‰…µÉ•™±•Ñ¥½¸…ÑÑ•µÁÐ¸((´´´((Œ€ÔØ¸A½ÍÐµÉ••¸±•…¹ÕÀ()=¹±ä…™Ñ•ÈÑ¡”•¹Ñ¥É”™¥¹…°Ñ¡•½É•´¥ÌÉ••¸è((ŒŒA½ÍÍ¥‰±”‘•±•Ñ¥½¹Ì()½¹Í¥‘•ÈÉ•µ½Ù¥¹œè()±•…¸)MQAÉ•™¥á=¹•	…‘I•™±•Ñ¥½¸)MQAÉ•™¥á=¹•M••‘½É”)ÍÑ}ÁÉ•™¥á}½¹•}Í••‘}½É•}½™}‰…‘}É•™±•Ñ¥½¸)ÍÑ}ÁÉ•™¥á}½¹•}¹…Ù¥…Ñ¥½¹}±¥™Ñ}½™}Í••‘}½É”)ÍÑ}ÁÉ•™¥á}½¹•}¹…Ù¥…Ñ¥½¹}±¥™Ñ}½™}‰…‘}É•™±•Ñ¥½¸)€()%˜Õ¹ÕÍ•¸()A½ÍÍ¥‰±ä…±Í¼è()±•…¸)MQM••‘=¹•™™¥¹•]¥Ñ¹•ÍÌ)ÍÑ}ÁÉ•™¥á}½¹•}ÁÉ½‘ÕÑ}ÍÑ…Ñ”)ÍÑ}ÁÉ•™¥á}½¹•}¹…Ù¥…Ñ¥½¹}½™}Í••‘}Ý¥Ñ¹•ÍÌ)€()¥˜¹¼½Ñ¡•È…Ñ¥Ù”Ñ¡•½É•´É•™•É•¹•ÌÑ¡•´¸()UÍ”„É•™•É•¹”Í•…É ‰•™½É”‘•±•Ñ¥¹œ¸((´´´((Œ€ÔÜ¸EÕ…É…¹Ñ¥¹•±•…ä½‘”()¼¹½ÐÕ¸µ½µµ•¹Ðè()Ñ•áÐ)ÍÑ}½µ•…}Ñ•Éµ¥¹…Ñ¥½¹}ÌÄ)ÍÑ}½µ•…}Ñ•Éµ¥¹…Ñ¥½¹}ÌÌ)ÍÑ}½µ•…}Ñ•Éµ¥¹…Ñ¥½¹}ÍÑ…‰±”)ÍÑ}É•Í¥‘Õ…±}½µ•…}Ñ•Éµ¥¹…Ñ¥½¸)€()Q¡”¹•Ü¥¹™¥¹¥Ñäµ½¹ÑÉ½°ÁÉ½½˜ÍÕÁ•ÉÍ•‘•ÌÑ¡…ÐÉ½ÕÑ”¸()1•…Ù”Ñ¡”…É¡…•½±½ä½µµ•¹Ð¥¹Ñ…ÐÕ¹Ñ¥°±…Ñ•È±•…¹ÕÀ¸((´´´((Œ€Ôà¸!•…‘•È½ÉÉ•Ñ¥½¸…™Ñ•ÈÁÉ½½˜½µÁ±•Ñ¥½¸()™Ñ•ÈÑ¡”Í½ÕÉ”¡…Ìé•É¼Í½ÉÉå€°ÕÁ‘…Ñ”±¥¹”€È™É½´Ñ¡”ÍÑ…±”è()Ñ•áÐ(´´€ÄÀÀÀÄ±¥¹•Ì°€ÀÍ½ÉÉä°€À¹…Ñ¥Ù•}‘•¥‘”)€()Ñ¼„ÍÑ…Ñ•µ•¹ÐÑ¡…Ð‘½•Ì¹½Ð¡…É‘½‘”…¸•…Í¥±äÍÑ…±”±¥¹”½Õ¹Ð°™½È•á…µÁ±”è()Ñ•áÐ(´´-•É¹•°µ…Õ‘¥Ñ•MP™½Éµ…±¥é…Ñ¥½¸èé•É¼Í½ÉÉä¥¸Ñ¡”…Ñ¥Ù”Ñ¡•½É•´¡…¥¸¸)€()¼Ñ¡¥Ì½¹±ä…™Ñ•ÈÙ•É¥™¥…Ñ¥½¸¸((´´´((Œ€Ôä¸¥¹…°Í½ÕÉ”…Õ‘¥Ð½µµ…¹‘Ì()IÕ¸…™Ñ•È¥µÁ±•µ•¹Ñ…Ñ¥½¸è()Á½Ý•ÉÍ¡•±°)M•±•ÐµMÑÉ¥¹œ€µA…Ñ É‘½ÍQ•É¹…ÉäÈ¹±•…¸±MQQ…Ñ¥Œ¹±•…¸€(€€µA…ÑÑ•É¸€q‰Í½ÉÉåq‰ñq‰…‘µ¥Ñq‰ñµ­M½ÉÉåñyqÌ©…á¥½µqˆœ)€()áÁ•Ñ•…Ñ¥Ù”µ…Ñ¡•µ…Ñ¥…°É•ÍÕ±Ðè()Ñ•áÐ)¹¼Í½ÉÉä)¹¼…‘µ¥Ð)¹¼µ­M½ÉÉä)¹¼ÕÍÑ½´…á¥½´)€()I•µ•µ‰•ÈÑ¡…Ð½µµ•¹ÑÌ½¹Ñ…¥¹¥¹œÑ¡”Ý½ÉÍ½ÉÉå€µ…äÍÑ¥±°…ÁÁ•…Èì¥¹ÍÁ•Ð)µ…Ñ¡•Ìµ…¹Õ…±±ä¸()Q¡•¸ÉÕ¸è()±•…¸(ÁÉ¥¹Ð…á¥½µÌÍÑ}½µ•…}•Ù•¹Ñ}ÍÕÉÙ¥Ù•}¥™™}…Ñ•}é•É¼(ÁÉ¥¹Ð…á¥½µÌÍÑ}½µ•…}ÁÉ•™¥á}½¹•}¹½}™É••}µ¥ÉÉ½É}Á…É…‘½à(ÁÉ¥¹Ð…á¥½µÌÍÑ}½µ•…}ÁÉ•™¥á}½¹•}…Ñ•}•á¥ÍÑÌ(ÁÉ¥¹Ð…á¥½µÌÍÑ}ÁÉ•™¥á}½¹•}¹…Ù¥…Ñ¥½¹}±¥™Ð(ÁÉ¥¹Ð…á¥½µÌÍÑ}Á½Ý•É}ÑÝ½}Ý…Ù•}±…É”(ÁÉ¥¹Ð…á¥½µÌ•É‘½Í}Ñ•É¹…Éå|É}•Ù•¹}Õ¹¥Ù•ÉÍ…°(ÁÉ¥¹Ð…á¥½µÌ•É‘½Í}Ñ•É¹…Éå|É}Õ¹¥Ù•ÉÍ…°)€()Q¡”¹•ÜÁÉ½½˜µÕÍÐ¹½Ð¥¹ÑÉ½‘Õ”„ÕÍÑ½´…á¥½´¸((´´´((Œ€ØÀ¸	Õ¥±µÍÕ•ÍÌ½É‘•È()Q¡”•á…ÐÍÕ•ÍÌÉ¥Ñ•É¥½¸¥Ìè()Ñ•áÐ(Ä¸MQQ…Ñ¥Œ¹±•…¸‰Õ¥±‘ÌÕ¹¡…¹•¸((È¸É‘½ÍQ•É¹…ÉäÈ¹±•…¸‰Õ¥±‘ÌÝ¥Ñ ¹•Ü•Ù•¹Ð±…å•È¸((Ì¸±°±½…°µ¥ÉÉ½È½…Ñ”Ñ¡•½É•µÌ½µÁ¥±”¸((Ð¸ÍÑ}½µ•…}ÁÉ•™¥á}½¹•}¹½}™É••}µ¥ÉÉ½É}Á…É…‘½à½µÁ¥±•Ì¸((Ô¸ÍÑ}½µ•…}ÁÉ•™¥á}½¹•}…Ñ•}•á¥ÍÑÌ½µÁ¥±•Ì¸((Ø¸ÍÑ}ÁÉ•™¥á}½¹•}¹…Ù¥…Ñ¥½¹}±¥™Ð½µÁ¥±•ÌÝ¥Ñ 9<Í½ÉÉä¸((Ü¸ÍÑ}¹…Ù¥…Ñ¥½¹}Ý¥Ñ¹•ÍÍ}™½ÕÉ}Á½Ý}‘¥Ù}Ñ¡É••}½™}ÁÉ•™¥á}½¹”½µÁ¥±•ÌÕ¹¡…¹•¸((à¸ÍÑ}Á½Ý•É}ÑÝ½}Ý…Ù•}±…É”½µÁ¥±•ÌÕ¹¡…¹•¸((ä¸•É‘½Í}Ñ•É¹…Éå|É}•Ù•¹}Õ¹¥Ù•ÉÍ…°½µÁ¥±•ÌÕ¹¡…¹•¸((ÄÀ¸•É‘½Í}Ñ•É¹…Éå|É}Õ¹¥Ù•ÉÍ…°½µÁ¥±•ÌÕ¹¡…¹•¸((ÄÄ¸€ÁÉ¥¹Ð…á¥½µÌÍ¡½ÝÌ¹¼¹•Üµ…Ñ¡•µ…Ñ¥…°…á¥½´¸)€()Q¡…Ð¥ÌÑ¡”ÍÕÉ¥…°‘•™¥¹¥Ñ¥½¸½˜ÍÕ•ÍÌ¸((´´´((Œ€ØÄ¸5¥¹¥µ…°µ•‘¥ÐÍÕµµ…Éä((ŒŒ()%¹Í¥‘”Ñ¡”…Ñ¥Ù”ƒ:§Š"x±¥‰É…Éäè()Ñ•áÐ)MQ=µ•…Ù•¹Ð)ÍÑ=µ•…A…É•¹Ñ=ÕÑÁÕÑ¥¥Ð)ÍÑ=µ•…Ù•¹Ñ=™MÑ…Ñ”)ÍÑ=µ•…Ù•¹Ð()ÍÑ}½µ•…}•Ù•¹Ñ}ÍÕÉÙ¥Ù•}¥™™}É…Ü)ÍÑ}½µ•…}Á…É•¹Ñ…ÉÉå}±Ñ}™½ÕÈ)ÍÑ}½µ•…}Á…É•¹Ñ¥¥Ñ}±Ñ}Ñ¡É•”)ÍÑ}½µ•…}•Ù•¹Ñ}ÍÕÉÙ¥Ù•}¥™™}…Ñ•}é•É¼()MQ=µ•…Ù•¹Ð¹µ¥ÉÉ½È)MQ=µ•…Ù•¹Ð¹Ñ¥Ù”)ÍÑ}½µ•…}•Ù•¹Ñ}µ¥ÉÉ½É}¥¹Ù½±ÕÑ¥Ù”)ÍÑ}½µ•…}…Ñ¥Ù•}µ¥ÉÉ½É}™¥á•‘}¥™™}ÍÕÉÙ¥Ù”)ÍÑ}½µ•…}…Ñ¥Ù•}™¥á•‘}¥™™}…Ñ•}é•É¼()MQ=µ•…A…É…‘½á5¥ÉÉ½ÉI•ÕÉÉ•¹”)ÍÑ}½µ•…}ÁÉ•™¥á}½¹•}¹½}™É••}µ¥ÉÉ½É}Á…É…‘½à)ÍÑ}½µ•…}ÁÉ•™¥á}½¹•}Á…É…‘½á}µ¥ÉÉ½É}É•ÕÉÉ•¹”)ÍÑ}½µ•…}ÁÉ•™¥á}½¹•}…Ñ•}•á¥ÍÑÌ)€((ŒŒIA1()=¹±äÑ¡”ÁÉ½½˜‰½‘ä½˜è()±•…¸)ÍÑ}ÁÉ•™¥á}½¹•}¹…Ù¥…Ñ¥½¹}±¥™Ð)€((ŒŒ<9=P!9()Ñ•áÐ)MQ=µ•…MÑ…Ñ”)ÍÑ=µ•…MÑ•À)ÍÑ=µ•„)MQ=µ•……Ñ•A½±å¹½µ¥…°)ÍÑ}½µ•…}…Ñ•}é•É½}±½Í•Í}Á…É•¹Ð()MQQ…Ñ¥Œ¹±•…¸()ÍÑ}Á½Ý•É}ÑÝ½}Ý…Ù•}±…É”)•É‘½Í}Ñ•É¹…Éå|É}•Ù•¹}Õ¹¥Ù•ÉÍ…°)•É‘½Í}Ñ•É¹…Éå|É}Õ¹¥Ù•ÉÍ…°)€()Õ¹Ñ¥°Ñ¡”¹•ÜÁ…Ñ ¥ÌÉ••¸¸((´´´((Œ€ØÈ¸¥¹…°É•Á±…•µ•¹ÐÁÉ½½˜()Q¡¥Ì¥ÌÑ¡”Ñ…É•Ð™¥¹…°Í¡…Á”è()±•…¸)Ñ¡•½É•´ÍÑ}ÁÉ•™¥á}½¹•}¹…Ù¥…Ñ¥½¹}±¥™Ð€è(€€€MQAÉ•™¥á=¹•9…Ù¥…Ñ¥½¹1¥™Ð€èô‰ä((€¥¹ÑÉ¼Ì¸¡Ì¡¸¡¡¥±((€¡…Ù”¡é•É¼€è(€€€€€ƒŠ"¨°(€€€€€€€MQ=µ•……Ñ•A½±å¹½µ¥…°(€€€€€€€€€€¡ÍÑ=µ•„Ì€Ä¸¨¤€ô€À€èô(€€€ÍÑ}½µ•…}ÁÉ•™¥á}½¹•}…Ñ•}•á¥ÍÑÌ(€€€€€Ì¸¡Ì¡¸¡¡¥±((€•á…Ð(€€€ÍÑ}½µ•…}…Ñ•}é•É½}±½Í•Í}Á…É•¹Ð(€€€€€Ì€Ä¸¡Ì¡é•É¼)€()Q¡”½±€ÈÀµ±¥¹”…ÑÑ•µÁÑ•‰…µÉ•™±•Ñ¥½¸‰½‘ä…¹¥ÑÌÍ½ÉÉå€‘¥Í…ÁÁ•…È¸((´´´((Œ€ØÌ¸=¹”µÍ•¹Ñ•¹”…É¡¥Ñ•ÑÕÉ…°É•ÍÕ±Ð()Q¡”€ÜàäÄµ±¥¹”…¹½¹¥…°™¥±”‘½•Ì€¨©¹½Ð¨¨¹••„±…É”É•ÝÉ¥Ñ”¸()%Ð¹••‘Ìè()Ñ•áÐ)½¹”¹•ÜÍ½ÕÉ”µ¹…Ñ¥Ù”ƒ:§Š"xÁ…É…‘½à½µ¥ÉÉ½ÈÑ¡•½É•´±…å•È(¬)½¹”É•Á±…•µ•¹ÐÁÉ½½˜‰½‘ä…ÐÑ¡”Í¥¹±”Í½ÉÉä(ô)Ñ¡”•á¥ÍÑ¥¹œ™¥¹…°Ñ¡•½É•´¡…¥¸‰•½µ•ÌÕÍ…‰±”Õ¹¡…¹•¸)€()Q¡…Ð¥ÌÑ¡”¡¥¡•ÍÐµÁÉ•¥Í¥½¸ÍÕÉ¥…°É½ÕÑ”Ù¥Í¥‰±”¥¸Ñ¡”…ÑÕ…°ÕÁ±½…‘•)Í½ÕÉ”¸(