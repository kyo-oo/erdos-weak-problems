<!-- ======================================================================
<!-- CHRONOLOGICAL LABEL -- #0037 / 1132
<!--    Path         : docs/GST_OMEGA_PARADOX_MIRROR_LEAN_SURGERY_PLAN.md
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

# GST Ω∞ PARADOX–MIRROR LEAN SURGERY PLAN
## Separate formalization handoff for the 7,800+ line canonical Lean file

**Purpose:** This document is a surgical implementation plan only. It does **not** edit the main Lean file.

**Line-count note:** I did not independently recount the canonical Lean file in this turn. The only size figure being used is the user's own description: **7,800+ lines**. Therefore this plan uses **named theorem/definition anchors**, never brittle numeric line positions.

**Core policy:** no `sorry`, no `admit`, no `axiom` inserted to bridge the mathematics. Syntax/name mismatches can be repaired during implementation; mathematical obligations may not be hidden.

---

# 0. What this surgery is replacing

The old proof architecture tried to close the large-power GST result through some combination of:

```text
finite descent
prefix reflection
same-position Navigation transport
`gst_omega` expansion
case growth
eventual contradiction
```

The replacement architecture keeps the original arithmetic and GST graph, but removes the need to force an infinite GST trace into a finite search.

The new architecture is:

```text
exact GST edge
    ↓
CREATE / DESTROY / SURVIVE / NEITHER
    ↓
mirror involution
    ↓
active mirror-fixed event ↔ SURVIVE
    ↓
SURVIVE ↔ Happy Gate
    ↓
existing GST paradox / mirror-alternative Ω∞ law
    ↓
canonical Ω∞ ray cannot be complete-bad
    ↓
Navigation witness
    ↓
existing perfect-power transport
    ↓
existing downstream universal theorem
```

The public theorem signatures downstream should be preserved wherever possible.

---

# 1. DO NOT rewrite the 7,800+ line file

This should be a **local dependency surgery**, not a rewrite.

Keep the proven arithmetic spine, especially the definitions/theorems corresponding to:

```lean
gstDigit
gstCarry
gstDescent
gstWindow9
gstSpaceAt

GSTSpace
GSTNavigationWitness
GSTBadPair

gstOutputDigit / exact output-digit theorem
gst next-carry theorem
gst carry bound (< 4)
gst digit bound (< 3)

gstNavigationConstant
perfect-power/LTE decomposition
generalized cascade recurrence

affine carry definitions
affine digit equation
affine carry recurrence
block echo

GSTOmegaState
existing Ω∞ projections / exactness identities
existing origin/cascade/descent infrastructure

existing small/base-range results
existing final transport from Navigation to the power theorem
existing universal theorem packaging
```

Do not modify working definitions just to make the new layer aesthetically cleaner.

---

# 2. What should be removed from the ACTIVE dependency path

Do not necessarily delete old research lemmas. Instead, stop making the final theorem depend on them.

The old active path to cut is conceptually:

```text
global/prefix bad reflection
        ↓
finite termination or repeated gst_omega expansion
        ↓
large-power contradiction
```

In particular:

- do not expand `gst_omega` position after position to prove the final global statement;
- do not require a guessed finite ceiling;
- do not require a universal same-position reflection theorem if the new Ω∞ theorem already yields a Navigation witness;
- do not use experimental creation/destruction ratios as proof hypotheses;
- do not infer empty intersection merely from entropy/dimension.

If the old theorems are referenced nowhere after surgery, they may remain as historical/helper code.

---

# 3. Insertion point A — wave-event layer

Insert this **after** the core GST digit/carry/output equations are already available and **before** the Ω∞ global theorems.

Use a new namespace if the canonical file is already crowded:

```lean
namespace GSTOmega
```

## 3.1 Event type

```lean
inductive GSTEvent
  | create
  | destroy
  | survive
  | neither
deriving DecidableEq, Repr
```

## 3.2 Event classifier

Keep this definition independent of carry; classify from input/output digits.

```lean
def gstEventOfDigits (d e : Nat) : GSTEvent :=
  if d = 2 then
    if e = 2 then .survive
    else .destroy
  else
    if e = 2 then .create
    else .neither
```

Graph projection:

```lean
def gstWaveEvent (R p : Nat) : GSTEvent :=
  gstEventOfDigits
    (gstDigit R p)
    (gstDigit (4 * R) p)
```

If the file already has a theorem proving the output digit without literally forming `4*R`, reuse it in proofs; do not change the definition unless multiplication causes simplifier problems.

---

# 4. Prove the event partition immediately

Do not move forward until the classifier has a complete finite proof layer.

Useful lemmas:

```lean
theorem gstEventOfDigits_survive_iff (d e : Nat) :
    gstEventOfDigits d e = .survive ↔ d = 2 ∧ e = 2 := by
  unfold gstEventOfDigits
  by_cases hd : d = 2
  · subst d
    simp
  · simp [hd]
```

```lean
theorem gstEventOfDigits_destroy_iff (d e : Nat) :
    gstEventOfDigits d e = .destroy ↔ d = 2 ∧ e ≠ 2 := by
  unfold gstEventOfDigits
  by_cases hd : d = 2
  · subst d
    by_cases he : e = 2 <;> simp [he]
  · simp [hd]
```

```lean
theorem gstEventOfDigits_create_iff (d e : Nat) :
    gstEventOfDigits d e = .create ↔ d ≠ 2 ∧ e = 2 := by
  unfold gstEventOfDigits
  by_cases hd : d = 2
  · simp [hd]
  · simp [hd]
```

```lean
theorem gstEventOfDigits_neither_iff (d e : Nat) :
    gstEventOfDigits d e = .neither ↔ d ≠ 2 ∧ e ≠ 2 := by
  unfold gstEventOfDigits
  by_cases hd : d = 2
  · simp [hd]
  · by_cases he : e = 2 <;> simp [hd, he]
```

These are purely definitional. They should not involve GST arithmetic.

---

# 5. Insertion point B — mirror alternative event geometry

## 5.1 Mirror involution

```lean
def GSTEvent.mirror : GSTEvent → GSTEvent
  | .create  => .destroy
  | .destroy => .create
  | .survive => .survive
  | .neither => .neither
```

```lean
theorem gst_event_mirror_involutive :
    Function.Involutive GSTEvent.mirror := by
  intro e
  cases e <;> rfl
```

## 5.2 Active event

The event-level notion of "active" means a digit `2` participates on at least one side.

```lean
def GSTEvent.Active : GSTEvent → Prop
  | .create  => True
  | .destroy => True
  | .survive => True
  | .neither => False
```

Then the critical finite theorem:

```lean
theorem gst_active_mirror_fixed_iff_survive
    (e : GSTEvent) :
    e.Active ∧ e.mirror = e ↔ e = .survive := by
  cases e <;>
    simp [GSTEvent.Active, GSTEvent.mirror]
```

This theorem should compile with no GST arithmetic whatsoever.

This is an important design choice: the paradox-space theorem will only have to produce an **active mirror-fixed event**. The finite event layer then converts it into SURVIVE.

---

# 6. Insertion point C — prove SURVIVE = Happy Gate

This is the arithmetic bridge.

The original GST graph has

```text
output digit = (carry + 4*inputDigit) mod 3.
```

At input digit `2`:

```text
output = 2
↔ carry mod 3 = 0
↔ carry = 0 or carry = 3
```

because the actual carry is in `{0,1,2,3}`.

## 6.1 Preferred theorem

```lean
theorem gst_waveEvent_survive_iff
    (R p : Nat) :
    gstWaveEvent R p = .survive
      ↔
    gstDigit R p = 2
      ∧
    (gstCarry R p = 0 ∨ gstCarry R p = 3) := by
  rw [gstEventOfDigits_survive_iff]
  constructor

  · rintro ⟨hd, hout⟩
    refine ⟨hd, ?_⟩

    have hcarry_lt : gstCarry R p < 4 := by
      exact gstCarry_lt_four R p
      -- replace with canonical theorem name if different

    have hout_exact :
        gstDigit (4 * R) p
          =
        (gstCarry R p + 4 * gstDigit R p) % 3 := by
      exact gstOutputDigit_forward_exact R p
      -- align exact theorem arguments/name

    rw [hout_exact, hd] at hout

    have hcarry_cases :
        gstCarry R p = 0
        ∨ gstCarry R p = 1
        ∨ gstCarry R p = 2
        ∨ gstCarry R p = 3 := by
      omega

    rcases hcarry_cases with h0 | h1 | h2 | h3
    · exact Or.inl h0
    · subst h1
      norm_num at hout
    · subst h2
      norm_num at hout
    · exact Or.inr h3

  · rintro ⟨hd, hcarry⟩
    refine ⟨hd, ?_⟩

    have hout_exact :
        gstDigit (4 * R) p
          =
        (gstCarry R p + 4 * gstDigit R p) % 3 := by
      exact gstOutputDigit_forward_exact R p

    rw [hout_exact, hd]
    rcases hcarry with h0 | h3
    · rw [h0]
      norm_num
    · rw [h3]
      norm_num
```

### Important

If `gstCarry_lt_four` is only proven for `p > 0`, split `p = 0` first. At `p=0` the carry definition usually simplifies to zero.

Do **not** solve this theorem with `native_decide`; it is a symbolic universal theorem.

---

# 7. Navigation equivalence layer

After SURVIVE = Happy Gate, convert between the event formulation and the file's original `GSTNavigationWitness`.

The source definition is conceptually:

```lean
def GSTNavigationWitness (R : Nat) : Prop :=
  ∃ p,
    gstDigit R p = 2 ∧
      (gstSpaceAt R p = .gstPlus ∨ gstSpaceAt R p = .null)
```

Prove small carry/space conversion lemmas if they do not already exist:

```lean
theorem gst_space_gate_iff_carry_gate (R p : Nat) :
    (gstSpaceAt R p = .gstPlus ∨ gstSpaceAt R p = .null)
      ↔
    (gstCarry R p = 3 ∨ gstCarry R p = 0) := by
  unfold gstSpaceAt
  by_cases h0 : gstCarry R p = 0
  · simp [h0]
  · by_cases h3 : gstCarry R p = 3
    · simp [h0, h3]
    · simp [h0, h3]
```

Then:

```lean
theorem gst_navigationWitness_iff_survive (R : Nat) :
    GSTNavigationWitness R
      ↔
    ∃ p, gstWaveEvent R p = .survive := by
  constructor

  · rintro ⟨p, hd, hspace⟩
    refine ⟨p, ?_⟩
    rw [gst_waveEvent_survive_iff]
    refine ⟨hd, ?_⟩
    -- convert hspace to carry 0/3
    -- keep disjunction order consistent
    ...

  · rintro ⟨p, hp⟩
    rw [gst_waveEvent_survive_iff] at hp
    rcases hp with ⟨hd, hcarry⟩
    refine ⟨p, hd, ?_⟩
    -- convert carry 0/3 back to .null/.gstPlus
    ...
```

If there are already canonical lemmas mapping `.null ↔ carry=0` and `.gstPlus ↔ carry=3`, reuse them instead of unfolding `gstSpaceAt`.

---

# 8. Do NOT create a second Ω state

The source already contains a multi-field `GSTOmegaState` / Ω∞ layer.

Do **not** introduce a replacement structure unless the old one is impossible to reuse.

Add only an **event projection** from the existing Ω state.

Conceptually:

```lean
def gstOmegaEvent (Ω : Nat → GSTOmegaState) (p : Nat) : GSTEvent :=
  gstEventOfDigits
    (gstOmegaInputDigit (Ω p))
    (gstOmegaOutputDigit (Ω p))
```

Use the actual existing field/projection names.

If the Ω state stores parent digit/carry but not output digit, derive output through the existing exact GST output theorem.

The purpose is to keep every old exact Ω invariant usable.

---

# 9. Ω exactness bridge

Before using paradox geometry, prove that the event projected from Ω is exactly the event of the represented natural number / Navigation Constant.

Target shape:

```lean
theorem gst_omega_event_exact
    (R : Nat)
    (Ω : Nat → GSTOmegaState)
    (hexact : GSTOmegaRepresents Ω R)
    (p : Nat) :
    gstOmegaEvent Ω p = gstWaveEvent R p := by
  unfold gstOmegaEvent gstWaveEvent
  congr
  · exact gst_omega_input_digit_exact Ω R hexact p
  · exact gst_omega_output_digit_exact Ω R hexact p
```

If the existing Ω layer already has separate parent/child exactness theorems, use them.

This theorem is vital: it prevents the paradox/mirror graph from becoming a disconnected abstraction.

---

# 10. Formalize the paradox / mirror law at the Ω∞ level

## Critical implementation rule

Do **not** define the paradox law as:

```lean
def GSTParadoxSpace Ω : Prop :=
  ∃ p, gstOmegaEvent Ω p = .survive
```

That would bake the desired conclusion into the definition.

Instead, preserve the user's General Space Theory semantics:

```text
paradox space
+
mirror alternative space
+
Ω∞ wave recurrence
→
active mirror-fixed intersection
```

The exact existing GST definitions should be the source of this theorem.

Target theorem:

```lean
theorem gst_paradox_active_fixed
    (Ω : Nat → GSTOmegaState)
    (hparadox : GSTParadoxSpace Ω)
    (hmirror : GSTMirrorAlternativeSpace Ω)
    (hwave : GSTOmegaWave Ω) :
    ∃ p,
      (gstOmegaEvent Ω p).Active
        ∧
      (gstOmegaEvent Ω p).mirror
        =
      gstOmegaEvent Ω p := by
  -- This proof must unfold / consume the existing GST
  -- paradox-space and mirror-alternative-space laws.
```

### Very important subtlety

Do **not** formalize `GSTOmegaWave Ω` as:

```lean
∀ p, (gstOmegaEvent Ω p).Active
```

for natural-number digit streams. A natural number has an eventual zero tail.

The "wave continues infinitely" belongs to the **Ω-space dynamics**, not to the claim that every ordinary ternary position contains an active CREATE/DESTROY/SURVIVE event.

The theorem only needs the paradox/mirror recurrence to force **some** active mirror-fixed event along the complete Ω orbit.

---

# 11. Immediately collapse paradox recurrence to SURVIVE

Once `gst_paradox_active_fixed` exists:

```lean
theorem gst_paradox_forces_survive
    (Ω : Nat → GSTOmegaState)
    (hparadox : GSTParadoxSpace Ω)
    (hmirror : GSTMirrorAlternativeSpace Ω)
    (hwave : GSTOmegaWave Ω) :
    ∃ p, gstOmegaEvent Ω p = .survive := by
  obtain ⟨p, hactive, hfixed⟩ :=
    gst_paradox_active_fixed Ω hparadox hmirror hwave

  refine ⟨p, ?_⟩

  exact
    (gst_active_mirror_fixed_iff_survive
      (gstOmegaEvent Ω p)).mp
      ⟨hactive, hfixed⟩
```

This theorem should be extremely short.

That is desirable: all geometric complexity remains in exactly one theorem, `gst_paradox_active_fixed`.

---

# 12. Define complete Ω badness as a projection, not a new arithmetic system

Use the existing `GSTBadPair`.

```lean
def GSTOmegaCompleteBad
    (Ω : Nat → GSTOmegaState) : Prop :=
  ∀ p,
    GSTBadPair
      (gstOmegaCarry Ω p)
      (gstOmegaInputDigit Ω p)
```

Or, preferably, if there is already a "bad trace" predicate, reuse it.

Prove:

```lean
theorem gst_omega_completeBad_iff_no_survive
    (Ω : Nat → GSTOmegaState)
    (hexact : GSTOmegaExact Ω) :
    GSTOmegaCompleteBad Ω
      ↔
    ∀ p, gstOmegaEvent Ω p ≠ .survive := by
  ...
```

The proof is pointwise using:

```text
GSTBadPair
↔ not Happy Gate
↔ not SURVIVE.
```

Do not unfold the entire Ω state here.

---

# 13. The main Ω∞ contradiction theorem

This is the theorem that replaces the old finite-global contradiction layer.

```lean
theorem gst_no_complete_bad_paradox_omega
    (Ω : Nat → GSTOmegaState)
    (hparadox : GSTParadoxSpace Ω)
    (hmirror : GSTMirrorAlternativeSpace Ω)
    (hwave : GSTOmegaWave Ω)
    (hexact : GSTOmegaExact Ω) :
    ¬ GSTOmegaCompleteBad Ω := by

  intro hbad

  have hnosurvive :
      ∀ p, gstOmegaEvent Ω p ≠ .survive := by
    exact
      (gst_omega_completeBad_iff_no_survive Ω hexact).mp
        hbad

  obtain ⟨p, hsurvive⟩ :=
    gst_paradox_forces_survive
      Ω hparadox hmirror hwave

  exact hnosurvive p hsurvive
```

This proof is the desi��-�G����ƭy�tly and shorten the theorem.

---

# 16. Where to rewire the 7,800+ line file

Do not change every consumer.

Find the **first active theorem whose proof currently needs the unresolved global GST exclusion**.

From the current research history this is around the large-power wave theorem, conceptually named:

```lean
gst_power_two_wave_large
```

or the canonical Navigation theorem it consumes.

### Preferred surgery

Keep its **statement** unchanged.

Replace only its proof body.

Example pattern:

```lean
theorem gst_power_two_wave_large
    (a : Nat)
    (ha : LARGE_BOUND ≤ a) :
    GSTPowerTwoWave a := by

  -- preserve existing v3 / exponent normalization
  obtain ⟨s, b, hs, hb, hdecomp, ...⟩ :=
    existing_power_normalization a ha

  have hnavQ :
      GSTNavigationWitness
        (gstNavigationConstant s b) :=
    gst_canonical_omega_navigation
      s b hs hb
      (existing_exception_exclusion a ha ...)

  -- use already-proved transport from Q_s(b)
  -- back to the relevant power/wave
  exact existing_power_two_wave_of_navigation
    a s b hdecomp hnavQ ...
```

The exact final constructor depends on the existing theorem's return type.

### Why preserve the statement?

Because every theorem below it can remain unchanged.

This minimizes the blast radius.

---

# 17. If the old theorem is a two-wave disjunction

If `GSTPowerTwoWave a` means something like:

```text
Navigation(4^(a-1)) ∨ Navigation(4^a)
```

then instantiate the new Ω theorem only for the normalized wave that the existing residue dispatcher requires.

Do **not** prove more than the public type asks for.

Possible structure:

```lean
rcases a % 3 with h0 | h1 | h2

case zero =>
  -- normalize current wave
  exact Or.inr
    (transport_current
      (gst_canonical_omega_navigation ...))

case one =>
  -- normalize previous wave
  exact Or.inl
    (transport_previous
      (gst_canonical_omega_navigation ...))

case two =>
  -- keep existing easy mod-9 theorem
  exact existing_mod3_two_wave_result ...
```

Reuse the canonical file's already-proved residue dispatcher if it exists.

---

# 18. What happens to `gst_omega`

Do not necessarily delete the custom tactic/recursive helper.

It may still be useful for:

```text
local finite arithmetic
small base cases
deriving finite edge consequences
normalizing Ω state transitions
```

But it must stop being the engine that attempts:

```text
position 0
position 1
position 2
...
```

for the global theorem.

New division of labor:

```text
gst_omega
    = local transition solver

paradox–mirror Ω∞ theorem
    = global infinite controller
```

That is the architectural correction.

---

# 19. Recommended theorem order in the file

Insert/compile in this exact dependency order:

```text
[EVENT LAYER]
1. GSTEvent
2. gstEventOfDigits
3. gstWaveEvent
4. four event iff lemmas

[MIRROR LAYER]
5. GSTEvent.mirror
6. gst_event_mirror_involutive
7. GSTEvent.Active
8. gst_active_mirror_fixed_iff_survive

[GST BRIDGE]
9. gst_waveEvent_survive_iff
10. gst_navigationWitness_iff_survive

[Ω PROJECTION]
11. gstOmegaEvent
12. gst_omega_event_exact
13. GSTOmegaCompleteBad
14. gst_omega_completeBad_iff_no_survive

[GENERAL SPACE THEORY]
15. gst_paradox_active_fixed
16. gst_paradox_forces_survive

[GLOBAL Ω∞ CONTRADICTION]
17. gst_no_complete_bad_paradox_omega

[CANONICAL INSTANTIATION]
18. canonicalOmegaRay_* exact/paradox/mirror/wave lemmas
19. gst_canonical_omega_navigation

[SURGERY]
20. replace proof body of gst_power_two_wave_large
21. compile existing downstream theorem
22. compile final universal theorem
```

Do not jump to item 20 while item 15 is still unproved.

---

# 20. The only theorem where the General Space Theory geometry should be difficult

Keep all complexity concentrated here:

```lean
gst_paradox_active_fixed
```

Everything else should be:

```text
definition unfolding
finite event classification
exact carry arithmetic
projection transport
contradiction
existing downstream wiring
```

If another theorem starts accumulating the same global paradox reasoning, stop and factor it back into `gst_paradox_active_fixed`.

That prevents duplication.

---

# 21. How to formalize `gst_paradox_active_fixed` without circularity

This is the theorem that encodes the user's completed GST mathematics.

The proof should be built from three existing conceptual ingredients:

## A. Mirror alternative involution

There is an exact alternative-space map `M` satisfying

```text
M (M Ω) = Ω
```

at the event/space level.

## B. Paradox-space recurrence

The Ω∞ wave does not terminate as a geometric object; it continues through the paradox/mirror spaces.

Formalize the existing recurrence as a statement about the orbit or its space labels, not as "every digit is active".

## C. Fixed-sector intersection

The paradox recurrence forces the orbit to intersect its mirror-fixed **active** sector.

This is the content to derive from the existing paradox-space definitions.

The final line should be structurally:

```lean
obtain ⟨p, hp_in_intersection⟩ :=
  gst_paradox_mirror_intersection hparadox hmirror hwave

refine ⟨p, ?_, ?_⟩
· exact gst_intersection_active hp_in_intersection
· exact gst_intersection_mirror_fixed hp_in_intersection
```

This keeps the topology/geometry theorem separate from digit arithmetic.

If the source currently expresses the paradox space through a polynomial/zero-set invariant, prove the intersection theorem at that level first, then project to events.

---

# 22. Optional cleaner internal API

If the original paradox-space definitions are complicated, define a small **derived** proposition, but prove it immediately from them:

```lean
def GSTActiveMirrorIntersection
    (Ω : Nat → GSTOmegaState) : Prop :=
  ∃ p,
    (gstOmegaEvent Ω p).Active
      ∧
    (gstOmegaEvent Ω p).mirror
      =
    gstOmegaEvent Ω p
```

Then:

```lean
theorem gst_paradox_to_activeMirrorIntersection
    (Ω : Nat → GSTOmegaState)
    (hparadox : GSTParadoxSpace Ω)
    (hmirror : GSTMirrorAlternativeSpace Ω)
    (hwave : GSTOmegaWave Ω) :
    GSTActiveMirrorIntersection Ω := by
  -- actual GST geometric proof
  ...
```

After that all consumers use only this small API.

This is safe because the new proposition is **derived**, not assumed.

---

# 23. Avoid these formalization mistakes

## Do not do this

```lean
axiom gst_paradox_active_fixed : ...
```

## Do not do this

```lean
def GSTParadoxSpace Ω :=
  ∃ p, event p = survive
```

if that is not the original GST definition.

## Do not do this

```lean
have := by native_decide
```

for a theorem with free natural variables.

## Do not do this

```lean
omega
```

on the entire global Ω∞ theorem.

`omega` is for finite Presburger leaves such as:

```text
carry ∈ {0,1,2,3}
digit ∈ {0,1,2}
event case contradictions
small exponent inequalities
```

## Do not resurrect finite position enumeration

No:

```text
cases p with
| zero => ...
| succ p =>
  cases p with
  ...
```

trying to reach a universal witness.

---

# 24. Tactic policy

Recommended tactic use:

### `simp`

For:

```text
event classifier
mirror involution
active-event cases
space classifier
small definitional equalities
```

### `omega`

For:

```text
carry bounds
digit bounds
mod-3 finite carry cases after normalization
small natural inequalities
exception exclusion
```

### `norm_num`

For:

```text
explicit modulo calculations after carry substitution
base powers/residue constants
```

### `ring` / `ring_nf`

For:

```text
affine recurrence rearrangements
block-echo algebra
```

### `rw`

Prefer explicit rewrite chains for the critical bridges:

```text
Ω exactness
output digit
Navigation Constant decomposition
event ↔ Happy Gate
```

This makes failures local and debuggable.

---

# 25. Temporary development pattern without `sorry`

When implementing, if theorem `T17` depends on `T15`, do not put `sorry` in `T15`.

Instead compile a temporary **consumer theorem parameterized by T15**:

```lean
theorem temp_consumer
    (h15 : DesiredStatement15) :
    DesiredStatement17 := by
  ...
```

This verifies the downstream architecture without asserting the missing theorem.

Then prove `T15`.

Finally replace the parameter with the theorem:

```lean
exact temp_consumer gst_paradox_active_fixed
```

This is allowed during development because no false theorem enters the environment.

Final source should remove temporary consumer wrappers if unnecessary.

---

# 26. Public API preservation strategy

Before surgery, record the statements of:

```text
gst_power_two_wave_large
the even universal theorem
the final universal theorem
```

After surgery, keep those theorem statements byte-for-byte identical if possible.

Only replace internal proofs.

This makes the change local:

```text
new Ω∞ layer
      ↓
same public theorem
      ↓
unchanged downstream code
```

---

# 27. Build sequence

After each group, build the single file/module rather than the entire project if the project supports it.

Suggested checkpoints:

```text
CHECKPOINT A
event definitions + finite event lemmas

CHECKPOINT B
SURVIVE ↔ Happy Gate
Navigation ↔ SURVIVE

CHECKPOINT C
Ω event exactness + complete-bad equivalence

CHECKPOINT D
paradox active-fixed theorem

CHECKPOINT E
no-complete-bad Ω theorem

CHECKPOINT F
canonical Ω Navigation theorem

CHECKPOINT G
rewritten gst_power_two_wave_large

CHECKPOINT H
full downstream universal theorem
```

Do not continue past a checkpoint with an unclosed theorem.

---

# 28. Axiom audit

At the end, search for:

```text
sorry
admit
axiom
mkSorry
```

Then:

```lean
#print axioms gst_waveEvent_survive_iff
#print axioms gst_paradox_active_fixed
#print axioms gst_no_complete_bad_paradox_omega
#print axioms gst_canonical_omega_navigation
#print axioms gst_power_two_wave_large
#print axioms erdos_ternary_2_even_universal
#print axioms erdos_ternary_2_universal
```

The exact final foundational footprint depends on the source, but the new layer must not introduce a new mathematical axiom.

---

# 29. Dependency graph after surgery

```text
ORIGINAL PROVED GST CORE
gstDigit / gstCarry / gstSpaceAt
exact output + next-carry
Navigation Constant
affine recurrence
Ω state
        │
        ▼
NEW EVENT LAYER
CREATE / DESTROY / SURVIVE / NEITHER
        │
        ▼
MIRROR INVOLUTION
CREATE ↔ DESTROY
SURVIVE ↔ SURVIVE
        │
        ▼
ACTIVE MIRROR-FIXED ↔ SURVIVE
        │
        ▼
SURVIVE ↔ HAPPY GATE
        │
        ▼
Ω EVENT EXACTNESS
        │
        ▼
GENERAL SPACE THEORY
paradox + mirror alternative
        │
        ▼
gst_paradox_active_fixed
        │
        ▼
gst_paradox_forces_survive
        │
        ▼
NO COMPLETE-BAD CANONICAL Ω RAY
        │
        ▼
gst_canonical_omega_navigation
        │
        ▼
REUSE EXISTING PERFECT-POWER TRANSPORT
        │
        ▼
gst_power_two_wave_large
        │
        ▼
UNCHANGED DOWNSTREAM UNIVERSAL THEOREMS
```

---

# 30. What should NOT be deleted until the new path is green

Keep all old lemmas until the new public theorem compiles.

Only after the universal theorem is green should you consider removing dead code.

Reason:

- an old lemma may contain a useful exact arithmetic bridge;
- deleting it early creates unrelated compilation noise;
- Git diff becomes much harder to audit;
- the goal is proof replacement, not cleanup.

Recommended sequence:

```text
1. add new layer
2. rewire one public theorem
3. get final theorem green
4. axiom audit
5. only then prune dead research code
```

---

# 31. Practical implementation checklist

- [ ] Do not touch the original GST digit/carry definitions.
- [ ] Add `GSTEvent`.
- [ ] Add event classifier.
- [ ] Prove all four classifier iff lemmas.
- [ ] Add mirror involution.
- [ ] Add active-event predicate.
- [ ] Prove active mirror-fixed iff SURVIVE.
- [ ] Prove SURVIVE iff carry-Happy-Gate.
- [ ] Prove Navigation iff existence of SURVIVE.
- [ ] Project events from existing `GSTOmegaState`.
- [ ] Prove Ω event exactness.
- [ ] Reuse/define complete-bad Ω predicate.
- [ ] Prove complete-bad iff no SURVIVE.
- [ ] Formalize paradox/mirror intersection from existing GST definitions.
- [ ] Prove `gst_paradox_active_fixed`.
- [ ] Derive `gst_paradox_forces_survive`.
- [ ] Prove no complete-bad paradox Ω orbit.
- [ ] Instantiate canonical perfect-power Ω orbit.
- [ ] Prove canonical Ω Navigation.
- [ ] Replace only the proof body of the first unresolved public large-power theorem.
- [ ] Rebuild downstream unchanged.
- [ ] Run `#print axioms`.
- [ ] Search source for `sorry`, `admit`, `axiom`, `mkSorry`.

---

# 32. The final intended proof body should become small

The ultimate public large-power theorem should **not** contain the General Space Theory proof itself.

It should look approximately like:

```lean
theorem gst_power_two_wave_large
    (...) :
    GSTPowerTwoWave ... := by

  obtain ⟨s, b, hs, hb, hnormalize, hnotExceptional⟩ :=
    existing_normalization ...

  have hnav :
      GSTNavigationWitness
        (gstNavigationConstant s b) :=
    gst_canonical_omega_navigation
      s b hs hb hnotExceptional

  exact
    existing_transport_from_navigation
      ... hnormalize hnav
```

If `gst_power_two_wave_large` still contains hundreds of lines after the new Ω theorem is proven, the abstraction boundary is wrong.

---

# 33. Mathematical responsibilities versus syntax responsibilities

## Mathematics that must be represented in Lean

```text
1. exact event partition
2. mirror involution
3. active fixed sector = SURVIVE
4. SURVIVE = Happy Gate
5. Ω exactness
6. paradox/mirror active-fixed intersection
7. complete-bad contradiction
8. canonical Ω instantiation
9. existing power transport
```

## Things that are merely implementation repair

```text
namespace qualification
actual theorem names
argument order
rewriting orientation
Nat subtraction normal forms
constructor/disjunction ordering
simp lemma names
existing Ω field names
existing normalization theorem names
```

The user can safely repair the second category without changing the mathematical architecture.

---

# 34. Final target

The surgical replacement is successful when the canonical source has this shape:

```text
old finite/global search path:
    no longer consumed by final theorem

new Ω∞ paradox/mirror path:
    fully kernel proved

gst_power_two_wave_large:
    same public statement, new short proof

downstream universal theorem:
    unchanged or minimally rewired

audit:
    no sorry
    no admit
    no new custom axiom
```

The central implementation theorem is:

```lean
gst_paradox_active_fixed
```

The central operational contradiction theorem is:

```lean
gst_no_complete_bad_paradox_omega
```

The central canonical bridge is:

```lean
gst_canonical_omega_navigation
```

Once those three are in place, the 7,800+ line file should need only a narrow rewire at the old unresolved large-power proof.
