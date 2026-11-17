# DISCOVERY — Task 2-e: the quarantined universal induction (ErdosTernary2.lean)

All line numbers refer to `/home/z/agent-work/src/ErdosTernary2.lean` (17,042 lines) unless a
different file is named. Everything below is VERBATIM from the source.

---

## 1. `gst_duality` — the carry-wave theorem (L3891–3901)

```lean
/-- Full GST Duality: the carry wave theorem (Infinite Paradox). -/
theorem gst_duality (R : Nat) (hR_mod3 : R % 3 = 1) (hR_has : hasTernaryTwo R = true)
    (h_creation : ∃ p : Nat, 1 ≤ p ∧ R / 3^p % 3 = 2 ∧
      ((4 * (R % 3^p)) / 3^p % 3 = 0 ∨
       ((4 * (R % 3^p)) / 3^p % 3 = 1 ∧ R / 3^(p+1) % 3 = 2))) :
    hasTernaryTwo (4 * R) = true
```

`h_creation` is NOT a definition — it is the name of the *hypothesis shape* above
(digit-two at p ≥ 1, plus carry 0, or carry 1 with next digit 2). This shape is
the "creation certificate". There is no `def h_creation` / `structure h_creation` anywhere
(grep over the whole `src/` confirms: only hypothesis binders, plus the theorems
`h_creation_4pow_survive`, `h_creation_cascade_lift`, `cubic_h_creation_lift`,
`hCreationCheck_univ`, `gst_hCreation_exists_iff_pure`).

## 2. `h_creation_4pow_survive` — SURVIVE case for R = 4^k (L3907–3914)

```lean
/-- h_creation for R = 4^k when v3(k) ≥ 1 (so v = 1+v3(k) ≥ 2) and b%3 = 2.
    p = v, R/3^v % 3 = 2 (Q%3 = b%3 = 2), carry = 0 (since 4 < 3^v for v≥2).
    This is the SURVIVE case of h_creation. -/
theorem h_creation_4pow_survive (k : Nat) (hk5 : 5 ≤ k)
    (hv3k : 1 ≤ v3 k) (hb3 : (k / 3^(v3 k)) % 3 = 2) :
    ∃ p : Nat, 1 ≤ p ∧ (4^k) / 3^p % 3 = 2 ∧
      ((4 * ((4^k) % 3^p)) / 3^p % 3 = 0 ∨
       ((4 * ((4^k) % 3^p)) / 3^p % 3 = 1 ∧ (4^k) / 3^(p+1) % 3 = 2))
```

Proof uses `cascade_universal` (L473): `4^(3^s·b) ≡ 1 mod 3^(s+1)` and digit at row
`s+1` = `b % 3`. Covers every k whose lowest nonzero ternary trit is 2 at position ≥ 1
(the `2·3^s` tower: k ≡ 6 mod 9, 18 mod 27, 54 mod 81, 162 mod 243, …).

## 3. `gst_hCreation_exists_iff_pure` — certificate ⟺ pure/happy form (L4930–4934)

```lean
theorem gst_hCreation_exists_iff_pure (R : Nat) :
    (∃ p, 1 ≤ p ∧ gstDigit R p = 2 ∧
      (gstCarry R p % 3 = 0 ∨
       (gstCarry R p % 3 = 1 ∧ gstDigit R (p + 1) = 2))) ↔
    ∃ q, 1 ≤ q ∧ gstDigit R q = 2 ∧ gstCarry R q % 3 = 0
```

(The create-branch is converted using `carry_reset_after_d2`, L4315:
carry ∈ {1,2} ∧ digit 2 → carry at p+1 = 3, so the pure witness sits at p+1 with carry 3.)

Supporting coordinate definitions (L4778, L4781):

```lean
def gstCarry (R p : Nat) : Nat := (4 * (R % 3^p)) / 3^p
def gstDigit (R p : Nat) : Nat := R / 3^p % 3
```

## 4. `gst_pure_lift_or_forced_cascade` — the ×4 two-wave surgical lift (L4947–4959)

```lean
/-- TWO-WAVE SURGICAL LIFT.  A Happy-Gate digit-two of `R` remains a
    digit-two after multiplication by four.  In the new wave it either is
    already in GST+/NULL, or it lies in ALT- with carry one/two and therefore
    resets to GST+ on the next forward edge.  This is the exact local bridge
    needed before the perfect-power origin rules out an infinite bad trace. -/
theorem gst_pure_lift_or_forced_cascade (R p : Nat) (hp : 1 ≤ p)
    (hd : gstDigit R p = 2)
    (hgood : gstCarry R p = 0 ∨ gstCarry R p = 3) :
    (gstDigit (4 * R) p = 2 ∧
        (gstCarry (4 * R) p = 0 ∨ gstCarry (4 * R) p = 3)) ∨
      (gstDigit (4 * R) p = 2 ∧
        (gstCarry (4 * R) p = 1 ∨ gstCarry (4 * R) p = 2) ∧
        gstCarry (4 * R) (p + 1) = 3)
```

## 5. The step/carry tables — the kernel-checked Φ graph law (L4883–4890, 4980–4995)

```lean
/-- The exact arithmetic carried by one forward GST edge. -/
def gstStepCarry (C d : Nat) : Nat := (C + 4 * d) / 3

/-- Output digit on the same edge. -/
def gstOutputDigit (C d : Nat) : Nat := (C + 4 * d) % 3

/-- The full local edge label `(output digit, next carry)`. -/
def gstStep (C d : Nat) : Nat × Nat :=
  (gstOutputDigit C d, gstStepCarry C d)

theorem gstStepCarry_table :
    gstStepCarry 0 0 = 0 ∧ gstStepCarry 0 1 = 1 ∧ gstStepCarry 0 2 = 2 ∧
    gstStepCarry 1 0 = 0 ∧ gstStepCarry 1 1 = 1 ∧ gstStepCarry 1 2 = 3 ∧
    gstStepCarry 2 0 = 0 ∧ gstStepCarry 2 1 = 2 ∧ gstStepCarry 2 2 = 3 ∧
    gstStepCarry 3 0 = 1 ∧ gstStepCarry 3 1 = 2 ∧ gstStepCarry 3 2 = 3 := by
  decide

/-- Complete edge table `(digit of 4R, carry at p+1)`. -/
theorem gstStep_table :
    gstStep 0 0 = (0, 0) ∧ gstStep 0 1 = (1, 1) ∧ gstStep 0 2 = (2, 2) ∧
    gstStep 1 0 = (1, 0) ∧ gstStep 1 1 = (2, 1) ∧ gstStep 1 2 = (0, 3) ∧
    gstStep 2 0 = (2, 0) ∧ gstStep 2 1 = (0, 2) ∧ gstStep 2 2 = (1, 3) ∧
    gstStep 3 0 = (0, 1) ∧ gstStep 3 1 = (1, 2) ∧ gstStep 3 2 = (2, 3) := by
  decide
```

Φ recurrence wrappers (verified, sound):

```lean
theorem gstCarry_forward_exact (R p : Nat) (hp : 1 ≤ p) :
    gstCarry R (p + 1) = gstStepCarry (gstCarry R p) (gstDigit R p)

theorem gstOutputDigit_forward_exact (R p : Nat) (hp : 1 ≤ p) :
    (4 * R) / 3^p % 3 = gstOutputDigit (gstCarry R p) (gstDigit R p)

theorem gstCarry_lt_four (R p : Nat) (hp : 1 ≤ p) : gstCarry R p < 4
```

Key table facts used by the plan: `gstStepCarry 3 2 = 3` (carry 3 is the STABLE happy
state through a digit-two), `gstStepCarry 0 2 = 2` (carry 0 DEGRADES to ALT- through a
digit-two, then `gstStepCarry 2 2 = 3` resets one row up), `gstStepCarry 1 0 = 0` and
`gstStepCarry 2 0 = 0` (a zero digit exits ALT-).

## 6. `gst_affine_mul_digit_exact` — the Φ carry recurrence, exact (L6821–6836)

```lean
theorem gst_affine_mul_digit_exact (A z T j : Nat) :
    gstDigit (z + A*T) j =
      (gstAffineMulCarry A z T j + A * gstDigit T j) % 3
```

with (L6803–6804) `def gstAffineMulCarry (A z T j : Nat) : Nat := (z + A * (T % 3^j)) / 3^j`,
and the Φ design comment (L4088–4097):

```
--  Φ(R, p) = (d_p + C(R, p)) % 3 — The Carry Recurrence Digit Function.
--  This is the TRUE universal equation — 100% accurate for ALL R, ALL p.
--  0 failures in 200,000 tests. This is NOT a theorem — it's the DEFINITION
--  of how multiplication by 4 works in base 3.
--    C(R, 0) = 0
--    C(R, p+1) = floor((4·d_p + C(R, p)) / 3)
--    Φ(R, p) = (d_p + C(R, p)) % 3 = digit of 4*R at position p
```

## 7. `gst_seeded_happy_iff_common_twoS` — seed-zero happy gate ⟺ CommonTwo (L12213–12221)

```lean
/-- A seeded Happy Gate is exactly a common ternary digit two between the input
    word H and its microscopic output word seed+4H. -/
theorem gst_seeded_happy_iff_common_twoS
    (seed H q : Nat)
    (hseed : seed < 4) :
    (gstDigitS H q = 2 ∧
      (gstAffineMulCarryS 4 seed H q = 0 ∨
       gstAffineMulCarryS 4 seed H q = 3)) ↔
    (gstDigitS H q = 2 ∧ gstDigitS (seed + 4*H) q = 2)
```

With `seed = 0`, `H = 4^K`: `seed + 4*H = 4^(K+1)` and
`gstAffineMulCarryS 4 0 H q = (0 + 4*(H % 3^q))/3^q = gstCarry H q` (definitional).
S-language coordinates (L9029–9035) are the same bodies as the un-suffixed ones:

```lean
def gstCarryS (R p : Nat) : Nat := (4 * (R % 3^p)) / 3^p
def gstDigitS (R p : Nat) : Nat := R / 3^p % 3
def gstAffineMulCarryS (A z T p : Nat) : Nat := ...
```

and the target file's `digit3` (GSTFourPowerDirectResidue.lean L9):
`def digit3 (R p : Nat) : Nat := R / 3^p % 3` — all definitional copies of `gstDigit`.

## 8. The navigation-witness bridge and the escape (L16897–16937; GSTPrefixOneOntologicalEscape.lean L93–104)

```lean
/-- Convert the standalone exact Happy-gate language into the monolith wrapper. -/
theorem gst_navigation_witness_of_standalone_navigation
    (R : Nat) (h : GSTCanonicalTailStateIso.Navigation R) :
    GSTNavigationWitness R

/-- Monolith-facing POE.  No child premise occurs; the one upstream input is
    exactly the independent four-power creation master isolated by the new DAG. -/
theorem gst_prefix_one_ontological_escape_of_master_inline
    (hMaster : GSTFourPowerOntologicalAdapter.FourPowerCreationMaster)
    (s n : Nat) (hs : 1 ≤ s) (hn : 1 ≤ n) :
    GSTNavigationWitness (gstNavigationConstant s (1 + 3*n))

/-- The independently kernel-checked width-three wave supplies the exact
    four-power creation master required by the ontological prefix-one adapter. -/
theorem gst_four_power_creation_master_inline :
    GSTFourPowerOntologicalAdapter.FourPowerCreationMaster := by
  intro K hK5 hK7
  simpa [GSTFourPowerOntologicalAdapter.CreationCertificate] using
    (gst_four_power_creation_certificate_inline K hK5 hK7)
```

Definitions (L5114–5122):

```lean
def gstNavigationConstant (s b : Nat) : Nat :=
  4^(3^s * b) / 3^(s+1)

def GSTNavigationWitness (R : Nat) : Prop :=
  ∃ j, gstDigit R j = 2 ∧
    (gstSpaceAt R j = .gstPlus ∨ gstSpaceAt R j = .null)
```

⚠ THE CIRCLE: `gst_four_power_creation_master_inline` is fed by
`gst_four_power_creation_certificate_inline`, which in the ACTIVE file
GSTPrefixOneOntologicalEscape.lean (L93–104) is a compatibility wrapper around the
AXIOM `gst_four_power_direct_existence_inline : GSTFourPowerDirectExistence.FourPowerDirectExistence`
via `GSTFourPowerDirectCreationMaster.directExistence_to_creation_master`. So the
navigation-witness route CANNOT be used to kill the axiom — it is downstream of it.

## 9. The h_creation-adjacent verified theorems

### `hCreationCheck_univ` — the finite base (L4099–4109, ACTIVE, kernel-checked)

```lean
/-- Universal h_creation check for k ∈ [5, 500] \ {7}.
    Proven by decide on bounded universal ∀ k < 501.
    This is the FINITE BASE CASE for the strong induction (not an hcase —
    the theorem is universal via the inductive step for k > 500). -/
theorem hCreationCheck_univ :
    ∀ k < 501, 5 ≤ k → k = 7 ∨
      ∃ p < 50, 1 ≤ p ∧
        (powMod 4 k (3^(p+1))) / 3^p % 3 = 2 ∧
        ((4 * (powMod 4 k (3^p))) / 3^p % 3 = 0 ∨
         ((4 * (powMod 4 k (3^p))) / 3^p % 3 = 1 ∧
          (powMod 4 k (3^(p+2))) / 3^(p+1) % 3 = 2)) := by decide
```

(`decide` on `∀ k < 501` — exactly at the permitted boundary N = 501; all arguments
are bounded by `3^52` since p < 50; this theorem is OUTSIDE the quarantine and
already compiles in the monolith.)

### `cubic_h_creation_lift` — the verified cube engine (L2439–2444)

```lean
theorem cubic_h_creation_lift (m p : Nat) (hp1 : 1 ≤ p)
    (hp_d2 : (4^m) / 3^p % 3 = 2)
    (hmod : (4^m) % 3^p = 1) :
    ∃ q : Nat, 1 ≤ q ∧ ((4^m)^3) / 3^q % 3 = 2 ∧
      ((4 * (((4^m)^3) % 3^q)) / 3^q % 3 = 0 ∨
       ((4 * (((4^m)^3) % 3^q)) / 3^q % 3 = 1 ∧ ((4^m)^3) / 3^(q+1) % 3 = 2))
```

Produces the SURVIVE witness (carry 0) at row `q = p+1` from a *seeded* witness:
`d_p(4^m) = 2` AND `4^m ≡ 1 mod 3^p`. Proof: `(4^m)^3 ≡ 1 + 2·3^(p+1) (mod 3^(p+2))`
(`digit_two_cubic_shift`). The `≡ 1 mod 3^p` side condition holds exactly when
`3^(p-1) ∣ m` (order of 4 mod 3^p is 3^(p-1)); i.e. this lifts the survive tower
`m ≡ 2·3^(p-1) → 3m ≡ 2·3^p`.

### `h_creation_cascade_lift` — ⚠ VACUOUS (L6372–6381, ACTIVE but dead)

```lean
theorem h_creation_cascade_lift (k s m : Nat) (hs : 2 ≤ s)
    (hk : k = 3^s * (1 + 3*m))
    (p : Nat) (hp1 : 1 ≤ p) (hp_le : p ≤ s - 1)
    (hd2 : (4^(3^(s+1)*m)) / 3^p % 3 = 2)
    (hcarry : (4 * ((4^(3^(s+1)*m)) % 3^p)) / 3^p % 3 = 0 ∨
             ((4 * ((4^(3^(s+1)*m)) % 3^p)) / 3^p % 3 = 1 ∧
              (4^(3^(s+1)*m)) / 3^(p+1) % 3 = 2)) :
    (4^k) / 3^p % 3 = 2 ∧
    ((4 * ((4^k) % 3^p)) / 3^p % 3 = 0 ∨
     ((4 * ((4^k) % 3^p)) / 3^p % 3 = 1 ∧ (4^k) / 3^(p+1) % 3 = 2))
```

⚠ **DISCOVERY (new, this slice): this theorem can never fire.** Its hypothesis needs
`d_p(4^(3^(s+1)·m)) = 2` at a row `p ≤ s-1`. But `3^(s+1)·m` (m ≥ 1) has
`v3 ≥ s+1`, so by `cascade_universal` `4^(3^(s+1)·m) ≡ 1 (mod 3^(s+2))`: every digit
at rows 1..s+1 is **0**, in particular at rows p ≤ s-1. For m = 0 the sub-power is
`4^0 = 1` with the same all-zero tail. The hypothesis is unsatisfiable; the theorem is
vacuously true and useless as a descent engine. (The quarantined plan's "cascade
structure" descent cannot be built on it.)

### Other verified step ingredients

```lean
theorem carry_reset_after_d2 (R p : Nat) (hp : 1 ≤ p)
    (h_carry : (4 * (R % 3^p)) / 3^p = 1 ∨ (4 * (R % 3^p)) / 3^p = 2)
    (h_d2 : R / 3^p % 3 = 2) :
    (4 * (R % 3^(p+1))) / 3^(p+1) = 3            -- L4315

theorem carry_bound (R p : Nat) (hp : 1 ≤ p) :
    (4 * (R % 3^p)) / 3^p < 4                      -- L4325

theorem highest_d2_carry (R h : Nat) (hh : 1 ≤ h)
    (h_d2 : R / 3^h % 3 = 2) :
    (4 * (R % 3^(h+1))) / 3^(h+1) = 2 ∨
    (4 * (R % 3^(h+1))) / 3^(h+1) = 3              -- L4338

theorem bridge_carry_zero (k : Nat) (hk : 2 ≤ k) :
    (4 * ((4^k) % 3^(2*k))) / 3^(2*k) = 0          -- L4359

theorem bridge_forces_non_one (R : Nat) (p N : Nat) (hp : 1 ≤ p) (hN : p < N)
    (h_state3 : (4 * (R % 3^p)) / 3^p = 3)
    (h_bridge : (4 * (R % 3^N)) / 3^N = 0) :
    ∃ j, p ≤ j ∧ j < N ∧ R / 3^j % 3 ≠ 1           -- L4513

theorem carry_state_after_zero (R p : Nat) (hp : 1 ≤ p)
    (h_c1 : (4 * (R % 3^p)) / 3^p = 1 ∨ (4 * (R % 3^p)) / 3^p = 2 ∨ (4 * (R % 3^p)) / 3^p = 3)
    (h_digit : R / 3^p % 3 = 0) :
    (4 * (R % 3^(p+1))) / 3^(p+1) = 0 ∨ (4 * (R % 3^(p+1))) / 3^(p+1) = 1   -- L4532

theorem hasTernaryTwo_first_pos (n : Nat) (h : hasTernaryTwo n = true) :
    ∃ q : Nat, n / 3^q % 3 = 2 ∧ ∀ p, p < q → n / 3^p % 3 ≠ 2   -- L4120

theorem first_d2_carry_ne_2 (n q : Nat)
    (h_qfirst : ∀ p, p < q → n / 3^p % 3 ≠ 2)
    (_h_d2 : n / 3^q % 3 = 2)
    (h_d0 : n % 3 ≤ 1) :
    (4 * (n % 3^q)) / 3^q % 3 ≠ 2                   -- L4219

theorem find_highest_d2 : ∀ (N R : Nat), 2 ≤ N → R < 3^N → R % 3 ≠ 2 → hasTernaryTwo R = true →
    ∃ h, 1 ≤ h ∧ h < N ∧ R / 3^h % 3 = 2            -- L4624
```

## 10. THE FULL QUARANTINED PLAN TEXT (L6420–6775)

```
/- BEGIN QUARANTINED LEGACY UNIVERSAL CHAIN
   This block still calls the removed false generic oscillation theorem through
   a sound adapter that now requires the missing power-specific Navigation
   witness.  It is not imported by the configured comparator (`Solution.lean`),
   and keeping it active makes the GST graph module fail before its independent
   declarations can be checked.  Preserve it here for proof archaeology until
   the origin-restricted bad-trace theorem supplies that witness. -/
/-
/-- For R = 4^k, the h_creation witness EXISTS.
    Proven by strong induction on k:
    - Base k ≤ 500: decide on bounded universal (finite check).
    - Inductive k > 500: ih(k-1) + gst_duality + Φ (carry recurrence).
    The carry recurrence Φ(R, p) = (d_p + C(R, p)) % 3 GUARANTEES
    the witness exists — 0 failures in 200,000 tests. -/
theorem gst_four_power_creation_certificate_inline (k : Nat) (hk5 : 5 ≤ k) (hk7 : k ≠ 7) :
    ∃ p : Nat, 1 ≤ p ∧ (4^k) / 3^p % 3 = 2 ∧
      ((4 * ((4^k) % 3^p)) / 3^p % 3 = 0 ∨
       ((4 * ((4^k) % 3^p)) / 3^p % 3 = 1 ∧ (4^k) / 3^(p+1) % 3 = 2)) := by
  by_cases hk500 : k ≤ 500
  · -- BASE CASE: k ≤ 500. Use hCreationCheck_univ (decide-proven).
    [powMod_eq + digit_identity conversion; sound, reusable — see PLAN §B]
  · -- INDUCTIVE CASE: k > 500.
    -- GST Oscillation Module: use hasTernaryTwo_first_pos + first_d2_carry_ne_2.
    [ih(k-1); 4^k = 4 * 4^(k-1); gst_duality (4^(k-1)) → hasTernaryTwo (4^k);
     hasTernaryTwo_first_pos → first d2 q, 1 ≤ q;
     first_d2_carry_ne_2 → C(q) ≠ 2;
     C(q)%3 = 0 → SURVIVE at q;
     C(q)%3 = 1 ∧ d_{q+1} = 2 → CREATE at q;
     else CASCADE: C(q) = 1, d_{q+1} ≠ 2, C(q+1) = 3 (carry_reset_after_d2);
       d_{q+1} = 2 → SURVIVE at q+1;
       else: highest-d2 analysis (find_highest_d2, highest_d2_carry):
         C(h+1) = 2 → C(h) = 0 → SURVIVE at h;
         C(h+1) = 3, C(h)%3 = 0 → SURVIVE at h;
         C(h+1) = 3, C(h) ∈ {1,2} → THE FALSE CALL:
           gst_oscillation_from_navigation (4^k) (2*k) h_bridge h4k_lt_3_2k h4k_mod3
             q hq_pos hq_lt_2k hqC_lt h_has hq_d2        ← missing hnav witness]
```

The archaeology comments inside the block (L6527–6614) correctly diagnose the last
sub-case: *the witness exists iff a 0 digit occurs between the first d2 q and the
highest d2 h; the bridge's 0 (from C(2k)=0) may lie AFTER the last d2 and then does
not help. "This is the GST oscillation — the coupling between GST+ and ALT-."*

### The removed FALSE theorem (L6177–6192, now a sound pass-through adapter)

```lean
/-- A sound interface for the GST oscillation step.  The former theorem at
    this location tried to derive a pure witness for an arbitrary `R`; that
    statement is false (for example `R = 7`, `N = 4`, `start = 1`).  The
    power-specific Navigation theorem must provide the witness explicitly. -/
theorem gst_oscillation_from_navigation (R : Nat) (N : Nat)
    (h_bridge : (4 * (R % 3^N)) / 3^N = 0)
    (hR_lt : R < 3^N) (hR_mod3 : R % 3 ≠ 2)
    (start : Nat) (hstart_pos : 1 ≤ start) (hstart_lt : start < N)
    (hC_lt : (4 * (R % 3^start)) / 3^start < 4)
    (h_has : hasTernaryTwo R = true)
    (hd_start : R / 3^start % 3 = 2)
    (hnav : ∃ p, 1 ≤ p ∧ p < N ∧ R / 3^p % 3 = 2 ∧
        (4 * (R % 3^p)) / 3^p % 3 = 0) :
    ∃ p, 1 ≤ p ∧ p < N ∧ R / 3^p % 3 = 2 ∧
        (4 * (R % 3^p)) / 3^p % 3 = 0 := by
  exact hnav
```

What was FALSE: the pre-adapter generic recursion ("`gst_oscillation_unified`",
retained as a comment at L6193–6269) claimed that for ANY R with a d2, a bridge carry
0 at N, and a starting d2 in ALT-, the carry state machine eventually produces a d2
with carry ≡ 0 mod 3. Counterexample recorded in the docstring: R = 7 (ternary `21`),
N = 4, start = 1 — the highest (and only high) d2 sits in ALT- and the zeros above it
bring the carry down only AFTER the last d2, so no witness exists. In the power
family the exact same digit configuration occurs at **K = 7**: 4^7 = 16384 =
`1 1 2 0 1 1 1 1 2`₃ (rows 0→8), d2s at rows 2 and 8, C(2) = 1, C(8) = 1 (ALT-),
all rows above are 0 — which is precisely why 7 is the unique excluded exponent of
the target statement. The false theorem asserted, for arbitrary R, exactly the
property that distinguishes 4^7 from all other 4^K.

## 11. Target and row theorems (GSTFourPowerDirectExistence.lean, verbatim)

```lean
def CommonTwo (K : Nat) : Prop :=
  ∃ p : Nat, 1 ≤ p ∧
    digit3 (4^K) p = 2 ∧
    digit3 (4^(K+1)) p = 2

def FourPowerDirectExistence : Prop :=
  ∀ K : Nat, 5 ≤ K → K ≠ 7 → CommonTwo K

theorem commonTwo_of_mod9_five_or_six
    (K : Nat) (hres : K % 9 = 5 ∨ K % 9 = 6) :
    CommonTwo K

theorem commonTwo_of_mod27_row_three
    (K : Nat)
    (hres : K % 27 = 14 ∨ K % 27 = 18 ∨ K % 27 = 19 ∨ K % 27 = 25) :
    CommonTwo K

theorem commonTwo_of_mod81_row_four
    (K : Nat) (hres : RowFourClass (K % 81)) :
    CommonTwo K
```

The axiom to kill (GSTPrefixOneOntologicalEscape.lean L90–94):

```lean
/-- Explicit production boundary for the still-open direct universal existence
    law.  Kept out of the obsolete infinite-navigation provider so the committed
    production closure can build and the comparator can certify the current seam. -/
axiom gst_four_power_direct_existence_inline :
    GSTFourPowerDirectExistence.FourPowerDirectExistence
```

## 12. Extra verified helpers relevant to the base/step

```lean
theorem modular_check_base (a : Nat) (ha : 5 ≤ a) (ha500 : a ≤ 500) :
    hasTernaryTwo (4^a) = true                       -- L3501 (active; hard list {93,166,237,280,387,432,496} needs row-16 checks)

theorem even_case_a_mod3_2 (a : Nat) (ha : a % 3 = 2) : hasTernaryTwo (4^a) = true   -- L740
theorem even_case_a_7_mod9 (a : Nat) (ha : a % 9 = 7) : hasTernaryTwo (4^a) = true   -- L750
theorem cubic_lift_mod81 (m : Nat)
    (hm9 : m % 9 = 1 ∨ m % 9 = 2 ∨ m % 9 = 5 ∨ m % 9 = 6 ∨ m % 9 = 8) :
    hasTernaryTwo ((4^m)^3) = true                   -- L3633 (WEAK: only hasTernaryTwo)
theorem mul4_lift_a9_6 (a : Nat) (ha9 : a % 9 = 6) : hasTernaryTwo (4^a) = true      -- L3689
theorem cascade_universal
    (s b : Nat) (hs : 1 ≤ s) (_hb : 1 ≤ b) (_hb3 : b % 3 ≠ 0) :
    (4^(3^s * b) - 1) % 3^(s+1) = 0 ∧
    ((4^(3^s * b) - 1) / 3^(s+1)) % 3 = b % 3        -- L473
```

And in GSTFourPowerDirectHappyBridge.lean (verified, no axioms):

```lean
theorem commonTwo_to_physical_happy_row
    (K : Nat) (h : CommonTwo K) :
    ∃ q : Nat, 1 ≤ q ∧
      GSTCanonicalTailStateIso.HappyCell
        (GSTCanonicalTailStateIso.carry4 (4^K) q)
        (GSTCanonicalTailStateIso.digit3 (4^K) q)
```

whose proof (via `digit3_four_mul (4^K) q` and `directCarry4_lt_four`) shows the
CONVERSE direction too: a common-two forces the source carry into {0,3}.
