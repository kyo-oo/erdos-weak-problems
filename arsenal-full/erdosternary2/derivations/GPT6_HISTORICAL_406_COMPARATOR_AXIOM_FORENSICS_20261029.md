# Forensic proof audit of the September 6, 2026, comparator PASS and the remaining HGate

**Audited historical revision:** `de11dc2c5ee340fee1929ba2adc6834a72ab9879`  
**GitHub Actions runs:** [34004380610](https://github.com/kyo-oo/erdosternary2/actions/runs/34004380610), [34004380616](https://github.com/kyo-oo/erdosternary2/actions/runs/34004380616)  
**Archived job IDs:** `101408817174`, `101408817243`, `101408817208`.

## Verified historical facts

Both comparator runs were successfully completed on September 6, 2026.
Both archived comparator-job logs contain the exact success strings

```
Your solution is okay!
=== COMPARATOR RESULT: PASS ===
```

The historical `questions/deepmind_problem_406/Solution.lean` supplies
`erdos_ternary_2` with the challenge signature and no explicit
`hGate` binder. At that revision the production monolith's final
`erdos_ternary_2_universal` also has an unconditional-looking syntax.

**This is not evidence that the statement has been proved without
nonstandard axioms.** The same historical revision contains, in
`GSTPrefixOneOntologicalEscape.lean`:

```lean
axiom gst_four_power_direct_existence_inline :
    GSTFourPowerDirectExistence.FourPowerDirectExistence

theorem gst_four_power_creation_certificate_inline
    (K : Nat) (hK5 : 5 ≤ K) (hK7 : K ≠ 7) :
    GSTFourPowerOntologicalAdapter.CreationCertificate (4^K) := by
  exact
    (GSTFourPowerDirectCreationMaster.directExistence_to_creation_master
      gst_four_power_direct_existence_inline) K hK5 hK7
```

That `axiom` is a declaration of precisely the missing global physical
common-two/existence statement. The final proof chain is:

```
gst_four_power_direct_existence_inline [CUSTOM AXIOM]
 -> gst_four_power_creation_certificate_inline
 -> gst_four_power_creation_master_inline
 -> gst_power_two_wave_large
 -> erdos_ternary_2_even_universal
 -> erdos_ternary_2_universal
 -> comparator Solution.lean : erdos_ternary_2
```

The full historic Lean Action log **explicitly printed**
the following kernel dependency (job `101408817208`,
September 6, 2026, 01:54:55 UTC):

```
'erdos_ternary_2_universal' depends on axioms:
[gst_four_power_direct_existence_inline,
 propext, Classical.choice, Quot.sound]
```

The archived comparator and build logs were genuinely green;
the axiom audit step searched only for `sorryAx`, errors and
unknown identifiers, and **did not reject the custom axiom name**.
Hence the former PASS is a valid statement about the historical
comparator execution, but is NOT a clean unconditional
proof within Lean.

## Relation to the latest branch

As of 2026-10-29 the original research tip was
`gpt6/problem406-hgate-discharge-20261029` at `e2ccbc451a811b6230392990d7dc36ef90219c4b`.
It exposes its hypothesis explicitly:

```lean
def gst_four_power_third_wave_gate : Prop :=
  ∀ K : Nat, 5 ≤ K → K ≠ 7 →
    GSTFourPowerThirdWave.thirdWave K
```

An existing exact equivalence turns the body into
`CommonTwo K`, a simultaneous digit-two position in the
actual consecutive physical powers `4^K` and `4^(K+1)`.

The current branch's conditional theorem is not a regression
from a genuine axiom-free historical proof: it makes an actual
historical axiom dependency transparent. The desired upgrade must
prove the global gate (or directly prove the original benchmark
statement) without postulates, circular providers, or a hidden
re-definition that weakens the statement.

## Positive new progress that does not use the historical axiom

Branch `gpt6/problem406-fourth-trit-discovery-20261029` adds
physical perfect-power source-neighbor exact GST Worldtrace
identities and Lean-kernel-proved unbounded `CommonTwo` residue
families, linked to the original thirdWave and creation-certificate
interfaces.

- Fourth-trit: `u mod 81 in {10,40,58}`, witnessed at `p=L+4`.
- Fifth-trit: `u mod 243 in {19,76,97,118,130,151,187,208,229,241}`, witnessed at `p=L+5`.
- Sixth-trit: `u mod 729 in {4,67,73,103,166,199,205,235,268,274,337,367,400,436,469,499,532,538,631,664,670,700}`, witnessed at `p=L+6`.

All of these quantify over `L>=6` and all natural `u`
in the corresponding residue classes. They follow from
`GSTWorldtraceBlockLift.pow4_whole_block_lift` and coefficient
stabilization; they do not assume the final gate.

Validated Lean actions:
- Fourth trit source: [40848436050](https://github.com/kyo-oo/erdosternary2/actions/runs/40848436050).
- Fifth trit source: [40849695938](https://github.com/kyo-oo/erdosternary2/actions/runs/40849695938).
- Fourth/fifth integration: [40849695946](https://github.com/kyo-oo/erdosternary2/actions/runs/40849695946).
- Sixth trit source: [40851017330](https://github.com/kyo-oo/erdosternary2/actions/runs/40851017330).
- Sixth trit integration: [40851046425](https://github.com/kyo-oo/erdosternary2/actions/runs/40851046425).

The variable-width physical Worldtrace result
`two_wave_any_width_certificate_to_CommonTwo`
is available for further derivations; the globally quantified
existence of a certificate for every exceptional-free K is not proved.
No unconditional original benchmark PASS is asserted on this new
branch.

## Follow-through standard

The acceptance gate must check the kernel dependency chain
with `#print axioms` on the FINAL exact target and explicitly
reject ANY custom axiom, not only `sorryAx`. The challenge theorem's
type must have exactly the original statement with no hGate input.
Both compilation and strict comparator PASS must occur on the
same committed revision.

The full reachable historical commit metadata on the original
research tip comprised 1,342 commits, ranging from the 2026-08-16
workspace initialization to the 2026-10-29 original tip.
The tree contains 1,579 files on that branch; this audit read
the mathematical target and its direct dependencies, proof attempts,
critical docs and CI logs, **not all archived file contents**.
