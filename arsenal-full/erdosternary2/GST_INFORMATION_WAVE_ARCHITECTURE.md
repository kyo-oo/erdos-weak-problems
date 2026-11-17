# GST Information-Wave Architecture

## Status and governing correction

The former Step-6 architecture was mathematically misdirected. It attempted
to turn a changing information packet into a monotone information descent and
then into a contradiction. That direction is rejected.

In GST spacetime, information is not required to remain constant in one
observable coordinate. A packet may be created or re-encoded and may change
its carry, digit, phase, sign, horizontal position, or wave representation.
For example, a representation may change from `B3` to `-B3` without the
underlying information being destroyed. Consequently, none of the following
implications may be assumed:

```text
parent boundary is Bad  ->  child information is Bad
changed representation  ->  information disappeared
finite origin suffix     ->  terminal information extinction
terminal n-wave packet   ->  False
```

The GST graph is dynamic and all-depth. There is no justified monotone order
called information descent or information ascent in the current formalism.

## The invalid proof route that was removed

The obsolete route was:

```text
child Happy
    +
all-depth parent/right Bad
    -> alleged child-information descent
    -> alleged complete child Bad trace
    -> contradiction with the original child Happy gate
    -> False
```

Its concrete Lean endpoints were:

```lean
canonical_perfect_power_block_collision : ... -> False
canonical_prefix_one_u2d_collision : ... -> False
gst_step6_collision_kernel : ... -> False
```

These declarations were removed or replaced. The replacement declarations do
not assert `False`:

```lean
GSTGraphV2PerfectPowerBlockCollision
  .canonical_perfect_power_block_terminal_packet

GSTPrefixOneU2DCollisionProof
  .canonical_prefix_one_u2d_terminal_packet

gst_step6_terminal_packet_kernel
```

No replacement may recreate the same implication under a new theorem name.

## Certified information behavior

The currently green mechanism is information creation/re-encoding and exact
transport:

```text
Happy gate
  -> visible output digit two
  -> next carry is two or three
  -> next carry is nonzero
  -> coupled invariant remains valid
  -> parent Bad suffix remains represented in the controller
  -> exact all-depth controller orbit
  -> exact Past/Future ledger at every depth
  -> exact n-wave re-coordination of the same physical packet
```

The principal certified modules are:

- `GSTInfiniteGateTransport.lean`
  - `happy_output_two`
  - `happy_next_carry_two_or_three`
  - `happy_next_carry_ne_zero`
  - `happy_mass_reencoded`
  - `coupled_happy_transports_information`
- `GSTGraphV2InfiniteControllerBridge.lean`
  - `graph_infinite_bad_control`
  - `graph_child_happy_to_controller`
  - `graph_child_happy_latent_transfer`
- `GSTInfiniteCoupledLedger.lean`
  - the exact all-depth coupled ledger and Past/Future synchronization
- `GSTGraphV2CanonicalInfiniteCycle.lean`
  - exact controller-cycle iteration
  - exact observable and ledger packets at every cycle turn
- `GSTGraphV2CanonicalNWave.lean`
  - exact arbitrary-depth physical re-coordination
  - exact Bad-trace transport
  - exact combined Happy/Bad strip-packet transport
  - exact unit-energy specialization after origin-suffix exhaustion

These theorems certify persistence through changing representation. They do
not certify extinction and they do not certify a contradiction.

## Existing green one-step form-change theorem

Sol's latest inventory identified the monolith theorem that most directly
formalizes the intended behavior:

```lean
gst_pure_lift_or_forced_cascade
  (R p : Nat) (hp : 1 <= p)
  (hd : gstDigit R p = 2)
  (hgood : gstCarry R p = 0 \/ gstCarry R p = 3) :
  (gstDigit (4 * R) p = 2 /\
    (gstCarry (4 * R) p = 0 \/ gstCarry (4 * R) p = 3)) \/
  (gstDigit (4 * R) p = 2 /\
    (gstCarry (4 * R) p = 1 \/ gstCarry (4 * R) p = 2) /\
    gstCarry (4 * R) (p + 1) = 3)
```

This theorem is the correct local physical direction:

- digit-two information survives multiplication by four;
- it may remain immediately in a Happy carry sector `0/3`; or
- it may be re-encoded in ALT carry sector `1/2` and force carry `3` on the
  next forward edge.

The second branch is not failure, extinction, or descent. It is a certified
change of representation followed by a forced cascade. Future production
surgery should compose this theorem with the exact all-depth controller,
ledger, phase, and n-wave theorems. It must not replace the second branch by
a contradiction.

## Meaning of the terminal n-wave packet

After choosing a cutoff `K` with `n / 3^K = 0`, the residual energy becomes
one, but the accumulated horizontal phase remains:

```lean
P := nWaveShift s n K
```

The certified packet has the form:

```lean
HappyCell (graph 1 P (b + q)) ...
  /\
forall j, not HappyCell (graph 1 (P + canonicalWidth s) (b + j)) ...
```

This is a re-coordination of the original packet, not an extinction theorem.
The phase `P` retains consumed information. Neutrality at horizontal origin
zero says nothing by itself about a packet at horizontal coordinate `P`.
Therefore the following step is forbidden:

```lean
terminal_unit_origin_neutral + shifted packet -> False
```

## Correct production graph

The production architecture must preserve the live information packet:

```text
child Happy event
  -> LatentGateTransfer
  -> nonzero transported carry and visible output
  -> InfiniteBadCoupledControl
  -> InfiniteCoupledLedger
  -> exact graphCoupledOrbit at every depth
  -> exact n-wave / phase / sign re-expression
  -> continued GST information-wave state
```

The output of this chain is a structured evolving state or an exact
equivalence, not `False`.

Any future final theorem must state the actual desired observable consequence
of this persistent wave. It must not silently reintroduce one of these
unsupported claims:

- monotone information descent;
- monotone information ascent;
- information destruction at a finite-support horizon;
- collision merely from Happy on one shifted boundary and Bad on another;
- contradiction merely from a change of sign, phase, carry, or digit;
- an arbitrary universal four-power creation theorem without a kernel proof.

## Monolith integration status

The old contradiction kernel has been replaced by
`gst_step6_terminal_packet_kernel`, which returns the certified packet.

The later monolith declarations

```lean
gst_prefix_one_information_bad_descends_inline
gst_prefix_one_child_gate_contradicts_parent_bad_inline
```

belong to the obsolete architecture. They cannot be repaired by applying the
terminal packet and must not be treated as proven consequences of it. Their
consumer, the unconditional `gst_prefix_one_navigation_lift`, requires a new
valid argument based on the actual information-wave dynamics or another
independently kernel-checked theorem.

Until that replacement exists, the repository must report the comparator as
failing. A green support module is not evidence that an unsupported consumer
is green.

## Verification rule

The final claim is accepted only when the committed production monolith is
compiled by the repository comparator and its log literally contains both:

```text
Your solution is okay!
=== COMPARATOR RESULT: PASS ===
```

The proof must contain no `sorry`, `admit`, custom axiom, circular theorem,
`unsafe` escape, or decision shortcut that bypasses kernel proof.
