# GST Worldtrace quadratic two-band lift and nonlinear Problem 406 physical HGate discovery

**Working branch:** `gpt6/problem406-fourth-trit-discovery-20261029`  
**Research date:** October 29, 2026.  
**Scope:** exact GST proof improvements, NOT a claim of unconditional Erdős 406 resolution.

## 1. Mathematically exact second-order GST law

Let `T = 3^(L+1)`, `c_L = GSTCanonicalTailLTE.lteCoeff L`,
where `4^(3^L) = 1+T*c_L`. Define the exact integer triangular
number `triangle 0 = 0` and `triangle (u+1)=triangle u+u`,
so `triangle u = u(u-1)/2` (integer-valued).

The newly proved Lean theorem
`GSTWorldtraceQuadraticBlockLift.quotient_quadratic_block_lift`
establishes, for **all** natural A,c,u and positive T:

```
(A*(1+T*c)^u/T) % T^2
 = (A/T + u*c*A + triangle u*T*c^2*A) % T^2.
```

This derives from the exact quotient increment
`Q_(u+1)=Q_u+c*A*(1+T*c)^u`
and the exact first-order power congruence
`(1+T*c)^u = 1+u*T*c (mod T^2)`.
The triangular quadratic term has NOT been dropped.

Specialization to the physical perfect power gives
`GSTWorldtraceQuadraticBlockLift.pow4_quadratic_window_lift`:

```
(4^(M+u*3^L) /3^(L+1)) % 3^w
 = (4^M /3^(L+1) +
    u*c_L*4^M +
    triangle u*3^(L+1)*c_L^2*4^M) %3^w
```

for **all M,u,L and all 1 <= w <= 2*(L+1)**.

The older linear GST Worldtrace block law only controlled
`1 <= w <= L+1`. The new theorem EXACTLY doubles the
available postcut scale band and is not a classical approximation,
not a bounded enumeration, and not conditional on the global gate.

Lean kernel run [40853110518](https://github.com/kyo-oo/erdosternary2/actions/runs/40853110518)
**PASSED**; the kernel reported only standard Lean axioms
`propext`, `Classical.choice` and `Quot.sound`, with no
`gst_four_power_direct_existence_inline` and no `sorryAx`.

## 2. Genuine nonlinear collision after the earlier linear band

Set `L=6`, `u=31`, `M=4` or `M=5`.
Then `K=4+31*3^6=22603`, `T=3^7=2187`,
and the row of interest is `p=15`
(ninth postcut quotient trit, index `k=8`).

The coefficient recurrence gives `c_6 % 19683 = 7225`,
and `triangle 31=465`.

The *invalid extrapolation* of the original linear formula
to width `w=9` would give:

```
linear-source residue   = (31*7225*256) %19683 = 1021
linear-neighbor residue = (31*7225*1024)%19683 = 4084
linear trit pair at k=8: (0,0)
```

The **new valid quadratic formula** adds the exact missing term
`465*2187*7225^2*4^M` and gives:

```
actual-source residue   = 14143 mod19683
actual-neighbor residue = 17206 mod19683
actual ninth-trit pair at k=8: (2,2)
```

Wolfram evaluated the literal physical powers by modular exponentiation,
without substituting any abstract source: the actual quotients of
`4^22603` and `4^22604` agree exactly with `14143` and
`17206` modulo `19683`, so their physical ternary digits
at `p=15` are both **2**.

The full nonlinear seed and global congruence-family proof is committed
in `GSTWorldtraceQuadraticHGateDiscovery.lean`.
The exact source theorem depends on the new quadratic transport,
and the extension to an infinite family uses the already proved
`GSTFourPowerDirectResidue.pow4_digit_period`.

## 3. New unbounded family

The proposed exact resulting theorem is

```lean
theorem commonTwo_new_nonlinear_ninth_trit_family
    (u : Nat) (hu : u % 19683 = 31) :
    CommonTwo (4 + u * 3^6)
```

The proof transports the source and neighbor physical row `p=15`
through the exponent's exact periodicity modulo `3^15`:

```
u = 31 + 19683*(u/19683)
4 + u*3^6 = (4 + 31*3^6) + 3^15*(u/19683)
```

Thus this is not only the one seed `K=22603`:
every natural multiplier in that infinite arithmetic progression
is an exact physical common-two gate. Independent Wolfram checks at
u = 31,19714,39397,59080,78763,98446,118129
all gave source/neighbor digit pair (2,2) at row 15.

The new file also states the original `thirdWave` and
`CreationCertificate` endpoints for this family, not a new
definition of an easier target.

**Lean proof status:** nonlinear ninth-trit original physical source, neighbor,
unbounded residue family, and direct original thirdWave / CreationCertificate
integration are all **KERNEL-VERIFIED** in strict targeted run
[40854333189](https://github.com/kyo-oo/erdosternary2/actions/runs/40854333189)
at commit `6d382e5013e0fab297101a89634aed7a7c5755af`.
The initial failed compilation (40853568897) reflected Lean simplifier and
witness-rewrite mistakes, fixed by exact polynomial modulus factorization,
a controlled exponent equality and explicit row-15 witness.

## 4. Unconditional boundary still outstanding

The global `gst_four_power_third_wave_gate` requires one
`CommonTwo K` for **every** `K>=5, K!=7`.
The new quadratic theorem, even when the ninth-trit family
is certified, covers explicit infinite exponent progressions,
not all K. The full comparator still requires a proof of the
remaining perfect-power survivor paths.

The historical comparator successes from September 6 retained
the custom axiom `gst_four_power_direct_existence_inline`,
as documented in
`derivations/GPT6_HISTORICAL_406_COMPARATOR_AXIOM_FORENSICS_20261029.md`.
We must not reinstate that axiom merely to produce another PASS.
