# GST / Worldtrace: infinity-control terminal normal form and noncircular escape attempts

2026-10-29 IST. Scope: Erdős ternary powers of two, and in particular the exact universal target
  forall K>=5, exists p>=1, digit3 (4^K) p = 2.
Status: **not proved**. This document separates proved global machinery from an unresolved universal collision.

## Evidence and repository dependency audit

The legacy "four-power universal Happy Gate" in GSTInfiniteFourPowerNavigation.lean is not a kernel theorem:
isolated workflow #40785543486 fails at power_three_step_collision line 176, and #print axioms contains sorryAx.
The hypotheses are a child Happy gate at (K,3+q) and a fully BAD right edge at (K+3,3+j).
It is a genuine source-dependent cross-column collision question; exact telescope identities, a negative
child jump and nonnegative parent jumps do not by themselves produce a contradictory inequality.
The older gst_omega_termination_s1, _s3, _stable in ErdosTernary2.lean similarly have an unresolved
final contradiction from exact origin/descent/carry identities.

In GSTFinalPrefixOneStep6Infinite.lean the all-Nat controller exists only with an explicitly
assumed hRightBad. Its infinite mass and Past/Future identities are valid conservation equations
and do not imply the conclusion. GSTCoupledControllerCountermodel.lean constructs a noncanonical
all-Nat parent BAD controller with a child Happy event (parent word 2944, child word 46).
Therefore any unconditional transfer theorem must exploit that the *canonical* input is a
specific perfect-power source.

## Exact terminal Ω normal form — kernel-verified

GSTOmegaTerminalNormalForm.lean is kernel green in dedicated run #40790148990.
Let Happy(C,d) := d=2 and C∈{0,3}; affineCarry D X j := (D+4*(X mod 3^j))/3^j.
The existing kernel theorem GSTOmegaAbsorbingZero.finite_seed_eventually_zero yields
for j>=B=D+4X+1 the exact pair (digit X j, affineCarry D X j)=(0,0).

Thus, with NO finite experiments or limiting hypotheses,
  SeededBadTrace D X <-> forall j<B, not Happy(affineCarry D X j,digit X j).
The infinite BAD suffix after B is automatic, not a contradiction.

For any positive A and valid coupled source initial st with st.childCarry=0,
  InfiniteBadCoupledControl A st <-> SeededBadTrace st.parentSeed (st.parentWord A),
hence also iff the finite preterminal BAD predicate above.
This proves that the all-depth controller introduces NO independent exclusion content
beyond its seeded BAD input. For a canonical parent, a new arithmetic exclusion must refute
that BAD input.

GSTOmegaCanonicalBoundaryIff.lean transports the same equivalence to the actual residual
perfect-power source E=residualEnergy s 1 n, width 3^s, base row s+2, using the existing
canonical zero left carry and fully exact graphCoupledState physical invariant.
Check its own CI before marking it kernel-verified.

## No uniform observation horizon — kernel verified

From GSTFourPowerDirectResidue.pow4_digit_period:
  digit3 (4^(m + 3^p*t)) p = digit3 (4^m) p, any p,m,t.
The special m=4 is clean at EVERY ternary digit (4^4=256=(100111)_3).

For arbitrary L,M, choose K=4+3^L(M+5), so K>=max(5,M).
For every p<=L, K=4+3^p*(3^(L-p)*(M+5)); its row-p digit agrees with
4^4, hence no digit two.
GSTOmegaArbitraryDelay.lean, dedicated CI #40790757888 PASS, proves this statement
fully quantified in Lean without sorryAx.

As a result an eventually-zero exponent path does not guarantee *any fixed finite*
terminal escape bound, including a bound uniform over arbitrary natural K.
This in NO way refutes eventual escape at a K-dependent position.

## An exact first-hit theorem for an infinite perfect-power family

Define c_L=(4^(3^L)-1)/3^(L+1). LTE recursion:
 c_(L+1)=c_L+3^(L+1)c_L^2+3^(2L+1)c_L^3.
For L>=2, c_L mod27 = 16. For L>=5, 4^4=256<3^(L+1).
The already kernel-verified whole-block transport gives
 floor(4^(4+u*3^L)/3^(L+1)) mod27 =
 (u*c_L*256) mod27 = 19u mod27, for every u and L>=5.

1. u=1: 19=(201)_3, so the first postcut trits from low to high
   are 1,0,2; earlier trits equal those of 256. The first 2
   is EXACTLY row L+3.
2. u mod3=2: 19u mod3=2. The first 2 is EXACTLY row L+1 for all
   u of that residue and ALL L>=5.
3. u mod27=1: the first three postcut trits equal (201)_3;
   thus the first 2 is EXACTLY at L+3 for every such u and L>=5.

These are two-variable, unbounded (u,L) algebraic results, not enumeration.
Wolfram independent tests: for u=1, L<=22 first p agrees for all L>=5;
for quotient all-u law, 600 exact pairs L in {5,6,10,15,25}, u=1..120
yielded zero failures. This is corroboration, not replacement for proof.

Lean modules: GSTOmegaExactDelayedEscape.lean and
GSTOmegaThreeTritMultiplierLaw.lean with dedicated CI.
Mark these kernel verified ONLY after their workflow is green.

## The precise missing terminal theorem

A true completion must prove for all canonical nonexceptional source states:
  not SeededBadTrace(parentSeed,parentWord).
Equivalently, an actual Happy parent event exists before its provable terminal cutoff.
The terminal normal form makes this quantifier finite *for each source*, but the
cutoff grows with source and no uniform bound exists. A source-specific
well-founded descent, arithmetic/phase obstruction, or rigorous nonnegative
potential impossibility must produce that witness independently of the assumed
parent BAD or the target conjecture.

No equation equating a bad controller to its initial bad trace can discharge
this. Nor can the 2^L perfect-shadow branching, a density-zero theorem,
an eventual-zero tail, or a passing source-only no-sorry build.

## Strict comparator target

The benchmark solution file previously defines
  erdos_ternary_2 (hGate : gst_four_power_third_wave_gate) :
    forall n, 9<=n -> noTernaryDigitTwo (2^n) = false.
Run #40780932923 correctly rejected this type because the challenge requires
the same proposition WITHOUT hGate. The strict comparator must pass only after
the perfect-power terminal exclusion is kernel proved and installed in the
unconditional type.

This work deliberately distinguishes (a) exact mathematics,
(b) kernel-verified Lean, (c) finite Wolfram checks,
(d) failed proof attempts, and (e) the still open universal theorem.


## Exact two-parameter coefficient classification and natural survivor residues

For every L>=5 and arbitrary natural multiplier u,
  floor(4^(4+u*3^L)/3^(L+1)) mod 27 = 19*u mod 27.
The proof is the exact GST Worldtrace whole-block kernel theorem,
the pure-power seed condition 256<3^(L+1), and the
uniform c_L mod27 =16 coefficient stabilization law.

The 18 three-free multiplier residues modulo 27 split exactly:
- first three postcut trits INCLUDE TWO for
  r∈{1,2,4,5,7,8,11,14,16,17,20,23,25,26};
- first three postcut trits are CLEAN for
  r∈{10,13,19,22}.

This is a *modulo-27 finite algebraic classification applied to all
unbounded u and all L>=5*, NOT a bounded exponent scan.
It covers 14 of the 18 three-free residue classes uniformly.
The four survivors may still have 2s later, and the universal conjecture
requires their escape too.

The first-hit statements are stronger:
- u≡2 mod3 → first 2 at L+1;
- u≡1 mod27 → first 2 at L+3.
A proof of u≡1 mod27 transports the u=1 trace using the period
3^(L+3): difference of exponents is (u-1)*3^L,
which is divisible by 3^(L+3).

Wolfram verified the 27-class table symbolically and the quotient
for 600 independent exact (L,u) pairs. The 2-parameter Lean module is
GSTOmegaThreeTritMultiplierLaw.lean; await its dedicated CI for
kernel-proof evidence. The single-parameter first-hit source theorem
GSTOmegaExactDelayedEscape.lean is now kernel green in run #40791677601.
The canonical perfect-power Omega boundary iff is kernel green in
run #40791456858. The exact Ω terminal normal form is kernel green in
run #40790148990, and arbitrary delay is kernel green in run #40790757888.

The strict unconditional Erdős theorem has not been established.


## Kernel closeout: full proof receipts for this research phase

All of the following isolated dedicated GitHub Lean jobs completed successfully
after explicit namespace, power, quotient, and exact source-state repairs:
- Run #40790148990: GSTOmegaTerminalNormalForm.lean, exact infinite BAD
  controller and preterminal source BAD equivalences;
- Run #40790757888: GSTOmegaArbitraryDelay.lean, arbitrary-depth
  clean prefixes at arbitrarily large natural exponents;
- Run #40791677601: GSTOmegaExactDelayedEscape.lean, for ALL L>=5
  the first digit two of 4^(4+3^L) is EXACTLY L+3;
- Run #40791456858: GSTOmegaCanonicalBoundaryIff.lean, exact
  canonical perfect-power all-depth controller iff preterminal BAD;
- Run #40792308751: GSTOmegaThreeTritMultiplierLaw.lean, ALL
  multipliers u and ALL scales L>=5 have quotient 19u mod27,
  with exact first-hit corollaries for u≡2 (mod3) and
  u≡1 (mod27);
- Run #40791943598: GSTOmegaResidualFiniteSupport.lean, the
  original GSTOmegaInfiniteBadTrace for every s,k,m is
  EXACTLY equivalent to BAD at every position below the
  explicitly constructed residual source cutoff.

No proof in this list assumes the claimed universal Erdős conclusion.
The last job closes the previously disconnected original Ω∞ interface,
rather than only a parallel V2 controller model.

### Adversarial proof boundary after integration

The direct residual-Ω normal form does NOT prove the original
GSTResidualOmegaTermination: a finite-source BAD sequence
unconditionally ends in a BAD absorbing zero/zero tail, and its
preterminal segment can itself be BAD. The all-depth theorem
therefore has exactly the same mathematical exclusion gap,
now isolated to one preterminal arithmetic witness.

A rigorous final route must use the true canonical perfect-power
source, its digit/carry phase dynamics and finite natural exponent
support to force the preterminal source witness. Existing
GSTInfiniteFourPowerNavigation.power_three_step_collision lacks
that implication and failed its isolated kernel audit #40785543486
at line 176 (sorryAx). The strict unconditional Problem406 comparator
failed #40780932923 because the submitted solution still has an
unproved hGate argument.

**Primary original conjecture status after this research phase:
OPEN / not proven by these source and kernel receipts.**


## Final global congruence certificate (newly kernel-green)

Module GSTOmegaResidueClassExit.lean, dedicated CI run #40792866139,
completed successfully with no sorryAx. It kernel-proves, for every
L>=5, every unbounded natural multiplier u with u mod3 !=0, and
u mod27 not in {10,13,19,22}, that there is a digit two in
4^(4+u*3^L) between positions L+1 and L+3 inclusive.

The proof has three exact pieces:
1. the universally quantified GST quotient 19u (mod27) obtained in
   GSTOmegaThreeTritMultiplierLaw.lean, green #40792308751;
2. a kernel-checked digit-window bridge from the quotient to three
   consecutive actual ternary digits of the full power;
3. 27-state Fin computation in Lean deciding exactly which of the 18
   three-free source residues generate a 2 in those three digits.

Every multiplier is unbounded: Fin 27 describes a congruence class
and is NOT a finite upper bound on u.

The new source-specific global facts and all original Ω-equivalences
are independent of the still-open universal residual Ω termination
proof obligation. They cannot be repackaged as a strict comparator
pass for the entire Erdős question.
