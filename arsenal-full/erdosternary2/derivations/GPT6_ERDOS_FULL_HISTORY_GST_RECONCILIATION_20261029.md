# Erdős ternary 2^n: full-reachability history audit and GST proof state (2026-10-29)

This research state reconciles the original comparator, Sol's noncircularity
attempts, and newly introduced GST Worldtrace work. It is a file/commit
inventory and critical-path proof audit, NOT a claim that every archived
snapshot line was individually reread.

## Reachable commit chronology
At the new branch head dbefc52afe13ac6048f6331f23f1d50d25712a99, the
GitHub API returned 1,420 reachable commits across 15 paginated pages:
14 full 100-commit pages and one 20-commit page, from
2026-08-16 19:16:56 UTC through 2026-10-29 16:20:26 UTC.
The historical commit de11dc2c5ee340fee1929ba2adc6834a72ab9879
belongs to the September 6 historical comparator phase.

The tree at that branch revision has 1,620 blob files (not a 1,620
independently proven mathematical facts); includes 1,005 .lean,
175 .yml, 272 .md, 1,138 under archival ker07-snapshot/,
43 under modules/, 23 under third-wave-research/, and 220 top-level
Lean modules. These counts overlap (extension groups and directories).
Thus the meaningful proof surface is a proper subset of the archive.

## Actual target, no renaming
Lean exact benchmark:
  forall n:Nat, 9<=n -> noTernaryDigitTwo (2^n)=false
The current main production proof is conditional on
  gst_four_power_third_wave_gate:
    forall K, 5<=K -> K!=7 -> CommonTwo K
CommonTwo K means the existence of one physical ternary position
p>=1 with digit 2 in BOTH 4^K and 4^(K+1).
ThirdWave and CommonTwo are kernel-proved equivalent.

## Historical comparator forensic outcome
Historical GitHub actions #34004380610 and #34004380616 on Sept 6
returned Your solution is okay and COMPARATOR RESULT PASS.
The historical apparently unconditional theorem nonetheless depended
on the nonstandard exact-target custom axiom
gst_four_power_direct_existence_inline, with its dependency printed by
Lean. This is a confirmed true comparator PASS, not a kernel proof
free of custom assumptions. See
GPT6_HISTORICAL_406_COMPARATOR_AXIOM_FORENSICS_20261029.md.

## Families of attempted methods and precise obstructions
1. U2D canonical 2D signed information, prefix-one transport, and
   the final perfect-power block collision: terminal signed conservation
   identity did not yield the required contradiction. Previous local
   proof attempted to close a false generic source-independent step.
2. Omega and all-depth infinite BAD controllers: an all-zero BAD
   absorbing tail is permitted. Their terminal normal forms are exact
   equivalences to the seed BAD trace, NOT exclusion of that seed.
3. Happy child-to-parent inheritance is false on generic integer
   controllers (source R=46 and scaled parent 2944), so physical
   4^K source identity is indispensable.
4. Single-column vacuum-neutral U-cocycle separations are impossible:
   the four physical carry constraints contradict algebraically.
5. Any globally fixed finite row depth cannot rule out all physical
   exponents. Both 4+u3^L and ternaryOnes(m) yield arbitrarily
   delayed genuine source states.
6. Finite-state entropy / 3-adic zero measure establishes scarcity
   of surviving exponent classes, not emptiness of the natural
   integer exceptional set.
7. Exact all-order and cubic Worldtrace identities and finite-width
   multiscale signatures preserve the real source and give
   new unbounded infinite CommonTwo subfamilies, not all K.

## New research committed on this branch
- GSTProblem406HGateSeventhTrit.lean: 58 new physical source-neighbor
  simultaneous-two congruence classes mod3^7, all scales L>=6,
  with original ThirdWave and CreationCertificate integrations;
  dedicated strict GitHub Actions run #40909733530 PASSED.
- derivations/GPT6_GST_ALL_ONES_FIRST_COMMON_TWO_20261029.md:
  exact all-m>=8 mathematical first CommonTwo at p=m+9 for exponent
  K_m=(3^m-1)/2. The fixed nine-trit coefficient uses genuine
  physical exponents, not the generic Omega controller.
- GSTProblem406AllOnesFirstCollision.lean: a new GST peel1-polynomial
  direct formalization of an all-m CommonTwo witness at m+9;
  the exact CommonTwo physical witness at p=m+9 and the original
  thirdWave body are strict Lean kernel VERIFIED, with CI run
  #40911647994 SUCCESS (without sorryAx or custom axioms).
  The stronger FIRST-row minimality conclusion is presently only
  recorded as a separate complete mathematical derivation.

## Strict done criteria
Only a theorem with the original forall n>=9 challenge type,
no explicit hGate or equivalent hidden assumption, no sorry,
and #print axioms free of all custom axioms, followed by actual
comparator PASS on the same exact commit, certifies the
requested universal conclusion. No unconditional theorem is
recorded by this research state.
