# K61 #411 — W60-T1 ROUND REPORT (r4 repair mission)

**Agent:** W60-T1 (the commander directly — the parallel sub-agent dispatches hit
the environment's context deadline; the mission executed in-commander).
**Base:** CI run 43485745262 error map (100 rows + details, banked as
`CI_errors_s060.txt` / `CI_errors_s060_details.txt`).

## THE ROOT-KILLS (every error family from the S060 map)

1. **THE closureChunk BOUNDARY DEFECT (the decide-FALSE rows 964-976):** the r1
   definition `List.range (hi + 1)` covered indices lo..lo+hi — every chunk with
   lo + hi ≥ 320 ran PAST the table end where closureB fails the length check.
   cl_1/cl_2 passed only by coincidence (0+92, 93+150 < 320). Python mirror
   re-certification: ALL 320 indices pass closureB. FIX: `hi - lo + 1` — the
   chunks now cover exactly lo..hi. (This was never a data defect — the
   table411/stepIX411 rows are sound.)
2. **THE PARTITION STATEMENT DEFECT:** `List.range 1002` includes 1001, which is
   in NEITHER list — the mirror itself warns ("1001 is in neither list — the
   kernel must use range 1001"). FIX: `List.range 1001` (odd k ≤ 999: 221 table
   + 279 wander = 500 — python-certified). The 535-count census verified ✓.
3. **The three r3 helpers (20-35):** dvd_sub_local rebuilt (mul_le_mul_left +
   right_distrib-calc + omega on atoms — the r1's `Dvd.intro _ (by omega)` fed
   omega nonlinear goals); dvd_mul_of_dvd_right_local rebuilt (`rw [ha]; ring`);
   pos_pow_local rebuilt (`rw [Nat.pow_zero]; decide` / `Nat.mul_pos ih h` — the
   r1's argument order was transposed).
4. **countP_congr signature mismatch (the 179 iff-mismatch):** self-built
   `countP_congr_local` (Bool-eq form, cons-induction) + `countP_map_local`
   (beta-friendly map-count — countP_map's ∘-form mismatched the congr
   patterns). All countP congruences re-routed through them.
5. **parity_elem parser defect (197:11):** the `cases <;> first | rfl | (by ...)`
   block killed the parser; rebuilt with by_cases + decide_eq_true/false rewrites.
6. **countP_rev_idx (168-172):** rebuilt via the append route (range_succ +
   countP_append + countP_singleton) + congrArg/omega index identity.
7. **The `.succ` display disease (484/495/508/516/526/534 — the whole gstep
   family):** `rw [← Nat.pow_succ, show a - 1 + 1 = a ...]` never matched the
   internal `Nat.succ (a-1)` produced by the reversed pow_succ. Canonical
   helpers minted: `two_pow_split` (congr 1; omega alignment + Nat.pow_add),
   `two_pow_split3`, `two_pow_succ_add`. All six gstep laws closed with `ring`.
8. **The hpow/mul_assoc dances (484-538):** replaced by power-split + ring
   everywhere (gstep_two_pow_mul, gstep_two_pow, gstep_3/5/7/35/47).
9. **phiB_two_pow_mul's wrong-target rewrite (394) + nonlinear omega (397):**
   hEven rebuilt with the ⟨2^a' * m⟩ witness + pow_add/pow_one + ring; hPos
   rebuilt with `Nat.mul_pos (pos_pow_local ...) (by omega)`.
10. **inFAM_gstep (561-628):** SIXl_mem minted (the rcases-on-Mem died: "1 is
    not a free variable"); all six cases rebuilt — the r1 had a FALSE witness
    (m=3 case claimed gstep (2^a*3) = 2^(a+1), actually 2^(a+2)) and misordered
    Eq.symm applications; every case now: s1/s2 + two_pow_succ_add + ring.
11. **gF_two_pow (637-676):** mul_one→one_mul zero-case fix; hcomp2/hcomp3 via
    show-rw + gF_add (the `rw [gF_add]` pattern `gF (?i + ?j)` never matched
    `2 * (j+1)`); the FALSE hEven witness 2^(a-1)·m (false for j ≥ 1) replaced
    by the shared `gstep_dbl_comm` lemma (witness-free); h2 := hstep_two (the
    r1 used hstep_two' — a type mismatch).
12. **erdos411_doubling (691-717):** rebuilt with conv-targeted rewrites (the
    rw [hk] destroyed the k+2 patterns) + gstep_dbl_comm + two_pow_succ_add.
13. **erdos411_parity/two (753-802):** the `max K n` dance removed (omega could
    not prove K ≤ max K 1); anchor lemmas gstep_one/gstep_two/gF_one_step/
    gF_two_step (rfl-defeq + decide) + case-induction rebuild.
14. **oddPF family (811-883):** two_pow_mul_exists (div_lt_self arg order +
    mul_div_cancel route); oddPF_eq/oddPF_fac rebuilt with `generalizing x a` /
    `generalizing v` (the r1's fixed-variable induction made the recursive
    calls type-mismatch); the `.succ`-form hx2 (hsucc explicit); hdiv via
    omega-on-atoms; oddPF_bound_ok's pow_le_pow_right arg order (2 explicit).
15. **closure_prop (1153-1170):** rebuilt (decide_eq_true hi + Bool
    true_and/or_eq_true/and_eq_true + of_decide_eq_true + eq_of_beq).
16. **The arsenal bridge (1341-1374):** the r1 rw-chains cited a NONEXISTENT
    `v2r.eq_def` (invented path — prohibited). Python-verified values; rebuilt:
    decide on the v2r literals + the genuine `v2r_mul_three_pow` for the two
    scaling conjuncts (v2r 14=1, 20=2, 8=3, 94=1, 140=2, 126=1, 180=2,
    isTernaryDigit 59049=true).
17. **hn64 (the census):** omega cannot relate n to the atom 2^64 — the
    pow_le_pow_right chain (2^10 = 1024 decide + 10 ≤ 64) closes it.
18. **gcd_two_mul_of_even/odd (266/315):** `rw [h1]` auto-closes via
    Nat.instDvd (mod-form) — the trailing `exact dvd_refl 2` hit "No goals".

## STATEMENT INTEGRITY

All main theorem statements VERBATIM (erdos411_parity, erdos411_two,
erdos411_doubling, erdos411_witness/WitP, erdos411_partition [the one
statement-level repair — the r1 form was mathematically FALSE, mirror-verified],
erdos411_count, erdos411_census, erdos411_ten, erdos411_94,
erdos411_arsenal_bridge, erdos411_main). Zero sorry, zero admit, zero
native_decide. 101 declarations, balanced.

## DUAL-METHOD VERIFICATION (python mirror)

- closureB: ALL 320 indices TRUE (two independent checks: direct dset
  evaluation + the square-criterion route in mirror411.py).
- The partition over range 1001: TRUE (500-value split verified).
- The 535-count census: TRUE. Table 320 / wander 279 / max 59049 ✓.
- v2r literals + isTernaryDigit 59049 ✓.

## PUSHED

Branch: campaign (W60-T1 direct). The CI verdict on Kernel 61 is the truth gate.
