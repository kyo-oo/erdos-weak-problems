#!/usr/bin/env python3
"""repair411.py — W62 r5: THE DETERMINISTIC FULL SURGERY on Erdos411.lean.
Source of truth: the git blob HEAD (the CI-compiled r4 state, 1413 lines).
All 22 root-kill fixes applied as asserted string replacements in-memory;
the result written once and verified by repeated md5 reads.
"""
import subprocess, hashlib, sys

BLOB = subprocess.run(
    ['git', 'show', 'HEAD:problem411-iterated-totient/Erdos411.lean'],
    capture_output=True, text=True, check=True).stdout

R = []  # (label, old, new)

# 1. countP_congr_local: the induction reverted h -> ih is an implication
R.append(("countP_congr_local cons",
"""  | cons a t ih =>
    rw [List.countP_cons, List.countP_cons, h a (by simp), ih]
""",
"""  | cons a t ih =>
    have hhead : p a = q a := h a (by simp)
    have htail : ∀ x ∈ t, p x = q x :=
      fun x hx => h x (by simp only [List.mem_cons]; exact Or.inr hx)
    rw [List.countP_cons, List.countP_cons, hhead, ih htail]
"""))

# 2. SIXl_mem: strip the impossible m ∈ [] tail
R.append(("SIXl_mem tail",
"""theorem SIXl_mem (m : Nat) (hm : m ∈ SIXl) :
    m = 1 ∨ m = 3 ∨ m = 5 ∨ m = 7 ∨ m = 35 ∨ m = 47 := by
  have h : m ∈ [1, 3, 5, 7, 35, 47] := hm
  simp only [List.mem_cons, List.mem_singleton] at h
  exact h
""",
"""theorem SIXl_mem (m : Nat) (hm : m ∈ SIXl) :
    m = 1 ∨ m = 3 ∨ m = 5 ∨ m = 7 ∨ m = 35 ∨ m = 47 := by
  simp only [List.mem_cons, List.mem_singleton] at hm
  rcases hm with h | h | h | h | h | h | h
  · omega
  · omega
  · omega
  · omega
  · omega
  · omega
  · exact absurd h (List.not_mem_nil m)
"""))

# 3. inFAM forward-reference fix: move the def before inFAM_pos
R.append(("inFAM move (insert)",
"""def inSIX (m : Nat) : Bool := SIXl.contains m
""",
"""def inSIX (m : Nat) : Bool := SIXl.contains m

def inFAM (x : Nat) : Prop :=
  ∃ a m, 1 ≤ a ∧ m ∈ SIXl ∧ (m = 1 → 2 ≤ a) ∧ x = 2^a * m
"""))
R.append(("inFAM move (delete old)",
"""/-- The chain-family predicate. -/
def inFAM (x : Nat) : Prop :=
  ∃ a m, 1 ≤ a ∧ m ∈ SIXl ∧ (m = 1 → 2 ≤ a) ∧ x = 2^a * m

theorem inFAM_gstep""",
"""theorem inFAM_gstep"""))

# 4. countP_rev_idx: the full clean rewrite (h3 was FALSE; omega correctly refused)
R.append(("countP_rev_idx",
"""theorem countP_rev_idx (P : Nat → Bool) : ∀ M,
    (List.range M).countP (fun j => P (M - 1 - j)) = (List.range M).countP P := by
  intro M
  induction M with
  | zero => rfl
  | succ M ih =>
    rw [List.range_succ, List.countP_append, List.countP_singleton]
    have hz : M + 1 - 1 - M = M := by omega
    rw [hz]
    have hc : (List.range M).countP (fun j => P (M + 1 - 1 - j))
        = (List.range M).countP (fun j => P (M - 1 - j)) :=
      countP_congr_local (fun x hx => congrArg P (by
        rw [List.mem_range] at hx; omega))
    rw [hc]
    omega
""",
"""theorem countP_rev_idx (P : Nat → Bool) : ∀ M,
    (List.range M).countP (fun j => P (M - 1 - j)) = (List.range M).countP P := by
  intro M
  induction M with
  | zero => rfl
  | succ M ih =>
    rw [List.range_succ, List.countP_append, List.countP_singleton,
        List.range_succ, List.countP_append, List.countP_singleton]
    have hbeta : ∀ j, M + 1 - 1 - j = M - j := by intro j; omega
    have hc : (List.range M).countP (fun j => P (M + 1 - 1 - j))
        = (List.range M).countP (fun j => P (M - j)) :=
      countP_congr_local (fun x _hx => congrArg P (hbeta x))
    rw [hc]
    have hz0 : M + 1 - 1 - M = 0 := by omega
    rw [hz0]
    have hshift := countP_shift (fun v => P (M - v)) M
    have hsplit : (List.range (M + 1)).countP (fun v => P (M - v))
        = (List.range M).countP (fun j => P (M - j)) + (if P (M - M) then 1 else 0) := by
      rw [List.range_succ, List.countP_append, List.countP_singleton]
    rw [hsplit] at hshift
    have hM : M - 0 = M := by omega
    have hMM : M - M = 0 := by omega
    rw [hM, hMM] at hshift
    have hc2 : (List.range M).countP (fun j => P (M - (j + 1)))
        = (List.range M).countP (fun j => P (M - 1 - j)) :=
      countP_congr_local (fun x hx => by
        rw [List.mem_range] at hx; congrArg P (by omega))
    rw [hc2] at hshift
    omega
"""))

# 5. parity_elem: the ite-literal residues close by rfl
R.append(("parity_elem rfl",
"""  by_cases hq : Q k
  · by_cases h1 : k % 2 = 1
    · rw [decide_eq_true ⟨hq, h1⟩,
          decide_eq_false (fun hc => absurd hc.2 (by omega)),
          decide_eq_true hq]
    · have h0 : k % 2 = 0 := by omega
      rw [decide_eq_false (fun hc => absurd hc.2 h1),
          decide_eq_true ⟨hq, h0⟩,
          decide_eq_true hq]
  · rw [decide_eq_false (fun hc => hq hc.1),
        decide_eq_false (fun hc => hq hc.1),
        decide_eq_false hq]
""",
"""  by_cases hq : Q k
  · by_cases h1 : k % 2 = 1
    · rw [decide_eq_true ⟨hq, h1⟩,
          decide_eq_false (fun hc => absurd hc.2 (by omega)),
          decide_eq_true hq]
      rfl
    · have h0 : k % 2 = 0 := by omega
      rw [decide_eq_false (fun hc => absurd hc.2 h1),
          decide_eq_true ⟨hq, h0⟩,
          decide_eq_true hq]
      rfl
  · rw [decide_eq_false (fun hc => hq hc.1),
        decide_eq_false (fun hc => hq hc.1),
        decide_eq_false hq]
    rfl
"""))

# 6. the shifted-parity split lemma (new) + phiB_odd_dbl's tail swap
R.append(("parity_split_succ insert",
"""/-- The parity-split count: (Q ∧ odd) + (Q ∧ even) = Q.
W59-F-1: the r1 `simp only [decide_eq_true, decide_eq_false] at *` never fired
(the decide-of-and conditions cannot be rewritten inside the bif instances —
motive issue). Replaced with the per-element lemma + omega on ite-atoms. -/
theorem countP_parity_split (Q : Nat → Prop) [DecidablePred Q] : ∀ (l : List Nat),
""",
"""/-- The parity-split count: (Q ∧ odd) + (Q ∧ even) = Q.
W59-F-1: the r1 `simp only [decide_eq_true, decide_eq_false] at *` never fired
(the decide-of-and conditions cannot be rewritten inside the bif instances —
motive issue). Replaced with the per-element lemma + omega on ite-atoms. -/

/- W62 r5: the (k+1)-shifted variant — phiB_odd_dbl's predicates are
succ-indexed; the parity_split lemma's k%2 shape never matched there. -/
private theorem parity_elem_succ (Q : Nat → Prop) [DecidablePred Q] (k : Nat) :
    (if decide (Q k ∧ (k + 1) % 2 = 1) then 1 else 0)
      + (if decide (Q k ∧ (k + 1) % 2 = 0) then 1 else 0)
      = (if decide (Q k) then 1 else 0) := by
  by_cases hq : Q k
  · by_cases h1 : (k + 1) % 2 = 1
    · rw [decide_eq_true ⟨hq, h1⟩,
          decide_eq_false (fun hc => absurd hc.2 (by omega)),
          decide_eq_true hq]
      rfl
    · have h0 : (k + 1) % 2 = 0 := by omega
      rw [decide_eq_false (fun hc => absurd hc.2 h1),
          decide_eq_true ⟨hq, h0⟩,
          decide_eq_true hq]
      rfl
  · rw [decide_eq_false (fun hc => hq hc.1),
        decide_eq_false (fun hc => hq hc.1),
        decide_eq_false hq]
    rfl

private theorem countP_parity_split_succ (Q : Nat → Prop) [DecidablePred Q] : ∀ (l : List Nat),
    l.countP (fun k => decide (Q k ∧ (k + 1) % 2 = 1))
      + l.countP (fun k => decide (Q k ∧ (k + 1) % 2 = 0))
      = l.countP (fun k => decide (Q k)) := by
  intro l
  induction l with
  | nil => rfl
  | cons a l ih =>
    rw [List.countP_cons, List.countP_cons, List.countP_cons]
    have hpe := parity_elem_succ Q a
    omega

theorem countP_parity_split (Q : Nat → Prop) [DecidablePred Q] : ∀ (l : List Nat),
"""))
R.append(("phiB_odd_dbl tail swap",
"""          rw [h2, hpar] at h1
          rw [h1]
          exact And.comm))]
  rw [countP_parity_split]
  rfl
""",
"""          rw [h2, hpar] at h1
          rw [h1]
          exact And.comm))]
  rw [countP_parity_split_succ]
  rfl
"""))

# 7. phiB_two_pow_mul: ih is already the equation (induction reverted ha/hm)
R.append(("two_pow_mul ih",
"""      rw [hEq, phiB_even_dbl hEven hPos, ih (by omega) hm]
""",
"""      rw [hEq, phiB_even_dbl hEven hPos, ih]
"""))

# 8. phiB_le: countP_le_length has no explicit binders in this toolchain
R.append(("phiB_le",
"""    List.countP_le_length _
""",
"""    List.countP_le_length
"""))

# 9. phiB_even_of_odd: range_succ via rw (not exact — binder is implicit);
#    hlast without rewriting under the decide (the Coprime-instance motive kill)
R.append(("hstrip hr",
"""    have hr : List.range x = List.range (x-1) ++ [x-1] := by
      rw [show x = (x-1)+1 from by omega]
      exact List.range_succ (x-1)
""",
"""    have hr : List.range x = List.range (x-1) ++ [x-1] := by
      have hx : x = (x-1) + 1 := by omega
      conv =>
        lhs
        rw [hx, List.range_succ]
"""))
R.append(("hstrip hlast",
"""    have hlast : decide (Nat.gcd ((x-1) + 1) x = 1) = false := by
      have : Nat.gcd ((x-1)+1) x = x := by omega
      rw [this]
      have : x ≠ 1 := by omega
      exact decide_eq_false (by intro h1; rw [h1] at this; exact absurd this (by omega))
""",
"""    have hlast : decide (Nat.gcd (x-1+1) x = 1) = false := by
      have hne : ¬ (Nat.gcd (x-1+1) x = 1) := by
        intro h1
        have hg : Nat.gcd (x-1+1) x = x := by
          have hx : x - 1 + 1 = x := by omega
          rw [hx]
          exact Nat.gcd_self x
        rw [h1] at hg
        exact absurd hg (by omega)
      exact decide_eq_false hne
"""))

# 10. gstep_3: the rw chain closes the goal by defeq-rfl; the trailing ring
#     errors "No goals to be solved" — delete it
R.append(("gstep_3 ring",
"""    rw [h1, Nat.pow_add, show 2^3 = 8 from by decide]
  rw [hexp]
  ring

theorem gstep_5""",
"""    rw [h1, Nat.pow_add, show 2^3 = 8 from by decide]
  rw [hexp]

theorem gstep_5"""))

# 11. gF_add: the induction hypothesis must be ∀-generalized over x
R.append(("gF_add",
"""theorem gF_add (i j x : Nat) : gF (i + j) x = gF i (gF j x) := by
  induction j with
  | zero => simp only [Nat.add_zero, gF]
  | succ j ih =>
    have h1 : i + (j + 1) = (i + j) + 1 := by omega
    have h2 : gF ((i + j) + 1) x = gF (i + j) (gstep x) := rfl
    have h3 : gF (j + 1) x = gF j (gstep x) := rfl
    rw [h1, h2, ih, ← h3]
""",
"""theorem gF_add (i j x : Nat) : gF (i + j) x = gF i (gF j x) := by
  revert x
  induction j with
  | zero => intro x; simp only [Nat.add_zero, gF]
  | succ j ih =>
    intro x
    have h1 : i + (j + 1) = (i + j) + 1 := by omega
    have h2 : gF ((i + j) + 1) x = gF (i + j) (gstep x) := rfl
    have h3 : gF (j + 1) x = gF j (gstep x) := rfl
    rw [h1, h2, ih (gstep x), ← h3]
"""))

# 12. inFAM_gstep m=3: the exponent a+2-1 is not syntactically ?a+1
R.append(("inFAM_gstep m3",
"""      have htp := gstep_two_pow (a+2) (by omega)
      rw [htp, two_pow_succ_add]
      ring
""",
"""      have htp := gstep_two_pow (a+2) (by omega)
      rw [htp, show a + 2 - 1 = a + 1 from by omega, two_pow_succ_add]
      ring
"""))

# 13. gF_two_pow zero-case: the def-unfold residues close by rfl
R.append(("gF_two_pow zero",
"""  | zero =>
    constructor
    · rw [Nat.mul_zero, Nat.pow_zero, Nat.one_mul]
    · rw [Nat.mul_zero, Nat.pow_zero, Nat.one_mul]
""",
"""  | zero =>
    constructor
    · rw [Nat.mul_zero, Nat.pow_zero, Nat.one_mul]; rfl
    · rw [Nat.mul_zero, Nat.pow_zero, Nat.one_mul]; rfl
"""))

# 15. erdos411_doubling: the conv-block's `rhs =>` parse error; the k-atom
#     rewrite self-references (k/2) — restructure via fresh q + subst
R.append(("doubling even",
"""  rcases (show k % 2 = 0 ∨ k % 2 = 1 from by omega) with hpar | hpar
  · -- k even: k = 2 * (k/2)
    obtain ⟨hE, hF⟩ := gF_two_pow x hx ((k/2)+1)
    obtain ⟨hC, hD⟩ := gF_two_pow x hx (k/2)
    conv =>
      rhs => rw [show k = 2*(k/2) from by omega]
      lhs => rw [show k + 2 = 2*((k/2)+1) from by omega]
    rw [hE, hC, two_pow_succ_add]
    ring
  · -- k odd: gstep (2^(q+1)·x) = 2·gstep (2^q·x) by the commutation law
    obtain ⟨a, m, ha, hm, hm1, hxe⟩ := hx
    have hfam : inFAM (2^(k/2) * x) := by
      refine ⟨a + k/2, m, by omega, hm, ?_, ?_⟩
      · intro h; subst h; omega
      · rw [hxe, ← Nat.mul_assoc, ← Nat.pow_add]
        congr 1 <;> omega
    have hgsd : gstep (2 * (2^(k/2) * x)) = 2 * gstep (2^(k/2) * x) :=
      gstep_dbl_comm hfam
    obtain ⟨hE, hF⟩ := gF_two_pow x hx ((k/2)+1)
    obtain ⟨hC, hD⟩ := gF_two_pow x hx (k/2)
    conv =>
      rhs => rw [show k = 2*(k/2) + 1 from by omega]
      lhs => rw [show k + 2 = 2*((k/2)+1) + 1 from by omega]
    rw [hF, hD, two_pow_succ_add, Nat.mul_assoc]
    exact hgsd
""",
"""  rcases (show k % 2 = 0 ∨ k % 2 = 1 from by omega) with hpar | hpar
  · -- k even: k = 2 * q with q fresh (the k/2 self-reference killed the rw)
    obtain ⟨q, hq⟩ : ∃ q, k = 2 * q := ⟨k / 2, by omega⟩
    subst hq
    obtain ⟨hE, hF⟩ := gF_two_pow x hx (q+1)
    obtain ⟨hC, hD⟩ := gF_two_pow x hx q
    rw [show 2 * q + 2 = 2 * (q + 1) from by omega, hE, hC, two_pow_succ_add]
    ring
  · -- k odd: k = 2 * q + 1 with q fresh
    obtain ⟨q, hq⟩ : ∃ q, k = 2 * q + 1 := ⟨k / 2, by omega⟩
    subst hq
    obtain ⟨a, m, ha, hm, hm1, hxe⟩ := hx
    have hfam : inFAM (2^q * x) := by
      refine ⟨a + q, m, by omega, hm, ?_, ?_⟩
      · intro h; subst h; omega
      · rw [hxe, ← Nat.mul_assoc, show 2^q * 2^a = 2^(a + q) from by
          rw [Nat.pow_add]; ring]
    have hgsd : gstep (2 * (2^q * x)) = 2 * gstep (2^q * x) :=
      gstep_dbl_comm hfam
    obtain ⟨hE, hF⟩ := gF_two_pow x hx (q+1)
    obtain ⟨hC, hD⟩ := gF_two_pow x hx q
    rw [show 2 * q + 1 + 2 = 2 * (q + 1) + 1 from by omega, hF, hD,
        two_pow_succ_add]
    exact hgsd
"""))

# 14. gF_two_pow succ hfam: powers are not omega-fragment; commute the exponent
R.append(("hfam pow commute",
"""      · rw [hxe, ← Nat.mul_assoc, ← Nat.pow_add]
        congr 1 <;> omega
""",
"""      · rw [hxe, ← Nat.mul_assoc, show 2^j * 2^a = 2^(a + j) from by
          rw [Nat.pow_add]; ring]
"""))

# 16. erdos411_parity n=1: cases (j-1) swallows the branch condition — the
#     zero-branch goal is false; split via explicit disjunction + k-inline
R.append(("erdos411_parity n=1",
"""    have hodd : ∀ j, 2 ≤ j → (gF j 1) % 2 = 1 := by
      intro j hj
      have h1 : gF j 1 = gF (j-1) 2 := by
        cases j with
        | zero => omega
        | succ j' =>
            have h2 : gF (j'+1) 1 = gF j' 2 := gF_one_step j'
            rw [h2]
            rfl
      have h3 : (gF (j-1) 2) % 2 = 1 := by
        cases (j-1) with
        | zero => omega
        | succ j'' =>
            have h4 : gF (j''+1) 2 = gF j'' 3 := gF_two_step j''
            rw [h4]
            exact gF_odd_of_odd (by decide) (by decide) j''
      rw [h1, h3]
    have k := K + 2
    have h1 := hodd (k + r) (by omega)
    have := hall k (by omega)
    rw [this] at h1
    omega
""",
"""    have hodd : ∀ j, 2 ≤ j → (gF j 1) % 2 = 1 := by
      intro j hj
      have h1 : gF j 1 = gF (j-1) 2 := by
        cases j with
        | zero => omega
        | succ j' =>
            have h2 : gF (j'+1) 1 = gF j' 2 := gF_one_step j'
            rw [h2]
            rfl
      have h3 : (gF (j-1) 2) % 2 = 1 := by
        rcases (show j - 1 = 0 ∨ 1 ≤ j - 1 from by omega) with h0 | hge
        · omega
        · have hs : j - 1 = (j - 2) + 1 := by omega
          have h4 : gF ((j-2) + 1) 2 = gF (j-2) 3 := gF_two_step (j-2)
          rw [← h4, hs]
          exact gF_odd_of_odd (by decide) (by decide) (j-2)
      rw [h1, h3]
    have h1 := hodd (K + 2 + r) (by omega)
    have := hall (K + 2) (by omega)
    rw [this] at h1
    omega
"""))

# 17. erdos411_two: k was let-bound (omega opaque); inline
R.append(("erdos411_two k",
"""  have k := K + 1
  have h1 := hodd (k + r) (by omega)
  have := hall k (by omega)
  rw [this] at h1
  omega
""",
"""  have h1 := hodd (K + 1 + r) (by omega)
  have := hall (K + 1) (by omega)
  rw [this] at h1
  omega
"""))

# 18. two_pow_mul_exists: the bullet indentation defect (parser death)
R.append(("two_pow_mul_exists indent",
"""  · have hy : i / 2 < i := Nat.div_lt_self (by omega) (by decide)
      have hypos : 0 < i / 2 := by omega
    obtain ⟨a, m, hm, hme⟩ := ih (i / 2) hy hypos
""",
"""  · have hy : i / 2 < i := Nat.div_lt_self (by omega) (by decide)
    have hypos : 0 < i / 2 := by omega
    obtain ⟨a, m, hm, hme⟩ := ih (i / 2) hy hypos
"""))

# 19. oddPF_eq: revert-explicit + the (a-1)+1 exponent show
R.append(("oddPF_eq",
"""theorem oddPF_eq : ∀ (x a m f : Nat), x = 2^a * m → m % 2 = 1 → a ≤ f →
    oddPF f x = m := by
  intro x a m f
  induction f generalizing x a with
""",
"""theorem oddPF_eq : ∀ (x a m f : Nat), x = 2^a * m → m % 2 = 1 → a ≤ f →
    oddPF f x = m := by
  intro x a m f
  revert x
  revert a
  induction f with
"""))
R.append(("oddPF_eq cases",
"""  | zero =>
      intro hxe hm haf
""",
"""  | zero =>
      intro x a hxe hm haf
"""))
R.append(("oddPF_eq succ cases",
"""  | succ f ih =>
      intro hxe hm haf
""",
"""  | succ f ih =>
      intro x a hxe hm haf
"""))
R.append(("oddPF_eq hx2",
"""        have hx2 : x = 2 * (2^(a-1) * m) := by
          rw [← Nat.mul_assoc, ← Nat.pow_succ, hsucc]
          exact hxe
""",
"""        have hx2 : x = 2 * (2^(a-1) * m) := by
          rw [← Nat.mul_assoc, ← Nat.pow_succ, show (a-1) + 1 = a from by omega]
          exact hxe
"""))
# delete the now-unused hsucc line
R.append(("oddPF_eq hsucc del",
"""      · have hsucc : Nat.succ (a-1) = a := by omega
        have hx2 : x = 2 * (2^(a-1) * m) := by
""",
"""      · have hx2 : x = 2 * (2^(a-1) * m) := by
"""))

# 20. oddPF_fac: same revert-explicit restructure
R.append(("oddPF_fac",
"""theorem oddPF_fac : ∀ (v f : Nat), 0 < v → v < 2^f →
    ∃ i m, m % 2 = 1 ∧ v = 2^i * m ∧ oddPF f v = m := by
  intro v f
  induction f generalizing v with
  | zero => intro v hv hlt; omega
  | succ f ih =>
      intro v hv hlt
""",
"""theorem oddPF_fac : ∀ (v f : Nat), 0 < v → v < 2^f →
    ∃ i m, m % 2 = 1 ∧ v = 2^i * m ∧ oddPF f v = m := by
  intro v f
  revert v
  induction f with
  | zero => intro v hv hlt; omega
  | succ f ih =>
      intro v hv hlt
"""))

# 21. oddPF_bound_ok: pow_le_pow_right's first explicit binder is the proof
R.append(("pow_le_pow_right",
"""    have hpow : (2:Nat)^64 ≤ 2^a := Nat.pow_le_pow_right 2 h65
""",
"""    have hpow : (2:Nat)^64 ≤ 2^a := Nat.pow_le_pow_right (by omega)
"""))

text = BLOB
applied = []
for label, old, new in R:
    n = text.count(old)
    if n != 1:
        print(f"FAIL [{label}]: {n} occurrences")
        sys.exit(1)
    text = text.replace(old, new)
    applied.append(label)

# 22. closure_all: insert the closureChunk unfold before every all_eq_true rw
import re
pat = re.compile(r"(    have h := cl_\w+\n)(    rw \[List\.all_eq_true\] at h\n)")
text, n22 = pat.subn(r"\1    simp only [closureChunk] at h\n\2", text)
applied.append(f"closure_all unfold x{n22}")
if n22 == 0:
    print("FAIL [closure_all]: 0 insertions"); sys.exit(1)

# also: the Mathlib countP_congr at the phiB_even_of_odd tail — replace with
# the local (signature-safe) form
old_cc = """  rw [List.countP_congr (p := fun k => decide (Nat.gcd (h + k + 1) x = 1))
        (q := fun k => decide (Nat.gcd (h - 1 - k + 1) x = 1))
        (by intro k _
            have hck : h + k + 1 ≤ x := by omega
            have hpar : Nat.gcd (x - (h + k + 1)) x = Nat.gcd (h + k + 1) x :=
              gcd_partners (h + k + 1) x hck
            have hEq : x - (h + k + 1) = h - k := by omega
            rw [hEq] at hpar
            exact decCongr (by rw [hpar]))]"""
new_cc = """  rw [countP_congr_local (p := fun k => decide (Nat.gcd (h + k + 1) x = 1))
        (q := fun k => decide (Nat.gcd (h - 1 - k + 1) x = 1))
        (fun k _ =>
            have hck : h + k + 1 ≤ x := by omega
            have hpar : Nat.gcd (x - (h + k + 1)) x = Nat.gcd (h + k + 1) x :=
              gcd_partners (h + k + 1) x hck
            have hEq : x - (h + k + 1) = h - k := by omega
            decCongr (by rw [hEq] at hpar; rw [hpar]))]"""
ncc = text.count(old_cc)
if ncc == 1:
    text = text.replace(old_cc, new_cc)
    applied.append("phiB_even_of_odd congr-local")
elif ncc == 0:
    print("WARN: countP_congr block not found verbatim (checking)")
else:
    print(f"FAIL [congr]: {ncc} occurrences"); sys.exit(1)

with open('problem411-iterated-totient/Erdos411.lean', 'w') as f:
    f.write(text)

m1 = hashlib.md5(open('problem411-iterated-totient/Erdos411.lean','rb').read()).hexdigest()
m2 = hashlib.md5(open('problem411-iterated-totient/Erdos411.lean','rb').read()).hexdigest()
m3 = hashlib.md5(open('problem411-iterated-totient/Erdos411.lean','rb').read()).hexdigest()
print(f"APPLIED {len(applied)} fix families: {applied}")
print(f"lines: {text.count(chr(10))}, md5 stable: {m1 == m2 == m3} ({m1[:12]})")
assert 'sorry' not in text.replace('sorryAx', '')
print("zero sorry: OK")
