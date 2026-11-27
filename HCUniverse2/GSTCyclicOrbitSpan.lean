import HCUniverse2.GSTSphereCycleLegs

/-
Copyright (c) 2026. The HC-PROOF campaign. All rights reserved.

# THE CYCLIC-ORBIT SPAN LAW (the positive-dimensional lane's algebra core)

THE PURE-ALGEBRA MODULE of the positive-dimensional law-landing: the Krylov
cyclicity of a family rotated by the M-cycle letter is a fact about the
iterated cyclic predecessor, with no geometry anywhere:

* `cyclicPred_iterate_val` — the closed form: the n-th iterate of the cyclic
  predecessor, started at the 0-th index, is the index `(n * (M - 1)) % M`
  (each step adds `M - 1`, the additive inverse of `1`, modulo `M`);

* `exists_iterate_cyclicPred` — the orbit of the 0-th index under the
  iterated predecessor visits EVERY index (the M-cycle is a single cycle:
  the arithmetic key `(M - t) * (M - 1) = (M - t - 1) * M + t`, discharged
  by `ring` after the successor split, then `Nat.add_mul_mod_self_left`);

* `span_range_cyclicIterate` — consequently, for ANY family `c` in ANY
  ℚ-module, the span of the rotated-orbit family
  `n ↦ c ((cyclicPred M)^[n] 0)` is EXACTLY the span of `c` itself.

This is the engine both live-weight certificates of the positive-dimensional
landing consume: the Krylov orbit of the 0-th honest class under the M-cycle
letter visits every component class (weight 0) and every point class
(weight 1), so the single-letter orbit spans the whole designed fiber.

Honesty ledger: every statement is proved unconditionally.  No `sorry`, no
new axioms, no `native_decide`.  The GitHub CI lane
`gst-positive-dimensional-law-landing.yml` owns the kernel check.
-/

set_option maxHeartbeats 200000000
set_option maxRecDepth 1000000

namespace GSTCyclicOrbitSpan

open GSTSphereCycleLegs

/-! ## §1 The closed form of the iterated cyclic predecessor -/

/-- **THE CLOSED FORM.**  The n-th iterate of the cyclic predecessor, started
at the 0-th index of `Fin M`, has value `(n * (M - 1)) % M`:  each step adds
`M - 1` — the additive inverse of `1` modulo `M` — and the partial sums
reduce modulo `M` by `Nat.mod_add_mod`. -/
theorem cyclicPred_iterate_val (M : ℕ) (hM : 0 < M) (n : ℕ) :
    (((cyclicPred M)^[n] ⟨0, hM⟩ : Fin M)).val = (n * (M - 1)) % M := by
  induction n with
  | zero =>
      rw [Function.iterate_zero_apply]
      simp
  | succ n ih =>
      rw [Function.iterate_succ_apply']
      show ((((cyclicPred M)^[n] ⟨0, hM⟩ : Fin M)).val + (M - 1)) % M = _
      rw [ih, Nat.mod_add_mod]
      have hr : n * (M - 1) + (M - 1) = (n + 1) * (M - 1) := by ring
      rw [hr]

/-! ## §2 The arithmetic key and the orbit surjectivity -/

/-- **THE ARITHMETIC KEY.**  For `t < M`, the product `(M - t) * (M - 1)`
decomposes as `(M - t - 1) * M + t`:  after the successor split
`M - t = w + 1`, both sides expand to the same polynomial (no truncated
subtraction survives the split, so `ring` applies). -/
private theorem arith_key (M t : ℕ) (ht : t < M) :
    (M - t) * (M - 1) = (M - t - 1) * M + t := by
  have hu : 0 < M - t := by omega
  obtain ⟨w, hw⟩ : ∃ w, M - t = w + 1 := ⟨M - t - 1, by omega⟩
  have hM1 : M - 1 = t + w := by omega
  have hMsucc : M = t + w + 1 := by omega
  -- WAVE 60.1: the successor split consumes the `M - t` occurrences (the
  -- wave-60 `hsub`-rewrite could never fire after `hw`); the residual
  -- `w + 1 - 1` closes by the pin's `Nat.add_sub_cancel`, and no truncated
  -- subtraction survives into the `ring` step.
  rw [hw, hM1, hMsucc, Nat.add_sub_cancel]
  ring

/-- **THE ORBIT SURJECTIVITY.**  Every index of `Fin M` lies on the orbit of
the 0-th index under the iterated cyclic predecessor:  the target `t = 0` is
reached in zero steps; a positive target `t` is reached in `M - t` steps,
because the closed form lands on `(M - t) * (M - 1) = (M - t - 1) * M + t`,
which reduces modulo `M` to `t`. -/
theorem exists_iterate_cyclicPred (M : ℕ) (hM : 0 < M) (i : Fin M) :
    ∃ n : ℕ, (cyclicPred M)^[n] ⟨0, hM⟩ = i := by
  rcases Nat.eq_zero_or_pos i.val with h0 | hpos
  · refine ⟨0, ?_⟩
    apply Fin.ext
    show (((cyclicPred M)^[0] ⟨0, hM⟩ : Fin M)).val = i.val
    rw [Function.iterate_zero_apply]
    show (0 : ℕ) = i.val
    omega
  · refine ⟨M - i.val, ?_⟩
    apply Fin.ext
    have hval := cyclicPred_iterate_val M hM (M - i.val)
    rw [hval]
    show ((M - i.val) * (M - 1)) % M = i.val
    -- WAVE 60.2 (run 44624313890): the pin's `Nat.add_mul_mod_self_left`
    -- is `(a + n * b) % n`-spelled (modulus = the product's FIRST factor);
    -- the arithmetic key's `(t + X * M)`-shape — modulus SECOND — is
    -- `Nat.add_mul_mod_self_right`.
    rw [arith_key M i.val i.isLt, Nat.add_comm, Nat.add_mul_mod_self_right]
    exact Nat.mod_eq_of_lt i.isLt

/-! ## §3 The span law -/

/-- **THE CYCLIC-ORBIT SPAN LAW.**  For any family `c` in any ℚ-module, the
span of the rotated-orbit family `n ↦ c ((cyclicPred M)^[n] 0)` is exactly
the span of `c`:  the orbit's range contains every `c i` (the orbit
surjectivity), and every orbit value is a value of `c`.  This is the single
algebraic fact the two live-weight Krylov certificates of the
positive-dimensional landing consume. -/
theorem span_range_cyclicIterate {W : Type*} [AddCommGroup W] [Module ℚ W]
    (M : ℕ) (hM : 0 < M) (c : Fin M → W) :
    Submodule.span ℚ
      (Set.range fun n : ℕ => c ((cyclicPred M)^[n] ⟨0, hM⟩)) =
      Submodule.span ℚ (Set.range c) := by
  apply le_antisymm
  · refine Submodule.span_le.mpr ?_
    rintro w ⟨n, rfl⟩
    exact Submodule.subset_span ⟨(cyclicPred M)^[n] ⟨0, hM⟩, rfl⟩
  · refine Submodule.span_le.mpr ?_
    rintro w ⟨i, rfl⟩
    obtain ⟨n, hn⟩ := exists_iterate_cyclicPred M hM i
    refine Submodule.subset_span ⟨n, ?_⟩
    -- WAVE 60.1: the range-membership goal sits under a beta-redex
    -- (`(fun n => …) n`); the `show` bridge beta-reduces it so the
    -- iterate-pattern surfaces for the rewrite.
    show c ((cyclicPred M)^[n] ⟨0, hM⟩) = c i
    rw [hn]

end GSTCyclicOrbitSpan
