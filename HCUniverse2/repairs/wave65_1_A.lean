/-! ## §2 The block rotation on the coordinate indices -/

/-- **THE BLOCK ROTATION FUNCTION** — `a ↦ (a + 2) mod 2M`: rotates the `M`
coordinate blocks cyclically (block `i` ↦ block `i + 1 mod M`).  The corpus
pattern is `cyclicSucc` (GSTSingularCohomologyMaps.lean:244). -/
def blockRotFn (M : ℕ) : Fin (2 * M) → Fin (2 * M) := fun a =>
  ⟨(a.val + 2) % (2 * M),
    Nat.mod_lt _ (Nat.lt_of_le_of_lt (Nat.zero_le a.val) a.isLt)⟩

/-- The inverse rotation `a ↦ (a + (2M − 2)) mod 2M`. -/
def blockRotInvFn (M : ℕ) : Fin (2 * M) → Fin (2 * M) := fun a =>
  ⟨(a.val + (2 * M - 2)) % (2 * M),
    Nat.mod_lt _ (Nat.lt_of_le_of_lt (Nat.zero_le a.val) a.isLt)⟩

theorem blockRotInvFn_fn (M : ℕ) (a : Fin (2 * M)) :
    blockRotInvFn M (blockRotFn M a) = a := by
  have ha : a.val < 2 * M := a.isLt
  apply Fin.ext
  show ((a.val + 2) % (2 * M) + (2 * M - 2)) % (2 * M) = a.val
  rw [Nat.mod_add_mod]
  have hadd : a.val + 2 + (2 * M - 2) = a.val + 2 * M := by omega
  rw [hadd, Nat.add_mod_right]
  exact Nat.mod_eq_of_lt ha

theorem blockRotFn_invFn (M : ℕ) (a : Fin (2 * M)) :
    blockRotFn M (blockRotInvFn M a) = a := by
  have ha : a.val < 2 * M := a.isLt
  apply Fin.ext
  show ((a.val + (2 * M - 2)) % (2 * M) + 2) % (2 * M) = a.val
  rw [Nat.mod_add_mod]
  have hadd : a.val + (2 * M - 2) + 2 = a.val + 2 * M := by omega
  rw [hadd, Nat.add_mod_right]
  exact Nat.mod_eq_of_lt ha

/-- **THE BLOCK-ROTATION EQUIV** on the coordinate indices. -/
def blockRot (M : ℕ) : Fin (2 * M) ≃ Fin (2 * M) where
  toFun := blockRotFn M
  invFun := blockRotInvFn M
  left_inv := blockRotInvFn_fn M
  right_inv := blockRotFn_invFn M

theorem blockRot_val (M : ℕ) (a : Fin (2 * M)) :
    (blockRot M a).val = (a.val + 2) % (2 * M) := rfl

/-- The function-level value bridge (the rotation function applied). -/
theorem blockRotFn_val (M : ℕ) (a : Fin (2 * M)) :
    (blockRotFn M a).val = (a.val + 2) % (2 * M) := rfl

/-- The iterate law: `n` rotations shift the index by `2n`. -/
theorem blockRotFn_iterate_val (M : ℕ) (n : ℕ) (a : Fin (2 * M)) :
    ((blockRotFn M)^[n] a).val = (a.val + 2 * n) % (2 * M) := by
  induction n generalizing a with
  | zero =>
      show a.val = (a.val + 2 * 0) % (2 * M)
      exact (Nat.mod_eq_of_lt a.isLt).symm
  | succ n ih =>
      rw [Function.iterate_succ_apply', blockRotFn_val, ih a, Nat.mod_add_mod]
      have hA : a.val + 2 * n + 2 = a.val + 2 * (n + 1) := by omega
      rw [hA]

/-- **THE M-TH POWER IS THE IDENTITY** — the cycle law at the index level. -/
theorem blockRotFn_pow (M : ℕ) (a : Fin (2 * M)) :
    (blockRotFn M)^[M] a = a := by
  apply Fin.ext
  have h := blockRotFn_iterate_val M M a
  rw [Nat.add_mod_right, Nat.mod_eq_of_lt a.isLt] at h
  exact h

/-- The function-level form of the cycle law. -/
theorem blockRotFn_pow' (M : ℕ) : (blockRotFn M)^[M] = id :=
  funext (blockRotFn_pow M)

/-- The two faces of the rotation value: the no-wrap and the wrap case,
with their wrap conditions (the case lemma carries its bound — required
for the same-block preservation below). -/
theorem blockRot_val_cases (M : ℕ) (c : Fin (2 * M)) :
    ((blockRot M c).val = c.val + 2 ∧ c.val + 2 < 2 * M) ∨
    ((blockRot M c).val = c.val + 2 - 2 * M ∧ 2 * M ≤ c.val + 2) := by
  have hc := c.isLt
  rcases Nat.lt_or_ge (c.val + 2) (2 * M) with h | h
  · exact Or.inl ⟨Nat.mod_eq_of_lt h, h⟩
  · refine Or.inr ⟨?_, h⟩
    have hX : c.val + 2 - 2 * M + 2 * M = c.val + 2 := by omega
    have hlt : c.val + 2 - 2 * M < 2 * M := by omega
    have hmod : (c.val + 2 - 2 * M + 2 * M) % (2 * M) = c.val + 2 - 2 * M := by
      rw [Nat.add_mod_right]
      exact Nat.mod_eq_of_lt hlt
    have hbr : (c.val + 2) % (2 * M) =
        (c.val + 2 - 2 * M + 2 * M) % (2 * M) := by rw [hX]
    show (c.val + 2) % (2 * M) = c.val + 2 - 2 * M
    rw [hbr, hmod]

/-- **SAME-BLOCK PRESERVATION** — the block structure is preserved in both
directions (the iff, not the equality: the rotation moves every block). -/
theorem blockRot_sameBlock (M : ℕ) (a b : Fin (2 * M)) :
    (blockRot M a).val / 2 = (blockRot M b).val / 2 ↔ a.val / 2 = b.val / 2 := by
  have ha := a.isLt
  have hb := b.isLt
  rcases blockRot_val_cases M a with ⟨ha', ha''⟩ | ⟨ha', ha''⟩ <;>
    rcases blockRot_val_cases M b with ⟨hb', hb''⟩ | ⟨hb', hb''⟩ <;>
    simp only [ha', hb'] <;> constructor <;> intro h <;> omega

/-- The symm version, for free from the iff and `Equiv.apply_symm_apply`. -/
theorem blockRot_symm_sameBlock (M : ℕ) (a b : Fin (2 * M)) :
    ((blockRot M).symm a).val / 2 = ((blockRot M).symm b).val / 2 ↔
      a.val / 2 = b.val / 2 := by
  have ea : blockRot M ((blockRot M).symm a) = a :=
    Equiv.apply_symm_apply (blockRot M) a
  have eb : blockRot M ((blockRot M).symm b) = b :=
    Equiv.apply_symm_apply (blockRot M) b
  constructor
  · intro h
    have h2 := (blockRot_sameBlock M ((blockRot M).symm a) ((blockRot M).symm b)).mpr h
    rwa [ea, eb] at h2
  · intro h
    have h2 : (blockRot M ((blockRot M).symm a)).val / 2
        = (blockRot M ((blockRot M).symm b)).val / 2 := by
      rw [ea, eb]
      exact h
    exact (blockRot_sameBlock M ((blockRot M).symm a) ((blockRot M).symm b)).mp h2
