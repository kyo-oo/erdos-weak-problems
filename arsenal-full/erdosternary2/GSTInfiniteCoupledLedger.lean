import GSTInfiniteBadTransport

set_option maxRecDepth 1000000
set_option maxHeartbeats 10000000

namespace GSTV2

/-!
# Coupled Past/Future information ledger

The live coupled state is only the unconsumed Future coordinate.  This module
adds the emitted Past explicitly, so a support horizon can never be mistaken
for destruction of information.

For a seeded x4 stream `(D,X)`, the fixed information mass `D + 4X` is split at
every natural depth K into

    Past(K) + 3^K * Future(K).

For a coupled parent/child state, the two ledgers synchronize exactly:

    parentPast(K) + 3^K * W(K)
      = W(0) + A * childPast(K).

Thus the finite residue W(K), the emitted parent information, and the emitted
child information are three representations of one conserved all-depth
packet.
-/

/-- Information emitted below depth K by a seeded x4 stream, in its original
ternary scale. -/
def seededPast (D X K : Nat) : Nat :=
  (D + 4 * (X % 3^K)) % 3^K

/-- Exact seeded Past/Future conservation at every natural depth. -/
theorem seeded_mass_past_future
    (D X K : Nat) :
    D + 4*X =
      seededPast D X K +
        3^K * (affineCarry D X K + 4*(X / 3^K)) := by
  let P := 3^K
  let H := D + 4*(X % P)
  have hP : 0 < P := by
    dsimp [P]
    exact Nat.pow_pos (by decide)
  have hX : X = X % P + P*(X/P) := by
    have h := Nat.mod_add_div X P
    omega
  have hH : H = H % P + P*(H/P) := by
    have h := Nat.mod_add_div H P
    omega
  calc
    D + 4*X = D + 4*(X % P + P*(X/P)) :=
      congrArg (fun Y : Nat => D + 4*Y) hX
    _ = H + P*(4*(X/P)) := by
      dsimp [H]
      ring
    _ = (H % P + P*(H/P)) + P*(4*(X/P)) :=
      congrArg (fun Y : Nat => Y + P*(4*(X/P))) hH
    _ = H % P + P*((H/P) + 4*(X/P)) := by ring
    _ = seededPast D X K +
        3^K * (affineCarry D X K + 4*(X / 3^K)) := by
      rfl

/-- Generic child carry realization, valid for an arbitrary initial child
seed, not only seed zero. -/
theorem coupledOrbit_childCarry_affine_exact
    (A : Nat) (initial : CoupledState) :
    ∀ K,
      (coupledOrbit A initial K).childCarry =
        affineCarry initial.childCarry initial.childTail K := by
  intro K
  induction K with
  | zero =>
      simp [coupledOrbit, affineCarry, Nat.mod_one]
  | succ K ih =>
      rw [coupledOrbit]
      change cellNextCarry (coupledOrbit A initial K).childCarry
          ((coupledOrbit A initial K).childTail % 3) = _
      rw [ih, affineCarry_forward]
      congr 1
      rw [coupledOrbit_childTail_exact A initial K]
      rfl

/-- The invariant is equivalently an exact equation for the complete live
Future words, not just their low offsets. -/
theorem coupled_state_full_future_equation
    (A : Nat) (st : CoupledState)
    (hInv : CoupledInvariant A st) :
    st.parentSeed + 4*(st.parentWord A) =
      st.childResidue + A*(st.childCarry + 4*st.childTail) := by
  rcases hInv with ⟨hEq, _⟩
  unfold CoupledState.parentWord
  calc
    st.parentSeed + 4*(st.parentOffset + A*st.childTail) =
        (st.parentSeed + 4*st.parentOffset) + 4*A*st.childTail := by ring
    _ = (st.childResidue + A*st.childCarry) + 4*A*st.childTail := by rw [hEq]
    _ = st.childResidue + A*(st.childCarry + 4*st.childTail) := by ring

/-- Closed-form parent Past of the initial represented affine word. -/
def CoupledState.parentPast (A : Nat) (st : CoupledState) (K : Nat) : Nat :=
  seededPast st.parentSeed (st.parentWord A) K

/-- Closed-form child Past. -/
def CoupledState.childPast (st : CoupledState) (K : Nat) : Nat :=
  seededPast st.childCarry st.childTail K

/-- The central all-depth synchronization law.  It explicitly records emitted
information on both sides, so no quotient becoming zero can erase the packet.
The only hypotheses are positivity of A and the exact initial coupled
invariant. -/
theorem coupledOrbit_past_synchronization
    (A : Nat) (initial : CoupledState)
    (hA : 0 < A) (h0 : CoupledInvariant A initial) :
    ∀ K,
      initial.parentPast A K +
          3^K * (coupledOrbit A initial K).childResidue =
        initial.childResidue + A * initial.childPast K := by
  intro K
  let st := coupledOrbit A initial K
  have hInvK : CoupledInvariant A st :=
    coupledOrbit_invariant_all A initial hA h0 K
  have hFullK := coupled_state_full_future_equation A st hInvK
  have hFull0 := coupled_state_full_future_equation A initial h0

  have hParent := seeded_mass_past_future
    initial.parentSeed (initial.parentWord A) K
  have hChild := seeded_mass_past_future
    initial.childCarry initial.childTail K

  have hParentSeed :
      affineCarry initial.parentSeed (initial.parentWord A) K =
        st.parentSeed := by
    simpa [st] using (coupledOrbit_parentSeed_exact A initial K).symm
  have hParentTail :
      initial.parentWord A / 3^K = st.parentWord A := by
    simpa [st] using (coupledOrbit_parentWord_exact A initial K).symm
  have hChildSeed :
      affineCarry initial.childCarry initial.childTail K =
        st.childCarry := by
    simpa [st] using (coupledOrbit_childCarry_affine_exact A initial K).symm
  have hChildTail :
      initial.childTail / 3^K = st.childTail := by
    simpa [st] using (coupledOrbit_childTail_exact A initial K).symm

  rw [hParentSeed, hParentTail] at hParent
  rw [hChildSeed, hChildTail] at hChild
  rw [hFullK] at hParent
  rw [hFull0] at hParent
  rw [hChild] at hParent

  have hCancel :
      (initial.childResidue + A * initial.childPast K) +
          3^K * A * (st.childCarry + 4*st.childTail) =
        (initial.parentPast A K + 3^K * st.childResidue) +
          3^K * A * (st.childCarry + 4*st.childTail) := by
    calc
      (initial.childResidue + A * initial.childPast K) +
          3^K * A * (st.childCarry + 4*st.childTail) =
        initial.childResidue +
          A * (initial.childPast K +
            3^K * (st.childCarry + 4*st.childTail)) := by ring
      _ = initial.parentPast A K +
          3^K * (st.childResidue +
            A * (st.childCarry + 4*st.childTail)) := by
        simpa [CoupledState.parentPast, CoupledState.childPast] using hParent
      _ = (initial.parentPast A K + 3^K * st.childResidue) +
          3^K * A * (st.childCarry + 4*st.childTail) := by ring

  have hCore :
      initial.childResidue + A * initial.childPast K =
        initial.parentPast A K + 3^K * st.childResidue :=
    Nat.add_right_cancel hCancel
  simpa [st] using hCore.symm

/-- The same synchronization packaged as an all-Nat controller. -/
structure InfiniteCoupledLedger
    (A : Nat) (initial : CoupledState) : Prop where
  coupled : InfiniteCoupledControl A initial
  pastSynchronized : ∀ K,
    initial.parentPast A K +
        3^K * (coupledOrbit A initial K).childResidue =
      initial.childResidue + A * initial.childPast K

/-- Every exact coupled controller carries the stronger Past/Future ledger. -/
theorem infinite_coupled_ledger
    (A : Nat) (initial : CoupledState)
    (hA : 0 < A) (h0 : CoupledInvariant A initial) :
    InfiniteCoupledLedger A initial := by
  exact {
    coupled := infinite_coupled_control A initial hA h0
    pastSynchronized := coupledOrbit_past_synchronization A initial hA h0
  }

end GSTV2
