import GSTGraphV2Ontological

/-!
# GST CLASSICAL HODGE — ONTOLOGICAL WINDOW REVERSE EXISTENCE

The original Hodge/de Rham absorption proposed a very strong reverse-window
statement: positivity of an entire GST production window should force its
preselected top-left source cell to be Happy.  The finite current calculus
already proves a different statement directly and without a postulate:

* if every physical cell in a horizontal row is non-Happy, its reverse
  ontological current is nonpositive;
* if every physical cell in a finite two-dimensional window is non-Happy,
  the whole base-three weighted ontological prefix is nonpositive;
* therefore every strictly positive finite GST window contains at least one
  genuine Happy cell.

This is the correct reverse-existence theorem.  It is exactly the form needed
by later recoordination: discover a live Happy cell first, then move the
observation frame to it, rather than assuming the live cell was already at a
fixed distinguished boundary position.
-/

set_option maxHeartbeats 30000000
set_option maxRecDepth 1000000

noncomputable section

namespace GSTClassicalHodgeOntologicalWindowReverseExistence

open GST2DMixedEmergence
open GSTU2DEventTransport
open GSTGraphV2InfiniteControl
open GSTGraphV2Ontological

/-- A finite physical horizontal row containing no Happy cell has
nonpositive reverse ontological current. -/
theorem reverseOntCode_nonpositive_of_all_bad
    (C d : Nat → Nat) : ∀ N : Nat,
    (∀ t, t < N → C t < 4) →
    (∀ t, t < N → d t < 3) →
    (∀ t, t < N → ¬ HappyCell (C t) (d t)) →
    reverseOntCode C d N ≤ 0 := by
  intro N
  induction N with
  | zero =>
      intro hC hd hbad
      simp [reverseOntCode]
  | succ N ih =>
      intro hC hd hbad
      have ih' := ih
        (fun t ht => hC t (by omega))
        (fun t ht => hd t (by omega))
        (fun t ht => hbad t (by omega))
      have hlast := ontDensity_nonpositive_of_not_happy
        (C N) (d N)
        (hC N (by omega))
        (hd N (by omega))
        (hbad N (by omega))
      rw [reverseOntCode]
      omega

/-- Contrapositive form: positive reverse current in a physical row detects
at least one actual Happy cell of that row. -/
theorem reverseOntCode_positive_exists_happy
    (C d : Nat → Nat)
    (N : Nat)
    (hC : ∀ t, t < N → C t < 4)
    (hd : ∀ t, t < N → d t < 3)
    (hpos : 0 < reverseOntCode C d N) :
    ∃ t : Nat, t < N ∧ HappyCell (C t) (d t) := by
  by_contra hnone
  have hbad : ∀ t, t < N → ¬ HappyCell (C t) (d t) := by
    intro t ht hhappy
    apply hnone
    exact ⟨t, ht, hhappy⟩
  have hnon := reverseOntCode_nonpositive_of_all_bad C d N hC hd hbad
  omega

/-- If every physical cell in a finite two-dimensional window is non-Happy,
then the complete base-three weighted ontological prefix is nonpositive. -/
theorem weightedOntPrefix_nonpositive_of_all_bad
    (C d : Nat → Nat → Nat)
    (N : Nat) : ∀ K : Nat,
    (∀ t p, t < N → p < K → C t p < 4) →
    (∀ t p, t < N → p < K → d t p < 3) →
    (∀ t p, t < N → p < K → ¬ HappyCell (C t p) (d t p)) →
    weightedOntPrefix C d N K ≤ 0 := by
  intro K
  induction K with
  | zero =>
      intro hC hd hbad
      simp [weightedOntPrefix]
  | succ K ih =>
      intro hC hd hbad
      have ih' := ih
        (fun t p ht hp => hC t p ht (by omega))
        (fun t p ht hp => hd t p ht (by omega))
        (fun t p ht hp => hbad t p ht (by omega))
      have hrow := reverseOntCode_nonpositive_of_all_bad
        (fun t => C t K) (fun t => d t K) N
        (fun t ht => hC t K ht (by omega))
        (fun t ht => hd t K ht (by omega))
        (fun t ht => hbad t K ht (by omega))
      have hpow : (0 : Int) ≤ (((3^K : Nat) : Int)) := by positivity
      have hweighted :
          (((3^K : Nat) : Int)) *
              reverseOntCode (fun t => C t K) (fun t => d t K) N ≤ 0 :=
        mul_nonpos_of_nonneg_of_nonpos hpow hrow
      rw [weightedOntPrefix]
      exact add_nonpos ih' hweighted

/-- **REVERSE ONTOLOGICAL WINDOW EXISTENCE.**
Strict positivity of a finite physical GST window forces at least one Happy
cell somewhere in that window.  No reverse-window postulate is used. -/
theorem weightedOntPrefix_positive_exists_happy
    (C d : Nat → Nat → Nat)
    (N K : Nat)
    (hC : ∀ t p, t < N → p < K → C t p < 4)
    (hd : ∀ t p, t < N → p < K → d t p < 3)
    (hpos : 0 < weightedOntPrefix C d N K) :
    ∃ p : Nat, p < K ∧ ∃ t : Nat, t < N ∧ HappyCell (C t p) (d t p) := by
  by_contra hnone
  have hbad :
      ∀ t p, t < N → p < K → ¬ HappyCell (C t p) (d t p) := by
    intro t p ht hp hhappy
    apply hnone
    exact ⟨p, hp, t, ht, hhappy⟩
  have hnon := weightedOntPrefix_nonpositive_of_all_bad
    C d N K hC hd hbad
  omega

/-- Graph-V2 specialization.  A positive shifted production window contains a
genuine Happy graph cell at some horizontal time and some included row. -/
theorem graphOntWindow_positive_exists_happy
    (E N b K : Nat)
    (hpos : 0 < graphOntWindow E N b K) :
    ∃ p : Nat, p < K ∧ ∃ t : Nat, t < N ∧
      HappyCell
        (graph E t (b + p)).seven.carry
        (graph E t (b + p)).seven.digit := by
  unfold graphOntWindow at hpos
  exact weightedOntPrefix_positive_exists_happy
    (fun t p => (graph E t (b + p)).seven.carry)
    (fun t p => (graph E t (b + p)).seven.digit)
    N K
    (fun t p ht hp => graph_carry_lt_four E t (b + p))
    (fun t p ht hp => graph_digit_lt_three E t (b + p))
    hpos

/-- Positive windows therefore admit an explicit live physical witness rather
than merely an existential positive scalar. -/
theorem graphOntWindow_positive_has_live_witness
    (E N b K : Nat)
    (hpos : 0 < graphOntWindow E N b K) :
    Nonempty
      {q : Nat × Nat //
        q.1 < N ∧ q.2 < K ∧
        HappyCell
          (graph E q.1 (b + q.2)).seven.carry
          (graph E q.1 (b + q.2)).seven.digit} := by
  obtain ⟨p, hp, t, ht, hhappy⟩ :=
    graphOntWindow_positive_exists_happy E N b K hpos
  exact ⟨⟨(t,p), ht, hp, hhappy⟩⟩

#check reverseOntCode_nonpositive_of_all_bad
#check reverseOntCode_positive_exists_happy
#check weightedOntPrefix_nonpositive_of_all_bad
#check weightedOntPrefix_positive_exists_happy
#check graphOntWindow_positive_exists_happy
#check graphOntWindow_positive_has_live_witness

#print axioms reverseOntCode_positive_exists_happy
#print axioms weightedOntPrefix_positive_exists_happy
#print axioms graphOntWindow_positive_exists_happy
#print axioms graphOntWindow_positive_has_live_witness

end GSTClassicalHodgeOntologicalWindowReverseExistence
