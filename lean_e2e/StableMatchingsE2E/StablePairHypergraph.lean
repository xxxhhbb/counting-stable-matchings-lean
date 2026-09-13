import Mathlib

/-!
# Labeled hypergraphs for the stable-pair theorem

Rotations are labeled choices, so parallel hyperedges must remain distinct.
This file develops the representation-independent part of the stable-pair
argument: matchings of labeled supports, monotonicity under shrinking, and
the injection from antichains when overlapping labels are comparable.
-/

namespace StableMatchingsE2E

/-- A finite labeled hypergraph.  Distinct labels may have identical
supports. -/
structure LabeledHypergraph (V E : Type) where
  support : E → Finset V

namespace LabeledHypergraph

variable {V E : Type} [Fintype E] [DecidableEq E] [DecidableEq V]

/-- A label set is a matching when distinct selected supports are disjoint. -/
def IsMatching (H : LabeledHypergraph V E) (S : Finset E) : Prop :=
  ∀ e ∈ S, ∀ f ∈ S, e ≠ f → Disjoint (H.support e) (H.support f)

instance (H : LabeledHypergraph V E) (S : Finset E) :
    Decidable (H.IsMatching S) := by
  unfold IsMatching
  infer_instance

/-- All labeled hypergraph matchings, including the empty matching. -/
def matchingFamily (H : LabeledHypergraph V E) : Finset (Finset E) :=
  Finset.univ.filter H.IsMatching

def matchingCount (H : LabeledHypergraph V E) : Nat :=
  H.matchingFamily.card

@[simp] theorem mem_matchingFamily_iff (H : LabeledHypergraph V E)
    (S : Finset E) : S ∈ H.matchingFamily ↔ H.IsMatching S := by
  simp [matchingFamily]

theorem empty_isMatching (H : LabeledHypergraph V E) :
    H.IsMatching ∅ := by
  simp [IsMatching]

theorem singleton_isMatching (H : LabeledHypergraph V E) (e : E) :
    H.IsMatching {e} := by
  simp [IsMatching]

/-- Shrinking every labeled support can only enlarge the matching family. -/
theorem isMatching_of_support_subset
    (H H' : LabeledHypergraph V E)
    (hsub : ∀ e, H'.support e ⊆ H.support e)
    {S : Finset E} (hS : H.IsMatching S) : H'.IsMatching S := by
  intro e he f hf hef
  rw [Finset.disjoint_left]
  intro v hve hvf
  have hold : Disjoint (H.support e) (H.support f) := hS e he f hf hef
  rw [Finset.disjoint_left] at hold
  exact hold (hsub e hve) (hsub f hvf)

theorem matchingFamily_subset_of_support_subset
    (H H' : LabeledHypergraph V E)
    (hsub : ∀ e, H'.support e ⊆ H.support e) :
    H.matchingFamily ⊆ H'.matchingFamily := by
  intro S hS
  rw [mem_matchingFamily_iff] at hS ⊢
  exact isMatching_of_support_subset H H' hsub hS

theorem matchingCount_le_of_support_subset
    (H H' : LabeledHypergraph V E)
    (hsub : ∀ e, H'.support e ⊆ H.support e) :
    H.matchingCount ≤ H'.matchingCount := by
  exact Finset.card_le_card
    (matchingFamily_subset_of_support_subset H H' hsub)

/-- Replace every support by a chosen smaller support, preserving labels. -/
def shrink (H : LabeledHypergraph V E) (p : E → Finset V) :
    LabeledHypergraph V E where
  support := p

theorem matchingCount_le_shrink (H : LabeledHypergraph V E)
    (p : E → Finset V) (hp : ∀ e, p e ⊆ H.support e) :
    H.matchingCount ≤ (H.shrink p).matchingCount := by
  apply matchingCount_le_of_support_subset H (H.shrink p)
  exact hp

/-- Two labeled supports overlap when they share a vertex. -/
def SupportsOverlap (H : LabeledHypergraph V E) (e f : E) : Prop :=
  ∃ v, v ∈ H.support e ∧ v ∈ H.support f

instance (H : LabeledHypergraph V E) (e f : E) :
    Decidable (H.SupportsOverlap e f) := by
  unfold SupportsOverlap
  infer_instance

/-- A finite-set formulation of an antichain for an arbitrary strict
relation. -/
def IsAntichain (r : E → E → Prop) (S : Finset E) : Prop :=
  ∀ e ∈ S, ∀ f ∈ S, e ≠ f → ¬r e f ∧ ¬r f e

instance (r : E → E → Prop) [DecidableRel r] (S : Finset E) :
    Decidable (IsAntichain r S) := by
  unfold IsAntichain
  infer_instance

/-- The structural property supplied by participant chains: two distinct
labels sharing a participant are comparable. -/
def OverlapComparable (H : LabeledHypergraph V E)
    (r : E → E → Prop) : Prop :=
  ∀ e f, e ≠ f → H.SupportsOverlap e f → r e f ∨ r f e

theorem isMatching_of_isAntichain (H : LabeledHypergraph V E)
    (r : E → E → Prop) (hcomp : H.OverlapComparable r)
    {S : Finset E} (hanti : IsAntichain r S) : H.IsMatching S := by
  intro e he f hf hef
  rw [Finset.disjoint_left]
  intro v hve hvf
  have hoverlap : H.SupportsOverlap e f := ⟨v, hve, hvf⟩
  rcases hcomp e f hef hoverlap with hef' | hfe'
  · exact (hanti e he f hf hef).1 hef'
  · exact (hanti e he f hf hef).2 hfe'

variable (r : E → E → Prop) [DecidableRel r]

def antichainFamily : Finset (Finset E) :=
  Finset.univ.filter (IsAntichain r)

def antichainCount : Nat :=
  (antichainFamily r).card

@[simp] theorem mem_antichainFamily_iff (S : Finset E) :
    S ∈ antichainFamily r ↔ IsAntichain r S := by
  simp [antichainFamily]

/-- Antichains inject into labeled hypergraph matchings by retaining their
label sets. -/
theorem antichainFamily_subset_matchingFamily
    (H : LabeledHypergraph V E) (hcomp : H.OverlapComparable r) :
    antichainFamily r ⊆ H.matchingFamily := by
  intro S hS
  rw [mem_antichainFamily_iff] at hS
  rw [mem_matchingFamily_iff]
  exact isMatching_of_isAntichain H r hcomp hS

theorem antichainCount_le_matchingCount
    (H : LabeledHypergraph V E) (hcomp : H.OverlapComparable r) :
    antichainCount r ≤ H.matchingCount := by
  exact Finset.card_le_card
    (antichainFamily_subset_matchingFamily r H hcomp)

end LabeledHypergraph

end StableMatchingsE2E
