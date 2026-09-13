import Std
import Lean.Elab.Tactic.Omega
import Mathlib.Data.Finset.Card

namespace StableMatchingsProbability

/-!
This file formalizes the finite, dependency-free counting bridge used before
the analytic entropy step.  It intentionally does not define real logarithms,
probability measures, Shannon entropy, or infinite series.
-/

/-! ## A finite conditional-support / decision-tree product bound -/

/-- A finite reveal process: leaves are complete outcomes and each node lists
the outcomes still possible after the next revealed coordinate. -/
inductive DecisionTree where
  | leaf
  | node (children : List DecisionTree)
deriving Repr

namespace DecisionTree

/-- Number of complete outcomes represented by a reveal tree. -/
def leafCount : DecisionTree → Nat
  | leaf => 1
  | node children => (children.map leafCount).sum

/-- `Respects bounds tree` says that every conditional support at reveal level
`i` has cardinality at most `bounds[i]`, and every path has exactly the stated
number of reveal levels. -/
def Respects : List Nat → DecisionTree → Prop
  | [], leaf => True
  | b :: bs, node children =>
      children.length ≤ b ∧ ∀ child, child ∈ children → Respects bs child
  | _, _ => False

private theorem sum_le_length_mul_of_pointwise
    (xs : List Nat) (c : Nat) (h : ∀ x, x ∈ xs → x ≤ c) :
    xs.sum ≤ xs.length * c := by
  induction xs with
  | nil => simp
  | cons a xs ih =>
      have ha : a ≤ c := h a (by simp)
      have htail : ∀ x, x ∈ xs → x ≤ c := by
        intro x hx
        exact h x (List.mem_cons_of_mem a hx)
      have hi := ih htail
      simp only [List.sum_cons, List.length_cons]
      calc
        a + xs.sum ≤ c + xs.length * c := Nat.add_le_add ha hi
        _ = (xs.length + 1) * c := by
          simp [Nat.add_mul, Nat.add_comm]

/-- Finite chain rule for support sizes.  If the next coordinate has at most
`b_i` possible values after every prefix, the complete support has at most
`prod_i b_i` leaves. -/
theorem leafCount_le_prod {bounds : List Nat} {tree : DecisionTree}
    (h : Respects bounds tree) : leafCount tree ≤ bounds.prod := by
  induction bounds generalizing tree with
  | nil =>
      cases tree with
      | leaf => simp [leafCount]
      | node children => simp [Respects] at h
  | cons b bs ih =>
      cases tree with
      | leaf => simp [Respects] at h
      | node children =>
          rcases h with ⟨hlen, hchild⟩
          have hpoint : ∀ x, x ∈ children.map leafCount → x ≤ bs.prod := by
            intro x hx
            simp only [List.mem_map] at hx
            obtain ⟨child, hmem, rfl⟩ := hx
            exact ih (hchild child hmem)
          have hsum : (children.map leafCount).sum ≤
              (children.map leafCount).length * bs.prod :=
            sum_le_length_mul_of_pointwise _ _ hpoint
          have hmaplen : (children.map leafCount).length = children.length := by
            simp
          simp only [leafCount, List.prod_cons]
          rw [hmaplen] at hsum
          exact Nat.le_trans hsum (Nat.mul_le_mul_right _ hlen)

/-- A concrete two-level sanity check: three first-step choices and at most
two second-step choices give at most six complete outcomes. -/
example :
    let tree := node [node [leaf, leaf], node [leaf], node [leaf, leaf]]
    Respects [3, 2] tree ∧ leafCount tree ≤ 6 := by
  simp [Respects, leafCount]

end DecisionTree

/-! ## Explicit rectangular encoding of a finite support -/

/-- All coordinate strings with coordinate `i` in `[0, bounds[i])`. -/
def codeSpace : List Nat → List (List Nat)
  | [] => [[]]
  | b :: bs =>
      (List.range b).flatMap fun x =>
        (codeSpace bs).map fun tail => x :: tail

private theorem sum_map_constant_nat {α : Type}
    (xs : List α) (c : Nat) :
    (xs.map fun _ => c).sum = xs.length * c := by
  induction xs with
  | nil => simp
  | cons a xs ih =>
      simp only [List.map_cons, List.sum_cons, List.length_cons, ih]
      simp [Nat.add_mul, Nat.add_comm]

@[simp] theorem codeSpace_length (bounds : List Nat) :
    (codeSpace bounds).length = bounds.prod := by
  induction bounds with
  | nil => simp [codeSpace]
  | cons b bs ih =>
      simp only [codeSpace, List.length_flatMap, List.length_map, ih]
      rw [sum_map_constant_nat]
      simp

/-- List form of `|S| ≤ ∏ b_i`: it is enough to exhibit a duplicate-free
encoding of the support into the rectangular code space. -/
theorem encoded_support_le_prod
    (bounds : List Nat) (support : List (List Nat))
    (hnodup : support.Nodup)
    (hsub : ∀ code, code ∈ support → code ∈ codeSpace bounds) :
    support.length ≤ bounds.prod := by
  rw [← codeSpace_length bounds]
  classical
  rw [← List.toFinset_card_of_nodup hnodup]
  exact (Finset.card_le_card (by
    intro code hcode
    simp only [List.mem_toFinset] at hcode ⊢
    exact hsub code hcode)).trans (List.toFinset_card_le (codeSpace bounds))

/-! ## Independent finite Bernoulli-marker convolution interface -/

/-- Positive waiting-time pairs with `left + right - 1 = k`. -/
def waitingSplits (k : Nat) : List (Nat × Nat) :=
  (List.range k).map fun i => (i + 1, k - i)

@[simp] theorem waitingSplits_length (k : Nat) :
    (waitingSplits k).length = k := by
  simp [waitingSplits]

theorem mem_waitingSplits_iff {k left right : Nat} :
    (left, right) ∈ waitingSplits k ↔
      1 ≤ left ∧ 1 ≤ right ∧ left + right - 1 = k := by
  constructor
  · intro h
    simp only [waitingSplits, List.mem_map] at h
    obtain ⟨i, hi, hp⟩ := h
    have hik : i < k := by simpa using hi
    cases hp
    constructor
    · omega
    constructor <;> omega
  · rintro ⟨hleft, hright, hsum⟩
    let i := left - 1
    have hi : i < k := by simp [i]; omega
    have hiLeft : i + 1 = left := by simp [i]; omega
    have hrightForm : k - i = right := by simp [i]; omega
    simp only [waitingSplits, List.mem_map]
    exact ⟨i, by simpa using hi, by simp [hiLeft, hrightForm]⟩

private theorem nodup_map_of_injective {α β : Type} {f : α → β}
    (hf : Function.Injective f) {xs : List α} (hxs : xs.Nodup) :
    (xs.map f).Nodup := by
  induction xs with
  | nil => simp
  | cons a xs ih =>
      rw [List.nodup_cons] at hxs
      simp only [List.map_cons, List.nodup_cons]
      constructor
      · simp only [List.mem_map]
        rintro ⟨b, hb, hba⟩
        have : b = a := hf hba
        exact hxs.1 (this ▸ hb)
      · exact ih hxs.2

/-- The `k` convolution cases really are `k` distinct cases, rather than a
list whose length only counts duplicates. -/
theorem waitingSplits_nodup (k : Nat) : (waitingSplits k).Nodup := by
  unfold waitingSplits
  apply nodup_map_of_injective
  · intro a b h
    have hab : a + 1 = b + 1 := (Prod.mk.inj h).1
    omega
  · exact List.nodup_range

/-- The finite Bernoulli word for waiting time `L`: `L-1` failures and then
one success. -/
def markerPrefix (L : Nat) : List Bool :=
  List.replicate (L - 1) false ++ [true]

/-- A pair of independent finite marker prefixes, kept separate so that the
product structure is explicit. -/
def markerPair (left right : Nat) : List Bool × List Bool :=
  (markerPrefix left, markerPrefix right)

theorem markerPrefix_counts {L : Nat} (_hL : 1 ≤ L) :
    (markerPrefix L).count true = 1 ∧
    (markerPrefix L).count false = L - 1 := by
  constructor <;> simp [markerPrefix, List.count_replicate]

/-- Every convolution class `left + right - 1 = k` has two successes and
exactly `k-1` failures. -/
theorem markerPair_counts {k left right : Nat}
    (h : (left, right) ∈ waitingSplits k) :
    (markerPair left right).1.count true +
        (markerPair left right).2.count true = 2 ∧
    (markerPair left right).1.count false +
        (markerPair left right).2.count false = k - 1 := by
  have hs := mem_waitingSplits_iff.mp h
  have hl := markerPrefix_counts hs.1
  have hr := markerPrefix_counts hs.2.1
  constructor
  · simp [markerPair, hl.1, hr.1]
  · simp only [markerPair, hl.2, hr.2]
    omega

/-- Natural-number Bernoulli monomial for a pair of independent marker
prefixes.  This avoids importing a probability/measure library while
certifying the exact exponent bookkeeping. -/
def markerPairWeight (successWeight failureWeight left right : Nat) : Nat :=
  successWeight ^
      ((markerPair left right).1.count true +
       (markerPair left right).2.count true) *
  failureWeight ^
      ((markerPair left right).1.count false +
       (markerPair left right).2.count false)

theorem markerPairWeight_eq {k left right successWeight failureWeight : Nat}
    (h : (left, right) ∈ waitingSplits k) :
    markerPairWeight successWeight failureWeight left right =
      successWeight ^ 2 * failureWeight ^ (k - 1) := by
  have hc := markerPair_counts h
  simp [markerPairWeight, hc.1, hc.2]

private theorem sum_constant_over_list
    {α : Type} (xs : List α) (weight : α → Nat) (c : Nat)
    (h : ∀ x, x ∈ xs → weight x = c) :
    (xs.map weight).sum = xs.length * c := by
  induction xs with
  | nil => simp
  | cons a xs ih =>
      have ha : weight a = c := h a (by simp)
      have htail : ∀ x, x ∈ xs → weight x = c := by
        intro x hx
        exact h x (List.mem_cons_of_mem a hx)
      simp only [List.map_cons, List.sum_cons, List.length_cons]
      rw [ha, ih htail]
      simp [Nat.add_mul, Nat.add_comm]

/-- Exact finite convolution identity: there are `k` possible positive
splits and every split has monomial `s^2 f^(k-1)`. -/
theorem finite_independent_marker_convolution
    (k successWeight failureWeight : Nat) :
    ((waitingSplits k).map fun p =>
      markerPairWeight successWeight failureWeight p.1 p.2).sum =
      k * (successWeight ^ 2 * failureWeight ^ (k - 1)) := by
  calc
    ((waitingSplits k).map fun p =>
      markerPairWeight successWeight failureWeight p.1 p.2).sum =
        (waitingSplits k).length *
          (successWeight ^ 2 * failureWeight ^ (k - 1)) := by
      apply sum_constant_over_list
      intro p hp
      rcases p with ⟨left, right⟩
      exact markerPairWeight_eq hp
    _ = k * (successWeight ^ 2 * failureWeight ^ (k - 1)) := by
      rw [waitingSplits_length]

/-! Kernel-evaluated regression examples. -/

example : waitingSplits 4 = [(1, 4), (2, 3), (3, 2), (4, 1)] := by
  decide

example : markerPairWeight 3 5 2 3 = 3 ^ 2 * 5 ^ 3 := by
  decide

end StableMatchingsProbability
