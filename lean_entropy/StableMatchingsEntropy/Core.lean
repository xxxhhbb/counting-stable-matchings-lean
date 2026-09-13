import Std
import Lean.Elab.Tactic.Omega
import Mathlib.Data.Finset.Card

namespace StableMatchingsEntropy

/-! ## Finite combinatorial core of the partner-reveal entropy argument

This file deliberately avoids measure theory.  It certifies the exact
finite counting and domination statements used before the analytic passage
to geometric random variables and entropy integrals.
-/

/-! ### Two positive waiting times -/

/-- The canonical list of positive decompositions of `k + 1`.
Entry `i` is `(i + 1, k - i)`, so its two coordinates are positive and
`L + R - 1 = k`. -/
def geometricSplits (k : Nat) : List (Nat × Nat) :=
  (List.range k).map fun i => (i + 1, k - i)

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

@[simp] theorem geometricSplits_length (k : Nat) :
    (geometricSplits k).length = k := by
  simp [geometricSplits]

theorem mem_geometricSplits_iff {k L R : Nat} :
    (L, R) ∈ geometricSplits k ↔
      1 ≤ L ∧ 1 ≤ R ∧ L + R - 1 = k := by
  constructor
  · intro h
    simp only [geometricSplits, List.mem_map] at h
    obtain ⟨i, hi, hp⟩ := h
    have hik : i < k := by simpa using hi
    cases hp
    constructor
    · omega
    constructor <;> omega
  · rintro ⟨hL, hR, hsum⟩
    have hLk : L ≤ k := by omega
    let i := L - 1
    have hi : i < k := by simp [i]; omega
    have hiL : i + 1 = L := by simp [i]; omega
    have hRform : k - i = R := by simp [i]; omega
    simp only [geometricSplits, List.mem_map]
    exact ⟨i, by simpa using hi, by simp [hiL, hRform]⟩

theorem geometricSplits_nodup (k : Nat) :
    (geometricSplits k).Nodup := by
  unfold geometricSplits
  apply nodup_map_of_injective
  · intro a b h
    have hab : a + 1 = b + 1 := (Prod.mk.inj h).1
    omega
  · exact List.nodup_range

/-- Every split contributing to `N = L + R - 1 = k` contains exactly
`k - 1` failed Bernoulli trials before the two successes. -/
theorem geometric_split_failure_exponent {k L R : Nat}
    (hmem : (L, R) ∈ geometricSplits k) :
    (L - 1) + (R - 1) = k - 1 := by
  have h := (mem_geometricSplits_iff.mp hmem)
  omega

/-- The finite trial word for a geometric waiting time `L`: `L-1` failures
followed by one success. -/
def geometricPrefix (L : Nat) : List Bool :=
  List.replicate (L - 1) false ++ [true]

theorem geometricPrefix_length {L : Nat} (hL : 1 ≤ L) :
    (geometricPrefix L).length = L := by
  simp [geometricPrefix]
  omega

/-- The concatenated word for a split has two successes and `k-1`
failures.  This is the finite exponent bookkeeping behind
`x^2 * (1-x)^(k-1)`. -/
theorem geometric_split_trial_counts {k L R : Nat}
    (hmem : (L, R) ∈ geometricSplits k) :
    (geometricPrefix L ++ geometricPrefix R).count true = 2 ∧
    (geometricPrefix L ++ geometricPrefix R).count false = k - 1 := by
  have h := mem_geometricSplits_iff.mp hmem
  have hfail := geometric_split_failure_exponent hmem
  constructor
  · simp [geometricPrefix, List.count_replicate]
  · simp [geometricPrefix]
    exact hfail

/-- The Bernoulli monomial attached to a finite Boolean trial word. -/
def bernoulliMonomial (successWeight failureWeight : Nat)
    (trials : List Bool) : Nat :=
  successWeight ^ trials.count true * failureWeight ^ trials.count false

theorem geometric_split_monomial {k L R successWeight failureWeight : Nat}
    (hmem : (L, R) ∈ geometricSplits k) :
    bernoulliMonomial successWeight failureWeight
        (geometricPrefix L ++ geometricPrefix R) =
      successWeight ^ 2 * failureWeight ^ (k - 1) := by
  have hcounts := geometric_split_trial_counts hmem
  simp only [bernoulliMonomial, hcounts.1, hcounts.2]

/-- There are exactly `k` ordered positive pairs `(L,R)` satisfying
`L + R - 1 = k`: `geometricSplits k` is a duplicate-free exhaustive list
of length `k`. -/
theorem geometric_waiting_time_convolution_count (k : Nat) :
    (geometricSplits k).length = k ∧
    (geometricSplits k).Nodup ∧
    ∀ L R, (L, R) ∈ geometricSplits k ↔
      1 ≤ L ∧ 1 ≤ R ∧ L + R - 1 = k := by
  exact ⟨geometricSplits_length k, geometricSplits_nodup k,
    fun _ _ => mem_geometricSplits_iff⟩

private theorem sum_map_eq_length_nsmul_of_constant
    {α : Type} (xs : List α) (weight : α → Nat) (c : Nat)
    (hconstant : ∀ x, x ∈ xs → weight x = c) :
    (xs.map weight).sum = xs.length * c := by
  induction xs with
  | nil => simp
  | cons a xs ih =>
      have ha : weight a = c := hconstant a (by simp)
      have htail : ∀ x, x ∈ xs → weight x = c := by
        intro x hx
        exact hconstant x (List.mem_cons_of_mem a hx)
      simp only [List.map_cons, List.sum_cons, List.length_cons]
      rw [ha, ih htail]
      simp [Nat.succ_mul, Nat.add_comm]

/-- Algebraic convolution factor: if every positive split of `k + 1` has
the same weight `c` (as happens for two geometric waiting times), summing
over all splits gives exactly `k • c`. -/
theorem geometric_split_constant_weight_sum
    (k : Nat) (weight : Nat × Nat → Nat) (c : Nat)
    (hconstant : ∀ p, p ∈ geometricSplits k → weight p = c) :
    ((geometricSplits k).map weight).sum = k * c := by
  calc
    ((geometricSplits k).map weight).sum =
        (geometricSplits k).length * c :=
      sum_map_eq_length_nsmul_of_constant
        (geometricSplits k) weight c hconstant
    _ = k * c := by rw [geometricSplits_length]

/-- Finite polynomial form of the two-geometric convolution.  Substituting
`successWeight = x` and `failureWeight = 1-x` in a suitable semiring gives
the familiar mass `k*x^2*(1-x)^(k-1)`; here the identity is kernel-checked
over naturals without importing analysis. -/
theorem finite_geometric_convolution_monomial
    (k successWeight failureWeight : Nat) :
    ((geometricSplits k).map fun p =>
      bernoulliMonomial successWeight failureWeight
        (geometricPrefix p.1 ++ geometricPrefix p.2)).sum =
      k * (successWeight ^ 2 * failureWeight ^ (k - 1)) := by
  apply geometric_split_constant_weight_sum
  intro p hp
  rcases p with ⟨L, R⟩
  exact geometric_split_monomial hp

/-! ### Finite marker windows and dummy extension -/

/-- Distance to the first marker, truncated at the finite endpoint.
Thus a marker at the head gives `1`, while a marker-free list of length `m`
has waiting time `m + 1`.  The extra unit is essential: an empty side still
contributes the central candidate to `L + R - 1`. -/
def truncatedWait : List Bool → Nat
  | [] => 1
  | true :: _ => 1
  | false :: xs => 1 + truncatedWait xs

@[simp] theorem truncatedWait_nil : truncatedWait [] = 1 := rfl
@[simp] theorem truncatedWait_true (xs : List Bool) :
    truncatedWait (true :: xs) = 1 := rfl
@[simp] theorem truncatedWait_false (xs : List Bool) :
    truncatedWait (false :: xs) = 1 + truncatedWait xs := rfl

theorem truncatedWait_pos (xs : List Bool) : 1 ≤ truncatedWait xs := by
  induction xs with
  | nil => simp
  | cons b xs ih => cases b <;> simp [truncatedWait]

theorem truncatedWait_le_length_succ (xs : List Bool) :
    truncatedWait xs ≤ xs.length + 1 := by
  induction xs with
  | nil => simp
  | cons b xs ih =>
      cases b
      · simp only [truncatedWait, List.length_cons]
        omega
      · simp [truncatedWait]

/-- Appending dummy trials beyond an endpoint can only move the first marker
outward; it can never decrease the truncated waiting distance. -/
theorem truncatedWait_le_append (xs ys : List Bool) :
    truncatedWait xs ≤ truncatedWait (xs ++ ys) := by
  induction xs with
  | nil => simpa using truncatedWait_pos ys
  | cons b xs ih => cases b <;> simp [truncatedWait, ih]

/-- If the finite side already contains a marker, dummy extension does not
change its waiting distance at all. -/
theorem truncatedWait_append_eq_of_marker
    (xs ys : List Bool) (hmarker : true ∈ xs) :
    truncatedWait (xs ++ ys) = truncatedWait xs := by
  induction xs with
  | nil => simp at hmarker
  | cons b xs ih =>
      cases b
      · have htail : true ∈ xs :=
          (List.mem_cons.mp hmarker).resolve_left (by decide)
        simp only [List.cons_append, truncatedWait]
        rw [ih htail]
      · simp [truncatedWait]

/-- If a finite side contains no marker, its truncated wait is exactly one
more than its finite length.  This is the endpoint case that dummy extension
dominates. -/
theorem truncatedWait_eq_length_succ_of_no_marker
    (xs : List Bool) (hmarker : true ∉ xs) :
    truncatedWait xs = xs.length + 1 := by
  induction xs with
  | nil => simp
  | cons b xs ih =>
      cases b
      · have htail : true ∉ xs := fun h =>
          hmarker (List.mem_cons_of_mem false h)
        simp only [truncatedWait, List.length_cons]
        rw [ih htail]
        omega
      · simp at hmarker

/-- Width of the interval cut out by left and right waiting distances. -/
def markerWindowWidth (left right : List Bool) : Nat :=
  truncatedWait left + truncatedWait right - 1

/-- Canonical zero-based enumeration of the abstract candidate indices in a
two-sided marker window. -/
def markerWindowIndices (left right : List Bool) : List Nat :=
  List.range (markerWindowWidth left right)

@[simp] theorem markerWindowIndices_length (left right : List Bool) :
    (markerWindowIndices left right).length = markerWindowWidth left right := by
  simp [markerWindowIndices]

theorem markerWindowIndices_nodup (left right : List Bool) :
    (markerWindowIndices left right).Nodup := by
  exact List.nodup_range

/-- The two-sided finite window width is dominated pointwise by the width
after independently extending both missing endpoints by dummy trials. -/
theorem finite_marker_window_le_extended
    (left right leftDummy rightDummy : List Bool) :
    markerWindowWidth left right ≤
      markerWindowWidth (left ++ leftDummy) (right ++ rightDummy) := by
  have hl := truncatedWait_le_append left leftDummy
  have hr := truncatedWait_le_append right rightDummy
  simp only [markerWindowWidth]
  omega

/-! ### Finite conditional support bounds -/

/-- Filtering a finite candidate list by any conditioning predicate cannot
increase its support size. -/
theorem conditional_support_length_le {α : Type} (candidates : List α)
    (compatible : α → Bool) :
    (candidates.filter compatible).length ≤ candidates.length := by
  exact List.length_filter_le _ _

/-- If a conditional support is a sublist of an interval enumeration, its
cardinality is at most the interval width.  `Nodup` makes list length equal
to support cardinality rather than multiplicity. -/
theorem conditional_support_interval_bound {α : Type}
    (support interval : List α)
    (hsupport : support.Nodup)
    (_hinterval : interval.Nodup)
    (hsub : ∀ x, x ∈ support → x ∈ interval) :
    support.length ≤ interval.length := by
  classical
  rw [← List.toFinset_card_of_nodup hsupport]
  exact (Finset.card_le_card (by
    intro x hx
    simp only [List.mem_toFinset] at hx ⊢
    exact hsub x hx)).trans (List.toFinset_card_le interval)

/-- Concrete index form of the finite support lemma: a duplicate-free
conditional support contained in the canonical marker-window enumeration
has size at most `L + R - 1`. -/
theorem conditional_index_support_le_marker_window
    (support : List Nat) (left right : List Bool)
    (hsupport : support.Nodup)
    (hsub : ∀ x, x ∈ support → x ∈ markerWindowIndices left right) :
    support.length ≤ markerWindowWidth left right := by
  rw [← markerWindowIndices_length left right]
  exact conditional_support_interval_bound support
    (markerWindowIndices left right) hsupport
    (markerWindowIndices_nodup left right) hsub

/-- Combined finite bridge: once a conditional support has been injected
into the finite marker interval, extending either endpoint by dummy trials
preserves a valid cardinality upper bound. -/
theorem conditional_support_le_extended_marker_window {α : Type}
    (support : List α) (left right leftDummy rightDummy : List Bool)
    (hfinite : support.length ≤ markerWindowWidth left right) :
    support.length ≤
      markerWindowWidth (left ++ leftDummy) (right ++ rightDummy) := by
  exact Nat.le_trans hfinite
    (finite_marker_window_le_extended left right leftDummy rightDummy)

/-- End-to-end finite combinatorial bridge from an explicitly indexed
conditional support to the dummy-extended marker window. -/
theorem conditional_index_support_le_extended_marker_window
    (support : List Nat) (left right leftDummy rightDummy : List Bool)
    (hsupport : support.Nodup)
    (hsub : ∀ x, x ∈ support → x ∈ markerWindowIndices left right) :
    support.length ≤
      markerWindowWidth (left ++ leftDummy) (right ++ rightDummy) := by
  apply conditional_support_le_extended_marker_window
  exact conditional_index_support_le_marker_window
    support left right hsupport hsub

/-! Small kernel-evaluated regression checks. -/

example : geometricSplits 4 = [(1, 4), (2, 3), (3, 2), (4, 1)] := by
  decide

example : truncatedWait [false, false, true, false] = 3 := by
  decide

example : markerWindowWidth [false, true] [true, false] = 2 := by
  decide

example : markerWindowWidth [] [] = 1 := by
  decide

end StableMatchingsEntropy
