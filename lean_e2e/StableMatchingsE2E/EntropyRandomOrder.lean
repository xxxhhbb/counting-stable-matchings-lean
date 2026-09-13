import StableMatchingsE2E.StableEntropyApplication
import StableMatchingsE2E.RandomPriorities
import StableMatchingsE2E.GeometricDomination
import Mathlib.Data.Fin.Tuple.Sort

namespace StableMatchingsE2E

open StableMatchings355
open MeasureTheory ProbabilityTheory
open scoped unitInterval

noncomputable section

/-! ## A genuine reveal permutation for every priority vector

`Tuple.sort` sorts the graph `(priority p, p)`.  Thus it is a permutation
even when priorities tie; the participant index is the deterministic
lexicographic tie-break.  No null-set argument is used in this section. -/

/-- The total reveal order induced by priorities, with `Fin` index as the
deterministic tie-break. -/
def priorityOrder {n : Nat} (priority : Fin n → I) : Equiv.Perm (Fin n) :=
  Tuple.sort priority

/-- Pointwise lexicographic reveal predicate. -/
def LexUnitRevealedBefore {n : Nat}
    (priority : Fin n → I) (target p : Fin n) : Prop :=
  priority p < priority target ∨
    priority p = priority target ∧ p < target

instance {n : Nat} (priority : Fin n → I) (target : Fin n) :
    DecidablePred (LexUnitRevealedBefore priority target) := by
  intro p
  unfold LexUnitRevealedBefore
  infer_instance

theorem priorityOrder_position_lt_iff {n : Nat}
    (priority : Fin n → I) (p target : Fin n) :
    ((priorityOrder priority).symm p).val <
        ((priorityOrder priority).symm target).val ↔
      LexUnitRevealedBefore priority target p := by
  let G := Tuple.graphEquiv₂ priority
  have hp : G ((priorityOrder priority).symm p) =
      Tuple.graphEquiv₁ priority p := by
    rw [Tuple.graphEquiv₂_apply]
    simp [priorityOrder]
  have ht : G ((priorityOrder priority).symm target) =
      Tuple.graphEquiv₁ priority target := by
    rw [Tuple.graphEquiv₂_apply]
    simp [priorityOrder]
  change (priorityOrder priority).symm p <
      (priorityOrder priority).symm target ↔ _
  rw [← G.lt_iff_lt, hp, ht]
  simp only [Tuple.graphEquiv₁, LexUnitRevealedBefore]
  exact Prod.Lex.toLex_lt_toLex

/-- The prefix of the total priority permutation at the target is exactly
the lexicographic threshold predicate.  This theorem is pointwise, including
ties. -/
theorem fixedOrderRevealed_priorityOrder_target_iff {n : Nat}
    (priority : Fin n → I) (target p : Fin n) :
    fixedOrderRevealed (priorityOrder priority)
        ((priorityOrder priority).symm target).val p ↔
      LexUnitRevealedBefore priority target p := by
  exact priorityOrder_position_lt_iff priority p target

theorem lex_target_not_revealed {n : Nat}
    (priority : Fin n → I) (target : Fin n) :
    ¬ LexUnitRevealedBefore priority target target := by
  simp [LexUnitRevealedBefore]

/-- The audited FullInterval bridge instantiated with the genuine total
priority order. -/
theorem exists_lex_priority_full_bridge {n : Nat}
    (P : Profile (Fin n) (Fin n)) (target : Fin n)
    (base : Matching (Fin n) (Fin n))
    (priority : Fin n → I)
    (hbase : StableMatchings355.Stable P base) :
    ∃ q,
      ∃ E : ExactStablePartnerEnumeration (q := q) P target,
        ∃ j : Fin q,
          base.manPartner target = E.ranked.partner j ∧
          ∃ W : NearestRevealedWindow E base
              (LexUnitRevealedBefore priority target) j,
            ∃ S : ExactConditionalIndexSupport P E base
                (LexUnitRevealedBefore priority target),
              S.indices.length ≤
                upperBoundary W.upper - lowerBoundary W.lower := by
  exact exists_full_conditional_support_bridge P target base
    (LexUnitRevealedBefore priority target) hbase

/-! ## Exact prefix fibers

The recursive Shannon proof generates fibers by equality on an initial
segment of the reveal list.  The following definitions and lemmas identify
those nodes with the already audited `stableFiber` predicate. -/

def listPrefixFiber {A J B : Type*} [DecidableEq A] [DecidableEq J]
    [DecidableEq B]
    (s : Finset A) (code : A → J → B) (pref : List J) (base : A) :
    Finset A :=
  s.filter fun x ↦ ∀ i ∈ pref, code x i = code base i

@[simp] theorem mem_listPrefixFiber_iff {A J B : Type*} [DecidableEq A]
    [DecidableEq J] [DecidableEq B]
    (s : Finset A) (code : A → J → B) (pref : List J)
    (base x : A) :
    x ∈ listPrefixFiber s code pref base ↔
      x ∈ s ∧ ∀ i ∈ pref, code x i = code base i := by
  simp [listPrefixFiber]

theorem idxOf_ofFn_perm {n : Nat} (order : Equiv.Perm (Fin n))
    (p : Fin n) :
    (List.ofFn order).idxOf p = (order.symm p).val := by
  have hnodup : (List.ofFn order).Nodup :=
    List.nodup_ofFn_ofInjective order.injective
  have hget := List.get_idxOf hnodup
    (⟨(order.symm p).val, by simp⟩ : Fin (List.ofFn order).length)
  simpa using hget

theorem mem_take_ofFn_perm_iff {n : Nat} (order : Equiv.Perm (Fin n))
    (k : Nat) (p : Fin n) :
    p ∈ (List.ofFn order).take k ↔ (order.symm p).val < k := by
  have hp : p ∈ List.ofFn order := by
    rw [List.mem_ofFn]
    exact ⟨order.symm p, order.apply_symm_apply p⟩
  rw [List.mem_take_iff_idxOf_lt hp, idxOf_ofFn_perm]

/-- A list-prefix node of the global Shannon recursion is definitionally the
true stable fiber for the corresponding fixed-order reveal predicate. -/
theorem listPrefixFiber_stableSet_eq_stableFiber {n : Nat}
    (P : ProfileCode n) (order : Equiv.Perm (Fin n))
    (k : Nat) (base : MatchingCode n) :
    listPrefixFiber (stableSet P) (fun mu m ↦ mu m)
        ((List.ofFn order).take k) base =
      stableFiber P base (fixedOrderRevealed order k) := by
  classical
  ext mu
  simp only [mem_listPrefixFiber_iff, mem_stableFiber_iff,
    mem_stableSet_iff]
  constructor
  · rintro ⟨hstable, hagree⟩
    refine ⟨hstable, ?_⟩
    intro p hp
    exact hagree p ((mem_take_ofFn_perm_iff order k p).2 hp)
  · rintro ⟨hstable, hagree⟩
    refine ⟨hstable, ?_⟩
    intro p hp
    exact hagree p ((mem_take_ofFn_perm_iff order k p).1 hp)

/-- The next-coordinate image at a recursion node is the actual conditional
partner support of the corresponding stable fiber. -/
theorem image_listPrefixFiber_eq_conditionalPartnerSupport {n : Nat}
    (P : ProfileCode n) (order : Equiv.Perm (Fin n))
    (k : Fin n) (base : MatchingCode n) :
    (listPrefixFiber (stableSet P) (fun mu m ↦ mu m)
        ((List.ofFn order).take k.val) base).image
          (fun mu ↦ mu (order k)) =
      conditionalPartnerSupport P base
        (fixedOrderRevealed order k.val) (order k) := by
  rw [listPrefixFiber_stableSet_eq_stableFiber]
  rfl

/-! ## Simultaneous finite choice of all local FullInterval certificates -/

/-- A packaged local window certificate at one `(position, stable base)`.
The package records the exact enumeration, center, nearest window, exact
support, and its proven conditional-entropy bound. -/
structure LocalWindowCertificate {n : Nat} (P : ProfileCode n)
    (order : Equiv.Perm (Fin n)) (k : Fin n)
    (base : MatchingCode n) where
  q : Nat
  enumeration : ExactStablePartnerEnumeration
    (q := q) P.toCore (order k)
  center : Fin q
  base_eq : base (order k) = enumeration.ranked.partner center
  window : NearestRevealedWindow enumeration base.toCore
    (fixedOrderRevealed order k.val) center
  support : ExactConditionalIndexSupport P.toCore enumeration base.toCore
    (fixedOrderRevealed order k.val)
  entropy_le :
    finiteEntropy
        (conditionalPartnerSupport P base
          (fixedOrderRevealed order k.val) (order k))
        (partnerWeight P base
          (fixedOrderRevealed order k.val) (order k)) ≤
      Real.log ((upperBoundary window.upper -
        lowerBoundary window.lower : Nat) : ℝ)

/-- Finite-choice aggregation: one coherent function simultaneously selects
a verified local certificate for every reveal position and every stable base.
No compatibility between existential witnesses is silently assumed. -/
theorem exists_all_localWindowCertificates {n : Nat}
    (P : ProfileCode n) (order : Equiv.Perm (Fin n)) :
    ∃ cert : (k : Fin n) → (base : MatchingCode n) →
        Stable P base → LocalWindowCertificate P order k base,
      True := by
  classical
  choose q E j hj W S hbound using
    fun (k : Fin n) (base : MatchingCode n) (hbase : Stable P base) ↦
      exists_fixedOrder_localEntropy_window_bound P order k base hbase
  let cert : (k : Fin n) → (base : MatchingCode n) →
      Stable P base → LocalWindowCertificate P order k base :=
    fun k base hbase ↦
      { q := q k base hbase
        enumeration := E k base hbase
        center := j k base hbase
        base_eq := hj k base hbase
        window := W k base hbase
        support := S k base hbase
        entropy_le := hbound k base hbase }
  exact ⟨cert, trivial⟩

/-! ## The lexicographic bits have the strict Bernoulli law

For a fixed outer threshold `x`, ties occur only on finitely many coordinate
hyperplanes.  We prove the relevant a.e. equality in the inner product space
and then transfer the already proved joint Bernoulli law. -/

/-- Reveal bits of the *total* lexicographic order, restricted to the actual
non-target participants in the split model. -/
def lexTargetOtherIndicators {n : Nat} (target : Fin n) (x : I) :
    (OtherMen target → I) → OtherMen target → Bool :=
  fun ω i ↦ decide
    (LexUnitRevealedBefore (assemblePriority target (x, ω)) target i.1)

/-- All finitely many non-target priorities avoid a fixed threshold almost
everywhere under the inner product measure. -/
theorem ae_targetOther_all_ne {n : Nat} (target : Fin n) (x : I) :
    ∀ᵐ ω ∂(TargetOtherPriorityMeasure target),
      ∀ i : OtherMen target, ω i ≠ x := by
  rw [Filter.eventually_all]
  intro i
  exact MeasureTheory.Measure.ae_eval_ne
    (fun _ : OtherMen target ↦ (volume : Measure I)) i x

/-- The total-order bits and strict-threshold bits agree a.e.  The proof
explicitly removes every singleton tie hyperplane. -/
theorem lexTargetOtherIndicators_ae_eq_strict {n : Nat}
    (target : Fin n) (x : I) :
    lexTargetOtherIndicators target x =ᵐ[TargetOtherPriorityMeasure target]
      (fun ω i ↦ revealIndicator x (ω i)) := by
  filter_upwards [ae_targetOther_all_ne target x] with ω hω
  funext i
  have hi : (i.1 : Fin n) ≠ target := i.2
  have hasmOther : assemblePriority target (x, ω) i.1 = ω i := by
    exact assemblePriority_other target i.1 (x, ω) hi
  have hasmTarget : assemblePriority target (x, ω) target = x := by
    exact assemblePriority_target target (x, ω)
  simp only [lexTargetOtherIndicators, LexUnitRevealedBefore,
    hasmOther, hasmTarget, revealIndicator]
  have hne : ω i ≠ x := hω i
  simp [hne]

/-- Exact joint Bernoulli law for the bits coming from the genuine total
priority permutation.  This is obtained by an explicit a.e. map congruence,
not by an informal appeal to continuity. -/
theorem map_lexTargetOtherIndicators {n : Nat}
    (target : Fin n) (x : I) :
    (TargetOtherPriorityMeasure target).map
        (lexTargetOtherIndicators target x) =
      Measure.pi (fun _ : OtherMen target ↦ Ber(true, false, x)) := by
  calc
    _ = (TargetOtherPriorityMeasure target).map
        (fun ω i ↦ revealIndicator x (ω i)) :=
      MeasureTheory.Measure.map_congr
        (lexTargetOtherIndicators_ae_eq_strict target x)
    _ = _ := map_targetOtherIndicators target x

/-- Any real-valued statistic of the complete bit vector has the same inner
expectation under lexicographic and strict threshold bits. -/
theorem integral_lexTargetOtherIndicators_eq_strict {n : Nat}
    (target : Fin n) (x : I)
    (F : (OtherMen target → Bool) → ℝ) :
    ∫ ω, F (lexTargetOtherIndicators target x ω)
        ∂(TargetOtherPriorityMeasure target) =
      ∫ ω, F (fun i ↦ revealIndicator x (ω i))
        ∂(TargetOtherPriorityMeasure target) := by
  apply MeasureTheory.integral_congr_ae
  exact (lexTargetOtherIndicators_ae_eq_strict target x).fun_comp F

/-! ## Flattening the recursive entropy budget

The next finite identity is the tower property for a uniform finite set.
It is proved by grouping the outer sum into the exact fibers of `f`. -/

private theorem sum_uniform_fiber_average {A B : Type*}
    [DecidableEq A] [Fintype B] [DecidableEq B]
    (s : Finset A) (f : A → B) (G : A → ℝ) :
    ∑ a ∈ s,
        (((s.filter fun b ↦ f b = f a).card : ℝ)⁻¹ *
          ∑ b ∈ s.filter (fun c ↦ f c = f a), G b) =
      ∑ a ∈ s, G a := by
  classical
  rw [← Finset.sum_fiberwise s f G]
  rw [← Finset.sum_fiberwise s f (fun a ↦
    (((s.filter fun b ↦ f b = f a).card : ℝ)⁻¹ *
      ∑ b ∈ s.filter (fun c ↦ f c = f a), G b))]
  apply Finset.sum_congr rfl
  intro y hy
  let fy := s.filter fun a ↦ f a = y
  by_cases hfy : fy.Nonempty
  · have hcard : ((fy.card : ℝ) ≠ 0) := by
      exact_mod_cast Finset.card_ne_zero.mpr hfy
    have hfiber_eq : ∀ a ∈ fy,
        s.filter (fun b ↦ f b = f a) = fy := by
      intro a ha
      have hay : f a = y := (Finset.mem_filter.1 ha).2
      simp only [hay, fy]
    change (∑ a ∈ fy,
      (((s.filter fun b ↦ f b = f a).card : ℝ)⁻¹ *
        ∑ b ∈ s.filter (fun c ↦ f c = f a), G b)) =
      ∑ a ∈ fy, G a
    calc
      _ = ∑ _a ∈ fy,
          ((fy.card : ℝ)⁻¹ * ∑ b ∈ fy, G b) := by
        apply Finset.sum_congr rfl
        intro a ha
        rw [hfiber_eq a ha]
      _ = ∑ a ∈ fy, G a := by
        rw [Finset.sum_const, nsmul_eq_mul]
        field_simp
  · have hzero : fy = ∅ := Finset.not_nonempty_iff_eq_empty.mp hfy
    have hfilter : s.filter (fun a ↦ f a = y) = ∅ := by
      simpa only [fy] using hzero
    rw [hfilter]
    simp

/-- Cost seen along the exact prefix-fiber path of one base element. -/
noncomputable def revealPathBudget {A J B : Type*}
    [DecidableEq A] [DecidableEq B]
    (s : Finset A) (code : A → J → B) (base : A) : List J → ℝ
  | [] => 0
  | i :: is =>
      Real.log (s.image fun a ↦ code a i).card +
        revealPathBudget
          (s.filter fun a ↦ code a i = code base i) code base is

private theorem revealPathBudget_fiber_congr {A J B : Type*}
    [DecidableEq A] [DecidableEq B]
    (s : Finset A) (code : A → J → B) (i : J) (is : List J)
    {a b : A} (hab : code a i = code b i) :
    revealPathBudget (s.filter fun x ↦ code x i = code a i) code b is =
      revealPathBudget (s.filter fun x ↦ code x i = code b i) code b is := by
  congr 2
  ext x
  simp [hab]

/-- Exact flattening of every recursive node: the recursive conditional
expectation is the ordinary uniform-base expectation of the sum of log
support sizes encountered along that base's prefix-fiber path. -/
theorem revealEntropyBudget_eq_uniform_pathBudget
    {A J B : Type*} [DecidableEq A] [Fintype B] [DecidableEq B]
    (s : Finset A) (code : A → J → B) (order : List J)
    (hs : s.Nonempty) :
    revealEntropyBudget s code order =
      ((s.card : ℝ)⁻¹ *
        ∑ base ∈ s, revealPathBudget s code base order) := by
  induction order generalizing s with
  | nil =>
      simp [revealEntropyBudget, revealPathBudget]
  | cons i is ih =>
      have hcard : ((s.card : ℝ) ≠ 0) := by
        exact_mod_cast Finset.card_ne_zero.mpr hs
      rw [revealEntropyBudget]
      simp only [revealPathBudget]
      rw [Finset.sum_add_distrib]
      have hconst :
          ((s.card : ℝ)⁻¹ *
              ∑ _base ∈ s,
                Real.log (s.image fun a ↦ code a i).card) =
            Real.log (s.image fun a ↦ code a i).card := by
        rw [Finset.sum_const, nsmul_eq_mul]
        field_simp
      rw [mul_add, hconst]
      congr 1
      have hnode : ∀ a ∈ s,
          revealEntropyBudget
              (s.filter fun x ↦ code x i = code a i) code is =
            (((s.filter fun x ↦ code x i = code a i).card : ℝ)⁻¹ *
              ∑ b ∈ s.filter (fun x ↦ code x i = code a i),
                revealPathBudget
                  (s.filter fun x ↦ code x i = code b i) code b is) := by
        intro a ha
        have hnonempty :
            (s.filter fun x ↦ code x i = code a i).Nonempty :=
          ⟨a, Finset.mem_filter.2 ⟨ha, rfl⟩⟩
        rw [ih _ hnonempty]
        apply congrArg (fun z : ℝ ↦
          (((s.filter fun x ↦ code x i = code a i).card : ℝ)⁻¹ * z))
        apply Finset.sum_congr rfl
        intro b hb
        exact revealPathBudget_fiber_congr s code i is
          (Finset.mem_filter.1 hb).2.symm
      apply congrArg (fun z : ℝ ↦ ((s.card : ℝ)⁻¹ * z))
      calc
        (∑ a ∈ s, revealEntropyBudget
            (s.filter fun x ↦ code x i = code a i) code is) =
            ∑ a ∈ s,
              (((s.filter fun x ↦ code x i = code a i).card : ℝ)⁻¹ *
                ∑ b ∈ s.filter (fun x ↦ code x i = code a i),
                  revealPathBudget
                    (s.filter fun x ↦ code x i = code b i) code b is) := by
              apply Finset.sum_congr rfl
              intro a ha
              exact hnode a ha
        _ = ∑ b ∈ s, revealPathBudget
              (s.filter fun x ↦ code x i = code b i) code b is :=
          sum_uniform_fiber_average s (fun a ↦ code a i)
            (fun b ↦ revealPathBudget
              (s.filter fun x ↦ code x i = code b i) code b is)

/-! ## From prefix nodes to a genuine uniform-base window expectation -/

def listRevealed {n : Nat} (seen : List (Fin n)) (p : Fin n) : Prop :=
  p ∈ seen

instance {n : Nat} (seen : List (Fin n)) :
    DecidablePred (listRevealed seen) := by
  intro p
  unfold listRevealed
  infer_instance

theorem listPrefixFiber_stableSet_eq_stableFiber_list {n : Nat}
    (P : ProfileCode n) (seen : List (Fin n)) (base : MatchingCode n) :
    listPrefixFiber (stableSet P) (fun mu m ↦ mu m) seen base =
      stableFiber P base (listRevealed seen) := by
  classical
  ext mu
  simp [mem_stableSet_iff, mem_stableFiber_iff, listRevealed]

theorem image_listPrefixFiber_eq_conditionalPartnerSupport_list {n : Nat}
    (P : ProfileCode n) (seen : List (Fin n))
    (m : Fin n) (base : MatchingCode n) :
    (listPrefixFiber (stableSet P) (fun mu p ↦ mu p) seen base).image
        (fun mu ↦ mu m) =
      conditionalPartnerSupport P base (listRevealed seen) m := by
  rw [listPrefixFiber_stableSet_eq_stableFiber_list]
  rfl

private theorem listPrefixFiber_append_singleton {A J B : Type*}
    [DecidableEq A] [DecidableEq J] [DecidableEq B]
    (s : Finset A) (code : A → J → B) (seen : List J)
    (i : J) (base : A) :
    (listPrefixFiber s code seen base).filter
        (fun x ↦ code x i = code base i) =
      listPrefixFiber s code (seen ++ [i]) base := by
  ext x
  simp only [Finset.mem_filter, mem_listPrefixFiber_iff]
  constructor
  · rintro ⟨⟨hxs, hseen⟩, hi⟩
    refine ⟨hxs, ?_⟩
    intro j hj
    rw [List.mem_append] at hj
    rcases hj with hj | hj
    · exact hseen j hj
    · have hji : j = i := by simpa using hj
      subst j
      exact hi
  · rintro ⟨hxs, hall⟩
    refine ⟨⟨hxs, ?_⟩, ?_⟩
    · intro j hj
      exact hall j (List.mem_append_left [i] hj)
    · exact hall i (by simp)

/-- Exact window certificate for an arbitrary list-prefix node. -/
structure PrefixWindowCertificate {n : Nat} (P : ProfileCode n)
    (seen : List (Fin n)) (m : Fin n) (base : MatchingCode n) where
  q : Nat
  enumeration : ExactStablePartnerEnumeration (q := q) P.toCore m
  center : Fin q
  base_eq : base m = enumeration.ranked.partner center
  window : NearestRevealedWindow enumeration base.toCore
    (listRevealed seen) center
  support : ExactConditionalIndexSupport P.toCore enumeration base.toCore
    (listRevealed seen)
  support_card_le :
    (conditionalPartnerSupport P base (listRevealed seen) m).card ≤
      upperBoundary window.upper - lowerBoundary window.lower

abbrev StableBase {n : Nat} (P : ProfileCode n) :=
  {base : MatchingCode n // Stable P base}

abbrev PrefixWindowSelector {n : Nat} (P : ProfileCode n) :=
  (seen : List (Fin n)) → (m : Fin n) → (base : StableBase P) →
    PrefixWindowCertificate P seen m base.1

/-- Simultaneously choose witnesses for every list-prefix, target and stable
base.  The selector is a single coherent finite-object-valued function. -/
theorem exists_prefixWindowSelector {n : Nat} (P : ProfileCode n) :
    Nonempty (PrefixWindowSelector P) := by
  classical
  choose q E j hj W S hlen using
    fun (seen : List (Fin n)) (m : Fin n) (base : StableBase P) ↦
      StableMatchings355.exists_full_conditional_support_bridge
        P.toCore m base.1.toCore (listRevealed seen)
        ((stableCode_iff_core P base.1).1 base.2)
  let selector : PrefixWindowSelector P := fun seen m base ↦
    { q := q seen m base
      enumeration := E seen m base
      center := j seen m base
      base_eq := hj seen m base
      window := W seen m base
      support := S seen m base
      support_card_le := by
        exact conditionalPartnerSupport_card_le_window P m
          (E seen m base) base.1 (listRevealed seen) base.2
          (hj seen m base) (W seen m base) (S seen m base) }
  exact ⟨selector⟩

/-- Sum of the certified log window widths along one actual prefix path. -/
noncomputable def prefixWindowPathBudget {n : Nat} (P : ProfileCode n)
    (selector : PrefixWindowSelector P) (base : StableBase P)
    (seen : List (Fin n)) : List (Fin n) → ℝ
  | [] => 0
  | m :: ms =>
      let C := selector seen m base
      Real.log ((upperBoundary C.window.upper -
        lowerBoundary C.window.lower : Nat) : ℝ) +
      prefixWindowPathBudget P selector base (seen ++ [m]) ms

/-- A proof-independent total function on matching codes, used to take a
literal uniform sum over `stableSet`.  Nonstable codes receive value zero and
never contribute. -/
noncomputable def prefixWindowPathBudgetOrZero {n : Nat}
    (P : ProfileCode n) (selector : PrefixWindowSelector P)
    (base : MatchingCode n) (order : List (Fin n)) : ℝ :=
  if h : Stable P base then
    prefixWindowPathBudget P selector ⟨base, h⟩ [] order
  else 0

/-- At every stable base, every exact prefix support term in the Shannon path
is bounded by its simultaneously selected FullInterval window term. -/
theorem revealPathBudget_le_prefixWindowPathBudget {n : Nat}
    (P : ProfileCode n) (selector : PrefixWindowSelector P)
    (base : StableBase P) (seen order : List (Fin n)) :
    revealPathBudget
        (listPrefixFiber (stableSet P) (fun mu m ↦ mu m) seen base.1)
        (fun mu m ↦ mu m) base.1 order ≤
      prefixWindowPathBudget P selector base seen order := by
  induction order generalizing seen with
  | nil => simp [revealPathBudget, prefixWindowPathBudget]
  | cons m ms ih =>
      simp only [revealPathBudget, prefixWindowPathBudget]
      let C := selector seen m base
      have hsupportEq :=
        image_listPrefixFiber_eq_conditionalPartnerSupport_list
          P seen m base.1
      have hsupportPos : 0 <
          ((conditionalPartnerSupport P base.1 (listRevealed seen) m).card : ℝ) := by
        exact_mod_cast Finset.card_pos.mpr
          (conditionalPartnerSupport_nonempty P base.1
            (listRevealed seen) m base.2)
      have hwidth :
          (conditionalPartnerSupport P base.1 (listRevealed seen) m).card ≤
            upperBoundary C.window.upper - lowerBoundary C.window.lower :=
        C.support_card_le
      have hlog :
          Real.log
              ((listPrefixFiber (stableSet P) (fun mu p ↦ mu p) seen
                base.1).image (fun mu ↦ mu m)).card ≤
            Real.log ((upperBoundary C.window.upper -
              lowerBoundary C.window.lower : Nat) : ℝ) := by
        rw [hsupportEq]
        apply Real.log_le_log hsupportPos
        exact_mod_cast hwidth
      have htail := ih (seen ++ [m])
      rw [listPrefixFiber_append_singleton]
      exact add_le_add hlog htail

/-- The actual uniform-base expectation of the sum of certified logarithmic
window widths. -/
noncomputable def uniformPrefixWindowExpectation {n : Nat}
    (P : ProfileCode n) (selector : PrefixWindowSelector P)
    (order : List (Fin n)) : ℝ :=
  ((stableSet P).card : ℝ)⁻¹ *
    ∑ base ∈ stableSet P,
      prefixWindowPathBudgetOrZero P selector base order

/-- Closed finite composition theorem: the global recursive Shannon budget is
bounded by a literal uniform-base expectation of a `Σ log(windowSize)` path.
All existential `E/W/S` witnesses are supplied by one selector. -/
theorem revealEntropyBudget_le_uniformPrefixWindowExpectation {n : Nat}
    (P : ProfileCode n) (selector : PrefixWindowSelector P)
    (order : List (Fin n)) (hstable : (stableSet P).Nonempty) :
    revealEntropyBudget (stableSet P) (fun mu m ↦ mu m) order ≤
      uniformPrefixWindowExpectation P selector order := by
  rw [revealEntropyBudget_eq_uniform_pathBudget _ _ _ hstable]
  unfold uniformPrefixWindowExpectation
  apply mul_le_mul_of_nonneg_left
  · apply Finset.sum_le_sum
    intro base hbase
    have hs : Stable P base := (mem_stableSet_iff P base).1 hbase
    simpa [prefixWindowPathBudgetOrZero, hs, listPrefixFiber] using
      (revealPathBudget_le_prefixWindowPathBudget P selector
        (⟨base, hs⟩ : StableBase P) [] order)
  · positivity

/-- Global fixed-order consequence, now with no unresolved node/fiber choice
gap. -/
theorem log_stableCount_le_uniformPrefixWindowExpectation {n : Nat}
    (P : ProfileCode n) (selector : PrefixWindowSelector P)
    (order : Equiv.Perm (Fin n)) (hstable : (stableSet P).Nonempty) :
    Real.log (stableCount P) ≤
      uniformPrefixWindowExpectation P selector (List.ofFn order) := by
  exact (log_stableCount_le_fixedOrder_revealEntropyBudget P order hstable).trans
    (revealEntropyBudget_le_uniformPrefixWindowExpectation
      P selector (List.ofFn order) hstable)

/-- The same global theorem for the genuine priority-induced total order.
This holds pointwise for every priority vector, including ties. -/
theorem log_stableCount_le_priorityWindowExpectation {n : Nat}
    (P : ProfileCode n) (selector : PrefixWindowSelector P)
    (priority : Fin n → I) (hstable : (stableSet P).Nonempty) :
    Real.log (stableCount P) ≤
      uniformPrefixWindowExpectation P selector
        (List.ofFn (priorityOrder priority)) := by
  exact log_stableCount_le_uniformPrefixWindowExpectation P selector
    (priorityOrder priority) hstable

/-- The common product law of all priorities. -/
abbrev FullPriorityMeasure (n : Nat) : Measure (Fin n → I) :=
  Measure.pi (fun _ : Fin n ↦ (volume : Measure I))

instance fullPriorityMeasure_isProbability (n : Nat) :
    IsProbabilityMeasure (FullPriorityMeasure n) := inferInstance

noncomputable def priorityWindowCost {n : Nat} (P : ProfileCode n)
    (selector : PrefixWindowSelector P) (priority : Fin n → I) : ℝ :=
  uniformPrefixWindowExpectation P selector
    (List.ofFn (priorityOrder priority))

/-- Exact outer-priority expectation interface.  Integrability is explicit
so no measurability claim is hidden; the preceding pointwise theorem is
strictly stronger than the conclusion. -/
theorem log_stableCount_le_integral_priorityWindowCost {n : Nat}
    (P : ProfileCode n) (selector : PrefixWindowSelector P)
    (hstable : (stableSet P).Nonempty)
    (hInt : Integrable (priorityWindowCost P selector)
      (FullPriorityMeasure n)) :
    Real.log (stableCount P) ≤
      ∫ priority, priorityWindowCost P selector priority
        ∂(FullPriorityMeasure n) := by
  have hconst : Integrable
      (fun _priority : Fin n → I ↦ Real.log (stableCount P))
      (FullPriorityMeasure n) := integrable_const _
  have hae :
      (fun _priority : Fin n → I ↦ Real.log (stableCount P))
        ≤ᵐ[FullPriorityMeasure n] priorityWindowCost P selector :=
    Filter.Eventually.of_forall fun priority ↦
      log_stableCount_le_priorityWindowExpectation
        P selector priority hstable
  have hmono := integral_mono_ae hconst hInt hae
  simpa using hmono

end

end StableMatchingsE2E
