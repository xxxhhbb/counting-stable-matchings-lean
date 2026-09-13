import StableMatchingsE2E.FiniteEntropy
import StableMatchingsE2E.ProfileCode
import StableMatchings355.FullInterval

namespace StableMatchingsE2E

open scoped BigOperators
open Finset Set Real

/-!
# Applying the finite entropy layer to stable matchings

This file contains the finite, exact-fiber part of the reveal argument.  It
does not use a conditional probability kernel: a conditional fiber is an
explicit `Finset` of stable matchings, and its partner support is an explicit
`Finset` image.  The bridge to `ExactConditionalIndexSupport` proves that the
list occurring in the interval theorem is the *whole* support, not a selected
sublist.
-/

/-- Stable matchings agreeing with `base` at every already revealed man. -/
def stableFiber {n : Nat} (P : ProfileCode n) (base : MatchingCode n)
    (revealed : Fin n → Prop) [DecidablePred revealed] : Finset (MatchingCode n) :=
  (stableSet P).filter fun nu ↦ ∀ p, revealed p → nu p = base p

theorem mem_stableFiber_iff {n : Nat} (P : ProfileCode n)
    (base nu : MatchingCode n) (revealed : Fin n → Prop)
    [DecidablePred revealed] :
    nu ∈ stableFiber P base revealed ↔
      Stable P nu ∧ ∀ p, revealed p → nu p = base p := by
  simp [stableFiber, mem_stableSet_iff]

theorem base_mem_stableFiber {n : Nat} (P : ProfileCode n)
    (base : MatchingCode n) (revealed : Fin n → Prop)
    [DecidablePred revealed] (hbase : Stable P base) :
    base ∈ stableFiber P base revealed := by
  exact (mem_stableFiber_iff P base base revealed).2 ⟨hbase, fun _ _ ↦ rfl⟩

theorem stableFiber_nonempty {n : Nat} (P : ProfileCode n)
    (base : MatchingCode n) (revealed : Fin n → Prop)
    [DecidablePred revealed] (hbase : Stable P base) :
    (stableFiber P base revealed).Nonempty :=
  ⟨base, base_mem_stableFiber P base revealed hbase⟩

/-- The exact set of partners still possible for `m` in the revealed fiber. -/
def conditionalPartnerSupport {n : Nat} (P : ProfileCode n)
    (base : MatchingCode n) (revealed : Fin n → Prop)
    [DecidablePred revealed] (m : Fin n) : Finset (Fin n) :=
  (stableFiber P base revealed).image fun nu ↦ nu m

theorem mem_conditionalPartnerSupport_iff {n : Nat} (P : ProfileCode n)
    (base : MatchingCode n) (revealed : Fin n → Prop)
    [DecidablePred revealed] (m w : Fin n) :
    w ∈ conditionalPartnerSupport P base revealed m ↔
      ∃ nu : MatchingCode n,
        Stable P nu ∧ (∀ p, revealed p → nu p = base p) ∧ nu m = w := by
  simp only [conditionalPartnerSupport, Finset.mem_image,
    mem_stableFiber_iff]
  constructor
  · rintro ⟨nu, hnu, rfl⟩
    exact ⟨nu, hnu.1, hnu.2, rfl⟩
  · rintro ⟨nu, hstable, hagree, rfl⟩
    exact ⟨nu, ⟨hstable, hagree⟩, rfl⟩

theorem conditionalPartnerSupport_nonempty {n : Nat} (P : ProfileCode n)
    (base : MatchingCode n) (revealed : Fin n → Prop)
    [DecidablePred revealed] (m : Fin n) (hbase : Stable P base) :
    (conditionalPartnerSupport P base revealed m).Nonempty := by
  exact ⟨base m, Finset.mem_image.2
    ⟨base, base_mem_stableFiber P base revealed hbase, rfl⟩⟩

private theorem matchingCode_toCore_ofCore {n : Nat}
    (mu : StableMatchings355.Matching (Fin n) (Fin n)) :
    (MatchingCode.ofCore mu).toCore = mu := by
  cases mu
  rfl

private theorem matchingCode_ofCore_toCore {n : Nat} (mu : MatchingCode n) :
    MatchingCode.ofCore mu.toCore = mu := by
  apply Equiv.ext
  intro m
  rfl

/-- A coded revealed fiber and the relation-level `CompatibleOn` predicate
are exactly the same object under the lossless matching conversion. -/
theorem mem_stableFiber_iff_core_compatible {n : Nat} (P : ProfileCode n)
    (base nu : MatchingCode n) (revealed : Fin n → Prop)
    [DecidablePred revealed] :
    nu ∈ stableFiber P base revealed ↔
      StableMatchings355.CompatibleOn P.toCore base.toCore nu.toCore revealed := by
  rw [mem_stableFiber_iff]
  rfl

/-- Partners represented by a full exact index-support certificate. -/
def indexedPartnerSupport {n q : Nat}
    {P : StableMatchings355.Profile (Fin n) (Fin n)} {m : Fin n}
    (E : StableMatchings355.ExactStablePartnerEnumeration (q := q) P m)
    {base : StableMatchings355.Matching (Fin n) (Fin n)}
    {revealed : Fin n → Prop}
    (S : StableMatchings355.ExactConditionalIndexSupport P E base revealed) :
    Finset (Fin n) :=
  S.indices.toFinset.image E.ranked.partner

/-- `ExactConditionalIndexSupport.complete` is used in the reverse
inclusion, so this is an equality with the true coded conditional support,
not merely a sound under-approximation. -/
theorem indexedPartnerSupport_eq_conditionalPartnerSupport {n q : Nat}
    (P : ProfileCode n) (m : Fin n)
    (E : StableMatchings355.ExactStablePartnerEnumeration (q := q) P.toCore m)
    (base : MatchingCode n) (revealed : Fin n → Prop)
    [DecidablePred revealed]
    (S : StableMatchings355.ExactConditionalIndexSupport
      P.toCore E base.toCore revealed) :
    indexedPartnerSupport E S = conditionalPartnerSupport P base revealed m := by
  classical
  ext w
  constructor
  · intro hw
    rw [indexedPartnerSupport, Finset.mem_image] at hw
    obtain ⟨t, ht, rfl⟩ := hw
    have htList : t ∈ S.indices := by simpa using ht
    obtain ⟨nu, hcompat, htarget⟩ := S.sound t htList
    let nuCode : MatchingCode n := MatchingCode.ofCore nu
    have hcore : nuCode.toCore = nu := matchingCode_toCore_ofCore nu
    apply (mem_conditionalPartnerSupport_iff P base revealed m
      (E.ranked.partner t)).2
    refine ⟨nuCode, ?_, ?_, ?_⟩
    · exact (stableCode_iff_core P nuCode).2 (by simpa [hcore] using hcompat.1)
    · intro p hp
      have heq := hcompat.2 p hp
      exact heq
    · exact htarget
  · intro hw
    obtain ⟨nu, hstable, hagree, htarget⟩ :=
      (mem_conditionalPartnerSupport_iff P base revealed m w).1 hw
    obtain ⟨t, ht⟩ := E.complete nu.toCore
      ((stableCode_iff_core P nu).1 hstable)
    have htList : t ∈ S.indices := S.complete nu.toCore
      ⟨(stableCode_iff_core P nu).1 hstable, hagree⟩ t ht
    rw [indexedPartnerSupport, Finset.mem_image]
    exact ⟨t, by simpa using htList, by
      calc
        E.ranked.partner t = nu m := ht.symm
        _ = w := htarget⟩

/-- The index list and the actual partner support have identical cardinality.
The proof explicitly uses both list nodup and injectivity of the ranked table;
it never identifies list length with finset cardinality without `Nodup`. -/
theorem indexedPartnerSupport_card_eq_length {n q : Nat}
    {P : StableMatchings355.Profile (Fin n) (Fin n)} {m : Fin n}
    (E : StableMatchings355.ExactStablePartnerEnumeration (q := q) P m)
    {base : StableMatchings355.Matching (Fin n) (Fin n)}
    {revealed : Fin n → Prop}
    (S : StableMatchings355.ExactConditionalIndexSupport P E base revealed) :
    (indexedPartnerSupport E S).card = S.indices.length := by
  classical
  rw [indexedPartnerSupport, Finset.card_image_of_injective _ E.ranked.injective]
  exact List.toFinset_card_of_nodup S.nodup

/-- The exact FullInterval support bound, stated for the actual coded partner
support used by entropy. -/
theorem conditionalPartnerSupport_card_le_window {n q : Nat}
    (P : ProfileCode n) (m : Fin n)
    (E : StableMatchings355.ExactStablePartnerEnumeration (q := q) P.toCore m)
    (base : MatchingCode n) (revealed : Fin n → Prop)
    [DecidablePred revealed] {j : Fin q}
    (hbase : Stable P base)
    (hbaseTarget : base m = E.ranked.partner j)
    (W : StableMatchings355.NearestRevealedWindow E base.toCore revealed j)
    (S : StableMatchings355.ExactConditionalIndexSupport
      P.toCore E base.toCore revealed) :
    (conditionalPartnerSupport P base revealed m).card ≤
      StableMatchings355.upperBoundary W.upper -
        StableMatchings355.lowerBoundary W.lower := by
  rw [← indexedPartnerSupport_eq_conditionalPartnerSupport P m E base revealed S,
    indexedPartnerSupport_card_eq_length E S]
  exact StableMatchings355.exact_conditional_support_length_le
    P.toCore E base.toCore revealed
      ((stableCode_iff_core P base).1 hbase) hbaseTarget W S

/-! ## The local Shannon inequality on a genuine stable fiber -/

/-- The push-forward mass of the uniform distribution on a nonempty stable
fiber under the partner coordinate `m`. -/
noncomputable def partnerWeight {n : Nat} (P : ProfileCode n)
    (base : MatchingCode n) (revealed : Fin n → Prop)
    [DecidablePred revealed] (m : Fin n) (w : Fin n) : ℝ :=
  (((stableFiber P base revealed).filter fun nu ↦ nu m = w).card : ℝ) /
    (stableFiber P base revealed).card

theorem partnerWeight_nonneg {n : Nat} (P : ProfileCode n)
    (base : MatchingCode n) (revealed : Fin n → Prop)
    [DecidablePred revealed] (m w : Fin n) :
    0 ≤ partnerWeight P base revealed m w := by
  exact div_nonneg (by positivity) (by positivity)

private theorem sum_card_fibers_all {A B : Type*} [DecidableEq A]
    [Fintype B] [DecidableEq B]
    (s : Finset A) (f : A → B) :
    ∑ b : B, (s.filter fun a ↦ f a = b).card = s.card := by
  induction s using Finset.induction_on with
  | empty => simp
  | @insert a s ha ih =>
      rw [Finset.card_insert_of_notMem ha, ← ih]
      calc
        (∑ b : B, ((insert a s).filter fun x ↦ f x = b).card) =
            ∑ b : B, ((if f a = b then 1 else 0) +
              (s.filter fun x ↦ f x = b).card) := by
          apply Finset.sum_congr rfl
          intro b _
          by_cases hab : f a = b
          · simp [Finset.filter_insert, ha, hab]
            omega
          · simp [Finset.filter_insert, ha, hab]
        _ = (∑ b : B, if f a = b then 1 else 0) +
              ∑ b : B, (s.filter fun x ↦ f x = b).card := by
          rw [Finset.sum_add_distrib]
        _ = 1 + ∑ b : B, (s.filter fun x ↦ f x = b).card := by
          simp
        _ = ∑ b : B, (s.filter fun x ↦ f x = b).card + 1 := by omega

private theorem sum_card_fibers {A B : Type*} [DecidableEq A]
    [Fintype B] [DecidableEq B]
    (s : Finset A) (f : A → B) :
    ∑ b ∈ s.image f, (s.filter fun a ↦ f a = b).card = s.card := by
  rw [← sum_card_fibers_all s f]
  apply Finset.sum_subset (Finset.subset_univ _)
  intro b _ hb
  have hempty : s.filter (fun a ↦ f a = b) = ∅ := by
    ext a
    constructor
    · intro hamem
      have ha : a ∈ s ∧ f a = b := Finset.mem_filter.1 hamem
      exact False.elim (hb (Finset.mem_image.2 ⟨a, ha.1, ha.2⟩))
    · intro hamem
      simp at hamem
  simp [hempty]

private theorem sum_card_fibers_mul {A B : Type*} [DecidableEq A]
    [DecidableEq B] (s : Finset A) (f : A → B) (g : B → ℝ) :
    ∑ b ∈ s.image f,
        ((s.filter fun a ↦ f a = b).card : ℝ) * g b =
      ∑ a ∈ s, g (f a) := by
  calc
    (∑ b ∈ s.image f,
        ((s.filter fun a ↦ f a = b).card : ℝ) * g b) =
      ∑ b ∈ s.image f, ∑ a ∈ s with f a = b, g (f a) := by
        apply Finset.sum_congr rfl
        intro b hb
        rw [show (∑ a ∈ s with f a = b, g (f a)) =
            ∑ _a ∈ s.filter (fun a ↦ f a = b), g b by
          apply Finset.sum_congr rfl
          intro a ha
          exact congrArg g (Finset.mem_filter.1 ha).2]
        simp
    _ = ∑ a ∈ s, g (f a) := by
      rw [Finset.sum_fiberwise_of_maps_to]
      intro a ha
      exact Finset.mem_image.2 ⟨a, ha, rfl⟩

/-- Push-forward of the uniform distribution on `s` along `f`. -/
noncomputable def imageWeight {A B : Type*} [DecidableEq A]
    [DecidableEq B] (s : Finset A) (f : A → B) (b : B) : ℝ :=
  ((s.filter fun a ↦ f a = b).card : ℝ) / s.card

theorem imageWeight_pos_of_mem {A B : Type*} [DecidableEq A]
    [DecidableEq B] (s : Finset A) (f : A → B) (b : B)
    (hb : b ∈ s.image f) : 0 < imageWeight s f b := by
  obtain ⟨a, ha, hab⟩ := Finset.mem_image.1 hb
  have hnum : 0 < (s.filter fun x ↦ f x = b).card :=
    Finset.card_pos.mpr ⟨a, Finset.mem_filter.2 ⟨ha, hab⟩⟩
  have hden : 0 < s.card := Finset.card_pos.mpr ⟨a, ha⟩
  exact div_pos (by exact_mod_cast hnum) (by exact_mod_cast hden)

theorem sum_imageWeight_eq_one {A B : Type*} [DecidableEq A]
    [Fintype B] [DecidableEq B] (s : Finset A) (f : A → B)
    (hs : s.Nonempty) :
    ∑ b ∈ s.image f, imageWeight s f b = 1 := by
  have hsne : (s.card : ℝ) ≠ 0 := by
    exact_mod_cast Finset.card_ne_zero.mpr hs
  simp only [imageWeight, div_eq_mul_inv, ← Finset.sum_mul]
  rw [show (∑ b ∈ s.image f,
      ((s.filter fun a ↦ f a = b).card : ℝ)) = (s.card : ℝ) by
    exact_mod_cast sum_card_fibers s f]
  exact mul_inv_cancel₀ hsne

/-- Exact entropy decomposition for a uniform finite set and one coordinate.
This is the numeric one-step chain rule used below; it is proved here rather
than assumed. -/
theorem finiteEntropy_imageWeight_eq_log_card_sub_average_log_fiber
    {A B : Type*} [DecidableEq A] [Fintype B] [DecidableEq B]
    (s : Finset A) (f : A → B) (hs : s.Nonempty) :
    finiteEntropy (s.image f) (imageWeight s f) =
      Real.log s.card -
        (s.card : ℝ)⁻¹ *
          ∑ a ∈ s, Real.log (s.filter fun x ↦ f x = f a).card := by
  have hspos : 0 < (s.card : ℝ) := by
    exact_mod_cast Finset.card_pos.mpr hs
  have hsne : (s.card : ℝ) ≠ 0 := hspos.ne'
  have hmass :
      ∑ b ∈ s.image f, imageWeight s f b = 1 := by
    simp only [imageWeight, div_eq_mul_inv, ← Finset.sum_mul]
    rw [show (∑ b ∈ s.image f,
        ((s.filter fun a ↦ f a = b).card : ℝ)) = (s.card : ℝ) by
      exact_mod_cast sum_card_fibers s f]
    exact mul_inv_cancel₀ hsne
  rw [finiteEntropy]
  calc
    (∑ b ∈ s.image f, (imageWeight s f b).negMulLog) =
        ∑ b ∈ s.image f,
          imageWeight s f b *
            (Real.log s.card -
              Real.log (s.filter fun a ↦ f a = b).card) := by
      apply Finset.sum_congr rfl
      intro b hb
      obtain ⟨a, ha, hab⟩ := Finset.mem_image.1 hb
      have hfpos : 0 < ((s.filter fun x ↦ f x = b).card : ℝ) := by
        exact_mod_cast Finset.card_pos.mpr ⟨a, Finset.mem_filter.2 ⟨ha, hab⟩⟩
      rw [Real.negMulLog, imageWeight,
        Real.log_div hfpos.ne' hsne]
      ring
    _ = Real.log s.card -
        (s.card : ℝ)⁻¹ *
          ∑ b ∈ s.image f,
            ((s.filter fun a ↦ f a = b).card : ℝ) *
              Real.log (s.filter fun a ↦ f a = b).card := by
      simp only [mul_sub, Finset.sum_sub_distrib]
      have hfirst :
          ∑ b ∈ s.image f, imageWeight s f b * Real.log s.card =
            Real.log s.card := by
        rw [← Finset.sum_mul, hmass, one_mul]
      have hsecond :
          ∑ b ∈ s.image f,
              imageWeight s f b *
                Real.log (s.filter fun a ↦ f a = b).card =
            (s.card : ℝ)⁻¹ *
              ∑ b ∈ s.image f,
                ((s.filter fun a ↦ f a = b).card : ℝ) *
                  Real.log (s.filter fun a ↦ f a = b).card := by
        rw [Finset.mul_sum]
        apply Finset.sum_congr rfl
        intro b hb
        simp only [imageWeight, div_eq_mul_inv]
        ring
      rw [hfirst, hsecond]
    _ = Real.log s.card -
        (s.card : ℝ)⁻¹ *
          ∑ a ∈ s, Real.log (s.filter fun x ↦ f x = f a).card := by
      rw [sum_card_fibers_mul s f
        (fun b ↦ Real.log (s.filter fun a ↦ f a = b).card)]

/-- One exact finite reveal step, already arranged in the direction used by
the iterated entropy argument. -/
theorem log_card_le_log_image_card_add_average_log_fiber
    {A B : Type*} [DecidableEq A] [Fintype B] [DecidableEq B]
    (s : Finset A) (f : A → B) (hs : s.Nonempty) :
    Real.log s.card ≤ Real.log (s.image f).card +
      (s.card : ℝ)⁻¹ *
        ∑ a ∈ s, Real.log (s.filter fun x ↦ f x = f a).card := by
  have hentropy := finiteEntropy_le_log_card_of_pos
    (s.image f) (imageWeight s f)
    (imageWeight_pos_of_mem s f)
    (sum_imageWeight_eq_one s f hs)
  rw [finiteEntropy_imageWeight_eq_log_card_sub_average_log_fiber
    s f hs] at hentropy
  linarith

/-! ## An iterated finite reveal chain -/

/-- Exact recursively averaged reveal cost.  The recursion is a finite
conditional expectation: at a node `s`, reveal coordinate `i`, pay the log
of its exact image support, then average the tail cost in the exact fibers. -/
noncomputable def revealEntropyBudget {A I B : Type*} [DecidableEq A]
    [DecidableEq B] (s : Finset A) (code : A → I → B) : List I → ℝ
  | [] => 0
  | i :: is =>
      Real.log (s.image fun a ↦ code a i).card +
        (s.card : ℝ)⁻¹ * ∑ a ∈ s,
          revealEntropyBudget
            (s.filter fun x ↦ code x i = code a i) code is

/-- Full finite Shannon iteration.  Terminal injectivity is the only coding
hypothesis: if two elements have equal values on every revealed coordinate,
they are equal.  No chain rule is assumed; the proof iterates the one-step
identity above over explicit `Finset` fibers. -/
theorem log_card_le_revealEntropyBudget
    {A I B : Type*} [DecidableEq A] [Fintype B] [DecidableEq B]
    (s : Finset A) (code : A → I → B) (order : List I)
    (hs : s.Nonempty)
    (hinj : ∀ a ∈ s, ∀ b ∈ s,
      (∀ i ∈ order, code a i = code b i) → a = b) :
    Real.log s.card ≤ revealEntropyBudget s code order := by
  induction order generalizing s with
  | nil =>
      obtain ⟨a, ha⟩ := hs
      have hsingleton : s = {a} := by
        ext b
        constructor
        · intro hb
          have hba : b = a := hinj b hb a ha (by simp)
          simpa [hba]
        · intro hb
          have hba : b = a := by simpa using hb
          subst b
          exact ha
      simp [hsingleton, revealEntropyBudget]
  | cons i is ih =>
      have hone := log_card_le_log_image_card_add_average_log_fiber
        s (fun a ↦ code a i) hs
      have htail :
          ∑ a ∈ s,
              Real.log (s.filter fun x ↦ code x i = code a i).card ≤
            ∑ a ∈ s,
              revealEntropyBudget
                (s.filter fun x ↦ code x i = code a i) code is := by
        apply Finset.sum_le_sum
        intro a ha
        let fiber := s.filter fun x ↦ code x i = code a i
        have hafiber : a ∈ fiber := Finset.mem_filter.2 ⟨ha, rfl⟩
        apply ih fiber
        · exact ⟨a, hafiber⟩
        · intro x hx y hy hagree
          apply hinj x (Finset.mem_filter.1 hx).1 y
            (Finset.mem_filter.1 hy).1
          intro j hj
          simp only [List.mem_cons] at hj
          rcases hj with rfl | hj
          · exact (Finset.mem_filter.1 hx).2.trans
              (Finset.mem_filter.1 hy).2.symm
          · exact hagree j hj
      rw [revealEntropyBudget]
      have hcardnonneg : 0 ≤ (s.card : ℝ) := by positivity
      have hmul := mul_le_mul_of_nonneg_left htail
        (inv_nonneg.mpr hcardnonneg)
      linarith

/-! ## Fixed reveal orders for stable matchings -/

/-- `order` maps a reveal position to the man revealed there. -/
def fixedOrderRevealed {n : Nat} (order : Equiv.Perm (Fin n))
    (k : Nat) (p : Fin n) : Prop :=
  (order.symm p).val < k

instance {n : Nat} (order : Equiv.Perm (Fin n)) (k : Nat) :
    DecidablePred (fixedOrderRevealed order k) := by
  intro p
  unfold fixedOrderRevealed
  infer_instance

/-- Every matching code is determined by its partner values in a complete
permutation reveal order. -/
theorem matchingCode_ext_of_agree_on_order {n : Nat}
    (order : Equiv.Perm (Fin n)) (mu nu : MatchingCode n)
    (h : ∀ p ∈ List.ofFn order, mu p = nu p) : mu = nu := by
  apply Equiv.ext
  intro m
  have hm : m ∈ List.ofFn order := by
    rw [List.mem_ofFn]
    exact ⟨order.symm m, order.apply_symm_apply m⟩
  exact h m hm

/-- The finite Shannon chain for the actual set of stable matchings in any
fixed reveal order.  Its right-hand side is the recursively exact finite
conditional expectation of the log support size at every coordinate. -/
theorem log_stableCount_le_fixedOrder_revealEntropyBudget {n : Nat}
    (P : ProfileCode n) (order : Equiv.Perm (Fin n))
    (hstable : (stableSet P).Nonempty) :
    Real.log (stableCount P) ≤
      revealEntropyBudget (stableSet P)
        (fun mu m ↦ mu m) (List.ofFn order) := by
  rw [stableCount]
  apply log_card_le_revealEntropyBudget
  · exact hstable
  · intro mu hmu nu hnu hagree
    exact matchingCode_ext_of_agree_on_order order mu nu hagree

/-- Empty stable families are not silently turned into probability spaces.
For every coded profile we either expose emptiness, or obtain the complete
fixed-order Shannon bound above. -/
theorem stableSet_empty_or_log_stableCount_le_fixedOrder_budget {n : Nat}
    (P : ProfileCode n) (order : Equiv.Perm (Fin n)) :
    stableSet P = ∅ ∨
      Real.log (stableCount P) ≤
        revealEntropyBudget (stableSet P)
          (fun mu m ↦ mu m) (List.ofFn order) := by
  classical
  by_cases hs : (stableSet P).Nonempty
  · exact Or.inr (log_stableCount_le_fixedOrder_revealEntropyBudget P order hs)
  · exact Or.inl (Finset.not_nonempty_iff_eq_empty.mp hs)

theorem sum_partnerWeight_eq_one {n : Nat} (P : ProfileCode n)
    (base : MatchingCode n) (revealed : Fin n → Prop)
    [DecidablePred revealed] (m : Fin n) (hbase : Stable P base) :
    ∑ w ∈ conditionalPartnerSupport P base revealed m,
      partnerWeight P base revealed m w = 1 := by
  classical
  have hcard : ((stableFiber P base revealed).card : ℝ) ≠ 0 := by
    exact_mod_cast Finset.card_ne_zero.mpr
      (stableFiber_nonempty P base revealed hbase)
  rw [show (∑ w ∈ conditionalPartnerSupport P base revealed m,
      partnerWeight P base revealed m w) =
      ((∑ w ∈ conditionalPartnerSupport P base revealed m,
          ((stableFiber P base revealed).filter fun nu ↦ nu m = w).card : ℝ) /
        (stableFiber P base revealed).card) by
      simp only [partnerWeight, Finset.sum_div]]
  have hpartitionNat :
      ∑ w ∈ conditionalPartnerSupport P base revealed m,
          ((stableFiber P base revealed).filter fun nu ↦ nu m = w).card =
        (stableFiber P base revealed).card := by
    exact sum_card_fibers (stableFiber P base revealed) (fun nu ↦ nu m)
  have hpartition :
      ∑ w ∈ conditionalPartnerSupport P base revealed m,
          (((stableFiber P base revealed).filter fun nu ↦ nu m = w).card : ℝ) =
        ((stableFiber P base revealed).card : ℝ) := by
    exact_mod_cast hpartitionNat
  rw [hpartition]
  exact div_self hcard

theorem partnerWeight_pos_of_mem {n : Nat} (P : ProfileCode n)
    (base : MatchingCode n) (revealed : Fin n → Prop)
    [DecidablePred revealed] (m w : Fin n)
    (hw : w ∈ conditionalPartnerSupport P base revealed m) :
    0 < partnerWeight P base revealed m w := by
  obtain ⟨nu, hnu, heq⟩ := Finset.mem_image.1 hw
  have hnum : 0 <
      ((stableFiber P base revealed).filter fun sigma ↦ sigma m = w).card := by
    exact Finset.card_pos.mpr ⟨nu, Finset.mem_filter.2 ⟨hnu, heq⟩⟩
  have hden : 0 < (stableFiber P base revealed).card :=
    Finset.card_pos.mpr ⟨nu, hnu⟩
  exact div_pos (by exact_mod_cast hnum) (by exact_mod_cast hden)

/-- The actual conditional partner entropy in a nonempty stable fiber is at
most the logarithm of the actual conditional-support cardinality. -/
theorem stableFiber_partnerEntropy_le_log_card {n : Nat} (P : ProfileCode n)
    (base : MatchingCode n) (revealed : Fin n → Prop)
    [DecidablePred revealed] (m : Fin n) (hbase : Stable P base) :
    finiteEntropy (conditionalPartnerSupport P base revealed m)
        (partnerWeight P base revealed m) ≤
      Real.log (conditionalPartnerSupport P base revealed m).card := by
  apply finiteEntropy_le_log_card_of_pos
  · intro w hw
    exact partnerWeight_pos_of_mem P base revealed m w hw
  · exact sum_partnerWeight_eq_one P base revealed m hbase

/-- Combine the finite Shannon support inequality with the exact nearest
revealed-window theorem. -/
theorem stableFiber_partnerEntropy_le_log_window {n q : Nat}
    (P : ProfileCode n) (m : Fin n)
    (E : StableMatchings355.ExactStablePartnerEnumeration (q := q) P.toCore m)
    (base : MatchingCode n) (revealed : Fin n → Prop)
    [DecidablePred revealed] {j : Fin q}
    (hbase : Stable P base)
    (hbaseTarget : base m = E.ranked.partner j)
    (W : StableMatchings355.NearestRevealedWindow E base.toCore revealed j)
    (S : StableMatchings355.ExactConditionalIndexSupport
      P.toCore E base.toCore revealed) :
    finiteEntropy (conditionalPartnerSupport P base revealed m)
        (partnerWeight P base revealed m) ≤
      Real.log ((StableMatchings355.upperBoundary W.upper -
        StableMatchings355.lowerBoundary W.lower : Nat) : ℝ) := by
  calc
    finiteEntropy (conditionalPartnerSupport P base revealed m)
        (partnerWeight P base revealed m) ≤
        Real.log (conditionalPartnerSupport P base revealed m).card :=
      stableFiber_partnerEntropy_le_log_card P base revealed m hbase
    _ ≤ Real.log ((StableMatchings355.upperBoundary W.upper -
          StableMatchings355.lowerBoundary W.lower : Nat) : ℝ) := by
      apply Real.log_le_log
      · exact_mod_cast Finset.card_pos.mpr
          (conditionalPartnerSupport_nonempty P base revealed m hbase)
      · exact_mod_cast conditionalPartnerSupport_card_le_window
          P m E base revealed hbase hbaseTarget W S

/-- Certificate-free local application.  Every stable base, revealed set and
target coordinate have an exact support/window certificate controlling the
true finite conditional entropy. -/
theorem exists_stableFiber_partnerEntropy_window_bound {n : Nat}
    (P : ProfileCode n) (m : Fin n) (base : MatchingCode n)
    (revealed : Fin n → Prop) [DecidablePred revealed]
    (hbase : Stable P base) :
    ∃ q,
      ∃ E : StableMatchings355.ExactStablePartnerEnumeration
        (q := q) P.toCore m,
      ∃ j : Fin q,
        base m = E.ranked.partner j ∧
        ∃ W : StableMatchings355.NearestRevealedWindow
          E base.toCore revealed j,
        ∃ S : StableMatchings355.ExactConditionalIndexSupport
          P.toCore E base.toCore revealed,
          finiteEntropy (conditionalPartnerSupport P base revealed m)
              (partnerWeight P base revealed m) ≤
            Real.log ((StableMatchings355.upperBoundary W.upper -
              StableMatchings355.lowerBoundary W.lower : Nat) : ℝ) := by
  obtain ⟨q, E, j, hj, W, S, hlen⟩ :=
    StableMatchings355.exists_full_conditional_support_bridge
      P.toCore m base.toCore revealed ((stableCode_iff_core P base).1 hbase)
  exact ⟨q, E, j, hj, W, S,
    stableFiber_partnerEntropy_le_log_window
      P m E base revealed hbase hj W S⟩

/-- At every position of a fixed reveal order, the true stable-matching
fiber has a certificate-free FullInterval window controlling its exact
conditional Shannon entropy. -/
theorem exists_fixedOrder_localEntropy_window_bound {n : Nat}
    (P : ProfileCode n) (order : Equiv.Perm (Fin n)) (k : Fin n)
    (base : MatchingCode n) (hbase : Stable P base) :
    ∃ q,
      ∃ E : StableMatchings355.ExactStablePartnerEnumeration
        (q := q) P.toCore (order k),
      ∃ j : Fin q,
        base (order k) = E.ranked.partner j ∧
        ∃ W : StableMatchings355.NearestRevealedWindow
          E base.toCore (fixedOrderRevealed order k.val) j,
        ∃ S : StableMatchings355.ExactConditionalIndexSupport
          P.toCore E base.toCore (fixedOrderRevealed order k.val),
          finiteEntropy
              (conditionalPartnerSupport P base
                (fixedOrderRevealed order k.val) (order k))
              (partnerWeight P base
                (fixedOrderRevealed order k.val) (order k)) ≤
            Real.log ((StableMatchings355.upperBoundary W.upper -
              StableMatchings355.lowerBoundary W.lower : Nat) : ℝ) := by
  exact exists_stableFiber_partnerEntropy_window_bound
    P (order k) base (fixedOrderRevealed order k.val) hbase

end StableMatchingsE2E
