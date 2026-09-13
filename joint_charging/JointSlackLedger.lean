import StableMatchingsE2E.MethodLimit

namespace StableMatchingsJointCharging

open MeasureTheory ProbabilityTheory Set
open scoped unitInterval ENNReal BigOperators
open StableMatchings355 StableMatchingsEntropy StableMatchingsE2E

noncomputable section

def totalJointSlack {n : Nat} (P : ProfileCode n) : ℝ :=
  (n : ℝ) * geometricLogSeries - Real.log (stableCount P)

def aggregateGeometricSlack {n : Nat} {P : ProfileCode n}
    (D : StaticWindowData P) : ℝ :=
  (n : ℝ) * geometricLogSeries -
    ∫ priority, aggregateLexCost D priority ∂(FullPriorityMeasure n)

def aggregateEntropyMarkerSlack {n : Nat} {P : ProfileCode n}
    (D : StaticWindowData P) : ℝ :=
  (∫ priority, aggregateLexCost D priority ∂(FullPriorityMeasure n)) -
    Real.log (stableCount P)

theorem totalJointSlack_eq_two_stage {n : Nat} {P : ProfileCode n}
    (D : StaticWindowData P) :
    totalJointSlack P =
      aggregateGeometricSlack D + aggregateEntropyMarkerSlack D := by
  simp only [totalJointSlack, aggregateGeometricSlack,
    aggregateEntropyMarkerSlack]
  ring

theorem aggregateGeometricSlack_nonneg {n : Nat} {P : ProfileCode n}
    (D : StaticWindowData P) (hstable : (stableSet P).Nonempty) :
    0 ≤ aggregateGeometricSlack D := by
  unfold aggregateGeometricSlack
  linarith [integral_aggregateLexCost_le_geometricLogSeries D hstable]

theorem aggregateEntropyMarkerSlack_nonneg {n : Nat} {P : ProfileCode n}
    (D : StaticWindowData P) (hstable : (stableSet P).Nonempty) :
    0 ≤ aggregateEntropyMarkerSlack D := by
  unfold aggregateEntropyMarkerSlack
  have hmono : Real.log (stableCount P) ≤
      ∫ priority, aggregateLexCost D priority
        ∂(FullPriorityMeasure n) := by
    have h := MeasureTheory.integral_mono
      (integrable_const (Real.log (stableCount P)) :
        Integrable (fun _ : Fin n → I ↦ Real.log (stableCount P))
          (FullPriorityMeasure n))
      (integrable_aggregateLexCost D)
      (fun priority ↦ log_stableCount_le_aggregateLexCost D priority hstable)
    simpa using h
  linarith

theorem totalJointSlack_nonneg {n : Nat} {P : ProfileCode n}
    (D : StaticWindowData P) (hstable : (stableSet P).Nonempty) :
    0 ≤ totalJointSlack P := by
  rw [totalJointSlack_eq_two_stage D]
  exact add_nonneg
    (aggregateGeometricSlack_nonneg D hstable)
    (aggregateEntropyMarkerSlack_nonneg D hstable)

theorem jointSlack_linear_lower_iff_log_bound {n : Nat}
    (P : ProfileCode n) (δ : ℝ) :
    (n : ℝ) * δ ≤ totalJointSlack P ↔
      Real.log (stableCount P) ≤
        (n : ℝ) * (geometricLogSeries - δ) := by
  unfold totalJointSlack
  constructor <;> intro h <;> linarith

/-! ## Exact entropy-to-support slack along a finite reveal chain -/

noncomputable def revealKLSlackBudget {A J B : Type*}
    [DecidableEq A] [Fintype B] [DecidableEq B]
    (s : Finset A) (code : A → J → B) : List J → ℝ
  | [] => 0
  | i :: is =>
      (Real.log (s.image fun a ↦ code a i).card -
        finiteEntropy (s.image fun a ↦ code a i)
          (imageWeight s fun a ↦ code a i)) +
      (s.card : ℝ)⁻¹ * ∑ a ∈ s,
        revealKLSlackBudget
          (s.filter fun x ↦ code x i = code a i) code is

/-- The recursively averaged log-support budget minus the exact uniform-set
entropy is exactly the accumulated conditional KL-to-uniform slack. -/
theorem revealEntropyBudget_sub_log_card_eq_KLSlackBudget
    {A J B : Type*} [DecidableEq A] [Fintype B] [DecidableEq B]
    (s : Finset A) (code : A → J → B) (order : List J)
    (hs : s.Nonempty)
    (hinj : ∀ a ∈ s, ∀ b ∈ s,
      (∀ i ∈ order, code a i = code b i) → a = b) :
    revealEntropyBudget s code order - Real.log s.card =
      revealKLSlackBudget s code order := by
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
      simp [revealEntropyBudget, revealKLSlackBudget, hsingleton]
  | cons i is ih =>
      let f : A → B := fun a ↦ code a i
      have hentropy :=
        finiteEntropy_imageWeight_eq_log_card_sub_average_log_fiber s f hs
      have htail :
          (∑ a ∈ s,
              revealEntropyBudget (s.filter fun x ↦ f x = f a) code is) =
            ∑ a ∈ s,
              (revealKLSlackBudget (s.filter fun x ↦ f x = f a) code is +
                Real.log (s.filter fun x ↦ f x = f a).card) := by
        apply Finset.sum_congr rfl
        intro a ha
        have hfiber : (s.filter fun x ↦ f x = f a).Nonempty :=
          ⟨a, Finset.mem_filter.2 ⟨ha, rfl⟩⟩
        have hfiberInj : ∀ x ∈ (s.filter fun x ↦ f x = f a),
            ∀ y ∈ (s.filter fun x ↦ f x = f a),
              (∀ j ∈ is, code x j = code y j) → x = y := by
          intro x hx y hy hagree
          apply hinj x (Finset.mem_filter.1 hx).1 y
            (Finset.mem_filter.1 hy).1
          intro j hj
          simp only [List.mem_cons] at hj
          rcases hj with rfl | hj
          · exact (Finset.mem_filter.1 hx).2.trans
              (Finset.mem_filter.1 hy).2.symm
          · exact hagree j hj
        have hih := ih (s.filter fun x ↦ f x = f a) hfiber hfiberInj
        linarith
      simp only [revealEntropyBudget, revealKLSlackBudget]
      change
        Real.log (s.image f).card +
            (s.card : ℝ)⁻¹ *
              ∑ a ∈ s,
                revealEntropyBudget (s.filter fun x ↦ f x = f a) code is -
              Real.log s.card = _
      rw [htail, Finset.sum_add_distrib, hentropy]
      ring

theorem revealKLSlackBudget_nonneg
    {A J B : Type*} [DecidableEq A] [Fintype B] [DecidableEq B]
    (s : Finset A) (code : A → J → B) (order : List J)
    (hs : s.Nonempty) :
    0 ≤ revealKLSlackBudget s code order := by
  induction order generalizing s with
  | nil => simp [revealKLSlackBudget]
  | cons i is ih =>
      let f : A → B := fun a ↦ code a i
      have himage : (s.image f).Nonempty := hs.image f
      have hnode :
          finiteEntropy (s.image f) (imageWeight s f) ≤
            Real.log (s.image f).card := by
        apply finiteEntropy_le_log_card_of_pos
        · intro b hb
          exact imageWeight_pos_of_mem s f b hb
        · exact sum_imageWeight_eq_one s f hs
      have htail : 0 ≤
          ∑ a ∈ s,
            revealKLSlackBudget (s.filter fun x ↦ f x = f a) code is := by
        apply Finset.sum_nonneg
        intro a ha
        apply ih
        exact ⟨a, Finset.mem_filter.2 ⟨ha, rfl⟩⟩
      simp only [revealKLSlackBudget]
      change 0 ≤
        (Real.log (s.image f).card -
          finiteEntropy (s.image f) (imageWeight s f)) +
        (s.card : ℝ)⁻¹ *
          ∑ a ∈ s,
            revealKLSlackBudget (s.filter fun x ↦ f x = f a) code is
      exact add_nonneg (sub_nonneg.mpr hnode)
        (mul_nonneg (inv_nonneg.mpr (Nat.cast_nonneg s.card)) htail)

/-! ## Stable-matching specialization and pointwise `A+B` split -/

noncomputable def priorityKLSlack {n : Nat} (P : ProfileCode n)
    (priority : Fin n → I) : ℝ :=
  revealKLSlackBudget (stableSet P) (fun mu m ↦ mu m)
    (List.ofFn (priorityOrder priority))

noncomputable def prioritySupportWindowSlack {n : Nat} {P : ProfileCode n}
    (D : StaticWindowData P) (priority : Fin n → I) : ℝ :=
  aggregateLexCost D priority -
    revealEntropyBudget (stableSet P) (fun mu m ↦ mu m)
      (List.ofFn (priorityOrder priority))

theorem revealEntropyBudget_sub_log_stableCount_eq_priorityKLSlack
    {n : Nat} (P : ProfileCode n) (priority : Fin n → I)
    (hstable : (stableSet P).Nonempty) :
    revealEntropyBudget (stableSet P) (fun mu m ↦ mu m)
        (List.ofFn (priorityOrder priority)) - Real.log (stableCount P) =
      priorityKLSlack P priority := by
  have h := revealEntropyBudget_sub_log_card_eq_KLSlackBudget
    (stableSet P) (fun mu m ↦ mu m)
    (List.ofFn (priorityOrder priority)) hstable
    (fun mu hmu nu hnu hagree ↦
      matchingCode_ext_of_agree_on_order (priorityOrder priority)
        mu nu hagree)
  simpa only [stableCount, priorityKLSlack] using h

theorem priorityKLSlack_nonneg {n : Nat} (P : ProfileCode n)
    (priority : Fin n → I) (hstable : (stableSet P).Nonempty) :
    0 ≤ priorityKLSlack P priority := by
  exact revealKLSlackBudget_nonneg (stableSet P) (fun mu m ↦ mu m)
    (List.ofFn (priorityOrder priority)) hstable

theorem prioritySupportWindowSlack_nonneg {n : Nat} {P : ProfileCode n}
    (D : StaticWindowData P) (priority : Fin n → I)
    (hstable : (stableSet P).Nonempty) :
    0 ≤ prioritySupportWindowSlack D priority := by
  unfold prioritySupportWindowSlack
  rw [← uniformPrefixWindowExpectation_priority_eq_aggregate D priority]
  exact sub_nonneg.mpr
    (revealEntropyBudget_le_uniformPrefixWindowExpectation P D.selector
      (List.ofFn (priorityOrder priority)) hstable)

/-- The literal per-base path gap whose uniform average is the global
support/window slack.  This is the normalization needed by local charging:
there is no hidden extra factor of `n` or of the number of stable matchings. -/
noncomputable def supportWindowPathGap {n : Nat} {P : ProfileCode n}
    (D : StaticWindowData P) (priority : Fin n → I)
    (base : MatchingCode n) : ℝ :=
  if h : Stable P base then
    prefixWindowPathBudget P D.selector ⟨base, h⟩ []
        (List.ofFn (priorityOrder priority)) -
      revealPathBudget (stableSet P) (fun mu m ↦ mu m) base
        (List.ofFn (priorityOrder priority))
  else 0

theorem prioritySupportWindowSlack_eq_average_path_gap
    {n : Nat} {P : ProfileCode n}
    (D : StaticWindowData P) (priority : Fin n → I)
    (hstable : (stableSet P).Nonempty) :
    prioritySupportWindowSlack D priority =
      ((stableSet P).card : ℝ)⁻¹ *
        ∑ base ∈ stableSet P, supportWindowPathGap D priority base := by
  rw [prioritySupportWindowSlack]
  rw [← uniformPrefixWindowExpectation_priority_eq_aggregate D priority]
  rw [revealEntropyBudget_eq_uniform_pathBudget
    (stableSet P) (fun mu m ↦ mu m)
    (List.ofFn (priorityOrder priority)) hstable]
  unfold uniformPrefixWindowExpectation supportWindowPathGap
  rw [← mul_sub]
  congr 1
  rw [← Finset.sum_sub_distrib]
  apply Finset.sum_congr rfl
  intro base hbase
  have hs : Stable P base := (mem_stableSet_iff P base).1 hbase
  simp [prefixWindowPathBudgetOrZero, hs]

/-- A literal one-node B charge.  If the exact conditional partner support
at the head node is a singleton while the certified window has width at
least two, the entire remaining path gap is at least `log 2`; all later node
gaps are nonnegative by the existing window bridge. -/
theorem prefixWindow_sub_reveal_ge_log_two_of_head
    {n : Nat} {P : ProfileCode n}
    (D : StaticWindowData P) (base : StableBase P)
    (seen : List (Fin n)) (m : Fin n) (ms : List (Fin n))
    (hsupport :
      (conditionalPartnerSupport P base.1 (listRevealed seen) m).card = 1)
    (hwidth : 2 ≤
      markerWindowWidth
        (leftMarkerBits (D.enumeration m) base.1.toCore
          (listRevealed seen) (D.center base m))
        (rightMarkerBits (D.enumeration m) base.1.toCore
          (listRevealed seen) (D.center base m))) :
    Real.log 2 ≤
      prefixWindowPathBudget P D.selector base seen (m :: ms) -
        revealPathBudget
          (listPrefixFiber (stableSet P) (fun mu p ↦ mu p) seen base.1)
          (fun mu p ↦ mu p) base.1 (m :: ms) := by
  simp only [prefixWindowPathBudget, revealPathBudget]
  have himage := image_listPrefixFiber_eq_conditionalPartnerSupport_list
    P seen m base.1
  have htail := revealPathBudget_le_prefixWindowPathBudget
    P D.selector base (seen ++ [m]) ms
  have hfiber :
      (listPrefixFiber (stableSet P) (fun mu p ↦ mu p) seen base.1).filter
          (fun x ↦ x m = base.1 m) =
        listPrefixFiber (stableSet P) (fun mu p ↦ mu p)
          (seen ++ [m]) base.1 := by
    ext x
    simp only [Finset.mem_filter, mem_listPrefixFiber_iff]
    constructor
    · rintro ⟨⟨hxs, hseen⟩, hm⟩
      refine ⟨hxs, ?_⟩
      intro i hi
      rw [List.mem_append] at hi
      rcases hi with hi | hi
      · exact hseen i hi
      · have him : i = m := by simpa using hi
        subst i
        exact hm
    · rintro ⟨hxs, hall⟩
      refine ⟨⟨hxs, ?_⟩, ?_⟩
      · intro i hi
        exact hall i (List.mem_append_left [m] hi)
      · exact hall m (by simp)
  have hwidthReal : (2 : ℝ) ≤
      (markerWindowWidth
        (leftMarkerBits (D.enumeration m) base.1.toCore
          (listRevealed seen) (D.center base m))
        (rightMarkerBits (D.enumeration m) base.1.toCore
          (listRevealed seen) (D.center base m)) : ℕ) := by
    exact_mod_cast hwidth
  have hlogwidth : Real.log 2 ≤
      Real.log
        ((markerWindowWidth
          (leftMarkerBits (D.enumeration m) base.1.toCore
            (listRevealed seen) (D.center base m))
          (rightMarkerBits (D.enumeration m) base.1.toCore
            (listRevealed seen) (D.center base m)) : ℕ) : ℝ) := by
    exact Real.log_le_log (by norm_num) hwidthReal
  rw [himage, hsupport, hfiber]
  norm_num
  exact le_sub_iff_add_le.mpr (by linarith)

theorem aggregateEntropyMarkerGap_eq_priority_KL_add_supportWindow
    {n : Nat} {P : ProfileCode n} (D : StaticWindowData P)
    (priority : Fin n → I) (hstable : (stableSet P).Nonempty) :
    aggregateLexCost D priority - Real.log (stableCount P) =
      priorityKLSlack P priority + prioritySupportWindowSlack D priority := by
  rw [← revealEntropyBudget_sub_log_stableCount_eq_priorityKLSlack
    P priority hstable]
  unfold prioritySupportWindowSlack
  ring

theorem priority_KL_add_supportWindow_nonneg
    {n : Nat} {P : ProfileCode n} (D : StaticWindowData P)
    (priority : Fin n → I) (hstable : (stableSet P).Nonempty) :
    0 ≤ priorityKLSlack P priority + prioritySupportWindowSlack D priority :=
  add_nonneg (priorityKLSlack_nonneg P priority hstable)
    (prioritySupportWindowSlack_nonneg D priority hstable)

theorem aggregateEntropyMarkerSlack_eq_integral_priority_slacks
    {n : Nat} {P : ProfileCode n} (D : StaticWindowData P)
    (hstable : (stableSet P).Nonempty) :
    aggregateEntropyMarkerSlack D =
      ∫ priority,
        (priorityKLSlack P priority + prioritySupportWindowSlack D priority)
        ∂(FullPriorityMeasure n) := by
  unfold aggregateEntropyMarkerSlack
  calc
    (∫ priority, aggregateLexCost D priority ∂(FullPriorityMeasure n)) -
        Real.log (stableCount P) =
      ∫ priority,
        (aggregateLexCost D priority - Real.log (stableCount P))
        ∂(FullPriorityMeasure n) := by
          rw [MeasureTheory.integral_sub (integrable_aggregateLexCost D)
            (integrable_const (Real.log (stableCount P)))]
          simp
    _ = _ := by
      apply MeasureTheory.integral_congr_ae
      exact Filter.Eventually.of_forall fun priority ↦
        aggregateEntropyMarkerGap_eq_priority_KL_add_supportWindow
          D priority hstable

theorem totalJointSlack_eq_geometric_add_integral_KL_supportWindow
    {n : Nat} {P : ProfileCode n} (D : StaticWindowData P)
    (hstable : (stableSet P).Nonempty) :
    totalJointSlack P = aggregateGeometricSlack D +
      ∫ priority,
        (priorityKLSlack P priority + prioritySupportWindowSlack D priority)
        ∂(FullPriorityMeasure n) := by
  rw [totalJointSlack_eq_two_stage D,
    aggregateEntropyMarkerSlack_eq_integral_priority_slacks D hstable]

/-! ## Per-stable-base, per-target decomposition of the geometric gap -/

noncomputable def actualTargetIntegral {n : Nat} {P : ProfileCode n}
    (D : StaticWindowData P) (base : MatchingCode n) (m : Fin n) : ℝ :=
  ∫ priority,
    if h : Stable P base then
      lexTargetMarkerLog D ⟨base, h⟩ priority m
    else 0
    ∂(FullPriorityMeasure n)

noncomputable def targetGeometricSlack {n : Nat} {P : ProfileCode n}
    (D : StaticWindowData P) (base : MatchingCode n) (m : Fin n) : ℝ :=
  geometricLogSeries - actualTargetIntegral D base m

noncomputable def averagedTargetGeometricSlack {n : Nat}
    {P : ProfileCode n} (D : StaticWindowData P) : ℝ :=
  ((stableSet P).card : ℝ)⁻¹ *
    ∑ base ∈ stableSet P, ∑ m : Fin n, targetGeometricSlack D base m

theorem targetGeometricSlack_nonneg_of_stable {n : Nat}
    {P : ProfileCode n} (D : StaticWindowData P)
    (base : MatchingCode n) (hbase : Stable P base) (m : Fin n) :
    0 ≤ targetGeometricSlack D base m := by
  unfold targetGeometricSlack actualTargetIntegral
  simp only [hbase, dif_pos]
  exact sub_nonneg.mpr
    (integral_full_lexTargetMarkerLog_le_geometricLogSeries
      D ⟨base, hbase⟩ m)

theorem averagedTargetGeometricSlack_nonneg {n : Nat}
    {P : ProfileCode n} (D : StaticWindowData P) :
    0 ≤ averagedTargetGeometricSlack D := by
  unfold averagedTargetGeometricSlack
  apply mul_nonneg (inv_nonneg.mpr (Nat.cast_nonneg _))
  apply Finset.sum_nonneg
  intro base hbase
  have hs : Stable P base := (mem_stableSet_iff P base).1 hbase
  exact Finset.sum_nonneg fun m _ ↦
    targetGeometricSlack_nonneg_of_stable D base hs m

theorem aggregateGeometricSlack_eq_averagedTargetGeometricSlack
    {n : Nat} {P : ProfileCode n} (D : StaticWindowData P)
    (hstable : (stableSet P).Nonempty) :
    aggregateGeometricSlack D = averagedTargetGeometricSlack D := by
  classical
  unfold aggregateGeometricSlack averagedTargetGeometricSlack
  rw [integral_aggregateLexCost_eq D]
  have hcard : ((stableSet P).card : ℝ) ≠ 0 := by
    exact_mod_cast Finset.card_ne_zero.mpr hstable
  have hactual :
      (∑ base ∈ stableSet P,
          ∑ m : Fin n, ∫ priority,
            if h : Stable P base then
              lexTargetMarkerLog D ⟨base, h⟩ priority m
            else 0
            ∂(FullPriorityMeasure n)) =
        ∑ base ∈ stableSet P,
          ∑ m : Fin n, actualTargetIntegral D base m := by
    rfl
  rw [hactual]
  have hgap :
      (∑ base ∈ stableSet P,
          ∑ m : Fin n, targetGeometricSlack D base m) =
        ((stableSet P).card : ℝ) * ((n : ℝ) * geometricLogSeries) -
          ∑ base ∈ stableSet P,
            ∑ m : Fin n, actualTargetIntegral D base m := by
    simp only [targetGeometricSlack, Finset.sum_sub_distrib]
    simp
  rw [hgap]
  field_simp

theorem totalJointSlack_eq_average_targetC_add_integral_A_B
    {n : Nat} {P : ProfileCode n} (D : StaticWindowData P)
    (hstable : (stableSet P).Nonempty) :
    totalJointSlack P = averagedTargetGeometricSlack D +
      ∫ priority,
        (priorityKLSlack P priority + prioritySupportWindowSlack D priority)
        ∂(FullPriorityMeasure n) := by
  rw [totalJointSlack_eq_geometric_add_integral_KL_supportWindow D hstable,
    aggregateGeometricSlack_eq_averagedTargetGeometricSlack D hstable]

/-! ## Exact finite-prefix functional on the shared-dummy space -/

noncomputable def finitePrefixCostNN (leftLen rightLen : Nat) : ENNReal :=
  ∫⁻ x : I, ∫⁻ z,
    prefixPairWindowLogNN leftLen rightLen
      (pairedPrefixVector leftLen rightLen z)
    ∂(InfiniteDummyPairMeasure x) ∂volume

noncomputable def finitePrefixCost (leftLen rightLen : Nat) : ℝ :=
  (finitePrefixCostNN leftLen rightLen).toReal

theorem lintegral_actualMarkerPair_eq_sharedFinitePrefix {n q : Nat}
    {P : Profile (Fin n) (Fin n)} {target : Fin n}
    (E : ExactStablePartnerEnumeration (q := q) P target)
    (base : Matching (Fin n) (Fin n)) (j : Fin q)
    (hbaseTarget : base.manPartner target = E.ranked.partner j)
    (x : I) :
    (∫⁻ ω, prefixPairWindowLogNN j.val (q - (j.val + 1))
        (actualMarkerPair E base j hbaseTarget x ω)
      ∂(TargetOtherPriorityMeasure target)) =
      ∫⁻ z, prefixPairWindowLogNN j.val (q - (j.val + 1))
        (pairedPrefixVector j.val (q - (j.val + 1)) z)
        ∂(InfiniteDummyPairMeasure x) := by
  calc
    _ = ∫⁻ v, prefixPairWindowLogNN j.val (q - (j.val + 1)) v
          ∂((TargetOtherPriorityMeasure target).map
            (actualMarkerPair E base j hbaseTarget x)) := by
      symm
      exact MeasureTheory.lintegral_map
        (measurable_prefixPairWindowLogNN _ _)
        (measurable_actualMarkerPair E base j hbaseTarget x)
    _ = ∫⁻ v, prefixPairWindowLogNN j.val (q - (j.val + 1)) v
          ∂((InfiniteDummyPairMeasure x).map
            (pairedPrefixVector j.val (q - (j.val + 1)))) := by
      rw [map_actualMarkerPair_eq_pairedPrefixVector E base j hbaseTarget x]
    _ = _ := by
      exact MeasureTheory.lintegral_map
        (measurable_prefixPairWindowLogNN _ _)
        (measurable_pairedPrefixVector _ _)

theorem lintegral_full_lexTargetMarkerLogNN_eq_finitePrefixCostNN
    {n : Nat} {P : ProfileCode n} (D : StaticWindowData P)
    (base : StableBase P) (m : Fin n) :
    (∫⁻ priority, lexTargetMarkerLogNN D base m priority
      ∂(FullPriorityMeasure n)) =
      finitePrefixCostNN (D.center base m).val
        (D.q m - ((D.center base m).val + 1)) := by
  calc
    _ = ∫⁻ z, lexTargetMarkerLogNN D base m
          (assemblePriority m z) ∂(SplitTargetPriorityMeasure m) := by
      rw [← map_assemblePriority_splitTargetPriorityMeasure m]
      exact MeasureTheory.lintegral_map
        (measurable_lexTargetMarkerLogNN D base m)
        (measurable_assemblePriority m)
    _ = ∫⁻ x : I, ∫⁻ ω,
          lexTargetMarkerLogNN D base m (assemblePriority m (x, ω))
          ∂(TargetOtherPriorityMeasure m) ∂volume := by
      exact MeasureTheory.lintegral_prod _
        ((measurable_lexTargetMarkerLogNN D base m).comp
          (measurable_assemblePriority m)).aemeasurable
    _ = ∫⁻ x : I, ∫⁻ ω,
          prefixPairWindowLogNN (D.center base m).val
            (D.q m - ((D.center base m).val + 1))
            (actualMarkerPair (D.enumeration m) base.1.toCore
              (D.center base m) (D.center_spec base m) x ω)
          ∂(TargetOtherPriorityMeasure m) ∂volume := by
      apply MeasureTheory.lintegral_congr
      intro x
      exact MeasureTheory.lintegral_congr_ae
        (ae_lexTargetMarkerLogNN_assemble_eq_actual D base m x)
    _ = _ := by
      unfold finitePrefixCostNN
      apply MeasureTheory.lintegral_congr
      intro x
      exact lintegral_actualMarkerPair_eq_sharedFinitePrefix
        (D.enumeration m) base.1.toCore (D.center base m)
        (D.center_spec base m) x

theorem integral_full_lexTargetMarkerLog_eq_finitePrefixCost
    {n : Nat} {P : ProfileCode n} (D : StaticWindowData P)
    (base : StableBase P) (m : Fin n) :
    (∫ priority, lexTargetMarkerLog D base priority m
      ∂(FullPriorityMeasure n)) =
      finitePrefixCost (D.center base m).val
        (D.q m - ((D.center base m).val + 1)) := by
  have hnonneg : 0 ≤
      ∫ priority, lexTargetMarkerLog D base priority m
        ∂(FullPriorityMeasure n) :=
    MeasureTheory.integral_nonneg_of_ae
      (Filter.Eventually.of_forall fun priority ↦
        lexTargetMarkerLog_nonneg D base priority m)
  have hOf :
      ENNReal.ofReal
          (∫ priority, lexTargetMarkerLog D base priority m
            ∂(FullPriorityMeasure n)) =
        finitePrefixCostNN (D.center base m).val
          (D.q m - ((D.center base m).val + 1)) := by
    rw [MeasureTheory.ofReal_integral_eq_lintegral_ofReal
      (integrable_lexTargetMarkerLog D base m)
      (Filter.Eventually.of_forall fun priority ↦
        lexTargetMarkerLog_nonneg D base priority m)]
    change (∫⁻ priority, lexTargetMarkerLogNN D base m priority
      ∂(FullPriorityMeasure n)) = _
    exact lintegral_full_lexTargetMarkerLogNN_eq_finitePrefixCostNN D base m
  unfold finitePrefixCost
  rw [← hOf, ENNReal.toReal_ofReal hnonneg]

theorem targetGeometricSlack_eq_series_sub_finitePrefixCost_of_stable
    {n : Nat} {P : ProfileCode n} (D : StaticWindowData P)
    (base : MatchingCode n) (hbase : Stable P base) (m : Fin n) :
    targetGeometricSlack D base m =
      geometricLogSeries - finitePrefixCost (D.center ⟨base, hbase⟩ m).val
        (D.q m - ((D.center ⟨base, hbase⟩ m).val + 1)) := by
  unfold targetGeometricSlack actualTargetIntegral
  simp only [hbase, dif_pos]
  rw [integral_full_lexTargetMarkerLog_eq_finitePrefixCost
    D ⟨base, hbase⟩ m]

/-! ## Exact masses of the two local charging events -/

theorem integral_endpoint_priority_event :
    (∫ x : ℝ in 0..1, x ^ 2 * (1 - x) ^ 2) = (1 : ℝ) / 30 := by
  rw [StableMatchingsE2E.integral_beta_kernel 3 (by norm_num)]
  norm_num

theorem integral_extra_priority_event :
    (∫ x : ℝ in 0..1, x ^ 3 * (1 - x)) = (1 : ℝ) / 20 := by
  let F : ℝ → ℝ := fun x ↦ x ^ 4 / 4 - x ^ 5 / 5
  have hderiv : ∀ x : ℝ, HasDerivAt F (x ^ 3 * (1 - x)) x := by
    intro x
    have h := ((hasDerivAt_pow 4 x).div_const (4 : ℝ)).sub
      ((hasDerivAt_pow 5 x).div_const (5 : ℝ))
    convert h using 1 <;> (try rfl) <;> (try dsimp [F]) <;> ring
  rw [intervalIntegral.integral_eq_sub_of_hasDerivAt_of_le (by norm_num)
    (by fun_prop) (fun x _ ↦ hderiv x)
    (((continuous_id.pow 3).mul (continuous_const.sub continuous_id)).intervalIntegrable 0 1)]
  norm_num [F]

/-! ## Pointwise content of the endpoint event -/

theorem endpoint_event_finite_width_le_two
    (shortLen otherLen : Nat) (hshort : shortLen ≤ 1)
    (shortStream otherStream : Nat → Bool)
    (hshortSuccess : hasSuccess shortStream)
    (hotherSuccess : hasSuccess otherStream)
    (hshortWait : firstSuccess shortStream = 2)
    (hotherWait : firstSuccess otherStream = 0) :
    markerWindowWidth (streamPrefix shortLen shortStream)
        (streamPrefix otherLen otherStream) ≤ 2 := by
  have hs := truncatedWait_le_length_succ
    (streamPrefix shortLen shortStream)
  have ho := truncatedWait_streamPrefix_le_firstSuccess_add_one
    otherLen otherStream hotherSuccess
  simp only [streamPrefix_length, hotherWait] at hs ho
  unfold markerWindowWidth
  omega

theorem endpoint_event_infinite_width_eq_three
    (shortStream otherStream : Nat → Bool)
    (hshortWait : firstSuccess shortStream = 2)
    (hotherWait : firstSuccess otherStream = 0) :
    geometricWindow (infiniteDummyWaitPair (shortStream, otherStream)) = 3 := by
  simp [geometricWindow, infiniteDummyWaitPair, hshortWait, hotherWait]

theorem endpoint_event_log_gap
    (shortLen otherLen : Nat) (hshort : shortLen ≤ 1)
    (shortStream otherStream : Nat → Bool)
    (hshortSuccess : hasSuccess shortStream)
    (hotherSuccess : hasSuccess otherStream)
    (hshortWait : firstSuccess shortStream = 2)
    (hotherWait : firstSuccess otherStream = 0) :
    Real.log (3 : ℝ) -
        Real.log (markerWindowWidth (streamPrefix shortLen shortStream)
          (streamPrefix otherLen otherStream) : ℝ) ≥
      Real.log ((3 : ℝ) / 2) := by
  have hwidth := endpoint_event_finite_width_le_two shortLen otherLen hshort
    shortStream otherStream hshortSuccess hotherSuccess hshortWait hotherWait
  have hspos := truncatedWait_pos (streamPrefix shortLen shortStream)
  have hopos := truncatedWait_pos (streamPrefix otherLen otherStream)
  have hpos : 0 < markerWindowWidth (streamPrefix shortLen shortStream)
      (streamPrefix otherLen otherStream) := by
    unfold markerWindowWidth
    omega
  have hlog : Real.log
      (markerWindowWidth (streamPrefix shortLen shortStream)
        (streamPrefix otherLen otherStream) : ℝ) ≤ Real.log (2 : ℝ) := by
    apply Real.log_le_log
    · exact_mod_cast hpos
    · exact_mod_cast hwidth
  rw [Real.log_div (by norm_num : (3 : ℝ) ≠ 0) (by norm_num : (2 : ℝ) ≠ 0)]
  linarith

end

end StableMatchingsJointCharging
