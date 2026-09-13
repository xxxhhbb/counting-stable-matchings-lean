import «CanonicalPathDecomposition»

/-!
# Global canonical joint-slack assembly
-/

namespace StableMatchingsJointCharging

open MeasureTheory ProbabilityTheory Set
open scoped unitInterval ENNReal BigOperators
open StableMatchings355 StableMatchingsEntropy StableMatchingsE2E

noncomputable section

noncomputable def targetSupportWindowGapOrZero {n : Nat}
    {P : ProfileCode n} (D : StaticWindowData P)
    (base : MatchingCode n) (priority : Fin n → I) (m : Fin n) : ℝ :=
  if h : Stable P base then
    targetSupportWindowGap D ⟨base, h⟩ priority m
  else 0

theorem integrable_targetSupportWindowGapOrZero {n : Nat}
    {P : ProfileCode n} (D : StaticWindowData P)
    (base : MatchingCode n) (m : Fin n) :
    Integrable (fun priority ↦
      targetSupportWindowGapOrZero D base priority m)
      (FullPriorityMeasure n) := by
  by_cases hbase : Stable P base
  · simpa [targetSupportWindowGapOrZero, hbase] using
      integrable_targetSupportWindowGap D ⟨base, hbase⟩ m
  · simp [targetSupportWindowGapOrZero, hbase]

noncomputable def averagedTargetSupportWindowSlack {n : Nat}
    {P : ProfileCode n} (D : StaticWindowData P) : ℝ :=
  ((stableSet P).card : ℝ)⁻¹ *
    ∑ base ∈ stableSet P, ∑ m : Fin n,
      ∫ priority, targetSupportWindowGapOrZero D base priority m
        ∂(FullPriorityMeasure n)

theorem prioritySupportWindowSlack_eq_average_target_gaps
    {n : Nat} {P : ProfileCode n}
    (D : StaticWindowData P) (hstable : (stableSet P).Nonempty)
    (priority : Fin n → I) :
    prioritySupportWindowSlack D priority =
      ((stableSet P).card : ℝ)⁻¹ *
        ∑ base ∈ stableSet P, ∑ m : Fin n,
          targetSupportWindowGapOrZero D base priority m := by
  classical
  rw [prioritySupportWindowSlack_eq_average_path_gap D priority hstable]
  congr 1
  apply Finset.sum_congr rfl
  intro base hbase
  have hs := (mem_stableSet_iff P base).1 hbase
  rw [supportWindowPathGap_eq_sum_targetSupportWindowGap D base hs priority]
  apply Finset.sum_congr rfl
  intro m hm
  simp [targetSupportWindowGapOrZero, hs]

theorem integrable_prioritySupportWindowSlack
    {n : Nat} {P : ProfileCode n}
    (D : StaticWindowData P) (hstable : (stableSet P).Nonempty) :
    Integrable (prioritySupportWindowSlack D) (FullPriorityMeasure n) := by
  classical
  rw [show prioritySupportWindowSlack D = fun priority ↦
      ((stableSet P).card : ℝ)⁻¹ *
        ∑ base ∈ stableSet P, ∑ m : Fin n,
          targetSupportWindowGapOrZero D base priority m by
    funext priority
    exact prioritySupportWindowSlack_eq_average_target_gaps
      D hstable priority]
  apply Integrable.const_mul
  exact integrable_finsetSum (stableSet P) fun base hbase ↦
    integrable_finsetSum Finset.univ fun m _ ↦
      integrable_targetSupportWindowGapOrZero D base m

theorem integral_prioritySupportWindowSlack_eq_averagedTarget
    {n : Nat} {P : ProfileCode n}
    (D : StaticWindowData P) (hstable : (stableSet P).Nonempty) :
    (∫ priority, prioritySupportWindowSlack D priority
        ∂(FullPriorityMeasure n)) =
      averagedTargetSupportWindowSlack D := by
  classical
  rw [show prioritySupportWindowSlack D = fun priority ↦
      ((stableSet P).card : ℝ)⁻¹ *
        ∑ base ∈ stableSet P, ∑ m : Fin n,
          targetSupportWindowGapOrZero D base priority m by
    funext priority
    exact prioritySupportWindowSlack_eq_average_target_gaps
      D hstable priority]
  rw [MeasureTheory.integral_const_mul]
  rw [MeasureTheory.integral_finsetSum (stableSet P)
    (fun base hbase ↦ integrable_finsetSum Finset.univ fun m _ ↦
      integrable_targetSupportWindowGapOrZero D base m)]
  congr 1
  apply Finset.sum_congr rfl
  intro base hbase
  rw [MeasureTheory.integral_finsetSum Finset.univ
    (fun m _ ↦ integrable_targetSupportWindowGapOrZero D base m)]

theorem integrable_priority_KL_add_supportWindow
    {n : Nat} {P : ProfileCode n}
    (D : StaticWindowData P) (hstable : (stableSet P).Nonempty) :
    Integrable (fun priority ↦
      priorityKLSlack P priority + prioritySupportWindowSlack D priority)
      (FullPriorityMeasure n) := by
  rw [show (fun priority ↦
      priorityKLSlack P priority + prioritySupportWindowSlack D priority) =
      fun priority ↦ aggregateLexCost D priority -
        Real.log (stableCount P) by
    funext priority
    rw [aggregateEntropyMarkerGap_eq_priority_KL_add_supportWindow
      D priority hstable]]
  exact (integrable_aggregateLexCost D).sub
    (integrable_const (Real.log (stableCount P)))

theorem averagedTargetSupportWindowSlack_le_entropyMarkerSlack
    {n : Nat} {P : ProfileCode n}
    (D : StaticWindowData P) (hstable : (stableSet P).Nonempty) :
    averagedTargetSupportWindowSlack D ≤ aggregateEntropyMarkerSlack D := by
  rw [aggregateEntropyMarkerSlack_eq_integral_priority_slacks D hstable,
    ← integral_prioritySupportWindowSlack_eq_averagedTarget D hstable]
  apply MeasureTheory.integral_mono
    (integrable_prioritySupportWindowSlack D hstable)
    (integrable_priority_KL_add_supportWindow D hstable)
  intro priority
  exact le_add_of_nonneg_left (priorityKLSlack_nonneg P priority hstable)

theorem averaged_joint_target_slack_le_totalJointSlack
    {n : Nat} {P : ProfileCode n}
    (D : StaticWindowData P) (hstable : (stableSet P).Nonempty) :
    averagedTargetGeometricSlack D + averagedTargetSupportWindowSlack D ≤
      totalJointSlack P := by
  rw [totalJointSlack_eq_two_stage D,
    aggregateGeometricSlack_eq_averagedTargetGeometricSlack D hstable]
  exact add_le_add_right
    (averagedTargetSupportWindowSlack_le_entropyMarkerSlack D hstable)
    (averagedTargetGeometricSlack D)

theorem log_three_halves_div_thirty_le_log_two_div_twenty :
    Real.log ((3 : ℝ) / 2) / 30 ≤ Real.log 2 / 20 := by
  have hlog : Real.log ((3 : ℝ) / 2) ≤ Real.log 2 := by
    exact Real.log_le_log (by norm_num) (by norm_num)
  have hnonneg : 0 ≤ Real.log ((3 : ℝ) / 2) :=
    (log_three_halves_pos).le
  nlinarith

theorem integral_targetSupportWindowGap_nonneg
    {n : Nat} {P : ProfileCode n}
    (D : StaticWindowData P) (base : StableBase P) (m : Fin n) :
    0 ≤ ∫ priority, targetSupportWindowGap D base priority m
      ∂(FullPriorityMeasure n) := by
  exact MeasureTheory.integral_nonneg fun priority ↦
    targetSupportWindowGap_nonneg D base priority m

theorem charged_target_joint_payment
    {n : Nat} {P : ProfileCode n} (hn : 5 ≤ n)
    (D : StaticWindowData P) (hstable : (stableSet P).Nonempty)
    (base : CodedStable P) (m : Fin n)
    (hcharged : m ∈ canonicalChargedMen P hstable base) :
    Real.log ((3 : ℝ) / 2) / 30 ≤
      targetGeometricSlack D base.1 m +
        ∫ priority, targetSupportWindowGap D base priority m
          ∂(FullPriorityMeasure n) := by
  rcases (mem_canonicalChargedMen_iff P hstable base m).1 hcharged with
    hshallow | hextra
  · have hC := canonicalShallow_targetGeometricSlack_ge_endpointPayment
      D hstable base.1 base.2 m hshallow
    have hB := integral_targetSupportWindowGap_nonneg D base m
    linarith
  · have hC := targetGeometricSlack_nonneg_of_stable
      D base.1 base.2 m
    have hB := canonicalExtra_targetSupportWindowGap_ge_extraPayment
      hn D hstable base m hextra
    have hconstant := log_three_halves_div_thirty_le_log_two_div_twenty
    linarith

noncomputable def targetJointPaymentOrZero {n : Nat}
    {P : ProfileCode n} (D : StaticWindowData P)
    (base : MatchingCode n) (m : Fin n) : ℝ :=
  targetGeometricSlack D base m +
    ∫ priority, targetSupportWindowGapOrZero D base priority m
      ∂(FullPriorityMeasure n)

theorem targetJointPaymentOrZero_nonneg_of_stable
    {n : Nat} {P : ProfileCode n} (D : StaticWindowData P)
    (base : MatchingCode n) (hbase : Stable P base) (m : Fin n) :
    0 ≤ targetJointPaymentOrZero D base m := by
  unfold targetJointPaymentOrZero
  have hC := targetGeometricSlack_nonneg_of_stable D base hbase m
  have hB : 0 ≤ ∫ priority,
      targetSupportWindowGapOrZero D base priority m
        ∂(FullPriorityMeasure n) := by
    simpa [targetSupportWindowGapOrZero, hbase] using
      integral_targetSupportWindowGap_nonneg D ⟨base, hbase⟩ m
  linarith

theorem charged_targetJointPaymentOrZero
    {n : Nat} {P : ProfileCode n} (hn : 5 ≤ n)
    (D : StaticWindowData P) (hstable : (stableSet P).Nonempty)
    (base : MatchingCode n) (hbase : Stable P base) (m : Fin n)
    (hcharged : m ∈ canonicalChargedMen P hstable ⟨base, hbase⟩) :
    Real.log ((3 : ℝ) / 2) / 30 ≤
      targetJointPaymentOrZero D base m := by
  have h := charged_target_joint_payment hn D hstable
    ⟨base, hbase⟩ m hcharged
  simpa [targetJointPaymentOrZero, targetSupportWindowGapOrZero, hbase] using h

theorem charged_card_times_localPayment_le_sum_jointPayment
    {n : Nat} {P : ProfileCode n} (hn : 5 ≤ n)
    (D : StaticWindowData P) (hstable : (stableSet P).Nonempty)
    (base : MatchingCode n) (hbase : Stable P base) :
    Real.log ((3 : ℝ) / 2) / 30 *
        ((canonicalChargedMen P hstable ⟨base, hbase⟩).card : ℝ) ≤
      ∑ m : Fin n, targetJointPaymentOrZero D base m := by
  classical
  let charged := canonicalChargedMen P hstable ⟨base, hbase⟩
  calc
    Real.log ((3 : ℝ) / 2) / 30 * (charged.card : ℝ) =
        ∑ _m ∈ charged, Real.log ((3 : ℝ) / 2) / 30 := by
      simp [mul_comm]
    _ ≤ ∑ m ∈ charged, targetJointPaymentOrZero D base m := by
      apply Finset.sum_le_sum
      intro m hm
      exact charged_targetJointPaymentOrZero hn D hstable base hbase m hm
    _ ≤ ∑ m ∈ (Finset.univ : Finset (Fin n)),
        targetJointPaymentOrZero D base m := by
      apply Finset.sum_le_sum_of_subset_of_nonneg (Finset.subset_univ charged)
      intro m hm hnot
      exact targetJointPaymentOrZero_nonneg_of_stable D base hbase m
    _ = _ := by simp

noncomputable def canonicalChargedCardOrZero {n : Nat}
    (P : ProfileCode n) (hstable : (stableSet P).Nonempty)
    (base : MatchingCode n) : Nat :=
  if h : Stable P base then
    (canonicalChargedMen P hstable ⟨base, h⟩).card
  else 0

theorem sum_canonicalChargedCardOrZero_eq_total {n : Nat}
    (P : ProfileCode n) (hstable : (stableSet P).Nonempty) :
    ∑ base ∈ stableSet P, canonicalChargedCardOrZero P hstable base =
      canonicalTotalCharge P hstable := by
  classical
  calc
    ∑ base ∈ stableSet P, canonicalChargedCardOrZero P hstable base =
        ∑ base : CodedStable P,
          canonicalChargedCardOrZero P hstable base.1 :=
      Finset.sum_subtype (stableSet P)
        (fun base ↦ mem_stableSet_iff P base)
        (canonicalChargedCardOrZero P hstable)
    _ = ∑ base : CodedStable P,
        (canonicalChargedMen P hstable base).card := by
      apply Finset.sum_congr rfl
      intro base hbase
      simp [canonicalChargedCardOrZero, base.2]
    _ = canonicalTotalCharge P hstable := rfl

theorem localPayment_times_totalCharge_le_sum_jointPayment
    {n : Nat} {P : ProfileCode n} (hn : 5 ≤ n)
    (D : StaticWindowData P) (hstable : (stableSet P).Nonempty) :
    Real.log ((3 : ℝ) / 2) / 30 *
        (canonicalTotalCharge P hstable : ℝ) ≤
      ∑ base ∈ stableSet P, ∑ m : Fin n,
        targetJointPaymentOrZero D base m := by
  classical
  have hsum :
      ∑ base ∈ stableSet P,
          Real.log ((3 : ℝ) / 2) / 30 *
            (canonicalChargedCardOrZero P hstable base : ℝ) ≤
        ∑ base ∈ stableSet P, ∑ m : Fin n,
          targetJointPaymentOrZero D base m := by
    apply Finset.sum_le_sum
    intro base hbase
    have hs := (mem_stableSet_iff P base).1 hbase
    simpa [canonicalChargedCardOrZero, hs] using
      charged_card_times_localPayment_le_sum_jointPayment
        hn D hstable base hs
  have hcards := congrArg (fun z : Nat ↦ (z : ℝ))
    (sum_canonicalChargedCardOrZero_eq_total P hstable)
  push_cast at hcards
  calc
    Real.log ((3 : ℝ) / 2) / 30 *
        (canonicalTotalCharge P hstable : ℝ) =
      Real.log ((3 : ℝ) / 2) / 30 *
        (∑ base ∈ stableSet P,
          (canonicalChargedCardOrZero P hstable base : ℝ)) := by rw [hcards]
    _ = ∑ base ∈ stableSet P,
        Real.log ((3 : ℝ) / 2) / 30 *
          (canonicalChargedCardOrZero P hstable base : ℝ) := by
      rw [Finset.mul_sum]
    _ ≤ _ := hsum

theorem averaged_joint_target_slack_eq_normalized_jointPayment
    {n : Nat} {P : ProfileCode n}
    (D : StaticWindowData P) :
    averagedTargetGeometricSlack D + averagedTargetSupportWindowSlack D =
      ((stableSet P).card : ℝ)⁻¹ *
        ∑ base ∈ stableSet P, ∑ m : Fin n,
          targetJointPaymentOrZero D base m := by
  classical
  unfold averagedTargetGeometricSlack averagedTargetSupportWindowSlack
  simp only [targetJointPaymentOrZero, Finset.sum_add_distrib]
  ring

theorem card_stableSet_eq_natCard_codedStable {n : Nat}
    (P : ProfileCode n) :
    (stableSet P).card = Nat.card (CodedStable P) := by
  rw [Nat.card_eq_fintype_card, ← stableCount_eq_fintype_card_codedStable]
  rfl

theorem normalized_canonical_charge_payment_le_averaged_joint_slack
    {n : Nat} {P : ProfileCode n} (hn : 5 ≤ n)
    (D : StaticWindowData P) (hstable : (stableSet P).Nonempty) :
    Real.log ((3 : ℝ) / 2) / 30 *
        ((Nat.card (CodedStable P) : ℝ)⁻¹ *
          (canonicalTotalCharge P hstable : ℝ)) ≤
      averagedTargetGeometricSlack D + averagedTargetSupportWindowSlack D := by
  rw [averaged_joint_target_slack_eq_normalized_jointPayment D,
    ← card_stableSet_eq_natCard_codedStable P]
  have hcardNonneg : 0 ≤ ((stableSet P).card : ℝ)⁻¹ := by positivity
  have hsum := localPayment_times_totalCharge_le_sum_jointPayment
    hn D hstable
  nlinarith

theorem optimizedJointDelta_le_averaged_joint_slack
    {n : Nat} {P : ProfileCode n} (hn : 8001 ≤ n)
    (D : StaticWindowData P) (hstable : (stableSet P).Nonempty) :
    (n : ℝ) * optimizedJointDelta ≤
      averagedTargetGeometricSlack D + averagedTargetSupportWindowSlack D := by
  have hcharge := canonical_normalized_average_charge_gt_three_n_over_160
    P hstable hn
  have hlocal := normalized_canonical_charge_payment_le_averaged_joint_slack
    (by omega) D hstable
  exact joint_charge_ge_optimized_delta n
    ((Nat.card (CodedStable P) : ℝ)⁻¹ *
      (canonicalTotalCharge P hstable : ℝ))
    (averagedTargetGeometricSlack D + averagedTargetSupportWindowSlack D)
    hcharge.le hlocal

theorem optimizedJointDelta_le_totalJointSlack
    {n : Nat} {P : ProfileCode n} (hn : 8001 ≤ n)
    (D : StaticWindowData P) (hstable : (stableSet P).Nonempty) :
    (n : ℝ) * optimizedJointDelta ≤ totalJointSlack P :=
  (optimizedJointDelta_le_averaged_joint_slack hn D hstable).trans
    (averaged_joint_target_slack_le_totalJointSlack D hstable)

theorem optimizedJointDelta_le_geometricLogSeries :
    optimizedJointDelta ≤ geometricLogSeries := by
  have hterm : geometricLogWeight 2 ≤ geometricLogSeries := by
    unfold geometricLogSeries
    exact summable_geometricLogWeight.le_tsum 2 fun j hj ↦
      geometricLogWeight_nonneg j
  have hlog : Real.log ((3 : ℝ) / 2) ≤ Real.log 2 :=
    Real.log_le_log (by norm_num) (by norm_num)
  have hlog0 : 0 ≤ Real.log ((3 : ℝ) / 2) :=
    (log_three_halves_pos).le
  have hlocal : optimizedJointDelta ≤ geometricLogWeight 2 := by
    unfold optimizedJointDelta geometricLogWeight
    norm_num
    nlinarith
  exact hlocal.trans hterm

theorem all_profiles_optimizedJointSlack
    {n : Nat} (hn : 8001 ≤ n) (P : ProfileCode n) :
    (n : ℝ) * optimizedJointDelta ≤ totalJointSlack P := by
  classical
  by_cases hz : stableCount P = 0
  · unfold totalJointSlack
    rw [hz]
    simp only [Nat.cast_zero, Real.log_zero, sub_zero]
    exact mul_le_mul_of_nonneg_left optimizedJointDelta_le_geometricLogSeries
      (Nat.cast_nonneg n)
  · have hpositive : 0 < stableCount P := Nat.pos_of_ne_zero hz
    have hstable : (stableSet P).Nonempty := by
      apply Finset.card_pos.mp
      simpa [stableCount] using hpositive
    let D : StaticWindowData P := Classical.choice (exists_staticWindowData P)
    exact optimizedJointDelta_le_totalJointSlack hn D hstable

theorem stableCount_lt_66623_div_20000_pow
    {n : Nat} (hn : 8001 ≤ n) (P : ProfileCode n) :
    (stableCount P : ℝ) < ((66623 : ℝ) / 20000) ^ n :=
  stableCount_lt_66623_div_20000_pow_of_optimizedJointSlack
    (by omega) P (all_profiles_optimizedJointSlack hn P)

theorem SM_lt_66623_div_20000_pow
    (n : Nat) (hn : 8001 ≤ n) :
    (SM n : ℝ) < ((66623 : ℝ) / 20000) ^ n := by
  exact SM_lt_66623_div_20000_pow_of_all_optimizedJointSlack n
    (by omega) (fun P ↦ all_profiles_optimizedJointSlack hn P)

end

end StableMatchingsJointCharging
