import «CanonicalUniformPaymentImprovement»

/-!
# Global consequence of the uniform `log 2 / 12` local payment

The shallow and extra branches now have the same certified local payment.
Combining it with the already verified near-critical charge density gives a
clean explicit upper bound `SM(n) < (2078/625)^n = 3.3248^n`.
-/

namespace StableMatchingsJointCharging

open MeasureTheory ProbabilityTheory Set
open scoped unitInterval ENNReal BigOperators
open StableMatchings355 StableMatchingsEntropy StableMatchingsE2E

noncomputable section

theorem charged_target_joint_payment_uniform
    {n : Nat} {P : ProfileCode n} (hn : 5 ≤ n)
    (D : StaticWindowData P) (hstable : (stableSet P).Nonempty)
    (base : CodedStable P) (m : Fin n)
    (hcharged : m ∈ canonicalChargedMen P hstable base) :
    Real.log 2 / 12 ≤
      targetGeometricSlack D base.1 m +
        ∫ priority, targetSupportWindowGap D base priority m
          ∂(FullPriorityMeasure n) := by
  rcases (mem_canonicalChargedMen_iff P hstable base m).1 hcharged with
    hshallow | hextra
  · have hC := canonicalShallow_targetGeometricSlack_ge_logTwoDivTwelve
      D hstable base.1 base.2 m hshallow
    have hB := integral_targetSupportWindowGap_nonneg D base m
    linarith
  · have hC := targetGeometricSlack_nonneg_of_stable D base.1 base.2 m
    have hB := canonicalExtra_targetSupportWindowGap_ge_reducedExtraPayment
      hn D hstable base m hextra
    linarith

theorem charged_targetJointPaymentOrZero_uniform
    {n : Nat} {P : ProfileCode n} (hn : 5 ≤ n)
    (D : StaticWindowData P) (hstable : (stableSet P).Nonempty)
    (base : MatchingCode n) (hbase : Stable P base) (m : Fin n)
    (hcharged : m ∈ canonicalChargedMen P hstable ⟨base, hbase⟩) :
    Real.log 2 / 12 ≤ targetJointPaymentOrZero D base m := by
  have h := charged_target_joint_payment_uniform hn D hstable
    ⟨base, hbase⟩ m hcharged
  simpa [targetJointPaymentOrZero, targetSupportWindowGapOrZero, hbase] using h

theorem charged_card_times_uniformPayment_le_sum_jointPayment
    {n : Nat} {P : ProfileCode n} (hn : 5 ≤ n)
    (D : StaticWindowData P) (hstable : (stableSet P).Nonempty)
    (base : MatchingCode n) (hbase : Stable P base) :
    Real.log 2 / 12 *
        ((canonicalChargedMen P hstable ⟨base, hbase⟩).card : ℝ) ≤
      ∑ m : Fin n, targetJointPaymentOrZero D base m := by
  classical
  let charged := canonicalChargedMen P hstable ⟨base, hbase⟩
  calc
    Real.log 2 / 12 * (charged.card : ℝ) =
        ∑ _m ∈ charged, Real.log 2 / 12 := by simp [mul_comm]
    _ ≤ ∑ m ∈ charged, targetJointPaymentOrZero D base m := by
      apply Finset.sum_le_sum
      intro m hm
      exact charged_targetJointPaymentOrZero_uniform
        hn D hstable base hbase m hm
    _ ≤ ∑ m ∈ (Finset.univ : Finset (Fin n)),
        targetJointPaymentOrZero D base m := by
      apply Finset.sum_le_sum_of_subset_of_nonneg (Finset.subset_univ charged)
      intro m hm hnot
      exact targetJointPaymentOrZero_nonneg_of_stable D base hbase m
    _ = _ := by simp

theorem uniformPayment_times_totalCharge_le_sum_jointPayment
    {n : Nat} {P : ProfileCode n} (hn : 5 ≤ n)
    (D : StaticWindowData P) (hstable : (stableSet P).Nonempty) :
    Real.log 2 / 12 * (canonicalTotalCharge P hstable : ℝ) ≤
      ∑ base ∈ stableSet P, ∑ m : Fin n,
        targetJointPaymentOrZero D base m := by
  classical
  have hsum :
      ∑ base ∈ stableSet P,
          Real.log 2 / 12 *
            (canonicalChargedCardOrZero P hstable base : ℝ) ≤
        ∑ base ∈ stableSet P, ∑ m : Fin n,
          targetJointPaymentOrZero D base m := by
    apply Finset.sum_le_sum
    intro base hbase
    have hs := (mem_stableSet_iff P base).1 hbase
    simpa [canonicalChargedCardOrZero, hs] using
      charged_card_times_uniformPayment_le_sum_jointPayment
        hn D hstable base hs
  have hcards := congrArg (fun z : Nat ↦ (z : ℝ))
    (sum_canonicalChargedCardOrZero_eq_total P hstable)
  push_cast at hcards
  calc
    Real.log 2 / 12 * (canonicalTotalCharge P hstable : ℝ) =
      Real.log 2 / 12 *
        (∑ base ∈ stableSet P,
          (canonicalChargedCardOrZero P hstable base : ℝ)) := by rw [hcards]
    _ = ∑ base ∈ stableSet P,
        Real.log 2 / 12 *
          (canonicalChargedCardOrZero P hstable base : ℝ) := by
      rw [Finset.mul_sum]
    _ ≤ _ := hsum

theorem normalized_canonical_charge_uniformPayment_le_averaged_joint_slack
    {n : Nat} {P : ProfileCode n} (hn : 5 ≤ n)
    (D : StaticWindowData P) (hstable : (stableSet P).Nonempty) :
    Real.log 2 / 12 *
        ((Nat.card (CodedStable P) : ℝ)⁻¹ *
          (canonicalTotalCharge P hstable : ℝ)) ≤
      averagedTargetGeometricSlack D + averagedTargetSupportWindowSlack D := by
  rw [averaged_joint_target_slack_eq_normalized_jointPayment D,
    ← card_stableSet_eq_natCard_codedStable P]
  have hcardNonneg : 0 ≤ ((stableSet P).card : ℝ)⁻¹ := by positivity
  have hsum := uniformPayment_times_totalCharge_le_sum_jointPayment
    hn D hstable
  nlinarith

def nearCriticalUniformJointDelta : ℝ :=
  616029 * Real.log 2 / 196608000

theorem nearCriticalUniformJointDelta_pos :
    0 < nearCriticalUniformJointDelta := by
  unfold nearCriticalUniformJointDelta
  have hlog : 0 < Real.log 2 := Real.log_pos (by norm_num)
  positivity

theorem nearCriticalUniformJointDelta_le_averaged_joint_slack
    {n : Nat} {P : ProfileCode n} (hn : 850001 ≤ n)
    (D : StaticWindowData P) (hstable : (stableSet P).Nonempty) :
    (n : ℝ) * nearCriticalUniformJointDelta ≤
      averagedTargetGeometricSlack D + averagedTargetSupportWindowSlack D := by
  have hcharge :=
    canonical_normalized_average_charge_gt_616029_n_over_16384000
      P hstable hn
  have hlocal :=
    normalized_canonical_charge_uniformPayment_le_averaged_joint_slack
      (by omega) D hstable
  have hlog : 0 ≤ Real.log 2 := Real.log_nonneg (by norm_num)
  unfold nearCriticalUniformJointDelta
  calc
    (n : ℝ) * (616029 * Real.log 2 / 196608000) =
        Real.log 2 / 12 *
          ((616029 : ℝ) * (n : ℝ) / 16384000) := by ring
    _ ≤ Real.log 2 / 12 *
        ((Nat.card (CodedStable P) : ℝ)⁻¹ *
          (canonicalTotalCharge P hstable : ℝ)) := by gcongr
    _ ≤ _ := hlocal

theorem nearCriticalUniformJointDelta_le_totalJointSlack
    {n : Nat} {P : ProfileCode n} (hn : 850001 ≤ n)
    (D : StaticWindowData P) (hstable : (stableSet P).Nonempty) :
    (n : ℝ) * nearCriticalUniformJointDelta ≤ totalJointSlack P :=
  (nearCriticalUniformJointDelta_le_averaged_joint_slack hn D hstable).trans
    (averaged_joint_target_slack_le_totalJointSlack D hstable)

theorem nearCriticalUniformJointDelta_le_geometricLogSeries :
    nearCriticalUniformJointDelta ≤ geometricLogSeries := by
  have hterm : geometricLogWeight 2 ≤ geometricLogSeries := by
    unfold geometricLogSeries
    exact summable_geometricLogWeight.le_tsum 2 fun j hj ↦
      geometricLogWeight_nonneg j
  have hlocal : nearCriticalUniformJointDelta ≤ geometricLogWeight 2 := by
    unfold nearCriticalUniformJointDelta geometricLogWeight
    have hlog : 0 ≤ Real.log 2 := Real.log_nonneg (by norm_num)
    norm_num
    nlinarith
  exact hlocal.trans hterm

theorem all_profiles_nearCriticalUniformJointSlack
    {n : Nat} (hn : 850001 ≤ n) (P : ProfileCode n) :
    (n : ℝ) * nearCriticalUniformJointDelta ≤ totalJointSlack P := by
  classical
  by_cases hz : stableCount P = 0
  · unfold totalJointSlack
    rw [hz]
    simp only [Nat.cast_zero, Real.log_zero, sub_zero]
    exact mul_le_mul_of_nonneg_left
      nearCriticalUniformJointDelta_le_geometricLogSeries (Nat.cast_nonneg n)
  · have hpositive : 0 < stableCount P := Nat.pos_of_ne_zero hz
    have hstable : (stableSet P).Nonempty := by
      apply Finset.card_pos.mp
      simpa [stableCount] using hpositive
    let D : StaticWindowData P := Classical.choice (exists_staticWindowData P)
    exact nearCriticalUniformJointDelta_le_totalJointSlack hn D hstable

theorem geometricLogSeries_sub_nearCriticalUniformJointDelta_lt_600697_div_500000 :
    geometricLogSeries - nearCriticalUniformJointDelta <
      (600697 : ℝ) / 500000 := by
  have hS := geometricLogSeries_lt_120356492_div_100000000
  have hd := log_two_gt_693_div_1000
  unfold nearCriticalUniformJointDelta
  linarith

theorem one_point_600697_div_500000_lt_log_2078_div_625 :
    (600697 : ℝ) / 500000 < Real.log ((2078 : ℝ) / 625) := by
  have h := Real.sum_range_le_log_div
    (x := (1453 : ℝ) / 2703) (by norm_num) (by norm_num) 16
  norm_num [Finset.sum_range_succ] at h
  nlinarith

theorem geometricLogSeries_sub_nearCriticalUniformJointDelta_lt_log_2078_div_625 :
    geometricLogSeries - nearCriticalUniformJointDelta <
      Real.log ((2078 : ℝ) / 625) :=
  geometricLogSeries_sub_nearCriticalUniformJointDelta_lt_600697_div_500000.trans
    one_point_600697_div_500000_lt_log_2078_div_625

theorem stableCount_lt_2078_div_625_pow
    {n : Nat} (hn : 850001 ≤ n) (P : ProfileCode n) :
    (stableCount P : ℝ) < ((2078 : ℝ) / 625) ^ n := by
  have hjoint := all_profiles_nearCriticalUniformJointSlack hn P
  have hmain :=
    (jointSlack_linear_lower_iff_log_bound P nearCriticalUniformJointDelta).1
      hjoint
  have hlog : Real.log (stableCount P) <
      (n : ℝ) * Real.log ((2078 : ℝ) / 625) :=
    hmain.trans_lt
      (mul_lt_mul_of_pos_left
        geometricLogSeries_sub_nearCriticalUniformJointDelta_lt_log_2078_div_625
        (by positivity))
  by_cases hz : stableCount P = 0
  · rw [hz]
    norm_num only [Nat.cast_zero]
    exact pow_pos (by norm_num) n
  · have hexp := (Real.exp_lt_exp).2 hlog
    rw [Real.exp_log (by exact_mod_cast Nat.pos_of_ne_zero hz)] at hexp
    rw [Real.exp_nat_mul, Real.exp_log (by norm_num)] at hexp
    exact hexp

theorem SM_lt_2078_div_625_pow
    (n : Nat) (hn : 850001 ≤ n) :
    (SM n : ℝ) < ((2078 : ℝ) / 625) ^ n := by
  obtain ⟨P, hP⟩ := exists_profile_attaining_SM n
  simpa [hP] using stableCount_lt_2078_div_625_pow hn P

end

end StableMatchingsJointCharging
