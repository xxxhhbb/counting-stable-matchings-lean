import StableMatchingsE2E.ConstantOptimization
import StableMatchingsE2E.OptimizedFinalTheorem
import «JointSlackLedger»

namespace StableMatchingsJointCharging

open StableMatchingsE2E

noncomputable section

/-- The explicit slack supplied by the sharpened boundary-deletion theorem
with threshold density `alpha = 1/27`. -/
def jointDelta : ℝ := Real.log ((3 : ℝ) / 2) / 1620

/-- Stronger asymptotic slack obtained from the near-optimal rational
deletion threshold `alpha = 3/80`. -/
def optimizedJointDelta : ℝ := Real.log ((3 : ℝ) / 2) / 1600

theorem log_three_halves_pos : 0 < Real.log ((3 : ℝ) / 2) := by
  exact Real.log_pos (by norm_num)

theorem jointDelta_pos : 0 < jointDelta := by
  unfold jointDelta
  positivity

theorem optimizedJointDelta_pos : 0 < optimizedJointDelta := by
  unfold optimizedJointDelta
  positivity

/-- A rational lower certificate for the logarithm used in `jointDelta`. -/
theorem log_three_halves_gt_4054_div_10000 :
    (4054 : ℝ) / 10000 < Real.log ((3 : ℝ) / 2) := by
  have h := Real.sum_range_le_log_div
    (x := (1 : ℝ) / 5) (by norm_num) (by norm_num) 4
  norm_num [Finset.sum_range_succ] at h
  nlinarith

/-- The already verified Abel decomposition also gives this explicit rational
upper certificate, before conversion to the old rounded exponential base. -/
theorem geometricLogSeries_lt_120356492_div_100000000 :
    geometricLogSeries < (120356492 : ℝ) / 100000000 := by
  rw [geometricLogSeries_eq_abel]
  have hsplit := summable_abelShiftTerm.sum_add_tsum_nat_add 160
  calc
    (2 / 3 : ℝ) * Real.log 2 + ∑' j : ℕ, abelShiftTerm j =
        (2 / 3 : ℝ) * Real.log 2 +
          (∑ j ∈ Finset.range 160, abelShiftTerm j) +
            ∑' j : ℕ, abelShiftTerm (j + 160) := by linarith
    _ ≤ (2 / 3 : ℝ) * Real.log 2 +
          (∑ j ∈ Finset.range 160, abelShiftTerm j) +
            sharpTailPotential120 40 := by
        gcongr
        exact abel_tail_le_sharp160
    _ < (120356492 : ℝ) / 100000000 :=
      abel_head160_plus_sharp_tail_lt_120356492_div_100000000

/-- Direct lower certificate for the clean improved base `16659/5000`. -/
theorem one_point_12034974_lt_log_16659_div_5000 :
    (12034974 : ℝ) / 10000000 <
      Real.log ((16659 : ℝ) / 5000) := by
  have h := Real.sum_range_le_log_div
    (x := (11659 : ℝ) / 21659) (by norm_num) (by norm_num) 16
  norm_num [Finset.sum_range_succ] at h
  nlinarith

/-- The candidate linear slack crosses a simple exact base strictly below the
previous `1665987/500000 = 3.331974` endpoint. -/
theorem geometricLogSeries_sub_jointDelta_lt_log_16659_div_5000 :
    geometricLogSeries - jointDelta <
      Real.log ((16659 : ℝ) / 5000) := by
  have hS := geometricLogSeries_lt_120356492_div_100000000
  have hd := log_three_halves_gt_4054_div_10000
  have hq := one_point_12034974_lt_log_16659_div_5000
  unfold jointDelta
  linarith

theorem improved_base_lt_old_base :
    ((16659 : ℝ) / 5000) < (1665987 : ℝ) / 500000 := by
  norm_num

theorem one_point_120332_lt_log_2082_div_625 :
    (120332 : ℝ) / 100000 < Real.log ((2082 : ℝ) / 625) := by
  have h := Real.sum_range_le_log_div
    (x := (1457 : ℝ) / 2707) (by norm_num) (by norm_num) 16
  norm_num [Finset.sum_range_succ] at h
  nlinarith

theorem geometricLogSeries_sub_jointDelta_lt_log_2082_div_625 :
    geometricLogSeries - jointDelta <
      Real.log ((2082 : ℝ) / 625) := by
  have hS := geometricLogSeries_lt_120356492_div_100000000
  have hd := log_three_halves_gt_4054_div_10000
  have hq := one_point_120332_lt_log_2082_div_625
  unfold jointDelta
  linarith

theorem sharper_base_lt_old_base :
    ((2082 : ℝ) / 625) < (1665987 : ℝ) / 500000 := by
  norm_num

theorem one_point_1203312_lt_log_66623_div_20000 :
    (1203312 : ℝ) / 1000000 < Real.log ((66623 : ℝ) / 20000) := by
  have h := Real.sum_range_le_log_div
    (x := (46623 : ℝ) / 86623) (by norm_num) (by norm_num) 16
  norm_num [Finset.sum_range_succ] at h
  nlinarith

theorem geometricLogSeries_sub_optimizedJointDelta_lt_log_66623_div_20000 :
    geometricLogSeries - optimizedJointDelta <
      Real.log ((66623 : ℝ) / 20000) := by
  have hS := geometricLogSeries_lt_120356492_div_100000000
  have hd := log_three_halves_gt_4054_div_10000
  have hq := one_point_1203312_lt_log_66623_div_20000
  unfold optimizedJointDelta
  linarith

theorem optimized_base_lt_old_base :
    ((66623 : ℝ) / 20000) < (1665987 : ℝ) / 500000 := by
  norm_num

/-- Kernel-level consequence of the still-to-be-closed structural charging
interface.  This theorem contains no rotation-system axiom: its hypothesis is
exactly the profile-level joint-slack inequality that the combinatorial bridge
must eventually discharge. -/
theorem log_stableCount_lt_n_log_16659_div_5000_of_jointSlack
    {n : ℕ} (hn : 1 ≤ n) (P : ProfileCode n)
    (hjoint : (n : ℝ) * jointDelta ≤ totalJointSlack P) :
    Real.log (stableCount P) <
      (n : ℝ) * Real.log ((16659 : ℝ) / 5000) := by
  have hmain :=
    (jointSlack_linear_lower_iff_log_bound P jointDelta).1 hjoint
  exact hmain.trans_lt
    (mul_lt_mul_of_pos_left
      geometricLogSeries_sub_jointDelta_lt_log_16659_div_5000
      (by exact_mod_cast hn))

theorem stableCount_lt_16659_div_5000_pow_of_jointSlack
    {n : ℕ} (hn : 1 ≤ n) (P : ProfileCode n)
    (hjoint : (n : ℝ) * jointDelta ≤ totalJointSlack P) :
    (stableCount P : ℝ) < ((16659 : ℝ) / 5000) ^ n := by
  by_cases hz : stableCount P = 0
  · rw [hz]
    norm_num only [Nat.cast_zero]
    have hq : (0 : ℝ) < (16659 : ℝ) / 5000 := by norm_num
    exact pow_pos hq n
  · have hlog :=
      log_stableCount_lt_n_log_16659_div_5000_of_jointSlack hn P hjoint
    have hexp := (Real.exp_lt_exp).2 hlog
    rw [Real.exp_log (by exact_mod_cast Nat.pos_of_ne_zero hz)] at hexp
    rw [Real.exp_nat_mul, Real.exp_log (by norm_num)] at hexp
    exact hexp

theorem log_stableCount_lt_n_log_2082_div_625_of_jointSlack
    {n : ℕ} (hn : 1 ≤ n) (P : ProfileCode n)
    (hjoint : (n : ℝ) * jointDelta ≤ totalJointSlack P) :
    Real.log (stableCount P) <
      (n : ℝ) * Real.log ((2082 : ℝ) / 625) := by
  have hmain :=
    (jointSlack_linear_lower_iff_log_bound P jointDelta).1 hjoint
  exact hmain.trans_lt
    (mul_lt_mul_of_pos_left
      geometricLogSeries_sub_jointDelta_lt_log_2082_div_625
      (by exact_mod_cast hn))

theorem stableCount_lt_2082_div_625_pow_of_jointSlack
    {n : ℕ} (hn : 1 ≤ n) (P : ProfileCode n)
    (hjoint : (n : ℝ) * jointDelta ≤ totalJointSlack P) :
    (stableCount P : ℝ) < ((2082 : ℝ) / 625) ^ n := by
  by_cases hz : stableCount P = 0
  · rw [hz]
    norm_num only [Nat.cast_zero]
    have hq : (0 : ℝ) < (2082 : ℝ) / 625 := by norm_num
    exact pow_pos hq n
  · have hlog :=
      log_stableCount_lt_n_log_2082_div_625_of_jointSlack hn P hjoint
    have hexp := (Real.exp_lt_exp).2 hlog
    rw [Real.exp_log (by exact_mod_cast Nat.pos_of_ne_zero hz)] at hexp
    rw [Real.exp_nat_mul, Real.exp_log (by norm_num)] at hexp
    exact hexp

/-- Final extremal wrapper.  The only remaining hypothesis is the universal
profile-level structural charging theorem. -/
theorem SM_lt_2082_div_625_pow_of_all_jointSlack
    (n : ℕ) (hn : 1 ≤ n)
    (hjoint : ∀ P : ProfileCode n,
      (n : ℝ) * jointDelta ≤ totalJointSlack P) :
    (SM n : ℝ) < ((2082 : ℝ) / 625) ^ n := by
  obtain ⟨P, hP⟩ := exists_profile_attaining_SM n
  simpa [hP] using
    stableCount_lt_2082_div_625_pow_of_jointSlack hn P (hjoint P)

theorem stableCount_lt_66623_div_20000_pow_of_optimizedJointSlack
    {n : ℕ} (hn : 1 ≤ n) (P : ProfileCode n)
    (hjoint : (n : ℝ) * optimizedJointDelta ≤ totalJointSlack P) :
    (stableCount P : ℝ) < ((66623 : ℝ) / 20000) ^ n := by
  have hmain :=
    (jointSlack_linear_lower_iff_log_bound P optimizedJointDelta).1 hjoint
  have hlog : Real.log (stableCount P) <
      (n : ℝ) * Real.log ((66623 : ℝ) / 20000) :=
    hmain.trans_lt
      (mul_lt_mul_of_pos_left
        geometricLogSeries_sub_optimizedJointDelta_lt_log_66623_div_20000
        (by exact_mod_cast hn))
  by_cases hz : stableCount P = 0
  · rw [hz]
    norm_num only [Nat.cast_zero]
    exact pow_pos (by norm_num) n
  · have hexp := (Real.exp_lt_exp).2 hlog
    rw [Real.exp_log (by exact_mod_cast Nat.pos_of_ne_zero hz)] at hexp
    rw [Real.exp_nat_mul, Real.exp_log (by norm_num)] at hexp
    exact hexp

theorem SM_lt_66623_div_20000_pow_of_all_optimizedJointSlack
    (n : ℕ) (hn : 1 ≤ n)
    (hjoint : ∀ P : ProfileCode n,
      (n : ℝ) * optimizedJointDelta ≤ totalJointSlack P) :
    (SM n : ℝ) < ((66623 : ℝ) / 20000) ^ n := by
  obtain ⟨P, hP⟩ := exists_profile_attaining_SM n
  simpa [hP] using
    stableCount_lt_66623_div_20000_pow_of_optimizedJointSlack
      hn P (hjoint P)

end

end StableMatchingsJointCharging
