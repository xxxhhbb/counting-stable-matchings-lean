import Mathlib.Analysis.SpecialFunctions.BinaryEntropy
import StableMatchingsE2E.ConstantOptimization

namespace StableMatchingsJointCharging

open StableMatchingsE2E

noncomputable section

theorem log_hundred_lt_4606_div_1000 :
    Real.log (100 : ℝ) < (4606 : ℝ) / 1000 := by
  rw [Real.log_lt_iff_lt_exp (by norm_num)]
  have hsum := Real.sum_le_exp_of_nonneg
    (x := (4606 : ℝ) / 1000) (by norm_num) 16
  have hpoly : (100 : ℝ) <
      ∑ i ∈ Finset.range 16,
        ((4606 : ℝ) / 1000) ^ i / (i.factorial : ℝ) := by
    norm_num [Finset.sum_range_succ, Nat.factorial]
  exact hpoly.trans_le hsum

theorem log_hundred_div_ninetynine_le_inv_ninetynine :
    Real.log ((100 : ℝ) / 99) ≤ (1 : ℝ) / 99 := by
  have h := Real.log_le_sub_one_of_pos
    (x := (100 : ℝ) / 99) (by norm_num)
  norm_num at h ⊢
  exact h

theorem log_two_gt_693_div_1000 :
    (693 : ℝ) / 1000 < Real.log 2 := by
  have h := Real.sum_range_le_log_div
    (x := (1 : ℝ) / 3) (by norm_num) (by norm_num) 4
  norm_num [Finset.sum_range_succ] at h
  nlinarith

/-- Exact rational certificate behind the paper's `H₂(0.01) < 0.081`.
The statement avoids division by `log 2`: `Real.binEntropy` uses natural
logarithms, so the right side is exactly `0.081 * log 2`. -/
theorem binEntropy_one_hundredth_lt_81_milli_log_two :
    Real.binEntropy ((1 : ℝ) / 100) <
      ((81 : ℝ) / 1000) * Real.log 2 := by
  have h100 := log_hundred_lt_4606_div_1000
  have hratio := log_hundred_div_ninetynine_le_inv_ninetynine
  have htwo := log_two_gt_693_div_1000
  rw [Real.binEntropy]
  have hinv1 : ((1 : ℝ) / 100)⁻¹ = (100 : ℝ) := by norm_num
  have hinv99 : (1 - (1 : ℝ) / 100)⁻¹ = (100 : ℝ) / 99 := by norm_num
  rw [hinv1, hinv99]
  nlinarith

/-- The exact positive exponent margin used by the deletion double count. -/
theorem deletion_entropy_margin_gt_164_milli_log_two :
    ((1 : ℝ) / 4 - ((1 : ℝ) / 100) / 2) * Real.log 2 -
        Real.binEntropy ((1 : ℝ) / 100) >
      ((164 : ℝ) / 1000) * Real.log 2 := by
  have h := binEntropy_one_hundredth_lt_81_milli_log_two
  nlinarith

theorem exp_neg_164_milli_n_log_two_lt_half {n : ℕ} (hn : 100 ≤ n) :
    Real.exp (-((164 : ℝ) / 1000) * (n : ℝ) * Real.log 2) <
      (1 : ℝ) / 2 := by
  have hlog : 0 < Real.log 2 := Real.log_pos (by norm_num)
  have hn' : (100 : ℝ) ≤ (n : ℝ) := by exact_mod_cast hn
  have harg :
      -((164 : ℝ) / 1000) * (n : ℝ) * Real.log 2 < -Real.log 2 := by
    nlinarith
  calc
    Real.exp (-((164 : ℝ) / 1000) * (n : ℝ) * Real.log 2) <
        Real.exp (-Real.log 2) := (Real.exp_lt_exp).2 harg
    _ = (1 : ℝ) / 2 := by rw [Real.exp_neg, Real.exp_log (by norm_num)]; norm_num

/-! ## Sharper threshold `alpha = 1/27` -/

theorem log_twentyseven_lt_3296_div_1000 :
    Real.log (27 : ℝ) < (3296 : ℝ) / 1000 := by
  have h2 := log_one_add_inv_le_atanhUpper14 1 (by norm_num)
  have h32 := log_one_add_inv_le_atanhUpper14 2 (by norm_num)
  have hlog3 : Real.log (3 : ℝ) =
      Real.log (2 : ℝ) + Real.log ((3 : ℝ) / 2) := by
    rw [← Real.log_mul (by norm_num : (2 : ℝ) ≠ 0) (by norm_num : (3 / 2 : ℝ) ≠ 0)]
    norm_num
  have hlog27 : Real.log (27 : ℝ) = 3 * Real.log (3 : ℝ) := by
    rw [show (27 : ℝ) = 3 ^ 3 by norm_num, Real.log_pow]
    norm_num
  norm_num [atanhUpper14, Finset.sum_range_succ] at h2 h32
  rw [hlog27, hlog3]
  nlinarith

theorem log_twentyseven_div_twentysix_upper :
    Real.log ((27 : ℝ) / 26) ≤ atanhUpper14 ((1 : ℝ) / 53) := by
  convert log_one_add_inv_le_atanhUpper14 26 (by norm_num) using 1 <;> norm_num

theorem binEntropy_one_twentyseventh_lt_229_milli_log_two :
    Real.binEntropy ((1 : ℝ) / 27) <
      ((229 : ℝ) / 1000) * Real.log 2 := by
  have h27 := log_twentyseven_lt_3296_div_1000
  have hratio := log_twentyseven_div_twentysix_upper
  have htwo := log_two_gt_693_div_1000
  norm_num [atanhUpper14, Finset.sum_range_succ] at hratio
  rw [Real.binEntropy]
  have hinv1 : ((1 : ℝ) / 27)⁻¹ = (27 : ℝ) := by norm_num
  have hinv26 : (1 - (1 : ℝ) / 27)⁻¹ = (27 : ℝ) / 26 := by norm_num
  rw [hinv1, hinv26]
  nlinarith

theorem deletion_entropy_margin_one_twentyseventh_pos :
    0 < ((1 : ℝ) / 4 - ((1 : ℝ) / 27) / 2) * Real.log 2 -
        Real.binEntropy ((1 : ℝ) / 27) := by
  have h := binEntropy_one_twentyseventh_lt_229_milli_log_two
  have hlog : 0 < Real.log 2 := Real.log_pos (by norm_num)
  nlinarith

theorem deletion_entropy_margin_one_twentyseventh_quantitative :
    ((67 : ℝ) / 27000) * Real.log 2 <
      ((1 : ℝ) / 4 - ((1 : ℝ) / 27) / 2) * Real.log 2 -
        Real.binEntropy ((1 : ℝ) / 27) := by
  have h := binEntropy_one_twentyseventh_lt_229_milli_log_two
  have hlog : 0 < Real.log 2 := Real.log_pos (by norm_num)
  nlinarith

theorem exp_neg_sharp_margin_n_lt_half {n : ℕ} (hn : 403 ≤ n) :
    Real.exp (-((67 : ℝ) / 27000) * (n : ℝ) * Real.log 2) <
      (1 : ℝ) / 2 := by
  have hlog : 0 < Real.log 2 := Real.log_pos (by norm_num)
  have hn' : (403 : ℝ) ≤ (n : ℝ) := by exact_mod_cast hn
  have harg :
      -((67 : ℝ) / 27000) * (n : ℝ) * Real.log 2 < -Real.log 2 := by
    nlinarith
  calc
    Real.exp (-((67 : ℝ) / 27000) * (n : ℝ) * Real.log 2) <
        Real.exp (-Real.log 2) := (Real.exp_lt_exp).2 harg
    _ = (1 : ℝ) / 2 := by rw [Real.exp_neg, Real.exp_log (by norm_num)]; norm_num

/-! ## Near-optimal rational threshold `alpha = 3/80` -/

theorem log_eighty_div_three_upper :
    Real.log ((80 : ℝ) / 3) ≤
      4 * ((6931472 : ℝ) / 10000000) +
        atanhUpper14 ((1 : ℝ) / 9) + atanhUpper14 ((1 : ℝ) / 7) := by
  have h2 := log_two_lt_6931472_div_ten_million.le
  have h54 := log_one_add_inv_le_atanhUpper14 4 (by norm_num)
  have h43 := log_one_add_inv_le_atanhUpper14 3 (by norm_num)
  have hdecomp : Real.log ((80 : ℝ) / 3) =
      4 * Real.log 2 + Real.log ((5 : ℝ) / 4) + Real.log ((4 : ℝ) / 3) := by
    rw [show (80 : ℝ) / 3 = 2 ^ 4 * ((5 : ℝ) / 4) * ((4 : ℝ) / 3) by norm_num]
    rw [Real.log_mul
      (by norm_num : (2 ^ 4 * ((5 : ℝ) / 4) : ℝ) ≠ 0)
      (by norm_num : (4 : ℝ) / 3 ≠ 0),
      Real.log_mul (by norm_num : (2 ^ 4 : ℝ) ≠ 0)
        (by norm_num : (5 : ℝ) / 4 ≠ 0), Real.log_pow]
    norm_num
  norm_num at h54 h43
  rw [hdecomp]
  linarith

theorem log_eighty_div_seventyseven_upper :
    Real.log ((80 : ℝ) / 77) ≤ atanhUpper14 ((3 : ℝ) / 157) := by
  have hx0 : (0 : ℝ) ≤ 3 / 157 := by norm_num
  have hx1 : (3 : ℝ) / 157 < 1 := by norm_num
  have h := Real.log_div_le_sum_range_add hx0 hx1 14
  have hratio :
      (1 + (3 : ℝ) / 157) / (1 - (3 : ℝ) / 157) = (80 : ℝ) / 77 := by
    norm_num
  rw [hratio] at h
  change Real.log ((80 : ℝ) / 77) ≤ atanhUpper14 ((3 : ℝ) / 157)
  unfold atanhUpper14
  norm_num at h ⊢
  linarith

theorem binEntropy_three_eightieths_lt_231_milli_log_two :
    Real.binEntropy ((3 : ℝ) / 80) <
      ((231 : ℝ) / 1000) * Real.log 2 := by
  have h803 := log_eighty_div_three_upper
  have h8077 := log_eighty_div_seventyseven_upper
  have htwo := log_two_gt_693_div_1000
  norm_num [atanhUpper14, Finset.sum_range_succ] at h803 h8077
  rw [Real.binEntropy]
  have hinv3 : ((3 : ℝ) / 80)⁻¹ = (80 : ℝ) / 3 := by norm_num
  have hinv77 : (1 - (3 : ℝ) / 80)⁻¹ = (80 : ℝ) / 77 := by norm_num
  rw [hinv3, hinv77]
  nlinarith

theorem deletion_entropy_margin_three_eightieths_quantitative :
    ((1 : ℝ) / 4000) * Real.log 2 <
      ((1 : ℝ) / 4 - ((3 : ℝ) / 80) / 2) * Real.log 2 -
        Real.binEntropy ((3 : ℝ) / 80) := by
  have h := binEntropy_three_eightieths_lt_231_milli_log_two
  have hlog : 0 < Real.log 2 := Real.log_pos (by norm_num)
  nlinarith

theorem exp_neg_three_eightieths_margin_n_lt_half
    {n : ℕ} (hn : 4001 ≤ n) :
    Real.exp (-((1 : ℝ) / 4000) * (n : ℝ) * Real.log 2) <
      (1 : ℝ) / 2 := by
  have hlog : 0 < Real.log 2 := Real.log_pos (by norm_num)
  have hn' : (4001 : ℝ) ≤ (n : ℝ) := by exact_mod_cast hn
  have harg :
      -((1 : ℝ) / 4000) * (n : ℝ) * Real.log 2 < -Real.log 2 := by
    nlinarith
  calc
    Real.exp (-((1 : ℝ) / 4000) * (n : ℝ) * Real.log 2) <
        Real.exp (-Real.log 2) := (Real.exp_lt_exp).2 harg
    _ = (1 : ℝ) / 2 := by rw [Real.exp_neg, Real.exp_log (by norm_num)]; norm_num

end

end StableMatchingsJointCharging
