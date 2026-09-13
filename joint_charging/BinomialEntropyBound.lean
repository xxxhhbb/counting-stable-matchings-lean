import Mathlib.Analysis.SpecialFunctions.BinaryEntropy
import Mathlib.Data.Nat.Choose.Sum
import Mathlib.Tactic

namespace StableMatchingsJointCharging

open scoped BigOperators

noncomputable section

def bernoulliWeight (p : ℝ) (n i : ℕ) : ℝ :=
  p ^ i * (1 - p) ^ (n - i)

theorem bernoulliWeight_antitone_to_half
    {p : ℝ} {i k n : ℕ}
    (hp : 0 ≤ p) (hpq : p ≤ 1 - p)
    (hik : i ≤ k) (hkn : k ≤ n) :
    bernoulliWeight p n k ≤ bernoulliWeight p n i := by
  have hi_n : i ≤ n := hik.trans hkn
  have hpow : p ^ (k - i) ≤ (1 - p) ^ (k - i) := by
    exact pow_le_pow_left₀ hp hpq _
  have hp_i : 0 ≤ p ^ i := pow_nonneg hp _
  have hq : 0 ≤ 1 - p := hp.trans hpq
  have hq_tail : 0 ≤ (1 - p) ^ (n - k) := pow_nonneg hq _
  unfold bernoulliWeight
  calc
    p ^ k * (1 - p) ^ (n - k) =
        (p ^ i * p ^ (k - i)) * (1 - p) ^ (n - k) := by
      rw [← pow_add]
      congr 2
      omega
    _ ≤ (p ^ i * (1 - p) ^ (k - i)) * (1 - p) ^ (n - k) := by
      gcongr
    _ = p ^ i * (1 - p) ^ (n - i) := by
      rw [mul_assoc, ← pow_add]
      congr 2
      omega

theorem bernoulliWeight_mul_choose_prefix_le_one
    {p : ℝ} {k n : ℕ}
    (hp : 0 ≤ p) (hpq : p ≤ 1 - p) (hkn : k ≤ n) :
    bernoulliWeight p n k *
        (∑ i ∈ Finset.range (k + 1), (n.choose i : ℝ)) ≤ 1 := by
  have hq : 0 ≤ 1 - p := hp.trans hpq
  calc
    bernoulliWeight p n k *
          (∑ i ∈ Finset.range (k + 1), (n.choose i : ℝ)) =
        ∑ i ∈ Finset.range (k + 1),
          bernoulliWeight p n k * (n.choose i : ℝ) := by
      rw [Finset.mul_sum]
    _ ≤ ∑ i ∈ Finset.range (k + 1),
          bernoulliWeight p n i * (n.choose i : ℝ) := by
      apply Finset.sum_le_sum
      intro i hi
      apply mul_le_mul_of_nonneg_right
        (bernoulliWeight_antitone_to_half hp hpq
          (Nat.le_of_lt_succ (Finset.mem_range.mp hi)) hkn)
        (Nat.cast_nonneg _)
    _ ≤ ∑ i ∈ Finset.range (n + 1),
          bernoulliWeight p n i * (n.choose i : ℝ) := by
      apply Finset.sum_le_sum_of_subset_of_nonneg
      · exact Finset.range_mono (Nat.add_le_add_right hkn 1)
      · intro i hi hnot
        exact mul_nonneg
          (mul_nonneg (pow_nonneg hp _) (pow_nonneg hq _))
          (Nat.cast_nonneg _)
    _ = (p + (1 - p)) ^ n := by
      rw [add_pow]
      apply Finset.sum_congr rfl
      intro i hi
      rfl
    _ = 1 := by ring

theorem choose_prefix_le_inv_bernoulliWeight
    {p : ℝ} {k n : ℕ}
    (hp : 0 < p) (hpq : p ≤ 1 - p) (hkn : k ≤ n) :
    (∑ i ∈ Finset.range (k + 1), (n.choose i : ℝ)) ≤
      1 / bernoulliWeight p n k := by
  have hq : 0 < 1 - p := hp.trans_le hpq
  have hw : 0 < bernoulliWeight p n k := by
    unfold bernoulliWeight
    positivity
  rw [le_div_iff₀ hw]
  simpa [mul_comm] using
    bernoulliWeight_mul_choose_prefix_le_one hp.le hpq hkn

theorem inv_bernoulliWeight_one_twentyseventh_eq_exp
    (n k : ℕ) :
    1 / bernoulliWeight ((1 : ℝ) / 27) n k =
      Real.exp
        ((k : ℝ) * Real.log 27 +
          ((n - k : ℕ) : ℝ) * Real.log ((27 : ℝ) / 26)) := by
  rw [Real.exp_add]
  have h27 : (0 : ℝ) < 27 := by norm_num
  have h2726 : (0 : ℝ) < (27 : ℝ) / 26 := by norm_num
  have hk : Real.exp ((k : ℝ) * Real.log 27) = (27 : ℝ) ^ k := by
    rw [Real.exp_nat_mul, Real.exp_log h27]
  have hnk :
      Real.exp (((n - k : ℕ) : ℝ) * Real.log ((27 : ℝ) / 26)) =
        ((27 : ℝ) / 26) ^ (n - k) := by
    rw [Real.exp_nat_mul, Real.exp_log h2726]
  rw [hk, hnk]
  unfold bernoulliWeight
  norm_num [one_div, div_pow]
  ring

theorem exponent_one_twentyseventh_le_binEntropy
    {n k : ℕ} (hkn : 27 * k ≤ n) :
    (k : ℝ) * Real.log 27 +
        ((n - k : ℕ) : ℝ) * Real.log ((27 : ℝ) / 26) ≤
      (n : ℝ) * Real.binEntropy ((1 : ℝ) / 27) := by
  have hk : k ≤ n := by omega
  have hcast : (27 : ℝ) * (k : ℝ) ≤ (n : ℝ) := by
    exact_mod_cast hkn
  have hsub : ((n - k : ℕ) : ℝ) = (n : ℝ) - (k : ℝ) := by
    exact Nat.cast_sub hk
  have hlog : Real.log ((27 : ℝ) / 26) ≤ Real.log 27 := by
    exact Real.strictMonoOn_log.monotoneOn (by norm_num) (by norm_num) (by norm_num)
  have hentropy :
      Real.binEntropy ((1 : ℝ) / 27) =
        ((1 : ℝ) / 27) * Real.log 27 +
          ((26 : ℝ) / 27) * Real.log ((27 : ℝ) / 26) := by
    rw [Real.binEntropy]
    norm_num
  rw [hsub, hentropy]
  nlinarith

theorem choose_prefix_le_exp_binEntropy_one_twentyseventh
    {n k : ℕ} (hkn : 27 * k ≤ n) :
    (∑ i ∈ Finset.range (k + 1), (n.choose i : ℝ)) ≤
      Real.exp ((n : ℝ) * Real.binEntropy ((1 : ℝ) / 27)) := by
  have hk : k ≤ n := by omega
  calc
    (∑ i ∈ Finset.range (k + 1), (n.choose i : ℝ)) ≤
        1 / bernoulliWeight ((1 : ℝ) / 27) n k := by
      exact choose_prefix_le_inv_bernoulliWeight (by norm_num) (by norm_num) hk
    _ = Real.exp
          ((k : ℝ) * Real.log 27 +
            ((n - k : ℕ) : ℝ) * Real.log ((27 : ℝ) / 26)) :=
      inv_bernoulliWeight_one_twentyseventh_eq_exp n k
    _ ≤ Real.exp ((n : ℝ) * Real.binEntropy ((1 : ℝ) / 27)) := by
      exact Real.exp_le_exp.mpr (exponent_one_twentyseventh_le_binEntropy hkn)

/-! ## Near-optimal rational threshold `p = 3/80` -/

theorem inv_bernoulliWeight_three_eightieths_eq_exp
    (n k : ℕ) :
    1 / bernoulliWeight ((3 : ℝ) / 80) n k =
      Real.exp
        ((k : ℝ) * Real.log ((80 : ℝ) / 3) +
          ((n - k : ℕ) : ℝ) * Real.log ((80 : ℝ) / 77)) := by
  rw [Real.exp_add]
  have h803 : (0 : ℝ) < (80 : ℝ) / 3 := by norm_num
  have h8077 : (0 : ℝ) < (80 : ℝ) / 77 := by norm_num
  have hk :
      Real.exp ((k : ℝ) * Real.log ((80 : ℝ) / 3)) =
        ((80 : ℝ) / 3) ^ k := by
    rw [Real.exp_nat_mul, Real.exp_log h803]
  have hnk :
      Real.exp (((n - k : ℕ) : ℝ) * Real.log ((80 : ℝ) / 77)) =
        ((80 : ℝ) / 77) ^ (n - k) := by
    rw [Real.exp_nat_mul, Real.exp_log h8077]
  rw [hk, hnk]
  unfold bernoulliWeight
  norm_num [one_div, div_pow]
  ring

theorem exponent_three_eightieths_le_binEntropy
    {n k : ℕ} (hkn : 80 * k ≤ 3 * n) :
    (k : ℝ) * Real.log ((80 : ℝ) / 3) +
        ((n - k : ℕ) : ℝ) * Real.log ((80 : ℝ) / 77) ≤
      (n : ℝ) * Real.binEntropy ((3 : ℝ) / 80) := by
  have hk : k ≤ n := by omega
  have hcast : (80 : ℝ) * (k : ℝ) ≤ 3 * (n : ℝ) := by
    exact_mod_cast hkn
  have hsub : ((n - k : ℕ) : ℝ) = (n : ℝ) - (k : ℝ) := Nat.cast_sub hk
  have hlog :
      Real.log ((80 : ℝ) / 77) ≤ Real.log ((80 : ℝ) / 3) := by
    exact Real.strictMonoOn_log.monotoneOn (by norm_num) (by norm_num) (by norm_num)
  have hentropy :
      Real.binEntropy ((3 : ℝ) / 80) =
        ((3 : ℝ) / 80) * Real.log ((80 : ℝ) / 3) +
          ((77 : ℝ) / 80) * Real.log ((80 : ℝ) / 77) := by
    rw [Real.binEntropy]
    norm_num
  rw [hsub, hentropy]
  nlinarith

theorem choose_prefix_le_exp_binEntropy_three_eightieths
    {n k : ℕ} (hkn : 80 * k ≤ 3 * n) :
    (∑ i ∈ Finset.range (k + 1), (n.choose i : ℝ)) ≤
      Real.exp ((n : ℝ) * Real.binEntropy ((3 : ℝ) / 80)) := by
  have hk : k ≤ n := by omega
  calc
    (∑ i ∈ Finset.range (k + 1), (n.choose i : ℝ)) ≤
        1 / bernoulliWeight ((3 : ℝ) / 80) n k := by
      exact choose_prefix_le_inv_bernoulliWeight (by norm_num) (by norm_num) hk
    _ = Real.exp
          ((k : ℝ) * Real.log ((80 : ℝ) / 3) +
            ((n - k : ℕ) : ℝ) * Real.log ((80 : ℝ) / 77)) :=
      inv_bernoulliWeight_three_eightieths_eq_exp n k
    _ ≤ Real.exp ((n : ℝ) * Real.binEntropy ((3 : ℝ) / 80)) := by
      exact Real.exp_le_exp.mpr (exponent_three_eightieths_le_binEntropy hkn)

end

end StableMatchingsJointCharging
