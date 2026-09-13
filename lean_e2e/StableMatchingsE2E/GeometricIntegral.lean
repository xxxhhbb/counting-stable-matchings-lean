import Mathlib.Analysis.SpecialFunctions.Gamma.Beta
import Mathlib.Analysis.PSeries
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.MeasureTheory.Integral.Lebesgue.Add
import Mathlib.MeasureTheory.Integral.IntervalIntegral.Basic

open scoped ENNReal NNReal Topology

open MeasureTheory Set intervalIntegral

namespace StableMatchingsE2E

lemma complex_beta_nat_three (k : ℕ) (hk : 1 ≤ k) :
    Complex.betaIntegral (k : ℂ) 3 =
      2 / ((k : ℂ) * (k + 1) * (k + 2)) := by
  have hkpos : 0 < ((k : ℂ).re) := by
    simpa using (Nat.cast_pos.mpr (Nat.zero_lt_of_lt hk) : (0 : ℝ) < k)
  convert (Complex.betaIntegral_eval_nat_add_one_right (u := (k : ℂ)) hkpos 2) using 1 <;>
    norm_num [Finset.prod_range_succ]

lemma complex_beta_three_nat_eq_real_integral (k : ℕ) (hk : 1 ≤ k) :
    Complex.betaIntegral 3 (k : ℂ) =
      Complex.ofReal (∫ x : ℝ in 0..1, x ^ 2 * (1 - x) ^ (k - 1)) := by
  have hsub : (k : ℂ) - 1 = ((k - 1 : ℕ) : ℂ) := by
    rw [Nat.cast_sub hk]
    norm_num
  rw [Complex.betaIntegral]
  simp_rw [show (3 : ℂ) - 1 = 2 by norm_num, hsub, Complex.cpow_natCast]
  convert (intervalIntegral.integral_ofReal
    (f := fun x : ℝ => x ^ 2 * (1 - x) ^ (k - 1)) (a := 0) (b := 1)
    (μ := volume)) using 1
  congr 1
  funext x
  push_cast
  change (x : ℂ) ^ ((2 : ℕ) : ℂ) * (1 - (x : ℂ)) ^ (k - 1) =
    (x : ℂ) ^ (2 : ℕ) * (1 - (x : ℂ)) ^ (k - 1)
  rw [Complex.cpow_natCast]

/-- The elementary Beta integral needed for the geometric mass calculation. -/
theorem integral_beta_kernel (k : ℕ) (hk : 1 ≤ k) :
    (∫ x : ℝ in 0..1, x ^ 2 * (1 - x) ^ (k - 1)) =
      2 / ((k : ℝ) * (k + 1) * (k + 2)) := by
  apply Complex.ofReal_injective
  rw [← complex_beta_three_nat_eq_real_integral k hk]
  rw [Complex.betaIntegral_symm]
  rw [complex_beta_nat_three k hk]
  push_cast
  norm_num [Complex.ofReal_div]

/-- Exact integrated mass of the `k`-th size-biased geometric atom.  The factor
`k` is part of the probability mass and must not be dropped. -/
theorem integral_geometric_mass (k : ℕ) (hk : 1 ≤ k) :
    (∫ x : ℝ in 0..1, (k : ℝ) * x ^ 2 * (1 - x) ^ (k - 1)) =
      2 / (((k + 1 : ℕ) : ℝ) * ((k + 2 : ℕ) : ℝ)) := by
  calc
    (∫ x : ℝ in 0..1, (k : ℝ) * x ^ 2 * (1 - x) ^ (k - 1)) =
        (k : ℝ) * (∫ x : ℝ in 0..1, x ^ 2 * (1 - x) ^ (k - 1)) := by
          rw [← intervalIntegral.integral_const_mul]
          congr 1
          funext x
          ring
    _ = (k : ℝ) * (2 / ((k : ℝ) * (k + 1) * (k + 2))) := by
          rw [integral_beta_kernel k hk]
    _ = 2 / (((k + 1 : ℕ) : ℝ) * ((k + 2 : ℕ) : ℝ)) := by
          have hk0 : (k : ℝ) ≠ 0 := by positivity
          push_cast
          field_simp

/-- The real-valued logarithmic atom.  The definitions at `k = 0` and `k = 1`
are harmless: respectively the factor `k` and `log 1` make the atom zero. -/
noncomputable def geometricLogTerm (k : ℕ) (x : ℝ) : ℝ :=
  Real.log (k : ℝ) * ((k : ℝ) * x ^ 2 * (1 - x) ^ (k - 1))

/-- Exact real mass of `geometricLogTerm k`.  Keeping this as a named function
makes later reindexing and Abel summation independent of the integration proof. -/
noncomputable def geometricLogWeight (k : ℕ) : ℝ :=
  Real.log (k : ℝ) *
    (2 / (((k + 1 : ℕ) : ℝ) * ((k + 2 : ℕ) : ℝ)))

lemma geometricLogTerm_continuous (k : ℕ) : Continuous (geometricLogTerm k) := by
  unfold geometricLogTerm
  fun_prop

lemma geometricLogTerm_nonneg_on_Ioc (k : ℕ) {x : ℝ} (hx : x ∈ Ioc (0 : ℝ) 1) :
    0 ≤ geometricLogTerm k x := by
  unfold geometricLogTerm
  have hx1 : 0 ≤ 1 - x := sub_nonneg.mpr hx.2
  exact mul_nonneg (Real.log_natCast_nonneg k)
    (mul_nonneg (mul_nonneg (Nat.cast_nonneg k) (sq_nonneg x)) (pow_nonneg hx1 _))

lemma geometricLogTerm_integrable_Ioc (k : ℕ) :
    Integrable (geometricLogTerm k) (volume.restrict (Ioc (0 : ℝ) 1)) := by
  change IntegrableOn (geometricLogTerm k) (Ioc (0 : ℝ) 1) volume
  exact (intervalIntegrable_iff_integrableOn_Ioc_of_le zero_le_one).mp
    ((geometricLogTerm_continuous k).intervalIntegrable 0 1)

theorem integral_geometric_log_term (k : ℕ) (hk : 1 ≤ k) :
    (∫ x : ℝ in Ioc (0 : ℝ) 1, geometricLogTerm k x) =
      geometricLogWeight k := by
  rw [← intervalIntegral.integral_of_le zero_le_one]
  calc
    (∫ x : ℝ in 0..1, geometricLogTerm k x) =
        Real.log (k : ℝ) *
          (∫ x : ℝ in 0..1, (k : ℝ) * x ^ 2 * (1 - x) ^ (k - 1)) := by
            rw [← intervalIntegral.integral_const_mul]
            congr 1
    _ = geometricLogWeight k := by
            rw [integral_geometric_mass k hk]
            rfl

theorem integral_geometric_log_term_all (k : ℕ) :
    (∫ x : ℝ in Ioc (0 : ℝ) 1, geometricLogTerm k x) = geometricLogWeight k := by
  rcases k with _ | k
  · simp [geometricLogTerm, geometricLogWeight]
  · exact integral_geometric_log_term (k + 1) (Nat.succ_le_succ (Nat.zero_le k))

lemma geometricLogWeight_nonneg (k : ℕ) : 0 ≤ geometricLogWeight k := by
  unfold geometricLogWeight
  positivity

theorem integral_norm_geometric_log_term (k : ℕ) :
    (∫ x : ℝ in Ioc (0 : ℝ) 1, ‖geometricLogTerm k x‖) = geometricLogWeight k := by
  rw [MeasureTheory.integral_congr_ae]
  · exact integral_geometric_log_term_all k
  · filter_upwards [ae_restrict_mem measurableSet_Ioc] with x hx
    rw [Real.norm_eq_abs, abs_of_nonneg (geometricLogTerm_nonneg_on_Ioc k hx)]

/-- Each nonnegative logarithmic atom has the exact `ℝ≥0∞` mass. -/
theorem lintegral_geometric_log_term (k : ℕ) :
    (∫⁻ x : ℝ in Ioc (0 : ℝ) 1, ENNReal.ofReal (geometricLogTerm k x)) =
      ENNReal.ofReal
        (geometricLogWeight k) := by
  rcases k with _ | k
  · simp [geometricLogTerm, geometricLogWeight]
  · have hk : 1 ≤ k + 1 := Nat.succ_le_succ (Nat.zero_le k)
    rw [← integral_geometric_log_term (k + 1) hk]
    apply (MeasureTheory.ofReal_integral_eq_lintegral_ofReal
      (geometricLogTerm_integrable_Ioc (k + 1)) ?_).symm
    filter_upwards [ae_restrict_mem measurableSet_Ioc] with x hx
    exact geometricLogTerm_nonneg_on_Ioc (k + 1) hx

/-- Tonelli's theorem for the whole geometric-logarithmic series.  This equality
is valid in `ℝ≥0∞` before any finiteness or real-valued convergence argument. -/
theorem lintegral_tsum_geometric_log_term :
    (∫⁻ x : ℝ in Ioc (0 : ℝ) 1,
        ∑' k : ℕ, ENNReal.ofReal (geometricLogTerm k x)) =
      ∑' k : ℕ, ENNReal.ofReal
        (geometricLogWeight k) := by
  rw [MeasureTheory.lintegral_tsum]
  · congr 1
    funext k
    exact lintegral_geometric_log_term k
  · intro k
    exact ((geometricLogTerm_continuous k).measurable.ennreal_ofReal).aemeasurable

/-- Real-valued Tonelli/Fubini conversion, with the sole remaining analytic
precondition exposed explicitly as summability of the exact weight sequence. -/
theorem integral_tsum_geometric_log_term_of_summable
    (hsum : Summable geometricLogWeight) :
    (∫ x : ℝ in Ioc (0 : ℝ) 1, ∑' k : ℕ, geometricLogTerm k x) =
      ∑' k : ℕ, geometricLogWeight k := by
  calc
    (∫ x : ℝ in Ioc (0 : ℝ) 1, ∑' k : ℕ, geometricLogTerm k x) =
        ∑' k : ℕ, ∫ x : ℝ in Ioc (0 : ℝ) 1, geometricLogTerm k x := by
          symm
          apply MeasureTheory.integral_tsum_of_summable_integral_norm
          · exact geometricLogTerm_integrable_Ioc
          · simpa only [integral_norm_geometric_log_term] using hsum
    _ = ∑' k : ℕ, geometricLogWeight k := by
          apply tsum_congr
          exact integral_geometric_log_term_all

end StableMatchingsE2E
