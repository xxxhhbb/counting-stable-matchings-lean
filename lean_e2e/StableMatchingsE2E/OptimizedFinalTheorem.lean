import StableMatchingsE2E.MethodLimit
import StableMatchingsE2E.ConstantOptimization

namespace StableMatchingsE2E

open MeasureTheory ProbabilityTheory Set
open scoped unitInterval ENNReal BigOperators
open StableMatchings355 StableMatchingsEntropy

noncomputable section

private theorem exp_nat_mul_log_eq_pow_optimized {q : ℝ} (hq : 0 < q)
    (n : ℕ) :
    Real.exp ((n : ℝ) * Real.log q) = q ^ n := by
  induction n with
  | zero => simp
  | succ n ih =>
      rw [Nat.cast_succ, add_mul, Real.exp_add, ih, pow_succ]
      simp [Real.exp_log hq]

private theorem log_lt_to_nat_crossmul_833_250 {n a : ℕ}
    (ha : 0 < a)
    (hlog : Real.log (a : ℝ) <
      (n : ℝ) * Real.log ((833 : ℝ) / 250)) :
    250 ^ n * a < 833 ^ n := by
  have hq : (0 : ℝ) < (833 : ℝ) / 250 := by norm_num
  have hexp := (Real.exp_lt_exp).mpr hlog
  rw [Real.exp_log (by exact_mod_cast ha),
    exp_nat_mul_log_eq_pow_optimized hq n] at hexp
  have hden : 0 < (250 : ℝ) ^ n := pow_pos (by norm_num) n
  have hmul := mul_lt_mul_of_pos_left hexp hden
  rw [div_pow] at hmul
  field_simp at hmul
  exact_mod_cast hmul

private theorem log_lt_to_nat_crossmul_1665987_500000 {n a : ℕ}
    (ha : 0 < a)
    (hlog : Real.log (a : ℝ) <
      (n : ℝ) * Real.log ((1665987 : ℝ) / 500000)) :
    500000 ^ n * a < 1665987 ^ n := by
  have hq : (0 : ℝ) < (1665987 : ℝ) / 500000 := by norm_num
  have hexp := (Real.exp_lt_exp).mpr hlog
  rw [Real.exp_log (by exact_mod_cast ha),
    exp_nat_mul_log_eq_pow_optimized hq n] at hexp
  have hden : 0 < (500000 : ℝ) ^ n := pow_pos (by norm_num) n
  have hmul := mul_lt_mul_of_pos_left hexp hden
  rw [div_pow] at hmul
  field_simp at hmul
  exact_mod_cast hmul

theorem log_stableCount_lt_n_log_833_div_250 (n : Nat)
    (hn : 1 ≤ n) (P : ProfileCode n) :
    Real.log (stableCount P) <
      (n : ℝ) * Real.log ((833 : ℝ) / 250) := by
  exact lt_of_le_of_lt
    (log_stableCount_le_n_geometricLogSeries_all n P)
    (mul_lt_mul_of_pos_left geometricLogSeries_lt_log_833_div_250
      (by exact_mod_cast hn))

theorem stableCount_nat_bound_833_div_250 (n : Nat)
    (hn : 1 ≤ n) (P : ProfileCode n) :
    250 ^ n * stableCount P < 833 ^ n := by
  by_cases hz : stableCount P = 0
  · rw [hz, mul_zero]
    exact pow_pos (by norm_num) n
  · exact log_lt_to_nat_crossmul_833_250 (Nat.pos_of_ne_zero hz)
      (log_stableCount_lt_n_log_833_div_250 n hn P)

theorem SM_nat_bound_833_div_250 (n : Nat) (hn : 1 ≤ n) :
    250 ^ n * SM n < 833 ^ n := by
  obtain ⟨P, hP⟩ := exists_profile_attaining_SM n
  simpa [hP] using stableCount_nat_bound_833_div_250 n hn P

theorem stableCount_lt_833_div_250_pow (n : Nat)
    (hn : 1 ≤ n) (P : ProfileCode n) :
    (stableCount P : ℝ) < ((833 : ℝ) / 250) ^ n := by
  have h := stableCount_nat_bound_833_div_250 n hn P
  have hden : 0 < (250 : ℝ) ^ n := pow_pos (by norm_num) n
  rw [div_pow, (lt_div_iff₀ hden)]
  exact_mod_cast (show stableCount P * 250 ^ n < 833 ^ n by
    simpa [Nat.mul_comm] using h)

theorem SM_lt_833_div_250_pow (n : Nat) (hn : 1 ≤ n) :
    (SM n : ℝ) < ((833 : ℝ) / 250) ^ n := by
  have h := SM_nat_bound_833_div_250 n hn
  have hden : 0 < (250 : ℝ) ^ n := pow_pos (by norm_num) n
  rw [div_pow, (lt_div_iff₀ hden)]
  exact_mod_cast (show SM n * 250 ^ n < 833 ^ n by
    simpa [Nat.mul_comm] using h)

/-! ## Six-decimal rounding-up of the exact analytic endpoint -/

theorem log_stableCount_lt_n_log_1665987_div_500000 (n : Nat)
    (hn : 1 ≤ n) (P : ProfileCode n) :
    Real.log (stableCount P) <
      (n : ℝ) * Real.log ((1665987 : ℝ) / 500000) := by
  exact lt_of_le_of_lt
    (log_stableCount_le_n_geometricLogSeries_all n P)
    (mul_lt_mul_of_pos_left geometricLogSeries_lt_log_1665987_div_500000
      (by exact_mod_cast hn))

/-- Exact kernel-facing profile bound at base `3.331974`. -/
theorem stableCount_nat_bound_1665987_div_500000 (n : Nat)
    (hn : 1 ≤ n) (P : ProfileCode n) :
    500000 ^ n * stableCount P < 1665987 ^ n := by
  by_cases hz : stableCount P = 0
  · rw [hz, mul_zero]
    exact pow_pos (by norm_num) n
  · exact log_lt_to_nat_crossmul_1665987_500000 (Nat.pos_of_ne_zero hz)
      (log_stableCount_lt_n_log_1665987_div_500000 n hn P)

/-- Exact kernel-facing extremal bound at base `3.331974`. -/
theorem SM_nat_bound_1665987_div_500000 (n : Nat) (hn : 1 ≤ n) :
    500000 ^ n * SM n < 1665987 ^ n := by
  obtain ⟨P, hP⟩ := exists_profile_attaining_SM n
  simpa [hP] using stableCount_nat_bound_1665987_div_500000 n hn P

/-- Real-valued profile bound at base `3.331974`. -/
theorem stableCount_lt_1665987_div_500000_pow (n : Nat)
    (hn : 1 ≤ n) (P : ProfileCode n) :
    (stableCount P : ℝ) < ((1665987 : ℝ) / 500000) ^ n := by
  have h := stableCount_nat_bound_1665987_div_500000 n hn P
  have hden : 0 < (500000 : ℝ) ^ n := pow_pos (by norm_num) n
  rw [div_pow, (lt_div_iff₀ hden)]
  exact_mod_cast (show stableCount P * 500000 ^ n < 1665987 ^ n by
    simpa [Nat.mul_comm] using h)

/-- Real-valued extremal bound at base `3.331974`. -/
theorem SM_lt_1665987_div_500000_pow (n : Nat) (hn : 1 ≤ n) :
    (SM n : ℝ) < ((1665987 : ℝ) / 500000) ^ n := by
  have h := SM_nat_bound_1665987_div_500000 n hn
  have hden : 0 < (500000 : ℝ) ^ n := pow_pos (by norm_num) n
  rw [div_pow, (lt_div_iff₀ hden)]
  exact_mod_cast (show SM n * 500000 ^ n < 1665987 ^ n by
    simpa [Nat.mul_comm] using h)

end

end StableMatchingsE2E
