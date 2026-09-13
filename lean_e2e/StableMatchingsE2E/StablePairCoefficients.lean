import StableMatchingsE2E.StablePairConnected
import Mathlib.Analysis.SpecialFunctions.Pow.Real

namespace StableMatchingsE2E.StablePairCoefficients

/-- Reciprocal fourth root of two, represented without decimal approximation. -/
noncomputable def t : ℝ := Real.sqrt (Real.sqrt (1 / 2 : ℝ))
noncomputable def gamma : ℝ := 3 / 2 * t^2

theorem t_pos : 0 < t := by
  unfold t
  positivity

theorem t_fourth : t^4 = (1 / 2 : ℝ) := by
  have h1 : t^2 = Real.sqrt (1 / 2 : ℝ) := by
    exact Real.sq_sqrt (Real.sqrt_nonneg _)
  calc
    t^4 = (t^2)^2 := by ring
    _ = (Real.sqrt (1 / 2 : ℝ))^2 := by rw [h1]
    _ = 1/2 := Real.sq_sqrt (by norm_num)

theorem t_lt_rational : t < (841 / 1000 : ℝ) := by
  by_contra h
  have hp : (841 / 1000 : ℝ)^4 ≤ t^4 :=
    pow_le_pow_left₀ (by norm_num) (le_of_not_gt h) 4
  rw [t_fourth] at hp
  norm_num at hp

theorem gamma_sq : gamma^2 = (9 / 8 : ℝ) := by
  calc
    gamma^2 = 9/4 * t^4 := by unfold gamma; ring
    _ = 9/8 := by rw [t_fourth]; norm_num

theorem gamma_pos : 0 < gamma := by
  have ht := t_pos
  unfold gamma
  positivity

theorem gamma_gt_one : 1 < gamma := by
  have h := gamma_sq
  have hp := gamma_pos
  nlinarith

theorem t_fifth : t^5 = t/2 := by
  calc t^5 = t*t^4 := by ring
       _ = t/2 := by rw [t_fourth]; ring

theorem t_cubed_gamma : t^3*gamma = 3/4*t := by
  calc t^3*gamma = 3/2*t^5 := by unfold gamma; ring
       _ = 3/4*t := by rw [t_fifth]; ring

theorem t_fifth_gamma : t^5*gamma = 3/4*t^3 := by
  rw [t_fifth]
  unfold gamma
  ring

theorem t_fifth_gamma_sq : t^5*gamma^2 = 9/16*t := by
  rw [t_fifth, gamma_sq]
  ring

theorem low_degree_one_two : t^3 + 3/8 < (1 : ℝ) := by
  have hp : t^3 ≤ (841/1000 : ℝ)^3 := pow_le_pow_left₀ t_pos.le t_lt_rational.le 3
  norm_num at hp
  linarith

theorem low_degree_one_large : t^3*gamma + 9/32 < (1 : ℝ) := by
  rw [t_cubed_gamma]
  have h := t_lt_rational
  linarith

theorem low_degree_two_no_high : t^5 + 9/16 < (1 : ℝ) := by
  rw [t_fifth]
  have h := t_lt_rational
  linarith

theorem low_degree_two_one_high : t^5*gamma + 63/128 < (1 : ℝ) := by
  rw [t_fifth_gamma]
  have hp : t^3 ≤ (841/1000 : ℝ)^3 := pow_le_pow_left₀ t_pos.le t_lt_rational.le 3
  norm_num at hp
  linarith

theorem low_degree_two_two_high : t^5*gamma^2 + 54/128 < (1 : ℝ) := by
  rw [t_fifth_gamma_sq]
  have h := t_lt_rational
  linarith

theorem low_degree_two_unique : t^5*gamma + gamma/2 < (1 : ℝ) := by
  rw [t_fifth_gamma]
  have h2 : t^2 ≤ (841/1000 : ℝ)^2 := pow_le_pow_left₀ t_pos.le t_lt_rational.le 2
  have h3 : t^3 ≤ (841/1000 : ℝ)^3 := pow_le_pow_left₀ t_pos.le t_lt_rational.le 3
  unfold gamma
  norm_num at h2 h3
  linarith

theorem high_degree_base : t*(3/4)^3 + 3*t^10*gamma^2 < (24/25 : ℝ) := by
  have h10 : t^10 = t^2/4 := by
    calc t^10 = t^2*(t^4)^2 := by ring
         _ = t^2/4 := by rw [t_fourth]; ring
  rw [h10, gamma_sq]
  have h2 : t^2 ≤ (841/1000 : ℝ)^2 := pow_le_pow_left₀ t_pos.le t_lt_rational.le 2
  have ht := t_lt_rational
  norm_num at h2 ⊢
  linarith

noncomputable def highBound (d : Nat) : ℝ :=
  t*(3/4)^d + (d : ℝ)*t^(2*(d+2))*gamma^2

theorem highBound_succ_le (d : Nat) (hd : 3 ≤ d) : highBound (d+1) ≤ highBound d := by
  have ht := t_pos
  have h2 : t^2 ≤ (3/4 : ℝ) := by
    have h := pow_le_pow_left₀ t_pos.le t_lt_rational.le 2
    norm_num at h
    linarith
  have hdR : (3 : ℝ) ≤ d := by exact_mod_cast hd
  have hcoef : ((d : ℝ)+1)*t^2 ≤ d := by
    calc ((d : ℝ)+1)*t^2 ≤ ((d : ℝ)+1)*(3/4) :=
           mul_le_mul_of_nonneg_left h2 (by positivity)
         _ ≤ d := by linarith
  have hfirst : t*(3/4 : ℝ)^(d+1) ≤ t*(3/4 : ℝ)^d := by
    rw [pow_succ]
    have hp : 0 ≤ t*(3/4 : ℝ)^d := by positivity
    nlinarith
  have hsecond : ((d+1 : Nat) : ℝ)*t^(2*((d+1)+2))*gamma^2 ≤
      (d : ℝ)*t^(2*(d+2))*gamma^2 := by
    have hexp : 2*((d+1)+2) = 2*(d+2)+2 := by omega
    rw [hexp, pow_add]
    push_cast
    calc ((d : ℝ)+1)*(t^(2*(d+2))*t^2)*gamma^2 =
          (((d : ℝ)+1)*t^2)*(t^(2*(d+2))*gamma^2) := by ring
         _ ≤ (d : ℝ)*(t^(2*(d+2))*gamma^2) :=
           mul_le_mul_of_nonneg_right hcoef (by positivity)
         _ = _ := by ring
  exact add_le_add hfirst hsecond

theorem highBound_lt (d : Nat) (hd : 3 ≤ d) : highBound d < (24/25 : ℝ) := by
  have hle : highBound d ≤ highBound 3 := by
    induction d, hd using Nat.le_induction with
    | base => exact le_rfl
    | succ d hd ih => exact (highBound_succ_le d hd).trans ih
  have hbase : highBound 3 < (24/25 : ℝ) := by
    simpa only [highBound, Nat.cast_ofNat] using high_degree_base
  exact hle.trans_lt hbase

end StableMatchingsE2E.StablePairCoefficients
