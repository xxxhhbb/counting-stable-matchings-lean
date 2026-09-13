import StableMatchingsE2E.GeometricIntegral
import Mathlib.Analysis.SpecialFunctions.Log.Deriv
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Analysis.PSeries

open scoped BigOperators Topology

open Filter Finset

namespace StableMatchingsE2E

/-- The exact logarithmic series arising after integrating the size-biased
geometric law. -/
noncomputable def geometricLogSeries : ℝ := ∑' k : ℕ, geometricLogWeight k

/-- A p-series comparison which closes the sole analytic hypothesis left by
`GeometricIntegral`. -/
theorem summable_geometricLogWeight : Summable geometricLogWeight := by
  have hp : Summable (fun k : ℕ => 4 * (k : ℝ) ^ (-(3 / 2 : ℝ))) :=
    (Real.summable_nat_rpow.mpr (by norm_num)).mul_left 4
  refine hp.of_nonneg_of_le geometricLogWeight_nonneg ?_
  intro k
  rcases k with _ | _ | k
  · simp [geometricLogWeight]
  · simp [geometricLogWeight]
  · simp only [Nat.cast_add, Nat.cast_one]
    have hkpos : (0 : ℝ) < (k : ℝ) + 1 + 1 := by positivity
    have hlog : Real.log ((k + 2 : ℕ) : ℝ) ≤
        ((k + 2 : ℕ) : ℝ) ^ (1 / 2 : ℝ) / (1 / 2 : ℝ) :=
      Real.log_natCast_le_rpow_div (k + 2) (by norm_num)
    rw [show (-(3 / 2 : ℝ)) = (1 / 2 : ℝ) - 2 by norm_num,
      Real.rpow_sub hkpos]
    unfold geometricLogWeight
    push_cast
    norm_num [Nat.cast_add, add_assoc] at hlog ⊢
    norm_num [div_eq_mul_inv] at hlog
    change Real.log ((k : ℝ) + 2) *
        (2 / (((k : ℝ) + 3) * ((k : ℝ) + 4))) ≤
      4 * (((k : ℝ) + 2) ^ (1 / 2 : ℝ) / ((k : ℝ) + 2) ^ 2)
    have hden : (((k : ℝ) + 2) : ℝ) ^ 2 ≤
        ((k : ℝ) + 3) * ((k : ℝ) + 4) := by nlinarith
    have hkpow : 0 ≤ ((k : ℝ) + 2) ^ (1 / 2 : ℝ) := by positivity
    have hfrac : 2 / (((k : ℝ) + 3) * ((k : ℝ) + 4)) ≤
        2 / ((k : ℝ) + 2) ^ 2 := by
      gcongr
    calc
      Real.log ((k : ℝ) + 2) *
          (2 / (((k : ℝ) + 3) * ((k : ℝ) + 4))) ≤
          (2 * ((k : ℝ) + 2) ^ (1 / 2 : ℝ)) *
            (2 / (((k : ℝ) + 3) * ((k : ℝ) + 4))) := by
              exact mul_le_mul_of_nonneg_right (by simpa [mul_comm] using hlog) (by positivity)
      _ ≤ (2 * ((k : ℝ) + 2) ^ (1 / 2 : ℝ)) *
            (2 / ((k : ℝ) + 2) ^ 2) := by gcongr
      _ = 4 * (((k : ℝ) + 2) ^ (1 / 2 : ℝ) / ((k : ℝ) + 2) ^ 2) := by ring

/-- Third-order alternating Taylor upper bound, proved globally on the
nonnegative half-line.  The proof uses Mathlib's certified atanh-series
remainder at `x = t/(2+t)`; the final gap is an explicitly positive rational
function. -/
theorem log_one_add_le_cubic {t : ℝ} (ht : 0 ≤ t) :
    Real.log (1 + t) ≤ t - t ^ 2 / 2 + t ^ 3 / 3 := by
  let x : ℝ := t / (2 + t)
  have hx0 : 0 ≤ x := by dsimp [x]; positivity
  have hx1 : x < 1 := by
    dsimp [x]
    rw [div_lt_one (by linarith : 0 < 2 + t)]
    linarith
  have hseries := Real.log_div_le_sum_range_add hx0 hx1 2
  have hratio : (1 + x) / (1 - x) = 1 + t := by
    dsimp [x]
    field_simp [show 2 + t ≠ 0 by linarith]
    ring
  rw [hratio] at hseries
  norm_num [Finset.sum_range_succ] at hseries
  have hlog : Real.log (1 + t) ≤
      2 * (x + x ^ 3 / 3 + x ^ 5 / (1 - x ^ 2)) := by linarith
  refine hlog.trans ?_
  rw [← sub_nonneg]
  have hone : 1 - x ^ 2 = 4 * (1 + t) / (2 + t) ^ 2 := by
    dsimp [x]
    field_simp [show 2 + t ≠ 0 by linarith]
    ring
  have hident :
      t - t ^ 2 / 2 + t ^ 3 / 3 -
          2 * (x + x ^ 3 / 3 + x ^ 5 / (1 - x ^ 2)) =
        t ^ 4 * (2 * t ^ 3 + 11 * t ^ 2 + 18 * t + 12) /
          (6 * (t + 1) * (t + 2) ^ 3) := by
    rw [hone]
    dsimp [x]
    field_simp [show t + 1 ≠ 0 by linarith, show t + 2 ≠ 0 by linarith]
    ring
  rw [hident]
  positivity

/-- A small exact rational upper certificate for `log 2`. -/
theorem log_two_lt_347_div_500 : Real.log 2 < (347 : ℝ) / 500 := by
  have h := Real.log_div_le_sum_range_add
    (x := (1 : ℝ) / 3) (by norm_num) (by norm_num) 6
  norm_num [Finset.sum_range_succ] at h
  nlinarith

/-- A small exact rational lower certificate for `log (17/5)`. -/
theorem sixty_one_div_fifty_lt_log_seventeen_div_five :
    (61 : ℝ) / 50 < Real.log ((17 : ℝ) / 5) := by
  have h := Real.sum_range_le_log_div
    (x := (6 : ℝ) / 11) (by norm_num) (by norm_num) 10
  norm_num [Finset.sum_range_succ] at h
  nlinarith

/-- Abel-transformed term with original index `m = j+2`. -/
noncomputable def abelShiftTerm (j : ℕ) : ℝ :=
  2 * Real.log (1 + 1 / ((j + 2 : ℕ) : ℝ)) / ((j + 4 : ℕ) : ℝ)

/-- The entire finite numerical part of the certificate.  All nineteen log
terms are bounded by `log_one_add_le_cubic`; `norm_num` checks the resulting
rational inequality in the kernel. -/
theorem abel_head_plus_tail_budget_lt_sixty_one_div_fifty :
    (2 / 3 : ℝ) * Real.log 2 +
        (∑ j ∈ Finset.range 19, abelShiftTerm j) + 1 / 10 < 61 / 50 := by
  have hsum :
      (∑ j ∈ Finset.range 19, abelShiftTerm j) ≤
        ∑ j ∈ Finset.range 19,
          (2 / (((j + 4 : ℕ) : ℝ))) *
            (1 / (((j + 2 : ℕ) : ℝ)) -
              (1 / (((j + 2 : ℕ) : ℝ))) ^ 2 / 2 +
              (1 / (((j + 2 : ℕ) : ℝ))) ^ 3 / 3) := by
    apply Finset.sum_le_sum
    intro j hj
    have hlog := log_one_add_le_cubic
      (t := 1 / (((j + 2 : ℕ) : ℝ))) (by positivity)
    unfold abelShiftTerm
    calc
      2 * Real.log (1 + 1 / (((j + 2 : ℕ) : ℝ))) / (((j + 4 : ℕ) : ℝ)) =
          (2 / (((j + 4 : ℕ) : ℝ))) *
            Real.log (1 + 1 / (((j + 2 : ℕ) : ℝ))) := by ring
      _ ≤ (2 / (((j + 4 : ℕ) : ℝ))) *
            (1 / (((j + 2 : ℕ) : ℝ)) -
              (1 / (((j + 2 : ℕ) : ℝ))) ^ 2 / 2 +
              (1 / (((j + 2 : ℕ) : ℝ))) ^ 3 / 3) :=
        mul_le_mul_of_nonneg_left hlog (by positivity)
  calc
    (2 / 3 : ℝ) * Real.log 2 +
          (∑ j ∈ Finset.range 19, abelShiftTerm j) + 1 / 10 ≤
        (2 / 3 : ℝ) * Real.log 2 +
          (∑ j ∈ Finset.range 19,
            (2 / (((j + 4 : ℕ) : ℝ))) *
              (1 / (((j + 2 : ℕ) : ℝ)) -
                (1 / (((j + 2 : ℕ) : ℝ))) ^ 2 / 2 +
                (1 / (((j + 2 : ℕ) : ℝ))) ^ 3 / 3)) + 1 / 10 := by
            gcongr
    _ <
        (2 / 3 : ℝ) * (347 / 500) +
          (∑ j ∈ Finset.range 19,
            (2 / (((j + 4 : ℕ) : ℝ))) *
              (1 / (((j + 2 : ℕ) : ℝ)) -
                (1 / (((j + 2 : ℕ) : ℝ))) ^ 2 / 2 +
                (1 / (((j + 2 : ℕ) : ℝ))) ^ 3 / 3)) + 1 / 10 := by
            gcongr <;> exact log_two_lt_347_div_500
    _ < 61 / 50 := by norm_num [Finset.sum_range_succ]

lemma abelShiftTerm_nonneg (j : ℕ) : 0 ≤ abelShiftTerm j := by
  unfold abelShiftTerm
  have hinv : 0 ≤ 1 / (((j + 2 : ℕ) : ℝ)) := by positivity
  have hlog : 0 ≤ Real.log (1 + 1 / (((j + 2 : ℕ) : ℝ))) :=
    Real.log_nonneg (by linarith)
  positivity

/-- Exact telescoping majorant used for the part `m > 20`. -/
noncomputable def tailTelescoper (j : ℕ) : ℝ :=
  2 * (1 / (((j + 20 : ℕ) : ℝ)) - 1 / (((j + 21 : ℕ) : ℝ)))

lemma tailTelescoper_nonneg (j : ℕ) : 0 ≤ tailTelescoper j := by
  unfold tailTelescoper
  have h : (0 : ℝ) < ((j : ℝ) + 20) := by positivity
  have h' : ((j : ℝ) + 20) ≤ (j : ℝ) + 21 := by linarith
  norm_num [Nat.cast_add, add_assoc]
  simpa only [one_div] using one_div_le_one_div_of_le h h'

lemma sum_range_tailTelescoper (n : ℕ) :
    ∑ j ∈ Finset.range n, tailTelescoper j =
      2 * (1 / 20 - 1 / (((n + 20 : ℕ) : ℝ))) := by
  induction n with
  | zero => norm_num [tailTelescoper]
  | succ n ih =>
      rw [Finset.sum_range_succ, ih]
      unfold tailTelescoper
      push_cast
      field_simp
      ring

theorem hasSum_tailTelescoper : HasSum tailTelescoper (1 / 10 : ℝ) := by
  rw [hasSum_iff_tendsto_nat_of_nonneg tailTelescoper_nonneg]
  simp_rw [sum_range_tailTelescoper]
  have htop : Filter.Tendsto (fun n : ℕ => (n : ℝ) + 20)
      Filter.atTop Filter.atTop :=
    tendsto_atTop_add_const_right Filter.atTop 20 tendsto_natCast_atTop_atTop
  have hinv : Filter.Tendsto (fun n : ℕ => 1 / ((n : ℝ) + 20))
      Filter.atTop (nhds 0) := by
    simpa only [one_div, Function.comp_def] using tendsto_inv_atTop_zero.comp htop
  have hlim : Filter.Tendsto
      (fun n : ℕ => 2 * (1 / 20 - 1 / ((n : ℝ) + 20))) Filter.atTop
      (nhds (2 * (1 / 20 - 0))) := (tendsto_const_nhds.sub hinv).const_mul 2
  convert hlim using 1 <;> norm_num [Nat.cast_add]

lemma abel_tail_pointwise (j : ℕ) :
    abelShiftTerm (j + 19) ≤ tailTelescoper j := by
  have hlog : Real.log (1 + 1 / (((j + 21 : ℕ) : ℝ))) ≤
      1 / (((j + 21 : ℕ) : ℝ)) := by
    have := Real.log_le_sub_one_of_pos
      (show (0 : ℝ) < 1 + 1 / (((j + 21 : ℕ) : ℝ)) by positivity)
    linarith
  unfold abelShiftTerm tailTelescoper
  norm_num [Nat.cast_add, add_assoc] at hlog ⊢
  calc
    2 * Real.log (1 + ((j : ℝ) + 21)⁻¹) / ((j : ℝ) + 23) =
        (2 / ((j : ℝ) + 23)) * Real.log (1 + ((j : ℝ) + 21)⁻¹) := by ring
    _ ≤ (2 / ((j : ℝ) + 23)) * ((j : ℝ) + 21)⁻¹ := by gcongr
    _ ≤ 2 / ((j : ℝ) + 21) ^ 2 := by
      rw [le_div_iff₀ (by positivity : (0 : ℝ) < ((j : ℝ) + 21) ^ 2)]
      field_simp
      nlinarith
    _ ≤ 2 * (((j : ℝ) + 20)⁻¹ - ((j : ℝ) + 21)⁻¹) := by
      rw [div_le_iff₀ (by positivity : (0 : ℝ) < ((j : ℝ) + 21) ^ 2)]
      field_simp
      nlinarith

theorem abel_tail_le_one_tenth :
    (∑' j : ℕ, abelShiftTerm (j + 19)) ≤ (1 / 10 : ℝ) := by
  have htel : Summable tailTelescoper := hasSum_tailTelescoper.summable
  have hab : Summable (fun j : ℕ => abelShiftTerm (j + 19)) :=
    htel.of_nonneg_of_le (fun j => abelShiftTerm_nonneg _) abel_tail_pointwise
  calc
    (∑' j : ℕ, abelShiftTerm (j + 19)) ≤ ∑' j : ℕ, tailTelescoper j :=
      Summable.tsum_le_tsum abel_tail_pointwise hab htel
    _ = 1 / 10 := hasSum_tailTelescoper.tsum_eq

theorem summable_abelShiftTerm : Summable abelShiftTerm := by
  have htail : Summable (fun j : ℕ => abelShiftTerm (j + 19)) := by
    have htel : Summable tailTelescoper := hasSum_tailTelescoper.summable
    exact htel.of_nonneg_of_le (fun j => abelShiftTerm_nonneg _) abel_tail_pointwise
  exact (summable_nat_add_iff 19).mp htail

noncomputable def abelBoundary (j : ℕ) : ℝ :=
  2 * Real.log (((j + 2 : ℕ) : ℝ)) / (((j + 3 : ℕ) : ℝ))

lemma geometric_weight_shift_abel (j : ℕ) :
    geometricLogWeight (j + 2) =
      (abelBoundary j - abelBoundary (j + 1)) + abelShiftTerm j := by
  have hratio : 1 + 1 / (((j + 2 : ℕ) : ℝ)) =
      (((j + 3 : ℕ) : ℝ)) / (((j + 2 : ℕ) : ℝ)) := by
    push_cast
    field_simp
    ring
  have hlog : Real.log (1 + 1 / (((j + 2 : ℕ) : ℝ))) =
      Real.log (((j + 3 : ℕ) : ℝ)) - Real.log (((j + 2 : ℕ) : ℝ)) := by
    rw [hratio, Real.log_div (by positivity) (by positivity)]
  unfold geometricLogWeight abelBoundary abelShiftTerm
  norm_num [Nat.cast_add, add_assoc] at hlog ⊢
  rw [hlog]
  field_simp
  ring

lemma sum_range_abelBoundary_diff (n : ℕ) :
    ∑ j ∈ Finset.range n, (abelBoundary j - abelBoundary (j + 1)) =
      abelBoundary 0 - abelBoundary n := by
  induction n with
  | zero => simp
  | succ n ih =>
      rw [Finset.sum_range_succ, ih]
      ring

lemma tendsto_abelBoundary_zero :
    Filter.Tendsto abelBoundary Filter.atTop (nhds 0) := by
  have htop : Filter.Tendsto (fun n : ℕ => (n : ℝ) + 2)
      Filter.atTop Filter.atTop :=
    tendsto_atTop_add_const_right Filter.atTop 2 tendsto_natCast_atTop_atTop
  have hratio : Filter.Tendsto
      (fun n : ℕ => Real.log ((n : ℝ) + 2) / ((n : ℝ) + 2))
      Filter.atTop (nhds 0) := by
    simpa only [Function.comp_def, id_eq] using
      Real.isLittleO_log_id_atTop.tendsto_div_nhds_zero.comp htop
  have hmajor := hratio.const_mul 2
  refine squeeze_zero' (f := abelBoundary)
    (g := fun n : ℕ => 2 * (Real.log ((n : ℝ) + 2) / ((n : ℝ) + 2))) ?_ ?_ ?_
  · filter_upwards with n
    unfold abelBoundary
    positivity
  · filter_upwards with n
    unfold abelBoundary
    norm_num [Nat.cast_add, add_assoc]
    have hlog : 0 ≤ Real.log ((n : ℝ) + 2) := Real.log_nonneg (by linarith)
    calc
      2 * Real.log ((n : ℝ) + 2) / ((n : ℝ) + 3) ≤
          2 * Real.log ((n : ℝ) + 2) / ((n : ℝ) + 2) := by gcongr <;> norm_num
      _ = 2 * (Real.log ((n : ℝ) + 2) / ((n : ℝ) + 2)) := by ring
  · simpa using hmajor

theorem hasSum_abelBoundary_diff :
    HasSum (fun j : ℕ => abelBoundary j - abelBoundary (j + 1))
      ((2 / 3 : ℝ) * Real.log 2) := by
  have hw : Summable (fun j : ℕ => geometricLogWeight (j + 2)) :=
    (summable_nat_add_iff 2).mpr summable_geometricLogWeight
  have hd : Summable (fun j : ℕ => abelBoundary j - abelBoundary (j + 1)) := by
    have := hw.sub summable_abelShiftTerm
    exact this.congr (fun j => by rw [geometric_weight_shift_abel]; ring)
  rw [hd.hasSum_iff_tendsto_nat]
  simp_rw [sum_range_abelBoundary_diff]
  have hlim : Filter.Tendsto (fun n : ℕ => abelBoundary 0 - abelBoundary n)
      Filter.atTop (nhds (abelBoundary 0 - 0)) :=
    tendsto_const_nhds.sub tendsto_abelBoundary_zero
  convert hlim using 1 <;> simp [abelBoundary] <;> ring

/-- Exact Abel reindexing identity, including all endpoint terms. -/
theorem geometricLogSeries_eq_abel :
    geometricLogSeries = (2 / 3 : ℝ) * Real.log 2 + ∑' j : ℕ, abelShiftTerm j := by
  have hw : Summable (fun j : ℕ => geometricLogWeight (j + 2)) :=
    (summable_nat_add_iff 2).mpr summable_geometricLogWeight
  have hd := hasSum_abelBoundary_diff.summable
  have hshift := summable_geometricLogWeight.sum_add_tsum_nat_add 2
  have hzero : ∑ k ∈ Finset.range 2, geometricLogWeight k = 0 := by
    norm_num [Finset.sum_range_succ, geometricLogWeight]
  unfold geometricLogSeries
  rw [hzero, zero_add] at hshift
  rw [← hshift]
  calc
    (∑' j : ℕ, geometricLogWeight (j + 2)) =
        ∑' j : ℕ, ((abelBoundary j - abelBoundary (j + 1)) + abelShiftTerm j) :=
      tsum_congr geometric_weight_shift_abel
    _ = (∑' j : ℕ, (abelBoundary j - abelBoundary (j + 1))) +
          ∑' j : ℕ, abelShiftTerm j := hd.tsum_add summable_abelShiftTerm
    _ = (2 / 3 : ℝ) * Real.log 2 + ∑' j : ℕ, abelShiftTerm j := by
      rw [hasSum_abelBoundary_diff.tsum_eq]

/-- Final strict constant certificate required by the counting theorem. -/
theorem geometricLogSeries_lt_log_seventeen_div_five :
    geometricLogSeries < Real.log ((17 : ℝ) / 5) := by
  rw [geometricLogSeries_eq_abel]
  have hsplit := summable_abelShiftTerm.sum_add_tsum_nat_add 19
  calc
    (2 / 3 : ℝ) * Real.log 2 + ∑' j : ℕ, abelShiftTerm j =
        (2 / 3 : ℝ) * Real.log 2 +
          (∑ j ∈ Finset.range 19, abelShiftTerm j) +
            ∑' j : ℕ, abelShiftTerm (j + 19) := by linarith
    _ ≤ (2 / 3 : ℝ) * Real.log 2 +
          (∑ j ∈ Finset.range 19, abelShiftTerm j) + 1 / 10 := by
        gcongr
        exact abel_tail_le_one_tenth
    _ < 61 / 50 := abel_head_plus_tail_budget_lt_sixty_one_div_fifty
    _ < Real.log ((17 : ℝ) / 5) := sixty_one_div_fifty_lt_log_seventeen_div_five

/-- The real Tonelli exchange is now unconditional, and its exact value obeys
the certified `17/5` logarithmic threshold. -/
theorem integral_tsum_geometric_log_term_lt_log_seventeen_div_five :
    (∫ x : ℝ in Set.Ioc (0 : ℝ) 1, ∑' k : ℕ, geometricLogTerm k x) <
      Real.log ((17 : ℝ) / 5) := by
  rw [integral_tsum_geometric_log_term_of_summable summable_geometricLogWeight]
  exact geometricLogSeries_lt_log_seventeen_div_five

end StableMatchingsE2E
