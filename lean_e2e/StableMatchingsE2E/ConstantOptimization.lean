import StableMatchingsE2E.ConstantCertificate

open scoped BigOperators Topology

open Filter Finset

namespace StableMatchingsE2E

/-- A sharper exact rational upper certificate for `log 2`. -/
theorem log_two_lt_693148_div_million :
    Real.log 2 < (693148 : ℝ) / 1000000 := by
  have h := Real.log_div_le_sum_range_add
    (x := (1 : ℝ) / 3) (by norm_num) (by norm_num) 7
  norm_num [Finset.sum_range_succ] at h
  nlinarith

/-- A seven-power atanh upper bound specialized to `log (1 + 1/m)`.
All quantities on the right are rational when `m` is a natural number. -/
theorem log_one_add_inv_le_atanh7 (m : ℕ) (hm : 1 ≤ m) :
    Real.log (1 + 1 / (m : ℝ)) ≤
      2 * ((1 / ((2 * m + 1 : ℕ) : ℝ)) +
        (1 / ((2 * m + 1 : ℕ) : ℝ)) ^ 3 / 3 +
        (1 / ((2 * m + 1 : ℕ) : ℝ)) ^ 5 / 5 +
        (1 / ((2 * m + 1 : ℕ) : ℝ)) ^ 7 /
          (1 - (1 / ((2 * m + 1 : ℕ) : ℝ)) ^ 2)) := by
  let x : ℝ := 1 / ((2 * m + 1 : ℕ) : ℝ)
  have hx0 : 0 ≤ x := by dsimp [x]; positivity
  have hx1 : x < 1 := by
    dsimp [x]
    rw [div_lt_one]
    · norm_num
      omega
    · positivity
  have h := Real.log_div_le_sum_range_add hx0 hx1 3
  have hratio : (1 + x) / (1 - x) = 1 + 1 / (m : ℝ) := by
    dsimp [x]
    push_cast
    field_simp [show (m : ℝ) ≠ 0 by positivity]
    ring
  rw [hratio] at h
  dsimp [x] at h
  norm_num [Finset.sum_range_succ] at h ⊢
  linarith

/-- Rational majorant for a finite Abel head, using the certified atanh bound. -/
noncomputable def abelShiftUpper7 (j : ℕ) : ℝ :=
  let x : ℝ := 1 / ((2 * (j + 2) + 1 : ℕ) : ℝ)
  (2 / (((j + 4 : ℕ) : ℝ))) *
    (2 * (x + x ^ 3 / 3 + x ^ 5 / 5 + x ^ 7 / (1 - x ^ 2)))

lemma abelShiftTerm_le_upper7 (j : ℕ) :
    abelShiftTerm j ≤ abelShiftUpper7 j := by
  have hlog := log_one_add_inv_le_atanh7 (j + 2) (by omega)
  unfold abelShiftTerm abelShiftUpper7
  dsimp only
  calc
    2 * Real.log (1 + 1 / (((j + 2 : ℕ) : ℝ))) / (((j + 4 : ℕ) : ℝ)) =
        (2 / (((j + 4 : ℕ) : ℝ))) *
          Real.log (1 + 1 / (((j + 2 : ℕ) : ℝ))) := by ring
    _ ≤ (2 / (((j + 4 : ℕ) : ℝ))) *
          (2 * ((1 / ((2 * (j + 2) + 1 : ℕ) : ℝ)) +
            (1 / ((2 * (j + 2) + 1 : ℕ) : ℝ)) ^ 3 / 3 +
            (1 / ((2 * (j + 2) + 1 : ℕ) : ℝ)) ^ 5 / 5 +
            (1 / ((2 * (j + 2) + 1 : ℕ) : ℝ)) ^ 7 /
              (1 - (1 / ((2 * (j + 2) + 1 : ℕ) : ℝ)) ^ 2))) := by
        exact mul_le_mul_of_nonneg_left hlog (by positivity)

/-- Exact telescoping majorant for the Abel tail beginning at index `120`. -/
noncomputable def tailTelescoper120 (j : ℕ) : ℝ :=
  2 * (1 / (((j + 121 : ℕ) : ℝ)) - 1 / (((j + 122 : ℕ) : ℝ)))

lemma tailTelescoper120_nonneg (j : ℕ) : 0 ≤ tailTelescoper120 j := by
  unfold tailTelescoper120
  have h : (0 : ℝ) < (j : ℝ) + 121 := by positivity
  have h' : (j : ℝ) + 121 ≤ (j : ℝ) + 122 := by linarith
  norm_num [Nat.cast_add, add_assoc]
  simpa only [one_div] using one_div_le_one_div_of_le h h'

lemma sum_range_tailTelescoper120 (n : ℕ) :
    ∑ j ∈ Finset.range n, tailTelescoper120 j =
      2 * (1 / 121 - 1 / (((n + 121 : ℕ) : ℝ))) := by
  induction n with
  | zero => norm_num [tailTelescoper120]
  | succ n ih =>
      rw [Finset.sum_range_succ, ih]
      unfold tailTelescoper120
      push_cast
      field_simp
      ring

theorem hasSum_tailTelescoper120 : HasSum tailTelescoper120 (2 / 121 : ℝ) := by
  rw [hasSum_iff_tendsto_nat_of_nonneg tailTelescoper120_nonneg]
  simp_rw [sum_range_tailTelescoper120]
  have htop : Filter.Tendsto (fun n : ℕ => (n : ℝ) + 121)
      Filter.atTop Filter.atTop :=
    tendsto_atTop_add_const_right Filter.atTop 121 tendsto_natCast_atTop_atTop
  have hinv : Filter.Tendsto (fun n : ℕ => 1 / ((n : ℝ) + 121))
      Filter.atTop (nhds 0) := by
    simpa only [one_div, Function.comp_def] using tendsto_inv_atTop_zero.comp htop
  have hlim : Filter.Tendsto
      (fun n : ℕ => 2 * (1 / 121 - 1 / ((n : ℝ) + 121))) Filter.atTop
      (nhds (2 * (1 / 121 - 0))) := (tendsto_const_nhds.sub hinv).const_mul 2
  convert hlim using 1 <;> norm_num [Nat.cast_add]

lemma abel_tail_pointwise120 (j : ℕ) :
    abelShiftTerm (j + 120) ≤ tailTelescoper120 j := by
  have hlog : Real.log (1 + 1 / (((j + 122 : ℕ) : ℝ))) ≤
      1 / (((j + 122 : ℕ) : ℝ)) := by
    have := Real.log_le_sub_one_of_pos
      (show (0 : ℝ) < 1 + 1 / (((j + 122 : ℕ) : ℝ)) by positivity)
    linarith
  unfold abelShiftTerm tailTelescoper120
  norm_num [Nat.cast_add, add_assoc] at hlog ⊢
  calc
    2 * Real.log (1 + ((j : ℝ) + 122)⁻¹) / ((j : ℝ) + 124) =
        (2 / ((j : ℝ) + 124)) * Real.log (1 + ((j : ℝ) + 122)⁻¹) := by ring
    _ ≤ (2 / ((j : ℝ) + 124)) * ((j : ℝ) + 122)⁻¹ := by gcongr
    _ ≤ 2 / ((j : ℝ) + 122) ^ 2 := by
      rw [le_div_iff₀ (by positivity : (0 : ℝ) < ((j : ℝ) + 122) ^ 2)]
      field_simp
      nlinarith
    _ ≤ 2 * (((j : ℝ) + 121)⁻¹ - ((j : ℝ) + 122)⁻¹) := by
      rw [div_le_iff₀ (by positivity : (0 : ℝ) < ((j : ℝ) + 122) ^ 2)]
      field_simp
      nlinarith

theorem abel_tail_le_two_div_121 :
    (∑' j : ℕ, abelShiftTerm (j + 120)) ≤ (2 / 121 : ℝ) := by
  have htel : Summable tailTelescoper120 := hasSum_tailTelescoper120.summable
  have hab : Summable (fun j : ℕ => abelShiftTerm (j + 120)) :=
    htel.of_nonneg_of_le (fun j => abelShiftTerm_nonneg _) abel_tail_pointwise120
  calc
    (∑' j : ℕ, abelShiftTerm (j + 120)) ≤ ∑' j : ℕ, tailTelescoper120 j :=
      Summable.tsum_le_tsum abel_tail_pointwise120 hab htel
    _ = 2 / 121 := hasSum_tailTelescoper120.tsum_eq

/-- The sharpened finite rational computation. -/
theorem abel_head120_plus_tail_lt_12039_div_10000 :
    (2 / 3 : ℝ) * Real.log 2 +
        (∑ j ∈ Finset.range 120, abelShiftTerm j) + 2 / 121 < 12039 / 10000 := by
  have hsum :
      (∑ j ∈ Finset.range 120, abelShiftTerm j) ≤
        ∑ j ∈ Finset.range 120, abelShiftUpper7 j := by
    exact Finset.sum_le_sum fun j _ => abelShiftTerm_le_upper7 j
  calc
    (2 / 3 : ℝ) * Real.log 2 +
          (∑ j ∈ Finset.range 120, abelShiftTerm j) + 2 / 121 ≤
        (2 / 3 : ℝ) * Real.log 2 +
          (∑ j ∈ Finset.range 120, abelShiftUpper7 j) + 2 / 121 := by
            gcongr
    _ < (2 / 3 : ℝ) * (693148 / 1000000) +
          (∑ j ∈ Finset.range 120, abelShiftUpper7 j) + 2 / 121 := by
            gcongr <;> exact log_two_lt_693148_div_million
    _ < 12039 / 10000 := by
      norm_num [abelShiftUpper7, Finset.sum_range_succ]

/-- Exact rational lower certificate for `log (10/3)`. -/
theorem one_point_2039_lt_log_ten_div_three :
    (12039 : ℝ) / 10000 < Real.log ((10 : ℝ) / 3) := by
  have h := Real.sum_range_le_log_div
    (x := (7 : ℝ) / 13) (by norm_num) (by norm_num) 6
  norm_num [Finset.sum_range_succ] at h
  nlinarith

/-- Kernel-checked constant optimization to the method's clean `10/3` target. -/
theorem geometricLogSeries_lt_log_ten_div_three :
    geometricLogSeries < Real.log ((10 : ℝ) / 3) := by
  rw [geometricLogSeries_eq_abel]
  have hsplit := summable_abelShiftTerm.sum_add_tsum_nat_add 120
  calc
    (2 / 3 : ℝ) * Real.log 2 + ∑' j : ℕ, abelShiftTerm j =
        (2 / 3 : ℝ) * Real.log 2 +
          (∑ j ∈ Finset.range 120, abelShiftTerm j) +
            ∑' j : ℕ, abelShiftTerm (j + 120) := by linarith
    _ ≤ (2 / 3 : ℝ) * Real.log 2 +
          (∑ j ∈ Finset.range 120, abelShiftTerm j) + 2 / 121 := by
        gcongr
        exact abel_tail_le_two_div_121
    _ < 12039 / 10000 := abel_head120_plus_tail_lt_12039_div_10000
    _ < Real.log ((10 : ℝ) / 3) := one_point_2039_lt_log_ten_div_three

/-! ## Second pass: a near-method-optimal clean rational constant

The preceding theorem is the minimal certificate.  The next certificate loses
less than `10⁻⁶` in the logarithm: one extra atanh term handles the finite
head, while a three-term telescoping potential handles the infinite tail.
-/

theorem log_two_lt_6931472_div_ten_million :
    Real.log 2 < (6931472 : ℝ) / 10000000 := by
  have h := Real.log_div_le_sum_range_add
    (x := (1 : ℝ) / 3) (by norm_num) (by norm_num) 8
  norm_num [Finset.sum_range_succ] at h
  nlinarith

theorem log_one_add_inv_le_atanh9 (m : ℕ) (hm : 1 ≤ m) :
    Real.log (1 + 1 / (m : ℝ)) ≤
      2 * ((1 / ((2 * m + 1 : ℕ) : ℝ)) +
        (1 / ((2 * m + 1 : ℕ) : ℝ)) ^ 3 / 3 +
        (1 / ((2 * m + 1 : ℕ) : ℝ)) ^ 5 / 5 +
        (1 / ((2 * m + 1 : ℕ) : ℝ)) ^ 7 / 7 +
        (1 / ((2 * m + 1 : ℕ) : ℝ)) ^ 9 /
          (1 - (1 / ((2 * m + 1 : ℕ) : ℝ)) ^ 2)) := by
  let x : ℝ := 1 / ((2 * m + 1 : ℕ) : ℝ)
  have hx0 : 0 ≤ x := by dsimp [x]; positivity
  have hx1 : x < 1 := by
    dsimp [x]
    rw [div_lt_one]
    · norm_num
      omega
    · positivity
  have h := Real.log_div_le_sum_range_add hx0 hx1 4
  have hratio : (1 + x) / (1 - x) = 1 + 1 / (m : ℝ) := by
    dsimp [x]
    push_cast
    field_simp [show (m : ℝ) ≠ 0 by positivity]
    ring
  rw [hratio] at h
  dsimp [x] at h
  norm_num [Finset.sum_range_succ] at h ⊢
  linarith

noncomputable def abelShiftUpper9 (j : ℕ) : ℝ :=
  let x : ℝ := 1 / ((2 * (j + 2) + 1 : ℕ) : ℝ)
  (2 / (((j + 4 : ℕ) : ℝ))) *
    (2 * (x + x ^ 3 / 3 + x ^ 5 / 5 + x ^ 7 / 7 + x ^ 9 / (1 - x ^ 2)))

lemma abelShiftTerm_le_upper9 (j : ℕ) :
    abelShiftTerm j ≤ abelShiftUpper9 j := by
  have hlog := log_one_add_inv_le_atanh9 (j + 2) (by omega)
  unfold abelShiftTerm abelShiftUpper9
  dsimp only
  rw [show 2 * Real.log (1 + 1 / (((j + 2 : ℕ) : ℝ))) /
      (((j + 4 : ℕ) : ℝ)) =
        (2 / (((j + 4 : ℕ) : ℝ))) *
          Real.log (1 + 1 / (((j + 2 : ℕ) : ℝ))) by ring]
  exact mul_le_mul_of_nonneg_left hlog (by positivity)

/-- Potential whose discrete derivative majorizes the cubic logarithmic tail. -/
noncomputable def sharpTailPotential120 (j : ℕ) : ℝ :=
  let m : ℝ := (j : ℝ) + 122
  2 * m⁻¹ - (3 / 2) * (m ^ 2)⁻¹ + (25 / 18) * (m ^ 3)⁻¹

noncomputable def sharpTailTelescoper120 (j : ℕ) : ℝ :=
  sharpTailPotential120 j - sharpTailPotential120 (j + 1)

lemma sharpTailTelescoper120_nonneg (j : ℕ) :
    0 ≤ sharpTailTelescoper120 j := by
  unfold sharpTailTelescoper120 sharpTailPotential120
  dsimp only
  push_cast
  field_simp
  ring_nf
  positivity

lemma sum_range_sharpTailTelescoper120 (n : ℕ) :
    ∑ j ∈ Finset.range n, sharpTailTelescoper120 j =
      sharpTailPotential120 0 - sharpTailPotential120 n := by
  induction n with
  | zero => simp
  | succ n ih =>
      rw [Finset.sum_range_succ, ih]
      unfold sharpTailTelescoper120
      ring

lemma tendsto_sharpTailPotential120_zero :
    Filter.Tendsto sharpTailPotential120 Filter.atTop (nhds 0) := by
  change Filter.Tendsto
    (fun n : ℕ => 2 * ((n : ℝ) + 122)⁻¹ -
      (3 / 2) * (((n : ℝ) + 122) ^ 2)⁻¹ +
      (25 / 18) * (((n : ℝ) + 122) ^ 3)⁻¹)
    Filter.atTop (nhds 0)
  have htop : Filter.Tendsto (fun n : ℕ => (n : ℝ) + 122)
      Filter.atTop Filter.atTop :=
    tendsto_atTop_add_const_right Filter.atTop 122 tendsto_natCast_atTop_atTop
  have hinv : Filter.Tendsto (fun n : ℕ => 1 / ((n : ℝ) + 122))
      Filter.atTop (nhds 0) := by
    simpa only [one_div, Function.comp_def] using tendsto_inv_atTop_zero.comp htop
  have hlim := ((hinv.const_mul 2).sub ((hinv.pow 2).const_mul (3 / 2))).add
    ((hinv.pow 3).const_mul (25 / 18))
  simpa [Nat.cast_add] using hlim

theorem hasSum_sharpTailTelescoper120 :
    HasSum sharpTailTelescoper120 (sharpTailPotential120 0) := by
  rw [hasSum_iff_tendsto_nat_of_nonneg sharpTailTelescoper120_nonneg]
  simp_rw [sum_range_sharpTailTelescoper120]
  simpa using tendsto_const_nhds.sub tendsto_sharpTailPotential120_zero

lemma abel_tail_pointwise_sharp120 (j : ℕ) :
    abelShiftTerm (j + 120) ≤ sharpTailTelescoper120 j := by
  have hj : (0 : ℝ) ≤ (j : ℝ) := Nat.cast_nonneg j
  have hlog := log_one_add_le_cubic
    (t := 1 / (((j + 122 : ℕ) : ℝ))) (by positivity)
  unfold abelShiftTerm
  norm_num [Nat.cast_add, add_assoc] at hlog ⊢
  calc
    2 * Real.log (1 + ((j : ℝ) + 122)⁻¹) / ((j : ℝ) + 124) ≤
        (2 / ((j : ℝ) + 124)) *
          (((j : ℝ) + 122)⁻¹ - (((j : ℝ) + 122) ^ 2)⁻¹ / 2 +
            (((j : ℝ) + 122) ^ 3)⁻¹ / 3) := by
      rw [show 2 * Real.log (1 + ((j : ℝ) + 122)⁻¹) / ((j : ℝ) + 124) =
        (2 / ((j : ℝ) + 124)) * Real.log (1 + ((j : ℝ) + 122)⁻¹) by ring]
      exact mul_le_mul_of_nonneg_left hlog (by positivity)
    _ ≤ sharpTailTelescoper120 j := by
      unfold sharpTailTelescoper120 sharpTailPotential120
      dsimp only
      push_cast
      field_simp
      ring_nf
      nlinarith [hj]

theorem abel_tail_le_sharp120 :
    (∑' j : ℕ, abelShiftTerm (j + 120)) ≤ sharpTailPotential120 0 := by
  have htel : Summable sharpTailTelescoper120 := hasSum_sharpTailTelescoper120.summable
  have hab : Summable (fun j : ℕ => abelShiftTerm (j + 120)) :=
    htel.of_nonneg_of_le (fun j => abelShiftTerm_nonneg _) abel_tail_pointwise_sharp120
  calc
    (∑' j : ℕ, abelShiftTerm (j + 120)) ≤
        ∑' j : ℕ, sharpTailTelescoper120 j :=
      Summable.tsum_le_tsum abel_tail_pointwise_sharp120 hab htel
    _ = sharpTailPotential120 0 := hasSum_sharpTailTelescoper120.tsum_eq

theorem abel_head120_plus_sharp_tail_lt_120357_div_100000 :
    (2 / 3 : ℝ) * Real.log 2 +
        (∑ j ∈ Finset.range 120, abelShiftTerm j) + sharpTailPotential120 0 <
      120357 / 100000 := by
  have hsum :
      (∑ j ∈ Finset.range 120, abelShiftTerm j) ≤
        ∑ j ∈ Finset.range 120, abelShiftUpper9 j :=
    Finset.sum_le_sum fun j _ => abelShiftTerm_le_upper9 j
  calc
    (2 / 3 : ℝ) * Real.log 2 +
          (∑ j ∈ Finset.range 120, abelShiftTerm j) + sharpTailPotential120 0 ≤
        (2 / 3 : ℝ) * Real.log 2 +
          (∑ j ∈ Finset.range 120, abelShiftUpper9 j) + sharpTailPotential120 0 := by
            gcongr
    _ < (2 / 3 : ℝ) * (6931472 / 10000000) +
          (∑ j ∈ Finset.range 120, abelShiftUpper9 j) + sharpTailPotential120 0 := by
            gcongr <;> exact log_two_lt_6931472_div_ten_million
    _ < 120357 / 100000 := by
      norm_num [abelShiftUpper9, sharpTailPotential120, Finset.sum_range_succ]

theorem one_point_20357_lt_log_833_div_250 :
    (120357 : ℝ) / 100000 < Real.log ((833 : ℝ) / 250) := by
  have h := Real.sum_range_le_log_div
    (x := (583 : ℝ) / 1083) (by norm_num) (by norm_num) 10
  norm_num [Finset.sum_range_succ] at h
  nlinarith

/-- A clean constant within about `2.6·10⁻⁵` of the method's numerical limit. -/
theorem geometricLogSeries_lt_log_833_div_250 :
    geometricLogSeries < Real.log ((833 : ℝ) / 250) := by
  rw [geometricLogSeries_eq_abel]
  have hsplit := summable_abelShiftTerm.sum_add_tsum_nat_add 120
  calc
    (2 / 3 : ℝ) * Real.log 2 + ∑' j : ℕ, abelShiftTerm j =
        (2 / 3 : ℝ) * Real.log 2 +
          (∑ j ∈ Finset.range 120, abelShiftTerm j) +
            ∑' j : ℕ, abelShiftTerm (j + 120) := by linarith
    _ ≤ (2 / 3 : ℝ) * Real.log 2 +
          (∑ j ∈ Finset.range 120, abelShiftTerm j) + sharpTailPotential120 0 := by
        gcongr
        exact abel_tail_le_sharp120
    _ < 120357 / 100000 := abel_head120_plus_sharp_tail_lt_120357_div_100000
    _ < Real.log ((833 : ℝ) / 250) := one_point_20357_lt_log_833_div_250

/-! ## Production six-decimal certificate -/

noncomputable def atanhUpper14 (x : ℝ) : ℝ :=
  2 * ((∑ i ∈ Finset.range 14, x ^ (2 * i + 1) / (2 * i + 1)) +
    x ^ 29 / (1 - x ^ 2))

theorem log_one_add_inv_le_atanhUpper14 (m : ℕ) (hm : 1 ≤ m) :
    Real.log (1 + 1 / (m : ℝ)) ≤
      atanhUpper14 (1 / ((2 * m + 1 : ℕ) : ℝ)) := by
  let x : ℝ := 1 / ((2 * m + 1 : ℕ) : ℝ)
  have hx0 : 0 ≤ x := by dsimp [x]; positivity
  have hx1 : x < 1 := by
    dsimp [x]
    rw [div_lt_one]
    · norm_num
      omega
    · positivity
  have h := Real.log_div_le_sum_range_add hx0 hx1 14
  have hratio : (1 + x) / (1 - x) = 1 + 1 / (m : ℝ) := by
    dsimp [x]
    push_cast
    field_simp [show (m : ℝ) ≠ 0 by positivity]
    ring
  rw [hratio] at h
  change Real.log (1 + 1 / (m : ℝ)) ≤ atanhUpper14 x
  unfold atanhUpper14
  norm_num at h ⊢
  linarith

noncomputable def abelShiftUpper14 (j : ℕ) : ℝ :=
  (2 / (((j + 4 : ℕ) : ℝ))) *
    atanhUpper14 (1 / ((2 * (j + 2) + 1 : ℕ) : ℝ))

lemma abelShiftTerm_le_upper14 (j : ℕ) :
    abelShiftTerm j ≤ abelShiftUpper14 j := by
  have hlog := log_one_add_inv_le_atanhUpper14 (j + 2) (by omega)
  unfold abelShiftTerm abelShiftUpper14
  rw [show 2 * Real.log (1 + 1 / (((j + 2 : ℕ) : ℝ))) /
      (((j + 4 : ℕ) : ℝ)) =
        (2 / (((j + 4 : ℕ) : ℝ))) *
          Real.log (1 + 1 / (((j + 2 : ℕ) : ℝ))) by ring]
  exact mul_le_mul_of_nonneg_left hlog (by positivity)

theorem hasSum_sharpTailTelescoper_from_40 :
    HasSum (fun j : ℕ => sharpTailTelescoper120 (j + 40))
      (sharpTailPotential120 40) := by
  have hs0 := hasSum_sharpTailTelescoper120.summable
  have hs : Summable (fun j : ℕ => sharpTailTelescoper120 (j + 40)) :=
    (summable_nat_add_iff 40).mpr hs0
  have hsplit := hs0.sum_add_tsum_nat_add 40
  have hprefix := sum_range_sharpTailTelescoper120 40
  have htsum : (∑' j : ℕ, sharpTailTelescoper120 (j + 40)) =
      sharpTailPotential120 40 := by
    rw [hasSum_sharpTailTelescoper120.tsum_eq, hprefix] at hsplit
    linarith
  rw [← htsum]
  exact hs.hasSum

lemma abel_tail_pointwise_sharp160 (j : ℕ) :
    abelShiftTerm (j + 160) ≤ sharpTailTelescoper120 (j + 40) := by
  simpa [Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using
    abel_tail_pointwise_sharp120 (j + 40)

theorem abel_tail_le_sharp160 :
    (∑' j : ℕ, abelShiftTerm (j + 160)) ≤ sharpTailPotential120 40 := by
  have htel : Summable (fun j : ℕ => sharpTailTelescoper120 (j + 40)) :=
    hasSum_sharpTailTelescoper_from_40.summable
  have hab : Summable (fun j : ℕ => abelShiftTerm (j + 160)) :=
    htel.of_nonneg_of_le (fun j => abelShiftTerm_nonneg _) abel_tail_pointwise_sharp160
  calc
    (∑' j : ℕ, abelShiftTerm (j + 160)) ≤
        ∑' j : ℕ, sharpTailTelescoper120 (j + 40) :=
      Summable.tsum_le_tsum abel_tail_pointwise_sharp160 hab htel
    _ = sharpTailPotential120 40 := hasSum_sharpTailTelescoper_from_40.tsum_eq

theorem abel_head160_plus_sharp_tail_lt_120356492_div_100000000 :
    (2 / 3 : ℝ) * Real.log 2 +
        (∑ j ∈ Finset.range 160, abelShiftTerm j) + sharpTailPotential120 40 <
      120356492 / 100000000 := by
  have hsum :
      (∑ j ∈ Finset.range 160, abelShiftTerm j) ≤
        ∑ j ∈ Finset.range 160, abelShiftUpper14 j :=
    Finset.sum_le_sum fun j _ => abelShiftTerm_le_upper14 j
  calc
    (2 / 3 : ℝ) * Real.log 2 +
          (∑ j ∈ Finset.range 160, abelShiftTerm j) + sharpTailPotential120 40 ≤
        (2 / 3 : ℝ) * atanhUpper14 (1 / 3) +
          (∑ j ∈ Finset.range 160, abelShiftUpper14 j) +
            sharpTailPotential120 40 := by
      gcongr
      have htwo := log_one_add_inv_le_atanhUpper14 1 (by norm_num)
      norm_num at htwo
      exact htwo
    _ < 120356492 / 100000000 := by
      norm_num [abelShiftUpper14, atanhUpper14, sharpTailPotential120,
        Finset.sum_range_succ]

theorem one_point_20356492_lt_log_1665987_div_500000 :
    (120356492 : ℝ) / 100000000 <
      Real.log ((1665987 : ℝ) / 500000) := by
  have h := Real.sum_range_le_log_div
    (x := (1165987 : ℝ) / 2165987) (by norm_num) (by norm_num) 16
  norm_num [Finset.sum_range_succ] at h
  nlinarith

/-- Six-decimal rounding-up of the natural limit of the current entropy chain. -/
theorem geometricLogSeries_lt_log_1665987_div_500000 :
    geometricLogSeries < Real.log ((1665987 : ℝ) / 500000) := by
  rw [geometricLogSeries_eq_abel]
  have hsplit := summable_abelShiftTerm.sum_add_tsum_nat_add 160
  calc
    (2 / 3 : ℝ) * Real.log 2 + ∑' j : ℕ, abelShiftTerm j =
        (2 / 3 : ℝ) * Real.log 2 +
          (∑ j ∈ Finset.range 160, abelShiftTerm j) +
            ∑' j : ℕ, abelShiftTerm (j + 160) := by linarith
    _ ≤ (2 / 3 : ℝ) * Real.log 2 +
          (∑ j ∈ Finset.range 160, abelShiftTerm j) + sharpTailPotential120 40 := by
        gcongr
        exact abel_tail_le_sharp160
    _ < 120356492 / 100000000 :=
      abel_head160_plus_sharp_tail_lt_120356492_div_100000000
    _ < Real.log ((1665987 : ℝ) / 500000) :=
      one_point_20356492_lt_log_1665987_div_500000

end StableMatchingsE2E
