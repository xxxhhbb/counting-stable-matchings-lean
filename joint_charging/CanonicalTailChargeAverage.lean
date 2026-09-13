import «CanonicalGlobalSlack»

/-!
# First exponential-tail improvement beyond the half-mass charge bound

This file keeps the canonical deletion double count and all local payments
unchanged.  It spends two bits, rather than one bit, of the certified
`alpha = 3/80` entropy margin.  Hence the low-charge family has mass at most
one quarter, and the normalized average charge is strictly larger than
`9n/320` instead of `3n/160`.
-/

namespace StableMatchingsJointCharging

open StableMatchingsE2E

noncomputable section

theorem deletion_double_count_quarter
    (bad total Q r : ℕ) (hQ : 0 < Q)
    (hcount : bad * 2 ^ r ≤ total * Q)
    (hquarter : 4 * Q ≤ 2 ^ r) :
    4 * bad ≤ total := by
  have hmul : (4 * bad) * Q ≤ total * Q := by
    calc
      (4 * bad) * Q = bad * (4 * Q) := by
        simp [Nat.mul_assoc, Nat.mul_comm, Nat.mul_left_comm]
      _ ≤ bad * 2 ^ r := Nat.mul_le_mul_left bad hquarter
      _ ≤ total * Q := hcount
  exact le_of_mul_le_mul_right hmul hQ

theorem normalized_average_ge_three_quarters_threshold
    (M bad r total : ℕ) (hM : 0 < M)
    (hbad : 4 * bad ≤ M)
    (hcharge : (M - bad) * r ≤ total) :
    (3 : ℝ) * (r : ℝ) / 4 ≤ (M : ℝ)⁻¹ * (total : ℝ) := by
  have hbadM : bad ≤ M := by omega
  have hMreal : (0 : ℝ) < (M : ℝ) := by exact_mod_cast hM
  have hbadReal : (4 : ℝ) * (bad : ℝ) ≤ (M : ℝ) := by
    exact_mod_cast hbad
  have hchargeReal :
      ((M : ℝ) - (bad : ℝ)) * (r : ℝ) ≤ (total : ℝ) := by
    rw [← Nat.cast_sub hbadM, ← Nat.cast_mul]
    exact_mod_cast hcharge
  rw [inv_mul_eq_div]
  apply (le_div_iff₀ hMreal).2
  have hr : 0 ≤ (r : ℝ) := by positivity
  nlinarith

theorem normalized_average_gt_nine_n_over_320
    (n M bad total : ℕ) (hM : 0 < M)
    (hbad : 4 * bad ≤ M)
    (hcharge :
      (M - bad) * ((3 * n) / 80 + 1) ≤ total) :
    (9 : ℝ) * (n : ℝ) / 320 < (M : ℝ)⁻¹ * (total : ℝ) := by
  have havg := normalized_average_ge_three_quarters_threshold
    M bad ((3 * n) / 80 + 1) total hM hbad hcharge
  have hfloor := three_n_div_eighty_lt_floor_succ n
  nlinarith

/-- Four times the optimized boundary budget fits inside the guaranteed
frontier.  The threshold `12001` pays for two probability bits and the one
unit integer-rounding loss. -/
theorem optimized_boundary_budget_quarter {n : Nat} (hn : 12001 ≤ n) :
    4 * (2 ^ (n / 4) *
        (∑ i ∈ Finset.range ((3 * n) / 80 + 1), n.choose i)) ≤
      2 ^ ((n - (3 * n) / 80) / 2) := by
  let k := (3 * n) / 80
  let a := n / 4
  let r := (n - k) / 2
  let B := ∑ i ∈ Finset.range (k + 1), n.choose i
  have hk : 80 * k ≤ 3 * n := by
    dsimp [k]
    omega
  have hprefix :=
    choose_prefix_le_exp_binEntropy_three_eightieths
      (n := n) (k := k) hk
  have hmargin := deletion_entropy_margin_three_eightieths_quantitative
  have hlog : 0 < Real.log 2 := Real.log_pos (by norm_num)
  have ha : (a : ℝ) ≤ (n : ℝ) / 4 := by
    dsimp [a]
    have hnat : 4 * (n / 4) ≤ n := by omega
    have hcast : ((4 * (n / 4) : Nat) : ℝ) ≤ (n : ℝ) := by
      exact_mod_cast hnat
    norm_num only [Nat.cast_mul, Nat.cast_ofNat] at hcast
    nlinarith
  have hkreal : (k : ℝ) ≤ (3 : ℝ) * (n : ℝ) / 80 := by
    have hcast : ((80 * k : Nat) : ℝ) ≤ ((3 * n : Nat) : ℝ) := by
      exact_mod_cast hk
    push_cast at hcast
    nlinarith
  have hr : ((n : ℝ) - (k : ℝ)) / 2 - 1 < (r : ℝ) := by
    have hkn : k ≤ n := by omega
    have hnat : n - k < 2 * ((n - k) / 2 + 1) := by omega
    have hcast : ((n - k : Nat) : ℝ) <
        (2 * ((n - k) / 2 + 1) : Nat) := by exact_mod_cast hnat
    rw [Nat.cast_sub hkn] at hcast
    dsimp [r]
    push_cast at hcast
    nlinarith
  have hnreal : (12001 : ℝ) ≤ (n : ℝ) := by exact_mod_cast hn
  have hexponent :
      2 * Real.log 2 + (a : ℝ) * Real.log 2 +
          (n : ℝ) * Real.binEntropy ((3 : ℝ) / 80) <
        (r : ℝ) * Real.log 2 := by
    have hmarginN :
        (n : ℝ) * Real.binEntropy ((3 : ℝ) / 80) <
          (n : ℝ) * (((1 : ℝ) / 4 - ((3 : ℝ) / 80) / 2) *
            Real.log 2 - ((1 : ℝ) / 4000) * Real.log 2) := by
      have hnNat : 0 < n := by omega
      have hnpos : (0 : ℝ) < (n : ℝ) := by exact_mod_cast hnNat
      nlinarith
    nlinarith
  have hB : (B : ℝ) ≤
      Real.exp ((n : ℝ) * Real.binEntropy ((3 : ℝ) / 80)) := by
    simpa [B] using hprefix
  have htwoA : ((2 ^ a : Nat) : ℝ) =
      Real.exp ((a : ℝ) * Real.log 2) := by
    rw [Real.exp_nat_mul, Real.exp_log (by norm_num)]
    norm_num
  have htwoR : ((2 ^ r : Nat) : ℝ) =
      Real.exp ((r : ℝ) * Real.log 2) := by
    rw [Real.exp_nat_mul, Real.exp_log (by norm_num)]
    norm_num
  have hfour : (4 : ℝ) = Real.exp ((2 : ℝ) * Real.log 2) := by
    rw [show (2 : ℝ) = (2 : Nat) by norm_num,
      Real.exp_nat_mul, Real.exp_log (by norm_num)]
    norm_num
  have hreal : ((4 * (2 ^ a * B) : Nat) : ℝ) < (2 ^ r : Nat) := by
    rw [Nat.cast_mul, Nat.cast_ofNat, Nat.cast_mul, htwoA, htwoR, hfour]
    calc
      Real.exp ((2 : ℝ) * Real.log 2) *
          (Real.exp ((a : ℝ) * Real.log 2) * (B : ℝ)) ≤
          Real.exp ((2 : ℝ) * Real.log 2) *
            (Real.exp ((a : ℝ) * Real.log 2) *
              Real.exp ((n : ℝ) *
                Real.binEntropy ((3 : ℝ) / 80))) := by
        gcongr
      _ = Real.exp (2 * Real.log 2 + (a : ℝ) * Real.log 2 +
          (n : ℝ) * Real.binEntropy ((3 : ℝ) / 80)) := by
        rw [← Real.exp_add, ← Real.exp_add]
        congr 1
        ring
      _ < Real.exp ((r : ℝ) * Real.log 2) :=
        Real.exp_lt_exp.mpr hexponent
  have hnat : 4 * (2 ^ a * B) < 2 ^ r := by exact_mod_cast hreal
  dsimp [a, B, r, k] at hnat ⊢
  omega

theorem canonical_low_charge_quarter_optimized {n : Nat}
    (P : ProfileCode n) (hstable : (stableSet P).Nonempty)
    (hn : 12001 ≤ n) :
    4 * Nat.card (CanonicalLowChargeSource P hstable ((3 * n) / 80)) ≤
      Nat.card (CodedStable P) := by
  let k := (3 * n) / 80
  let Q := 2 ^ (n / 4) *
    (∑ i ∈ Finset.range (k + 1), n.choose i)
  have hQ : 0 < Q := by
    dsimp [Q]
    have hsum : 0 < ∑ i ∈ Finset.range (k + 1), n.choose i := by
      apply Finset.sum_pos'
      · intro i hi
        exact Nat.zero_le _
      · refine ⟨0, by simp, ?_⟩
        simp
    exact Nat.mul_pos (pow_pos (by omega) _) hsum
  apply deletion_double_count_quarter
    (Nat.card (CanonicalLowChargeSource P hstable k))
    (Nat.card (CodedStable P)) Q ((n - k) / 2) hQ
  · exact canonical_low_charge_double_count P hstable k
  · simpa [Q, k] using optimized_boundary_budget_quarter hn

theorem canonical_normalized_average_charge_gt_nine_n_over_320
    {n : Nat} (P : ProfileCode n)
    (hstable : (stableSet P).Nonempty) (hn : 12001 ≤ n) :
    (9 : ℝ) * (n : ℝ) / 320 <
      (Nat.card (CodedStable P) : ℝ)⁻¹ *
        (canonicalTotalCharge P hstable : ℝ) := by
  let mu := Classical.choose hstable
  have hmu : mu ∈ stableSet P := Classical.choose_spec hstable
  letI : Nonempty (CodedStable P) :=
    ⟨⟨mu, (mem_stableSet_iff P mu).1 hmu⟩⟩
  have hM : 0 < Nat.card (CodedStable P) := Nat.card_pos
  exact normalized_average_gt_nine_n_over_320 n
    (Nat.card (CodedStable P))
    (Nat.card (CanonicalLowChargeSource P hstable ((3 * n) / 80)))
    (canonicalTotalCharge P hstable) hM
    (canonical_low_charge_quarter_optimized P hstable hn)
    (canonical_good_sources_pay_threshold
      P hstable ((3 * n) / 80))

/-- First tail-improved joint slack: 3/4 of the `3/80` threshold times the
canonical local payment. -/
def quarterTailJointDelta : ℝ :=
  3 * Real.log ((3 : ℝ) / 2) / 3200

theorem quarterTailJointDelta_pos : 0 < quarterTailJointDelta := by
  unfold quarterTailJointDelta
  have := log_three_halves_pos
  positivity

theorem quarterTailJointDelta_le_averaged_joint_slack
    {n : Nat} {P : ProfileCode n} (hn : 12001 ≤ n)
    (D : StaticWindowData P) (hstable : (stableSet P).Nonempty) :
    (n : ℝ) * quarterTailJointDelta ≤
      averagedTargetGeometricSlack D + averagedTargetSupportWindowSlack D := by
  have hcharge := canonical_normalized_average_charge_gt_nine_n_over_320
    P hstable hn
  have hlocal := normalized_canonical_charge_payment_le_averaged_joint_slack
    (by omega) D hstable
  have hlog : 0 ≤ Real.log ((3 : ℝ) / 2) := (log_three_halves_pos).le
  unfold quarterTailJointDelta
  calc
    (n : ℝ) * (3 * Real.log ((3 : ℝ) / 2) / 3200) =
        Real.log ((3 : ℝ) / 2) / 30 *
          ((9 : ℝ) * (n : ℝ) / 320) := by ring
    _ ≤ Real.log ((3 : ℝ) / 2) / 30 *
        ((Nat.card (CodedStable P) : ℝ)⁻¹ *
          (canonicalTotalCharge P hstable : ℝ)) := by
      gcongr
    _ ≤ _ := hlocal

theorem quarterTailJointDelta_le_totalJointSlack
    {n : Nat} {P : ProfileCode n} (hn : 12001 ≤ n)
    (D : StaticWindowData P) (hstable : (stableSet P).Nonempty) :
    (n : ℝ) * quarterTailJointDelta ≤ totalJointSlack P :=
  (quarterTailJointDelta_le_averaged_joint_slack hn D hstable).trans
    (averaged_joint_target_slack_le_totalJointSlack D hstable)

theorem quarterTailJointDelta_le_geometricLogSeries :
    quarterTailJointDelta ≤ geometricLogSeries := by
  have hterm : geometricLogWeight 2 ≤ geometricLogSeries := by
    unfold geometricLogSeries
    exact summable_geometricLogWeight.le_tsum 2 fun j hj ↦
      geometricLogWeight_nonneg j
  have hlog : Real.log ((3 : ℝ) / 2) ≤ Real.log 2 :=
    Real.log_le_log (by norm_num) (by norm_num)
  have hlog0 : 0 ≤ Real.log ((3 : ℝ) / 2) :=
    (log_three_halves_pos).le
  have hlocal : quarterTailJointDelta ≤ geometricLogWeight 2 := by
    unfold quarterTailJointDelta geometricLogWeight
    norm_num
    nlinarith
  exact hlocal.trans hterm

theorem all_profiles_quarterTailJointSlack
    {n : Nat} (hn : 12001 ≤ n) (P : ProfileCode n) :
    (n : ℝ) * quarterTailJointDelta ≤ totalJointSlack P := by
  classical
  by_cases hz : stableCount P = 0
  · unfold totalJointSlack
    rw [hz]
    simp only [Nat.cast_zero, Real.log_zero, sub_zero]
    exact mul_le_mul_of_nonneg_left quarterTailJointDelta_le_geometricLogSeries
      (Nat.cast_nonneg n)
  · have hpositive : 0 < stableCount P := Nat.pos_of_ne_zero hz
    have hstable : (stableSet P).Nonempty := by
      apply Finset.card_pos.mp
      simpa [stableCount] using hpositive
    let D : StaticWindowData P := Classical.choice (exists_staticWindowData P)
    exact quarterTailJointDelta_le_totalJointSlack hn D hstable

theorem one_point_12032_lt_log_8327_div_2500 :
    (12032 : ℝ) / 10000 < Real.log ((8327 : ℝ) / 2500) := by
  have h := Real.sum_range_le_log_div
    (x := (5827 : ℝ) / 10827) (by norm_num) (by norm_num) 16
  norm_num [Finset.sum_range_succ] at h
  nlinarith

theorem geometricLogSeries_sub_quarterTailJointDelta_lt_log_8327_div_2500 :
    geometricLogSeries - quarterTailJointDelta <
      Real.log ((8327 : ℝ) / 2500) := by
  have hS := geometricLogSeries_lt_120356492_div_100000000
  have hd := log_three_halves_gt_4054_div_10000
  have hq := one_point_12032_lt_log_8327_div_2500
  unfold quarterTailJointDelta
  linarith

theorem stableCount_lt_8327_div_2500_pow
    {n : Nat} (hn : 12001 ≤ n) (P : ProfileCode n) :
    (stableCount P : ℝ) < ((8327 : ℝ) / 2500) ^ n := by
  have hjoint := all_profiles_quarterTailJointSlack hn P
  have hmain :=
    (jointSlack_linear_lower_iff_log_bound P quarterTailJointDelta).1 hjoint
  have hlog : Real.log (stableCount P) <
      (n : ℝ) * Real.log ((8327 : ℝ) / 2500) :=
    hmain.trans_lt
      (mul_lt_mul_of_pos_left
        geometricLogSeries_sub_quarterTailJointDelta_lt_log_8327_div_2500
        (by positivity))
  by_cases hz : stableCount P = 0
  · rw [hz]
    norm_num only [Nat.cast_zero]
    exact pow_pos (by norm_num) n
  · have hexp := (Real.exp_lt_exp).2 hlog
    rw [Real.exp_log (by exact_mod_cast Nat.pos_of_ne_zero hz)] at hexp
    rw [Real.exp_nat_mul, Real.exp_log (by norm_num)] at hexp
    exact hexp

theorem SM_lt_8327_div_2500_pow
    (n : Nat) (hn : 12001 ≤ n) :
    (SM n : ℝ) < ((8327 : ℝ) / 2500) ^ n := by
  obtain ⟨P, hP⟩ := exists_profile_attaining_SM n
  simpa [hP] using stableCount_lt_8327_div_2500_pow hn P

/-! ## Arbitrarily many exponential-tail bits

For every fixed `s`, the same entropy margin makes the low-charge mass at
most `2^{-s}` once `n ≥ 4000(s+1)+1`.  The eight-bit specialization below
removes 255/256 of the former half-mass loss.
-/

theorem deletion_double_count_pow_two
    (s bad total Q r : ℕ) (hQ : 0 < Q)
    (hcount : bad * 2 ^ r ≤ total * Q)
    (hsmall : 2 ^ s * Q ≤ 2 ^ r) :
    2 ^ s * bad ≤ total := by
  have hmul : (2 ^ s * bad) * Q ≤ total * Q := by
    calc
      (2 ^ s * bad) * Q = bad * (2 ^ s * Q) := by
        simp [Nat.mul_comm, Nat.mul_left_comm]
      _ ≤ bad * 2 ^ r := Nat.mul_le_mul_left bad hsmall
      _ ≤ total * Q := hcount
  exact le_of_mul_le_mul_right hmul hQ

theorem optimized_boundary_budget_pow_two {n : Nat}
    (s : Nat) (hn : 4000 * (s + 1) + 1 ≤ n) :
    2 ^ s * (2 ^ (n / 4) *
        (∑ i ∈ Finset.range ((3 * n) / 80 + 1), n.choose i)) ≤
      2 ^ ((n - (3 * n) / 80) / 2) := by
  let k := (3 * n) / 80
  let a := n / 4
  let r := (n - k) / 2
  let B := ∑ i ∈ Finset.range (k + 1), n.choose i
  have hk : 80 * k ≤ 3 * n := by
    dsimp [k]
    omega
  have hprefix :=
    choose_prefix_le_exp_binEntropy_three_eightieths
      (n := n) (k := k) hk
  have hmargin := deletion_entropy_margin_three_eightieths_quantitative
  have hlog : 0 < Real.log 2 := Real.log_pos (by norm_num)
  have ha : (a : ℝ) ≤ (n : ℝ) / 4 := by
    dsimp [a]
    have hnat : 4 * (n / 4) ≤ n := by omega
    have hcast : ((4 * (n / 4) : Nat) : ℝ) ≤ (n : ℝ) := by
      exact_mod_cast hnat
    norm_num only [Nat.cast_mul, Nat.cast_ofNat] at hcast
    nlinarith
  have hkreal : (k : ℝ) ≤ (3 : ℝ) * (n : ℝ) / 80 := by
    have hcast : ((80 * k : Nat) : ℝ) ≤ ((3 * n : Nat) : ℝ) := by
      exact_mod_cast hk
    push_cast at hcast
    nlinarith
  have hr : ((n : ℝ) - (k : ℝ)) / 2 - 1 < (r : ℝ) := by
    have hkn : k ≤ n := by omega
    have hnat : n - k < 2 * ((n - k) / 2 + 1) := by omega
    have hcast : ((n - k : Nat) : ℝ) <
        (2 * ((n - k) / 2 + 1) : Nat) := by exact_mod_cast hnat
    rw [Nat.cast_sub hkn] at hcast
    dsimp [r]
    push_cast at hcast
    nlinarith
  have hnreal : ((4000 * (s + 1) + 1 : Nat) : ℝ) ≤ (n : ℝ) := by
    exact_mod_cast hn
  push_cast at hnreal
  have hbudget : ((s : ℝ) + 1) * Real.log 2 <
      (n : ℝ) / 4000 * Real.log 2 := by
    have hnum : (s : ℝ) + 1 < (n : ℝ) / 4000 := by
      nlinarith
    exact mul_lt_mul_of_pos_right hnum hlog
  have hexponent :
      (s : ℝ) * Real.log 2 + (a : ℝ) * Real.log 2 +
          (n : ℝ) * Real.binEntropy ((3 : ℝ) / 80) <
        (r : ℝ) * Real.log 2 := by
    have hmarginN :
        (n : ℝ) * Real.binEntropy ((3 : ℝ) / 80) <
          (n : ℝ) * (((1 : ℝ) / 4 - ((3 : ℝ) / 80) / 2) *
            Real.log 2 - ((1 : ℝ) / 4000) * Real.log 2) := by
      have hnNat : 0 < n := by omega
      have hnpos : (0 : ℝ) < (n : ℝ) := by exact_mod_cast hnNat
      nlinarith
    nlinarith
  have hB : (B : ℝ) ≤
      Real.exp ((n : ℝ) * Real.binEntropy ((3 : ℝ) / 80)) := by
    simpa [B] using hprefix
  have htwoS : ((2 ^ s : Nat) : ℝ) =
      Real.exp ((s : ℝ) * Real.log 2) := by
    rw [Real.exp_nat_mul, Real.exp_log (by norm_num)]
    norm_num
  have htwoA : ((2 ^ a : Nat) : ℝ) =
      Real.exp ((a : ℝ) * Real.log 2) := by
    rw [Real.exp_nat_mul, Real.exp_log (by norm_num)]
    norm_num
  have htwoR : ((2 ^ r : Nat) : ℝ) =
      Real.exp ((r : ℝ) * Real.log 2) := by
    rw [Real.exp_nat_mul, Real.exp_log (by norm_num)]
    norm_num
  have hreal : ((2 ^ s * (2 ^ a * B) : Nat) : ℝ) < (2 ^ r : Nat) := by
    rw [Nat.cast_mul, Nat.cast_mul, htwoS, htwoA, htwoR]
    calc
      Real.exp ((s : ℝ) * Real.log 2) *
          (Real.exp ((a : ℝ) * Real.log 2) * (B : ℝ)) ≤
          Real.exp ((s : ℝ) * Real.log 2) *
            (Real.exp ((a : ℝ) * Real.log 2) *
              Real.exp ((n : ℝ) *
                Real.binEntropy ((3 : ℝ) / 80))) := by
        gcongr
      _ = Real.exp ((s : ℝ) * Real.log 2 + (a : ℝ) * Real.log 2 +
          (n : ℝ) * Real.binEntropy ((3 : ℝ) / 80)) := by
        rw [← Real.exp_add, ← Real.exp_add]
        congr 1
        ring
      _ < Real.exp ((r : ℝ) * Real.log 2) :=
        Real.exp_lt_exp.mpr hexponent
  have hnat : 2 ^ s * (2 ^ a * B) < 2 ^ r := by exact_mod_cast hreal
  dsimp [a, B, r, k] at hnat ⊢
  omega

theorem canonical_low_charge_pow_two_optimized {n : Nat}
    (s : Nat) (P : ProfileCode n) (hstable : (stableSet P).Nonempty)
    (hn : 4000 * (s + 1) + 1 ≤ n) :
    2 ^ s * Nat.card
        (CanonicalLowChargeSource P hstable ((3 * n) / 80)) ≤
      Nat.card (CodedStable P) := by
  let k := (3 * n) / 80
  let Q := 2 ^ (n / 4) *
    (∑ i ∈ Finset.range (k + 1), n.choose i)
  have hQ : 0 < Q := by
    dsimp [Q]
    have hsum : 0 < ∑ i ∈ Finset.range (k + 1), n.choose i := by
      apply Finset.sum_pos'
      · intro i hi
        exact Nat.zero_le _
      · refine ⟨0, by simp, ?_⟩
        simp
    exact Nat.mul_pos (pow_pos (by omega) _) hsum
  apply deletion_double_count_pow_two s
    (Nat.card (CanonicalLowChargeSource P hstable k))
    (Nat.card (CodedStable P)) Q ((n - k) / 2) hQ
  · exact canonical_low_charge_double_count P hstable k
  · simpa [Q, k] using optimized_boundary_budget_pow_two s hn

theorem normalized_average_ge_255_over_256_threshold
    (M bad r total : ℕ) (hM : 0 < M)
    (hbad : 256 * bad ≤ M)
    (hcharge : (M - bad) * r ≤ total) :
    (255 : ℝ) * (r : ℝ) / 256 ≤
      (M : ℝ)⁻¹ * (total : ℝ) := by
  have hbadM : bad ≤ M := by omega
  have hMreal : (0 : ℝ) < (M : ℝ) := by exact_mod_cast hM
  have hbadReal : (256 : ℝ) * (bad : ℝ) ≤ (M : ℝ) := by
    exact_mod_cast hbad
  have hchargeReal :
      ((M : ℝ) - (bad : ℝ)) * (r : ℝ) ≤ (total : ℝ) := by
    rw [← Nat.cast_sub hbadM, ← Nat.cast_mul]
    exact_mod_cast hcharge
  have hgood : (255 : ℝ) * (M : ℝ) / 256 ≤
      (M : ℝ) - (bad : ℝ) := by
    nlinarith
  have hr : 0 ≤ (r : ℝ) := by positivity
  have hmul := mul_le_mul_of_nonneg_right hgood hr
  rw [inv_mul_eq_div]
  apply (le_div_iff₀ hMreal).2
  calc
    (255 : ℝ) * (r : ℝ) / 256 * (M : ℝ) =
        ((255 : ℝ) * (M : ℝ) / 256) * (r : ℝ) := by ring
    _ ≤ ((M : ℝ) - (bad : ℝ)) * (r : ℝ) := hmul
    _ ≤ (total : ℝ) := hchargeReal

theorem normalized_average_gt_153_n_over_4096
    (n M bad total : ℕ) (hM : 0 < M)
    (hbad : 256 * bad ≤ M)
    (hcharge :
      (M - bad) * ((3 * n) / 80 + 1) ≤ total) :
    (153 : ℝ) * (n : ℝ) / 4096 <
      (M : ℝ)⁻¹ * (total : ℝ) := by
  have havg := normalized_average_ge_255_over_256_threshold
    M bad ((3 * n) / 80 + 1) total hM hbad hcharge
  have hfloor := three_n_div_eighty_lt_floor_succ n
  nlinarith

theorem canonical_normalized_average_charge_gt_153_n_over_4096
    {n : Nat} (P : ProfileCode n)
    (hstable : (stableSet P).Nonempty) (hn : 36001 ≤ n) :
    (153 : ℝ) * (n : ℝ) / 4096 <
      (Nat.card (CodedStable P) : ℝ)⁻¹ *
        (canonicalTotalCharge P hstable : ℝ) := by
  let mu := Classical.choose hstable
  have hmu : mu ∈ stableSet P := Classical.choose_spec hstable
  letI : Nonempty (CodedStable P) :=
    ⟨⟨mu, (mem_stableSet_iff P mu).1 hmu⟩⟩
  have hM : 0 < Nat.card (CodedStable P) := Nat.card_pos
  apply normalized_average_gt_153_n_over_4096 n
    (Nat.card (CodedStable P))
    (Nat.card (CanonicalLowChargeSource P hstable ((3 * n) / 80)))
    (canonicalTotalCharge P hstable) hM
  · simpa using canonical_low_charge_pow_two_optimized 8 P hstable (by omega)
  · exact canonical_good_sources_pay_threshold
      P hstable ((3 * n) / 80)

def eightBitTailJointDelta : ℝ :=
  51 * Real.log ((3 : ℝ) / 2) / 40960

theorem eightBitTailJointDelta_pos : 0 < eightBitTailJointDelta := by
  unfold eightBitTailJointDelta
  have := log_three_halves_pos
  positivity

theorem eightBitTailJointDelta_le_averaged_joint_slack
    {n : Nat} {P : ProfileCode n} (hn : 36001 ≤ n)
    (D : StaticWindowData P) (hstable : (stableSet P).Nonempty) :
    (n : ℝ) * eightBitTailJointDelta ≤
      averagedTargetGeometricSlack D + averagedTargetSupportWindowSlack D := by
  have hcharge := canonical_normalized_average_charge_gt_153_n_over_4096
    P hstable hn
  have hlocal := normalized_canonical_charge_payment_le_averaged_joint_slack
    (by omega) D hstable
  have hlog : 0 ≤ Real.log ((3 : ℝ) / 2) := (log_three_halves_pos).le
  unfold eightBitTailJointDelta
  calc
    (n : ℝ) * (51 * Real.log ((3 : ℝ) / 2) / 40960) =
        Real.log ((3 : ℝ) / 2) / 30 *
          ((153 : ℝ) * (n : ℝ) / 4096) := by ring
    _ ≤ Real.log ((3 : ℝ) / 2) / 30 *
        ((Nat.card (CodedStable P) : ℝ)⁻¹ *
          (canonicalTotalCharge P hstable : ℝ)) := by
      gcongr
    _ ≤ _ := hlocal

theorem eightBitTailJointDelta_le_totalJointSlack
    {n : Nat} {P : ProfileCode n} (hn : 36001 ≤ n)
    (D : StaticWindowData P) (hstable : (stableSet P).Nonempty) :
    (n : ℝ) * eightBitTailJointDelta ≤ totalJointSlack P :=
  (eightBitTailJointDelta_le_averaged_joint_slack hn D hstable).trans
    (averaged_joint_target_slack_le_totalJointSlack D hstable)

theorem eightBitTailJointDelta_le_geometricLogSeries :
    eightBitTailJointDelta ≤ geometricLogSeries := by
  have hterm : geometricLogWeight 2 ≤ geometricLogSeries := by
    unfold geometricLogSeries
    exact summable_geometricLogWeight.le_tsum 2 fun j hj ↦
      geometricLogWeight_nonneg j
  have hlog : Real.log ((3 : ℝ) / 2) ≤ Real.log 2 :=
    Real.log_le_log (by norm_num) (by norm_num)
  have hlog0 : 0 ≤ Real.log ((3 : ℝ) / 2) :=
    (log_three_halves_pos).le
  have hlocal : eightBitTailJointDelta ≤ geometricLogWeight 2 := by
    unfold eightBitTailJointDelta geometricLogWeight
    norm_num
    nlinarith
  exact hlocal.trans hterm

theorem all_profiles_eightBitTailJointSlack
    {n : Nat} (hn : 36001 ≤ n) (P : ProfileCode n) :
    (n : ℝ) * eightBitTailJointDelta ≤ totalJointSlack P := by
  classical
  by_cases hz : stableCount P = 0
  · unfold totalJointSlack
    rw [hz]
    simp only [Nat.cast_zero, Real.log_zero, sub_zero]
    exact mul_le_mul_of_nonneg_left eightBitTailJointDelta_le_geometricLogSeries
      (Nat.cast_nonneg n)
  · have hpositive : 0 < stableCount P := Nat.pos_of_ne_zero hz
    have hstable : (stableSet P).Nonempty := by
      apply Finset.card_pos.mp
      simpa [stableCount] using hpositive
    let D : StaticWindowData P := Classical.choice (exists_staticWindowData P)
    exact eightBitTailJointDelta_le_totalJointSlack hn D hstable

theorem one_point_120307_lt_log_8326_div_2500 :
    (120307 : ℝ) / 100000 < Real.log ((8326 : ℝ) / 2500) := by
  have h := Real.sum_range_le_log_div
    (x := (2913 : ℝ) / 5413) (by norm_num) (by norm_num) 16
  norm_num [Finset.sum_range_succ] at h
  nlinarith

theorem geometricLogSeries_sub_eightBitTailJointDelta_lt_log_8326_div_2500 :
    geometricLogSeries - eightBitTailJointDelta <
      Real.log ((8326 : ℝ) / 2500) := by
  have hS := geometricLogSeries_lt_120356492_div_100000000
  have hd := log_three_halves_gt_4054_div_10000
  have hq := one_point_120307_lt_log_8326_div_2500
  unfold eightBitTailJointDelta
  linarith

theorem stableCount_lt_8326_div_2500_pow
    {n : Nat} (hn : 36001 ≤ n) (P : ProfileCode n) :
    (stableCount P : ℝ) < ((8326 : ℝ) / 2500) ^ n := by
  have hjoint := all_profiles_eightBitTailJointSlack hn P
  have hmain :=
    (jointSlack_linear_lower_iff_log_bound P eightBitTailJointDelta).1 hjoint
  have hlog : Real.log (stableCount P) <
      (n : ℝ) * Real.log ((8326 : ℝ) / 2500) :=
    hmain.trans_lt
      (mul_lt_mul_of_pos_left
        geometricLogSeries_sub_eightBitTailJointDelta_lt_log_8326_div_2500
        (by positivity))
  by_cases hz : stableCount P = 0
  · rw [hz]
    norm_num only [Nat.cast_zero]
    exact pow_pos (by norm_num) n
  · have hexp := (Real.exp_lt_exp).2 hlog
    rw [Real.exp_log (by exact_mod_cast Nat.pos_of_ne_zero hz)] at hexp
    rw [Real.exp_nat_mul, Real.exp_log (by norm_num)] at hexp
    exact hexp

theorem SM_lt_8326_div_2500_pow
    (n : Nat) (hn : 36001 ≤ n) :
    (SM n : ℝ) < ((8326 : ℝ) / 2500) ^ n := by
  obtain ⟨P, hP⟩ := exists_profile_attaining_SM n
  simpa [hP] using stableCount_lt_8326_div_2500_pow hn P

end

end StableMatchingsJointCharging
