import StableMatchingsE2E.FinalTheorem

namespace StableMatchingsE2E

open MeasureTheory ProbabilityTheory Set
open scoped unitInterval ENNReal BigOperators
open StableMatchings355 StableMatchingsEntropy

noncomputable section

/-! # Exact endpoint of the geometric-series reduction

This module deliberately does not alter the frozen `3.4` theorem.  It removes
only the final comparison with `log (17/5)` and records the exact non-strict
constant supplied by the already verified geometric reduction. -/

theorem geometricLogSeries_nonneg : 0 ≤ geometricLogSeries := by
  unfold geometricLogSeries
  exact tsum_nonneg geometricLogWeight_nonneg

theorem lintegral_unit_geometricSeries_eq_ofReal :
    (∫⁻ x : I,
        ∑' k : Nat, ENNReal.ofReal (geometricLogTerm k (x : ℝ)) ∂volume) =
      ENNReal.ofReal geometricLogSeries := by
  let F : ℝ → ENNReal := fun x ↦
    ∑' k : Nat, ENNReal.ofReal (geometricLogTerm k x)
  have hF : Measurable F := by
    exact Measurable.tsum fun k ↦
      (geometricLogTerm_continuous k).measurable.ennreal_ofReal
  change (∫⁻ x : I, F (x : ℝ) ∂volume) = _
  rw [lintegral_unitInterval_eq_Ioc F hF]
  rw [show (∫⁻ x : ℝ in Set.Ioc (0 : ℝ) 1, F x) =
      ∑' k : Nat, ENNReal.ofReal (geometricLogWeight k) by
    exact lintegral_tsum_geometric_log_term]
  rw [← ENNReal.ofReal_tsum_of_nonneg geometricLogWeight_nonneg
    summable_geometricLogWeight]
  rfl

theorem lintegral_unit_actualMarkerPair_le_geometricLogSeries {n q : Nat}
    {P : Profile (Fin n) (Fin n)} {target : Fin n}
    (E : ExactStablePartnerEnumeration (q := q) P target)
    (base : Matching (Fin n) (Fin n)) (j : Fin q)
    (hbaseTarget : base.manPartner target = E.ranked.partner j) :
    (∫⁻ x : I, ∫⁻ ω,
        prefixPairWindowLogNN j.val (q - (j.val + 1))
          (actualMarkerPair E base j hbaseTarget x ω)
        ∂(TargetOtherPriorityMeasure target) ∂volume) ≤
      ENNReal.ofReal geometricLogSeries := by
  calc
    _ ≤ (∫⁻ x : I,
        ∑' k : Nat, ENNReal.ofReal (geometricLogTerm k (x : ℝ)) ∂volume) := by
      apply MeasureTheory.lintegral_mono_ae
      filter_upwards [MeasureTheory.volume.ae_ne (0 : I)] with x hx
      exact lintegral_actualMarkerPair_le_geometricSeries
        E base j hbaseTarget hx
    _ = _ := lintegral_unit_geometricSeries_eq_ofReal

theorem lintegral_full_lexTargetMarkerLogNN_le_geometricLogSeries {n : Nat}
    {P : ProfileCode n} (D : StaticWindowData P) (base : StableBase P)
    (m : Fin n) :
    (∫⁻ priority, lexTargetMarkerLogNN D base m priority
      ∂(FullPriorityMeasure n)) ≤ ENNReal.ofReal geometricLogSeries := by
  calc
    _ = ∫⁻ z, lexTargetMarkerLogNN D base m
          (assemblePriority m z) ∂(SplitTargetPriorityMeasure m) := by
      rw [← map_assemblePriority_splitTargetPriorityMeasure m]
      exact MeasureTheory.lintegral_map
        (measurable_lexTargetMarkerLogNN D base m)
        (measurable_assemblePriority m)
    _ = ∫⁻ x : I, ∫⁻ ω,
          lexTargetMarkerLogNN D base m (assemblePriority m (x, ω))
          ∂(TargetOtherPriorityMeasure m) ∂volume := by
      exact MeasureTheory.lintegral_prod _
        ((measurable_lexTargetMarkerLogNN D base m).comp
          (measurable_assemblePriority m)).aemeasurable
    _ = ∫⁻ x : I, ∫⁻ ω,
          prefixPairWindowLogNN (D.center base m).val
            (D.q m - ((D.center base m).val + 1))
            (actualMarkerPair (D.enumeration m) base.1.toCore
              (D.center base m) (D.center_spec base m) x ω)
          ∂(TargetOtherPriorityMeasure m) ∂volume := by
      apply MeasureTheory.lintegral_congr
      intro x
      exact MeasureTheory.lintegral_congr_ae
        (ae_lexTargetMarkerLogNN_assemble_eq_actual D base m x)
    _ ≤ _ := lintegral_unit_actualMarkerPair_le_geometricLogSeries
      (D.enumeration m) base.1.toCore (D.center base m)
      (D.center_spec base m)

theorem integral_full_lexTargetMarkerLog_le_geometricLogSeries {n : Nat}
    {P : ProfileCode n} (D : StaticWindowData P) (base : StableBase P)
    (m : Fin n) :
    (∫ priority, lexTargetMarkerLog D base priority m
      ∂(FullPriorityMeasure n)) ≤ geometricLogSeries := by
  apply (ENNReal.ofReal_le_ofReal_iff geometricLogSeries_nonneg).1
  rw [MeasureTheory.ofReal_integral_eq_lintegral_ofReal
    (integrable_lexTargetMarkerLog D base m)
    (Filter.Eventually.of_forall fun priority ↦
      lexTargetMarkerLog_nonneg D base priority m)]
  change (∫⁻ priority, lexTargetMarkerLogNN D base m priority
    ∂(FullPriorityMeasure n)) ≤ ENNReal.ofReal geometricLogSeries
  exact lintegral_full_lexTargetMarkerLogNN_le_geometricLogSeries D base m

theorem integral_stableBaseLexCost_le_geometricLogSeries {n : Nat}
    {P : ProfileCode n} (D : StaticWindowData P)
    (base : MatchingCode n) (hbase : Stable P base) :
    (∫ priority, stableBaseLexCost D base priority
      ∂(FullPriorityMeasure n)) ≤ (n : ℝ) * geometricLogSeries := by
  rw [integral_stableBaseLexCost_of_stable D base hbase]
  calc
    (∑ m : Fin n, ∫ priority,
        lexTargetMarkerLog D ⟨base, hbase⟩ priority m
        ∂(FullPriorityMeasure n)) ≤
        ∑ _m : Fin n, geometricLogSeries := by
      exact Finset.sum_le_sum fun m _ ↦
        integral_full_lexTargetMarkerLog_le_geometricLogSeries
          D ⟨base, hbase⟩ m
    _ = (n : ℝ) * geometricLogSeries := by simp

theorem integral_aggregateLexCost_le_geometricLogSeries {n : Nat}
    {P : ProfileCode n} (D : StaticWindowData P)
    (hstable : (stableSet P).Nonempty) :
    (∫ priority, aggregateLexCost D priority
      ∂(FullPriorityMeasure n)) ≤ (n : ℝ) * geometricLogSeries := by
  classical
  rw [integral_aggregateLexCost_eq D]
  have hcard : 0 < ((stableSet P).card : ℝ) := by
    exact_mod_cast (Finset.card_pos.mpr hstable)
  have hsum :
      (∑ base ∈ stableSet P,
          ∑ m : Fin n, ∫ priority,
            if h : Stable P base then
              lexTargetMarkerLog D ⟨base, h⟩ priority m
            else 0
            ∂(FullPriorityMeasure n)) ≤
        ∑ _base ∈ stableSet P, (n : ℝ) * geometricLogSeries := by
    apply Finset.sum_le_sum
    intro base hbase
    have hs : Stable P base := (mem_stableSet_iff P base).1 hbase
    simpa [hs, integral_stableBaseLexCost_of_stable] using
      integral_stableBaseLexCost_le_geometricLogSeries D base hs
  calc
    ((stableSet P).card : ℝ)⁻¹ *
        (∑ base ∈ stableSet P,
          ∑ m : Fin n, ∫ priority,
            if h : Stable P base then
              lexTargetMarkerLog D ⟨base, h⟩ priority m
            else 0
            ∂(FullPriorityMeasure n)) ≤
      ((stableSet P).card : ℝ)⁻¹ *
        (∑ _base ∈ stableSet P, (n : ℝ) * geometricLogSeries) :=
      mul_le_mul_of_nonneg_left hsum (le_of_lt (inv_pos.mpr hcard))
    _ = (n : ℝ) * geometricLogSeries := by
      rw [Finset.sum_const, nsmul_eq_mul]
      field_simp

theorem log_stableCount_le_n_geometricLogSeries {n : Nat}
    {P : ProfileCode n} (D : StaticWindowData P)
    (hstable : (stableSet P).Nonempty) :
    Real.log (stableCount P) ≤ (n : ℝ) * geometricLogSeries := by
  have hmono : Real.log (stableCount P) ≤
      ∫ priority, aggregateLexCost D priority
        ∂(FullPriorityMeasure n) := by
    have h := MeasureTheory.integral_mono
      (integrable_const (Real.log (stableCount P)) :
        Integrable (fun _ : Fin n → I ↦ Real.log (stableCount P))
          (FullPriorityMeasure n))
      (integrable_aggregateLexCost D)
      (fun priority ↦ log_stableCount_le_aggregateLexCost D priority hstable)
    simpa using h
  exact hmono.trans (integral_aggregateLexCost_le_geometricLogSeries D hstable)

/-- The exact non-strict endpoint furnished by the geometric-series reduction. -/
theorem log_stableCount_le_n_geometricLogSeries_all (n : Nat)
    (P : ProfileCode n) :
    Real.log (stableCount P) ≤ (n : ℝ) * geometricLogSeries := by
  classical
  by_cases hz : stableCount P = 0
  · rw [hz]
    simp only [Nat.cast_zero, Real.log_zero]
    exact mul_nonneg (Nat.cast_nonneg n) geometricLogSeries_nonneg
  · have hpos : 0 < stableCount P := Nat.pos_of_ne_zero hz
    have hstable : (stableSet P).Nonempty := by
      apply Finset.card_pos.mp
      simpa [stableCount] using hpos
    let D : StaticWindowData P := Classical.choice (exists_staticWindowData P)
    exact log_stableCount_le_n_geometricLogSeries D hstable

private theorem exp_nat_mul_eq_pow (x : ℝ) (n : Nat) :
    Real.exp ((n : ℝ) * x) = (Real.exp x) ^ n := by
  induction n with
  | zero => simp
  | succ n ih =>
      rw [Nat.cast_succ, add_mul, Real.exp_add, ih, pow_succ]
      simp

/-- Profile-level form of the exact geometric-series endpoint. -/
theorem stableCount_le_exp_geometricLogSeries_pow (n : Nat)
    (P : ProfileCode n) :
    (stableCount P : ℝ) ≤ (Real.exp geometricLogSeries) ^ n := by
  by_cases hz : stableCount P = 0
  · rw [hz]
    simpa only [Nat.cast_zero] using
      pow_nonneg (le_of_lt (Real.exp_pos geometricLogSeries)) n
  · have hpos : (0 : ℝ) < stableCount P := by
      exact_mod_cast Nat.pos_of_ne_zero hz
    have hexp := (Real.exp_le_exp).2
      (log_stableCount_le_n_geometricLogSeries_all n P)
    rw [Real.exp_log hpos, exp_nat_mul_eq_pow] at hexp
    exact hexp

/-- Extremal form of the exact geometric-series endpoint. -/
theorem SM_le_exp_geometricLogSeries_pow (n : Nat) :
    (SM n : ℝ) ≤ (Real.exp geometricLogSeries) ^ n := by
  obtain ⟨P, hP⟩ := exists_profile_attaining_SM n
  simpa [hP] using stableCount_le_exp_geometricLogSeries_pow n P

end

end StableMatchingsE2E
