import «CanonicalPartnerIndexBridge»

/-!
# Local endpoint payment for canonical shallow men

This file turns the endpoint description of a man's canonical rotation chain
into an explicit loss in the infinite-geometric comparison.  The proof uses
the same two infinite Bernoulli streams for the finite prefixes and for the
geometric waits, so the positive gap is pointwise on an event of exact mass.
-/

namespace StableMatchingsJointCharging

open MeasureTheory ProbabilityTheory Set
open scoped unitInterval ENNReal BigOperators
open StableMatchings355 StableMatchingsEntropy StableMatchingsE2E

noncomputable section

def leftEndpointEvent : Set ((Nat → Bool) × (Nat → Bool)) :=
  infiniteDummyWaitPair ⁻¹' ({(2, 0)} : Set (Nat × Nat))

def rightEndpointEvent : Set ((Nat → Bool) × (Nat → Bool)) :=
  infiniteDummyWaitPair ⁻¹' ({(0, 2)} : Set (Nat × Nat))

theorem measurableSet_leftEndpointEvent : MeasurableSet leftEndpointEvent :=
  (measurableSet_singleton (2, 0)).preimage measurable_infiniteDummyWaitPair

theorem measurableSet_rightEndpointEvent : MeasurableSet rightEndpointEvent :=
  (measurableSet_singleton (0, 2)).preimage measurable_infiniteDummyWaitPair

theorem infiniteDummyPairMeasure_leftEndpointEvent {x : I} (hx : x ≠ 0) :
    InfiniteDummyPairMeasure x leftEndpointEvent =
      ENNReal.ofReal ((x : ℝ) ^ 2 * (1 - (x : ℝ)) ^ 2) := by
  unfold leftEndpointEvent
  rw [← Measure.map_apply measurable_infiniteDummyWaitPair
    (measurableSet_singleton (2, 0))]
  rw [infiniteDummyWaitPair_has_geometric_pair_law hx]
  rw [← ENNReal.ofReal_toReal (measure_ne_top _ _)]
  congr 1
  change (GeometricPairMeasure x).real {(2, 0)} = _
  rw [geometricPairMeasure_real_singleton,
    geometricMeasure_real_singleton hx,
    geometricMeasure_real_singleton hx]
  ring

theorem infiniteDummyPairMeasure_rightEndpointEvent {x : I} (hx : x ≠ 0) :
    InfiniteDummyPairMeasure x rightEndpointEvent =
      ENNReal.ofReal ((x : ℝ) ^ 2 * (1 - (x : ℝ)) ^ 2) := by
  unfold rightEndpointEvent
  rw [← Measure.map_apply measurable_infiniteDummyWaitPair
    (measurableSet_singleton (0, 2))]
  rw [infiniteDummyWaitPair_has_geometric_pair_law hx]
  rw [← ENNReal.ofReal_toReal (measure_ne_top _ _)]
  congr 1
  change (GeometricPairMeasure x).real {(0, 2)} = _
  rw [geometricPairMeasure_real_singleton,
    geometricMeasure_real_singleton hx,
    geometricMeasure_real_singleton hx]
  ring

theorem markerPrefixLog_nonneg (leftLen rightLen : Nat)
    (z : (Nat → Bool) × (Nat → Bool)) :
    0 ≤ Real.log (markerWindowWidth
      (streamPrefix leftLen z.1) (streamPrefix rightLen z.2) : ℝ) := by
  apply Real.log_nonneg
  have hl := truncatedWait_pos (streamPrefix leftLen z.1)
  have hr := truncatedWait_pos (streamPrefix rightLen z.2)
  exact_mod_cast (show 1 ≤ markerWindowWidth
    (streamPrefix leftLen z.1) (streamPrefix rightLen z.2) by
      simp only [markerWindowWidth]
      omega)

theorem left_endpoint_pointwise_payment
    (leftLen rightLen : Nat) (hleft : leftLen ≤ 1)
    (z : (Nat → Bool) × (Nat → Bool))
    (hs : hasSuccess z.1 ∧ hasSuccess z.2)
    (hevent : z ∈ leftEndpointEvent) :
    prefixPairWindowLogNN leftLen rightLen
        (pairedPrefixVector leftLen rightLen z) +
        ENNReal.ofReal (Real.log ((3 : ℝ) / 2)) ≤
      geometricWindowLogNN (infiniteDummyWaitPair z) := by
  have hwaits : firstSuccess z.1 = 2 ∧ firstSuccess z.2 = 0 := by
    simpa [leftEndpointEvent, infiniteDummyWaitPair, Prod.ext_iff] using hevent
  have hgap := endpoint_event_log_gap leftLen rightLen hleft z.1 z.2
    hs.1 hs.2 hwaits.1 hwaits.2
  have hfinite := markerPrefixLog_nonneg leftLen rightLen z
  simp only [prefixPairWindowLogNN, pairedPrefixVector,
    ofFn_streamPrefixVector, geometricWindowLogNN]
  rw [← ENNReal.ofReal_add hfinite (Real.log_nonneg (by norm_num : (1 : ℝ) ≤ 3 / 2))]
  apply ENNReal.ofReal_le_ofReal
  rw [show geometricWindow (infiniteDummyWaitPair z) = 3 by
    exact endpoint_event_infinite_width_eq_three z.1 z.2 hwaits.1 hwaits.2]
  linarith

theorem right_endpoint_pointwise_payment
    (leftLen rightLen : Nat) (hright : rightLen ≤ 1)
    (z : (Nat → Bool) × (Nat → Bool))
    (hs : hasSuccess z.1 ∧ hasSuccess z.2)
    (hevent : z ∈ rightEndpointEvent) :
    prefixPairWindowLogNN leftLen rightLen
        (pairedPrefixVector leftLen rightLen z) +
        ENNReal.ofReal (Real.log ((3 : ℝ) / 2)) ≤
      geometricWindowLogNN (infiniteDummyWaitPair z) := by
  have hwaits : firstSuccess z.1 = 0 ∧ firstSuccess z.2 = 2 := by
    simpa [rightEndpointEvent, infiniteDummyWaitPair, Prod.ext_iff] using hevent
  have hgap := endpoint_event_log_gap rightLen leftLen hright z.2 z.1
    hs.2 hs.1 hwaits.2 hwaits.1
  have hfinite := markerPrefixLog_nonneg leftLen rightLen z
  simp only [prefixPairWindowLogNN, pairedPrefixVector,
    ofFn_streamPrefixVector, geometricWindowLogNN]
  rw [← ENNReal.ofReal_add hfinite (Real.log_nonneg (by norm_num : (1 : ℝ) ≤ 3 / 2))]
  apply ENNReal.ofReal_le_ofReal
  rw [show geometricWindow (infiniteDummyWaitPair z) = 3 by
    simp [geometricWindow, infiniteDummyWaitPair, hwaits.1, hwaits.2]]
  have hwidthSwap : markerWindowWidth
      (streamPrefix leftLen z.1) (streamPrefix rightLen z.2) =
      markerWindowWidth (streamPrefix rightLen z.2)
        (streamPrefix leftLen z.1) := by
    simp only [markerWindowWidth]
    omega
  rw [hwidthSwap]
  linarith

theorem lintegral_left_endpoint_payment {x : I} (hx : x ≠ 0)
    (leftLen rightLen : Nat) (hleft : leftLen ≤ 1) :
    (∫⁻ z, prefixPairWindowLogNN leftLen rightLen
        (pairedPrefixVector leftLen rightLen z)
        ∂(InfiniteDummyPairMeasure x)) +
        ENNReal.ofReal (Real.log ((3 : ℝ) / 2)) *
          ENNReal.ofReal ((x : ℝ) ^ 2 * (1 - (x : ℝ)) ^ 2) ≤
      ∑' k : Nat, ENNReal.ofReal (geometricLogTerm k (x : ℝ)) := by
  let finiteLog : ((Nat → Bool) × (Nat → Bool)) → ENNReal := fun z ↦
    prefixPairWindowLogNN leftLen rightLen
      (pairedPrefixVector leftLen rightLen z)
  let payment : ((Nat → Bool) × (Nat → Bool)) → ENNReal :=
    leftEndpointEvent.indicator
      (fun _ ↦ ENNReal.ofReal (Real.log ((3 : ℝ) / 2)))
  have hfiniteMeas : Measurable finiteLog :=
    (measurable_prefixPairWindowLogNN _ _).comp
      (measurable_pairedPrefixVector _ _)
  have hpayMeas : Measurable payment := by
    exact measurable_const.indicator measurableSet_leftEndpointEvent
  calc
    _ = ∫⁻ z, finiteLog z + payment z
          ∂(InfiniteDummyPairMeasure x) := by
      rw [MeasureTheory.lintegral_add_left hfiniteMeas]
      unfold payment
      rw [MeasureTheory.lintegral_indicator measurableSet_leftEndpointEvent,
        MeasureTheory.setLIntegral_const,
        infiniteDummyPairMeasure_leftEndpointEvent hx]
    _ ≤ ∫⁻ z, geometricWindowLogNN (infiniteDummyWaitPair z)
          ∂(InfiniteDummyPairMeasure x) := by
      apply MeasureTheory.lintegral_mono_ae
      filter_upwards [ae_infiniteDummyPair_hasSuccess hx,
        ae_markerWindowWidth_prefix_le_geometricWindow hx leftLen rightLen]
          with z hs hdom
      by_cases hevent : z ∈ leftEndpointEvent
      · simpa [finiteLog, payment, Set.indicator_of_mem hevent] using
          left_endpoint_pointwise_payment leftLen rightLen hleft z hs hevent
      · have hbase : finiteLog z ≤
            geometricWindowLogNN (infiniteDummyWaitPair z) := by
          unfold finiteLog prefixPairWindowLogNN geometricWindowLogNN
          simp only [pairedPrefixVector, ofFn_streamPrefixVector]
          apply ENNReal.ofReal_le_ofReal
          apply Real.log_le_log
          · have hl := truncatedWait_pos (streamPrefix leftLen z.1)
            have hr := truncatedWait_pos (streamPrefix rightLen z.2)
            exact_mod_cast (show 0 < markerWindowWidth
              (streamPrefix leftLen z.1) (streamPrefix rightLen z.2) by
                simp only [markerWindowWidth]
                omega)
          · exact_mod_cast hdom
        simpa [payment, hevent] using hbase
    _ = ∫⁻ p, geometricWindowLogNN p ∂(GeometricPairMeasure x) := by
      rw [← infiniteDummyWaitPair_has_geometric_pair_law hx]
      exact (MeasureTheory.lintegral_map measurable_geometricWindowLogNN
        measurable_infiniteDummyWaitPair).symm
    _ = _ := lintegral_geometricWindowLogNN_eq_tsum hx

theorem lintegral_right_endpoint_payment {x : I} (hx : x ≠ 0)
    (leftLen rightLen : Nat) (hright : rightLen ≤ 1) :
    (∫⁻ z, prefixPairWindowLogNN leftLen rightLen
        (pairedPrefixVector leftLen rightLen z)
        ∂(InfiniteDummyPairMeasure x)) +
        ENNReal.ofReal (Real.log ((3 : ℝ) / 2)) *
          ENNReal.ofReal ((x : ℝ) ^ 2 * (1 - (x : ℝ)) ^ 2) ≤
      ∑' k : Nat, ENNReal.ofReal (geometricLogTerm k (x : ℝ)) := by
  let finiteLog : ((Nat → Bool) × (Nat → Bool)) → ENNReal := fun z ↦
    prefixPairWindowLogNN leftLen rightLen
      (pairedPrefixVector leftLen rightLen z)
  let payment : ((Nat → Bool) × (Nat → Bool)) → ENNReal :=
    rightEndpointEvent.indicator
      (fun _ ↦ ENNReal.ofReal (Real.log ((3 : ℝ) / 2)))
  have hfiniteMeas : Measurable finiteLog :=
    (measurable_prefixPairWindowLogNN _ _).comp
      (measurable_pairedPrefixVector _ _)
  have hpayMeas : Measurable payment := by
    exact measurable_const.indicator measurableSet_rightEndpointEvent
  calc
    _ = ∫⁻ z, finiteLog z + payment z
          ∂(InfiniteDummyPairMeasure x) := by
      rw [MeasureTheory.lintegral_add_left hfiniteMeas]
      unfold payment
      rw [MeasureTheory.lintegral_indicator measurableSet_rightEndpointEvent,
        MeasureTheory.setLIntegral_const,
        infiniteDummyPairMeasure_rightEndpointEvent hx]
    _ ≤ ∫⁻ z, geometricWindowLogNN (infiniteDummyWaitPair z)
          ∂(InfiniteDummyPairMeasure x) := by
      apply MeasureTheory.lintegral_mono_ae
      filter_upwards [ae_infiniteDummyPair_hasSuccess hx,
        ae_markerWindowWidth_prefix_le_geometricWindow hx leftLen rightLen]
          with z hs hdom
      by_cases hevent : z ∈ rightEndpointEvent
      · simpa [finiteLog, payment, Set.indicator_of_mem hevent] using
          right_endpoint_pointwise_payment leftLen rightLen hright z hs hevent
      · have hbase : finiteLog z ≤
            geometricWindowLogNN (infiniteDummyWaitPair z) := by
          unfold finiteLog prefixPairWindowLogNN geometricWindowLogNN
          simp only [pairedPrefixVector, ofFn_streamPrefixVector]
          apply ENNReal.ofReal_le_ofReal
          apply Real.log_le_log
          · have hl := truncatedWait_pos (streamPrefix leftLen z.1)
            have hr := truncatedWait_pos (streamPrefix rightLen z.2)
            exact_mod_cast (show 0 < markerWindowWidth
              (streamPrefix leftLen z.1) (streamPrefix rightLen z.2) by
                simp only [markerWindowWidth]
                omega)
          · exact_mod_cast hdom
        simpa [payment, hevent] using hbase
    _ = ∫⁻ p, geometricWindowLogNN p ∂(GeometricPairMeasure x) := by
      rw [← infiniteDummyWaitPair_has_geometric_pair_law hx]
      exact (MeasureTheory.lintegral_map measurable_geometricWindowLogNN
        measurable_infiniteDummyWaitPair).symm
    _ = _ := lintegral_geometricWindowLogNN_eq_tsum hx

theorem lintegral_unit_endpoint_priority_event :
    (∫⁻ x : I,
        ENNReal.ofReal ((x : ℝ) ^ 2 * (1 - (x : ℝ)) ^ 2) ∂volume) =
      ENNReal.ofReal ((1 : ℝ) / 30) := by
  let p : ℝ → ℝ := fun x ↦ x ^ 2 * (1 - x) ^ 2
  have hpcont : Continuous p := by
    exact (continuous_id.pow 2).mul ((continuous_const.sub continuous_id).pow 2)
  have hpmeas : Measurable (fun x ↦ ENNReal.ofReal (p x)) :=
    hpcont.measurable.ennreal_ofReal
  rw [lintegral_unitInterval_eq_Ioc (fun x ↦ ENNReal.ofReal (p x)) hpmeas]
  have hpint : IntegrableOn p (Set.Ioc (0 : ℝ) 1) :=
    hpcont.integrableOn_Icc.mono_set Set.Ioc_subset_Icc_self
  have hpnonneg : ∀ᵐ x ∂(volume.restrict (Set.Ioc (0 : ℝ) 1)),
      0 ≤ p x := by
    exact Filter.Eventually.of_forall fun x ↦ by
      dsimp [p]
      positivity
  rw [← MeasureTheory.ofReal_integral_eq_lintegral_ofReal hpint hpnonneg]
  rw [← intervalIntegral.integral_of_le (by norm_num : (0 : ℝ) ≤ 1)]
  rw [show (∫ x : ℝ in 0..1, p x) = (1 : ℝ) / 30 by
    simpa [p] using integral_endpoint_priority_event]

theorem finitePrefixCostNN_add_endpointPayment_le_of_left
    (leftLen rightLen : Nat) (hleft : leftLen ≤ 1) :
    finitePrefixCostNN leftLen rightLen +
        ENNReal.ofReal (Real.log ((3 : ℝ) / 2) / 30) ≤
      ENNReal.ofReal geometricLogSeries := by
  let penalty : I → ENNReal := fun x ↦
    ENNReal.ofReal (Real.log ((3 : ℝ) / 2)) *
      ENNReal.ofReal ((x : ℝ) ^ 2 * (1 - (x : ℝ)) ^ 2)
  have hkernelMeas : Measurable (fun x : I ↦
      ENNReal.ofReal ((x : ℝ) ^ 2 * (1 - (x : ℝ)) ^ 2)) := by
    fun_prop
  have hpenaltyMeas : Measurable penalty := by
    exact measurable_const.mul hkernelMeas
  have hpenaltyIntegral :
      (∫⁻ x : I, penalty x ∂volume) =
        ENNReal.ofReal (Real.log ((3 : ℝ) / 2) / 30) := by
    unfold penalty
    rw [MeasureTheory.lintegral_const_mul _ hkernelMeas,
      lintegral_unit_endpoint_priority_event]
    rw [← ENNReal.ofReal_mul (Real.log_nonneg
      (by norm_num : (1 : ℝ) ≤ 3 / 2))]
    congr 1
    ring
  calc
    _ = (∫⁻ x : I,
          (∫⁻ z, prefixPairWindowLogNN leftLen rightLen
              (pairedPrefixVector leftLen rightLen z)
              ∂(InfiniteDummyPairMeasure x)) + penalty x ∂volume) := by
      rw [MeasureTheory.lintegral_add_right _ hpenaltyMeas]
      rw [hpenaltyIntegral]
      rfl
    _ ≤ (∫⁻ x : I,
          ∑' k : Nat, ENNReal.ofReal (geometricLogTerm k (x : ℝ))
          ∂volume) := by
      apply MeasureTheory.lintegral_mono_ae
      filter_upwards [MeasureTheory.volume.ae_ne (0 : I)] with x hx
      exact lintegral_left_endpoint_payment hx leftLen rightLen hleft
    _ = _ := lintegral_unit_geometricSeries_eq_ofReal

theorem finitePrefixCostNN_add_endpointPayment_le_of_right
    (leftLen rightLen : Nat) (hright : rightLen ≤ 1) :
    finitePrefixCostNN leftLen rightLen +
        ENNReal.ofReal (Real.log ((3 : ℝ) / 2) / 30) ≤
      ENNReal.ofReal geometricLogSeries := by
  let penalty : I → ENNReal := fun x ↦
    ENNReal.ofReal (Real.log ((3 : ℝ) / 2)) *
      ENNReal.ofReal ((x : ℝ) ^ 2 * (1 - (x : ℝ)) ^ 2)
  have hkernelMeas : Measurable (fun x : I ↦
      ENNReal.ofReal ((x : ℝ) ^ 2 * (1 - (x : ℝ)) ^ 2)) := by
    fun_prop
  have hpenaltyMeas : Measurable penalty := by
    exact measurable_const.mul hkernelMeas
  have hpenaltyIntegral :
      (∫⁻ x : I, penalty x ∂volume) =
        ENNReal.ofReal (Real.log ((3 : ℝ) / 2) / 30) := by
    unfold penalty
    rw [MeasureTheory.lintegral_const_mul _ hkernelMeas,
      lintegral_unit_endpoint_priority_event]
    rw [← ENNReal.ofReal_mul (Real.log_nonneg
      (by norm_num : (1 : ℝ) ≤ 3 / 2))]
    congr 1
    ring
  calc
    _ = (∫⁻ x : I,
          (∫⁻ z, prefixPairWindowLogNN leftLen rightLen
              (pairedPrefixVector leftLen rightLen z)
              ∂(InfiniteDummyPairMeasure x)) + penalty x ∂volume) := by
      rw [MeasureTheory.lintegral_add_right _ hpenaltyMeas]
      rw [hpenaltyIntegral]
      rfl
    _ ≤ (∫⁻ x : I,
          ∑' k : Nat, ENNReal.ofReal (geometricLogTerm k (x : ℝ))
          ∂volume) := by
      apply MeasureTheory.lintegral_mono_ae
      filter_upwards [MeasureTheory.volume.ae_ne (0 : I)] with x hx
      exact lintegral_right_endpoint_payment hx leftLen rightLen hright
    _ = _ := lintegral_unit_geometricSeries_eq_ofReal

theorem finitePrefixCost_add_endpointPayment_le_of_left
    (leftLen rightLen : Nat) (hleft : leftLen ≤ 1) :
    finitePrefixCost leftLen rightLen +
        Real.log ((3 : ℝ) / 2) / 30 ≤ geometricLogSeries := by
  have hNN := finitePrefixCostNN_add_endpointPayment_le_of_left
    leftLen rightLen hleft
  have hsumTop : finitePrefixCostNN leftLen rightLen +
      ENNReal.ofReal (Real.log ((3 : ℝ) / 2) / 30) ≠ ⊤ := by
    apply ne_of_lt
    exact lt_of_le_of_lt hNN (ENNReal.ofReal_lt_top)
  have hfinTop : finitePrefixCostNN leftLen rightLen ≠ ⊤ :=
    (ENNReal.add_ne_top.mp hsumTop).1
  have hpayTop : ENNReal.ofReal (Real.log ((3 : ℝ) / 2) / 30) ≠ ⊤ :=
    ENNReal.ofReal_ne_top
  have hreal := (ENNReal.toReal_le_toReal hsumTop ENNReal.ofReal_ne_top).2 hNN
  rw [ENNReal.toReal_add hfinTop hpayTop,
    ENNReal.toReal_ofReal (div_nonneg
      (Real.log_nonneg (by norm_num : (1 : ℝ) ≤ 3 / 2)) (by norm_num)),
    ENNReal.toReal_ofReal geometricLogSeries_nonneg] at hreal
  exact hreal

theorem finitePrefixCost_add_endpointPayment_le_of_right
    (leftLen rightLen : Nat) (hright : rightLen ≤ 1) :
    finitePrefixCost leftLen rightLen +
        Real.log ((3 : ℝ) / 2) / 30 ≤ geometricLogSeries := by
  have hNN := finitePrefixCostNN_add_endpointPayment_le_of_right
    leftLen rightLen hright
  have hsumTop : finitePrefixCostNN leftLen rightLen +
      ENNReal.ofReal (Real.log ((3 : ℝ) / 2) / 30) ≠ ⊤ := by
    apply ne_of_lt
    exact lt_of_le_of_lt hNN (ENNReal.ofReal_lt_top)
  have hfinTop : finitePrefixCostNN leftLen rightLen ≠ ⊤ :=
    (ENNReal.add_ne_top.mp hsumTop).1
  have hpayTop : ENNReal.ofReal (Real.log ((3 : ℝ) / 2) / 30) ≠ ⊤ :=
    ENNReal.ofReal_ne_top
  have hreal := (ENNReal.toReal_le_toReal hsumTop ENNReal.ofReal_ne_top).2 hNN
  rw [ENNReal.toReal_add hfinTop hpayTop,
    ENNReal.toReal_ofReal (div_nonneg
      (Real.log_nonneg (by norm_num : (1 : ℝ) ≤ 3 / 2)) (by norm_num)),
    ENNReal.toReal_ofReal geometricLogSeries_nonneg] at hreal
  exact hreal

theorem canonicalShallow_targetGeometricSlack_ge_endpointPayment
    {n : Nat} {P : ProfileCode n}
    (D : StaticWindowData P) (hstable : (stableSet P).Nonempty)
    (base : MatchingCode n) (hbase : Stable P base) (m : Fin n)
    (hshallow : canonicalShallow P hstable ⟨base, hbase⟩ m) :
    Real.log ((3 : ℝ) / 2) / 30 ≤ targetGeometricSlack D base m := by
  rw [targetGeometricSlack_eq_series_sub_finitePrefixCost_of_stable
    D base hbase m]
  let stableBase : CodedStable P := ⟨base, hbase⟩
  let j := D.center stableBase m
  have hendpoint := (canonicalShallow_iff_center_endpoint
    P hstable stableBase m (D.enumeration m) j
      (D.center_spec stableBase m)).1 hshallow
  rcases hendpoint with hleft | hright
  · have h := finitePrefixCost_add_endpointPayment_le_of_left
      j.val (D.q m - (j.val + 1)) hleft
    dsimp [stableBase, j] at h ⊢
    linarith
  · have h := finitePrefixCost_add_endpointPayment_le_of_right
      j.val (D.q m - (j.val + 1)) hright
    dsimp [stableBase, j] at h ⊢
    linarith

end

end StableMatchingsJointCharging
