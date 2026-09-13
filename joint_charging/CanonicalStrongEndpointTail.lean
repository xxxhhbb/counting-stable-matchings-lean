import «CanonicalTailChargeAverage»

/-!
# Strong endpoint payment combined with the exponential charge tail

The old shallow payment retained only the exact wait pair `(2,0)`.  Here we
use the larger cylinder event on which the short stream fails at coordinates
`0,1,2` and the other stream succeeds at coordinate `0`.  Its conditional
mass is `x(1-x)^3`, its unit-interval average is `1/20`, and on it the
infinite window is at least four while the finite endpoint window is at most
two.  Thus shallow and extra targets both pay `log 2 / 20`.
-/

namespace StableMatchingsJointCharging

open MeasureTheory ProbabilityTheory Set
open scoped unitInterval ENNReal BigOperators
open StableMatchings355 StableMatchingsEntropy StableMatchingsE2E

noncomputable section

def firstThreeFailureEvent : Set (Nat → Bool) :=
  ⋂ i ∈ Finset.range 3, failureEvent i

def leftStrongEndpointEvent : Set ((Nat → Bool) × (Nat → Bool)) :=
  firstThreeFailureEvent ×ˢ successEvent 0

def rightStrongEndpointEvent : Set ((Nat → Bool) × (Nat → Bool)) :=
  successEvent 0 ×ˢ firstThreeFailureEvent

theorem measurableSet_firstThreeFailureEvent :
    MeasurableSet firstThreeFailureEvent := by
  unfold firstThreeFailureEvent
  apply MeasurableSet.iInter
  intro i
  apply MeasurableSet.iInter
  intro _hi
  exact measurableSet_failureEvent i

theorem measurableSet_leftStrongEndpointEvent :
    MeasurableSet leftStrongEndpointEvent :=
  measurableSet_firstThreeFailureEvent.prod (measurableSet_successEvent 0)

theorem measurableSet_rightStrongEndpointEvent :
    MeasurableSet rightStrongEndpointEvent :=
  (measurableSet_successEvent 0).prod measurableSet_firstThreeFailureEvent

theorem bernoulliSequenceMeasure_firstThreeFailureEvent (x : I) :
    BernoulliSequenceMeasure x firstThreeFailureEvent =
      (unitInterval.toNNReal (unitInterval.symm x) : ENNReal) ^ 3 := by
  unfold firstThreeFailureEvent
  have hi : iIndepFun (fun i (b : Nat → Bool) => b i)
      (BernoulliSequenceMeasure x) :=
    iIndepFun_infinitePi (X := fun _ b => b) (fun _ => measurable_id)
  rw [hi.meas_biInter (fun i _ ↦ by
    exact MeasurableSpace.measurableSet_comap.mpr
      ⟨{false}, measurableSet_singleton false, rfl⟩)]
  calc
    (∏ i ∈ Finset.range 3,
        BernoulliSequenceMeasure x (failureEvent i)) =
        ∏ _i ∈ Finset.range 3,
          (unitInterval.toNNReal (unitInterval.symm x) : ENNReal) := by
      apply Finset.prod_congr rfl
      intro i hi
      exact bernoulliSequenceMeasure_failureEvent x i
    _ = (unitInterval.toNNReal (unitInterval.symm x) : ENNReal) ^ 3 := by simp

theorem infiniteDummyPairMeasure_leftStrongEndpointEvent (x : I) :
    InfiniteDummyPairMeasure x leftStrongEndpointEvent =
      ENNReal.ofReal ((1 - (x : ℝ)) ^ 3 * (x : ℝ)) := by
  unfold leftStrongEndpointEvent InfiniteDummyPairMeasure
  rw [Measure.prod_prod,
    bernoulliSequenceMeasure_firstThreeFailureEvent,
    bernoulliSequenceMeasure_successEvent]
  rw [← ENNReal.ofReal_toReal (by finiteness :
    ((unitInterval.toNNReal (unitInterval.symm x) : ENNReal) ^ 3 *
      (unitInterval.toNNReal x : ENNReal)) ≠ ⊤)]
  congr 1

theorem infiniteDummyPairMeasure_rightStrongEndpointEvent (x : I) :
    InfiniteDummyPairMeasure x rightStrongEndpointEvent =
      ENNReal.ofReal ((1 - (x : ℝ)) ^ 3 * (x : ℝ)) := by
  unfold rightStrongEndpointEvent InfiniteDummyPairMeasure
  rw [Measure.prod_prod,
    bernoulliSequenceMeasure_successEvent,
    bernoulliSequenceMeasure_firstThreeFailureEvent]
  rw [← ENNReal.ofReal_toReal (by finiteness :
    ((unitInterval.toNNReal x : ENNReal) *
      (unitInterval.toNNReal (unitInterval.symm x) : ENNReal) ^ 3) ≠ ⊤)]
  congr 1
  simp only [ENNReal.toReal_mul, ENNReal.toReal_pow, ENNReal.coe_toReal,
    unitInterval.coe_toNNReal, unitInterval.coe_symm_eq]
  ring

theorem mem_firstThreeFailureEvent_iff (b : Nat → Bool) :
    b ∈ firstThreeFailureEvent ↔ ∀ i < 3, b i = false := by
  simp [firstThreeFailureEvent, failureEvent]

theorem firstSuccess_ge_three_of_mem_firstThreeFailureEvent
    (b : Nat → Bool) (hs : hasSuccess b)
    (hb : b ∈ firstThreeFailureEvent) :
    3 ≤ firstSuccess b := by
  rw [mem_firstThreeFailureEvent_iff] at hb
  by_contra h
  have hlt : firstSuccess b < 3 := by omega
  have hfalse := hb (firstSuccess b) hlt
  have htrue := firstSuccess_spec b hs
  simp_all

theorem firstSuccess_eq_zero_of_mem_successEvent_zero
    (b : Nat → Bool) (hb : b ∈ successEvent 0) :
    firstSuccess b = 0 := by
  exact firstSuccess_eq_of_first b 0 hb (by omega)

theorem strong_endpoint_finite_width_le_two
    (shortLen otherLen : Nat) (hshort : shortLen ≤ 1)
    (shortStream otherStream : Nat → Bool)
    (hotherZero : otherStream ∈ successEvent 0) :
    markerWindowWidth (streamPrefix shortLen shortStream)
        (streamPrefix otherLen otherStream) ≤ 2 := by
  have hs := truncatedWait_le_length_succ
    (streamPrefix shortLen shortStream)
  have ho : truncatedWait (streamPrefix otherLen otherStream) ≤ 1 := by
    cases otherLen with
    | zero => simp [streamPrefix]
    | succ k =>
        refine truncatedWait_le_of_getElem_true _ 0 (by simp) ?_
        simpa [streamPrefix, successEvent] using hotherZero
  simp only [streamPrefix_length] at hs
  unfold markerWindowWidth
  omega

theorem strong_endpoint_log_gap
    (shortLen otherLen : Nat) (hshort : shortLen ≤ 1)
    (shortStream otherStream : Nat → Bool)
    (hshortSuccess : hasSuccess shortStream)
    (hshortFailure : shortStream ∈ firstThreeFailureEvent)
    (hotherZero : otherStream ∈ successEvent 0) :
    Real.log
        (geometricWindow (infiniteDummyWaitPair
          (shortStream, otherStream)) : ℝ) -
        Real.log (markerWindowWidth (streamPrefix shortLen shortStream)
          (streamPrefix otherLen otherStream) : ℝ) ≥
      Real.log 2 := by
  have hfirst : 3 ≤ firstSuccess shortStream :=
    firstSuccess_ge_three_of_mem_firstThreeFailureEvent
      shortStream hshortSuccess hshortFailure
  have hzero : firstSuccess otherStream = 0 :=
    firstSuccess_eq_zero_of_mem_successEvent_zero otherStream hotherZero
  have hinf : 4 ≤ geometricWindow
      (infiniteDummyWaitPair (shortStream, otherStream)) := by
    simp only [geometricWindow, infiniteDummyWaitPair, hzero]
    omega
  have hfin := strong_endpoint_finite_width_le_two shortLen otherLen hshort
    shortStream otherStream hotherZero
  have hspos := truncatedWait_pos (streamPrefix shortLen shortStream)
  have hopos := truncatedWait_pos (streamPrefix otherLen otherStream)
  have hfinpos : 0 < markerWindowWidth (streamPrefix shortLen shortStream)
      (streamPrefix otherLen otherStream) := by
    unfold markerWindowWidth
    omega
  have hinfpos : 0 < geometricWindow
      (infiniteDummyWaitPair (shortStream, otherStream)) := by omega
  have hratio : (2 : ℝ) *
      (markerWindowWidth (streamPrefix shortLen shortStream)
        (streamPrefix otherLen otherStream) : ℝ) ≤
      (geometricWindow (infiniteDummyWaitPair
        (shortStream, otherStream)) : ℝ) := by
    exact_mod_cast (show 2 * markerWindowWidth
      (streamPrefix shortLen shortStream) (streamPrefix otherLen otherStream) ≤
        geometricWindow (infiniteDummyWaitPair
          (shortStream, otherStream)) by omega)
  rw [← Real.log_div (by exact_mod_cast hinfpos.ne')
    (by exact_mod_cast hfinpos.ne')]
  apply Real.log_le_log (by norm_num)
  rw [le_div_iff₀ (by exact_mod_cast hfinpos)]
  simpa [mul_comm] using hratio

theorem left_strong_endpoint_pointwise_payment
    (leftLen rightLen : Nat) (hleft : leftLen ≤ 1)
    (z : (Nat → Bool) × (Nat → Bool))
    (hs : hasSuccess z.1 ∧ hasSuccess z.2)
    (hevent : z ∈ leftStrongEndpointEvent) :
    prefixPairWindowLogNN leftLen rightLen
        (pairedPrefixVector leftLen rightLen z) +
        ENNReal.ofReal (Real.log 2) ≤
      geometricWindowLogNN (infiniteDummyWaitPair z) := by
  have hgap := strong_endpoint_log_gap leftLen rightLen hleft z.1 z.2
    hs.1 hevent.1 hevent.2
  have hfinite := markerPrefixLog_nonneg leftLen rightLen z
  simp only [prefixPairWindowLogNN, pairedPrefixVector,
    ofFn_streamPrefixVector, geometricWindowLogNN]
  rw [← ENNReal.ofReal_add hfinite
    (Real.log_nonneg (by norm_num : (1 : ℝ) ≤ 2))]
  apply ENNReal.ofReal_le_ofReal
  linarith

theorem right_strong_endpoint_pointwise_payment
    (leftLen rightLen : Nat) (hright : rightLen ≤ 1)
    (z : (Nat → Bool) × (Nat → Bool))
    (hs : hasSuccess z.1 ∧ hasSuccess z.2)
    (hevent : z ∈ rightStrongEndpointEvent) :
    prefixPairWindowLogNN leftLen rightLen
        (pairedPrefixVector leftLen rightLen z) +
        ENNReal.ofReal (Real.log 2) ≤
      geometricWindowLogNN (infiniteDummyWaitPair z) := by
  have hgap := strong_endpoint_log_gap rightLen leftLen hright z.2 z.1
    hs.2 hevent.2 hevent.1
  have hfinite := markerPrefixLog_nonneg leftLen rightLen z
  have hwidthSwap : markerWindowWidth
      (streamPrefix leftLen z.1) (streamPrefix rightLen z.2) =
      markerWindowWidth (streamPrefix rightLen z.2)
        (streamPrefix leftLen z.1) := by
    simp only [markerWindowWidth]
    omega
  have hinfSwap : geometricWindow (infiniteDummyWaitPair z) =
      geometricWindow (infiniteDummyWaitPair (z.2, z.1)) := by
    simp only [geometricWindow, infiniteDummyWaitPair]
    omega
  simp only [prefixPairWindowLogNN, pairedPrefixVector,
    ofFn_streamPrefixVector, geometricWindowLogNN]
  rw [← ENNReal.ofReal_add hfinite
    (Real.log_nonneg (by norm_num : (1 : ℝ) ≤ 2))]
  apply ENNReal.ofReal_le_ofReal
  rw [hwidthSwap, hinfSwap]
  linarith

theorem lintegral_left_strong_endpoint_payment {x : I} (hx : x ≠ 0)
    (leftLen rightLen : Nat) (hleft : leftLen ≤ 1) :
    (∫⁻ z, prefixPairWindowLogNN leftLen rightLen
        (pairedPrefixVector leftLen rightLen z)
        ∂(InfiniteDummyPairMeasure x)) +
        ENNReal.ofReal (Real.log 2) *
          ENNReal.ofReal ((1 - (x : ℝ)) ^ 3 * (x : ℝ)) ≤
      ∑' k : Nat, ENNReal.ofReal (geometricLogTerm k (x : ℝ)) := by
  let finiteLog : ((Nat → Bool) × (Nat → Bool)) → ENNReal := fun z ↦
    prefixPairWindowLogNN leftLen rightLen
      (pairedPrefixVector leftLen rightLen z)
  let payment : ((Nat → Bool) × (Nat → Bool)) → ENNReal :=
    leftStrongEndpointEvent.indicator
      (fun _ ↦ ENNReal.ofReal (Real.log 2))
  have hfiniteMeas : Measurable finiteLog :=
    (measurable_prefixPairWindowLogNN _ _).comp
      (measurable_pairedPrefixVector _ _)
  have hpayMeas : Measurable payment := by
    exact measurable_const.indicator measurableSet_leftStrongEndpointEvent
  calc
    _ = ∫⁻ z, finiteLog z + payment z
          ∂(InfiniteDummyPairMeasure x) := by
      rw [MeasureTheory.lintegral_add_left hfiniteMeas]
      unfold payment
      rw [MeasureTheory.lintegral_indicator measurableSet_leftStrongEndpointEvent,
        MeasureTheory.setLIntegral_const,
        infiniteDummyPairMeasure_leftStrongEndpointEvent]
    _ ≤ ∫⁻ z, geometricWindowLogNN (infiniteDummyWaitPair z)
          ∂(InfiniteDummyPairMeasure x) := by
      apply MeasureTheory.lintegral_mono_ae
      filter_upwards [ae_infiniteDummyPair_hasSuccess hx,
        ae_markerWindowWidth_prefix_le_geometricWindow hx leftLen rightLen]
          with z hs hdom
      by_cases hevent : z ∈ leftStrongEndpointEvent
      · simpa [finiteLog, payment, Set.indicator_of_mem hevent] using
          left_strong_endpoint_pointwise_payment
            leftLen rightLen hleft z hs hevent
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

theorem lintegral_right_strong_endpoint_payment {x : I} (hx : x ≠ 0)
    (leftLen rightLen : Nat) (hright : rightLen ≤ 1) :
    (∫⁻ z, prefixPairWindowLogNN leftLen rightLen
        (pairedPrefixVector leftLen rightLen z)
        ∂(InfiniteDummyPairMeasure x)) +
        ENNReal.ofReal (Real.log 2) *
          ENNReal.ofReal ((1 - (x : ℝ)) ^ 3 * (x : ℝ)) ≤
      ∑' k : Nat, ENNReal.ofReal (geometricLogTerm k (x : ℝ)) := by
  let finiteLog : ((Nat → Bool) × (Nat → Bool)) → ENNReal := fun z ↦
    prefixPairWindowLogNN leftLen rightLen
      (pairedPrefixVector leftLen rightLen z)
  let payment : ((Nat → Bool) × (Nat → Bool)) → ENNReal :=
    rightStrongEndpointEvent.indicator
      (fun _ ↦ ENNReal.ofReal (Real.log 2))
  have hfiniteMeas : Measurable finiteLog :=
    (measurable_prefixPairWindowLogNN _ _).comp
      (measurable_pairedPrefixVector _ _)
  have hpayMeas : Measurable payment := by
    exact measurable_const.indicator measurableSet_rightStrongEndpointEvent
  calc
    _ = ∫⁻ z, finiteLog z + payment z
          ∂(InfiniteDummyPairMeasure x) := by
      rw [MeasureTheory.lintegral_add_left hfiniteMeas]
      unfold payment
      rw [MeasureTheory.lintegral_indicator measurableSet_rightStrongEndpointEvent,
        MeasureTheory.setLIntegral_const,
        infiniteDummyPairMeasure_rightStrongEndpointEvent]
    _ ≤ ∫⁻ z, geometricWindowLogNN (infiniteDummyWaitPair z)
          ∂(InfiniteDummyPairMeasure x) := by
      apply MeasureTheory.lintegral_mono_ae
      filter_upwards [ae_infiniteDummyPair_hasSuccess hx,
        ae_markerWindowWidth_prefix_le_geometricWindow hx leftLen rightLen]
          with z hs hdom
      by_cases hevent : z ∈ rightStrongEndpointEvent
      · simpa [finiteLog, payment, Set.indicator_of_mem hevent] using
          right_strong_endpoint_pointwise_payment
            leftLen rightLen hright z hs hevent
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

theorem integral_strong_endpoint_priority_event :
    (∫ x : ℝ in 0..1, (1 - x) ^ 3 * x) = (1 : ℝ) / 20 := by
  let F : ℝ → ℝ := fun x ↦
    x ^ 2 / 2 - x ^ 3 + 3 * x ^ 4 / 4 - x ^ 5 / 5
  have hderiv : ∀ x : ℝ, HasDerivAt F ((1 - x) ^ 3 * x) x := by
    intro x
    have h := ((hasDerivAt_pow 2 x).div_const (2 : ℝ)).sub
      (hasDerivAt_pow 3 x) |>.add
      ((hasDerivAt_const x 3).mul (hasDerivAt_pow 4 x) |>.div_const (4 : ℝ)) |>.sub
      ((hasDerivAt_pow 5 x).div_const (5 : ℝ))
    convert h using 1 <;> (try rfl) <;> (try dsimp [F]) <;> ring
  rw [intervalIntegral.integral_eq_sub_of_hasDerivAt_of_le (by norm_num)
    (by fun_prop) (fun x _ ↦ hderiv x)
    (((continuous_const.sub continuous_id).pow 3).mul continuous_id
      |>.intervalIntegrable 0 1)]
  norm_num [F]

theorem lintegral_unit_strong_endpoint_priority_event :
    (∫⁻ x : I,
        ENNReal.ofReal ((1 - (x : ℝ)) ^ 3 * (x : ℝ)) ∂volume) =
      ENNReal.ofReal ((1 : ℝ) / 20) := by
  let p : ℝ → ℝ := fun x ↦ (1 - x) ^ 3 * x
  have hpcont : Continuous p := by
    exact ((continuous_const.sub continuous_id).pow 3).mul continuous_id
  have hpmeas : Measurable (fun x ↦ ENNReal.ofReal (p x)) :=
    hpcont.measurable.ennreal_ofReal
  rw [lintegral_unitInterval_eq_Ioc (fun x ↦ ENNReal.ofReal (p x)) hpmeas]
  have hpint : IntegrableOn p (Set.Ioc (0 : ℝ) 1) :=
    hpcont.integrableOn_Icc.mono_set Set.Ioc_subset_Icc_self
  have hpnonneg : ∀ᵐ x ∂(volume.restrict (Set.Ioc (0 : ℝ) 1)),
      0 ≤ p x := by
    filter_upwards [ae_restrict_mem measurableSet_Ioc] with x hx
    dsimp [p]
    have hx0 : 0 ≤ x := le_of_lt hx.1
    have hx1 : x ≤ 1 := hx.2
    positivity
  rw [← MeasureTheory.ofReal_integral_eq_lintegral_ofReal hpint hpnonneg]
  rw [← intervalIntegral.integral_of_le (by norm_num : (0 : ℝ) ≤ 1)]
  rw [show (∫ x : ℝ in 0..1, p x) = (1 : ℝ) / 20 by
    simpa [p] using integral_strong_endpoint_priority_event]

theorem finitePrefixCostNN_add_strongEndpointPayment_le_of_left
    (leftLen rightLen : Nat) (hleft : leftLen ≤ 1) :
    finitePrefixCostNN leftLen rightLen +
        ENNReal.ofReal (Real.log 2 / 20) ≤
      ENNReal.ofReal geometricLogSeries := by
  let penalty : I → ENNReal := fun x ↦
    ENNReal.ofReal (Real.log 2) *
      ENNReal.ofReal ((1 - (x : ℝ)) ^ 3 * (x : ℝ))
  have hkernelMeas : Measurable (fun x : I ↦
      ENNReal.ofReal ((1 - (x : ℝ)) ^ 3 * (x : ℝ))) := by fun_prop
  have hpenaltyMeas : Measurable penalty :=
    measurable_const.mul hkernelMeas
  have hpenaltyIntegral :
      (∫⁻ x : I, penalty x ∂volume) =
        ENNReal.ofReal (Real.log 2 / 20) := by
    unfold penalty
    rw [MeasureTheory.lintegral_const_mul _ hkernelMeas,
      lintegral_unit_strong_endpoint_priority_event]
    rw [← ENNReal.ofReal_mul (Real.log_nonneg (by norm_num : (1 : ℝ) ≤ 2))]
    congr 1
    ring
  calc
    _ = (∫⁻ x : I,
          (∫⁻ z, prefixPairWindowLogNN leftLen rightLen
              (pairedPrefixVector leftLen rightLen z)
              ∂(InfiniteDummyPairMeasure x)) + penalty x ∂volume) := by
      rw [MeasureTheory.lintegral_add_right _ hpenaltyMeas,
        hpenaltyIntegral]
      rfl
    _ ≤ (∫⁻ x : I,
          ∑' k : Nat, ENNReal.ofReal (geometricLogTerm k (x : ℝ))
          ∂volume) := by
      apply MeasureTheory.lintegral_mono_ae
      filter_upwards [MeasureTheory.volume.ae_ne (0 : I)] with x hx
      exact lintegral_left_strong_endpoint_payment hx leftLen rightLen hleft
    _ = _ := lintegral_unit_geometricSeries_eq_ofReal

theorem finitePrefixCostNN_add_strongEndpointPayment_le_of_right
    (leftLen rightLen : Nat) (hright : rightLen ≤ 1) :
    finitePrefixCostNN leftLen rightLen +
        ENNReal.ofReal (Real.log 2 / 20) ≤
      ENNReal.ofReal geometricLogSeries := by
  let penalty : I → ENNReal := fun x ↦
    ENNReal.ofReal (Real.log 2) *
      ENNReal.ofReal ((1 - (x : ℝ)) ^ 3 * (x : ℝ))
  have hkernelMeas : Measurable (fun x : I ↦
      ENNReal.ofReal ((1 - (x : ℝ)) ^ 3 * (x : ℝ))) := by fun_prop
  have hpenaltyMeas : Measurable penalty :=
    measurable_const.mul hkernelMeas
  have hpenaltyIntegral :
      (∫⁻ x : I, penalty x ∂volume) =
        ENNReal.ofReal (Real.log 2 / 20) := by
    unfold penalty
    rw [MeasureTheory.lintegral_const_mul _ hkernelMeas,
      lintegral_unit_strong_endpoint_priority_event]
    rw [← ENNReal.ofReal_mul (Real.log_nonneg (by norm_num : (1 : ℝ) ≤ 2))]
    congr 1
    ring
  calc
    _ = (∫⁻ x : I,
          (∫⁻ z, prefixPairWindowLogNN leftLen rightLen
              (pairedPrefixVector leftLen rightLen z)
              ∂(InfiniteDummyPairMeasure x)) + penalty x ∂volume) := by
      rw [MeasureTheory.lintegral_add_right _ hpenaltyMeas,
        hpenaltyIntegral]
      rfl
    _ ≤ (∫⁻ x : I,
          ∑' k : Nat, ENNReal.ofReal (geometricLogTerm k (x : ℝ))
          ∂volume) := by
      apply MeasureTheory.lintegral_mono_ae
      filter_upwards [MeasureTheory.volume.ae_ne (0 : I)] with x hx
      exact lintegral_right_strong_endpoint_payment hx leftLen rightLen hright
    _ = _ := lintegral_unit_geometricSeries_eq_ofReal

theorem finitePrefixCost_add_strongEndpointPayment_le_of_left
    (leftLen rightLen : Nat) (hleft : leftLen ≤ 1) :
    finitePrefixCost leftLen rightLen + Real.log 2 / 20 ≤
      geometricLogSeries := by
  have hNN := finitePrefixCostNN_add_strongEndpointPayment_le_of_left
    leftLen rightLen hleft
  have hsumTop : finitePrefixCostNN leftLen rightLen +
      ENNReal.ofReal (Real.log 2 / 20) ≠ ⊤ := by
    apply ne_of_lt
    exact lt_of_le_of_lt hNN ENNReal.ofReal_lt_top
  have hfinTop : finitePrefixCostNN leftLen rightLen ≠ ⊤ :=
    (ENNReal.add_ne_top.mp hsumTop).1
  have hpayTop : ENNReal.ofReal (Real.log 2 / 20) ≠ ⊤ :=
    ENNReal.ofReal_ne_top
  have hreal := (ENNReal.toReal_le_toReal hsumTop ENNReal.ofReal_ne_top).2 hNN
  rw [ENNReal.toReal_add hfinTop hpayTop,
    ENNReal.toReal_ofReal (div_nonneg
      (Real.log_nonneg (by norm_num : (1 : ℝ) ≤ 2)) (by norm_num)),
    ENNReal.toReal_ofReal geometricLogSeries_nonneg] at hreal
  exact hreal

theorem finitePrefixCost_add_strongEndpointPayment_le_of_right
    (leftLen rightLen : Nat) (hright : rightLen ≤ 1) :
    finitePrefixCost leftLen rightLen + Real.log 2 / 20 ≤
      geometricLogSeries := by
  have hNN := finitePrefixCostNN_add_strongEndpointPayment_le_of_right
    leftLen rightLen hright
  have hsumTop : finitePrefixCostNN leftLen rightLen +
      ENNReal.ofReal (Real.log 2 / 20) ≠ ⊤ := by
    apply ne_of_lt
    exact lt_of_le_of_lt hNN ENNReal.ofReal_lt_top
  have hfinTop : finitePrefixCostNN leftLen rightLen ≠ ⊤ :=
    (ENNReal.add_ne_top.mp hsumTop).1
  have hpayTop : ENNReal.ofReal (Real.log 2 / 20) ≠ ⊤ :=
    ENNReal.ofReal_ne_top
  have hreal := (ENNReal.toReal_le_toReal hsumTop ENNReal.ofReal_ne_top).2 hNN
  rw [ENNReal.toReal_add hfinTop hpayTop,
    ENNReal.toReal_ofReal (div_nonneg
      (Real.log_nonneg (by norm_num : (1 : ℝ) ≤ 2)) (by norm_num)),
    ENNReal.toReal_ofReal geometricLogSeries_nonneg] at hreal
  exact hreal

theorem canonicalShallow_targetGeometricSlack_ge_strongEndpointPayment
    {n : Nat} {P : ProfileCode n}
    (D : StaticWindowData P) (hstable : (stableSet P).Nonempty)
    (base : MatchingCode n) (hbase : Stable P base) (m : Fin n)
    (hshallow : canonicalShallow P hstable ⟨base, hbase⟩ m) :
    Real.log 2 / 20 ≤ targetGeometricSlack D base m := by
  rw [targetGeometricSlack_eq_series_sub_finitePrefixCost_of_stable
    D base hbase m]
  let stableBase : CodedStable P := ⟨base, hbase⟩
  let j := D.center stableBase m
  have hendpoint := (canonicalShallow_iff_center_endpoint
    P hstable stableBase m (D.enumeration m) j
      (D.center_spec stableBase m)).1 hshallow
  rcases hendpoint with hleft | hright
  · have h := finitePrefixCost_add_strongEndpointPayment_le_of_left
      j.val (D.q m - (j.val + 1)) hleft
    dsimp [stableBase, j] at h ⊢
    linarith
  · have h := finitePrefixCost_add_strongEndpointPayment_le_of_right
      j.val (D.q m - (j.val + 1)) hright
    dsimp [stableBase, j] at h ⊢
    linarith

theorem charged_target_joint_payment_strong
    {n : Nat} {P : ProfileCode n} (hn : 5 ≤ n)
    (D : StaticWindowData P) (hstable : (stableSet P).Nonempty)
    (base : CodedStable P) (m : Fin n)
    (hcharged : m ∈ canonicalChargedMen P hstable base) :
    Real.log 2 / 20 ≤
      targetGeometricSlack D base.1 m +
        ∫ priority, targetSupportWindowGap D base priority m
          ∂(FullPriorityMeasure n) := by
  rcases (mem_canonicalChargedMen_iff P hstable base m).1 hcharged with
    hshallow | hextra
  · have hC := canonicalShallow_targetGeometricSlack_ge_strongEndpointPayment
      D hstable base.1 base.2 m hshallow
    have hB := integral_targetSupportWindowGap_nonneg D base m
    linarith
  · have hC := targetGeometricSlack_nonneg_of_stable D base.1 base.2 m
    have hB := canonicalExtra_targetSupportWindowGap_ge_extraPayment
      hn D hstable base m hextra
    linarith

theorem charged_targetJointPaymentOrZero_strong
    {n : Nat} {P : ProfileCode n} (hn : 5 ≤ n)
    (D : StaticWindowData P) (hstable : (stableSet P).Nonempty)
    (base : MatchingCode n) (hbase : Stable P base) (m : Fin n)
    (hcharged : m ∈ canonicalChargedMen P hstable ⟨base, hbase⟩) :
    Real.log 2 / 20 ≤ targetJointPaymentOrZero D base m := by
  have h := charged_target_joint_payment_strong hn D hstable
    ⟨base, hbase⟩ m hcharged
  simpa [targetJointPaymentOrZero, targetSupportWindowGapOrZero, hbase] using h

theorem charged_card_times_strongPayment_le_sum_jointPayment
    {n : Nat} {P : ProfileCode n} (hn : 5 ≤ n)
    (D : StaticWindowData P) (hstable : (stableSet P).Nonempty)
    (base : MatchingCode n) (hbase : Stable P base) :
    Real.log 2 / 20 *
        ((canonicalChargedMen P hstable ⟨base, hbase⟩).card : ℝ) ≤
      ∑ m : Fin n, targetJointPaymentOrZero D base m := by
  classical
  let charged := canonicalChargedMen P hstable ⟨base, hbase⟩
  calc
    Real.log 2 / 20 * (charged.card : ℝ) =
        ∑ _m ∈ charged, Real.log 2 / 20 := by simp [mul_comm]
    _ ≤ ∑ m ∈ charged, targetJointPaymentOrZero D base m := by
      apply Finset.sum_le_sum
      intro m hm
      exact charged_targetJointPaymentOrZero_strong
        hn D hstable base hbase m hm
    _ ≤ ∑ m ∈ (Finset.univ : Finset (Fin n)),
        targetJointPaymentOrZero D base m := by
      apply Finset.sum_le_sum_of_subset_of_nonneg (Finset.subset_univ charged)
      intro m hm hnot
      exact targetJointPaymentOrZero_nonneg_of_stable D base hbase m
    _ = _ := by simp

theorem strongPayment_times_totalCharge_le_sum_jointPayment
    {n : Nat} {P : ProfileCode n} (hn : 5 ≤ n)
    (D : StaticWindowData P) (hstable : (stableSet P).Nonempty) :
    Real.log 2 / 20 * (canonicalTotalCharge P hstable : ℝ) ≤
      ∑ base ∈ stableSet P, ∑ m : Fin n,
        targetJointPaymentOrZero D base m := by
  classical
  have hsum :
      ∑ base ∈ stableSet P,
          Real.log 2 / 20 *
            (canonicalChargedCardOrZero P hstable base : ℝ) ≤
        ∑ base ∈ stableSet P, ∑ m : Fin n,
          targetJointPaymentOrZero D base m := by
    apply Finset.sum_le_sum
    intro base hbase
    have hs := (mem_stableSet_iff P base).1 hbase
    simpa [canonicalChargedCardOrZero, hs] using
      charged_card_times_strongPayment_le_sum_jointPayment
        hn D hstable base hs
  have hcards := congrArg (fun z : Nat ↦ (z : ℝ))
    (sum_canonicalChargedCardOrZero_eq_total P hstable)
  push_cast at hcards
  calc
    Real.log 2 / 20 * (canonicalTotalCharge P hstable : ℝ) =
      Real.log 2 / 20 *
        (∑ base ∈ stableSet P,
          (canonicalChargedCardOrZero P hstable base : ℝ)) := by rw [hcards]
    _ = ∑ base ∈ stableSet P,
        Real.log 2 / 20 *
          (canonicalChargedCardOrZero P hstable base : ℝ) := by
      rw [Finset.mul_sum]
    _ ≤ _ := hsum

theorem normalized_canonical_charge_strongPayment_le_averaged_joint_slack
    {n : Nat} {P : ProfileCode n} (hn : 5 ≤ n)
    (D : StaticWindowData P) (hstable : (stableSet P).Nonempty) :
    Real.log 2 / 20 *
        ((Nat.card (CodedStable P) : ℝ)⁻¹ *
          (canonicalTotalCharge P hstable : ℝ)) ≤
      averagedTargetGeometricSlack D + averagedTargetSupportWindowSlack D := by
  rw [averaged_joint_target_slack_eq_normalized_jointPayment D,
    ← card_stableSet_eq_natCard_codedStable P]
  have hcardNonneg : 0 ≤ ((stableSet P).card : ℝ)⁻¹ := by positivity
  have hsum := strongPayment_times_totalCharge_le_sum_jointPayment
    hn D hstable
  nlinarith

def strongEightBitTailJointDelta : ℝ :=
  153 * Real.log 2 / 81920

theorem strongEightBitTailJointDelta_pos :
    0 < strongEightBitTailJointDelta := by
  unfold strongEightBitTailJointDelta
  have hlog : 0 < Real.log 2 := Real.log_pos (by norm_num)
  positivity

theorem strongEightBitTailJointDelta_le_averaged_joint_slack
    {n : Nat} {P : ProfileCode n} (hn : 36001 ≤ n)
    (D : StaticWindowData P) (hstable : (stableSet P).Nonempty) :
    (n : ℝ) * strongEightBitTailJointDelta ≤
      averagedTargetGeometricSlack D + averagedTargetSupportWindowSlack D := by
  have hcharge := canonical_normalized_average_charge_gt_153_n_over_4096
    P hstable hn
  have hlocal :=
    normalized_canonical_charge_strongPayment_le_averaged_joint_slack
      (by omega) D hstable
  have hlog : 0 ≤ Real.log 2 := Real.log_nonneg (by norm_num)
  unfold strongEightBitTailJointDelta
  calc
    (n : ℝ) * (153 * Real.log 2 / 81920) =
        Real.log 2 / 20 * ((153 : ℝ) * (n : ℝ) / 4096) := by ring
    _ ≤ Real.log 2 / 20 *
        ((Nat.card (CodedStable P) : ℝ)⁻¹ *
          (canonicalTotalCharge P hstable : ℝ)) := by gcongr
    _ ≤ _ := hlocal

theorem strongEightBitTailJointDelta_le_totalJointSlack
    {n : Nat} {P : ProfileCode n} (hn : 36001 ≤ n)
    (D : StaticWindowData P) (hstable : (stableSet P).Nonempty) :
    (n : ℝ) * strongEightBitTailJointDelta ≤ totalJointSlack P :=
  (strongEightBitTailJointDelta_le_averaged_joint_slack hn D hstable).trans
    (averaged_joint_target_slack_le_totalJointSlack D hstable)

theorem strongEightBitTailJointDelta_le_geometricLogSeries :
    strongEightBitTailJointDelta ≤ geometricLogSeries := by
  have hterm : geometricLogWeight 2 ≤ geometricLogSeries := by
    unfold geometricLogSeries
    exact summable_geometricLogWeight.le_tsum 2 fun j hj ↦
      geometricLogWeight_nonneg j
  have hlocal : strongEightBitTailJointDelta ≤ geometricLogWeight 2 := by
    unfold strongEightBitTailJointDelta geometricLogWeight
    have hlog : 0 ≤ Real.log 2 := Real.log_nonneg (by norm_num)
    norm_num
    nlinarith
  exact hlocal.trans hterm

theorem all_profiles_strongEightBitTailJointSlack
    {n : Nat} (hn : 36001 ≤ n) (P : ProfileCode n) :
    (n : ℝ) * strongEightBitTailJointDelta ≤ totalJointSlack P := by
  classical
  by_cases hz : stableCount P = 0
  · unfold totalJointSlack
    rw [hz]
    simp only [Nat.cast_zero, Real.log_zero, sub_zero]
    exact mul_le_mul_of_nonneg_left
      strongEightBitTailJointDelta_le_geometricLogSeries (Nat.cast_nonneg n)
  · have hpositive : 0 < stableCount P := Nat.pos_of_ne_zero hz
    have hstable : (stableSet P).Nonempty := by
      apply Finset.card_pos.mp
      simpa [stableCount] using hpositive
    let D : StaticWindowData P := Classical.choice (exists_staticWindowData P)
    exact strongEightBitTailJointDelta_le_totalJointSlack hn D hstable

theorem geometricLogSeries_sub_strongEightBitTailJointDelta_lt_1202271_div_million :
    geometricLogSeries - strongEightBitTailJointDelta <
      (1202271 : ℝ) / 1000000 := by
  have hS := geometricLogSeries_lt_120356492_div_100000000
  have hd := log_two_gt_693_div_1000
  unfold strongEightBitTailJointDelta
  linarith

theorem one_point_1202271_div_million_lt_log_33277_div_10000 :
    (1202271 : ℝ) / 1000000 < Real.log ((33277 : ℝ) / 10000) := by
  have h := Real.sum_range_le_log_div
    (x := (23277 : ℝ) / 43277) (by norm_num) (by norm_num) 16
  norm_num [Finset.sum_range_succ] at h
  nlinarith

theorem geometricLogSeries_sub_strongEightBitTailJointDelta_lt_log_33277_div_10000 :
    geometricLogSeries - strongEightBitTailJointDelta <
      Real.log ((33277 : ℝ) / 10000) :=
  geometricLogSeries_sub_strongEightBitTailJointDelta_lt_1202271_div_million.trans
    one_point_1202271_div_million_lt_log_33277_div_10000

theorem stableCount_lt_33277_div_10000_pow
    {n : Nat} (hn : 36001 ≤ n) (P : ProfileCode n) :
    (stableCount P : ℝ) < ((33277 : ℝ) / 10000) ^ n := by
  have hjoint := all_profiles_strongEightBitTailJointSlack hn P
  have hmain :=
    (jointSlack_linear_lower_iff_log_bound P strongEightBitTailJointDelta).1
      hjoint
  have hlog : Real.log (stableCount P) <
      (n : ℝ) * Real.log ((33277 : ℝ) / 10000) :=
    hmain.trans_lt
      (mul_lt_mul_of_pos_left
        geometricLogSeries_sub_strongEightBitTailJointDelta_lt_log_33277_div_10000
        (by positivity))
  by_cases hz : stableCount P = 0
  · rw [hz]
    norm_num only [Nat.cast_zero]
    exact pow_pos (by norm_num) n
  · have hexp := (Real.exp_lt_exp).2 hlog
    rw [Real.exp_log (by exact_mod_cast Nat.pos_of_ne_zero hz)] at hexp
    rw [Real.exp_nat_mul, Real.exp_log (by norm_num)] at hexp
    exact hexp

theorem SM_lt_33277_div_10000_pow
    (n : Nat) (hn : 36001 ≤ n) :
    (SM n : ℝ) < ((33277 : ℝ) / 10000) ^ n := by
  obtain ⟨P, hP⟩ := exists_profile_attaining_SM n
  simpa [hP] using stableCount_lt_33277_div_10000_pow hn P

/-! ## Sixteen-bit tail specialization -/

theorem normalized_average_ge_65535_over_65536_threshold
    (M bad r total : ℕ) (hM : 0 < M)
    (hbad : 65536 * bad ≤ M)
    (hcharge : (M - bad) * r ≤ total) :
    (65535 : ℝ) * (r : ℝ) / 65536 ≤
      (M : ℝ)⁻¹ * (total : ℝ) := by
  have hbadM : bad ≤ M := by omega
  have hMreal : (0 : ℝ) < (M : ℝ) := by exact_mod_cast hM
  have hbadReal : (65536 : ℝ) * (bad : ℝ) ≤ (M : ℝ) := by
    exact_mod_cast hbad
  have hchargeReal :
      ((M : ℝ) - (bad : ℝ)) * (r : ℝ) ≤ (total : ℝ) := by
    rw [← Nat.cast_sub hbadM, ← Nat.cast_mul]
    exact_mod_cast hcharge
  have hgood : (65535 : ℝ) * (M : ℝ) / 65536 ≤
      (M : ℝ) - (bad : ℝ) := by nlinarith
  have hr : 0 ≤ (r : ℝ) := by positivity
  have hmul := mul_le_mul_of_nonneg_right hgood hr
  rw [inv_mul_eq_div]
  apply (le_div_iff₀ hMreal).2
  calc
    (65535 : ℝ) * (r : ℝ) / 65536 * (M : ℝ) =
        ((65535 : ℝ) * (M : ℝ) / 65536) * (r : ℝ) := by ring
    _ ≤ ((M : ℝ) - (bad : ℝ)) * (r : ℝ) := hmul
    _ ≤ (total : ℝ) := hchargeReal

theorem normalized_average_gt_39321_n_over_1048576
    (n M bad total : ℕ) (hM : 0 < M)
    (hbad : 65536 * bad ≤ M)
    (hcharge : (M - bad) * ((3 * n) / 80 + 1) ≤ total) :
    (39321 : ℝ) * (n : ℝ) / 1048576 <
      (M : ℝ)⁻¹ * (total : ℝ) := by
  have havg := normalized_average_ge_65535_over_65536_threshold
    M bad ((3 * n) / 80 + 1) total hM hbad hcharge
  have hfloor := three_n_div_eighty_lt_floor_succ n
  nlinarith

theorem canonical_normalized_average_charge_gt_39321_n_over_1048576
    {n : Nat} (P : ProfileCode n)
    (hstable : (stableSet P).Nonempty) (hn : 68001 ≤ n) :
    (39321 : ℝ) * (n : ℝ) / 1048576 <
      (Nat.card (CodedStable P) : ℝ)⁻¹ *
        (canonicalTotalCharge P hstable : ℝ) := by
  let mu := Classical.choose hstable
  have hmu : mu ∈ stableSet P := Classical.choose_spec hstable
  letI : Nonempty (CodedStable P) :=
    ⟨⟨mu, (mem_stableSet_iff P mu).1 hmu⟩⟩
  have hM : 0 < Nat.card (CodedStable P) := Nat.card_pos
  apply normalized_average_gt_39321_n_over_1048576 n
    (Nat.card (CodedStable P))
    (Nat.card (CanonicalLowChargeSource P hstable ((3 * n) / 80)))
    (canonicalTotalCharge P hstable) hM
  · simpa using canonical_low_charge_pow_two_optimized 16 P hstable (by omega)
  · exact canonical_good_sources_pay_threshold P hstable ((3 * n) / 80)

def strongSixteenBitTailJointDelta : ℝ :=
  39321 * Real.log 2 / 20971520

theorem strongSixteenBitTailJointDelta_pos :
    0 < strongSixteenBitTailJointDelta := by
  unfold strongSixteenBitTailJointDelta
  have hlog : 0 < Real.log 2 := Real.log_pos (by norm_num)
  positivity

theorem strongSixteenBitTailJointDelta_le_averaged_joint_slack
    {n : Nat} {P : ProfileCode n} (hn : 68001 ≤ n)
    (D : StaticWindowData P) (hstable : (stableSet P).Nonempty) :
    (n : ℝ) * strongSixteenBitTailJointDelta ≤
      averagedTargetGeometricSlack D + averagedTargetSupportWindowSlack D := by
  have hcharge :=
    canonical_normalized_average_charge_gt_39321_n_over_1048576
      P hstable hn
  have hlocal :=
    normalized_canonical_charge_strongPayment_le_averaged_joint_slack
      (by omega) D hstable
  have hlog : 0 ≤ Real.log 2 := Real.log_nonneg (by norm_num)
  unfold strongSixteenBitTailJointDelta
  calc
    (n : ℝ) * (39321 * Real.log 2 / 20971520) =
        Real.log 2 / 20 * ((39321 : ℝ) * (n : ℝ) / 1048576) := by ring
    _ ≤ Real.log 2 / 20 *
        ((Nat.card (CodedStable P) : ℝ)⁻¹ *
          (canonicalTotalCharge P hstable : ℝ)) := by gcongr
    _ ≤ _ := hlocal

theorem strongSixteenBitTailJointDelta_le_totalJointSlack
    {n : Nat} {P : ProfileCode n} (hn : 68001 ≤ n)
    (D : StaticWindowData P) (hstable : (stableSet P).Nonempty) :
    (n : ℝ) * strongSixteenBitTailJointDelta ≤ totalJointSlack P :=
  (strongSixteenBitTailJointDelta_le_averaged_joint_slack hn D hstable).trans
    (averaged_joint_target_slack_le_totalJointSlack D hstable)

theorem strongSixteenBitTailJointDelta_le_geometricLogSeries :
    strongSixteenBitTailJointDelta ≤ geometricLogSeries := by
  have hterm : geometricLogWeight 2 ≤ geometricLogSeries := by
    unfold geometricLogSeries
    exact summable_geometricLogWeight.le_tsum 2 fun j hj ↦
      geometricLogWeight_nonneg j
  have hlocal : strongSixteenBitTailJointDelta ≤ geometricLogWeight 2 := by
    unfold strongSixteenBitTailJointDelta geometricLogWeight
    have hlog : 0 ≤ Real.log 2 := Real.log_nonneg (by norm_num)
    norm_num
    nlinarith
  exact hlocal.trans hterm

theorem all_profiles_strongSixteenBitTailJointSlack
    {n : Nat} (hn : 68001 ≤ n) (P : ProfileCode n) :
    (n : ℝ) * strongSixteenBitTailJointDelta ≤ totalJointSlack P := by
  classical
  by_cases hz : stableCount P = 0
  · unfold totalJointSlack
    rw [hz]
    simp only [Nat.cast_zero, Real.log_zero, sub_zero]
    exact mul_le_mul_of_nonneg_left
      strongSixteenBitTailJointDelta_le_geometricLogSeries (Nat.cast_nonneg n)
  · have hpositive : 0 < stableCount P := Nat.pos_of_ne_zero hz
    have hstable : (stableSet P).Nonempty := by
      apply Finset.card_pos.mp
      simpa [stableCount] using hpositive
    let D : StaticWindowData P := Classical.choice (exists_staticWindowData P)
    exact strongSixteenBitTailJointDelta_le_totalJointSlack hn D hstable

theorem geometricLogSeries_sub_strongSixteenBitTailJointDelta_lt_751416_div_625000 :
    geometricLogSeries - strongSixteenBitTailJointDelta <
      (751416 : ℝ) / 625000 := by
  have hS := geometricLogSeries_lt_120356492_div_100000000
  have hd := log_two_gt_693_div_1000
  unfold strongSixteenBitTailJointDelta
  linarith

theorem one_point_751416_div_625000_lt_log_66553_div_20000 :
    (751416 : ℝ) / 625000 < Real.log ((66553 : ℝ) / 20000) := by
  have h := Real.sum_range_le_log_div
    (x := (46553 : ℝ) / 86553) (by norm_num) (by norm_num) 16
  norm_num [Finset.sum_range_succ] at h
  nlinarith

theorem geometricLogSeries_sub_strongSixteenBitTailJointDelta_lt_log_66553_div_20000 :
    geometricLogSeries - strongSixteenBitTailJointDelta <
      Real.log ((66553 : ℝ) / 20000) :=
  geometricLogSeries_sub_strongSixteenBitTailJointDelta_lt_751416_div_625000.trans
    one_point_751416_div_625000_lt_log_66553_div_20000

theorem stableCount_lt_66553_div_20000_pow
    {n : Nat} (hn : 68001 ≤ n) (P : ProfileCode n) :
    (stableCount P : ℝ) < ((66553 : ℝ) / 20000) ^ n := by
  have hjoint := all_profiles_strongSixteenBitTailJointSlack hn P
  have hmain :=
    (jointSlack_linear_lower_iff_log_bound P strongSixteenBitTailJointDelta).1
      hjoint
  have hlog : Real.log (stableCount P) <
      (n : ℝ) * Real.log ((66553 : ℝ) / 20000) :=
    hmain.trans_lt
      (mul_lt_mul_of_pos_left
        geometricLogSeries_sub_strongSixteenBitTailJointDelta_lt_log_66553_div_20000
        (by positivity))
  by_cases hz : stableCount P = 0
  · rw [hz]
    norm_num only [Nat.cast_zero]
    exact pow_pos (by norm_num) n
  · have hexp := (Real.exp_lt_exp).2 hlog
    rw [Real.exp_log (by exact_mod_cast Nat.pos_of_ne_zero hz)] at hexp
    rw [Real.exp_nat_mul, Real.exp_log (by norm_num)] at hexp
    exact hexp

theorem SM_lt_66553_div_20000_pow
    (n : Nat) (hn : 68001 ≤ n) :
    (SM n : ℝ) < ((66553 : ℝ) / 20000) ^ n := by
  obtain ⟨P, hP⟩ := exists_profile_attaining_SM n
  simpa [hP] using stableCount_lt_66553_div_20000_pow hn P

/-! ## Near-critical charge threshold `47/1250 = 0.0376` -/

theorem log_two_gt_6931471_div_ten_million :
    (6931471 : ℝ) / 10000000 < Real.log 2 := by
  have h := Real.sum_range_le_log_div
    (x := (1 : ℝ) / 3) (by norm_num) (by norm_num) 8
  norm_num [Finset.sum_range_succ] at h
  nlinarith

theorem log_1250_div_47_upper :
    Real.log ((1250 : ℝ) / 47) ≤
      4 * ((6931472 : ℝ) / 10000000) +
        2 * atanhUpper14 ((1 : ℝ) / 9) +
        atanhUpper14 ((3 : ℝ) / 97) := by
  have h2 := log_two_lt_6931472_div_ten_million.le
  have h54 := log_one_add_inv_le_atanhUpper14 4 (by norm_num)
  have h5047 : Real.log ((50 : ℝ) / 47) ≤
      atanhUpper14 ((3 : ℝ) / 97) := by
    have hx0 : (0 : ℝ) ≤ 3 / 97 := by norm_num
    have hx1 : (3 : ℝ) / 97 < 1 := by norm_num
    have h := Real.log_div_le_sum_range_add hx0 hx1 14
    have hratio :
        (1 + (3 : ℝ) / 97) / (1 - (3 : ℝ) / 97) =
          (50 : ℝ) / 47 := by norm_num
    rw [hratio] at h
    change Real.log ((50 : ℝ) / 47) ≤ atanhUpper14 ((3 : ℝ) / 97)
    unfold atanhUpper14
    norm_num at h ⊢
    linarith
  have hdecomp : Real.log ((1250 : ℝ) / 47) =
      4 * Real.log 2 + 2 * Real.log ((5 : ℝ) / 4) +
        Real.log ((50 : ℝ) / 47) := by
    rw [show (1250 : ℝ) / 47 =
      2 ^ 4 * ((5 : ℝ) / 4) ^ 2 * ((50 : ℝ) / 47) by norm_num]
    rw [Real.log_mul (by norm_num) (by norm_num),
      Real.log_mul (by norm_num) (by norm_num), Real.log_pow, Real.log_pow]
    norm_num
  rw [hdecomp]
  nlinarith

theorem log_1250_div_1203_upper :
    Real.log ((1250 : ℝ) / 1203) ≤
      atanhUpper14 ((47 : ℝ) / 2453) := by
  have hx0 : (0 : ℝ) ≤ 47 / 2453 := by norm_num
  have hx1 : (47 : ℝ) / 2453 < 1 := by norm_num
  have h := Real.log_div_le_sum_range_add hx0 hx1 14
  have hratio :
      (1 + (47 : ℝ) / 2453) / (1 - (47 : ℝ) / 2453) =
        (1250 : ℝ) / 1203 := by norm_num
  rw [hratio] at h
  change Real.log ((1250 : ℝ) / 1203) ≤
    atanhUpper14 ((47 : ℝ) / 2453)
  unfold atanhUpper14
  norm_num at h ⊢
  linarith

theorem binEntropy_47_over_1250_lt_11559_over_50000_log_two :
    Real.binEntropy ((47 : ℝ) / 1250) <
      ((11559 : ℝ) / 50000) * Real.log 2 := by
  have h1 := log_1250_div_47_upper
  have h2 := log_1250_div_1203_upper
  have hlog := log_two_gt_6931471_div_ten_million
  norm_num [atanhUpper14, Finset.sum_range_succ] at h1 h2
  rw [Real.binEntropy]
  have hinv47 : ((47 : ℝ) / 1250)⁻¹ = (1250 : ℝ) / 47 := by norm_num
  have hinv1203 : (1 - (47 : ℝ) / 1250)⁻¹ =
      (1250 : ℝ) / 1203 := by norm_num
  rw [hinv47, hinv1203]
  nlinarith

theorem deletion_entropy_margin_47_over_1250_quantitative :
    ((1 : ℝ) / 50000) * Real.log 2 <
      ((1 : ℝ) / 4 - ((47 : ℝ) / 1250) / 2) * Real.log 2 -
        Real.binEntropy ((47 : ℝ) / 1250) := by
  have h := binEntropy_47_over_1250_lt_11559_over_50000_log_two
  have hlog : 0 < Real.log 2 := Real.log_pos (by norm_num)
  nlinarith

theorem inv_bernoulliWeight_47_over_1250_eq_exp
    (n k : ℕ) :
    1 / bernoulliWeight ((47 : ℝ) / 1250) n k =
      Real.exp
        ((k : ℝ) * Real.log ((1250 : ℝ) / 47) +
          ((n - k : ℕ) : ℝ) * Real.log ((1250 : ℝ) / 1203)) := by
  rw [Real.exp_add]
  have h1 : (0 : ℝ) < (1250 : ℝ) / 47 := by norm_num
  have h2 : (0 : ℝ) < (1250 : ℝ) / 1203 := by norm_num
  have hk : Real.exp ((k : ℝ) * Real.log ((1250 : ℝ) / 47)) =
      ((1250 : ℝ) / 47) ^ k := by
    rw [Real.exp_nat_mul, Real.exp_log h1]
  have hnk : Real.exp (((n - k : ℕ) : ℝ) *
      Real.log ((1250 : ℝ) / 1203)) =
      ((1250 : ℝ) / 1203) ^ (n - k) := by
    rw [Real.exp_nat_mul, Real.exp_log h2]
  rw [hk, hnk]
  unfold bernoulliWeight
  norm_num [one_div, div_pow]
  ring

theorem exponent_47_over_1250_le_binEntropy
    {n k : ℕ} (hkn : 1250 * k ≤ 47 * n) :
    (k : ℝ) * Real.log ((1250 : ℝ) / 47) +
        ((n - k : ℕ) : ℝ) * Real.log ((1250 : ℝ) / 1203) ≤
      (n : ℝ) * Real.binEntropy ((47 : ℝ) / 1250) := by
  have hk : k ≤ n := by omega
  have hcast : (1250 : ℝ) * (k : ℝ) ≤ 47 * (n : ℝ) := by
    exact_mod_cast hkn
  have hsub : ((n - k : ℕ) : ℝ) = (n : ℝ) - (k : ℝ) := Nat.cast_sub hk
  have hlog : Real.log ((1250 : ℝ) / 1203) ≤
      Real.log ((1250 : ℝ) / 47) := by
    exact Real.strictMonoOn_log.monotoneOn (by norm_num) (by norm_num) (by norm_num)
  have hentropy : Real.binEntropy ((47 : ℝ) / 1250) =
      ((47 : ℝ) / 1250) * Real.log ((1250 : ℝ) / 47) +
        ((1203 : ℝ) / 1250) * Real.log ((1250 : ℝ) / 1203) := by
    rw [Real.binEntropy]
    norm_num
  rw [hsub, hentropy]
  nlinarith

theorem choose_prefix_le_exp_binEntropy_47_over_1250
    {n k : ℕ} (hkn : 1250 * k ≤ 47 * n) :
    (∑ i ∈ Finset.range (k + 1), (n.choose i : ℝ)) ≤
      Real.exp ((n : ℝ) * Real.binEntropy ((47 : ℝ) / 1250)) := by
  have hk : k ≤ n := by omega
  calc
    (∑ i ∈ Finset.range (k + 1), (n.choose i : ℝ)) ≤
        1 / bernoulliWeight ((47 : ℝ) / 1250) n k := by
      exact choose_prefix_le_inv_bernoulliWeight (by norm_num) (by norm_num) hk
    _ = Real.exp
          ((k : ℝ) * Real.log ((1250 : ℝ) / 47) +
            ((n - k : ℕ) : ℝ) * Real.log ((1250 : ℝ) / 1203)) :=
      inv_bernoulliWeight_47_over_1250_eq_exp n k
    _ ≤ Real.exp ((n : ℝ) * Real.binEntropy ((47 : ℝ) / 1250)) := by
      exact Real.exp_le_exp.mpr (exponent_47_over_1250_le_binEntropy hkn)

theorem boundary_budget_47_over_1250_pow_two {n : Nat}
    (s : Nat) (hn : 50000 * (s + 1) + 1 ≤ n) :
    2 ^ s * (2 ^ (n / 4) *
        (∑ i ∈ Finset.range ((47 * n) / 1250 + 1), n.choose i)) ≤
      2 ^ ((n - (47 * n) / 1250) / 2) := by
  let k := (47 * n) / 1250
  let a := n / 4
  let r := (n - k) / 2
  let B := ∑ i ∈ Finset.range (k + 1), n.choose i
  have hk : 1250 * k ≤ 47 * n := by
    dsimp [k]
    omega
  have hprefix := choose_prefix_le_exp_binEntropy_47_over_1250
    (n := n) (k := k) hk
  have hmargin := deletion_entropy_margin_47_over_1250_quantitative
  have hlog : 0 < Real.log 2 := Real.log_pos (by norm_num)
  have ha : (a : ℝ) ≤ (n : ℝ) / 4 := by
    dsimp [a]
    have hnat : 4 * (n / 4) ≤ n := by omega
    have hcast : ((4 * (n / 4) : Nat) : ℝ) ≤ (n : ℝ) := by
      exact_mod_cast hnat
    norm_num only [Nat.cast_mul, Nat.cast_ofNat] at hcast
    nlinarith
  have hkreal : (k : ℝ) ≤ (47 : ℝ) * (n : ℝ) / 1250 := by
    have hcast : ((1250 * k : Nat) : ℝ) ≤ ((47 * n : Nat) : ℝ) := by
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
  have hnreal : ((50000 * (s + 1) + 1 : Nat) : ℝ) ≤ (n : ℝ) := by
    exact_mod_cast hn
  push_cast at hnreal
  have hbudget : ((s : ℝ) + 1) * Real.log 2 <
      (n : ℝ) / 50000 * Real.log 2 := by
    have hnum : (s : ℝ) + 1 < (n : ℝ) / 50000 := by nlinarith
    exact mul_lt_mul_of_pos_right hnum hlog
  have hexponent :
      (s : ℝ) * Real.log 2 + (a : ℝ) * Real.log 2 +
          (n : ℝ) * Real.binEntropy ((47 : ℝ) / 1250) <
        (r : ℝ) * Real.log 2 := by
    have hmarginN :
        (n : ℝ) * Real.binEntropy ((47 : ℝ) / 1250) <
          (n : ℝ) * (((1 : ℝ) / 4 - ((47 : ℝ) / 1250) / 2) *
            Real.log 2 - ((1 : ℝ) / 50000) * Real.log 2) := by
      have hnNat : 0 < n := by omega
      have hnpos : (0 : ℝ) < (n : ℝ) := by exact_mod_cast hnNat
      nlinarith
    nlinarith
  have hB : (B : ℝ) ≤
      Real.exp ((n : ℝ) * Real.binEntropy ((47 : ℝ) / 1250)) := by
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
                Real.binEntropy ((47 : ℝ) / 1250))) := by gcongr
      _ = Real.exp ((s : ℝ) * Real.log 2 + (a : ℝ) * Real.log 2 +
          (n : ℝ) * Real.binEntropy ((47 : ℝ) / 1250)) := by
        rw [← Real.exp_add, ← Real.exp_add]
        congr 1
        ring
      _ < Real.exp ((r : ℝ) * Real.log 2) :=
        Real.exp_lt_exp.mpr hexponent
  have hnat : 2 ^ s * (2 ^ a * B) < 2 ^ r := by exact_mod_cast hreal
  dsimp [a, B, r, k] at hnat ⊢
  omega

theorem canonical_low_charge_47_over_1250_pow_two {n : Nat}
    (s : Nat) (P : ProfileCode n) (hstable : (stableSet P).Nonempty)
    (hn : 50000 * (s + 1) + 1 ≤ n) :
    2 ^ s * Nat.card
        (CanonicalLowChargeSource P hstable ((47 * n) / 1250)) ≤
      Nat.card (CodedStable P) := by
  let k := (47 * n) / 1250
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
  · simpa [Q, k] using boundary_budget_47_over_1250_pow_two s hn

theorem fortyseven_n_div_1250_lt_floor_succ (n : ℕ) :
    (47 : ℝ) * (n : ℝ) / 1250 <
      (((47 * n) / 1250 + 1 : ℕ) : ℝ) := by
  have hrem : 47 * n < 1250 * ((47 * n) / 1250 + 1) := by omega
  have hcast : (47 * n : ℝ) <
      (1250 * ((47 * n) / 1250 + 1) : ℕ) := by exact_mod_cast hrem
  push_cast at hcast
  rw [div_lt_iff₀ (by norm_num : (0 : ℝ) < 1250)]
  push_cast
  nlinarith

theorem normalized_average_gt_616029_n_over_16384000
    (n M bad total : ℕ) (hM : 0 < M)
    (hbad : 65536 * bad ≤ M)
    (hcharge : (M - bad) * ((47 * n) / 1250 + 1) ≤ total) :
    (616029 : ℝ) * (n : ℝ) / 16384000 <
      (M : ℝ)⁻¹ * (total : ℝ) := by
  have havg := normalized_average_ge_65535_over_65536_threshold
    M bad ((47 * n) / 1250 + 1) total hM hbad hcharge
  have hfloor := fortyseven_n_div_1250_lt_floor_succ n
  nlinarith

theorem canonical_normalized_average_charge_gt_616029_n_over_16384000
    {n : Nat} (P : ProfileCode n)
    (hstable : (stableSet P).Nonempty) (hn : 850001 ≤ n) :
    (616029 : ℝ) * (n : ℝ) / 16384000 <
      (Nat.card (CodedStable P) : ℝ)⁻¹ *
        (canonicalTotalCharge P hstable : ℝ) := by
  let mu := Classical.choose hstable
  have hmu : mu ∈ stableSet P := Classical.choose_spec hstable
  letI : Nonempty (CodedStable P) :=
    ⟨⟨mu, (mem_stableSet_iff P mu).1 hmu⟩⟩
  have hM : 0 < Nat.card (CodedStable P) := Nat.card_pos
  apply normalized_average_gt_616029_n_over_16384000 n
    (Nat.card (CodedStable P))
    (Nat.card (CanonicalLowChargeSource P hstable ((47 * n) / 1250)))
    (canonicalTotalCharge P hstable) hM
  · simpa using canonical_low_charge_47_over_1250_pow_two
      16 P hstable (by omega)
  · exact canonical_good_sources_pay_threshold
      P hstable ((47 * n) / 1250)

def nearCriticalStrongTailJointDelta : ℝ :=
  616029 * Real.log 2 / 327680000

theorem nearCriticalStrongTailJointDelta_pos :
    0 < nearCriticalStrongTailJointDelta := by
  unfold nearCriticalStrongTailJointDelta
  have hlog : 0 < Real.log 2 := Real.log_pos (by norm_num)
  positivity

theorem nearCriticalStrongTailJointDelta_le_averaged_joint_slack
    {n : Nat} {P : ProfileCode n} (hn : 850001 ≤ n)
    (D : StaticWindowData P) (hstable : (stableSet P).Nonempty) :
    (n : ℝ) * nearCriticalStrongTailJointDelta ≤
      averagedTargetGeometricSlack D + averagedTargetSupportWindowSlack D := by
  have hcharge :=
    canonical_normalized_average_charge_gt_616029_n_over_16384000
      P hstable hn
  have hlocal :=
    normalized_canonical_charge_strongPayment_le_averaged_joint_slack
      (by omega) D hstable
  have hlog : 0 ≤ Real.log 2 := Real.log_nonneg (by norm_num)
  unfold nearCriticalStrongTailJointDelta
  calc
    (n : ℝ) * (616029 * Real.log 2 / 327680000) =
        Real.log 2 / 20 *
          ((616029 : ℝ) * (n : ℝ) / 16384000) := by ring
    _ ≤ Real.log 2 / 20 *
        ((Nat.card (CodedStable P) : ℝ)⁻¹ *
          (canonicalTotalCharge P hstable : ℝ)) := by gcongr
    _ ≤ _ := hlocal

theorem nearCriticalStrongTailJointDelta_le_totalJointSlack
    {n : Nat} {P : ProfileCode n} (hn : 850001 ≤ n)
    (D : StaticWindowData P) (hstable : (stableSet P).Nonempty) :
    (n : ℝ) * nearCriticalStrongTailJointDelta ≤ totalJointSlack P :=
  (nearCriticalStrongTailJointDelta_le_averaged_joint_slack hn D hstable).trans
    (averaged_joint_target_slack_le_totalJointSlack D hstable)

theorem nearCriticalStrongTailJointDelta_le_geometricLogSeries :
    nearCriticalStrongTailJointDelta ≤ geometricLogSeries := by
  have hterm : geometricLogWeight 2 ≤ geometricLogSeries := by
    unfold geometricLogSeries
    exact summable_geometricLogWeight.le_tsum 2 fun j hj ↦
      geometricLogWeight_nonneg j
  have hlocal : nearCriticalStrongTailJointDelta ≤ geometricLogWeight 2 := by
    unfold nearCriticalStrongTailJointDelta geometricLogWeight
    have hlog : 0 ≤ Real.log 2 := Real.log_nonneg (by norm_num)
    norm_num
    nlinarith
  exact hlocal.trans hterm

theorem all_profiles_nearCriticalStrongTailJointSlack
    {n : Nat} (hn : 850001 ≤ n) (P : ProfileCode n) :
    (n : ℝ) * nearCriticalStrongTailJointDelta ≤ totalJointSlack P := by
  classical
  by_cases hz : stableCount P = 0
  · unfold totalJointSlack
    rw [hz]
    simp only [Nat.cast_zero, Real.log_zero, sub_zero]
    exact mul_le_mul_of_nonneg_left
      nearCriticalStrongTailJointDelta_le_geometricLogSeries (Nat.cast_nonneg n)
  · have hpositive : 0 < stableCount P := Nat.pos_of_ne_zero hz
    have hstable : (stableSet P).Nonempty := by
      apply Finset.card_pos.mp
      simpa [stableCount] using hpositive
    let D : StaticWindowData P := Classical.choice (exists_staticWindowData P)
    exact nearCriticalStrongTailJointDelta_le_totalJointSlack hn D hstable

theorem geometricLogSeries_sub_nearCriticalStrongTailJointDelta_lt_6011311_div_5000000 :
    geometricLogSeries - nearCriticalStrongTailJointDelta <
      (6011311 : ℝ) / 5000000 := by
  have hS := geometricLogSeries_lt_120356492_div_100000000
  have hd := log_two_gt_693_div_1000
  unfold nearCriticalStrongTailJointDelta
  linarith

theorem one_point_6011311_div_5000000_lt_log_83191_div_25000 :
    (6011311 : ℝ) / 5000000 < Real.log ((83191 : ℝ) / 25000) := by
  have h := Real.sum_range_le_log_div
    (x := (58191 : ℝ) / 108191) (by norm_num) (by norm_num) 16
  norm_num [Finset.sum_range_succ] at h
  nlinarith

theorem geometricLogSeries_sub_nearCriticalStrongTailJointDelta_lt_log_83191_div_25000 :
    geometricLogSeries - nearCriticalStrongTailJointDelta <
      Real.log ((83191 : ℝ) / 25000) :=
  geometricLogSeries_sub_nearCriticalStrongTailJointDelta_lt_6011311_div_5000000.trans
    one_point_6011311_div_5000000_lt_log_83191_div_25000

theorem stableCount_lt_83191_div_25000_pow
    {n : Nat} (hn : 850001 ≤ n) (P : ProfileCode n) :
    (stableCount P : ℝ) < ((83191 : ℝ) / 25000) ^ n := by
  have hjoint := all_profiles_nearCriticalStrongTailJointSlack hn P
  have hmain :=
    (jointSlack_linear_lower_iff_log_bound P nearCriticalStrongTailJointDelta).1
      hjoint
  have hlog : Real.log (stableCount P) <
      (n : ℝ) * Real.log ((83191 : ℝ) / 25000) :=
    hmain.trans_lt
      (mul_lt_mul_of_pos_left
        geometricLogSeries_sub_nearCriticalStrongTailJointDelta_lt_log_83191_div_25000
        (by positivity))
  by_cases hz : stableCount P = 0
  · rw [hz]
    norm_num only [Nat.cast_zero]
    exact pow_pos (by norm_num) n
  · have hexp := (Real.exp_lt_exp).2 hlog
    rw [Real.exp_log (by exact_mod_cast Nat.pos_of_ne_zero hz)] at hexp
    rw [Real.exp_nat_mul, Real.exp_log (by norm_num)] at hexp
    exact hexp

theorem SM_lt_83191_div_25000_pow
    (n : Nat) (hn : 850001 ≤ n) :
    (SM n : ℝ) < ((83191 : ℝ) / 25000) ^ n := by
  obtain ⟨P, hP⟩ := exists_profile_attaining_SM n
  simpa [hP] using stableCount_lt_83191_div_25000_pow hn P

end

end StableMatchingsJointCharging
