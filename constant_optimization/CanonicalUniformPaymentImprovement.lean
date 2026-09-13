import «CanonicalStrongEndpointTail»

/-!
# Uniform local-payment improvement

The old extra event fixed a padding bit that is not used by the pointwise gap
argument.  Freeing that bit enlarges its integrated mass from `1/20` to
`1/12`.  This file first formalizes that extra-target improvement.
-/

namespace StableMatchingsJointCharging

open MeasureTheory ProbabilityTheory Set
open scoped unitInterval ENNReal BigOperators
open StableMatchings355 StableMatchingsEntropy StableMatchingsE2E

noncomputable section

def reducedExtraPriorityPatternSet : Set (Fin 4 → Bool) :=
  {b | b 0 = true ∧ b 1 = true ∧ b 3 = false}

theorem measurableSet_reducedExtraPriorityPatternSet :
    MeasurableSet reducedExtraPriorityPatternSet := by
  unfold reducedExtraPriorityPatternSet
  change MeasurableSet
    ({b : Fin 4 → Bool | b 0 = true} ∩
      ({b : Fin 4 → Bool | b 1 = true} ∩
        {b : Fin 4 → Bool | b 3 = false}))
  exact
    ((measurableSet_singleton (true : Bool)).preimage
      (measurable_pi_apply (0 : Fin 4))).inter
      (((measurableSet_singleton (true : Bool)).preimage
        (measurable_pi_apply (1 : Fin 4))).inter
        ((measurableSet_singleton (false : Bool)).preimage
          (measurable_pi_apply (3 : Fin 4))))

theorem pi_ber_reducedExtraPriorityPatternSet_real (x : I) :
    (Measure.pi (fun _ : Fin 4 => Ber(true, false, x))).real
        reducedExtraPriorityPatternSet =
      (x : ℝ) ^ 2 * (1 - (x : ℝ)) := by
  have hset : reducedExtraPriorityPatternSet =
      Set.pi Set.univ (fun i : Fin 4 =>
        ![({true} : Set Bool), ({true} : Set Bool), Set.univ,
          ({false} : Set Bool)] i) := by
    ext b
    constructor
    · rintro ⟨h0, h1, h3⟩ i hi
      fin_cases i <;> simp_all
    · intro h
      have h0 := h (0 : Fin 4) (by simp)
      have h1 := h (1 : Fin 4) (by simp)
      have h3 := h (3 : Fin 4) (by simp)
      simpa [reducedExtraPriorityPatternSet] using And.intro h0 (And.intro h1 h3)
  rw [measureReal_def, hset, Measure.pi_pi]
  simp only [ENNReal.toReal_prod]
  norm_num [Fin.prod_univ_succ, ProbabilityTheory.bernoulliMeasure_apply,
    Matrix.cons_val_zero, Matrix.cons_val_one]
  ring

theorem selected_lex_reducedExtraPriorityPatternSet_real {n : Nat}
    (target : Fin n) (x : I) (e : Fin 4 ↪ OtherMen target) :
    ((TargetOtherPriorityMeasure target).map
        (fun omega i ↦ lexTargetOtherIndicators target x omega (e i))).real
          reducedExtraPriorityPatternSet =
      (x : ℝ) ^ 2 * (1 - (x : ℝ)) := by
  rw [map_selected_lexTargetOtherIndicators target x e]
  exact pi_ber_reducedExtraPriorityPatternSet_real x

def selectedReducedExtraPriorityEvent {n : Nat} (target : Fin n)
    (e : Fin 4 ↪ OtherMen target) : Set (Fin n → I) :=
  selectedExtraPriorityBits target e ⁻¹' reducedExtraPriorityPatternSet

theorem measurableSet_selectedReducedExtraPriorityEvent {n : Nat}
    (target : Fin n) (e : Fin 4 ↪ OtherMen target) :
    MeasurableSet (selectedReducedExtraPriorityEvent target e) :=
  measurableSet_reducedExtraPriorityPatternSet.preimage
    (measurable_selectedExtraPriorityBits target e)

theorem reducedExtraPriorityEvent_witness_before {n : Nat}
    {target witness leftOwner rightOwner : Fin n}
    (E : ExtraPriorityEmbedding target witness leftOwner rightOwner)
    (priority : Fin n → I)
    (hevent : priority ∈
      selectedReducedExtraPriorityEvent target E.embedding) :
    LexUnitRevealedBefore priority target witness := by
  have hbit := hevent.1
  change decide (LexUnitRevealedBefore priority target
    (E.embedding 0).1) = true at hbit
  rw [E.witness_at_zero] at hbit
  simpa [lexRevealBits] using hbit

theorem reducedExtraPriorityEvent_left_before {n : Nat}
    {target witness leftOwner rightOwner : Fin n}
    (E : ExtraPriorityEmbedding target witness leftOwner rightOwner)
    (priority : Fin n → I)
    (hevent : priority ∈
      selectedReducedExtraPriorityEvent target E.embedding) :
    LexUnitRevealedBefore priority target leftOwner := by
  rcases E.left_at_zero_or_one with hleft | hleft
  · have hbit := hevent.1
    change decide (LexUnitRevealedBefore priority target
      (E.embedding 0).1) = true at hbit
    rw [hleft] at hbit
    simpa [lexRevealBits] using hbit
  · have hbit := hevent.2.1
    change decide (LexUnitRevealedBefore priority target
      (E.embedding 1).1) = true at hbit
    rw [hleft] at hbit
    simpa [lexRevealBits] using hbit

theorem reducedExtraPriorityEvent_right_after {n : Nat}
    {target witness leftOwner rightOwner : Fin n}
    (E : ExtraPriorityEmbedding target witness leftOwner rightOwner)
    (priority : Fin n → I)
    (hevent : priority ∈
      selectedReducedExtraPriorityEvent target E.embedding) :
    ¬ LexUnitRevealedBefore priority target rightOwner := by
  have hbit := hevent.2.2
  change decide (LexUnitRevealedBefore priority target
    (E.embedding 3).1) = false at hbit
  rw [E.right_at_three] at hbit
  simpa [lexRevealBits] using hbit

theorem targetSupportWindowGap_ge_log_two_on_reducedExtraPriorityEvent
    {n : Nat} {P : ProfileCode n}
    (D : StaticWindowData P) (hstable : (stableSet P).Nonempty)
    (base : CodedStable P) (m : Fin n)
    (L : CanonicalExtraLocalData D hstable base m)
    (priority : Fin n → I)
    (hevent : priority ∈
      selectedReducedExtraPriorityEvent m L.priorityEmbedding.embedding) :
    Real.log 2 ≤ targetSupportWindowGap D base priority m := by
  apply targetSupportWindowGap_ge_log_two_of_extra_conditions
    D hstable base m L priority
  · exact reducedExtraPriorityEvent_witness_before
      L.priorityEmbedding priority hevent
  · exact reducedExtraPriorityEvent_left_before
      L.priorityEmbedding priority hevent
  · exact reducedExtraPriorityEvent_right_after
      L.priorityEmbedding priority hevent

theorem integral_reduced_extra_priority_kernel :
    (∫ x : ℝ in 0..1, x ^ 2 * (1 - x)) = (1 : ℝ) / 12 := by
  have h := StableMatchingsE2E.integral_beta_kernel 2 (by norm_num)
  norm_num at h ⊢
  exact h

theorem selected_lex_reducedExtraPriorityPatternSet_measure {n : Nat}
    (target : Fin n) (x : I) (e : Fin 4 ↪ OtherMen target) :
    ((TargetOtherPriorityMeasure target).map
        (fun omega i ↦ lexTargetOtherIndicators target x omega (e i)))
          reducedExtraPriorityPatternSet =
      ENNReal.ofReal ((x : ℝ) ^ 2 * (1 - (x : ℝ))) := by
  rw [← ENNReal.ofReal_toReal (measure_ne_top _ _)]
  congr 1
  exact selected_lex_reducedExtraPriorityPatternSet_real target x e

theorem lintegral_unitInterval_reducedExtraPriorityPatternSet :
    (∫⁻ x : I,
        ENNReal.ofReal ((x : ℝ) ^ 2 * (1 - (x : ℝ))) ∂volume) =
      ENNReal.ofReal ((1 : ℝ) / 12) := by
  let p : ℝ → ℝ := fun x ↦ x ^ 2 * (1 - x)
  have hpcont : Continuous p := by
    exact (continuous_id.pow 2).mul (continuous_const.sub continuous_id)
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
  apply congrArg ENNReal.ofReal
  calc
    ∫ x : ℝ in Set.Ioc (0 : ℝ) 1, p x =
        ∫ x : ℝ in 0..1, p x :=
      (intervalIntegral.integral_of_le (by norm_num : (0 : ℝ) ≤ 1)).symm
    _ = (1 : ℝ) / 12 := by
      simpa [p] using integral_reduced_extra_priority_kernel

theorem fullPriorityMeasure_selectedReducedExtraPriorityEvent {n : Nat}
    (target : Fin n) (e : Fin 4 ↪ OtherMen target) :
    FullPriorityMeasure n (selectedReducedExtraPriorityEvent target e) =
      ENNReal.ofReal ((1 : ℝ) / 12) := by
  let event := selectedReducedExtraPriorityEvent target e
  have hevent : MeasurableSet event :=
    measurableSet_selectedReducedExtraPriorityEvent target e
  calc
    FullPriorityMeasure n event =
        (SplitTargetPriorityMeasure target)
          (assemblePriority target ⁻¹' event) := by
      rw [← MeasureTheory.Measure.map_apply
        (measurable_assemblePriority target) hevent]
      rw [map_assemblePriority_splitTargetPriorityMeasure target]
    _ = ∫⁻ x : I, (TargetOtherPriorityMeasure target)
          ((fun omega ↦ (x, omega)) ⁻¹'
            (assemblePriority target ⁻¹' event)) ∂volume := by
      exact MeasureTheory.Measure.prod_apply
        (hevent.preimage (measurable_assemblePriority target))
    _ = ∫⁻ x : I,
          ENNReal.ofReal ((x : ℝ) ^ 2 * (1 - (x : ℝ))) ∂volume := by
      apply MeasureTheory.lintegral_congr
      intro x
      rw [← selected_lex_reducedExtraPriorityPatternSet_measure target x e]
      rw [MeasureTheory.Measure.map_apply
        (measurable_selectedLexFourBits target e x)
        measurableSet_reducedExtraPriorityPatternSet]
      rfl
    _ = _ := lintegral_unitInterval_reducedExtraPriorityPatternSet

theorem fullPriorityMeasureReal_selectedReducedExtraPriorityEvent {n : Nat}
    (target : Fin n) (e : Fin 4 ↪ OtherMen target) :
    (FullPriorityMeasure n).real
        (selectedReducedExtraPriorityEvent target e) = (1 : ℝ) / 12 := by
  rw [measureReal_def, fullPriorityMeasure_selectedReducedExtraPriorityEvent]
  norm_num

theorem integral_targetSupportWindowGap_ge_reducedExtraPayment
    {n : Nat} {P : ProfileCode n}
    (D : StaticWindowData P) (hstable : (stableSet P).Nonempty)
    (base : CodedStable P) (m : Fin n)
    (L : CanonicalExtraLocalData D hstable base m) :
    Real.log 2 / 12 ≤
      ∫ priority, targetSupportWindowGap D base priority m
        ∂(FullPriorityMeasure n) := by
  let event := selectedReducedExtraPriorityEvent m L.priorityEmbedding.embedding
  let payment : (Fin n → I) → ℝ :=
    event.indicator (fun _ ↦ Real.log 2)
  have hevent : MeasurableSet event :=
    measurableSet_selectedReducedExtraPriorityEvent
      m L.priorityEmbedding.embedding
  have hpayInt : Integrable payment (FullPriorityMeasure n) := by
    exact (integrable_const (c := Real.log 2)).indicator hevent
  have hgapInt := integrable_targetSupportWindowGap D base m
  have hpoint : ∀ priority, payment priority ≤
      targetSupportWindowGap D base priority m := by
    intro priority
    by_cases hp : priority ∈ event
    · simpa [payment, Set.indicator_of_mem hp] using
        targetSupportWindowGap_ge_log_two_on_reducedExtraPriorityEvent
          D hstable base m L priority hp
    · simpa [payment, hp] using
        targetSupportWindowGap_nonneg D base priority m
  have hint := MeasureTheory.integral_mono hpayInt hgapInt hpoint
  have hpay : (∫ priority, payment priority ∂(FullPriorityMeasure n)) =
      Real.log 2 / 12 := by
    unfold payment
    rw [MeasureTheory.integral_indicator_const (Real.log 2) hevent,
      fullPriorityMeasureReal_selectedReducedExtraPriorityEvent]
    simp only [smul_eq_mul]
    ring
  linarith

theorem canonicalExtra_targetSupportWindowGap_ge_reducedExtraPayment
    {n : Nat} {P : ProfileCode n} (hn : 5 ≤ n)
    (D : StaticWindowData P) (hstable : (stableSet P).Nonempty)
    (base : CodedStable P) (m : Fin n)
    (hextra : canonicalExtraLeft P hstable base m) :
    Real.log 2 / 12 ≤
      ∫ priority, targetSupportWindowGap D base priority m
        ∂(FullPriorityMeasure n) := by
  obtain ⟨L⟩ := exists_canonicalExtraLocalData hn D hstable base m hextra
  exact integral_targetSupportWindowGap_ge_reducedExtraPayment
    D hstable base m L

/-! ## A finite three-event certificate for the shallow endpoint -/

def leftSecondTailEvent : Set ((Nat → Bool) × (Nat → Bool)) :=
  firstThreeFailureEvent ×ˢ firstAtEvent 1

def rightSecondTailEvent : Set ((Nat → Bool) × (Nat → Bool)) :=
  firstAtEvent 1 ×ˢ firstThreeFailureEvent

theorem measurableSet_leftSecondTailEvent :
    MeasurableSet leftSecondTailEvent :=
  measurableSet_firstThreeFailureEvent.prod (measurableSet_firstAtEvent 1)

theorem measurableSet_rightSecondTailEvent :
    MeasurableSet rightSecondTailEvent :=
  (measurableSet_firstAtEvent 1).prod measurableSet_firstThreeFailureEvent

theorem infiniteDummyPairMeasure_leftSecondTailEvent (x : I) :
    InfiniteDummyPairMeasure x leftSecondTailEvent =
      ENNReal.ofReal ((1 - (x : ℝ)) ^ 4 * (x : ℝ)) := by
  unfold leftSecondTailEvent InfiniteDummyPairMeasure
  rw [Measure.prod_prod,
    bernoulliSequenceMeasure_firstThreeFailureEvent,
    bernoulliSequenceMeasure_firstAtEvent]
  rw [← ENNReal.ofReal_toReal (by finiteness :
    ((unitInterval.toNNReal (unitInterval.symm x) : ENNReal) ^ 3 *
      ((unitInterval.toNNReal (unitInterval.symm x) : ENNReal) ^ 1 *
        (unitInterval.toNNReal x : ENNReal))) ≠ ⊤)]
  congr 1
  simp only [ENNReal.toReal_mul, ENNReal.toReal_pow, ENNReal.coe_toReal,
    unitInterval.coe_toNNReal, unitInterval.coe_symm_eq]
  ring

theorem infiniteDummyPairMeasure_rightSecondTailEvent (x : I) :
    InfiniteDummyPairMeasure x rightSecondTailEvent =
      ENNReal.ofReal ((1 - (x : ℝ)) ^ 4 * (x : ℝ)) := by
  unfold rightSecondTailEvent InfiniteDummyPairMeasure
  rw [Measure.prod_prod,
    bernoulliSequenceMeasure_firstAtEvent,
    bernoulliSequenceMeasure_firstThreeFailureEvent]
  rw [← ENNReal.ofReal_toReal (by finiteness :
    (((unitInterval.toNNReal (unitInterval.symm x) : ENNReal) ^ 1 *
        (unitInterval.toNNReal x : ENNReal)) *
      (unitInterval.toNNReal (unitInterval.symm x) : ENNReal) ^ 3) ≠ ⊤)]
  congr 1
  simp only [ENNReal.toReal_mul, ENNReal.toReal_pow, ENNReal.coe_toReal,
    unitInterval.coe_toNNReal, unitInterval.coe_symm_eq]
  ring

theorem firstSuccess_eq_one_of_mem_firstAtEvent_one
    (b : Nat → Bool) (hb : b ∈ firstAtEvent 1) :
    firstSuccess b = 1 := by
  unfold firstAtEvent at hb
  apply firstSuccess_eq_of_first b 1 hb.1
  intro i hi
  have hfalse := Set.mem_iInter.mp hb.2 ⟨i, by omega⟩
  simpa using hfalse

theorem second_tail_finite_width_le_three
    (shortLen otherLen : Nat) (hshort : shortLen ≤ 1)
    (shortStream otherStream : Nat → Bool)
    (hotherOne : otherStream ∈ firstAtEvent 1) :
    markerWindowWidth (streamPrefix shortLen shortStream)
        (streamPrefix otherLen otherStream) ≤ 3 := by
  have hs := truncatedWait_le_length_succ
    (streamPrefix shortLen shortStream)
  have ho : truncatedWait (streamPrefix otherLen otherStream) ≤ 2 := by
    cases otherLen with
    | zero => simp [streamPrefix]
    | succ k =>
      cases k with
      | zero =>
        simpa [streamPrefix] using
          truncatedWait_le_length_succ (streamPrefix 1 otherStream)
      | succ k =>
        refine truncatedWait_le_of_getElem_true _ 1 (by simp) ?_
        simpa [streamPrefix, firstAtEvent, successEvent] using hotherOne.1
  simp only [streamPrefix_length] at hs
  unfold markerWindowWidth
  omega

theorem second_tail_log_gap
    (shortLen otherLen : Nat) (hshort : shortLen ≤ 1)
    (shortStream otherStream : Nat → Bool)
    (hshortSuccess : hasSuccess shortStream)
    (hshortFailure : shortStream ∈ firstThreeFailureEvent)
    (hotherOne : otherStream ∈ firstAtEvent 1) :
    Real.log
        (geometricWindow (infiniteDummyWaitPair
          (shortStream, otherStream)) : ℝ) -
        Real.log (markerWindowWidth (streamPrefix shortLen shortStream)
          (streamPrefix otherLen otherStream) : ℝ) ≥
      Real.log ((5 : ℝ) / 3) := by
  have hfirst : 3 ≤ firstSuccess shortStream :=
    firstSuccess_ge_three_of_mem_firstThreeFailureEvent
      shortStream hshortSuccess hshortFailure
  have hone : firstSuccess otherStream = 1 :=
    firstSuccess_eq_one_of_mem_firstAtEvent_one otherStream hotherOne
  have hinf : 5 ≤ geometricWindow
      (infiniteDummyWaitPair (shortStream, otherStream)) := by
    simp only [geometricWindow, infiniteDummyWaitPair, hone]
    omega
  have hfin := second_tail_finite_width_le_three shortLen otherLen hshort
    shortStream otherStream hotherOne
  have hfinpos : 0 < markerWindowWidth (streamPrefix shortLen shortStream)
      (streamPrefix otherLen otherStream) := by
    have hs := truncatedWait_pos (streamPrefix shortLen shortStream)
    have ho := truncatedWait_pos (streamPrefix otherLen otherStream)
    unfold markerWindowWidth
    omega
  have hinfpos : 0 < geometricWindow
      (infiniteDummyWaitPair (shortStream, otherStream)) := by omega
  have hratio : ((5 : ℝ) / 3) *
      (markerWindowWidth (streamPrefix shortLen shortStream)
        (streamPrefix otherLen otherStream) : ℝ) ≤
      (geometricWindow (infiniteDummyWaitPair
        (shortStream, otherStream)) : ℝ) := by
    have hfinReal :
        (markerWindowWidth (streamPrefix shortLen shortStream)
          (streamPrefix otherLen otherStream) : ℝ) ≤ 3 := by
      exact_mod_cast hfin
    have hinfReal : (5 : ℝ) ≤
        geometricWindow (infiniteDummyWaitPair
          (shortStream, otherStream)) := by exact_mod_cast hinf
    nlinarith
  rw [← Real.log_div (by exact_mod_cast hinfpos.ne')
    (by exact_mod_cast hfinpos.ne')]
  apply Real.log_le_log (by norm_num)
  rw [le_div_iff₀ (by exact_mod_cast hfinpos)]
  simpa [mul_comm] using hratio

theorem left_second_tail_pointwise_payment
    (leftLen rightLen : Nat) (hleft : leftLen ≤ 1)
    (z : (Nat → Bool) × (Nat → Bool))
    (hs : hasSuccess z.1 ∧ hasSuccess z.2)
    (hevent : z ∈ leftSecondTailEvent) :
    prefixPairWindowLogNN leftLen rightLen
        (pairedPrefixVector leftLen rightLen z) +
        ENNReal.ofReal (Real.log ((5 : ℝ) / 3)) ≤
      geometricWindowLogNN (infiniteDummyWaitPair z) := by
  have hgap := second_tail_log_gap leftLen rightLen hleft z.1 z.2
    hs.1 hevent.1 hevent.2
  have hfinite := markerPrefixLog_nonneg leftLen rightLen z
  simp only [prefixPairWindowLogNN, pairedPrefixVector,
    ofFn_streamPrefixVector, geometricWindowLogNN]
  rw [← ENNReal.ofReal_add hfinite
    (Real.log_nonneg (by norm_num : (1 : ℝ) ≤ 5 / 3))]
  apply ENNReal.ofReal_le_ofReal
  linarith

theorem right_second_tail_pointwise_payment
    (leftLen rightLen : Nat) (hright : rightLen ≤ 1)
    (z : (Nat → Bool) × (Nat → Bool))
    (hs : hasSuccess z.1 ∧ hasSuccess z.2)
    (hevent : z ∈ rightSecondTailEvent) :
    prefixPairWindowLogNN leftLen rightLen
        (pairedPrefixVector leftLen rightLen z) +
        ENNReal.ofReal (Real.log ((5 : ℝ) / 3)) ≤
      geometricWindowLogNN (infiniteDummyWaitPair z) := by
  have hgap := second_tail_log_gap rightLen leftLen hright z.2 z.1
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
    (Real.log_nonneg (by norm_num : (1 : ℝ) ≤ 5 / 3))]
  apply ENNReal.ofReal_le_ofReal
  rw [hwidthSwap, hinfSwap]
  linarith

theorem leftStrongEndpointEvent_disjoint_leftEndpointEvent :
    Disjoint leftStrongEndpointEvent leftEndpointEvent := by
  rw [Set.disjoint_left]
  intro z hstrong hendpoint
  have hfalse := (mem_firstThreeFailureEvent_iff z.1).1 hstrong.1 2 (by omega)
  have hwaits : firstSuccess z.1 = 2 ∧ firstSuccess z.2 = 0 := by
    simpa [leftEndpointEvent, infiniteDummyWaitPair, Prod.ext_iff] using hendpoint
  have hfirstAt : z.1 ∈ firstAtEvent 2 := by
    have h : z.1 ∈ {b : Nat → Bool | firstSuccess b = 2} := hwaits.1
    rw [firstSuccess_fiber] at h
    simpa using h
  have htrue := hfirstAt.1
  simpa [successEvent, hfalse] using htrue

theorem leftStrongEndpointEvent_disjoint_leftSecondTailEvent :
    Disjoint leftStrongEndpointEvent leftSecondTailEvent := by
  rw [Set.disjoint_left]
  intro z hstrong hsecond
  have hzero : z.2 0 = true := by
    simpa [successEvent] using hstrong.2
  have hone := firstSuccess_eq_one_of_mem_firstAtEvent_one z.2 hsecond.2
  have hsuccess : hasSuccess z.2 := ⟨1, hsecond.2.1⟩
  have hfalse := firstSuccess_before z.2 hsuccess (by omega : 0 < firstSuccess z.2)
  simp_all

theorem leftEndpointEvent_disjoint_leftSecondTailEvent :
    Disjoint leftEndpointEvent leftSecondTailEvent := by
  rw [Set.disjoint_left]
  intro z hendpoint hsecond
  have hwaits : firstSuccess z.1 = 2 ∧ firstSuccess z.2 = 0 := by
    simpa [leftEndpointEvent, infiniteDummyWaitPair, Prod.ext_iff] using hendpoint
  have hone := firstSuccess_eq_one_of_mem_firstAtEvent_one z.2 hsecond.2
  omega

theorem rightStrongEndpointEvent_disjoint_rightEndpointEvent :
    Disjoint rightStrongEndpointEvent rightEndpointEvent := by
  rw [Set.disjoint_left]
  intro z hstrong hendpoint
  have hfalse := (mem_firstThreeFailureEvent_iff z.2).1 hstrong.2 2 (by omega)
  have hwaits : firstSuccess z.1 = 0 ∧ firstSuccess z.2 = 2 := by
    simpa [rightEndpointEvent, infiniteDummyWaitPair, Prod.ext_iff] using hendpoint
  have hfirstAt : z.2 ∈ firstAtEvent 2 := by
    have h : z.2 ∈ {b : Nat → Bool | firstSuccess b = 2} := hwaits.2
    rw [firstSuccess_fiber] at h
    simpa using h
  have htrue := hfirstAt.1
  simpa [successEvent, hfalse] using htrue

theorem rightStrongEndpointEvent_disjoint_rightSecondTailEvent :
    Disjoint rightStrongEndpointEvent rightSecondTailEvent := by
  rw [Set.disjoint_left]
  intro z hstrong hsecond
  have hzero : z.1 0 = true := by
    simpa [successEvent] using hstrong.1
  have hone := firstSuccess_eq_one_of_mem_firstAtEvent_one z.1 hsecond.1
  have hsuccess : hasSuccess z.1 := ⟨1, hsecond.1.1⟩
  have hfalse := firstSuccess_before z.1 hsuccess (by omega : 0 < firstSuccess z.1)
  simp_all

theorem rightEndpointEvent_disjoint_rightSecondTailEvent :
    Disjoint rightEndpointEvent rightSecondTailEvent := by
  rw [Set.disjoint_left]
  intro z hendpoint hsecond
  have hwaits : firstSuccess z.1 = 0 ∧ firstSuccess z.2 = 2 := by
    simpa [rightEndpointEvent, infiniteDummyWaitPair, Prod.ext_iff] using hendpoint
  have hone := firstSuccess_eq_one_of_mem_firstAtEvent_one z.1 hsecond.1
  omega

def leftThreeEventPayment :
    ((Nat → Bool) × (Nat → Bool)) → ENNReal := fun z ↦
  (leftStrongEndpointEvent.indicator (fun _ ↦ ENNReal.ofReal (Real.log 2)) z +
  leftEndpointEvent.indicator
    (fun _ ↦ ENNReal.ofReal (Real.log ((3 : ℝ) / 2))) z) +
  leftSecondTailEvent.indicator
    (fun _ ↦ ENNReal.ofReal (Real.log ((5 : ℝ) / 3))) z

def rightThreeEventPayment :
    ((Nat → Bool) × (Nat → Bool)) → ENNReal := fun z ↦
  (rightStrongEndpointEvent.indicator (fun _ ↦ ENNReal.ofReal (Real.log 2)) z +
  rightEndpointEvent.indicator
    (fun _ ↦ ENNReal.ofReal (Real.log ((3 : ℝ) / 2))) z) +
  rightSecondTailEvent.indicator
    (fun _ ↦ ENNReal.ofReal (Real.log ((5 : ℝ) / 3))) z

theorem measurable_leftThreeEventPayment : Measurable leftThreeEventPayment := by
  unfold leftThreeEventPayment
  exact ((measurable_const.indicator measurableSet_leftStrongEndpointEvent).add
    (measurable_const.indicator measurableSet_leftEndpointEvent)).add
      (measurable_const.indicator measurableSet_leftSecondTailEvent)

theorem measurable_rightThreeEventPayment : Measurable rightThreeEventPayment := by
  unfold rightThreeEventPayment
  exact ((measurable_const.indicator measurableSet_rightStrongEndpointEvent).add
    (measurable_const.indicator measurableSet_rightEndpointEvent)).add
      (measurable_const.indicator measurableSet_rightSecondTailEvent)

theorem left_three_event_pointwise_payment
    (leftLen rightLen : Nat) (hleft : leftLen ≤ 1)
    (z : (Nat → Bool) × (Nat → Bool))
    (hs : hasSuccess z.1 ∧ hasSuccess z.2)
    (hdom : markerWindowWidth (streamPrefix leftLen z.1)
        (streamPrefix rightLen z.2) ≤
      geometricWindow (infiniteDummyWaitPair z)) :
    prefixPairWindowLogNN leftLen rightLen
        (pairedPrefixVector leftLen rightLen z) + leftThreeEventPayment z ≤
      geometricWindowLogNN (infiniteDummyWaitPair z) := by
  by_cases hstrong : z ∈ leftStrongEndpointEvent
  · have hne := Set.disjoint_left.1
        leftStrongEndpointEvent_disjoint_leftEndpointEvent hstrong
    have hns := Set.disjoint_left.1
        leftStrongEndpointEvent_disjoint_leftSecondTailEvent hstrong
    simpa [leftThreeEventPayment, Set.indicator_of_mem hstrong, hne, hns]
      using left_strong_endpoint_pointwise_payment
        leftLen rightLen hleft z hs hstrong
  · by_cases hendpoint : z ∈ leftEndpointEvent
    · have hns := Set.disjoint_left.1
          leftEndpointEvent_disjoint_leftSecondTailEvent hendpoint
      simpa [leftThreeEventPayment, hstrong,
        Set.indicator_of_mem hendpoint, hns]
        using left_endpoint_pointwise_payment
          leftLen rightLen hleft z hs hendpoint
    · by_cases hsecond : z ∈ leftSecondTailEvent
      · simpa [leftThreeEventPayment, hstrong, hendpoint,
          Set.indicator_of_mem hsecond]
          using left_second_tail_pointwise_payment
            leftLen rightLen hleft z hs hsecond
      · have hbase : prefixPairWindowLogNN leftLen rightLen
            (pairedPrefixVector leftLen rightLen z) ≤
          geometricWindowLogNN (infiniteDummyWaitPair z) := by
          unfold prefixPairWindowLogNN geometricWindowLogNN
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
        simpa [leftThreeEventPayment, hstrong, hendpoint, hsecond] using hbase

theorem right_three_event_pointwise_payment
    (leftLen rightLen : Nat) (hright : rightLen ≤ 1)
    (z : (Nat → Bool) × (Nat → Bool))
    (hs : hasSuccess z.1 ∧ hasSuccess z.2)
    (hdom : markerWindowWidth (streamPrefix leftLen z.1)
        (streamPrefix rightLen z.2) ≤
      geometricWindow (infiniteDummyWaitPair z)) :
    prefixPairWindowLogNN leftLen rightLen
        (pairedPrefixVector leftLen rightLen z) + rightThreeEventPayment z ≤
      geometricWindowLogNN (infiniteDummyWaitPair z) := by
  by_cases hstrong : z ∈ rightStrongEndpointEvent
  · have hne := Set.disjoint_left.1
        rightStrongEndpointEvent_disjoint_rightEndpointEvent hstrong
    have hns := Set.disjoint_left.1
        rightStrongEndpointEvent_disjoint_rightSecondTailEvent hstrong
    simpa [rightThreeEventPayment, Set.indicator_of_mem hstrong, hne, hns]
      using right_strong_endpoint_pointwise_payment
        leftLen rightLen hright z hs hstrong
  · by_cases hendpoint : z ∈ rightEndpointEvent
    · have hns := Set.disjoint_left.1
          rightEndpointEvent_disjoint_rightSecondTailEvent hendpoint
      simpa [rightThreeEventPayment, hstrong,
        Set.indicator_of_mem hendpoint, hns]
        using right_endpoint_pointwise_payment
          leftLen rightLen hright z hs hendpoint
    · by_cases hsecond : z ∈ rightSecondTailEvent
      · simpa [rightThreeEventPayment, hstrong, hendpoint,
          Set.indicator_of_mem hsecond]
          using right_second_tail_pointwise_payment
            leftLen rightLen hright z hs hsecond
      · have hbase : prefixPairWindowLogNN leftLen rightLen
            (pairedPrefixVector leftLen rightLen z) ≤
          geometricWindowLogNN (infiniteDummyWaitPair z) := by
          unfold prefixPairWindowLogNN geometricWindowLogNN
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
        simpa [rightThreeEventPayment, hstrong, hendpoint, hsecond] using hbase

theorem lintegral_leftThreeEventPayment {x : I} (hx : x ≠ 0) :
    (∫⁻ z, leftThreeEventPayment z ∂(InfiniteDummyPairMeasure x)) =
      ENNReal.ofReal (Real.log 2) *
          ENNReal.ofReal ((1 - (x : ℝ)) ^ 3 * (x : ℝ)) +
        ENNReal.ofReal (Real.log ((3 : ℝ) / 2)) *
          ENNReal.ofReal ((x : ℝ) ^ 2 * (1 - (x : ℝ)) ^ 2) +
        ENNReal.ofReal (Real.log ((5 : ℝ) / 3)) *
          ENNReal.ofReal ((1 - (x : ℝ)) ^ 4 * (x : ℝ)) := by
  unfold leftThreeEventPayment
  let A : ((Nat → Bool) × (Nat → Bool)) → ENNReal :=
    leftStrongEndpointEvent.indicator
      (fun _ ↦ ENNReal.ofReal (Real.log 2))
  let B : ((Nat → Bool) × (Nat → Bool)) → ENNReal :=
    leftEndpointEvent.indicator
      (fun _ ↦ ENNReal.ofReal (Real.log ((3 : ℝ) / 2)))
  let C : ((Nat → Bool) × (Nat → Bool)) → ENNReal :=
    leftSecondTailEvent.indicator
      (fun _ ↦ ENNReal.ofReal (Real.log ((5 : ℝ) / 3)))
  have hA : Measurable A :=
    measurable_const.indicator measurableSet_leftStrongEndpointEvent
  have hB : Measurable B :=
    measurable_const.indicator measurableSet_leftEndpointEvent
  change (∫⁻ z, ((A + B) + C) z ∂(InfiniteDummyPairMeasure x)) = _
  simp only [Pi.add_apply]
  rw [MeasureTheory.lintegral_add_left
      (f := fun z ↦ A z + B z) (g := C) (hA.add hB),
    MeasureTheory.lintegral_add_left (f := A) (g := B) hA]
  unfold A B C
  rw [MeasureTheory.lintegral_indicator measurableSet_leftStrongEndpointEvent,
    MeasureTheory.lintegral_indicator measurableSet_leftEndpointEvent,
    MeasureTheory.lintegral_indicator measurableSet_leftSecondTailEvent]
  rw [MeasureTheory.setLIntegral_const, MeasureTheory.setLIntegral_const,
    MeasureTheory.setLIntegral_const]
  rw [infiniteDummyPairMeasure_leftStrongEndpointEvent,
    infiniteDummyPairMeasure_leftEndpointEvent hx,
    infiniteDummyPairMeasure_leftSecondTailEvent]

theorem lintegral_rightThreeEventPayment {x : I} (hx : x ≠ 0) :
    (∫⁻ z, rightThreeEventPayment z ∂(InfiniteDummyPairMeasure x)) =
      ENNReal.ofReal (Real.log 2) *
          ENNReal.ofReal ((1 - (x : ℝ)) ^ 3 * (x : ℝ)) +
        ENNReal.ofReal (Real.log ((3 : ℝ) / 2)) *
          ENNReal.ofReal ((x : ℝ) ^ 2 * (1 - (x : ℝ)) ^ 2) +
        ENNReal.ofReal (Real.log ((5 : ℝ) / 3)) *
          ENNReal.ofReal ((1 - (x : ℝ)) ^ 4 * (x : ℝ)) := by
  unfold rightThreeEventPayment
  let A : ((Nat → Bool) × (Nat → Bool)) → ENNReal :=
    rightStrongEndpointEvent.indicator
      (fun _ ↦ ENNReal.ofReal (Real.log 2))
  let B : ((Nat → Bool) × (Nat → Bool)) → ENNReal :=
    rightEndpointEvent.indicator
      (fun _ ↦ ENNReal.ofReal (Real.log ((3 : ℝ) / 2)))
  let C : ((Nat → Bool) × (Nat → Bool)) → ENNReal :=
    rightSecondTailEvent.indicator
      (fun _ ↦ ENNReal.ofReal (Real.log ((5 : ℝ) / 3)))
  have hA : Measurable A :=
    measurable_const.indicator measurableSet_rightStrongEndpointEvent
  have hB : Measurable B :=
    measurable_const.indicator measurableSet_rightEndpointEvent
  change (∫⁻ z, ((A + B) + C) z ∂(InfiniteDummyPairMeasure x)) = _
  simp only [Pi.add_apply]
  rw [MeasureTheory.lintegral_add_left
      (f := fun z ↦ A z + B z) (g := C) (hA.add hB),
    MeasureTheory.lintegral_add_left (f := A) (g := B) hA]
  unfold A B C
  rw [MeasureTheory.lintegral_indicator measurableSet_rightStrongEndpointEvent,
    MeasureTheory.lintegral_indicator measurableSet_rightEndpointEvent,
    MeasureTheory.lintegral_indicator measurableSet_rightSecondTailEvent]
  rw [MeasureTheory.setLIntegral_const, MeasureTheory.setLIntegral_const,
    MeasureTheory.setLIntegral_const]
  rw [infiniteDummyPairMeasure_rightStrongEndpointEvent,
    infiniteDummyPairMeasure_rightEndpointEvent hx,
    infiniteDummyPairMeasure_rightSecondTailEvent]

theorem lintegral_left_three_event_payment {x : I} (hx : x ≠ 0)
    (leftLen rightLen : Nat) (hleft : leftLen ≤ 1) :
    (∫⁻ z, prefixPairWindowLogNN leftLen rightLen
        (pairedPrefixVector leftLen rightLen z)
        ∂(InfiniteDummyPairMeasure x)) +
      (ENNReal.ofReal (Real.log 2) *
          ENNReal.ofReal ((1 - (x : ℝ)) ^ 3 * (x : ℝ)) +
        ENNReal.ofReal (Real.log ((3 : ℝ) / 2)) *
          ENNReal.ofReal ((x : ℝ) ^ 2 * (1 - (x : ℝ)) ^ 2) +
        ENNReal.ofReal (Real.log ((5 : ℝ) / 3)) *
          ENNReal.ofReal ((1 - (x : ℝ)) ^ 4 * (x : ℝ))) ≤
      ∑' k : Nat, ENNReal.ofReal (geometricLogTerm k (x : ℝ)) := by
  let finiteLog : ((Nat → Bool) × (Nat → Bool)) → ENNReal := fun z ↦
    prefixPairWindowLogNN leftLen rightLen
      (pairedPrefixVector leftLen rightLen z)
  have hfiniteMeas : Measurable finiteLog :=
    (measurable_prefixPairWindowLogNN _ _).comp
      (measurable_pairedPrefixVector _ _)
  calc
    _ = ∫⁻ z, finiteLog z + leftThreeEventPayment z
          ∂(InfiniteDummyPairMeasure x) := by
      rw [MeasureTheory.lintegral_add_left hfiniteMeas,
        lintegral_leftThreeEventPayment hx]
    _ ≤ ∫⁻ z, geometricWindowLogNN (infiniteDummyWaitPair z)
          ∂(InfiniteDummyPairMeasure x) := by
      apply MeasureTheory.lintegral_mono_ae
      filter_upwards [ae_infiniteDummyPair_hasSuccess hx,
        ae_markerWindowWidth_prefix_le_geometricWindow hx leftLen rightLen]
          with z hs hdom
      exact left_three_event_pointwise_payment
        leftLen rightLen hleft z hs hdom
    _ = ∫⁻ p, geometricWindowLogNN p ∂(GeometricPairMeasure x) := by
      rw [← infiniteDummyWaitPair_has_geometric_pair_law hx]
      exact (MeasureTheory.lintegral_map measurable_geometricWindowLogNN
        measurable_infiniteDummyWaitPair).symm
    _ = _ := lintegral_geometricWindowLogNN_eq_tsum hx

theorem lintegral_right_three_event_payment {x : I} (hx : x ≠ 0)
    (leftLen rightLen : Nat) (hright : rightLen ≤ 1) :
    (∫⁻ z, prefixPairWindowLogNN leftLen rightLen
        (pairedPrefixVector leftLen rightLen z)
        ∂(InfiniteDummyPairMeasure x)) +
      (ENNReal.ofReal (Real.log 2) *
          ENNReal.ofReal ((1 - (x : ℝ)) ^ 3 * (x : ℝ)) +
        ENNReal.ofReal (Real.log ((3 : ℝ) / 2)) *
          ENNReal.ofReal ((x : ℝ) ^ 2 * (1 - (x : ℝ)) ^ 2) +
        ENNReal.ofReal (Real.log ((5 : ℝ) / 3)) *
          ENNReal.ofReal ((1 - (x : ℝ)) ^ 4 * (x : ℝ))) ≤
      ∑' k : Nat, ENNReal.ofReal (geometricLogTerm k (x : ℝ)) := by
  let finiteLog : ((Nat → Bool) × (Nat → Bool)) → ENNReal := fun z ↦
    prefixPairWindowLogNN leftLen rightLen
      (pairedPrefixVector leftLen rightLen z)
  have hfiniteMeas : Measurable finiteLog :=
    (measurable_prefixPairWindowLogNN _ _).comp
      (measurable_pairedPrefixVector _ _)
  calc
    _ = ∫⁻ z, finiteLog z + rightThreeEventPayment z
          ∂(InfiniteDummyPairMeasure x) := by
      rw [MeasureTheory.lintegral_add_left hfiniteMeas,
        lintegral_rightThreeEventPayment hx]
    _ ≤ ∫⁻ z, geometricWindowLogNN (infiniteDummyWaitPair z)
          ∂(InfiniteDummyPairMeasure x) := by
      apply MeasureTheory.lintegral_mono_ae
      filter_upwards [ae_infiniteDummyPair_hasSuccess hx,
        ae_markerWindowWidth_prefix_le_geometricWindow hx leftLen rightLen]
          with z hs hdom
      exact right_three_event_pointwise_payment
        leftLen rightLen hright z hs hdom
    _ = ∫⁻ p, geometricWindowLogNN p ∂(GeometricPairMeasure x) := by
      rw [← infiniteDummyWaitPair_has_geometric_pair_law hx]
      exact (MeasureTheory.lintegral_map measurable_geometricWindowLogNN
        measurable_infiniteDummyWaitPair).symm
    _ = _ := lintegral_geometricWindowLogNN_eq_tsum hx

theorem integral_second_tail_priority_event :
    (∫ x : ℝ in 0..1, (1 - x) ^ 4 * x) = (1 : ℝ) / 30 := by
  let F : ℝ → ℝ := fun x ↦
    x ^ 2 / 2 - 4 * x ^ 3 / 3 + 3 * x ^ 4 / 2 -
      4 * x ^ 5 / 5 + x ^ 6 / 6
  have hderiv : ∀ x : ℝ, HasDerivAt F ((1 - x) ^ 4 * x) x := by
    intro x
    have h := ((hasDerivAt_pow 2 x).div_const (2 : ℝ)).sub
      ((hasDerivAt_const x 4).mul (hasDerivAt_pow 3 x) |>.div_const (3 : ℝ)) |>.add
      ((hasDerivAt_const x 3).mul (hasDerivAt_pow 4 x) |>.div_const (2 : ℝ)) |>.sub
      ((hasDerivAt_const x 4).mul (hasDerivAt_pow 5 x) |>.div_const (5 : ℝ)) |>.add
      ((hasDerivAt_pow 6 x).div_const (6 : ℝ))
    convert h using 1 <;> (try rfl) <;> (try dsimp [F]) <;> ring
  rw [intervalIntegral.integral_eq_sub_of_hasDerivAt_of_le (by norm_num)
    (by fun_prop) (fun x _ ↦ hderiv x)
    (((continuous_const.sub continuous_id).pow 4).mul continuous_id
      |>.intervalIntegrable 0 1)]
  norm_num [F]

theorem lintegral_unit_second_tail_priority_event :
    (∫⁻ x : I,
        ENNReal.ofReal ((1 - (x : ℝ)) ^ 4 * (x : ℝ)) ∂volume) =
      ENNReal.ofReal ((1 : ℝ) / 30) := by
  let p : ℝ → ℝ := fun x ↦ (1 - x) ^ 4 * x
  have hpcont : Continuous p := by
    exact ((continuous_const.sub continuous_id).pow 4).mul continuous_id
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
  apply congrArg ENNReal.ofReal
  calc
    ∫ x : ℝ in Set.Ioc (0 : ℝ) 1, p x =
        ∫ x : ℝ in 0..1, p x :=
      (intervalIntegral.integral_of_le (by norm_num : (0 : ℝ) ≤ 1)).symm
    _ = (1 : ℝ) / 30 := by
      simpa [p] using integral_second_tail_priority_event

def threeEventEndpointPayment : ℝ :=
  Real.log 2 / 20 + Real.log ((3 : ℝ) / 2) / 30 +
    Real.log ((5 : ℝ) / 3) / 30

def threeEventPenalty (x : I) : ENNReal :=
  (ENNReal.ofReal (Real.log 2) *
      ENNReal.ofReal ((1 - (x : ℝ)) ^ 3 * (x : ℝ)) +
    ENNReal.ofReal (Real.log ((3 : ℝ) / 2)) *
      ENNReal.ofReal ((x : ℝ) ^ 2 * (1 - (x : ℝ)) ^ 2)) +
    ENNReal.ofReal (Real.log ((5 : ℝ) / 3)) *
      ENNReal.ofReal ((1 - (x : ℝ)) ^ 4 * (x : ℝ))

theorem measurable_threeEventPenalty : Measurable threeEventPenalty := by
  unfold threeEventPenalty
  fun_prop

theorem lintegral_unit_threeEventPenalty :
    (∫⁻ x : I, threeEventPenalty x ∂volume) =
      ENNReal.ofReal threeEventEndpointPayment := by
  let A : I → ENNReal := fun x ↦
    ENNReal.ofReal (Real.log 2) *
      ENNReal.ofReal ((1 - (x : ℝ)) ^ 3 * (x : ℝ))
  let B : I → ENNReal := fun x ↦
    ENNReal.ofReal (Real.log ((3 : ℝ) / 2)) *
      ENNReal.ofReal ((x : ℝ) ^ 2 * (1 - (x : ℝ)) ^ 2)
  let C : I → ENNReal := fun x ↦
    ENNReal.ofReal (Real.log ((5 : ℝ) / 3)) *
      ENNReal.ofReal ((1 - (x : ℝ)) ^ 4 * (x : ℝ))
  have hk0 : Measurable (fun x : I ↦
      ENNReal.ofReal ((1 - (x : ℝ)) ^ 3 * (x : ℝ))) := by fun_prop
  have hk1 : Measurable (fun x : I ↦
      ENNReal.ofReal ((x : ℝ) ^ 2 * (1 - (x : ℝ)) ^ 2)) := by fun_prop
  have hk2 : Measurable (fun x : I ↦
      ENNReal.ofReal ((1 - (x : ℝ)) ^ 4 * (x : ℝ))) := by fun_prop
  have hA : Measurable A := measurable_const.mul hk0
  have hB : Measurable B := measurable_const.mul hk1
  have hAi : (∫⁻ x : I, A x ∂volume) =
      ENNReal.ofReal (Real.log 2 / 20) := by
    unfold A
    rw [MeasureTheory.lintegral_const_mul _ hk0,
      lintegral_unit_strong_endpoint_priority_event]
    rw [← ENNReal.ofReal_mul (Real.log_nonneg (by norm_num : (1 : ℝ) ≤ 2))]
    congr 1
    ring
  have hBi : (∫⁻ x : I, B x ∂volume) =
      ENNReal.ofReal (Real.log ((3 : ℝ) / 2) / 30) := by
    unfold B
    rw [MeasureTheory.lintegral_const_mul _ hk1,
      lintegral_unit_endpoint_priority_event]
    rw [← ENNReal.ofReal_mul
      (Real.log_nonneg (by norm_num : (1 : ℝ) ≤ 3 / 2))]
    congr 1
    ring
  have hCi : (∫⁻ x : I, C x ∂volume) =
      ENNReal.ofReal (Real.log ((5 : ℝ) / 3) / 30) := by
    unfold C
    rw [MeasureTheory.lintegral_const_mul _ hk2,
      lintegral_unit_second_tail_priority_event]
    rw [← ENNReal.ofReal_mul
      (Real.log_nonneg (by norm_num : (1 : ℝ) ≤ 5 / 3))]
    congr 1
    ring
  change (∫⁻ x : I, ((A + B) + C) x ∂volume) = _
  simp only [Pi.add_apply]
  rw [MeasureTheory.lintegral_add_left
      (f := fun x ↦ A x + B x) (g := C) (hA.add hB),
    MeasureTheory.lintegral_add_left (f := A) (g := B) hA,
    hAi, hBi, hCi]
  rw [← ENNReal.ofReal_add (by positivity : 0 ≤ Real.log 2 / 20)
      (by positivity : 0 ≤ Real.log ((3 : ℝ) / 2) / 30),
    ← ENNReal.ofReal_add (by positivity :
      0 ≤ Real.log 2 / 20 + Real.log ((3 : ℝ) / 2) / 30)
      (by positivity : 0 ≤ Real.log ((5 : ℝ) / 3) / 30)]
  rfl

theorem log_two_div_twelve_le_threeEventEndpointPayment :
    Real.log 2 / 12 ≤ threeEventEndpointPayment := by
  have hprod : Real.log ((3 : ℝ) / 2) + Real.log ((5 : ℝ) / 3) =
      Real.log ((5 : ℝ) / 2) := by
    rw [← Real.log_mul (by norm_num : (3 : ℝ) / 2 ≠ 0)
      (by norm_num : (5 : ℝ) / 3 ≠ 0)]
    norm_num
  have hmono : Real.log 2 ≤ Real.log ((5 : ℝ) / 2) := by
    exact Real.strictMonoOn_log.monotoneOn
      (by norm_num) (by norm_num) (by norm_num)
  unfold threeEventEndpointPayment
  rw [← hprod] at hmono
  linarith

theorem finitePrefixCostNN_add_threeEventPayment_le_of_left
    (leftLen rightLen : Nat) (hleft : leftLen ≤ 1) :
    finitePrefixCostNN leftLen rightLen +
        ENNReal.ofReal threeEventEndpointPayment ≤
      ENNReal.ofReal geometricLogSeries := by
  have hpenaltyMeas : Measurable threeEventPenalty :=
    measurable_threeEventPenalty
  calc
    _ = (∫⁻ x : I,
          (∫⁻ z, prefixPairWindowLogNN leftLen rightLen
              (pairedPrefixVector leftLen rightLen z)
              ∂(InfiniteDummyPairMeasure x)) + threeEventPenalty x ∂volume) := by
      rw [MeasureTheory.lintegral_add_right _ hpenaltyMeas,
        lintegral_unit_threeEventPenalty]
      rfl
    _ ≤ (∫⁻ x : I,
          ∑' k : Nat, ENNReal.ofReal (geometricLogTerm k (x : ℝ))
          ∂volume) := by
      apply MeasureTheory.lintegral_mono_ae
      filter_upwards [MeasureTheory.volume.ae_ne (0 : I)] with x hx
      simpa [threeEventPenalty, add_assoc] using
        lintegral_left_three_event_payment hx leftLen rightLen hleft
    _ = _ := lintegral_unit_geometricSeries_eq_ofReal

theorem finitePrefixCostNN_add_threeEventPayment_le_of_right
    (leftLen rightLen : Nat) (hright : rightLen ≤ 1) :
    finitePrefixCostNN leftLen rightLen +
        ENNReal.ofReal threeEventEndpointPayment ≤
      ENNReal.ofReal geometricLogSeries := by
  have hpenaltyMeas : Measurable threeEventPenalty :=
    measurable_threeEventPenalty
  calc
    _ = (∫⁻ x : I,
          (∫⁻ z, prefixPairWindowLogNN leftLen rightLen
              (pairedPrefixVector leftLen rightLen z)
              ∂(InfiniteDummyPairMeasure x)) + threeEventPenalty x ∂volume) := by
      rw [MeasureTheory.lintegral_add_right _ hpenaltyMeas,
        lintegral_unit_threeEventPenalty]
      rfl
    _ ≤ (∫⁻ x : I,
          ∑' k : Nat, ENNReal.ofReal (geometricLogTerm k (x : ℝ))
          ∂volume) := by
      apply MeasureTheory.lintegral_mono_ae
      filter_upwards [MeasureTheory.volume.ae_ne (0 : I)] with x hx
      simpa [threeEventPenalty, add_assoc] using
        lintegral_right_three_event_payment hx leftLen rightLen hright
    _ = _ := lintegral_unit_geometricSeries_eq_ofReal

theorem threeEventEndpointPayment_nonneg : 0 ≤ threeEventEndpointPayment := by
  unfold threeEventEndpointPayment
  positivity

theorem finitePrefixCost_add_threeEventPayment_le_of_left
    (leftLen rightLen : Nat) (hleft : leftLen ≤ 1) :
    finitePrefixCost leftLen rightLen + threeEventEndpointPayment ≤
      geometricLogSeries := by
  have hNN := finitePrefixCostNN_add_threeEventPayment_le_of_left
    leftLen rightLen hleft
  have hsumTop : finitePrefixCostNN leftLen rightLen +
      ENNReal.ofReal threeEventEndpointPayment ≠ ⊤ := by
    apply ne_of_lt
    exact lt_of_le_of_lt hNN ENNReal.ofReal_lt_top
  have hfinTop : finitePrefixCostNN leftLen rightLen ≠ ⊤ :=
    (ENNReal.add_ne_top.mp hsumTop).1
  have hpayTop : ENNReal.ofReal threeEventEndpointPayment ≠ ⊤ :=
    ENNReal.ofReal_ne_top
  have hreal := (ENNReal.toReal_le_toReal hsumTop ENNReal.ofReal_ne_top).2 hNN
  rw [ENNReal.toReal_add hfinTop hpayTop,
    ENNReal.toReal_ofReal threeEventEndpointPayment_nonneg,
    ENNReal.toReal_ofReal geometricLogSeries_nonneg] at hreal
  exact hreal

theorem finitePrefixCost_add_threeEventPayment_le_of_right
    (leftLen rightLen : Nat) (hright : rightLen ≤ 1) :
    finitePrefixCost leftLen rightLen + threeEventEndpointPayment ≤
      geometricLogSeries := by
  have hNN := finitePrefixCostNN_add_threeEventPayment_le_of_right
    leftLen rightLen hright
  have hsumTop : finitePrefixCostNN leftLen rightLen +
      ENNReal.ofReal threeEventEndpointPayment ≠ ⊤ := by
    apply ne_of_lt
    exact lt_of_le_of_lt hNN ENNReal.ofReal_lt_top
  have hfinTop : finitePrefixCostNN leftLen rightLen ≠ ⊤ :=
    (ENNReal.add_ne_top.mp hsumTop).1
  have hpayTop : ENNReal.ofReal threeEventEndpointPayment ≠ ⊤ :=
    ENNReal.ofReal_ne_top
  have hreal := (ENNReal.toReal_le_toReal hsumTop ENNReal.ofReal_ne_top).2 hNN
  rw [ENNReal.toReal_add hfinTop hpayTop,
    ENNReal.toReal_ofReal threeEventEndpointPayment_nonneg,
    ENNReal.toReal_ofReal geometricLogSeries_nonneg] at hreal
  exact hreal

theorem canonicalShallow_targetGeometricSlack_ge_logTwoDivTwelve
    {n : Nat} {P : ProfileCode n}
    (D : StaticWindowData P) (hstable : (stableSet P).Nonempty)
    (base : MatchingCode n) (hbase : Stable P base) (m : Fin n)
    (hshallow : canonicalShallow P hstable ⟨base, hbase⟩ m) :
    Real.log 2 / 12 ≤ targetGeometricSlack D base m := by
  rw [targetGeometricSlack_eq_series_sub_finitePrefixCost_of_stable
    D base hbase m]
  let stableBase : CodedStable P := ⟨base, hbase⟩
  let j := D.center stableBase m
  have hendpoint := (canonicalShallow_iff_center_endpoint
    P hstable stableBase m (D.enumeration m) j
      (D.center_spec stableBase m)).1 hshallow
  rcases hendpoint with hleft | hright
  · have h := finitePrefixCost_add_threeEventPayment_le_of_left
      j.val (D.q m - (j.val + 1)) hleft
    have hp := log_two_div_twelve_le_threeEventEndpointPayment
    dsimp [stableBase, j] at h ⊢
    linarith
  · have h := finitePrefixCost_add_threeEventPayment_le_of_right
      j.val (D.q m - (j.val + 1)) hright
    have hp := log_two_div_twelve_le_threeEventEndpointPayment
    dsimp [stableBase, j] at h ⊢
    linarith

end

end StableMatchingsJointCharging
