import «CanonicalJointIntegration»
import «PriorityEventMass»

/-!
# Exact integrated payment of a canonical extra-left charge

The selected four-coordinate event has three participants before the target
and the immediate-right owner after it.  Its exact mass is `1/20`, and on
that event the target support/window gap is at least `log 2`.
-/

namespace StableMatchingsJointCharging

open MeasureTheory ProbabilityTheory Set
open scoped unitInterval ENNReal BigOperators
open StableMatchings355 StableMatchingsEntropy StableMatchingsE2E

noncomputable section

def selectedExtraPriorityBits {n : Nat} (target : Fin n)
    (e : Fin 4 ↪ OtherMen target) (priority : Fin n → I) :
    Fin 4 → Bool :=
  fun i ↦ lexRevealBits target priority (e i).1

def selectedExtraPriorityEvent {n : Nat} (target : Fin n)
    (e : Fin 4 ↪ OtherMen target) : Set (Fin n → I) :=
  selectedExtraPriorityBits target e ⁻¹' {extraPriorityPattern}

theorem measurable_selectedExtraPriorityBits {n : Nat} (target : Fin n)
    (e : Fin 4 ↪ OtherMen target) :
    Measurable (selectedExtraPriorityBits target e) := by
  apply measurable_pi_lambda
  intro i
  exact (measurable_pi_apply (e i).1).comp (measurable_lexRevealBits target)

theorem measurableSet_selectedExtraPriorityEvent {n : Nat} (target : Fin n)
    (e : Fin 4 ↪ OtherMen target) :
    MeasurableSet (selectedExtraPriorityEvent target e) :=
  (measurableSet_singleton extraPriorityPattern).preimage
    (measurable_selectedExtraPriorityBits target e)

theorem selectedExtraPriorityBits_assemble {n : Nat} (target : Fin n)
    (e : Fin 4 ↪ OtherMen target) (x : I)
    (omega : OtherMen target → I) :
    selectedExtraPriorityBits target e
        (assemblePriority target (x, omega)) =
      fun i ↦ lexTargetOtherIndicators target x omega (e i) := by
  rfl

theorem measurable_selectedLexFourBits {n : Nat} (target : Fin n)
    (e : Fin 4 ↪ OtherMen target) (x : I) :
    Measurable (fun omega ↦
      (fun i ↦ lexTargetOtherIndicators target x omega (e i))) := by
  have hins : Measurable (fun omega : OtherMen target → I ↦
      (x, omega)) := by fun_prop
  have hcomp := (measurable_selectedExtraPriorityBits target e).comp
    ((measurable_assemblePriority target).comp hins)
  simpa only [Function.comp_def, selectedExtraPriorityBits_assemble] using hcomp

theorem selected_lex_extraPriorityPattern_measure {n : Nat}
    (target : Fin n) (x : I) (e : Fin 4 ↪ OtherMen target) :
    ((TargetOtherPriorityMeasure target).map
        (fun omega i ↦ lexTargetOtherIndicators target x omega (e i)))
          ({extraPriorityPattern} : Set (Fin 4 → Bool)) =
      ENNReal.ofReal ((x : ℝ) ^ 3 * (1 - (x : ℝ))) := by
  rw [← ENNReal.ofReal_toReal (measure_ne_top _ _)]
  congr 1
  exact selected_lex_extraPriorityPattern_real target x e

theorem lintegral_unitInterval_extraPriorityPattern :
    (∫⁻ x : I,
        ENNReal.ofReal ((x : ℝ) ^ 3 * (1 - (x : ℝ))) ∂volume) =
      ENNReal.ofReal ((1 : ℝ) / 20) := by
  let p : ℝ → ℝ := fun x ↦ x ^ 3 * (1 - x)
  have hpcont : Continuous p := by
    exact (continuous_id.pow 3).mul (continuous_const.sub continuous_id)
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
  rw [← StableMatchingsE2E.integral_unitInterval_eq_Ioc p]
  simpa [p] using integral_unitInterval_extraPriorityPattern

theorem fullPriorityMeasure_selectedExtraPriorityEvent {n : Nat}
    (target : Fin n) (e : Fin 4 ↪ OtherMen target) :
    FullPriorityMeasure n (selectedExtraPriorityEvent target e) =
      ENNReal.ofReal ((1 : ℝ) / 20) := by
  let event := selectedExtraPriorityEvent target e
  have hevent : MeasurableSet event :=
    measurableSet_selectedExtraPriorityEvent target e
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
          ENNReal.ofReal ((x : ℝ) ^ 3 * (1 - (x : ℝ))) ∂volume := by
      apply MeasureTheory.lintegral_congr
      intro x
      rw [← selected_lex_extraPriorityPattern_measure target x e]
      rw [MeasureTheory.Measure.map_apply
        (measurable_selectedLexFourBits target e x)
        (measurableSet_singleton extraPriorityPattern)]
      rfl
    _ = _ := lintegral_unitInterval_extraPriorityPattern

theorem fullPriorityMeasureReal_selectedExtraPriorityEvent {n : Nat}
    (target : Fin n) (e : Fin 4 ↪ OtherMen target) :
    (FullPriorityMeasure n).real (selectedExtraPriorityEvent target e) =
      (1 : ℝ) / 20 := by
  rw [measureReal_def, fullPriorityMeasure_selectedExtraPriorityEvent]
  norm_num

theorem extraPriorityEvent_witness_before {n : Nat}
    {target witness leftOwner rightOwner : Fin n}
    (E : ExtraPriorityEmbedding target witness leftOwner rightOwner)
    (priority : Fin n → I)
    (hevent : priority ∈ selectedExtraPriorityEvent target E.embedding) :
    LexUnitRevealedBefore priority target witness := by
  have hzero := congrFun hevent 0
  simp only [selectedExtraPriorityEvent, Set.mem_preimage,
    Set.mem_singleton_iff, selectedExtraPriorityBits] at hevent
  have hbit := congrFun hevent 0
  change decide (LexUnitRevealedBefore priority target
    (E.embedding 0).1) = extraPriorityPattern 0 at hbit
  rw [E.witness_at_zero] at hbit
  simpa [lexRevealBits, extraPriorityPattern] using hbit

theorem extraPriorityEvent_left_before {n : Nat}
    {target witness leftOwner rightOwner : Fin n}
    (E : ExtraPriorityEmbedding target witness leftOwner rightOwner)
    (priority : Fin n → I)
    (hevent : priority ∈ selectedExtraPriorityEvent target E.embedding) :
    LexUnitRevealedBefore priority target leftOwner := by
  simp only [selectedExtraPriorityEvent, Set.mem_preimage,
    Set.mem_singleton_iff, selectedExtraPriorityBits] at hevent
  rcases E.left_at_zero_or_one with hleft | hleft
  · have hbit := congrFun hevent 0
    change decide (LexUnitRevealedBefore priority target
      (E.embedding 0).1) = extraPriorityPattern 0 at hbit
    rw [hleft] at hbit
    simpa [lexRevealBits, extraPriorityPattern] using hbit
  · have hbit := congrFun hevent 1
    change decide (LexUnitRevealedBefore priority target
      (E.embedding 1).1) = extraPriorityPattern 1 at hbit
    rw [hleft] at hbit
    simpa [lexRevealBits, extraPriorityPattern] using hbit

theorem extraPriorityEvent_right_after {n : Nat}
    {target witness leftOwner rightOwner : Fin n}
    (E : ExtraPriorityEmbedding target witness leftOwner rightOwner)
    (priority : Fin n → I)
    (hevent : priority ∈ selectedExtraPriorityEvent target E.embedding) :
    ¬ LexUnitRevealedBefore priority target rightOwner := by
  simp only [selectedExtraPriorityEvent, Set.mem_preimage,
    Set.mem_singleton_iff, selectedExtraPriorityBits] at hevent
  have hbit := congrFun hevent 3
  change decide (LexUnitRevealedBefore priority target
    (E.embedding 3).1) = extraPriorityPattern 3 at hbit
  rw [E.right_at_three] at hbit
  simpa [lexRevealBits, extraPriorityPattern] using hbit

theorem targetSupportWindowGap_ge_log_two_on_extraPriorityEvent
    {n : Nat} {P : ProfileCode n}
    (D : StaticWindowData P) (hstable : (stableSet P).Nonempty)
    (base : CodedStable P) (m : Fin n)
    (L : CanonicalExtraLocalData D hstable base m)
    (priority : Fin n → I)
    (hevent : priority ∈
      selectedExtraPriorityEvent m L.priorityEmbedding.embedding) :
    Real.log 2 ≤ targetSupportWindowGap D base priority m := by
  apply targetSupportWindowGap_ge_log_two_of_extra_conditions
    D hstable base m L priority
  · exact extraPriorityEvent_witness_before L.priorityEmbedding priority hevent
  · exact extraPriorityEvent_left_before L.priorityEmbedding priority hevent
  · exact extraPriorityEvent_right_after L.priorityEmbedding priority hevent

theorem integral_targetSupportWindowGap_ge_extraPayment
    {n : Nat} {P : ProfileCode n}
    (D : StaticWindowData P) (hstable : (stableSet P).Nonempty)
    (base : CodedStable P) (m : Fin n)
    (L : CanonicalExtraLocalData D hstable base m) :
    Real.log 2 / 20 ≤
      ∫ priority, targetSupportWindowGap D base priority m
        ∂(FullPriorityMeasure n) := by
  let event := selectedExtraPriorityEvent m L.priorityEmbedding.embedding
  let payment : (Fin n → I) → ℝ :=
    event.indicator (fun _ ↦ Real.log 2)
  have hevent : MeasurableSet event :=
    measurableSet_selectedExtraPriorityEvent m L.priorityEmbedding.embedding
  have hpayInt : Integrable payment (FullPriorityMeasure n) := by
    exact (integrable_const (c := Real.log 2)).indicator hevent
  have hgapInt := integrable_targetSupportWindowGap D base m
  have hpoint : ∀ priority, payment priority ≤
      targetSupportWindowGap D base priority m := by
    intro priority
    by_cases hp : priority ∈ event
    · simpa [payment, Set.indicator_of_mem hp] using
        targetSupportWindowGap_ge_log_two_on_extraPriorityEvent
          D hstable base m L priority hp
    · simpa [payment, hp] using
        targetSupportWindowGap_nonneg D base priority m
  have hint := MeasureTheory.integral_mono hpayInt hgapInt hpoint
  have hpay : (∫ priority, payment priority ∂(FullPriorityMeasure n)) =
      Real.log 2 / 20 := by
    unfold payment
    rw [MeasureTheory.integral_indicator_const (Real.log 2) hevent,
      fullPriorityMeasureReal_selectedExtraPriorityEvent]
    simp only [smul_eq_mul]
    ring
  linarith

theorem canonicalExtra_targetSupportWindowGap_ge_extraPayment
    {n : Nat} {P : ProfileCode n} (hn : 5 ≤ n)
    (D : StaticWindowData P) (hstable : (stableSet P).Nonempty)
    (base : CodedStable P) (m : Fin n)
    (hextra : canonicalExtraLeft P hstable base m) :
    Real.log 2 / 20 ≤
      ∫ priority, targetSupportWindowGap D base priority m
        ∂(FullPriorityMeasure n) := by
  obtain ⟨L⟩ := exists_canonicalExtraLocalData hn D hstable base m hextra
  exact integral_targetSupportWindowGap_ge_extraPayment
    D hstable base m L

end

end StableMatchingsJointCharging
