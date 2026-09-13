import StableMatchings355RandomReveal
import Mathlib.MeasureTheory.Constructions.UnitInterval
import Mathlib.MeasureTheory.Integral.Prod
import Mathlib.Probability.Distributions.Bernoulli
import Mathlib.Probability.HasLaw
import Mathlib.Probability.Independence.Basic

namespace StableMatchingsE2E

open MeasureTheory ProbabilityTheory Set
open scoped unitInterval ENNReal
open StableMatchings355

noncomputable section

/-- At threshold `x`, a priority `u` has been revealed exactly when `u < x`. -/
def revealIndicator (x u : I) : Bool := decide (u < x)

theorem measurable_revealIndicator (x : I) : Measurable (revealIndicator x) := by
  change Measurable (fun u : I => if u < x then true else false)
  exact measurable_const.ite measurableSet_Iio measurable_const

theorem revealIndicator_true_iff (x u : I) :
    revealIndicator x u = true ↔ u < x := by
  simp [revealIndicator]

theorem revealIndicator_false_iff (x u : I) :
    revealIndicator x u = false ↔ x ≤ u := by
  simp [revealIndicator, not_lt]

/-- A scalar uniform priority, thresholded at `x`, has the exact
`Bernoulli(x)` law.  The first atom (`true`) has mass `x`. -/
theorem map_revealIndicator_volume (x : I) :
    (volume : Measure I).map (revealIndicator x) = Ber(true, false, x) := by
  apply Measure.ext_of_singleton
  intro b
  fin_cases b
  · rw [Measure.map_apply (measurable_revealIndicator x) (measurableSet_singleton true)]
    have hpre : revealIndicator x ⁻¹' ({true} : Set Bool) = Iio x := by
      ext u
      simp [revealIndicator]
    rw [hpre]
    simp [← unitInterval.coe_toNNReal]
  · rw [Measure.map_apply (measurable_revealIndicator x) (measurableSet_singleton false)]
    have hpre : revealIndicator x ⁻¹' ({false} : Set Bool) = Ici x := by
      ext u
      simp [revealIndicator, not_lt]
    rw [hpre]
    simp [← unitInterval.coe_toNNReal]
    rw [show 1 - ((unitInterval.toNNReal x : NNReal) : Real) =
      ((unitInterval.toNNReal (unitInterval.symm x) : NNReal) : Real) by rfl]
    exact ENNReal.ofReal_coe_nnreal

/-- The finite product probability space of the non-target priorities. -/
abbrev OtherPriorityMeasure (n : Nat) : Measure (Fin n → I) :=
  Measure.pi (fun _ : Fin n => (volume : Measure I))

instance otherPriorityMeasure_isProbability (n : Nat) :
    IsProbabilityMeasure (OtherPriorityMeasure n) := inferInstance

/-- Fixed-threshold reveal indicators on the independent other-priority
product space. -/
def fixedThresholdIndicators (n : Nat) (x : I) :
    Fin n → (Fin n → I) → Bool :=
  fun i ω => revealIndicator x (ω i)

theorem measurable_fixedThresholdIndicator (n : Nat) (x : I) (i : Fin n) :
    Measurable (fixedThresholdIndicators n x i) :=
  (measurable_revealIndicator x).comp (measurable_pi_apply i)

/-- Conditional on an externally supplied threshold `x`, all reveal bits are
independent.  This is a statement on a genuine finite product probability
space; it does not condition on the null event that a sampled target equals
`x`. -/
theorem iIndepFun_fixedThresholdIndicators (n : Nat) (x : I) :
    iIndepFun (fixedThresholdIndicators n x) (OtherPriorityMeasure n) := by
  change iIndepFun (fun i (ω : Fin n → I) => revealIndicator x (ω i))
    (OtherPriorityMeasure n)
  have hcoord : iIndepFun
      (fun i (ω : Fin n → I) => ω i) (OtherPriorityMeasure n) := by
    exact iIndepFun_pi (X := fun _ : Fin n => id)
      (fun _ => measurable_id.aemeasurable)
  simpa only [Function.comp_def] using
    hcoord.comp (fun _ => revealIndicator x) (fun _ => measurable_revealIndicator x)

/-- Every individual reveal bit has the same exact `Bernoulli(x)` marginal. -/
theorem map_fixedThresholdIndicator (n : Nat) (x : I) (i : Fin n) :
    (OtherPriorityMeasure n).map (fixedThresholdIndicators n x i) =
      Ber(true, false, x) := by
  change (OtherPriorityMeasure n).map
      (revealIndicator x ∘ Function.eval i) = Ber(true, false, x)
  rw [← Measure.map_map (measurable_revealIndicator x) (measurable_pi_apply i)]
  rw [(measurePreserving_eval
    (fun _ : Fin n => (volume : Measure I)) i).map_eq]
  exact map_revealIndicator_volume x

/-- The law formulation of the previous marginal theorem, including explicit
measurability. -/
theorem hasLaw_fixedThresholdIndicator (n : Nat) (x : I) (i : Fin n) :
    HasLaw (fixedThresholdIndicators n x i) Ber(true, false, x)
      (OtherPriorityMeasure n) where
  aemeasurable := (measurable_fixedThresholdIndicator n x i).aemeasurable
  map_eq := map_fixedThresholdIndicator n x i

/-- Joint form: the complete fixed-threshold bit vector is exactly the finite
product of identical `Bernoulli(x)` measures. -/
theorem map_fixedThresholdIndicators (n : Nat) (x : I) :
    (OtherPriorityMeasure n).map
        (fun ω i => fixedThresholdIndicators n x i ω) =
      Measure.pi (fun _ : Fin n => Ber(true, false, x)) := by
  rw [(iIndepFun_fixedThresholdIndicators n x).map_fun_eq_pi_map
    (fun i => (measurable_fixedThresholdIndicator n x i).aemeasurable)]
  congr 1
  funext i
  exact map_fixedThresholdIndicator n x i

/-- Product measure used by the null-conditioning-free decomposition: the
first coordinate is the target threshold, and the second coordinate consists
of all other independent priorities. -/
abbrev SplitPriorityMeasure (n : Nat) : Measure (I × (Fin n → I)) :=
  (volume : Measure I).prod (OtherPriorityMeasure n)

instance splitPriorityMeasure_isProbability (n : Nat) :
    IsProbabilityMeasure (SplitPriorityMeasure n) := inferInstance

/-- Jointly sampled reveal vector in the split target/others construction. -/
def splitRevealVector (n : Nat) (z : I × (Fin n → I)) : Fin n → Bool :=
  fun i => fixedThresholdIndicators n z.1 i z.2

theorem measurable_splitRevealCoordinate (n : Nat) (i : Fin n) :
    Measurable (fun z : I × (Fin n → I) => splitRevealVector n z i) := by
  simp only [splitRevealVector, fixedThresholdIndicators, revealIndicator]
  change Measurable (fun z : I × (Fin n → I) =>
    if z.2 i < z.1 then true else false)
  exact measurable_const.ite
    (measurableSet_lt ((measurable_pi_apply i).comp measurable_snd) measurable_fst)
    measurable_const

theorem measurable_splitRevealVector (n : Nat) :
    Measurable (splitRevealVector n) := by
  exact measurable_pi_lambda _ (measurable_splitRevealCoordinate n)

/-- The exact Fubini interface used downstream.  The threshold is integrated
as an ordinary outer coordinate; no regular conditional probability at
`U_target = x` appears anywhere. -/
theorem integral_splitPriority_fubini (n : Nat)
    (f : I × (Fin n → I) → Real)
    (hf : Integrable f (SplitPriorityMeasure n)) :
    ∫ z, f z ∂(SplitPriorityMeasure n) =
      ∫ x : I, ∫ ω : Fin n → I, f (x, ω) ∂(OtherPriorityMeasure n) ∂volume := by
  exact integral_prod f hf

/-- Real-valued priorities induce a deterministic reveal prefix in the
already audited stable-matching support bridge.  This theorem holds pointwise
for every sampled vector, so it composes directly with the Fubini layer. -/
def UnitRevealedBefore {n : Nat}
    (priority : Fin n → I) (target p : Fin n) : Prop :=
  priority p < priority target

theorem unit_target_not_revealed {n : Nat}
    (priority : Fin n → I) (target : Fin n) :
    ¬ UnitRevealedBefore priority target target := by
  exact lt_irrefl _

theorem exists_unit_priority_full_bridge {n : Nat}
    (P : Profile (Fin n) (Fin n)) (target : Fin n)
    (base : Matching (Fin n) (Fin n))
    (priority : Fin n → I)
    (hbase : Stable P base) :
    ∃ q,
      ∃ E : ExactStablePartnerEnumeration (q := q) P target,
        ∃ j : Fin q,
          base.manPartner target = E.ranked.partner j ∧
          ∃ W : NearestRevealedWindow E base
              (UnitRevealedBefore priority target) j,
            ∃ S : ExactConditionalIndexSupport P E base
                (UnitRevealedBefore priority target),
              S.indices.length ≤
                upperBoundary W.upper - lowerBoundary W.lower := by
  exact exists_full_conditional_support_bridge P target base
    (UnitRevealedBefore priority target) hbase

/-! ## Target-specific split model

The next definitions remove a possible semantic ambiguity in the generic
`Fin n` product above: for an actual stable-marriage target, the product is
indexed by precisely the other men, and the target priority is inserted as a
separate outer coordinate. -/

abbrev OtherMen {n : Nat} (target : Fin n) := {p : Fin n // p ≠ target}

abbrev TargetOtherPriorityMeasure {n : Nat} (target : Fin n) :
    Measure (OtherMen target → I) :=
  Measure.pi (fun _ : OtherMen target => (volume : Measure I))

instance targetOtherPriorityMeasure_isProbability {n : Nat} (target : Fin n) :
    IsProbabilityMeasure (TargetOtherPriorityMeasure target) := inferInstance

abbrev SplitTargetPriorityMeasure {n : Nat} (target : Fin n) :
    Measure (I × (OtherMen target → I)) :=
  (volume : Measure I).prod (TargetOtherPriorityMeasure target)

instance splitTargetPriorityMeasure_isProbability {n : Nat} (target : Fin n) :
    IsProbabilityMeasure (SplitTargetPriorityMeasure target) := inferInstance

/-- Insert the externally integrated target threshold into the independently
sampled vector of all other priorities. -/
def assemblePriority {n : Nat} (target : Fin n)
    (z : I × (OtherMen target → I)) : Fin n → I :=
  fun p => if h : p = target then z.1 else z.2 ⟨p, h⟩

@[simp] theorem assemblePriority_target {n : Nat} (target : Fin n)
    (z : I × (OtherMen target → I)) :
    assemblePriority target z target = z.1 := by
  simp [assemblePriority]

theorem assemblePriority_other {n : Nat} (target p : Fin n)
    (z : I × (OtherMen target → I)) (hp : p ≠ target) :
    assemblePriority target z p = z.2 ⟨p, hp⟩ := by
  simp [assemblePriority, hp]

theorem unitRevealedBefore_assemble_other_iff {n : Nat}
    (target p : Fin n) (z : I × (OtherMen target → I)) (hp : p ≠ target) :
    UnitRevealedBefore (assemblePriority target z) target p ↔
      z.2 ⟨p, hp⟩ < z.1 := by
  simp [UnitRevealedBefore, assemblePriority_other target p z hp]

theorem measurable_assemblePriority_coordinate {n : Nat} (target p : Fin n) :
    Measurable (fun z : I × (OtherMen target → I) =>
      assemblePriority target z p) := by
  by_cases hp : p = target
  · subst p
    simpa only [assemblePriority_target] using
      (measurable_fst : Measurable (Prod.fst : I × (OtherMen target → I) → I))
  · simp only [assemblePriority_other target p _ hp]
    exact (measurable_pi_apply (⟨p, hp⟩ : OtherMen target)).comp measurable_snd

theorem measurable_assemblePriority {n : Nat} (target : Fin n) :
    Measurable (assemblePriority target) := by
  exact measurable_pi_lambda _ (measurable_assemblePriority_coordinate target)

/-- At every fixed target threshold, the actual other-men reveal bits are an
independent family. -/
theorem iIndepFun_targetOtherIndicators {n : Nat}
    (target : Fin n) (x : I) :
    iIndepFun
      (fun i (ω : OtherMen target → I) => revealIndicator x (ω i))
      (TargetOtherPriorityMeasure target) := by
  have hcoord : iIndepFun
      (fun i (ω : OtherMen target → I) => ω i)
      (TargetOtherPriorityMeasure target) := by
    exact iIndepFun_pi (X := fun _ : OtherMen target => id)
      (fun _ => measurable_id.aemeasurable)
  simpa only [Function.comp_def] using
    hcoord.comp (fun _ => revealIndicator x) (fun _ => measurable_revealIndicator x)

theorem map_targetOtherIndicator {n : Nat} (target : Fin n)
    (x : I) (i : OtherMen target) :
    (TargetOtherPriorityMeasure target).map
        (fun ω => revealIndicator x (ω i)) = Ber(true, false, x) := by
  change (TargetOtherPriorityMeasure target).map
    (revealIndicator x ∘ Function.eval i) = Ber(true, false, x)
  rw [← Measure.map_map (measurable_revealIndicator x) (measurable_pi_apply i)]
  rw [(measurePreserving_eval
    (fun _ : OtherMen target => (volume : Measure I)) i).map_eq]
  exact map_revealIndicator_volume x

/-- Exact joint conditional law for the actual non-target participants. -/
theorem map_targetOtherIndicators {n : Nat} (target : Fin n) (x : I) :
    (TargetOtherPriorityMeasure target).map
        (fun ω i => revealIndicator x (ω i)) =
      Measure.pi (fun _ : OtherMen target => Ber(true, false, x)) := by
  change (TargetOtherPriorityMeasure target).map
      (fun ω i => revealIndicator x (ω i)) =
    Measure.pi (fun _ : OtherMen target => Ber(true, false, x))
  have hmap := (iIndepFun_targetOtherIndicators target x).map_fun_eq_pi_map
    (fun i => ((measurable_revealIndicator x).comp
      (measurable_pi_apply i)).aemeasurable)
  calc
    _ = Measure.pi (fun i : OtherMen target =>
        (TargetOtherPriorityMeasure target).map
          (fun ω => revealIndicator x (ω i))) := by
      simpa only [Function.comp_def] using hmap
    _ = _ := by
      congr 1
      funext i
      exact map_targetOtherIndicator target x i

/-- Fubini specialized to the actual target/other-men split. -/
theorem integral_splitTargetPriority_fubini {n : Nat} (target : Fin n)
    (f : I × (OtherMen target → I) → Real)
    (hf : Integrable f (SplitTargetPriorityMeasure target)) :
    ∫ z, f z ∂(SplitTargetPriorityMeasure target) =
      ∫ x : I, ∫ ω : OtherMen target → I,
        f (x, ω) ∂(TargetOtherPriorityMeasure target) ∂volume := by
  exact integral_prod f hf

/-- Pointwise composition of the exact target/other-men sampling model with
the audited stable-matching structural bridge. -/
theorem exists_split_target_priority_full_bridge {n : Nat}
    (P : Profile (Fin n) (Fin n)) (target : Fin n)
    (base : Matching (Fin n) (Fin n))
    (z : I × (OtherMen target → I))
    (hbase : Stable P base) :
    ∃ q,
      ∃ E : ExactStablePartnerEnumeration (q := q) P target,
        ∃ j : Fin q,
          base.manPartner target = E.ranked.partner j ∧
          ∃ W : NearestRevealedWindow E base
              (UnitRevealedBefore (assemblePriority target z) target) j,
            ∃ S : ExactConditionalIndexSupport P E base
                (UnitRevealedBefore (assemblePriority target z) target),
              S.indices.length ≤
                upperBoundary W.upper - lowerBoundary W.lower := by
  exact exists_unit_priority_full_bridge P target base
    (assemblePriority target z) hbase

end

end StableMatchingsE2E
