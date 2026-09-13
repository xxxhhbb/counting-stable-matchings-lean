import «JointSlackLedger»
import Mathlib.Tactic

namespace StableMatchingsJointCharging

open MeasureTheory ProbabilityTheory StableMatchingsE2E
open scoped unitInterval ENNReal

noncomputable section

/-- Three required-earlier bits and one required-later bit. -/
def extraPriorityPattern : Fin 4 → Bool :=
  fun i => if i.1 < 3 then true else false

theorem pi_ber_extraPriorityPattern_real (x : I) :
    (Measure.pi (fun _ : Fin 4 => Ber(true, false, x))).real
        ({extraPriorityPattern} : Set (Fin 4 → Bool)) =
      (x : ℝ) ^ 3 * (1 - (x : ℝ)) := by
  have hset : ({extraPriorityPattern} : Set (Fin 4 → Bool)) =
      Set.pi Set.univ (fun i : Fin 4 => ({extraPriorityPattern i} : Set Bool)) := by
    ext f
    simp only [Set.mem_singleton_iff, Set.mem_pi, Set.mem_univ, true_implies,
      ]
    exact funext_iff
  rw [measureReal_def, hset, Measure.pi_pi]
  simp only [ENNReal.toReal_prod]
  norm_num [extraPriorityPattern, Fin.prod_univ_succ,
    ProbabilityTheory.bernoulliMeasure_apply]
  ring

/-- Selecting any four distinct non-target participants from the strict
threshold vector preserves the exact four-fold Bernoulli product law. -/
theorem map_selected_targetOtherIndicators {n : Nat}
    (target : Fin n) (x : I) (e : Fin 4 ↪ OtherMen target) :
    (TargetOtherPriorityMeasure target).map
        (fun ω i ↦ revealIndicator x (ω (e i))) =
      Measure.pi (fun _ : Fin 4 ↦ Ber(true, false, x)) := by
  have hind := (iIndepFun_targetOtherIndicators target x).precomp e.injective
  have hmap := hind.map_fun_eq_pi_map
    (fun i ↦ ((measurable_revealIndicator x).comp
      (measurable_pi_apply (e i))).aemeasurable)
  calc
    _ = Measure.pi (fun i : Fin 4 ↦
        (TargetOtherPriorityMeasure target).map
          (fun ω ↦ revealIndicator x (ω (e i)))) := by
      simpa only [Function.comp_def] using hmap
    _ = _ := by
      congr 1
      funext i
      exact map_targetOtherIndicator target x (e i)

/-- The same four-coordinate marginal law holds for the bits produced by
the genuine lexicographically tie-broken priority order. -/
theorem map_selected_lexTargetOtherIndicators {n : Nat}
    (target : Fin n) (x : I) (e : Fin 4 ↪ OtherMen target) :
    (TargetOtherPriorityMeasure target).map
        (fun ω i ↦ lexTargetOtherIndicators target x ω (e i)) =
      Measure.pi (fun _ : Fin 4 ↦ Ber(true, false, x)) := by
  calc
    _ = (TargetOtherPriorityMeasure target).map
        (fun ω i ↦ revealIndicator x (ω (e i))) :=
      MeasureTheory.Measure.map_congr
        ((lexTargetOtherIndicators_ae_eq_strict target x).fun_comp
          (fun b i ↦ b (e i)))
    _ = _ := map_selected_targetOtherIndicators target x e

/-- Exact conditional mass of the extra-left witness pattern inside the
actual lexicographic target/other-men priority model.  Stating this through
the pushforward measure avoids imposing artificial pointwise measurability
on the lexicographic representative; the map itself is already certified by
an a.e. congruence to the measurable strict-threshold representative. -/
theorem selected_lex_extraPriorityPattern_real {n : Nat}
    (target : Fin n) (x : I) (e : Fin 4 ↪ OtherMen target) :
    ((TargetOtherPriorityMeasure target).map
        (fun ω i ↦ lexTargetOtherIndicators target x ω (e i))).real
          ({extraPriorityPattern} : Set (Fin 4 → Bool)) =
      (x : ℝ) ^ 3 * (1 - (x : ℝ)) := by
  rw [map_selected_lexTargetOtherIndicators target x e]
  exact pi_ber_extraPriorityPattern_real x

/-- The conditional witness mass integrates to exactly `1/20` over the
uniform target threshold. -/
theorem integral_unitInterval_extraPriorityPattern :
    (∫ x : I, (x : ℝ) ^ 3 * (1 - (x : ℝ)) ∂volume) =
      (1 : ℝ) / 20 := by
  let f : ℝ → ℝ := fun y ↦ y ^ 3 * (1 - y)
  change (∫ x : I, f (x : ℝ) ∂volume) = _
  calc
    _ = ∫ x : ℝ in Set.Ioc (0 : ℝ) 1, f x :=
      StableMatchingsE2E.integral_unitInterval_eq_Ioc f
    _ = ∫ x : ℝ in 0..1, f x :=
      (intervalIntegral.integral_of_le (by norm_num : (0 : ℝ) ≤ 1)).symm
    _ = (1 : ℝ) / 20 := by
      simpa only [f] using integral_extra_priority_event

/-- Consequently, every embedded four-person extra-left witness has exact
unconditional mass `1/20` in the genuine split priority model. -/
theorem integral_selected_lex_extraPriorityPattern_real {n : Nat}
    (target : Fin n) (e : Fin 4 ↪ OtherMen target) :
    (∫ x : I,
      ((TargetOtherPriorityMeasure target).map
        (fun ω i ↦ lexTargetOtherIndicators target x ω (e i))).real
          ({extraPriorityPattern} : Set (Fin 4 → Bool)) ∂volume) =
      (1 : ℝ) / 20 := by
  simp_rw [selected_lex_extraPriorityPattern_real target]
  exact integral_unitInterval_extraPriorityPattern

end

end StableMatchingsJointCharging
