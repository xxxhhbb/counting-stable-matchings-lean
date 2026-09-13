import Mathlib.Analysis.Convex.Jensen
import Mathlib.Analysis.Convex.SpecificFunctions.Basic
import Mathlib.Analysis.SpecialFunctions.Log.NegMulLog

namespace StableMatchingsE2E

open scoped BigOperators
open Finset Set Real

/-!
# A finite Shannon layer

This file deliberately uses only finite sums.  In particular, no conditional
probability kernel and no conditioning on a null event occurs here.
-/

/-- Shannon entropy of weights indexed by a finite set.  Terms of weight zero
are harmless because `Real.negMulLog 0 = 0`. -/
noncomputable def finiteEntropy {α : Type*} (s : Finset α) (w : α → ℝ) : ℝ :=
  ∑ a ∈ s, Real.negMulLog (w a)

/-- A positive probability vector supported on `s` has entropy at most the
logarithm of the size of `s`.  The proof is finite Jensen applied to
`log`, with points `1 / w a` and weights `w a`. -/
theorem finiteEntropy_le_log_card_of_pos
    {α : Type*} (s : Finset α) (w : α → ℝ)
    (hwpos : ∀ a ∈ s, 0 < w a)
    (hwsum : ∑ a ∈ s, w a = 1) :
    finiteEntropy s w ≤ Real.log s.card := by
  have hJ := strictConcaveOn_log_Ioi.concaveOn.le_map_sum
    (t := s) (w := w) (p := fun a ↦ (w a)⁻¹)
    (fun a ha ↦ (hwpos a ha).le) hwsum
    (fun a ha ↦ by exact inv_pos.mpr (hwpos a ha))
  have hleft :
      (∑ a ∈ s, w a • Real.log (w a)⁻¹) = finiteEntropy s w := by
    apply Finset.sum_congr rfl
    intro a ha
    simp only [smul_eq_mul, Real.log_inv]
    simp [Real.negMulLog]
  have hright : (∑ a ∈ s, w a • (w a)⁻¹) = (s.card : ℝ) := by
    calc
      (∑ a ∈ s, w a • (w a)⁻¹) = ∑ _a ∈ s, (1 : ℝ) := by
        apply Finset.sum_congr rfl
        intro a ha
        simp [smul_eq_mul, (hwpos a ha).ne']
      _ = (s.card : ℝ) := by simp
  rw [hleft, hright] at hJ
  exact hJ

/-- The positive support of weights inside `s`. -/
noncomputable def positiveSupport {α : Type*} (s : Finset α) (w : α → ℝ) : Finset α :=
  s.filter fun a ↦ 0 < w a

@[simp] theorem mem_positiveSupport {α : Type*} {s : Finset α}
    {w : α → ℝ} {a : α} :
    a ∈ positiveSupport s w ↔ a ∈ s ∧ 0 < w a := by
  simp [positiveSupport]

/-- Removing zero-weight points changes neither total mass nor entropy. -/
theorem sum_positiveSupport_eq_sum_of_nonneg
    {α : Type*} (s : Finset α) (w : α → ℝ)
    (hw : ∀ a ∈ s, 0 ≤ w a) :
    (∑ a ∈ positiveSupport s w, w a) = ∑ a ∈ s, w a := by
  simp only [positiveSupport]
  rw [Finset.sum_filter]
  apply Finset.sum_congr rfl
  intro a ha
  by_cases hpos : 0 < w a
  · simp [hpos]
  · have hz : w a = 0 := le_antisymm (le_of_not_gt hpos) (hw a ha)
    simp [hz]

theorem finiteEntropy_positiveSupport_eq_of_nonneg
    {α : Type*} (s : Finset α) (w : α → ℝ)
    (hw : ∀ a ∈ s, 0 ≤ w a) :
    finiteEntropy (positiveSupport s w) w = finiteEntropy s w := by
  simp only [finiteEntropy, positiveSupport, Finset.sum_filter]
  apply Finset.sum_congr rfl
  intro a ha
  by_cases hpos : 0 < w a
  · simp [hpos]
  · have hz : w a = 0 := le_antisymm (le_of_not_gt hpos) (hw a ha)
    simp [hz]

/-- Unit total mass forces the computed positive support to be nonempty. -/
theorem positiveSupport_nonempty_of_sum_one
    {α : Type*} (s : Finset α) (w : α → ℝ)
    (hw : ∀ a ∈ s, 0 ≤ w a)
    (hwsum : ∑ a ∈ s, w a = 1) :
    (positiveSupport s w).Nonempty := by
  by_contra hne
  have hempty : positiveSupport s w = ∅ := Finset.not_nonempty_iff_eq_empty.mp hne
  have hmass := sum_positiveSupport_eq_sum_of_nonneg s w hw
  rw [hempty] at hmass
  simp [hwsum] at hmass

/-- General finite support bound, including zero weights.  The support is
computed rather than postulated, so the empty-support edge case cannot be
silently used to manufacture a probability distribution. -/
theorem finiteEntropy_le_log_positiveSupport_card
    {α : Type*} (s : Finset α) (w : α → ℝ)
    (hw : ∀ a ∈ s, 0 ≤ w a)
    (hwsum : ∑ a ∈ s, w a = 1) :
    finiteEntropy s w ≤ Real.log (positiveSupport s w).card := by
  rw [← finiteEntropy_positiveSupport_eq_of_nonneg s w hw]
  apply finiteEntropy_le_log_card_of_pos
  · intro a ha
    exact (mem_positiveSupport.mp ha).2
  · rw [sum_positiveSupport_eq_sum_of_nonneg s w hw, hwsum]

/-- Uniform weight on a finite set.  It is only used under a nonemptiness
hypothesis; no empty-set probability distribution is defined implicitly. -/
noncomputable def uniformWeight {α : Type*} (s : Finset α) (_a : α) : ℝ :=
  (s.card : ℝ)⁻¹

theorem sum_uniformWeight_eq_one {α : Type*} (s : Finset α)
    (hs : s.Nonempty) :
    ∑ a ∈ s, uniformWeight s a = 1 := by
  have hcard : (s.card : ℝ) ≠ 0 := by
    exact_mod_cast (Finset.card_ne_zero.mpr hs)
  simp [uniformWeight, hcard]

/-- The entropy of the uniform distribution on a nonempty finite set is
exactly the logarithm of its cardinality. -/
theorem finiteEntropy_uniform {α : Type*} (s : Finset α)
    (hs : s.Nonempty) :
    finiteEntropy s (uniformWeight s) = Real.log s.card := by
  have hcard : (s.card : ℝ) ≠ 0 := by
    exact_mod_cast (Finset.card_ne_zero.mpr hs)
  simp only [finiteEntropy, uniformWeight]
  rw [Finset.sum_const]
  simp only [nsmul_eq_mul]
  rw [Real.negMulLog]
  rw [Real.log_inv]
  field_simp

/-! ## A finite conditional chain rule -/

/-- Marginal mass of a prefix `a`; `next a` is its finite conditional
support. -/
noncomputable def marginalMass {α β : Type*}
    (next : α → Finset β) (joint : α → β → ℝ) (a : α) : ℝ :=
  ∑ b ∈ next a, joint a b

/-- Conditional weights inside a nonempty positive-mass prefix fiber. -/
noncomputable def conditionalWeight {α β : Type*}
    (next : α → Finset β) (joint : α → β → ℝ) (a : α) (b : β) : ℝ :=
  joint a b / marginalMass next joint a

/-- Entropy of a finite joint table whose valid cells are the dependent
fibers `next a`. -/
noncomputable def finiteJointEntropy {α β : Type*}
    (prefixes : Finset α) (next : α → Finset β)
    (joint : α → β → ℝ) : ℝ :=
  ∑ a ∈ prefixes, finiteEntropy (next a) (joint a)

/-- Entropy of the marginal distribution on prefixes. -/
noncomputable def finiteMarginalEntropy {α β : Type*}
    (prefixes : Finset α) (next : α → Finset β)
    (joint : α → β → ℝ) : ℝ :=
  finiteEntropy prefixes (marginalMass next joint)

/-- Marginally weighted finite conditional entropy. -/
noncomputable def finiteConditionalEntropy {α β : Type*}
    (prefixes : Finset α) (next : α → Finset β)
    (joint : α → β → ℝ) : ℝ :=
  ∑ a ∈ prefixes, marginalMass next joint a *
    finiteEntropy (next a) (conditionalWeight next joint a)

theorem marginalMass_pos_of_pos
    {α β : Type*} (prefixes : Finset α) (next : α → Finset β)
    (joint : α → β → ℝ)
    (hnext : ∀ a ∈ prefixes, (next a).Nonempty)
    (hjoint : ∀ a ∈ prefixes, ∀ b ∈ next a, 0 < joint a b)
    {a : α} (ha : a ∈ prefixes) :
    0 < marginalMass next joint a := by
  obtain ⟨b, hb⟩ := hnext a ha
  unfold marginalMass
  exact Finset.sum_pos' (fun c hc ↦ (hjoint a ha c hc).le)
    ⟨b, hb, hjoint a ha b hb⟩

theorem sum_conditionalWeight_eq_one
    {α β : Type*} (prefixes : Finset α) (next : α → Finset β)
    (joint : α → β → ℝ)
    (hnext : ∀ a ∈ prefixes, (next a).Nonempty)
    (hjoint : ∀ a ∈ prefixes, ∀ b ∈ next a, 0 < joint a b)
    {a : α} (ha : a ∈ prefixes) :
    ∑ b ∈ next a, conditionalWeight next joint a b = 1 := by
  have hm := (marginalMass_pos_of_pos prefixes next joint hnext hjoint ha).ne'
  simp only [conditionalWeight, div_eq_mul_inv, ← Finset.sum_mul]
  rw [show (∑ b ∈ next a, joint a b) = marginalMass next joint a by rfl]
  exact mul_inv_cancel₀ hm

/-- Summing the marginal masses is exactly summing the joint table. -/
theorem sum_marginalMass
    {α β : Type*} (prefixes : Finset α) (next : α → Finset β)
    (joint : α → β → ℝ) :
    (∑ a ∈ prefixes, marginalMass next joint a) =
      ∑ a ∈ prefixes, ∑ b ∈ next a, joint a b := by
  rfl

theorem sum_marginalMass_eq_one
    {α β : Type*} (prefixes : Finset α) (next : α → Finset β)
    (joint : α → β → ℝ)
    (hjointSum : ∑ a ∈ prefixes, ∑ b ∈ next a, joint a b = 1) :
    ∑ a ∈ prefixes, marginalMass next joint a = 1 := by
  rw [sum_marginalMass]
  exact hjointSum

/-- Exact finite Shannon chain rule.  It is stated for the active prefix
support and its nonempty dependent successor fibers, so no empty conditional
distribution is ever formed. -/
theorem finiteEntropy_chain_rule_of_pos
    {α β : Type*} (prefixes : Finset α) (next : α → Finset β)
    (joint : α → β → ℝ)
    (hnext : ∀ a ∈ prefixes, (next a).Nonempty)
    (hjoint : ∀ a ∈ prefixes, ∀ b ∈ next a, 0 < joint a b) :
    finiteJointEntropy prefixes next joint =
      finiteMarginalEntropy prefixes next joint +
        finiteConditionalEntropy prefixes next joint := by
  simp only [finiteJointEntropy, finiteMarginalEntropy,
    finiteConditionalEntropy, finiteEntropy]
  rw [← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro a ha
  have hmpos := marginalMass_pos_of_pos prefixes next joint hnext hjoint ha
  have hmne : marginalMass next joint a ≠ 0 := hmpos.ne'
  have hcondSum := sum_conditionalWeight_eq_one prefixes next joint hnext hjoint ha
  calc
    (∑ b ∈ next a, (joint a b).negMulLog) =
        ∑ b ∈ next a,
          (marginalMass next joint a * conditionalWeight next joint a b).negMulLog := by
      apply Finset.sum_congr rfl
      intro b hb
      congr 1
      rw [conditionalWeight]
      field_simp
    _ = ∑ b ∈ next a,
          (conditionalWeight next joint a b *
              (marginalMass next joint a).negMulLog +
            marginalMass next joint a *
              (conditionalWeight next joint a b).negMulLog) := by
      apply Finset.sum_congr rfl
      intro b hb
      exact Real.negMulLog_mul _ _
    _ = (marginalMass next joint a).negMulLog +
          marginalMass next joint a *
            ∑ b ∈ next a, (conditionalWeight next joint a b).negMulLog := by
      rw [Finset.sum_add_distrib]
      simp only [← Finset.sum_mul, ← mul_sum]
      rw [hcondSum]
      ring

/-- Conditional entropy is bounded by the marginal expectation of the log
conditional-support size.  This is the precise local inequality iterated by
the reveal-prefix argument. -/
theorem finiteConditionalEntropy_le_expected_log_card
    {α β : Type*} (prefixes : Finset α) (next : α → Finset β)
    (joint : α → β → ℝ)
    (hnext : ∀ a ∈ prefixes, (next a).Nonempty)
    (hjoint : ∀ a ∈ prefixes, ∀ b ∈ next a, 0 < joint a b) :
    finiteConditionalEntropy prefixes next joint ≤
      ∑ a ∈ prefixes, marginalMass next joint a * Real.log (next a).card := by
  simp only [finiteConditionalEntropy]
  apply Finset.sum_le_sum
  intro a ha
  have hmpos := marginalMass_pos_of_pos prefixes next joint hnext hjoint ha
  have hprob :
      finiteEntropy (next a) (conditionalWeight next joint a) ≤
        Real.log (next a).card := by
    apply finiteEntropy_le_log_card_of_pos
    · intro b hb
      exact div_pos (hjoint a ha b hb) hmpos
    · exact sum_conditionalWeight_eq_one prefixes next joint hnext hjoint ha
  exact mul_le_mul_of_nonneg_left hprob hmpos.le

/-- One reveal step: joint entropy is at most prefix entropy plus the
marginal expectation of the logarithm of the conditional support size.
Repeated application is the finite Shannon chain used by coordinate/prefix
reveal arguments. -/
theorem finiteJointEntropy_le_marginal_add_expected_log_card
    {α β : Type*} (prefixes : Finset α) (next : α → Finset β)
    (joint : α → β → ℝ)
    (hnext : ∀ a ∈ prefixes, (next a).Nonempty)
    (hjoint : ∀ a ∈ prefixes, ∀ b ∈ next a, 0 < joint a b) :
    finiteJointEntropy prefixes next joint ≤
      finiteMarginalEntropy prefixes next joint +
        ∑ a ∈ prefixes,
          marginalMass next joint a * Real.log (next a).card := by
  rw [finiteEntropy_chain_rule_of_pos prefixes next joint hnext hjoint]
  gcongr
  exact finiteConditionalEntropy_le_expected_log_card
    prefixes next joint hnext hjoint

end StableMatchingsE2E
