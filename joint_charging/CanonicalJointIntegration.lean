import «CanonicalExtraPayment»

/-!
# Integration of the canonical shallow/extra local payments
-/

namespace StableMatchingsJointCharging

open MeasureTheory ProbabilityTheory Set
open scoped unitInterval ENNReal BigOperators
open StableMatchings355 StableMatchingsEntropy StableMatchingsE2E

noncomputable section

theorem conditionalPartnerSupport_decidable_irrel {n : Nat}
    (P : ProfileCode n) (base : MatchingCode n)
    (revealed : Fin n → Prop) (m : Fin n)
    (d₁ d₂ : DecidablePred revealed) :
    @conditionalPartnerSupport n P base revealed d₁ m =
      @conditionalPartnerSupport n P base revealed d₂ m := by
  rw [show d₁ = d₂ from Subsingleton.elim _ _]

theorem markerWindowWidth_decidable_irrel {n q : Nat}
    {P : Profile (Fin n) (Fin n)} {target : Fin n}
    (E : ExactStablePartnerEnumeration (q := q) P target)
    (base : Matching (Fin n) (Fin n)) (revealed : Fin n → Prop)
    (j : Fin q) (d₁ d₂ : DecidablePred revealed) :
    markerWindowWidth
        (@leftMarkerBits n q P target E base revealed d₁ j)
        (@rightMarkerBits n q P target E base revealed d₁ j) =
      markerWindowWidth
        (@leftMarkerBits n q P target E base revealed d₂ j)
        (@rightMarkerBits n q P target E base revealed d₂ j) := by
  rw [show d₁ = d₂ from Subsingleton.elim _ _]

def lexRevealBits {n : Nat} (target : Fin n)
    (priority : Fin n → I) : Fin n → Bool :=
  fun p ↦ decide (LexUnitRevealedBefore priority target p)

theorem measurable_lexRevealBits {n : Nat} (target : Fin n) :
    Measurable (lexRevealBits target) := by
  exact measurable_pi_lambda _ fun p ↦ by
    simpa [lexRevealBits] using measurable_decide_lexBefore target p

noncomputable def supportLogFromBits {n : Nat} (P : ProfileCode n)
    (base : MatchingCode n) (m : Fin n) (bits : Fin n → Bool) : ℝ :=
  Real.log ((conditionalPartnerSupport P base
    (fun p ↦ bits p = true) m).card : ℝ)

theorem measurable_supportLogFromBits {n : Nat} (P : ProfileCode n)
    (base : MatchingCode n) (m : Fin n) :
    Measurable (supportLogFromBits P base m) :=
  measurable_of_finite _

noncomputable def targetSupportLog {n : Nat} (P : ProfileCode n)
    (base : MatchingCode n) (priority : Fin n → I) (m : Fin n) : ℝ :=
  supportLogFromBits P base m (lexRevealBits m priority)

theorem targetSupportLog_eq {n : Nat} (P : ProfileCode n)
    (base : MatchingCode n) (priority : Fin n → I) (m : Fin n) :
    targetSupportLog P base priority m =
      Real.log ((conditionalPartnerSupport P base
        (LexUnitRevealedBefore priority m) m).card : ℝ) := by
  unfold targetSupportLog supportLogFromBits lexRevealBits
  simp only [decide_eq_true_eq]

theorem integrable_targetSupportLog {n : Nat} (P : ProfileCode n)
    (base : MatchingCode n) (m : Fin n) :
    Integrable (fun priority ↦ targetSupportLog P base priority m)
      (FullPriorityMeasure n) := by
  let f := supportLogFromBits P base m
  have hfinite : Integrable f
      ((FullPriorityMeasure n).map (lexRevealBits m)) := Integrable.of_finite
  have hcomp := (integrable_map_measure
    (measurable_supportLogFromBits P base m).aestronglyMeasurable
    (measurable_lexRevealBits m).aemeasurable).mp hfinite
  simpa [targetSupportLog, Function.comp_def, f] using hcomp

noncomputable def targetSupportWindowGap {n : Nat} {P : ProfileCode n}
    (D : StaticWindowData P) (base : StableBase P)
    (priority : Fin n → I) (m : Fin n) : ℝ :=
  lexTargetMarkerLog D base priority m -
    targetSupportLog P base.1 priority m

theorem integrable_targetSupportWindowGap {n : Nat} {P : ProfileCode n}
    (D : StaticWindowData P) (base : StableBase P) (m : Fin n) :
    Integrable (fun priority ↦ targetSupportWindowGap D base priority m)
      (FullPriorityMeasure n) :=
  (integrable_lexTargetMarkerLog D base m).sub
    (integrable_targetSupportLog P base.1 m)

theorem targetSupportWindowGap_nonneg {n : Nat} {P : ProfileCode n}
    (D : StaticWindowData P) (base : StableBase P)
    (priority : Fin n → I) (m : Fin n) :
    0 ≤ targetSupportWindowGap D base priority m := by
  classical
  let revealed := LexUnitRevealedBefore priority m
  let seen := (List.ofFn (priorityOrder priority)).take
    ((priorityOrder priority).symm m).val
  have hrevealed : listRevealed seen = revealed := by
    funext p
    apply propext
    change p ∈ seen ↔ _
    rw [show seen = (List.ofFn (priorityOrder priority)).take
      ((priorityOrder priority).symm m).val by rfl]
    rw [mem_take_ofFn_perm_iff]
    exact fixedOrderRevealed_priorityOrder_target_iff priority m p
  have hcard0 := conditionalPartnerSupport_card_le_window P m
    (D.enumeration m) base.1 (listRevealed seen) base.2
    (D.center_spec base m) (D.window seen base m) (D.support seen base m)
  have hbound0 :
      (conditionalPartnerSupport P base.1 (listRevealed seen) m).card ≤
        markerWindowWidth
          (leftMarkerBits (D.enumeration m) base.1.toCore
            (listRevealed seen) (D.center base m))
          (rightMarkerBits (D.enumeration m) base.1.toCore
            (listRevealed seen) (D.center base m)) :=
    hcard0.trans_eq (D.selector_width seen m base)
  have hbound :
      (conditionalPartnerSupport P base.1 revealed m).card ≤
        markerWindowWidth
          (leftMarkerBits (D.enumeration m) base.1.toCore
            revealed (D.center base m))
          (rightMarkerBits (D.enumeration m) base.1.toCore
            revealed (D.center base m)) := by
    simpa [hrevealed] using hbound0
  have hpositive0 := conditionalPartnerSupport_nonempty
    P base.1 revealed m base.2
  have hpositive :
      (@conditionalPartnerSupport n P base.1 revealed
        (instDecidablePredFinLexUnitRevealedBefore priority m) m).Nonempty := by
    rw [conditionalPartnerSupport_decidable_irrel P base.1 revealed m
      (instDecidablePredFinLexUnitRevealedBefore priority m)
      (inferInstance : DecidablePred revealed)]
    exact hpositive0
  have hboundCanonical :
      (@conditionalPartnerSupport n P base.1 revealed
        (instDecidablePredFinLexUnitRevealedBefore priority m) m).card ≤
        markerWindowWidth
          (leftMarkerBits (D.enumeration m) base.1.toCore
            revealed (D.center base m))
          (rightMarkerBits (D.enumeration m) base.1.toCore
            revealed (D.center base m)) := by
    rw [conditionalPartnerSupport_decidable_irrel P base.1 revealed m
      (instDecidablePredFinLexUnitRevealedBefore priority m)
      (inferInstance : DecidablePred revealed)]
    exact hbound
  have hboundTarget :
      (@conditionalPartnerSupport n P base.1 revealed
        (instDecidablePredFinLexUnitRevealedBefore priority m) m).card ≤
        markerWindowWidth
          (@leftMarkerBits n (D.q m) P.toCore m (D.enumeration m)
            base.1.toCore revealed
            (fun a ↦ Classical.propDecidable (revealed a)) (D.center base m))
          (@rightMarkerBits n (D.q m) P.toCore m (D.enumeration m)
            base.1.toCore revealed
            (fun a ↦ Classical.propDecidable (revealed a)) (D.center base m)) := by
    rw [← markerWindowWidth_decidable_irrel
      (D.enumeration m) base.1.toCore revealed (D.center base m)
      (instDecidablePredFinLexUnitRevealedBefore priority m)
      (fun a ↦ Classical.propDecidable (revealed a))]
    exact hboundCanonical
  unfold targetSupportWindowGap
  rw [targetSupportLog_eq]
  unfold lexTargetMarkerLog staticMarkerLog
  apply sub_nonneg.mpr
  apply Real.log_le_log
  · exact_mod_cast Finset.card_pos.mpr hpositive
  · exact_mod_cast hboundTarget

theorem targetSupportWindowGap_ge_log_two_of_extra_conditions
    {n : Nat} {P : ProfileCode n}
    (D : StaticWindowData P) (hstable : (stableSet P).Nonempty)
    (base : CodedStable P) (m : Fin n)
    (L : CanonicalExtraLocalData D hstable base m)
    (priority : Fin n → I)
    (hwit : LexUnitRevealedBefore priority m L.witness.participant)
    (hleft : LexUnitRevealedBefore priority m
      (stablePartnerOwner (D.enumeration m) base.1.toCore
        (leftMarkerIndex (D.center base m) ⟨0, by
          have := L.leftTwo; omega⟩)))
    (hright : ¬ LexUnitRevealedBefore priority m
      (stablePartnerOwner (D.enumeration m) base.1.toCore
        (rightMarkerIndex (D.center base m) ⟨0, by
          have := L.rightTwo; omega⟩))) :
    Real.log 2 ≤ targetSupportWindowGap D base priority m := by
  classical
  let revealed := LexUnitRevealedBefore priority m
  have hsupp0 := conditionalPartnerSupport_card_eq_one_of_extra_witness
    hstable base m (D.enumeration m) (D.center base m)
    (D.center_spec base m) L.witness revealed
    (by have := L.leftTwo; omega) hwit hleft
  have hsupp :
      (@conditionalPartnerSupport n P base.1 revealed
        (instDecidablePredFinLexUnitRevealedBefore priority m) m).card = 1 := by
    rw [conditionalPartnerSupport_decidable_irrel P base.1 revealed m
      (instDecidablePredFinLexUnitRevealedBefore priority m)
      (inferInstance : DecidablePred revealed)]
    exact hsupp0
  have hwidth := markerWindowWidth_ge_two_of_right_owner_not_revealed
    (D.enumeration m) base.1.toCore (D.center base m) revealed
    (by have := L.rightTwo; omega) hright
  have hwidthTarget :
      2 ≤ markerWindowWidth
        (@leftMarkerBits n (D.q m) P.toCore m (D.enumeration m)
          base.1.toCore revealed
          (fun a ↦ Classical.propDecidable (revealed a)) (D.center base m))
        (@rightMarkerBits n (D.q m) P.toCore m (D.enumeration m)
          base.1.toCore revealed
          (fun a ↦ Classical.propDecidable (revealed a)) (D.center base m)) := by
    rw [← markerWindowWidth_decidable_irrel
      (D.enumeration m) base.1.toCore revealed (D.center base m)
      (instDecidablePredFinLexUnitRevealedBefore priority m)
      (fun a ↦ Classical.propDecidable (revealed a))]
    exact hwidth
  unfold targetSupportWindowGap
  rw [targetSupportLog_eq, hsupp]
  norm_num
  unfold lexTargetMarkerLog staticMarkerLog
  have hwidthReal : (2 : ℝ) ≤
      (markerWindowWidth
        (@leftMarkerBits n (D.q m) P.toCore m (D.enumeration m)
          base.1.toCore revealed
          (fun a ↦ Classical.propDecidable (revealed a)) (D.center base m))
        (@rightMarkerBits n (D.q m) P.toCore m (D.enumeration m)
          base.1.toCore revealed
          (fun a ↦ Classical.propDecidable (revealed a)) (D.center base m)) : ℕ) := by
    exact_mod_cast hwidthTarget
  exact Real.log_le_log (by norm_num) (by
    simpa [revealed] using hwidthReal)

end

end StableMatchingsJointCharging
