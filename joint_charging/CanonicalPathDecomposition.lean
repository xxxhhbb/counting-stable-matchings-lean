import «CanonicalExtraIntegration»

/-!
# Exact targetwise decomposition of the support/window path gap
-/

namespace StableMatchingsJointCharging

open MeasureTheory ProbabilityTheory Set
open scoped unitInterval ENNReal BigOperators
open StableMatchings355 StableMatchingsEntropy StableMatchingsE2E

noncomputable section

noncomputable def staticSupportLog {n : Nat} (P : ProfileCode n)
    (base : MatchingCode n) (m : Fin n) (revealed : Fin n → Prop) : ℝ := by
  classical
  exact Real.log ((conditionalPartnerSupport P base revealed m).card : ℝ)

noncomputable def indexedSupportPathBudget {n : Nat} (P : ProfileCode n)
    (base : MatchingCode n) (seen order : List (Fin n)) : ℝ :=
  (order.mapIdx fun k m ↦
    staticSupportLog P base m
      (listRevealed (seen ++ order.take k))).sum

theorem revealPathBudget_eq_indexedSupportPathBudget
    {n : Nat} (P : ProfileCode n) (base : MatchingCode n)
    (seen order : List (Fin n)) :
    revealPathBudget
        (listPrefixFiber (stableSet P) (fun mu p ↦ mu p) seen base)
        (fun mu p ↦ mu p) base order =
      indexedSupportPathBudget P base seen order := by
  classical
  induction order generalizing seen with
  | nil => simp [revealPathBudget, indexedSupportPathBudget]
  | cons m ms ih =>
      simp only [revealPathBudget, indexedSupportPathBudget, List.mapIdx_cons,
        List.sum_cons]
      rw [image_listPrefixFiber_eq_conditionalPartnerSupport_list
        P seen m base]
      rw [listPrefixFiber_filter_eq_append_singleton_local]
      simp only [List.take_zero, List.append_nil, staticSupportLog]
      rw [ih (seen := seen ++ [m])]
      congr 1
      unfold indexedSupportPathBudget
      apply congrArg List.sum
      simp only [List.mapIdx_eq_ofFn]
      apply congrArg List.ofFn
      funext i
      simp [List.take_succ_cons, List.append_assoc, staticSupportLog]
      congr 3
      apply conditionalPartnerSupport_decidable_irrel

theorem staticSupportLog_lex_eq_targetSupportLog {n : Nat}
    (P : ProfileCode n) (base : MatchingCode n)
    (priority : Fin n → I) (m : Fin n) :
    staticSupportLog P base m (LexUnitRevealedBefore priority m) =
      targetSupportLog P base priority m := by
  classical
  rw [targetSupportLog_eq]
  unfold staticSupportLog
  congr 2
  exact congrArg Finset.card
    (conditionalPartnerSupport_decidable_irrel P base
      (LexUnitRevealedBefore priority m) m
      (fun a ↦ Classical.propDecidable
        (LexUnitRevealedBefore priority m a))
      (instDecidablePredFinLexUnitRevealedBefore priority m))

theorem indexedSupportPathBudget_priorityOrder_eq_sum {n : Nat}
    (P : ProfileCode n) (base : MatchingCode n)
    (priority : Fin n → I) :
    indexedSupportPathBudget P base []
        (List.ofFn (priorityOrder priority)) =
      ∑ m : Fin n, targetSupportLog P base priority m := by
  classical
  unfold indexedSupportPathBudget
  let order := priorityOrder priority
  have hmap :
      (List.ofFn order).mapIdx (fun k m ↦
        staticSupportLog P base m
          (listRevealed ([] ++ (List.ofFn order).take k))) =
        List.ofFn (fun i : Fin n ↦
          staticSupportLog P base (order i)
            (listRevealed ((List.ofFn order).take i.val))) := by
    apply List.ext_get
    · simp
    · intro k hk hk'
      simp
  rw [show List.ofFn (priorityOrder priority) = List.ofFn order by rfl]
  rw [hmap, List.sum_ofFn]
  have hpoint : ∀ i : Fin n,
      staticSupportLog P base (order i)
          (listRevealed ((List.ofFn order).take i.val)) =
        targetSupportLog P base priority (order i) := by
    intro i
    rw [← staticSupportLog_lex_eq_targetSupportLog]
    congr 1
    funext p
    apply propext
    rw [show listRevealed ((List.ofFn order).take i.val) p ↔
        p ∈ (List.ofFn order).take i.val by rfl]
    rw [mem_take_ofFn_perm_iff]
    have hi : (order.symm (order i)).val = i.val := by simp
    rw [← hi]
    exact fixedOrderRevealed_priorityOrder_target_iff
      priority (order i) p
  calc
    (∑ i : Fin n, staticSupportLog P base (order i)
        (listRevealed ((List.ofFn order).take i.val))) =
        ∑ i : Fin n, targetSupportLog P base priority (order i) := by
      apply Finset.sum_congr rfl
      intro i hi
      exact hpoint i
    _ = _ := Equiv.sum_comp order (targetSupportLog P base priority)

theorem revealPathBudget_priorityOrder_eq_sum_targetSupportLog
    {n : Nat} (P : ProfileCode n) (base : MatchingCode n)
    (priority : Fin n → I) :
    revealPathBudget (stableSet P) (fun mu m ↦ mu m) base
        (List.ofFn (priorityOrder priority)) =
      ∑ m : Fin n, targetSupportLog P base priority m := by
  rw [show stableSet P =
      listPrefixFiber (stableSet P) (fun mu p ↦ mu p) [] base by
    ext mu
    simp [listPrefixFiber]]
  rw [revealPathBudget_eq_indexedSupportPathBudget]
  exact indexedSupportPathBudget_priorityOrder_eq_sum P base priority

theorem supportWindowPathGap_eq_sum_targetSupportWindowGap
    {n : Nat} {P : ProfileCode n}
    (D : StaticWindowData P) (base : MatchingCode n)
    (hbase : Stable P base) (priority : Fin n → I) :
    supportWindowPathGap D priority base =
      ∑ m : Fin n,
        targetSupportWindowGap D ⟨base, hbase⟩ priority m := by
  unfold supportWindowPathGap targetSupportWindowGap
  simp only [hbase, dif_pos]
  rw [prefixWindowPathBudget_priorityOrder_eq_sum D ⟨base, hbase⟩ priority,
    revealPathBudget_priorityOrder_eq_sum_targetSupportLog P base priority,
    Finset.sum_sub_distrib]

end

end StableMatchingsJointCharging
